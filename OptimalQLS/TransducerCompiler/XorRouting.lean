import OptimalQLS.TransducerCompiler.Basic

/-! # XOR implementation of selected-clock work

Conjugating a zero-clock work gate by any clock permutation that maps zero
to the selected slot gives the same matrix. This allows the swap-based
semantic compiler to be synthesized using amortized binary XOR updates.
-/

noncomputable section
namespace OptimalQLS.TransducerCompiler
open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] {K : ℕ}

/-- A different clock permutation in every data/label sector. -/
def routingVia (p : n → Equiv.Perm (Fin K)) : Equiv.Perm (n × Fin K) where
  toFun x := (x.1,p x.1 x.2)
  invFun x := (x.1,(p x.1).symm x.2)
  left_inv x := by simp
  right_inv x := by simp

@[simp] theorem routingVia_apply (p : n → Equiv.Perm (Fin K)) (x : n × Fin K) :
    routingVia p x = (x.1,p x.1 x.2) := rfl

/-- One controlled-work call, with arbitrary invertible address routing. -/
def routedWorkUsing (zero : Fin K) (p : n → Equiv.Perm (Fin K))
    (U : Matrix.unitaryGroup n ℂ) : Matrix.unitaryGroup (n × Fin K) ℂ :=
  permutation (routingVia (fun i => (p i).symm)) *
    controlledUnitary K (fun k => decide (k = zero)) U * permutation (routingVia p)

theorem routedWorkUsing_apply (zero : Fin K) (p : n → Equiv.Perm (Fin K))
    (U : Matrix.unitaryGroup n ℂ) (v : n × Fin K → ℂ) (i : n) (k : Fin K) :
    ((routedWorkUsing zero p U : Matrix (n × Fin K) (n × Fin K) ℂ) *ᵥ v) (i,k) =
      if k = p i zero then ((U : Matrix n n ℂ) *ᵥ fun j => v (j,p j zero)) i else v (i,k) := by
  simp only [routedWorkUsing, Submonoid.coe_mul, ← Matrix.mulVec_mulVec,
    permutation_apply, Function.comp_apply, routingVia_apply]
  rw [controlled_apply]
  have hz : (p i).symm k = zero ↔ k = p i zero := (p i).symm_apply_eq
  simp only [decide_eq_true_eq, hz]
  split_ifs with hk
  · congr 2
    funext j
    simp [hk]
  · simp

/-- Routing choices are exactly interchangeable as full matrices, not just on
one promised catalyst state. -/
theorem routedWorkUsing_eq (zero : Fin K) (p : n → Equiv.Perm (Fin K))
    (f : n → Fin K) (hp : ∀ i, p i zero = f i) (U : Matrix.unitaryGroup n ℂ) :
    routedWorkUsing zero p U = routedWork zero f U := by
  apply Subtype.ext
  apply Matrix.ext_of_mulVec_single
  intro j
  ext ⟨i,k⟩
  rw [routedWorkUsing_apply, routedWork_apply]
  simp only [hp]
  split_ifs
  · congr 2
    funext a
    rw [hp a]
  · rfl

/-- XOR by a fixed bit mask is a real reversible clock operation. -/
def xorClock {ℓ : ℕ} (mask : Fin (2^ℓ)) : Equiv.Perm (Fin (2^ℓ)) where
  toFun k := (BitVec.ofFin k ^^^ BitVec.ofFin mask).toFin
  invFun k := (BitVec.ofFin k ^^^ BitVec.ofFin mask).toFin
  left_inv k := by
    apply Fin.ext
    simp [Nat.xor_assoc]
  right_inv k := by
    apply Fin.ext
    simp [Nat.xor_assoc]

@[simp] theorem xorClock_zero {ℓ : ℕ} (mask : Fin (2^ℓ)) :
    xorClock mask 0 = mask := by
  apply Fin.ext
  simp [xorClock]


@[simp] theorem xorClock_zero_mask {ℓ : ℕ} : xorClock (0 : Fin (2^ℓ)) = Equiv.refl _ := by
  ext k
  simp [xorClock]

@[simp] theorem xorClock_symm {ℓ : ℕ} (mask : Fin (2^ℓ)) :
    (xorClock mask).symm = xorClock mask := by
  ext k
  rfl

/-- The compiler's work step has an exact XOR-routing implementation. -/
theorem xor_routedWork_eq {ℓ : ℕ} (f : n → Fin (2^ℓ))
    (U : Matrix.unitaryGroup n ℂ) :
    routedWorkUsing 0 (fun i => xorClock (f i)) U = routedWork 0 f U :=
  routedWorkUsing_eq 0 _ f (fun i => xorClock_zero (f i)) U

/-- Neighboring XOR routes combine to the XOR of their two addresses. -/
theorem xorClock_trans {ℓ : ℕ} (a b : Fin (2^ℓ)) :
    (xorClock a).trans (xorClock b) = xorClock (BitVec.ofFin a ^^^ BitVec.ofFin b).toFin := by
  ext k
  simp [xorClock, Nat.xor_assoc]

end OptimalQLS.TransducerCompiler
