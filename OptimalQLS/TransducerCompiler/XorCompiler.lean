import OptimalQLS.TransducerCompiler.Circuit
import OptimalQLS.TransducerCompiler.XorRouting

noncomputable section
namespace OptimalQLS.TransducerCompiler
open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] {ℓ : ℕ}

/-- The current per-label XOR frame; it fixes every data and label index. -/
def xorFrame (b : Layout (2^ℓ)) (t : ℕ) : Matrix.unitaryGroup (Space n (2^ℓ)) ℂ :=
  permutation (routingVia fun i => xorClock
    (address b.zero b.D₁ b.D₂ (b.time t) b.positive₁ b.positive₂ b.le₁ b.le₂ i))

@[simp] theorem xorFrame_zero (b : Layout (2^ℓ)) : xorFrame (n := n) b 0 = 1 := by
  have ha : address b.zero b.D₁ b.D₂ (b.time 0)
      b.positive₁ b.positive₂ b.le₁ b.le₂ = (fun _ : Base n => (0 : Fin (2^ℓ))) := by
    ext ⟨i,l⟩
    cases l <;> rfl
  simp only [xorFrame, ha, xorClock_zero_mask]
  have he : routingVia (fun _ : Base n => Equiv.refl (Fin (2^ℓ))) = Equiv.refl _ := by
    apply Equiv.ext
    intro x
    rfl
  rw [he]
  apply Subtype.ext
  exact Matrix.permMatrix_refl

@[simp] theorem xorFrame_final (b : Layout (2^ℓ)) : xorFrame (n := n) b (2^ℓ) = 1 := by
  have ht : b.time (2^ℓ) = b.time 0 := by
    apply Fin.ext
    simp [Layout.time]
  simpa only [xorFrame, ht] using xorFrame_zero (n := n) b

theorem xorFrame_square (b : Layout (2^ℓ)) (t : ℕ) :
    xorFrame (n := n) b t * xorFrame b t = 1 := by
  let e := routingVia fun i : Base n => xorClock
    (address b.zero b.D₁ b.D₂ (b.time t) b.positive₁ b.positive₂ b.le₁ b.le₂ i)
  apply Subtype.ext
  change e.permMatrix ℂ * e.permMatrix ℂ = 1
  rw [← Matrix.permMatrix_mul]
  have he : e * e = 1 := by
    apply Equiv.ext
    rintro ⟨i,k⟩
    simp only [e, Equiv.Perm.mul_apply, routingVia_apply, Prod.mk.injEq, true_and]
    exact congrArg (fun z => (i,z)) ((xorClock _).left_inv k)
  rw [he]
  exact Matrix.permMatrix_one

/-- The swap-address work matrix equals a pair of XOR frames around a zero-clock call. -/
theorem xorFrame_work (b : Layout (2^ℓ)) (t : ℕ) (S : Matrix.unitaryGroup (Base n) ℂ) :
    routedWork b.zero
      (address b.zero b.D₁ b.D₂ (b.time t) b.positive₁ b.positive₂ b.le₁ b.le₂) S =
      xorFrame b t * controlledUnitary (2^ℓ) (fun k => decide (k = b.zero)) S *
        xorFrame b t := by
  have hz : b.zero = (0 : Fin (2^ℓ)) := by apply Fin.ext; rfl
  rw [hz, ← xor_routedWork_eq]
  simp only [routedWorkUsing, xorClock_symm, xorFrame, hz]

/-- The address is determined by label alone. -/
def labelAddress (b : Layout (2^ℓ)) (t : ℕ) : Label → Fin (2^ℓ)
  | .pub => b.time t
  | .internal => b.zero
  | .first => ⟨(b.time t).val % b.D₁, (Nat.mod_lt _ b.positive₁).trans_le b.le₁⟩
  | .second => ⟨(b.time t).val % b.D₂, (Nat.mod_lt _ b.positive₂).trans_le b.le₂⟩

theorem address_eq_labelAddress (b : Layout (2^ℓ)) (t : ℕ) :
    address b.zero b.D₁ b.D₂ (b.time t) b.positive₁ b.positive₂ b.le₁ b.le₂ =
      (fun i : Base n => labelAddress b t i.2) := by
  funext ⟨i,l⟩
  cases l <;> rfl

/-- Data queries commute with every label-dependent clock permutation. -/
theorem query_commutes_labelRouting {K : ℕ} (p : Label → Equiv.Perm (Fin K))
    (l : Label) (U : Matrix.unitaryGroup n ℂ) :
    Commute (query (K := K) l U)
      (permutation (routingVia (fun i : Base n => p i.2))) := by
  apply Subtype.ext
  apply Matrix.ext_of_mulVec_single
  intro j
  ext ⟨⟨i,m⟩,k⟩
  simp only [Submonoid.coe_mul, ← Matrix.mulVec_mulVec, permutation_apply,
    Function.comp_apply, routingVia_apply]
  rw [query_apply]
  simp only [Function.comp_apply, routingVia_apply, query_apply]

theorem oracleStage_commutes_xorFrame (b : Layout (2^ℓ)) (t : ℕ)
    (U₁ U₂ : Matrix.unitaryGroup n ℂ) :
    Commute (oracleStage b.D₁ b.D₂ t U₁ U₂) (xorFrame b t) := by
  unfold xorFrame
  rw [address_eq_labelAddress]
  have h₁ := query_commutes_labelRouting (fun l => xorClock (labelAddress b t l)) .first U₁
  have h₂ := query_commutes_labelRouting (fun l => xorClock (labelAddress b t l)) .second U₂
  unfold oracleStage
  split_ifs <;> simp only [one_mul, mul_one]
  · exact h₂.mul_left h₁
  · exact h₂
  · exact h₁
  · exact Commute.one_left _

/-- The optimized step has a single zero-clock work call and one frame update. -/
def xorStep (b : Layout (2^ℓ)) (S : Matrix.unitaryGroup (Base n) ℂ)
    (U₁ U₂ : Matrix.unitaryGroup n ℂ) (t : ℕ) : Matrix.unitaryGroup (Space n (2^ℓ)) ℂ :=
  xorFrame b (t+1) * xorFrame b t *
    controlledUnitary (2^ℓ) (fun k => decide (k = b.zero)) S *
      oracleStage b.D₁ b.D₂ t U₁ U₂

def xorPrefix (b : Layout (2^ℓ)) (S : Matrix.unitaryGroup (Base n) ℂ)
    (U₁ U₂ : Matrix.unitaryGroup n ℂ) : ℕ → Matrix.unitaryGroup (Space n (2^ℓ)) ℂ
  | 0 => 1
  | t+1 => xorStep b S U₁ U₂ t * xorPrefix b S U₁ U₂ t

/-- Full matrix equivalence, without any catalyst-state promise. -/
theorem xorPrefix_eq (b : Layout (2^ℓ)) (S : Matrix.unitaryGroup (Base n) ℂ)
    (U₁ U₂ : Matrix.unitaryGroup n ℂ) (t : ℕ) :
    xorPrefix b S U₁ U₂ t = xorFrame b t * (compilePrefix b t).eval b S U₁ U₂ := by
  induction t with
  | zero => simp [xorPrefix, compilePrefix, Circuit.eval]
  | succ t ih =>
    rw [xorPrefix, ih, compilePrefix, Circuit.eval_append, round_eval, xorFrame_work]
    simp only [xorStep, mul_assoc]
    have hc := oracleStage_commutes_xorFrame b t U₁ U₂
    rw [← mul_assoc (oracleStage b.D₁ b.D₂ t U₁ U₂) (xorFrame b t)
      ((compilePrefix b t).eval b S U₁ U₂), hc.eq, mul_assoc]

/-- After one full cycle the optimized frame disappears exactly. -/
theorem xorPrefix_final (b : Layout (2^ℓ)) (S : Matrix.unitaryGroup (Base n) ℂ)
    (U₁ U₂ : Matrix.unitaryGroup n ℂ) :
    xorPrefix b S U₁ U₂ (2^ℓ) = (compile b).eval b S U₁ U₂ := by
  rw [xorPrefix_eq, xorFrame_final, one_mul]
  rfl

end OptimalQLS.TransducerCompiler
