import OptimalQLS.LowerBounds.Physical.Proposition64

/-! Eliminate controlled standard-bit queries with an explicit clean response bit. -/
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 4096
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
namespace OptimalQLS.LowerBounds.Physical
open Matrix PolynomialTransform
variable {S W : Type*} [Fintype S] [DecidableEq S] [Fintype W] [DecidableEq W]

theorem queryPort_basis_transition (p : QueryPort S W) (U : Matrix.unitaryGroup S ℂ)
    (i j : S) (k : Fin p.multiplicity)
    (h : U.val *ᵥ Pi.single i 1 = Pi.single j 1) :
    (p.apply U).val *ᵥ Pi.single (p.wiring (i,k)) 1 =
      Pi.single (p.wiring ((if p.control k then j else i),k)) 1 := by
  ext w
  obtain ⟨⟨x,l⟩,rfl⟩ := p.wiring.surjective w
  simp only [Matrix.mulVec_single_one, Matrix.col_apply, QueryPort.apply_entries]
  by_cases hl : l=k
  · subst l
    have hx := congrFun h x
    simp only [Matrix.mulVec_single_one, Matrix.col_apply, Pi.single_apply] at hx
    cases hc : p.control k <;> simp [hc, Pi.single_apply, p.wiring.injective.eq_iff, hx]
  · simp [hl, Pi.single_apply, p.wiring.injective.eq_iff]

@[simp] theorem standardBitOracle_inv {m : ℕ} (z : BitString m) :
    (standardBitOracle z)⁻¹ = standardBitOracle z := by
  apply Subtype.ext
  change (forwardPermutation (bitPermutation z)).valᴴ = (forwardPermutation (bitPermutation z)).val
  change (Equiv.Perm.permMatrix ℂ ((bitPermutation z)⁻¹))ᴴ =
    Equiv.Perm.permMatrix ℂ ((bitPermutation z)⁻¹)
  rw [Matrix.conjTranspose_permMatrix]
  rfl

/-- Query the added response bit, leaving the original response and workspace
sector as spectators. This port has every control set to true. -/
def responseCoordinates {m : ℕ} (p : QueryPort (BitBasis m) W) :
    BitBasis m × (Bool × Fin p.multiplicity) ≃ W × Bool where
  toFun x := (p.wiring ((x.1.1,x.2.1),x.2.2),x.1.2)
  invFun x := (((p.wiring.symm x.1).1.1,x.2),((p.wiring.symm x.1).1.2,(p.wiring.symm x.1).2))
  left_inv x := by rcases x with ⟨⟨i,c⟩,a,k⟩; simp
  right_inv x := by rcases x with ⟨w,c⟩; simp

def responsePort {m : ℕ} (p : QueryPort (BitBasis m) W) : QueryPort (BitBasis m) (W × Bool) :=
  scratchPort (responseCoordinates p)

@[simp] theorem responsePort_control {m : ℕ} (p : QueryPort (BitBasis m) W)
    (k : Fin (responsePort p).multiplicity) : (responsePort p).control k = true := rfl

def selectResponseMap {m : ℕ} (p : QueryPort (BitBasis m) W) (x : W × Bool) : W × Bool :=
  let y := p.wiring.symm x.1
  (p.wiring ((y.1.1, Bool.xor y.1.2 (x.2 && p.control y.2)),y.2),x.2)

def selectResponse {m : ℕ} (p : QueryPort (BitBasis m) W) : Equiv.Perm (W × Bool) :=
  (show Function.Involutive (selectResponseMap p) from by
    rintro ⟨w,c⟩
    obtain ⟨⟨⟨i,a⟩,k⟩,rfl⟩ := p.wiring.surjective w
    cases a <;> cases c <;> cases hc : p.control k <;> simp [selectResponseMap,hc]).toPerm

/-- Exactly two uncontrolled oracle calls; the middle CNOT is known. -/
def uncontrolledBitCall {m : ℕ} (p : QueryPort (BitBasis m) W) :
    QueryCircuit (BitBasis m) Unit (W × Bool) :=
  [.matrixCall (responsePort p) false,
   .work (forwardPermutation (selectResponse p)),
   .matrixCall (responsePort p) false]

theorem responsePort_basis {m : ℕ} (p : QueryPort (BitBasis m) W) (z : BitString m)
    (i : Fin m) (a c : Bool) (k : Fin p.multiplicity) :
    ((responsePort p).apply (standardBitOracle z)).val *ᵥ
      Pi.single (p.wiring ((i,a),k),c) 1 =
      Pi.single (p.wiring ((i,a),k),Bool.xor c (z i)) 1 := by
  rw [responsePort, scratchPort_apply]
  simpa only [one_smul] using placeHom_basis_smul (responseCoordinates p) (standardBitOracle z)
    (i,c) (i,Bool.xor c (z i)) (a,k) 1 (by simpa using standardBitOracle_basis z i c)

theorem uncontrolledBitCall_basis {m : ℕ} (p : QueryPort (BitBasis m) W) (z : BitString m)
    (i : Fin m) (a : Bool) (k : Fin p.multiplicity) :
    ((uncontrolledBitCall p).eval (standardBitOracle z) 1).val *ᵥ
      Pi.single (p.wiring ((i,a),k),false) 1 =
      Pi.single (p.wiring ((i,if p.control k then Bool.xor a (z i) else a),k),false) 1 := by
  simp only [uncontrolledBitCall, QueryCircuit.eval, QueryInstruction.eval, Bool.false_eq_true,
    if_false, one_mul, Submonoid.coe_mul, ← Matrix.mulVec_mulVec]
  rw [responsePort_basis, forwardPermutation_basis]
  change ((responsePort p).apply (standardBitOracle z)).val *ᵥ
    Pi.single (selectResponseMap p (p.wiring ((i,a),k),Bool.xor false (z i))) 1 = _
  simp only [selectResponseMap, Equiv.symm_apply_apply, Bool.false_xor]
  rw [responsePort_basis]
  cases a <;> cases hc : p.control k <;> cases hz : z i <;> simp [hc,hz]

/-- The replacement preserves arbitrary input superpositions and resets its
one response scratch bit, even for an adjoint controlled query. -/
theorem uncontrolledBitCall_clean {m : ℕ} (p : QueryPort (BitBasis m) W)
    (adjoint : Bool) (z : BitString m) :
    ((uncontrolledBitCall p).eval (standardBitOracle z) 1).val *
      basisInsertion (fun w : W => (w,false)) =
      basisInsertion (fun w : W => (w,false)) *
        (p.apply (if adjoint then (standardBitOracle z)⁻¹ else standardBitOracle z)).val := by
  simp only [standardBitOracle_inv, ite_self]
  apply basisInsertion_intertwines
  intro w
  obtain ⟨⟨⟨i,a⟩,k⟩,rfl⟩ := p.wiring.surjective w
  rw [uncontrolledBitCall_basis,
    queryPort_basis_transition p (standardBitOracle z) (i,a) (i,Bool.xor a (z i)) k
      (standardBitOracle_basis z i a), basisInsertion_basis]
  cases p.control k <;> rfl

end OptimalQLS.LowerBounds.Physical
