import QuantumChannelStein.Testing

/-!
# Arbitrary finite-reference acceptance amplitudes

The reassociation maps below explicitly identify `R ⊗ (B ⊗ E)` with
`(R ⊗ B) ⊗ E`. Reference extension is proved to leave the original
Stinespring error bound unchanged, rather than assumed as a hypothesis.
-/
set_option maxHeartbeats 800000
noncomputable section
namespace QuantumChannelStein
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker
open Matrix WithLp

namespace ReferenceAcceptance

variable {r a b e f : Type*} [Fintype r] [Fintype a] [Fintype b]
  [Fintype e] [Fintype f]

/-- Canonical reassociation of the output of a reference-extended dilation. -/
def reassociate (x : EuclideanSpace ℂ (r × (b × e))) :
    EuclideanSpace ℂ ((r × b) × e) :=
  toLp 2 (fun p => x (p.1.1, (p.1.2, p.2)))

@[simp] theorem reassociate_norm (x : EuclideanSpace ℂ (r × (b × e))) :
    ‖reassociate x‖ = ‖x‖ := by
  simp only [EuclideanSpace.norm_eq, reassociate, PiLp.toLp_apply,
    Fintype.sum_prod_type]

@[simp] theorem reassociate_sub (x y : EuclideanSpace ℂ (r × (b × e))) :
    reassociate (x - y) = reassociate x - reassociate y := by
  ext p
  rfl

variable [DecidableEq r] [DecidableEq a] [DecidableEq b]
  [DecidableEq e] [DecidableEq f]

/-- Identity-reference extension followed by canonical output reassociation. -/
def dilation (V : Matrix (b × e) a ℂ) : Matrix ((r × b) × e) (r × a) ℂ :=
  fun p q => ((1 : Matrix r r ℂ) ⊗ₖ V) (p.1.1, (p.1.2, p.2)) q

omit [DecidableEq b] [DecidableEq e] in
@[simp] theorem dilation_map (V : Matrix (b × e) a ℂ)
    (ψ : EuclideanSpace ℂ (r × a)) :
    TensorNorm.matrixMap (dilation V) ψ =
      reassociate (TensorNorm.matrixMap ((1 : Matrix r r ℂ) ⊗ₖ V) ψ) := by
  ext p
  rfl

omit [Fintype r] [Fintype a] [Fintype b] [Fintype e]
  [DecidableEq a] [DecidableEq b] [DecidableEq e] in
@[simp] theorem dilation_sub (V W : Matrix (b × e) a ℂ) :
    dilation (r := r) (V - W) = dilation V - dilation W := by
  ext p q
  simp [dilation, mul_sub]

omit [Fintype a] [Fintype e] [DecidableEq a] [DecidableEq e] [DecidableEq f] in
/-- Reassociation intertwines environment comparison and reference extension. -/
theorem dilation_environment (C : Matrix e f ℂ) (V : Matrix (b × f) a ℂ) :
    dilation (r := r) (((1 : Matrix b b ℂ) ⊗ₖ C) * V) =
      ((1 : Matrix (r × b) (r × b) ℂ) ⊗ₖ C) * dilation V := by
  ext ⟨⟨i, j⟩, k⟩ ⟨l, s⟩
  simp [dilation, Matrix.mul_apply, Matrix.one_apply, Fintype.sum_prod_type]
  split_ifs with h
  · subst l
    simp
  · simp [h]

omit [DecidableEq b] [DecidableEq e] in
/-- The reassociated reference extension never increases the L2 operator norm. -/
theorem dilation_opNorm_le (V : Matrix (b × e) a ℂ) :
    ‖dilation (r := r) V‖ ≤ ‖V‖ := by
  rw [Matrix.l2_opNorm_def]
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg V)
  intro ψ
  change ‖TensorNorm.matrixMap (dilation V) ψ‖ ≤ _
  rw [dilation_map, reassociate_norm]
  exact TensorNorm.one_kronecker_mulVec_norm_le V ψ

omit [DecidableEq b] [DecidableEq e] in
/-- A nonempty finite reference preserves the dilation's L2 operator norm
exactly, even after the canonical reassociation. -/
theorem dilation_opNorm [Nonempty r] (V : Matrix (b × e) a ℂ) :
    ‖dilation (r := r) V‖ = ‖V‖ := by
  apply le_antisymm (dilation_opNorm_le V)
  rw [← TensorNorm.one_kronecker_opNorm (r := r) V, Matrix.l2_opNorm_def]
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro ψ
  change ‖TensorNorm.matrixMap ((1 : Matrix r r ℂ) ⊗ₖ V) ψ‖ ≤ _
  rw [← reassociate_norm, ← dilation_map]
  exact (TensorNorm.matrixMap (dilation V)).le_opNorm ψ

omit [DecidableEq e] in
/-- The pure reference-assisted input error is controlled by the original,
unextended Stinespring error. No bound on the extended error is assumed. -/
theorem dilation_error_le (VN : Matrix (b × e) a ℂ)
    (VM : Matrix (b × f) a ℂ) (C : Matrix e f ℂ)
    (ψ : EuclideanSpace ℂ (r × a)) (hψ : ‖ψ‖ ≤ 1) :
    ‖TensorNorm.matrixMap (dilation VN) ψ -
      TensorNorm.matrixMap ((1 : Matrix (r × b) (r × b) ℂ) ⊗ₖ C)
        (TensorNorm.matrixMap (dilation VM) ψ)‖ ≤
      ‖VN - ((1 : Matrix b b ℂ) ⊗ₖ C) * VM‖ := by
  have h := (TensorNorm.matrixMap
    (dilation (r := r) (VN - ((1 : Matrix b b ℂ) ⊗ₖ C) * VM))).le_of_opNorm_le_of_le
    (dilation_opNorm_le (r := r) (VN - ((1 : Matrix b b ℂ) ⊗ₖ C) * VM)) hψ
  simpa only [dilation_sub, dilation_environment, TensorNorm.matrixMap_sub,
    TensorNorm.matrixMap_mul, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.comp_apply, mul_one] using h

/-- Partial trace for arbitrary finite output and environment index types. -/
def traceEnvironment {o d : Type*} [Fintype d]
    (X : Matrix (o × d) (o × d) ℂ) : Matrix o o ℂ :=
  fun i j => ∑ k, X (i, k) (j, k)

/-- The test probability of a possibly unnormalized dilation vector. -/
def acceptance {o d : Type*} [Fintype o] [Fintype d]
    (T : Matrix o o ℂ) (x : EuclideanSpace ℂ (o × d)) : ℝ :=
  (T * traceEnvironment (pureMatrix x)).trace.re

/-- The duality between partial trace and an identity extension of the test. -/
theorem traceEnvironment_duality {o d : Type*} [Fintype o] [Fintype d]
    [DecidableEq d] (T : Matrix o o ℂ)
    (X : Matrix (o × d) (o × d) ℂ) :
    (T * traceEnvironment X).trace =
      (((T ⊗ₖ (1 : Matrix d d ℂ)) * X).trace) := by
  simp [traceEnvironment, Matrix.trace, Matrix.mul_apply,
    Matrix.one_apply, Fintype.sum_prod_type, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]

/-- A finite-type binary test and its positive square root are contractions. -/
theorem sqrt_opNorm_le_one {o : Type*} [Fintype o] [DecidableEq o]
    (T : Matrix o o ℂ) (hT : T.PosSemidef) (hTc : (1 - T).PosSemidef) :
    ‖CFC.sqrt T‖ ≤ 1 := by
  letI : CStarAlgebra (Matrix o o ℂ) := CStarAlgebra.mk
  have hn : ‖T‖ ≤ 1 :=
    (CStarAlgebra.norm_le_one_iff_of_nonneg T hT.nonneg).mpr hTc
  have hs : (CFC.sqrt T).PosSemidef := (CFC.sqrt_nonneg T).posSemidef
  have hsq : ‖CFC.sqrt T‖ * ‖CFC.sqrt T‖ = ‖T‖ := by
    rw [← Matrix.l2_opNorm_conjTranspose_mul_self, hs.isHermitian.eq,
      CFC.sqrt_mul_sqrt_self T hT.nonneg]
  have hp := norm_nonneg (CFC.sqrt T)
  nlinarith

/-- Born's rule identifies the partial-trace probability with the squared norm
of the test square root, without an assumption on scalar amplitudes. -/
theorem acceptance_eq_norm_sq {o d : Type*} [Fintype o] [Fintype d]
    [DecidableEq o] [DecidableEq d] (T : Matrix o o ℂ) (hT : T.PosSemidef)
    (x : EuclideanSpace ℂ (o × d)) :
    acceptance T x =
      ‖TensorNorm.matrixMap (CFC.sqrt T ⊗ₖ (1 : Matrix d d ℂ)) x‖ ^ 2 := by
  unfold acceptance
  rw [traceEnvironment_duality, TensorNorm.matrixMap_apply, ← trace_test_pure_eq_norm_sq]
  have hs : (CFC.sqrt T).PosSemidef := (CFC.sqrt_nonneg T).posSemidef
  rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    hs.isHermitian.eq, ← Matrix.mul_kronecker_mul,
    CFC.sqrt_mul_sqrt_self T hT.nonneg, Matrix.one_mul]

/-- Square root of the Born acceptance probability is exactly the acceptance
amplitude. -/
theorem sqrt_acceptance {o d : Type*} [Fintype o] [Fintype d]
    [DecidableEq o] [DecidableEq d] (T : Matrix o o ℂ) (hT : T.PosSemidef)
    (x : EuclideanSpace ℂ (o × d)) :
    Real.sqrt (acceptance T x) =
      ‖TensorNorm.matrixMap (CFC.sqrt T ⊗ₖ (1 : Matrix d d ℂ)) x‖ := by
  rw [acceptance_eq_norm_sq T hT, Real.sqrt_sq (norm_nonneg _)]

/-- The arbitrary finite-reference, pure-input acceptance-amplitude statement
of Lemma 3.4. The error is the original unextended dilation error, and the test
may be any binary effect jointly on the reference and channel output. -/
theorem pure_reference_acceptance_le
    (T : Matrix (r × b) (r × b) ℂ)
    (hT : T.PosSemidef) (hTc : (1 - T).PosSemidef)
    (VN : Matrix (b × e) a ℂ) (VM : Matrix (b × f) a ℂ) (C : Matrix e f ℂ)
    (ψ : EuclideanSpace ℂ (r × a)) (hψ : ‖ψ‖ ≤ 1) :
    Real.sqrt (acceptance T (TensorNorm.matrixMap (dilation VN) ψ)) ≤
      ‖C‖ * Real.sqrt (acceptance T (TensorNorm.matrixMap (dilation VM) ψ)) +
        ‖VN - ((1 : Matrix b b ℂ) ⊗ₖ C) * VM‖ := by
  rw [sqrt_acceptance T hT, sqrt_acceptance T hT]
  exact TensorNorm.tensor_amplitude_le (CFC.sqrt T) C _ _ _
    (sqrt_opNorm_le_one T hT hTc) (dilation_error_le VN VM C ψ hψ)

end ReferenceAcceptance
end QuantumChannelStein
