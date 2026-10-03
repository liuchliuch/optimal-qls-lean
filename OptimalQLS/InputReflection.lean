import OptimalQLS.FractionalTransducer
import Mathlib.Data.Matrix.Basis

/-! # Exact input-reflection circuit and its separate oracle charges

This constructs the two vector-oracle calls explicitly. Synthesis of the
basis-state phase test into O(log d) elementary gates remains separate.
-/
noncomputable section
namespace OptimalQLS
open Matrix
variable {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]

/-- Query without a control and without extra workspace. -/
def identityQueryPort (S : Type*) : QueryPort S S where
  multiplicity := 1
  wiring := Equiv.prodUnique S (Fin 1)
  control := fun _ => true

theorem identityQueryPort_apply (U : Matrix.unitaryGroup S ℂ) :
    (identityQueryPort S).apply U = U := by
  apply Subtype.ext
  ext i j
  simp [identityQueryPort, QueryPort.apply, rewireUnitary, controlledUnitary,
    Matrix.submatrix_apply, Matrix.blockDiagonal_apply]

/-- Reflection fixing one computational basis state and negating all others. -/
def basisStateReflection (i₀ : S) : Matrix.unitaryGroup S ℂ :=
  ⟨Matrix.diagonal (fun i => if i = i₀ then (1 : ℂ) else -1), by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
      Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
    have h : (fun i => (if i = i₀ then (1 : ℂ) else -1) *
        star (if i = i₀ then (1 : ℂ) else -1)) = 1 := by
      funext i
      split_ifs <;> simp
    simp only [Pi.star_apply]
    rw [h]
    exact Matrix.diagonal_one⟩

def preparedReflection (Ub : Matrix.unitaryGroup S ℂ) (i₀ : S) :
    Matrix.unitaryGroup S ℂ := Ub * basisStateReflection i₀ * Ub⁻¹


omit [Fintype A] [DecidableEq A] in
theorem basisStateReflection_matrix (i₀ : S) :
    (basisStateReflection i₀ : Matrix S S ℂ) =
      (2 : ℂ) • Matrix.single i₀ i₀ 1 - 1 := by
  ext i j
  by_cases hij : i = j
  · subst j
    by_cases hi : i = i₀
    · subst i
      norm_num [basisStateReflection, Matrix.single]
    · simp [basisStateReflection, Matrix.single, hi, Ne.symm hi]
  · have hh : ¬ (i₀ = i ∧ i₀ = j) := fun h => hij (h.1.symm.trans h.2)
    simp [basisStateReflection, Matrix.single, hij, hh]

/-- The conjugated phase test is exactly 2|b><b|-I, where b is the prepared
column of the full oracle. No action on the other columns is assumed. -/
theorem preparedReflection_matrix (Ub : Matrix.unitaryGroup S ℂ) (i₀ : S) :
    (preparedReflection Ub i₀ : Matrix S S ℂ) =
      (2 : ℂ) • (Matrix.of (fun i j => Ub i i₀ * star (Ub j i₀))) - 1 := by
  have hcol : (Ub : Matrix S S ℂ) * Matrix.single i₀ i₀ 1 *
      (Ub : Matrix S S ℂ)ᴴ = Matrix.of (fun i j => Ub i i₀ * star (Ub j i₀)) := by
    ext i j
    change (∑ k, (((Ub : Matrix S S ℂ) * (Matrix.single i₀ i₀ (1 : ℂ) : Matrix S S ℂ)) : Matrix S S ℂ) i k *
      star (Ub j k)) = Ub i i₀ * star (Ub j i₀)
    have hm (k : S) : (((Ub : Matrix S S ℂ) * (Matrix.single i₀ i₀ (1 : ℂ) : Matrix S S ℂ)) : Matrix S S ℂ) i k =
        if k = i₀ then Ub i i₀ else 0 := by
      by_cases hk : k = i₀
      · subst k; simp
      · rw [Matrix.mul_single_apply_of_ne 1 i₀ i₀ i k hk]
        simp [hk]
    simp_rw [hm]
    simp
  have hU : (Ub : Matrix S S ℂ) * (Ub : Matrix S S ℂ)ᴴ = 1 := Ub.property.2
  change (Ub : Matrix S S ℂ) * (basisStateReflection i₀ : Matrix S S ℂ) *
    (Ub : Matrix S S ℂ)ᴴ = _
  rw [basisStateReflection_matrix, Matrix.mul_sub, Matrix.sub_mul,
    mul_smul_comm, smul_mul_assoc, Matrix.mul_one, hU, hcol]

/-- Execution order is Ub†, the basis-state phase test, Ub. -/
def inputReflectionCircuit (i₀ : S) : QueryCircuit A S S :=
  [.vectorCall (identityQueryPort S) true,
   .work (basisStateReflection i₀),
   .vectorCall (identityQueryPort S) false]

theorem inputReflectionCircuit_eval (i₀ : S) (UA : Matrix.unitaryGroup A ℂ)
    (Ub : Matrix.unitaryGroup S ℂ) :
    (inputReflectionCircuit (A := A) i₀).eval UA Ub = preparedReflection Ub i₀ := by
  simp [inputReflectionCircuit, QueryCircuit.eval, QueryInstruction.eval,
    identityQueryPort_apply, preparedReflection, mul_assoc]

omit [Fintype A] [DecidableEq A] in
theorem inputReflectionCircuit_counts (i₀ : S) :
    (inputReflectionCircuit (A := A) i₀).matrixQueries = 0 ∧
    (inputReflectionCircuit (A := A) i₀).vectorQueries = 2 := by
  simp [inputReflectionCircuit, QueryCircuit.matrixQueries, QueryCircuit.vectorQueries]

/-- Swapping public and private copies is the explicit work operation for
the reflection transducer in Proposition 4.5. -/
def swapPublicPrivate : Matrix.unitaryGroup (S ⊕ S) ℂ :=
  ⟨Matrix.fromBlocks 0 1 1 0, by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
      Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply]
    simp only [Matrix.conjTranspose_zero, Matrix.conjTranspose_one, Matrix.mul_zero,
      Matrix.mul_one, zero_add, add_zero, Matrix.fromBlocks_one]⟩

def inputReflectionTransducer (Ub : Matrix.unitaryGroup S ℂ) (i₀ : S) :
    Matrix.unitaryGroup (S ⊕ S) ℂ := swapPublicPrivate * privateOracle (preparedReflection Ub i₀)

/-- Every private input vector is restored exactly by the actual unitary. -/
theorem inputReflectionTransducer_identity (Ub : Matrix.unitaryGroup S ℂ) (i₀ : S)
    (ξ : S → ℂ) :
    (inputReflectionTransducer Ub i₀ : Matrix (S ⊕ S) (S ⊕ S) ℂ) *ᵥ Sum.elim ξ ξ =
      Sum.elim ((preparedReflection Ub i₀ : Matrix S S ℂ) *ᵥ ξ) ξ := by
  change (Matrix.fromBlocks 0 1 1 0 * Matrix.fromBlocks 1 0 0
    (preparedReflection Ub i₀ : Matrix S S ℂ)) *ᵥ _ = _
  rw [← Matrix.mulVec_mulVec, Matrix.fromBlocks_mulVec, Matrix.fromBlocks_mulVec]
  simp

end OptimalQLS
