import OptimalQLS.LowerBounds.TraceDistance
import OptimalQLS.OracleCircuit

/-! Actual oracle norm distance is preserved by controlled/adjoint query wiring. -/
noncomputable section
open scoped BigOperators Kronecker Matrix.Norms.L2Operator
namespace OptimalQLS.LowerBounds
open Matrix

variable {D E : Type*} [Fintype D] [DecidableEq D] [Fintype E] [DecidableEq E]

theorem euclidean_norm_comp_equiv (e : E ≃ D) (v : D → ℂ) :
    ‖WithLp.toLp 2 (v ∘ e)‖ = ‖WithLp.toLp 2 v‖ := by
  simp only [EuclideanSpace.norm_eq]
  congr 1
  exact Equiv.sum_comp e (fun i => ‖v i‖ ^ 2)

theorem matrix_norm_submatrix_equiv_le (A : Matrix D D ℂ) (e : E ≃ D) :
    ‖A.submatrix e e‖ ≤ ‖A‖ := by
  rw [← Matrix.l2_opNorm_toEuclideanCLM]
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg A)
  intro x
  change ‖WithLp.toLp 2 ((A.submatrix e e) *ᵥ (fun i => x i))‖ ≤ ‖A‖ * ‖x‖
  rw [Matrix.submatrix_mulVec_equiv, euclidean_norm_comp_equiv]
  have h := A.l2_opNorm_mulVec (WithLp.toLp 2 ((fun i => x i) ∘ e.symm))
  change ‖WithLp.toLp 2 (A *ᵥ ((fun i => x i) ∘ e.symm))‖ ≤
    ‖A‖ * ‖WithLp.toLp 2 ((fun i => x i) ∘ e.symm)‖ at h
  rw [euclidean_norm_comp_equiv] at h
  exact h

theorem matrix_norm_kronecker_le (A : Matrix D D ℂ) (B : Matrix E E ℂ) :
    ‖A ⊗ₖ B‖ ≤ ‖A‖ * ‖B‖ := by
  have heq : A ⊗ₖ B = (A ⊗ₖ (1 : Matrix E E ℂ)) * ((1 : Matrix D D ℂ) ⊗ₖ B) := by
    rw [← Matrix.mul_kronecker_mul]
    simp
  rw [heq]
  apply (Matrix.l2_opNorm_mul _ _).trans
  exact mul_le_mul (QuantumChannelStein.TensorNorm.kronecker_one_opNorm_le A)
    (QuantumChannelStein.TensorNorm.one_kronecker_opNorm_le B) (norm_nonneg _) (norm_nonneg _)

def controlProjection (r : ℕ) (control : Fin r → Bool) : Matrix (Fin r) (Fin r) ℂ :=
  Matrix.diagonal (fun i => if control i then 1 else 0)

theorem controlProjection_norm_le (r : ℕ) (control : Fin r → Bool) : ‖controlProjection r control‖ ≤ 1 := by
  rw [controlProjection, Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
  intro i
  cases control i <;> norm_num

theorem controlledUnitary_difference (r : ℕ) (control : Fin r → Bool)
    (U V : Matrix.unitaryGroup D ℂ) :
    (OptimalQLS.controlledUnitary r control U : Matrix (D × Fin r) (D × Fin r) ℂ) -
      (OptimalQLS.controlledUnitary r control V : Matrix (D × Fin r) (D × Fin r) ℂ) =
      ((U : Matrix D D ℂ) - (V : Matrix D D ℂ)) ⊗ₖ controlProjection r control := by
  ext i j
  rcases i with ⟨i, a⟩
  rcases j with ⟨j, b⟩
  by_cases hab : a = b
  · subst b
    cases hc : control a <;>
      simp [OptimalQLS.controlledUnitary, Matrix.blockDiagonal_apply, controlProjection, Matrix.kronecker_apply, hc]
  · simp [OptimalQLS.controlledUnitary, Matrix.blockDiagonal_apply, controlProjection,
      Matrix.kronecker_apply, hab]

theorem controlledUnitary_difference_norm_le (r : ℕ) (control : Fin r → Bool)
    (U V : Matrix.unitaryGroup D ℂ) :
    ‖(OptimalQLS.controlledUnitary r control U : Matrix (D × Fin r) (D × Fin r) ℂ) -
      (OptimalQLS.controlledUnitary r control V : Matrix (D × Fin r) (D × Fin r) ℂ)‖ ≤
      ‖(U : Matrix D D ℂ) - (V : Matrix D D ℂ)‖ := by
  rw [controlledUnitary_difference]
  exact (matrix_norm_kronecker_le _ _).trans
    (mul_le_of_le_one_right (norm_nonneg _) (controlProjection_norm_le r control))

theorem queryPort_difference_norm_le (port : OptimalQLS.QueryPort D E)
    (U V : Matrix.unitaryGroup D ℂ) :
    ‖(port.apply U : Matrix E E ℂ) - (port.apply V : Matrix E E ℂ)‖ ≤
      ‖(U : Matrix D D ℂ) - (V : Matrix D D ℂ)‖ := by
  let CU : Matrix (D × Fin port.multiplicity) (D × Fin port.multiplicity) ℂ :=
    OptimalQLS.controlledUnitary port.multiplicity port.control U
  let CV : Matrix (D × Fin port.multiplicity) (D × Fin port.multiplicity) ℂ :=
    OptimalQLS.controlledUnitary port.multiplicity port.control V
  have h := matrix_norm_submatrix_equiv_le (CU - CV) port.wiring.symm
  have heq : (CU - CV).submatrix port.wiring.symm port.wiring.symm =
      CU.submatrix port.wiring.symm port.wiring.symm - CV.submatrix port.wiring.symm port.wiring.symm := rfl
  rw [heq] at h
  exact h.trans (controlledUnitary_difference_norm_le _ _ U V)

/-- The original full-oracle distance bounds every allowed query type. -/
theorem queryPort_adjoint_difference_norm_le (port : OptimalQLS.QueryPort D E) (adjoint : Bool)
    (U V : Matrix.unitaryGroup D ℂ) :
    ‖(port.apply (if adjoint then U⁻¹ else U) : Matrix E E ℂ) -
      (port.apply (if adjoint then V⁻¹ else V) : Matrix E E ℂ)‖ ≤
      ‖(U : Matrix D D ℂ) - (V : Matrix D D ℂ)‖ := by
  cases adjoint
  · exact queryPort_difference_norm_le port U V
  · have h := queryPort_difference_norm_le port U⁻¹ V⁻¹
    simp only [Matrix.UnitaryGroup.inv_val, Matrix.star_eq_conjTranspose,
      ← Matrix.conjTranspose_sub, Matrix.l2_opNorm_conjTranspose] at h
    exact h

end OptimalQLS.LowerBounds
