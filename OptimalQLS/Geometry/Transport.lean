import OptimalQLS.Geometry.Correction
import OptimalQLS.Geometry.SpectralGap
import OptimalQLS.Perturbation.Lemma71

noncomputable section
namespace OptimalQLS.Geometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]
variable {ι : Type*} [Fintype ι]

abbrev Block (E : Type*) := PiLp 2 (fun _ : Fin 3 => E)

def blockTriple (x y z : E) : Block E := WithLp.toLp 2 ![x,y,z]

/-- The canonical block extension of the orthonormal coordinate isometry. -/
def tripleCoordinates (U : E ≃ₗᵢ[ℂ] Vec ι) : Block E ≃ₗᵢ[ℂ] Triple ι where
  toFun x := WithLp.toLp 2 (fun ji => U (x ji.1) ji.2)
  invFun x := WithLp.toLp 2 (fun j => U.symm (WithLp.toLp 2 (fun i => x (j,i))))
  left_inv x := by ext j; simp
  right_inv x := by ext ⟨j,i⟩; simp
  map_add' x y := by ext ⟨j,i⟩; simp
  map_smul' c x := by ext ⟨j,i⟩; simp
  norm_map' x := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [EuclideanSpace.norm_sq_eq, PiLp.norm_sq_eq_of_L2]
    simp only [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro j _
    change (∑ i, ‖U (x j) i‖ ^ 2) = ‖x j‖ ^ 2
    rw [← EuclideanSpace.norm_sq_eq, U.norm_map]

@[simp] theorem tripleCoordinates_apply (U : E ≃ₗᵢ[ℂ] Vec ι) (x : Block E)
    (j : Fin 3) (i : ι) : tripleCoordinates U x (j,i) = U (x j) i := rfl

@[simp] theorem tripleCoordinates_blockTriple (U : E ≃ₗᵢ[ℂ] Vec ι) (x y z : E) :
    tripleCoordinates U (blockTriple x y z) = triple (U x) (U y) (U z) := by
  ext ⟨j,i⟩; fin_cases j <;> rfl

/-- The paper's auxiliary block operator in the original Hilbert space. -/
def blockAuxiliary (A : E →L[ℂ] E) (t : ℝ) : Block E →L[ℂ] Block E :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => WithLp.toLp 2 ![A (x 1) - (t : ℂ) • x 2,
        A (x 0), -(t : ℂ) • x 0]
      map_add' := by
        intros; ext j; fin_cases j <;> simp [smul_add, map_add, sub_add_sub_comm]
      map_smul' := by
        intros; ext j; fin_cases j <;> simp [smul_sub, smul_smul, mul_comm] <;> rw [RCLike.real_smul_eq_coe_smul (K := ℂ), smul_smul] <;> rfl }

/-- The auxiliary matrix really is blockwise unitarily equivalent to our
spectral-coordinate construction. -/
theorem tripleCoordinates_intertwines (U : E ≃ₗᵢ[ℂ] Vec ι)
    (A : E →L[ℂ] E) (a : ι → ℝ)
    (hdiag : ∀ x i, U (A x) i = (a i : ℂ) * U x i) (t : ℝ) (x : Block E) :
    tripleCoordinates U (blockAuxiliary A t x) = auxiliary a t (tripleCoordinates U x) := by
  ext ⟨j,i⟩
  fin_cases j <;> simp [blockAuxiliary, hdiag]
  all_goals
    simpa using congrArg (fun v : Vec ι => v i) (U.map_smul (t : ℂ) (x _))

/-- An arbitrary finite-dimensional Hermitian operator has the real
orthonormal coordinates needed by the concrete development. -/
theorem exists_real_spectral_coordinates (A : E →L[ℂ] E)
    (hA : A.toLinearMap.IsSymmetric) :
    ∃ (U : E ≃ₗᵢ[ℂ] Vec (Fin (Module.finrank ℂ E))) (a : Fin (Module.finrank ℂ E) → ℝ),
      ∀ x i, U (A x) i = (a i : ℂ) * U x i := by
  refine ⟨(hA.eigenvectorBasis rfl).repr, hA.eigenvalues rfl, ?_⟩
  exact fun x i => hA.eigenvectorBasis_apply_self_apply rfl x i

/-- Original operator-norm promises imply the coordinatewise spectral
promises. These bounds are proved, not supplied as extra geometric axioms. -/
theorem spectral_coordinate_bounds (A : E →L[ℂ] E)
    (hA : A.toLinearMap.IsSymmetric) (hunit : IsUnit A) {κ : ℝ}
    (hκ : 0 < κ) (hAnorm : ‖A‖ ≤ 1) (hinv : ‖Ring.inverse A‖ ≤ κ)
    (i : Fin (Module.finrank ℂ E)) :
    κ⁻¹ ≤ |hA.eigenvalues rfl i| ∧ |hA.eigenvalues rfl i| ≤ 1 := by
  let v := hA.eigenvectorBasis rfl i
  let a := hA.eigenvalues rfl i
  have hv : ‖v‖ = 1 := (hA.eigenvectorBasis rfl).orthonormal.norm_eq_one i
  have heig : A v = (a : ℂ) • v := by
    exact Module.End.mem_eigenspace_iff.mp (hA.hasEigenvector_eigenvectorBasis rfl i).1
  have hnorm : ‖A v‖ = |a| := by
    rw [heig, norm_smul, hv, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have hup : |a| ≤ 1 := by
    have h := A.le_opNorm v
    rw [hv, mul_one, hnorm] at h
    exact h.trans hAnorm
  have hid : Ring.inverse A (A v) = v := by
    have h := congrArg (fun T : E →L[ℂ] E => T v) (Ring.inverse_mul_cancel A hunit)
    simpa using h
  have hlow : 1 ≤ κ * |a| := by
    calc
      1 = ‖Ring.inverse A (A v)‖ := by rw [hid, hv]
      _ ≤ ‖Ring.inverse A‖ * ‖A v‖ := (Ring.inverse A).le_opNorm _
      _ ≤ κ * |a| := by rw [hnorm]; exact mul_le_mul_of_nonneg_right hinv (abs_nonneg _)
  refine ⟨?_, hup⟩
  rw [inv_eq_one_div]
  apply (div_le_iff₀ hκ).mpr
  simpa [mul_comm] using hlow

end OptimalQLS.Geometry
