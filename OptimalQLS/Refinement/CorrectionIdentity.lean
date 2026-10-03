import OptimalQLS.Preparation.Coarse
import OptimalQLS.Geometry.GeneralCorrection

noncomputable section
namespace OptimalQLS.Refinement
open Matrix Preparation Alignment GraphEncoding Geometry
variable {D : Type*} [Fintype D] [DecidableEq D]

def graphCoordinate (g : Fin 4) : EuclideanSpace ℂ (Fin 4 × D) →L[ℂ] EuclideanSpace ℂ D :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => WithLp.toLp 2 (fun i => x (g,i))
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }

theorem graphCoordinate_norm_le (g : Fin 4) (x : EuclideanSpace ℂ (Fin 4 × D)) :
    ‖graphCoordinate g x‖≤‖x‖ :=
  coordinate_slice_norm_le ⟨fun i => (g,i),fun _ _ h => congrArg Prod.snd h⟩ x

theorem graphCoordinate_active (x : Block (EuclideanSpace ℂ D)) :
    graphCoordinate 2 (activeTriple x)=x 2 := by ext i; rfl

/-- The exact data component selected by the graph-label10 measurement. -/
theorem projectedGraph_coordinate (A : Matrix D D ℂ) (hA : A.IsHermitian)
    {κ : ℝ} (hκ : 0<κ) (b : EuclideanSpace ℂ D) :
    graphCoordinate 2 (Alignment.kernelProjector (graphMatrix A κ) (graphInput b)) =
      (κ⁻¹ : ℂ) • (Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) A)
        (Ring.inverse ((Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) A)^2+
          ((κ⁻¹)^2 : ℂ) • (1 : EuclideanSpace ℂ D →L[ℂ] EuclideanSpace ℂ D)) b) := by
  rw [graphInput_active,Alignment.kernelProjector,activeTriple_kernel_projection,
    (lemma42_exact_formulas _ (matrixHermitian_symmetric A hA) hκ b).1,graphCoordinate_active]
  rfl

/-- The exact correction operator on the original data Hilbert space. -/
def exactCorrection (A : EuclideanSpace ℂ D →L[ℂ] EuclideanSpace ℂ D) (κ : ℝ) :=
  (1/4 : ℂ) • ((1 : EuclideanSpace ℂ D →L[ℂ] EuclideanSpace ℂ D)+
    ((κ⁻¹)^2 : ℂ) • (Ring.inverse A)^2)

theorem exactCorrection_projectedGraph (A : Matrix D D ℂ) (hA : A.IsHermitian)
    (hunit : IsUnit (Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) A))
    {κ : ℝ} (hκ : 0<κ)
    (hAnorm : ‖Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) A‖≤1)
    (hinorm : ‖Ring.inverse (Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) A)‖≤κ)
    (b : EuclideanSpace ℂ D) :
    exactCorrection (Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) A) κ
      (graphCoordinate 2 (Alignment.kernelProjector (graphMatrix A κ) (graphInput b))) =
      ((1/(4*κ) : ℝ) : ℂ) • Ring.inverse (Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) A) b := by
  rw [projectedGraph_coordinate A hA hκ]
  have h := congrArg (fun T : EuclideanSpace ℂ D →L[ℂ] EuclideanSpace ℂ D => T b)
    (proposition53_identity _ (matrixHermitian_symmetric A hA) hunit hκ hAnorm hinorm)
  change ((1 : EuclideanSpace ℂ D →L[ℂ] EuclideanSpace ℂ D)+((κ⁻¹)^2 : ℂ) • (Ring.inverse (Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) A))^2)
    ((Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) A)
      (Ring.inverse ((Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) A)^2+((κ⁻¹)^2 : ℂ) • (1 : EuclideanSpace ℂ D →L[ℂ] EuclideanSpace ℂ D)) b)) =
    Ring.inverse (Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) A) b at h
  rw [exactCorrection,ContinuousLinearMap.smul_apply,map_smul,h,smul_smul]
  congr 1
  push_cast
  ring


/-- The exact graph postselection/correction identity, with the literal
normalization of the projected input and the literal normalized solution. -/
theorem exactCorrection_normalized_kernel (A : Matrix D D ℂ) (hA : A.IsHermitian)
    (hunit : IsUnit (Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) A))
    {κ : ℝ} (hκ : 0<κ)
    (hAnorm : ‖Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) A‖≤1)
    (hinorm : ‖Ring.inverse (Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) A)‖≤κ)
    (b : EuclideanSpace ℂ D) (hb : ‖b‖=1) (β : ℝ) :
    let H := graphMatrix A κ
    let γ := ‖Alignment.kernelProjector H (graphInput b)‖
    let v := Ring.inverse (Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) A) b
    exactCorrection (Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) A) κ
      (β • graphCoordinate 2 (normalizedProjectedInput H (graphInput b))) =
      (β*‖v‖/(4*κ*γ)) • NormedSpace.normalize v := by
  let T := Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) A
  let H := graphMatrix A κ
  let γ := ‖Alignment.kernelProjector H (graphInput b)‖
  let v := Ring.inverse T b
  let C := exactCorrection T κ
  have hbn : b≠0 := by intro hz; simp [hz] at hb
  have hv : v≠0 := Perturbation.inverse_apply_ne_zero T hunit hbn
  have hvn : ‖v‖≠0 := norm_ne_zero_iff.mpr hv
  have hp : C (graphCoordinate 2 (Alignment.kernelProjector H (graphInput b))) =
      (1/(4*κ) : ℝ) • v := by
    simpa only [RCLike.real_smul_eq_coe_smul (K := ℂ)] using
      exactCorrection_projectedGraph A hA hunit hκ hAnorm hinorm b
  have mapreal (L : EuclideanSpace ℂ D →L[ℂ] EuclideanSpace ℂ D) (r : ℝ) (x : EuclideanSpace ℂ D) :
      L (r • x)=r • L x := L.toLinearMap.map_smul_of_tower r x
  have hg : graphCoordinate 2 (normalizedProjectedInput H (graphInput b)) =
      γ⁻¹ • graphCoordinate 2 (Alignment.kernelProjector H (graphInput b)) :=
    (graphCoordinate (D := D) 2).toLinearMap.map_smul_of_tower _ _
  change C (β • graphCoordinate 2 (normalizedProjectedInput H (graphInput b))) =
    (β*‖v‖/(4*κ*γ)) • NormedSpace.normalize v
  rw [hg,mapreal,mapreal,hp,NormedSpace.normalize,smul_smul,smul_smul,smul_smul]
  congr 1
  field_simp

/-- The exact geometric projection bound yields the stated correction amplitude. -/
theorem correction_amplitude_lower {β s κ γ : ℝ} (hβ : 1/32≤β) (hs : 0<s)
    (hκ : 0<κ) (hγ : 0<γ) (hγbound : γ≤s/κ) :
    1/128≤β*s/(4*κ*γ) := by
  have hkg : κ*γ≤s := by
    have h := (le_div_iff₀ hκ).mp hγbound
    nlinarith
  apply (le_div_iff₀ (by positivity : 0<4*κ*γ)).mpr
  nlinarith

end OptimalQLS.Refinement
