import OptimalQLS.PhysicalRobustness.NoisyGeometry
import OptimalQLS.PhysicalRobustness.TruncatedStability

/-! Constant noisy refinement amplitude from the original physical promises. -/
noncomputable section
namespace OptimalQLS.PhysicalRobustness
open PhysicalPadding Geometry Preparation GraphEncoding Matrix TransducerCompiler
open scoped Matrix.Norms.L2Operator
variable {D P : Type*} [Fintype D] [DecidableEq D] [Fintype P] [DecidableEq P]

theorem noisy_refinement_geometry (f : D ↪ P)
    (A : Matrix D D ℂ) (hA : A.IsHermitian) (hunit : IsUnit A) (hAnorm : ‖A‖≤1)
    (B : Matrix P P ℂ) (hB : B.IsHermitian) (hBn : ‖B‖≤1)
    (b : EuclideanSpace ℂ D) (hb : ‖b‖=1)
    {κ δ ŝ : ℝ} (hκ : 2≤κ) (hδ : 0≤δ) (hinv : ‖Ring.inverse A‖≤κ)
    (hpert : ‖B-zeroExtend f A‖≤δ) (hsmall : κ*δ≤1/4)
    (hestlo : solutionScale 1 A b/2≤ŝ) (hesthi : ŝ≤2*solutionScale 1 A b) :
    let C := Matrix.toEuclideanCLM (n := P) (𝕜 := ℂ) B
    let hC := matrixHermitian_symmetric B hB
    let v := highInverse C hC δ (coordinateIsometry f b)
    let γ := ‖Alignment.kernelProjector (graphMatrix B (2*κ)) (graphInput (coordinateIsometry f b))‖
    v≠0 ∧ 0<γ ∧ γ≤3*‖v‖/(2*κ) ∧
      ∀ i, |hC.eigenvalues rfl i|≤δ ∨ κ⁻¹-δ≤|hC.eigenvalues rfl i| := by
  let J := coordinateIsometry f
  let T := Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) A
  let H := Matrix.toEuclideanCLM (n := P) (𝕜 := ℂ) (zeroExtend f A)
  let C := Matrix.toEuclideanCLM (n := P) (𝕜 := ℂ) B
  let hC := matrixHermitian_symmetric B hB
  let s := solutionScale 1 A b
  let w := ‖Ring.inverse (imaginaryShift C (2*κ)⁻¹) (J b)‖
  let σ := noisyAnalysisScale w ŝ
  have hk : 0<κ := by linarith
  have hTi : ‖Ring.inverse T‖≤κ := by rw [← Perturbation.toEuclideanCLM_inverse A hunit]; exact hinv
  have hTu : IsUnit T := hunit.map (Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ)).toMonoidHom
  have hH : H.toLinearMap.IsSymmetric := matrixHermitian_symmetric _ (zeroExtend_hermitian f A hA)
  have hCT : ‖C-H‖≤δ := by
    change ‖Matrix.toEuclideanCLM (n := P) (𝕜 := ℂ) B-
      Matrix.toEuclideanCLM (n := P) (𝕜 := ℂ) (zeroExtend f A)‖≤δ
    rw [← map_sub]
    exact hpert
  have hgap := noisy_spectral_gap H C hH hC hδ (zeroExtend_spectral_gap f A hunit hH hk hinv) hCT
  have hbn : b≠0 := by intro hz; simp [hz] at hb
  have hstate := truncated_solution_normalized_error J T hTu H C hC (zeroExtend_apply f A)
    hk hδ hTi hCT hsmall hgap b hbn
  have hnorm := (truncated_solution_norm_bounds J T hTu H C hC (zeroExtend_apply f A)
    hk hδ hTi hCT hsmall hgap b).1
  have hsEq : ‖Ring.inverse T b‖=s := by
    dsimp [s,solutionScale]
    rw [one_mul,Perturbation.toEuclideanCLM_inverse A hunit]
  rw [hsEq] at hnorm
  have hs : 1≤s := by
    have hn := T.le_opNorm (Ring.inverse T b)
    rw [Perturbation.apply_inverse T hTu,hb,hsEq] at hn
    have htn : ‖T‖≤1 := hAnorm
    have hm := mul_le_mul_of_nonneg_right htn (show 0≤s by rw [← hsEq]; positivity)
    nlinarith
  have hdt : δ/((2*κ)⁻¹)≤1/2 := by rw [div_inv_eq_mul]; nlinarith
  have hw : w≤3*s/2 := by
    have hu := noisy_regularized_solution_upper J T (matrixHermitian_symmetric A hA) hTu H C hC
      (zeroExtend_apply f A) hk.le (by positivity : 0<(2*κ)⁻¹) hδ hdt hTi hCT b
    rwa [hsEq] at hu
  have hσ : σ≤3*s/2 := max_le (by linarith) (max_le hw (by dsimp [s] at *; linarith))
  have hp := noisy_graph_promises f A hA hunit hAnorm B hB hBn b hb hκ hδ hinv hpert
    hsmall hestlo hesthi
  dsimp only at hp ⊢
  refine ⟨hstate.1,?_,?_,hgap⟩
  · have hσpos : 0<σ := by have h := hp.1.scale_ge_one; change 1≤σ at h; linarith
    have hpos : 0<σ^2/(2*(2*κ)^2) := by positivity
    have hlo := hp.2.2.1
    change σ^2/(2*(2*κ)^2)≤_ at hlo
    have hg : 0<‖Alignment.kernelProjector (graphMatrix B (2*κ)) (graphInput (J b))‖^2 :=
      hpos.trans_le hlo
    nlinarith [norm_nonneg (Alignment.kernelProjector (graphMatrix B (2*κ)) (graphInput (J b)))]
  · have hup := hp.2.2.2.1
    have hσ0 : 0≤σ := by have h := hp.1.scale_ge_one; change 1≤σ at h; linarith
    have hg : ‖Alignment.kernelProjector (graphMatrix B (2*κ)) (graphInput (J b))‖≤σ/(2*κ) := by
      apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
      rw [div_pow]
      exact hup
    apply hg.trans
    apply (div_le_div_iff_of_pos_right (by positivity : (0:ℝ)<2*κ)).mpr
    nlinarith

end OptimalQLS.PhysicalRobustness
