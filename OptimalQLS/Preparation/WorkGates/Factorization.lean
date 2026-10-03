import OptimalQLS.Preparation.WorkGates.KernelFactors
import OptimalQLS.Preparation.WorkGates.PureLabelFactors

noncomputable section
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace OptimalQLS.Preparation.WorkGates
open Matrix
variable {S D : Type*} [Fintype S] [DecidableEq S] [Fintype D] [DecidableEq D]


omit [Fintype S] in
theorem signalProjector_entries (s₀ s t : S) (i j : D) :
    signalProjector s₀ (s,i) (t,j) =
      if (s,i)=(t,j) then (if s=s₀ then 1 else 0) else 0 := by
  simp [signalProjector, signalInjection, Matrix.mul_apply, Matrix.conjTranspose_apply,
    ite_and]
  split_ifs <;> simp_all

theorem kernelWork8_fiber (s₀ : S) {μ : ℝ} (hμ : 0<μ) :
    (kernelWork8 (signalProjector (D := D) s₀) (signalProjector_star s₀)
      (signalProjector_idempotent s₀) hμ).val =
      fiberMatrix (fun x : S × D =>
        kernelLabelMatrix (kernelMixA μ) (kernelMixB μ) (decide (x.1=s₀))) := by
  rw [kernelWork8_blocks]
  ext ⟨i,s,x⟩ ⟨j,t,y⟩
  simp only [Matrix.compRingEquiv_apply, Matrix.comp_apply, fiberMatrix]
  rw [kernelBlocks8_entries, kernelLabelMatrix_entries]
  by_cases hxy : (s,x)=(t,y)
  · obtain ⟨rfl,rfl⟩ := Prod.mk.inj hxy
    by_cases hs : s=s₀
    all_goals
      simp [Matrix.ite_apply, Matrix.one_apply, Matrix.smul_apply, Complex.real_smul,
        signalProjector_entries, hs] <;> norm_num
  · simp [Matrix.ite_apply, Matrix.one_apply, Matrix.smul_apply, Complex.real_smul,
      signalProjector_entries, hxy]

/-- Nine literal controlled one-qubit operations, in their execution order. -/
def workOperation (s₀ : S) {μ r : ℝ} (hμ : 0<μ) (hr : |r|<1) (k : Fin 9) :
    Matrix (Fin 8 × (S × D)) (Fin 8 × (S × D)) ℂ :=
  fiberMatrix (fun x => labelOperation hμ hr (decide (x.1=s₀)) k)


theorem preparationWork_factorization (s₀ : S) {μ r : ℝ} (hμ : 0<μ) (hr : |r|<1) :
    (preparationWork (signalProjector (D := D) s₀) (signalProjector_star s₀)
      (signalProjector_idempotent s₀) hμ hr).val =
      workOperation s₀ hμ hr 8 * workOperation s₀ hμ hr 7 *
      workOperation s₀ hμ hr 6 * workOperation s₀ hμ hr 5 *
      workOperation s₀ hμ hr 4 * workOperation s₀ hμ hr 3 *
      workOperation s₀ hμ hr 2 * workOperation s₀ hμ hr 1 *
      workOperation s₀ hμ hr 0 := by
  simp only [preparationWork, Submonoid.coe_mul, workOperation,
    mix8_fiber hμ hr (fun x : S × D => decide (x.1=s₀)),
    sign1_fiber hμ hr (fun x : S × D => decide (x.1=s₀)),
    swap14_fiber, kernelWork8_fiber, fiberMatrix_mul]
  congr 1
  funext x
  rw [← kernel_four_factorization hμ hr (decide (x.1=s₀)),
    ← swap_three_factorization hμ hr (decide (x.1=s₀))]
  simp only [Matrix.mul_assoc]

end OptimalQLS.Preparation.WorkGates
