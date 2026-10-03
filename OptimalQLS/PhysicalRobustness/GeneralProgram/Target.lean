import OptimalQLS.PhysicalRobustness.GeneralProgram.Inputs
import OptimalQLS.Reduction.DirectExecution

/-! The actual truncated target has exact right-head support, before perturbation. -/
noncomputable section
set_option synthInstance.maxSize 16384
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
open scoped Classical Matrix.Norms.L2Operator
namespace OptimalQLS.PhysicalRobustness.GeneralProgram
open Matrix LowerBounds PhysicalPadding Reduction TransducerCompiler BinaryClock PolynomialTransform
open Refinement.PhysicalExecution

section FunctionalCalculus
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]

/-- Spectral cutoff inversion respects every genuine intertwiner. -/
theorem highInverse_intertwines (B : E →L[ℂ] E) (C : F →L[ℂ] F)
    (hB : B.toLinearMap.IsSymmetric) (hC : C.toLinearMap.IsSymmetric)
    (L : E →ₗ[ℂ] F) (hi : ∀ x,C (L x)=L (B x)) (δ : ℝ) (x : E) :
    highInverse C hC δ (L x)=L (highInverse B hB δ x) := by
  have heq : (highInverse C hC δ).toLinearMap.comp L=
      L.comp (highInverse B hB δ).toLinearMap := by
    apply (hB.eigenvectorBasis rfl).toBasis.ext
    intro i
    let v := hB.eigenvectorBasis rfl i
    let μ := hB.eigenvalues rfl i
    have hv : B v=(μ : ℂ) • v :=
      Module.End.mem_eigenspace_iff.mp (hB.hasEigenvector_eigenvectorBasis rfl i).1
    have hLv : C (L v)=(μ : ℂ) • L v := by rw [hi,hv,map_smul]
    change highInverse C hC δ (L v)=L (highInverse B hB δ v)
    rw [highInverse_apply_eigenvector C hC δ μ (L v) hLv,
      highInverse_apply_eigenvector B hB δ μ v hv,map_smul]
  exact congrArg (fun T : E →ₗ[ℂ] F=>T x) heq
end FunctionalCalculus

variable {D P Q : Type*} [Fintype D] [DecidableEq D] [Fintype P] [DecidableEq P]
  [Fintype Q] [DecidableEq Q]

theorem reindex_operator_apply (e : P ≃ Q) (B : Matrix P P ℂ) (v : EuclideanSpace ℂ P) :
    Matrix.toEuclideanCLM (n := Q) (𝕜 := ℂ) (B.submatrix e.symm e.symm)
      (coordinateIsometry e.toEmbedding v)=
    coordinateIsometry e.toEmbedding (Matrix.toEuclideanCLM (n := P) (𝕜 := ℂ) B v) := by
  ext q
  rw [DirectExecution.coordinate_equiv_apply]
  change ((B.submatrix e.symm e.symm)*ᵥWithLp.ofLp (coordinateIsometry e.toEmbedding v)) q=(B*ᵥWithLp.ofLp v) (e.symm q)
  have hv : WithLp.ofLp (coordinateIsometry e.toEmbedding v)=WithLp.ofLp v ∘ e.symm := by
    funext i
    exact DirectExecution.coordinate_equiv_apply e v i
  rw [hv,Matrix.submatrix_mulVec_equiv]
  simp only [Function.comp_def,Equiv.symm_symm,Equiv.symm_apply_apply]

theorem highInverse_reindex (e : P ≃ Q) (B : Matrix P P ℂ) (hB : B.IsHermitian)
    (δ : ℝ) (v : EuclideanSpace ℂ P) :
    highInverse (Matrix.toEuclideanCLM (n := Q) (𝕜 := ℂ) (B.submatrix e.symm e.symm))
      (matrixHermitian_symmetric _ (hB.submatrix _)) δ (coordinateIsometry e.toEmbedding v)=
    coordinateIsometry e.toEmbedding
      (highInverse (Matrix.toEuclideanCLM (n := P) (𝕜 := ℂ) B)
        (matrixHermitian_symmetric _ hB) δ v) :=
  highInverse_intertwines _ _ _ _ (coordinateIsometry e.toEmbedding).toLinearMap
    (reindex_operator_apply e B) δ v

variable {a n : ℕ}

def truncated (f : D ↪ Bits n) (UA : Matrix.unitaryGroup (Bits a × Bits n) ℂ)
    (b : EuclideanSpace ℂ D) (η : ℝ) : EuclideanSpace ℂ (Bits (n+1)) :=
  highInverse (Matrix.toEuclideanCLM (n := Bits (n+1)) (𝕜 := ℂ) (noisyMatrix UA))
    (matrixHermitian_symmetric _ (noisyMatrix_hermitian UA)) η
    (coordinateIsometry (dilationActive f) (WithLp.toLp 2 (source (WithLp.ofLp b))))

def sumOutput (n : ℕ) : EuclideanSpace ℂ (Bits (n+1)) →ₗᵢ[ℂ]
    EuclideanSpace ℂ (Fin (2^n) ⊕ Fin (2^n)) :=
  (coordinateIsometry (extractionCoordinates n).symm.toEmbedding).comp (outputCoordinates (n+1))

theorem sumOutput_apply (v : EuclideanSpace ℂ (Bits (n+1))) (i : Fin (2^n) ⊕ Fin (2^n)) :
    sumOutput n v i=v ((PhysicalAdapter.sumBits n).symm
      ((Equiv.sumCongr (HadamardClock.bitsFinEquiv n).symm (HadamardClock.bitsFinEquiv n).symm) i)) := by
  change coordinateIsometry (extractionCoordinates n).symm.toEmbedding (outputCoordinates (n+1) v) i=_
  rw [DirectExecution.coordinate_equiv_apply,outputCoordinates_apply]
  simp [extractionCoordinates]

theorem truncated_head_zero (f : D ↪ Bits n) (UA : Matrix.unitaryGroup (Bits a × Bits n) ℂ)
    (b : EuclideanSpace ℂ D) (η : ℝ) (i : Bits n) :
    truncated f UA b η ((PhysicalAdapter.sumBits n).symm (.inl i))=0 := by
  have hs : coordinateIsometry (dilationActive f) (WithLp.toLp 2 (source (WithLp.ofLp b)))=
      coordinateIsometry (PhysicalAdapter.sumBits n).symm.toEmbedding
        (WithLp.toLp 2 (source (WithLp.ofLp (coordinateIsometry f b)))) := by
    rw [dilationActive,coordinateIsometry_postEquiv,physical_source]
    ext j
    rw [DirectExecution.coordinate_equiv_apply]
    rfl
  unfold truncated noisyMatrix
  rw [hs]
  have ht := highInverse_reindex (PhysicalAdapter.sumBits n).symm
    (hermitianDilation (signalBlock (fun _ : Fin a=>false) UA))
    (hermitianDilation_hermitian _) η
    (WithLp.toLp 2 (source (WithLp.ofLp (coordinateIsometry f b))))
  simp only [Equiv.symm_symm] at ht
  rw [ht]
  rw [DirectExecution.coordinate_equiv_apply]
  simp only [Equiv.symm_symm,Equiv.apply_symm_apply]
  exact highInverse_dilation_left_zero _ η _ i

theorem sum_truncated_right (f : D ↪ Bits n) (UA : Matrix.unitaryGroup (Bits a × Bits n) ℂ)
    (b : EuclideanSpace ℂ D) (η : ℝ) :
    sumOutput n (NormedSpace.normalize (truncated f UA b η))=
      WithLp.toLp 2 (rightState (WithLp.ofLp
        (rightPart (sumOutput n (NormedSpace.normalize (truncated f UA b η)))))) := by
  ext i
  cases i with
  | inl i =>
    rw [sumOutput_apply]
    simp only [Equiv.sumCongr_apply,Sum.map_inl,rightState,Sum.elim_inl,Pi.zero_apply]
    simp only [NormedSpace.normalize,PiLp.smul_apply,truncated_head_zero,smul_zero]
  | inr i => rfl

end OptimalQLS.PhysicalRobustness.GeneralProgram
