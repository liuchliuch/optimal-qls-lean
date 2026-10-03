import OptimalQLS.PolynomialTransform.GraphComposition
import OptimalQLS.PolynomialTransform.GraphPaperParameters

/-! # Polynomial and kernel guarantees for the shared-scratch graph compiler -/
noncomputable section
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 800000
namespace OptimalQLS.PolynomialTransform
open Matrix Polynomial DirtyAncilla
open scoped Matrix.Norms.L2Operator
variable {D B : Type*} [Fintype D] [DecidableEq D] [Fintype B] [DecidableEq B]

theorem binaryGraphOracle_exact [Nonempty D] (a : ℕ) (κ : ℝ) (hκ : 0 < κ)
    (U : Matrix.unitaryGroup ((Fin a → Bool) × D) ℂ) (A : Matrix D D ℂ)
    (hA : A.IsHermitian) (hU : IsBlockEncoding (fun _ : Fin a => false) 1 0 U A) :
    IsBlockEncoding (fun _ : Fin (a+4) => false) 1 0 (binaryGraphOracle a κ hκ U)
      (GraphEncoding.normalizedGraph A κ) := by
  have h := normalize_exact_encoding _ (GraphEncoding.physicalEncoding κ hκ U) _
    (GraphEncoding.physicalEncoding_exact κ hκ _ U A hA hU)
  have hb := signalBlock_relabel (graphSignalBits a)
    (GraphEncoding.physicalSignalZero (fun _ : Fin a => false))
    (GraphEncoding.physicalEncoding κ hκ U)
  rw [graphSignalBits_zero] at hb
  simpa only [IsBlockEncoding,binaryGraphOracle,hb,GraphEncoding.normalizedGraph] using h

/-- General polynomial endpoint of the explicit graph-call compiler. -/
theorem graphPolynomial_from_masked_calls [Nonempty D] (a : ℕ) (κ : ℝ) (hκ : 0 < κ)
    (p : ℝ[X]) (hp : Function.Even p.eval) (hbound : ∀ x : ℝ, |x| ≤ 1 → |p.eval x| ≤ 1)
    (K : ℕ)
    (calls : Bool × Bool → ElementaryCircuit ((Fin a → Bool) × D) B GraphLocalWire ((Fin a → Bool) × D))
    (hq : ∀ mask, (calls mask).toQuery.matrixQueries=2 ∧ (calls mask).toQuery.vectorQueries=0)
    (hg : ∀ mask, (calls mask).workGates ≤ K)
    (hcall : ∀ mask (U : Matrix.unitaryGroup ((Fin a → Bool) × D) ℂ) (Ub : Matrix.unitaryGroup B ℂ),
      ((calls mask).toQuery.eval U Ub).val*basisInsertion graphLocalClean=
        basisInsertion graphLocalClean*
          ((GraphEncoding.maskedGraphPort (GraphEncoding.PhysicalSignal (Fin a → Bool) × (Fin 4 × D)) mask).apply
            (GraphEncoding.physicalEncoding κ hκ U)).val) :
    ∃ out : GraphAttachedCircuit a D B,
      (out.toQuery (GraphAttachedGate.eval a)).matrixQueries ≤ 8*p.natDegree ∧
      (out.toQuery (GraphAttachedGate.eval a)).vectorQueries=0 ∧
      out.workGates ≤ (6248*(a+5)+4*K)*(p.natDegree+1) ∧
      ∀ (U : Matrix.unitaryGroup ((Fin a → Bool) × D) ℂ) (Ub : Matrix.unitaryGroup B ℂ)
        (A : Matrix D D ℂ), A.IsHermitian → IsBlockEncoding (fun _ : Fin a => false) 1 0 U A →
        IsBlockEncoding (physicalZero (a+4)) 1 0 ((out.toQuery (GraphAttachedGate.eval a)).eval U Ub)
          (Polynomial.aeval (GraphEncoding.normalizedGraph A κ) (liftReal p)) := by
  obtain ⟨z₀,zs,hlen,henc⟩ := bounded_even_exact_encoding (D := Fin 4 × D)
    (fun _ : Fin (a+4) => false) p hp hbound
  obtain ⟨out,hm,hv,hgates,he⟩ := graphTransform_from_masked_calls a κ hκ z₀ zs K calls hq hg hcall
  refine ⟨out,by omega,hv,hgates.trans ?_,?_⟩
  · exact Nat.mul_le_mul_left _ (by omega)
  · intro U Ub A hA hU
    have hb := henc (binaryGraphOracle a κ hκ U) (GraphEncoding.normalizedGraph A κ)
      (GraphEncoding.normalizedGraph_hermitian A hA κ) (binaryGraphOracle_exact a κ hκ U A hA hU)
    have hc := signalBlock_of_clean_intertwines (physicalCleanSignal (a+4))
      (physicalCleanSignal_injective (a+4)) ((false,false),fun _ : Fin (a+4) => false)
      ((out.toQuery (GraphAttachedGate.eval a)).eval U Ub).val
      (boundedTransformUnitary (fun _ : Fin (a+4) => false) (binaryGraphOracle a κ hκ U) z₀ zs).val
      (he U Ub)
    rw [physicalClean_zero] at hc
    simpa only [IsBlockEncoding,hc] using hb

/-- The only parameters here are the actual masked-call lists and their
proved semantics/counts; the final paper endpoint instantiates these lists. -/
theorem graphKernel_from_masked_calls [Nonempty D] (a : ℕ)
    {κ η : ℝ} (hκ : 2 ≤ κ) (hη0 : 0 < η) (hη1 : η < 1/2) (K : ℕ)
    (calls : Bool × Bool → ElementaryCircuit ((Fin a → Bool) × D) B GraphLocalWire ((Fin a → Bool) × D))
    (hq : ∀ mask, (calls mask).toQuery.matrixQueries=2 ∧ (calls mask).toQuery.vectorQueries=0)
    (hg : ∀ mask, (calls mask).workGates ≤ K)
    (hcall : ∀ mask (U : Matrix.unitaryGroup ((Fin a → Bool) × D) ℂ) (Ub : Matrix.unitaryGroup B ℂ),
      ((calls mask).toQuery.eval U Ub).val*basisInsertion graphLocalClean=
        basisInsertion graphLocalClean*
          ((GraphEncoding.maskedGraphPort (GraphEncoding.PhysicalSignal (Fin a → Bool) × (Fin 4 × D)) mask).apply
            (GraphEncoding.physicalEncoding κ (by linarith) U)).val) :
    ∃ out : GraphAttachedCircuit a D B,
      ((out.toQuery (GraphAttachedGate.eval a)).matrixQueries : ℝ) < 96*κ*Real.log (1/η) ∧
      (out.toQuery (GraphAttachedGate.eval a)).vectorQueries=0 ∧
      (out.workGates : ℝ) ≤ (6248*(a+5)+4*K)*(12*κ*Real.log (1/η)+1) ∧
      ∀ (U : Matrix.unitaryGroup ((Fin a → Bool) × D) ℂ) (Ub : Matrix.unitaryGroup B ℂ)
        (A : Matrix D D ℂ), A.IsHermitian → IsUnit A →
        IsBlockEncoding (fun _ : Fin a => false) 1 0 U A → ‖Ring.inverse A‖ ≤ κ →
        IsBlockEncoding (physicalZero (a+4)) 1 0 ((out.toQuery (GraphAttachedGate.eval a)).eval U Ub)
          (Polynomial.aeval (GraphEncoding.normalizedGraph A κ) (liftReal (kernelFilter (graphFilterGap κ) η))) ∧
        ‖Matrix.toEuclideanCLM (n := Fin 4 × D) (𝕜 := ℂ)
            (signalBlock (physicalZero (a+4)) ((out.toQuery (GraphAttachedGate.eval a)).eval U Ub))-
          (LinearMap.ker (Matrix.toEuclideanCLM (n := Fin 4 × D) (𝕜 := ℂ)
            (GraphEncoding.graphMatrix A κ)).toLinearMap).starProjection‖ ≤ η := by
  have hk : 0 < κ := by linarith
  have hd : 0 < graphFilterGap κ ∧ graphFilterGap κ ≤ 1/Real.sqrt 12 :=
    ⟨graphFilterGap_pos hk,min_le_right _ _⟩
  have hp := lemma51_kernel_filter hd.1 hd.2 hη0 hη1
  have hdeg := paperGraphFilter_degree_bound hκ hη0 hη1
  obtain ⟨out,hm,hv,hgates,henc⟩ := graphPolynomial_from_masked_calls a κ hk
    (kernelFilter (graphFilterGap κ) η) hp.1 hp.2.2.2.1 K calls hq hg hcall
  refine ⟨out,?_,hv,?_,?_⟩
  · have hm' : ((out.toQuery (GraphAttachedGate.eval a)).matrixQueries : ℝ) ≤
        8*(kernelFilter (graphFilterGap κ) η).natDegree := by exact_mod_cast hm
    nlinarith
  · have hg' : (out.workGates : ℝ) ≤
        (6248*(a+5)+4*K)*((kernelFilter (graphFilterGap κ) η).natDegree+1) := by exact_mod_cast hgates
    refine hg'.trans ?_
    gcongr
  · intro U Ub A hA hu hU hi
    have he := henc U Ub A hA hU
    refine ⟨he,?_⟩
    have heq := exact_block_eq he
    rw [one_smul] at heq
    rw [← heq,polynomial_matrix_to_operator,← normalizedGraph_kernel_projection A hk]
    have hs : (Matrix.toEuclideanCLM (n := Fin 4 × D) (𝕜 := ℂ)
        (GraphEncoding.normalizedGraph A κ)).toLinearMap.IsSymmetric :=
      Matrix.isHermitian_iff_isSymmetric.mp (GraphEncoding.normalizedGraph_hermitian A hA κ)
    apply kernelFilter_operator_bound _ hs hd.1 hd.2 hη0 hη1
    intro μ hmem hμ
    obtain ⟨hlo,hup⟩ := GraphEncoding.normalizedGraph_spectrum_paper A hA hu hκ
      (norm_le_of_exact_block hU) hi μ hmem hμ
    refine ⟨(min_le_left _ _).trans ?_,hup⟩
    simpa only [graphNormalization] using hlo

end OptimalQLS.PolynomialTransform
