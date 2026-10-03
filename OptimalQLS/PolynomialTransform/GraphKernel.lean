import OptimalQLS.PolynomialTransform.RegisterRelabel
import OptimalQLS.PolynomialTransform.ElementaryRefinement
import OptimalQLS.GraphEncoding.Proposition43
import OptimalQLS.GraphEncoding.SpectralGap

/-! # The elementary Chebyshev filter on the actual physical auxiliary graph -/
noncomputable section
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 800000
namespace OptimalQLS.PolynomialTransform
open Matrix Polynomial DirtyAncilla
open scoped Matrix.Norms.L2Operator
variable {D B : Type*} [Fintype D] [DecidableEq D] [Fintype B] [DecidableEq B]

theorem graph_gap_parameter {κ : ℝ} (hκ : 2 ≤ κ) :
    0 < 1/(2*κ) ∧ 1/(2*κ) ≤ 1/Real.sqrt 12 := by
  have hk : 0 < κ := by linarith
  have hs : 0 < Real.sqrt 12 := Real.sqrt_pos.mpr (by norm_num)
  have hs4 : Real.sqrt 12 ≤ 4 := by nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 12)]
  refine ⟨by positivity,?_⟩
  exact one_div_le_one_div_of_le hs (by linarith)

theorem normalize_exact_encoding {S : Type*} [Fintype S] [DecidableEq S]
    (s₀ : S) {α : ℝ} (U : Matrix.unitaryGroup (S × D) ℂ) (A : Matrix D D ℂ)
    (h : IsBlockEncoding s₀ α 0 U A) : IsBlockEncoding s₀ 1 0 U (α⁻¹ • A) := by
  have he := exact_block_eq h
  rw [he,smul_smul,inv_mul_cancel₀ (ne_of_gt h.1),one_smul]
  exact ⟨by norm_num,by norm_num,by simp⟩

/-- Fixed physical-coordinate wiring for the four graph-construction signal bits. -/
def graphSignalBits (a : ℕ) :
    GraphEncoding.PhysicalSignal (Fin a → Bool) ≃ (Fin (a+4) → Bool) := bitPrefixEquiv 4 a

theorem graphSignalBits_zero (a : ℕ) :
    graphSignalBits a (GraphEncoding.physicalSignalZero (fun _ : Fin a => false))=(fun _ => false) :=
  bitPrefixEquiv_zero 4 a

/-- Nonzero normalization leaves the actual graph kernel unchanged. -/
theorem normalizedGraph_kernel (A : Matrix D D ℂ) {κ : ℝ} (hκ : 0 < κ) :
    LinearMap.ker (Matrix.toEuclideanCLM (n := Fin 4 × D) (𝕜 := ℂ)
      (GraphEncoding.normalizedGraph A κ)).toLinearMap=
    LinearMap.ker (Matrix.toEuclideanCLM (n := Fin 4 × D) (𝕜 := ℂ)
      (GraphEncoding.graphMatrix A κ)).toLinearMap := by
  have ha : (1+κ⁻¹ : ℝ) ≠ 0 := ne_of_gt (by positivity)
  have hac : (((1+κ⁻¹)⁻¹ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast inv_ne_zero ha
  ext x
  simp only [LinearMap.mem_ker]
  rw [GraphEncoding.normalizedGraph,RCLike.real_smul_eq_coe_smul (K := ℂ),map_smul]
  change (((1+κ⁻¹)⁻¹ : ℝ) : ℂ) •
    ((Matrix.toEuclideanCLM (n := Fin 4 × D) (𝕜 := ℂ) (GraphEncoding.graphMatrix A κ)) x) = 0 ↔ _
  exact smul_eq_zero_iff_right hac

theorem normalizedGraph_kernel_projection (A : Matrix D D ℂ) {κ : ℝ} (hκ : 0 < κ) :
    (LinearMap.ker (Matrix.toEuclideanCLM (n := Fin 4 × D) (𝕜 := ℂ)
      (GraphEncoding.normalizedGraph A κ)).toLinearMap).starProjection=
    (LinearMap.ker (Matrix.toEuclideanCLM (n := Fin 4 × D) (𝕜 := ℂ)
      (GraphEncoding.graphMatrix A κ)).toLinearMap).starProjection := by
  have hc (K L : Submodule ℂ (EuclideanSpace ℂ (Fin 4 × D)))
      [K.HasOrthogonalProjection] [L.HasOrthogonalProjection] (h : K=L) :
      K.starProjection=L.starProjection := by subst L; rfl
  exact hc _ _ (normalizedGraph_kernel A hκ)

/-- The final graph-filter circuit has a+9 total signal qubits. Its input
oracle is the concrete Hermitian graph encoding from Proposition4.3. -/
theorem lemma52_physical_graph_elementary_filter [Nonempty D] (a : ℕ)
    {κ η : ℝ} (hκ : 2 ≤ κ) (hη0 : 0 < η) (hη1 : η < 1/2) :
    ∃ c : ElementaryCircuit
        (GraphEncoding.PhysicalSignal (Fin a → Bool) × (Fin 4 × D)) B (QSVTWire (a+4)) (Fin 4 × D),
      (c.toQuery.matrixQueries : ℝ) < 48*κ*Real.log (1/η) ∧ c.toQuery.vectorQueries=0 ∧
      (c.workGates : ℝ) ≤ 6248*(12*κ*Real.log (1/η)+1)*(a+5) ∧
      ∀ (U : Matrix.unitaryGroup ((Fin a → Bool) × D) ℂ) (Ub : Matrix.unitaryGroup B ℂ)
        (A : Matrix D D ℂ), A.IsHermitian → IsUnit A →
        IsBlockEncoding (fun _ : Fin a => false) 1 0 U A → ‖Ring.inverse A‖ ≤ κ →
        let V := GraphEncoding.physicalEncoding κ (by linarith) U
        IsBlockEncoding (physicalZero (a+4)) 1 0 (c.toQuery.eval V Ub)
          (Polynomial.aeval (GraphEncoding.normalizedGraph A κ)
            (liftReal (kernelFilter (1/(2*κ)) η))) ∧
        ‖Matrix.toEuclideanCLM (n := Fin 4 × D) (𝕜 := ℂ)
            (signalBlock (physicalZero (a+4)) (c.toQuery.eval V Ub))-
          (LinearMap.ker (Matrix.toEuclideanCLM (n := Fin 4 × D) (𝕜 := ℂ)
            (GraphEncoding.graphMatrix A κ)).toLinearMap).starProjection‖ ≤ η := by
  have hk : 0 < κ := by linarith
  have hd := graph_gap_parameter hκ
  have hp := lemma51_kernel_filter hd.1 hd.2 hη0 hη1
  have hdeg := kernelFilter_degree_complexity hd.1 hd.2 hη0 hη1
  have hinv : (1/(2*κ) : ℝ)⁻¹=2*κ := by simp
  rw [hinv] at hdeg
  obtain ⟨c,hq,hv,hg,henc⟩ := lemma24_elementary_encoding_relabel
    (D := Fin 4 × D) (B := B) (a+4) (graphSignalBits a)
    (GraphEncoding.physicalSignalZero (fun _ : Fin a => false)) (graphSignalBits_zero a)
    (kernelFilter (1/(2*κ)) η) hp.1 hp.2.2.2.1
  refine ⟨c,?_,hv,?_,?_⟩
  · have hq' : (c.toQuery.matrixQueries : ℝ) ≤ 4*(kernelFilter (1/(2*κ)) η).natDegree := by exact_mod_cast hq
    nlinarith
  · have hg' : (c.workGates : ℝ) ≤ 6248*((kernelFilter (1/(2*κ)) η).natDegree+1)*(a+5) := by
      exact_mod_cast hg
    refine hg'.trans ?_
    gcongr
    nlinarith
  · intro U Ub A hA hu hU hi
    let V := GraphEncoding.physicalEncoding κ hk U
    have hb : IsBlockEncoding (GraphEncoding.physicalSignalZero (fun _ : Fin a => false)) 1 0 V
        (GraphEncoding.normalizedGraph A κ) :=
      normalize_exact_encoding _ V _ (GraphEncoding.physicalEncoding_exact κ hk _ U A hA hU)
    have hH := GraphEncoding.normalizedGraph_hermitian A hA κ
    have he := henc V Ub (GraphEncoding.normalizedGraph A κ) hH hb
    refine ⟨he,?_⟩
    have heq := exact_block_eq he
    rw [one_smul] at heq
    rw [← heq,polynomial_matrix_to_operator,← normalizedGraph_kernel_projection A hk]
    have hs : (Matrix.toEuclideanCLM (n := Fin 4 × D) (𝕜 := ℂ)
        (GraphEncoding.normalizedGraph A κ)).toLinearMap.IsSymmetric :=
      Matrix.isHermitian_iff_isSymmetric.mp hH
    exact kernelFilter_operator_bound _ hs hd.1 hd.2 hη0 hη1
      (GraphEncoding.normalizedGraph_spectrum A hA hu hκ (norm_le_of_exact_block hU) hi)

theorem graph_filter_signal_cardinality (a : ℕ) :
    Fintype.card (PhysicalSignal (a+4))=2^(a+9) := by
  simpa [Nat.add_assoc] using physical_signal_cardinality (a+4)

end OptimalQLS.PolynomialTransform
