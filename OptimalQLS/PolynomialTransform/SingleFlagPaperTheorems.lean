import OptimalQLS.PolynomialTransform.SingleFlagEncoding
import OptimalQLS.PolynomialTransform.GraphPolynomial
import OptimalQLS.PolynomialTransform.ParameterBounds

/-! # Paper endpoints retaining literal single-flag original-oracle provenance -/
noncomputable section
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace OptimalQLS.PolynomialTransform
open Matrix Polynomial DirtyAncilla
open scoped Matrix.Norms.L2Operator
variable {D B : Type*} [Fintype D] [DecidableEq D] [Fintype B] [DecidableEq B]

def graphOriginalSingleFlagPort (a : ℕ) (D : Type*) [Fintype D] [DecidableEq D] :
    QueryPort ((Fin a → Bool) × D) (PhysicalSignal (a+4) × (Fin 4 × D)) :=
  (relabelPort (graphAttachWiring a D)).comp
    (GraphEncoding.singleFlagOraclePort ((Fin a → Bool) × D) GraphEncoding.flagWire)

theorem attachedGraph_callsOnly (a : ℕ)
    (c : ElementaryCircuit ((Fin a → Bool) × D) B GraphLocalWire ((Fin a → Bool) × D))
    (hc : GraphEncoding.SingleFlagRealCircuit GraphEncoding.flagWire c) :
    (attachGraphCircuit a c).CallsOnly (graphOriginalSingleFlagPort a D) := by
  intro p adj hp
  obtain ⟨g,hg,hEq⟩ := List.mem_map.mp hp
  cases g with
  | gate g => cases hEq
  | vectorCall p b => cases hEq
  | matrixCall q b =>
    obtain ⟨rfl,rfl⟩ := NamedInstruction.matrixCall.inj hEq
    rw [hc.2 q b hg]
    rfl

/-- Strict query-model graph transformation with only the common named flag
controlling every original U_A/adjoint call. -/
theorem graphTransform_single_flag (a : ℕ) (κ : ℝ) (hκ : 0 < κ)
    (z₀ : Circle) (zs : List Circle) :
    ∃ out : GraphAttachedCircuit a D B,
      (out.toQuery (GraphAttachedGate.eval a)).matrixQueries=8*zs.length ∧
      (out.toQuery (GraphAttachedGate.eval a)).vectorQueries=0 ∧
      out.workGates≤(6248*(a+5)+1009216)*(zs.length+1) ∧
      out.CallsOnly (graphOriginalSingleFlagPort a D) ∧
      ∀ (U : Matrix.unitaryGroup ((Fin a → Bool) × D) ℂ) (Ub : Matrix.unitaryGroup B ℂ),
        ((out.toQuery (GraphAttachedGate.eval a)).eval U Ub).val*basisInsertion (physicalClean (a+4))=
          basisInsertion (physicalClean (a+4))*
            (boundedTransformUnitary (fun _ : Fin (a+4) => false) (binaryGraphOracle a κ hκ U) z₀ zs).val := by
  choose calls hm hv hg hs he using
    (fun mask => GraphEncoding.controlled_graph_single_flag (S := Fin a → Bool) (D := D) (B := B) κ hκ mask)
  let c := boundedTransformCircuit (D := Fin 4 × D) (B := B) (fun _ : Fin (a+4) => false) z₀ zs
  have hwork : ∀ U, QueryInstruction.work U ∈ c → ∃ code : GraphAttachedCircuit a D B,
      (code.toQuery (GraphAttachedGate.eval a)).matrixQueries=0 ∧
      (code.toQuery (GraphAttachedGate.eval a)).vectorQueries=0 ∧ code.workGates≤781*(a+5) ∧
      code.CallsOnly (graphOriginalSingleFlagPort a D) ∧
      ∀ UA Ub, ((code.toQuery (GraphAttachedGate.eval a)).eval UA Ub).val*basisInsertion (physicalClean (a+4))=
        basisInsertion (physicalClean (a+4))*U.val := by
    intro U hU
    obtain ⟨code,hlen,he⟩ := bounded_work_synthesis (a+4) z₀ zs U hU
    refine ⟨attachedQSPMacro a code,?_,?_,?_,?_,?_⟩
    · rw [attachedQSPMacro_toQuery]; exact (elementaryMacro_queries _).1
    · rw [attachedQSPMacro_toQuery]; exact (elementaryMacro_queries _).2
    · rw [attachedQSPMacro_workGates]; simpa [Nat.add_assoc] using hlen
    · intro p adj hp; simp [attachedQSPMacro] at hp
    · intro UA Ub; rw [attachedQSPMacro_toQuery,elementaryMacro_eval]; exact he
  have hquery : ∀ p adj, QueryInstruction.matrixCall p adj ∈ c → ∃ code : GraphAttachedCircuit a D B,
      (code.toQuery (GraphAttachedGate.eval a)).matrixQueries=2 ∧
      (code.toQuery (GraphAttachedGate.eval a)).vectorQueries=0 ∧ code.workGates≤252304 ∧
      code.CallsOnly (graphOriginalSingleFlagPort a D) ∧
      ∀ UA Ub, ((code.toQuery (GraphAttachedGate.eval a)).eval UA Ub).val*basisInsertion (physicalClean (a+4))=
        basisInsertion (physicalClean (a+4))*(p.apply
          (if adj then (binaryGraphOracle a κ hκ UA)⁻¹ else binaryGraphOracle a κ hκ UA)).val := by
    intro p adj hp
    obtain ⟨branch,hbranch⟩ := bounded_query_controls _ z₀ zs p adj hp
    refine ⟨attachGraphCircuit a (calls (branch,adj)),?_,?_,?_,attachedGraph_callsOnly a _ (hs _),?_⟩
    · exact (attachGraphCircuit_counts _ _).1.trans (hm _)
    · exact (attachGraphCircuit_counts _ _).2.1.trans (hv _)
    · rw [attachGraphCircuit_workGates]; exact hg _
    · intro UA Ub
      rw [attachGraphCircuit_eval,binaryGraphOracle_inv,ite_self,hbranch]
      rw [binaryGraphOracle,nested_mask_relabel]
      exact graphAttached_intertwines a _ _ (by simpa using he (branch,adj) false UA Ub)
  obtain ⟨out,houtm,houtv,houtg,hports,houte⟩ := refine_named_single_port (GraphAttachedGate.eval a) c
    (boundedTransformCircuit_counts _ z₀ zs).2 (basisInsertion (physicalClean (a+4)))
    (binaryGraphOracle a κ hκ) (graphOriginalSingleFlagPort a D) (781*(a+5)) 252304 2 hwork hquery
  refine ⟨out,?_,houtv,?_,hports,?_⟩
  · rw [(boundedTransformCircuit_counts _ z₀ zs).1] at houtm
    omega
  · have hw := bounded_work_count (D := Fin 4 × D) (B := B) (a+4) z₀ zs
    change workInstructions c=8*zs.length+4 at hw
    have hmc := (boundedTransformCircuit_counts (D := Fin 4 × D) (B := B) (fun _ : Fin (a+4) => false) z₀ zs).1
    change c.matrixQueries=4*zs.length at hmc
    rw [hw,hmc] at houtg
    nlinarith
  · intro U Ub
    simpa only [c,boundedTransformCircuit_eval] using houte U Ub

theorem graphPolynomial_single_flag [Nonempty D] (a : ℕ) (κ : ℝ) (hκ : 0 < κ)
    (p : ℝ[X]) (hp : Function.Even p.eval) (hbound : ∀ x : ℝ, |x|≤1 → |p.eval x|≤1) :
    ∃ out : GraphAttachedCircuit a D B,
      (out.toQuery (GraphAttachedGate.eval a)).matrixQueries≤8*p.natDegree ∧
      (out.toQuery (GraphAttachedGate.eval a)).vectorQueries=0 ∧
      out.workGates≤(6248*(a+5)+1009216)*(p.natDegree+1) ∧
      out.CallsOnly (graphOriginalSingleFlagPort a D) ∧
      ∀ (U : Matrix.unitaryGroup ((Fin a → Bool) × D) ℂ) (Ub : Matrix.unitaryGroup B ℂ)
        (A : Matrix D D ℂ), A.IsHermitian → IsBlockEncoding (fun _ : Fin a => false) 1 0 U A →
        IsBlockEncoding (physicalZero (a+4)) 1 0 ((out.toQuery (GraphAttachedGate.eval a)).eval U Ub)
          (Polynomial.aeval (GraphEncoding.normalizedGraph A κ) (liftReal p)) := by
  obtain ⟨z₀,zs,hlen,henc⟩ := bounded_even_exact_encoding (D := Fin 4 × D)
    (fun _ : Fin (a+4) => false) p hp hbound
  obtain ⟨out,hm,hv,hg,hports,he⟩ := graphTransform_single_flag (D := D) (B := B) a κ hκ z₀ zs
  refine ⟨out,by omega,hv,hg.trans ?_,hports,?_⟩
  · exact Nat.mul_le_mul_left _ (by omega)
  · intro U Ub A hA hU
    have hb := henc (binaryGraphOracle a κ hκ U) (GraphEncoding.normalizedGraph A κ)
      (GraphEncoding.normalizedGraph_hermitian A hA κ) (binaryGraphOracle_exact a κ hκ U A hA hU)
    have hc := signalBlock_of_clean_intertwines (physicalCleanSignal (a+4))
      (physicalCleanSignal_injective (a+4)) ((false,false),fun _ : Fin (a+4) => false)
      ((out.toQuery (GraphAttachedGate.eval a)).eval U Ub).val
      (boundedTransformUnitary (fun _ : Fin (a+4) => false) (binaryGraphOracle a κ hκ U) z₀ zs).val (he U Ub)
    rw [physicalClean_zero] at hc
    simpa only [IsBlockEncoding,hc] using hb

theorem single_flag_graph_gate_bound (a : ℕ) {κ η : ℝ}
    (hκ : 2≤κ) (hη0 : 0<η) (hη1 : η<1/2) :
    (6248*(a+5)+1009216)*(12*κ*Real.log (1/η)+1) ≤
      13525928*κ*(a+1)*Real.log (1/η) := by
  have hm := kappa_log_ge_one hκ hη0 hη1
  have ha : 6248*((a:ℝ)+5)+1009216 ≤ 1040456*(a+1) := by nlinarith [Nat.cast_nonneg (α:=ℝ) a]
  have hb : 12*κ*Real.log (1/η)+1 ≤ 13*(κ*Real.log (1/η)) := by nlinarith
  calc
    _ ≤ (1040456*(a+1))*(13*(κ*Real.log (1/η))) := mul_le_mul ha hb (by nlinarith) (by positivity)
    _ = _ := by ring

/-- Full Lemma5.2 with the paper's literal min-definedδ, true original queries,
a+9 signal qubits, actual kernel projector, and retained single-flag provenance. -/
theorem lemma52_kernel_filter_single_flag [Nonempty D] (a : ℕ)
    {κ η : ℝ} (hκ : 2≤κ) (hη0 : 0<η) (hη1 : η<1/2) :
    ∃ out : GraphAttachedCircuit a D B,
      ((out.toQuery (GraphAttachedGate.eval a)).matrixQueries : ℝ)<96*κ*Real.log (1/η) ∧
      (out.toQuery (GraphAttachedGate.eval a)).vectorQueries=0 ∧
      (out.workGates : ℝ)≤13525928*κ*(a+1)*Real.log (1/η) ∧
      out.CallsOnly (graphOriginalSingleFlagPort a D) ∧
      ∀ (U : Matrix.unitaryGroup ((Fin a → Bool) × D) ℂ) (Ub : Matrix.unitaryGroup B ℂ)
        (A : Matrix D D ℂ), A.IsHermitian → IsUnit A →
        IsBlockEncoding (fun _ : Fin a => false) 1 0 U A → ‖Ring.inverse A‖≤κ →
        IsBlockEncoding (physicalZero (a+4)) 1 0 ((out.toQuery (GraphAttachedGate.eval a)).eval U Ub)
          (Polynomial.aeval (GraphEncoding.normalizedGraph A κ) (liftReal (kernelFilter (graphFilterGap κ) η))) ∧
        ‖Matrix.toEuclideanCLM (n:=Fin 4 × D) (𝕜:=ℂ)
            (signalBlock (physicalZero (a+4)) ((out.toQuery (GraphAttachedGate.eval a)).eval U Ub))-
          (LinearMap.ker (Matrix.toEuclideanCLM (n:=Fin 4 × D) (𝕜:=ℂ)
            (GraphEncoding.graphMatrix A κ)).toLinearMap).starProjection‖≤η := by
  have hk : 0<κ := by linarith
  have hd : 0<graphFilterGap κ ∧ graphFilterGap κ≤1/Real.sqrt 12 :=
    ⟨graphFilterGap_pos hk,min_le_right _ _⟩
  have hp := lemma51_kernel_filter hd.1 hd.2 hη0 hη1
  have hdeg := paperGraphFilter_degree_bound hκ hη0 hη1
  obtain ⟨out,hm,hv,hg,hports,henc⟩ := graphPolynomial_single_flag (D := D) (B := B) a κ hk
    (kernelFilter (graphFilterGap κ) η) hp.1 hp.2.2.2.1
  refine ⟨out,?_,hv,?_,hports,?_⟩
  · have hm' : ((out.toQuery (GraphAttachedGate.eval a)).matrixQueries : ℝ)≤
        8*(kernelFilter (graphFilterGap κ) η).natDegree := by exact_mod_cast hm
    nlinarith
  · have hg' : (out.workGates : ℝ)≤
        (6248*(a+5)+1009216)*((kernelFilter (graphFilterGap κ) η).natDegree+1) := by exact_mod_cast hg
    refine (hg'.trans ?_).trans (single_flag_graph_gate_bound a hκ hη0 hη1)
    gcongr
  · intro U Ub A hA hu hU hi
    have he := henc U Ub A hA hU
    refine ⟨he,?_⟩
    have heq := exact_block_eq he
    rw [one_smul] at heq
    rw [← heq,polynomial_matrix_to_operator,← normalizedGraph_kernel_projection A hk]
    have hs : (Matrix.toEuclideanCLM (n:=Fin 4 × D) (𝕜:=ℂ)
        (GraphEncoding.normalizedGraph A κ)).toLinearMap.IsSymmetric :=
      Matrix.isHermitian_iff_isSymmetric.mp (GraphEncoding.normalizedGraph_hermitian A hA κ)
    apply kernelFilter_operator_bound _ hs hd.1 hd.2 hη0 hη1
    intro μ hmem hμ
    obtain ⟨hlo,hup⟩ := GraphEncoding.normalizedGraph_spectrum_paper A hA hu hκ
      (norm_le_of_exact_block hU) hi μ hmem hμ
    refine ⟨(min_le_left _ _).trans ?_,hup⟩
    simpa only [graphNormalization] using hlo

/-- Full correction implementation with no hidden multi-bit oracle predicate. -/
theorem lemma55_correction_single_flag [Nonempty D] (a : ℕ)
    {κ η : ℝ} (hκ : 2≤κ) (hη0 : 0<η) (hη1 : η<1/2) :
    ∃ c : SingleFlagCircuit a D B,
      ((c.toQuery (SingleFlagGate.eval a)).matrixQueries : ℝ)≤840000*κ*Real.log (1/η) ∧
      (c.toQuery (SingleFlagGate.eval a)).vectorQueries=0 ∧
      (c.workGates : ℝ)≤3328095848*κ*(a+1)*Real.log (1/η) ∧
      c.CallsOnly (originalSingleFlagPort a D) ∧
      ∀ (U : Matrix.unitaryGroup ((Fin a → Bool) × D) ℂ) (Ub : Matrix.unitaryGroup B ℂ)
        (A : Matrix D D ℂ), A.IsHermitian → IsUnit A →
        IsBlockEncoding (fun _ : Fin a => false) 1 0 U A → ‖Ring.inverse A‖≤κ →
        IsBlockEncoding (physicalZero a) 1 0 ((c.toQuery (SingleFlagGate.eval a)).eval U Ub)
          (Polynomial.aeval A (liftReal (paperCorrectionPolynomial κ η))) ∧
        ‖signalBlock (physicalZero a) ((c.toQuery (SingleFlagGate.eval a)).eval U Ub)-
          (1/4 : ℂ) • (1+((κ⁻¹)^2 : ℂ) • (Ring.inverse A)^2)‖≤η/2 := by
  have hp := lemma54_correction_polynomial hκ hη0 hη1
  obtain ⟨c,hq,hv,hg,hports,henc⟩ := lemma24_single_flag_encoding (D:=D) (B:=B) a
    (paperCorrectionPolynomial κ η) hp.1 (fun x hx => (hp.2.1 x hx).trans (by norm_num))
  refine ⟨c,?_,hv,?_,hports,?_⟩
  · have hq' : ((c.toQuery (SingleFlagGate.eval a)).matrixQueries : ℝ)≤4*(paperCorrectionPolynomial κ η).natDegree := by exact_mod_cast hq
    nlinarith [hp.2.2.2]
  · have hg' : (c.workGates : ℝ)≤15848*((paperCorrectionPolynomial κ η).natDegree+1)*(a+1) := by exact_mod_cast hg
    have hl := kappa_log_ge_one hκ hη0 hη1
    calc
      _ ≤ 15848*(210000*κ*Real.log (1/η)+1)*(a+1) := hg'.trans (by gcongr; exact hp.2.2.2)
      _ ≤ 15848*(210001*(κ*Real.log (1/η)))*(a+1) := by gcongr; nlinarith
      _ = _ := by ring
  · intro U Ub A hA hu hU hi
    have he := henc U Ub A hA hU
    refine ⟨he,?_⟩
    have hb := exact_block_eq he
    rw [one_smul] at hb
    rw [← hb]
    exact lemma55_correction_matrix_error A hA hu hκ hη0 hη1 (norm_le_of_exact_block hU) hi

end OptimalQLS.PolynomialTransform
