import OptimalQLS.PolynomialTransform.CircuitProvenance
import OptimalQLS.PolynomialTransform.ElementaryEncoding

/-! # Elementary QSVT realization with its two-mask oracle controls retained -/
noncomputable section
namespace OptimalQLS.PolynomialTransform
open Matrix Polynomial DirtyAncilla
variable {D B : Type*} [Fintype D] [DecidableEq D] [Fintype B] [DecidableEq B]

/-- The explicit controlled oracle at the physical scratch-extended workspace. -/
def physicalMaskedOracle (a : ℕ) (branch sector : Bool)
    (U : Matrix.unitaryGroup ((Fin a → Bool) × D) ℂ) :
    Matrix.unitaryGroup (PhysicalSignal a × D) ℂ :=
  (scratchPort (physicalEquiv a D)).apply
    (rewireUnitary (twoLabelSignalEquiv (Fin a → Bool) D)
      (if branch then sumUnitary 1 (if sector then sumUnitary 1 U else sumUnitary U 1)
        else sumUnitary (if sector then sumUnitary 1 U else sumUnitary U 1) 1))

/-- Strong synthesis endpoint: every retained query has one of the two-label
mask controls, with the dilation selector equal to its adjoint flag. -/
theorem boundedTransform_elementary_with_controls (a : ℕ) (z₀ : Circle) (zs : List Circle) :
    ∃ out : ElementaryCircuit ((Fin a → Bool) × D) B (QSVTWire a) D,
      out.toQuery.matrixQueries=4*zs.length ∧ out.toQuery.vectorQueries=0 ∧
      out.workGates ≤ 6248*(zs.length+1)*(a+1) ∧
      (∀ p adj, ElementaryInstruction.matrixCall p adj ∈ out →
        ∃ branch : Bool, ∀ U, p.apply U=physicalMaskedOracle a branch adj U) ∧
      ∀ (UA : Matrix.unitaryGroup ((Fin a → Bool) × D) ℂ) (Ub : Matrix.unitaryGroup B ℂ),
        (out.toQuery.eval UA Ub).val*basisInsertion (physicalClean a)=
          basisInsertion (physicalClean a)*
            (boundedTransformUnitary (fun _ : Fin a => false) UA z₀ zs).val := by
  let c := boundedTransformCircuit (D := D) (B := B) (fun _ : Fin a => false) z₀ zs
  have hport : ∀ U : Matrix.unitaryGroup (LogicalSignal a × D) ℂ,
      ((scratchPort (physicalEquiv a D)).apply U).val*basisInsertion (physicalClean a)=
        basisInsertion (physicalClean a)*U.val := by
    intro U
    exact scratchPort_intertwines (physicalEquiv a D) (false,false,false) U
  obtain ⟨out,hm,hv,hg,hp,he⟩ := refine_query_circuit_with_ports c (basisInsertion (physicalClean a))
    (scratchPort (physicalEquiv a D)) hport (781*(a+1)) (bounded_work_synthesis a z₀ zs)
  refine ⟨out,hm.trans (boundedTransformCircuit_counts _ z₀ zs).1,
    hv.trans (boundedTransformCircuit_counts _ z₀ zs).2,?_,?_,?_⟩
  · have hw := bounded_work_count (D := D) (B := B) a z₀ zs
    change workInstructions c=8*zs.length+4 at hw
    rw [hw] at hg
    nlinarith
  · intro p adj h
    obtain ⟨q,hq,rfl⟩ := hp p adj h
    obtain ⟨branch,hbranch⟩ := bounded_query_controls _ z₀ zs q adj hq
    refine ⟨branch,?_⟩
    intro U
    rw [QueryPort.comp_apply,hbranch U]
    rfl
  · intro UA Ub
    simpa only [c,boundedTransformCircuit_eval] using he UA Ub

/-- Lemma2.4 retaining the actual mask of every matrix call for subsequent
controlled-oracle substitution by an elementary implementation. -/
theorem lemma24_elementary_encoding_with_controls [Nonempty D] (a : ℕ) (p : ℝ[X])
    (hp : Function.Even p.eval) (hbound : ∀ x : ℝ, |x| ≤ 1 → |p.eval x| ≤ 1) :
    ∃ out : ElementaryCircuit ((Fin a → Bool) × D) B (QSVTWire a) D,
      out.toQuery.matrixQueries ≤ 4*p.natDegree ∧ out.toQuery.vectorQueries=0 ∧
      out.workGates ≤ 6248*(p.natDegree+1)*(a+1) ∧
      (∀ port adj, ElementaryInstruction.matrixCall port adj ∈ out →
        ∃ branch : Bool, ∀ U, port.apply U=physicalMaskedOracle a branch adj U) ∧
      ∀ (UA : Matrix.unitaryGroup ((Fin a → Bool) × D) ℂ) (Ub : Matrix.unitaryGroup B ℂ)
        (A : Matrix D D ℂ), A.IsHermitian → IsBlockEncoding (fun _ : Fin a => false) 1 0 UA A →
        IsBlockEncoding (physicalZero a) 1 0 (out.toQuery.eval UA Ub)
          (Polynomial.aeval A (liftReal p)) := by
  obtain ⟨z₀,zs,hlen,henc⟩ := bounded_even_exact_encoding (D := D)
    (fun _ : Fin a => false) p hp hbound
  obtain ⟨out,hm,hv,hg,hports,he⟩ := boundedTransform_elementary_with_controls (D := D) (B := B) a z₀ zs
  refine ⟨out,by omega,hv,hg.trans ?_,hports,?_⟩
  · exact Nat.mul_le_mul_right (a+1) (Nat.mul_le_mul_left 6248 (by omega))
  · intro UA Ub A hA hUA
    have hb := henc UA A hA hUA
    have hc := signalBlock_of_clean_intertwines (physicalCleanSignal a)
      (physicalCleanSignal_injective a) ((false,false),fun _ : Fin a => false)
      (out.toQuery.eval UA Ub).val (boundedTransformUnitary (fun _ : Fin a => false) UA z₀ zs).val
      (he UA Ub)
    rw [physicalClean_zero] at hc
    simpa only [IsBlockEncoding,hc] using hb

end OptimalQLS.PolynomialTransform
