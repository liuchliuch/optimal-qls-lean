import OptimalQLS.Reduction.DirectCorrectness
import OptimalQLS.OracleCoordinates

/-! # Conventional physical input records and public-only synthesis choices -/
noncomputable section
set_option synthInstance.maxSize 16384
set_option maxHeartbeats 600000
set_option maxRecDepth 4096
open scoped Classical Matrix.Norms.L2Operator
namespace OptimalQLS.Reduction.PublicInputs
open Matrix LowerBounds PhysicalPadding TransducerCompiler BinaryClock PolynomialTransform
open Refinement Refinement.PhysicalExecution Refinement.Repetition
variable {d : ℕ} [NeZero d] {p : QLSParameters}

/-- Only estimates outside the range of every possible promised input receive
a fixed public default. Every admissible supplied estimate is retained. -/
def effectiveEstimate (κ ŝ : ℝ) : ℝ := if 3/8≤ŝ ∧ ŝ≤5*κ/2 then ŝ else 1

theorem effectiveEstimate_bounds {κ ŝ : ℝ} (hk : 2≤κ) :
    3/8≤effectiveEstimate κ ŝ ∧ effectiveEstimate κ ŝ≤5*κ/2 := by
  unfold effectiveEstimate
  split_ifs with h
  · exact h
  · constructor <;> linarith

theorem promise_estimate_eq
    {A : Matrix (Fin d) (Fin d) ℂ} {b : DataSpace d}
    {UA : Matrix.unitaryGroup (SignalIndex p.signalQubits × PhysicalData d) ℂ}
    {Ub : Matrix.unitaryGroup (PhysicalData d) ℂ}
    (h : PhysicalRelaxedQLSPromise p A b UA Ub) :
    effectiveEstimate p.kappa p.normEstimate=p.normEstimate := by
  apply if_pos
  have hs := h.toPhysicalBaseQLSPromise.scale_bounds
  exact ⟨by linarith [h.estimateLower],by linarith [h.estimateUpper]⟩

theorem promise_encoding {A : Matrix (Fin d) (Fin d) ℂ} {b : DataSpace d}
    {UA : Matrix.unitaryGroup (SignalIndex p.signalQubits × PhysicalData d) ℂ}
    {Ub : Matrix.unitaryGroup (PhysicalData d) ℂ}
    (h : PhysicalRelaxedQLSPromise p A b UA Ub) :
    IsBlockEncoding (fun _ : Fin p.signalQubits=>false) p.alpha 0
      (rewireUnitary (oracleRegisterCoordinates p.signalQubits d).symm UA)
      (zeroExtend (activeDataBits d) A) := by
  refine ⟨h.exactEncoding.1,h.exactEncoding.2.1,?_⟩
  have he : zeroExtend (activeDataBits d) A-p.alpha •
      signalBlock (fun _ : Fin p.signalQubits=>false)
        (rewireUnitary (oracleRegisterCoordinates p.signalQubits d).symm UA).val=
      (physicalMatrix A-p.alpha • signalBlock (0 : SignalIndex p.signalQubits) UA.val).submatrix
        (physicalDataCoordinates d) (physicalDataCoordinates d) := by
    rw [activeDataBits,zeroExtend_postEquiv]
    ext i j
    simp [signalBlock_entries,rewireUnitary,oracleRegisterCoordinates,HadamardClock.bitsFinEquiv_zero,
      physicalMatrix]
  rw [he]
  exact (matrix_norm_submatrix_equiv_le _ (physicalDataCoordinates d)).trans h.exactEncoding.2.2

theorem promise_source {A : Matrix (Fin d) (Fin d) ℂ} {b : DataSpace d}
    {UA : Matrix.unitaryGroup (SignalIndex p.signalQubits × PhysicalData d) ℂ}
    {Ub : Matrix.unitaryGroup (PhysicalData d) ℂ}
    (h : PhysicalRelaxedQLSPromise p A b UA Ub) (i : Bits (dataQubits d)) :
    rewireUnitary (physicalDataCoordinates d).symm Ub i (fun _ : Fin (dataQubits d)=>false)=
      coordinateIsometry (activeDataBits d) b i := by
  change Ub (physicalDataCoordinates d i) (physicalDataCoordinates d (fun _=>false))=_
  rw [physicalDataCoordinates_zero,h.statePreparation,activeDataBits,coordinateIsometry_postEquiv]
  rfl

theorem physical_solution_coordinates (A : Matrix (Fin d) (Fin d) ℂ) (b : DataSpace d) :
    outputCoordinates (dataQubits d) (coordinateIsometry (activeDataBits d)
      (NormedSpace.normalize (WithLp.toLp 2 (A⁻¹*ᵥWithLp.ofLp b))))=physicalSolution A b := by
  ext i
  rw [outputCoordinates_apply,activeDataBits,coordinateIsometry_postEquiv]
  change coordinateIsometry (activeIndex d)
    (NormedSpace.normalize (WithLp.toLp 2 (A⁻¹*ᵥWithLp.ofLp b)))
      (physicalDataCoordinates d ((physicalDataCoordinates d).symm i))=_
  rw [Equiv.apply_symm_apply,Matrix.nonsing_inv_eq_ringInverse]
  rfl

end OptimalQLS.Reduction.PublicInputs
