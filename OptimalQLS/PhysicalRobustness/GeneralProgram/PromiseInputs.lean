import OptimalQLS.PhysicalRobustness.GeneralProgram.Correctness
import OptimalQLS.PhysicalRobustness.Input
import OptimalQLS.OracleCoordinates

/-! Conventional full physical-register promises, with all supplied estimates. -/
noncomputable section
set_option synthInstance.maxSize 16384
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
open scoped Classical Matrix.Norms.L2Operator
namespace OptimalQLS.PhysicalRobustness.GeneralProgram
open Matrix LowerBounds PhysicalPadding Reduction TransducerCompiler BinaryClock PolynomialTransform
open Refinement Refinement.PhysicalExecution Refinement.Repetition
variable {d : ℕ} [NeZero d] {p : QLSParameters} {δ : ℝ}

/-- Only an impossible public estimate is replaced by a fixed admissible one.
No matrix, vector, input precision or hidden solution norm chooses the code. -/
def publicEstimate (κ ŝ : ℝ) : ℝ := if 1/2≤ŝ ∧ ŝ≤2*κ then ŝ else 1

theorem publicEstimate_bounds {κ ŝ : ℝ} (hk : 2≤κ) :
    1/2≤publicEstimate κ ŝ ∧ publicEstimate κ ŝ≤2*κ := by
  unfold publicEstimate
  split_ifs with h
  · exact h
  · constructor <;> linarith

theorem promise_estimate_eq
    {A : Matrix (Fin d) (Fin d) ℂ} {b : DataSpace d}
    {UA : Matrix.unitaryGroup (SignalIndex p.signalQubits × PhysicalData d) ℂ}
    {Ub : Matrix.unitaryGroup (PhysicalData d) ℂ}
    (h : PhysicalApproximateQLSPromise p δ A b UA Ub) :
    publicEstimate p.kappa p.normEstimate=p.normEstimate := by
  apply if_pos
  have hs := h.scale_bounds
  exact ⟨by linarith [h.estimateLower],by linarith [h.estimateUpper]⟩


theorem promise_encoding {A : Matrix (Fin d) (Fin d) ℂ} {b : DataSpace d}
    {UA : Matrix.unitaryGroup (SignalIndex p.signalQubits × PhysicalData d) ℂ}
    {Ub : Matrix.unitaryGroup (PhysicalData d) ℂ}
    (h : PhysicalApproximateQLSPromise p δ A b UA Ub) :
    IsBlockEncoding (fun _ : Fin p.signalQubits=>false) p.alpha δ
      (rewireUnitary (oracleRegisterCoordinates p.signalQubits d).symm UA)
      (zeroExtend (activeDataBits d) A) := by
  refine ⟨h.approximateEncoding.1,h.approximateEncoding.2.1,?_⟩
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
  exact (matrix_norm_submatrix_equiv_le _ (physicalDataCoordinates d)).trans h.approximateEncoding.2.2

theorem promise_source {A : Matrix (Fin d) (Fin d) ℂ} {b : DataSpace d}
    {UA : Matrix.unitaryGroup (SignalIndex p.signalQubits × PhysicalData d) ℂ}
    {Ub : Matrix.unitaryGroup (PhysicalData d) ℂ}
    (h : PhysicalApproximateQLSPromise p δ A b UA Ub) (i : Bits (dataQubits d)) :
    rewireUnitary (physicalDataCoordinates d).symm Ub i (fun _ : Fin (dataQubits d)=>false)=
      coordinateIsometry (activeDataBits d) b i := by
  change Ub (physicalDataCoordinates d i) (physicalDataCoordinates d (fun _=>false))=_
  rw [physicalDataCoordinates_zero,h.statePreparation,activeDataBits,coordinateIsometry_postEquiv]
  rfl

theorem physical_solution_coordinates (A : Matrix (Fin d) (Fin d) ℂ) (b : DataSpace d) :
    solution (activeDataBits d) A b=physicalSolution A b := by
  unfold solution
  ext i
  rw [outputCoordinates_apply,activeDataBits,coordinateIsometry_postEquiv]
  change coordinateIsometry (activeIndex d)
    (NormedSpace.normalize (WithLp.toLp 2 (A⁻¹*ᵥWithLp.ofLp b)))
      (physicalDataCoordinates d ((physicalDataCoordinates d).symm i))=_
  rw [Equiv.apply_symm_apply]
  rw [Matrix.nonsing_inv_eq_ringInverse]
  rfl

end OptimalQLS.PhysicalRobustness.GeneralProgram
