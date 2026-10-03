import OptimalQLS.Refinement.NormalizedQueryTheorem
import OptimalQLS.OracleCoordinates

/-! # Conventional physical input records and every supplied norm estimate -/
noncomputable section
namespace OptimalQLS.Refinement
open Matrix Preparation TransducerCompiler BinaryClock PhysicalPadding LowerBounds Repetition
open scoped Matrix.Norms.L2Operator
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 300000

/-- Classical input record for the normalized Hermitian problem. -/
def normalizedPublicParameters (a : ℕ) (κ ŝ ε : ℝ) : QLSParameters := ⟨1,a,κ,ŝ,ε⟩

def signalCoordinates (a : ℕ) (d : ℕ) : Bits a × PhysicalData d ≃ SignalIndex a × PhysicalData d :=
  Equiv.prodCongr (HadamardClock.bitsFinEquiv a) (Equiv.refl _)

theorem signalCoordinates_block (a d : ℕ)
    (UA : Matrix.unitaryGroup (SignalIndex a × PhysicalData d) ℂ) :
    signalBlock (D := PhysicalData d) (fun _ : Fin a=>false) (rewireUnitary (signalCoordinates a d).symm UA).val=
      signalBlock (D := PhysicalData d) (0 : SignalIndex a) UA.val := by
  ext i j
  simp [signalBlock_entries,rewireUnitary,signalCoordinates,HadamardClock.bitsFinEquiv_zero]

theorem physicalPromise_budget {a d : ℕ} [NeZero d] {κ ŝ ε : ℝ}
    {M : Matrix (Fin d) (Fin d) ℂ} {b : DataSpace d}
    {UA : Matrix.unitaryGroup (SignalIndex a × PhysicalData d) ℂ}
    {Ub : Matrix.unitaryGroup (PhysicalData d) ℂ}
    (h : PhysicalRelaxedQLSPromise (normalizedPublicParameters a κ ŝ ε) M b UA Ub) :
    BudgetParameters κ (solutionScale 1 M b) ŝ :=
  ⟨h.kappaLower,h.toPhysicalBaseQLSPromise.scale_bounds.1,
    h.toPhysicalBaseQLSPromise.scale_bounds.2,h.estimateLower,h.estimateUpper⟩

/-- A single actual finite program exists for every supplied classical estimate.
When no input can satisfy that estimate, the correctness implication is empty.
Otherwise the actual factor bounds are used, never an oracle-dependent choice
of code or the hidden exact solution norm. -/
theorem normalized_physical_promise_algorithm (a d : ℕ) [NeZero d] {κ ŝ ε : ℝ}
    (hκ : 2≤κ) (hε0 : 0<ε) (hε1 : ε<1/2) :
    ∃ (w : ℕ) (zero : Fin w)
      (program : FiniteOracleProgram (SignalIndex a × PhysicalData d) (PhysicalData d) (physicalDimension d) w),
      (Repetition.matrixDepth program : ℝ)<79200000000000*κ*Real.log (1/ε) ∧
      Repetition.RegisterBound w program ∧
      ∀ (M : Matrix (Fin d) (Fin d) ℂ) (b : DataSpace d)
        (UA : Matrix.unitaryGroup (SignalIndex a × PhysicalData d) ℂ)
        (Ub : Matrix.unitaryGroup (PhysicalData d) ℂ), M.IsHermitian →
        PhysicalRelaxedQLSPromise (normalizedPublicParameters a κ ŝ ε) M b UA Ub →
        (program.vectorDepth : ℝ)<8640000072000*(κ/solutionScale 1 M b) ∧
        (2 : ℝ)/3<program.successProbability UA Ub (Repetition.basis zero) ∧
        ∃ x : PhysicalSource d, ‖x‖=1 ∧ ‖x-physicalSolution M b‖≤ε/2 ∧
          program.conditionalOutput UA Ub (Repetition.basis zero)=pureDensity (WithLp.ofLp x) := by
  classical
  by_cases hr : 3/8≤ŝ ∧ ŝ≤5*κ/2
  · obtain ⟨w,zero,c,hqa,hreg,hcorrect⟩ := normalized_physical_query_algorithm a d hκ hr.1 hr.2 hε0 hε1
    let e := signalCoordinates a d
    let result := OracleCoordinates.program e (Equiv.refl (PhysicalData d)) c
    refine ⟨w,zero,result,?_,?_,?_⟩
    · simpa only [result,OracleCoordinates.program_matrixDepth] using hqa
    · exact (OracleCoordinates.program_registerBound e (Equiv.refl _) c w).mpr hreg
    · intro M b UA Ub hM hp
      have hbgt := physicalPromise_budget hp
      have henc : IsBlockEncoding (fun _ : Fin a=>false) 1 0 (rewireUnitary e.symm UA) (physicalMatrix M) := by
        simpa only [IsBlockEncoding,signalCoordinates_block,e,normalizedPublicParameters]
          using hp.exactEncoding
      have hi : ‖Ring.inverse M‖≤κ := by simpa [normalizedPublicParameters] using hp.inverseBound
      have hout := hcorrect M hM hp.invertible hi (rewireUnitary e.symm UA) henc Ub b
        hp.unitVector hp.statePreparation hbgt
      have hrefl : rewireUnitary (Equiv.refl (PhysicalData d)) Ub=Ub := by
        apply Subtype.ext
        rfl
      simpa only [result,OracleCoordinates.program_vectorDepth,
        OracleCoordinates.program_successProbability,OracleCoordinates.program_conditionalOutput,
        Equiv.refl_symm,hrefl] using hout
  · let c : FiniteOracleProgram (SignalIndex a × PhysicalData d) (PhysicalData d)
        (physicalDimension d) (physicalDimension d) := .output false false
    refine ⟨physicalDimension d,0,c,?_,le_rfl,?_⟩
    · simp only [c,Repetition.matrixDepth,Nat.cast_zero]
      have hl := log_accuracy_lower hε0 hε1
      have hk : 0<κ := by linarith
      positivity
    · intro M b UA Ub hM hp
      exact False.elim (hr (classical_parameter_range (physicalPromise_budget hp)))

end OptimalQLS.Refinement
