import OptimalQLS.Reduction.GenericSolver.FreshCopiesReduction
import OptimalQLS.Reduction.GenericSolver.FreshCopiesProcessPaths

/-! The supplied solver is a literal physical program. Its correctness is the
input premise of Proposition 2.3; the reduction, oracle substitution, fresh-copy
execution, local gates, measurements and costs are constructed here. -/
noncomputable section
open scoped Classical
namespace OptimalQLS.Reduction.GenericSolver.FreshCopies
open Matrix LowerBounds Refinement.Repetition TransducerCompiler BinaryClock PolynomialTransform
open Refinement.CostedExecution Physical
set_option synthInstance.maxSize 32768
set_option maxHeartbeats 1000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false
variable {P W : Type} [Fintype P] [DecidableEq P] [Fintype W] [DecidableEq W]
variable {chart : P ≃ (W → Bool)} {a n : ℕ}

theorem reducedProcess_correct (F : OutputLayout chart n) (c : AnyProgram chart a n)
    (zero : P) (UA : Matrix.unitaryGroup (Bits a × Bits n) ℂ) (Ub : Matrix.unitaryGroup (Bits n) ℂ)
    (x : EuclideanSpace ℂ (Fin (dataRegister n).dimension)) {ε : ℝ}
    (hx : ‖x‖=1) (hε0 : 0<ε) (hε1 : ε<1/2)
    (h : Returns (CloseDoubledState (doubledIndex n) x ε)
      (dilationEncoding UA) (preparation Ub) (c.lower F) (basis ((Fintype.equivFin P) zero)))
    (hp : 2/3≤(c.lower F).successProbability (dilationEncoding UA) (preparation Ub)
      (basis ((Fintype.equivFin P) zero))) :
    (2:ℝ)/3<(reducedProcess F c).lower.successProbability UA Ub (reducedInput (chart := chart) zero) ∧
    (∀ t : (reducedProcess F c).lower.Terminal,(reducedProcess F c).lower.terminalSuccess t=true→
      CloseState x ε (((reducedProcess F c).lower.terminalPath
        (.initial (reducedInput (chart := chart) zero)) t).state UA Ub)) := by
  have hr:Returns (CloseDoubledState (doubledIndex n) x ε) UA Ub (adaptedProcess F c).lower
      (basis ((adaptedRegister chart).index (adaptedZero (chart := chart) zero))) :=
    (adaptedProcess_returns F c _ (closeDoubledState_zero _ x hx hε0.le) zero UA Ub).mpr h
  have hp':2/3≤(adaptedProcess F c).lower.successProbability UA Ub
      (basis ((adaptedRegister chart).index (adaptedZero (chart := chart) zero))) := by
    simpa only [FiniteOracleProgram.successProbability,adaptedProcess_density] using hp
  have hs:=fresh_three_physical n (adaptedRegister chart) (adaptedProcess F c)
    (adaptedZero zero) (fun _=>false) UA Ub x hx hε0 hε1 hr hp'
  exact ⟨hs.1,hs.2.1⟩

theorem reducedProcess_reachable (F : OutputLayout chart n) (c : AnyProgram chart a n)
    (zero : P) (UA : Matrix.unitaryGroup (Bits a × Bits n) ℂ) (Ub : Matrix.unitaryGroup (Bits n) ℂ)
    (x : EuclideanSpace ℂ (Fin (dataRegister n).dimension)) {ε : ℝ}
    (hx : ‖x‖=1) (hε0 : 0<ε) (hε1 : ε<1/2)
    (h : ∀ t : (c.lower F).Terminal,(c.lower F).terminalSuccess t=true→
      0<bornMass (((c.lower F).terminalPath (.initial (basis ((Fintype.equivFin P) zero))) t).state
        (dilationEncoding UA) (preparation Ub))→
      CloseDoubledState (doubledIndex n) x ε
        (((c.lower F).terminalPath (.initial (basis ((Fintype.equivFin P) zero))) t).state
          (dilationEncoding UA) (preparation Ub)))
    (hp : 2/3≤(c.lower F).successProbability (dilationEncoding UA) (preparation Ub)
      (basis ((Fintype.equivFin P) zero))) :
    (2:ℝ)/3<(reducedProcess F c).lower.successProbability UA Ub (reducedInput (chart := chart) zero) ∧
    (∀ t : (reducedProcess F c).lower.Terminal,(reducedProcess F c).lower.terminalSuccess t=true→
      CloseState x ε (((reducedProcess F c).lower.terminalPath
        (.initial (reducedInput (chart := chart) zero)) t).state UA Ub)) := by
  apply reducedProcess_correct F c zero UA Ub x hx hε0 hε1 _ hp
  exact (returns_iff_positive_terminals _ (closeDoubledState_zero _ x hx hε0.le)
    _ _ _ _).mpr h

theorem reducedProcess_terminal_resources (F : OutputLayout chart n) (c : AnyProgram chart a n)
    (psi : Fin (poolRegister (adaptedRegister chart) n 3).dimension → ℂ)
    (t : (reducedProcess F c).lower.Terminal) :
    (((reducedProcess F c).lower.terminalPath (.initial psi)) t).matrixQueries≤6*c.matrixCalls ∧
    (((reducedProcess F c).lower.terminalPath (.initial psi)) t).vectorQueries≤3*c.vectorCalls ∧
    (reducedProcess F c).terminalWork t≤3*c.work+14406*c.matrixCalls+3*c.vectorCalls ∧
    (reducedProcess F c).terminalMeasurements t≤3*(c.measurements+1) := by
  have ht:=(reducedProcess F c).terminal_resources psi t
  have hr:=reducedProcess_resources F c
  rw [←(reducedProcess F c).lower_matrixCalls,←(reducedProcess F c).lower_vectorCalls] at ht
  exact ⟨ht.1.trans hr.2.2.1,ht.2.1.trans hr.2.2.2.1,ht.2.2.1.trans hr.1,
    ht.2.2.2.trans hr.2.1⟩

/-- All fresh registers start in the literal zero bit pattern when the supplied
solver does. No unknown quantum input is copied and no full-register reset is charged. -/
theorem reducedInput_zero (zero : P) (hzero : chart zero=fun _=>false) :
    (poolRegister (adaptedRegister chart) n 3).bits
      (poolPoint (adaptedRegister chart) n (adaptedZero zero) (fun _=>false) 3)=fun _=>false := by
  apply poolPoint_zero_bits
  funext i
  cases i with
  | inl i =>
    cases i with
    | inl i => rfl
    | inr i => change chart zero i=false;rw [hzero]
  | inr i => cases i with
    | inl i => rfl
    | inr i => cases i <;> rfl

/-- The same reduced program is selected before every pair of complete input
oracles and every target. The source algorithm's success and accuracy are the
legitimate hypotheses of the reduction, not assumptions about its implementation. -/
theorem proposition23_uniform_reduction (F : OutputLayout chart n) (c : AnyProgram chart a n)
    (zero : P) :
    ∃ result : Process (matrixArguments a n) (Equiv.refl (Bits n)) (dataRegister n)
      (poolRegister (adaptedRegister chart) n 3),
    result.work≤3*c.work+14406*c.matrixCalls+3*c.vectorCalls ∧
    result.measurements≤3*(c.measurements+1) ∧
    matrixDepth result.lower≤6*c.matrixCalls ∧ result.lower.vectorDepth≤3*c.vectorCalls ∧
    RegisterBound (2^(4*Fintype.card W+16)) result.lower ∧
    ∀ (UA : Matrix.unitaryGroup (Bits a × Bits n) ℂ) (Ub : Matrix.unitaryGroup (Bits n) ℂ)
      (x : EuclideanSpace ℂ (Fin (dataRegister n).dimension)) (ε : ℝ),
      ‖x‖=1→0<ε→ε<1/2→
      Returns (CloseDoubledState (doubledIndex n) x ε)
        (dilationEncoding UA) (preparation Ub) (c.lower F) (basis ((Fintype.equivFin P) zero))→
      2/3≤(c.lower F).successProbability (dilationEncoding UA) (preparation Ub)
        (basis ((Fintype.equivFin P) zero))→
      (2:ℝ)/3<result.lower.successProbability UA Ub (reducedInput (chart := chart) zero) ∧
      (∀ t : result.lower.Terminal,result.lower.terminalSuccess t=true→
        CloseState x ε ((result.lower.terminalPath
          (.initial (reducedInput (chart := chart) zero)) t).state UA Ub)) := by
  have h:=reducedProcess_resources F c
  exact ⟨reducedProcess F c,h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2,
    fun UA Ub x ε hx hε0 hε1 hr hp=>reducedProcess_correct F c zero UA Ub x hx hε0 hε1 hr hp⟩

end OptimalQLS.Reduction.GenericSolver.FreshCopies
