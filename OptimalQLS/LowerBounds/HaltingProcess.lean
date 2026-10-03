import OptimalQLS.LowerBounds.HaltingTermination

/-!
# Concrete finite halting quantum processes

A round queries only the live memory, then applies a finite exit/continue
instrument. Completed output is retained untouched. The state is deliberately
unnormalized in each sector; their total trace is preserved by actual Kraus
identities. This supports literal stopping and continuation residuals.
-/
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
namespace OptimalQLS.LowerBounds
open Matrix

structure HaltingState (D A : Type*) where
  completed : Matrix D D ℂ
  live : Matrix A A ℂ

variable {D A O : Type*} [Fintype D] [DecidableEq D] [Fintype A] [DecidableEq A]
  [Fintype O] [DecidableEq O]

def HaltingState.matrix (s : HaltingState D A) : Matrix (D ⊕ A) (D ⊕ A) ℂ :=
  Matrix.fromBlocks s.completed 0 0 s.live

def HaltingState.Positive (s : HaltingState D A) : Prop := s.completed.PosSemidef ∧ s.live.PosSemidef

def HaltingState.mass (s : HaltingState D A) : ℂ := s.completed.trace + s.live.trace

def HaltingState.addCompleted (Y : Matrix D D ℂ) (s : HaltingState D A) : HaltingState D A :=
  ⟨Y + s.completed, s.live⟩

theorem HaltingState.matrix_positive (s : HaltingState D A) (hs : s.Positive) : s.matrix.PosSemidef :=
  blockDiagonal_positive hs.1 hs.2

theorem HaltingState.matrix_trace (s : HaltingState D A) : s.matrix.trace = s.mass :=
  trace_blockDiagonal _ _

structure HaltingRound (O D A : Type*) [Fintype D] [Fintype A] [DecidableEq A] where
  port : OptimalQLS.QueryPort O A
  adjoint : Bool
  instrument : HaltingInstrument D A

def HaltingRound.query (r : HaltingRound O D A) (U : Matrix.unitaryGroup O ℂ) : Matrix.unitaryGroup A ℂ :=
  r.port.apply (if r.adjoint then U⁻¹ else U)

def HaltingRound.queried (r : HaltingRound O D A) (U : Matrix.unitaryGroup O ℂ)
    (X : Matrix A A ℂ) : Matrix A A ℂ :=
  (r.query U : Matrix A A ℂ) * X * (r.query U : Matrix A A ℂ).conjTranspose

def HaltingRound.apply (r : HaltingRound O D A) (U : Matrix.unitaryGroup O ℂ)
    (s : HaltingState D A) : HaltingState D A :=
  ⟨s.completed + r.instrument.exit (r.queried U s.live), r.instrument.continue (r.queried U s.live)⟩

theorem HaltingRound.queried_positive (r : HaltingRound O D A) (U : Matrix.unitaryGroup O ℂ)
    {X : Matrix A A ℂ} (hX : X.PosSemidef) : (r.queried U X).PosSemidef :=
  hX.mul_mul_conjTranspose_same _

theorem HaltingRound.queried_trace (r : HaltingRound O D A) (U : Matrix.unitaryGroup O ℂ)
    (X : Matrix A A ℂ) : (r.queried U X).trace = X.trace := by
  rw [HaltingRound.queried, Matrix.trace_mul_cycle]
  have hU : (r.query U : Matrix A A ℂ).conjTranspose * (r.query U : Matrix A A ℂ) = 1 :=
    (r.query U).property.1
  rw [hU, Matrix.one_mul]

theorem HaltingRound.apply_positive (r : HaltingRound O D A) (U : Matrix.unitaryGroup O ℂ)
    (s : HaltingState D A) (hs : s.Positive) : (r.apply U s).Positive := by
  have hX := r.queried_positive U hs.2
  exact ⟨hs.1.add (r.instrument.exit_positive hX), r.instrument.continue_positive hX⟩

theorem HaltingRound.apply_mass (r : HaltingRound O D A) (U : Matrix.unitaryGroup O ℂ)
    (s : HaltingState D A) : (r.apply U s).mass = s.mass := by
  change (s.completed + r.instrument.exit (r.queried U s.live)).trace +
    (r.instrument.continue (r.queried U s.live)).trace = _
  rw [Matrix.trace_add, add_assoc, r.instrument.trace_preserved, r.queried_trace]
  rfl

theorem HaltingRound.apply_addCompleted (r : HaltingRound O D A) (U : Matrix.unitaryGroup O ℂ)
    (Y : Matrix D D ℂ) (s : HaltingState D A) :
    r.apply U (s.addCompleted Y) = (r.apply U s).addCompleted Y := by
  cases s
  simp [HaltingRound.apply, HaltingState.addCompleted, add_assoc]

def HaltingRound.fullQuery (r : HaltingRound O D A) (U : Matrix.unitaryGroup O ℂ) :
    Matrix.unitaryGroup (D ⊕ A) ℂ := blockSumUnitary 1 (r.query U)

/-- One round is exactly a unitary query followed by the proved Kraus channel. -/
theorem HaltingRound.apply_matrix (r : HaltingRound O D A) (U : Matrix.unitaryGroup O ℂ)
    (s : HaltingState D A) :
    (r.apply U s).matrix = r.instrument.channel.apply
      ((r.fullQuery U : Matrix (D ⊕ A) (D ⊕ A) ℂ) * s.matrix *
        (r.fullQuery U : Matrix (D ⊕ A) (D ⊕ A) ℂ).conjTranspose) := by
  have heq : (r.fullQuery U : Matrix (D ⊕ A) (D ⊕ A) ℂ) * s.matrix *
      (r.fullQuery U : Matrix (D ⊕ A) (D ⊕ A) ℂ).conjTranspose =
      Matrix.fromBlocks s.completed 0 0 (r.queried U s.live) := by
    change Matrix.fromBlocks 1 0 0 (r.query U : Matrix A A ℂ) *
      Matrix.fromBlocks s.completed 0 0 s.live *
      (Matrix.fromBlocks 1 0 0 (r.query U : Matrix A A ℂ)).conjTranspose = _
    rw [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    simp [HaltingRound.queried]
  rw [heq, r.instrument.channel_apply]
  rfl

abbrev HaltingProgram (O D A : Type*) [Fintype D] [Fintype A] [DecidableEq A] := List (HaltingRound O D A)

def HaltingProgram.run (p : HaltingProgram O D A) (U : Matrix.unitaryGroup O ℂ)
    (s : HaltingState D A) : HaltingState D A :=
  match p with
  | [] => s
  | r :: rest => HaltingProgram.run rest U (r.apply U s)

theorem HaltingProgram.run_append (p q : HaltingProgram O D A) (U : Matrix.unitaryGroup O ℂ)
    (s : HaltingState D A) : (p ++ q).run U s = q.run U (p.run U s) := by
  induction p generalizing s with
  | nil => rfl
  | cons r rest ih => exact ih _

theorem HaltingProgram.run_positive (p : HaltingProgram O D A) (U : Matrix.unitaryGroup O ℂ)
    (s : HaltingState D A) (hs : s.Positive) : (p.run U s).Positive := by
  induction p generalizing s with
  | nil => exact hs
  | cons r rest ih => exact ih _ (r.apply_positive U s hs)

theorem HaltingProgram.run_mass (p : HaltingProgram O D A) (U : Matrix.unitaryGroup O ℂ)
    (s : HaltingState D A) : (p.run U s).mass = s.mass := by
  induction p generalizing s with
  | nil => rfl
  | cons r rest ih => exact (ih _).trans (r.apply_mass U s)

theorem HaltingProgram.run_addCompleted (p : HaltingProgram O D A) (U : Matrix.unitaryGroup O ℂ)
    (Y : Matrix D D ℂ) (s : HaltingState D A) :
    p.run U (s.addCompleted Y) = (p.run U s).addCompleted Y := by
  induction p generalizing s with
  | nil => rfl
  | cons r rest ih =>
    simp only [run, r.apply_addCompleted, ih]

theorem HaltingProgram.run_decomposition (p : HaltingProgram O D A) (U : Matrix.unitaryGroup O ℂ)
    (Y : Matrix D D ℂ) (X : Matrix A A ℂ) :
    p.run U ⟨Y, X⟩ = (p.run U ⟨0, X⟩).addCompleted Y := by
  have h := p.run_addCompleted U Y ⟨0, X⟩
  simpa [HaltingState.addCompleted] using h

/-- Actual eventual contribution of initially live mass under the remaining program. -/
def HaltingProgram.residual (p : HaltingProgram O D A) (U : Matrix.unitaryGroup O ℂ)
    (F : FiniteChannel A D) (X : Matrix A A ℂ) : Matrix D D ℂ :=
  (p.run U ⟨0, X⟩).completed + F.apply (p.run U ⟨0, X⟩).live

theorem HaltingProgram.residual_positive (p : HaltingProgram O D A) (U : Matrix.unitaryGroup O ℂ)
    (F : FiniteChannel A D) {X : Matrix A A ℂ} (hX : X.PosSemidef) : (p.residual U F X).PosSemidef := by
  have h := p.run_positive U ⟨0, X⟩ ⟨Matrix.PosSemidef.zero, hX⟩
  exact h.1.add (F.apply_positive h.2)

theorem HaltingProgram.residual_trace (p : HaltingProgram O D A) (U : Matrix.unitaryGroup O ℂ)
    (F : FiniteChannel A D) (X : Matrix A A ℂ) : (p.residual U F X).trace = X.trace := by
  rw [HaltingProgram.residual, Matrix.trace_add, F.trace_apply]
  have h := p.run_mass U ⟨0, X⟩
  simpa [HaltingState.mass] using h

def HaltingProgram.output (p : HaltingProgram O D A) (U : Matrix.unitaryGroup O ℂ)
    (F : FiniteChannel A D) (s : HaltingState D A) : Matrix (D ⊕ Unit) (D ⊕ Unit) ℂ :=
  (finishChannel F).apply (p.run U s).matrix

def HaltingProgram.truncatedOutput (p : HaltingProgram O D A) (q : ℕ)
    (U : Matrix.unitaryGroup O ℂ) (s : HaltingState D A) : Matrix (D ⊕ Unit) (D ⊕ Unit) ℂ :=
  (abortChannel (D := D) (A := A)).apply (HaltingProgram.run (p.take q) U s).matrix

/-- Completion really equals retained output plus a positive continuation residual. -/
theorem HaltingProgram.output_decomposition (p : HaltingProgram O D A) (U : Matrix.unitaryGroup O ℂ)
    (F : FiniteChannel A D) (Y : Matrix D D ℂ) (X : Matrix A A ℂ) :
    p.output U F ⟨Y, X⟩ = Matrix.fromBlocks (Y + p.residual U F X) 0 0 (0 : Matrix Unit Unit ℂ) := by
  rw [HaltingProgram.output, p.run_decomposition]
  simp only [HaltingState.addCompleted, HaltingState.matrix, finishChannel_apply,
    HaltingProgram.residual, add_assoc]

/-- The stopping-time completion cost is derived from actual program execution. -/
theorem HaltingProgram.output_truncation_distance (p : HaltingProgram O D A) (q : ℕ)
    (U : Matrix.unitaryGroup O ℂ) (F : FiniteChannel A D) (s : HaltingState D A) (hs : s.Positive) :
    traceDistance (p.output U F s) (p.truncatedOutput q U s) ≤ (HaltingProgram.run (p.take q) U s).live.trace.re := by
  let t := HaltingProgram.run (p.take q) U s
  have ht : t.Positive := HaltingProgram.run_positive (p.take q) U s hs
  have hsplit : p.run U s = HaltingProgram.run (p.drop q) U t := by
    calc
      p.run U s = HaltingProgram.run (p.take q ++ p.drop q) U s := by rw [List.take_append_drop]
      _ = _ := HaltingProgram.run_append (p.take q) (p.drop q) U s
  change traceDistance ((finishChannel F).apply (p.run U s).matrix)
    ((abortChannel (D := D) (A := A)).apply t.matrix) ≤ t.live.trace.re
  rw [hsplit]
  change traceDistance (HaltingProgram.output (p.drop q) U F t) ((abortChannel (D := D) (A := A)).apply t.matrix) ≤ _
  have htd : t = ⟨t.completed, t.live⟩ := rfl
  rw [htd, HaltingProgram.output_decomposition]
  exact completed_vs_abort_distance t.completed (HaltingProgram.residual (p.drop q) U F t.live) t.live ht.2
    (HaltingProgram.residual_positive (p.drop q) U F ht.2) (congrArg Complex.re (HaltingProgram.residual_trace (p.drop q) U F t.live))

end OptimalQLS.LowerBounds
