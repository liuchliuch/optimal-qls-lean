import OptimalQLS.Reduction.GenericSolver.BranchwiseExtraction

/-! Three actual executions, extraction and measured reset preserve a
branch-dependent guarantee. No pure conditional density is assumed. -/
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
namespace OptimalQLS.Reduction.GenericSolver
open Matrix LowerBounds Refinement.Repetition
set_option maxHeartbeats 500000
universe u v
variable {A : Type u} {B : Type v} [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B] {d m w : ℕ}

theorem returns_measureExtract (P : (Fin d → ℂ) → Prop)
    (hP : ∀ v (c : ℂ), P v → P (c • v)) (e : Fin d ↪ Fin m)
    (zero : Fin w) (out : Fin d) (next : FiniteOracleProgram A B d w)
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ)
    (h : Returns P UA Ub next (basis zero)) (v : Fin m → ℂ)
    (hv : P (fun i => v (e i))) : Returns P UA Ub (measureExtract e zero out next) v := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · change true=true → P (acceptMatrix e *ᵥ v)
    rw [acceptMatrix_mulVec]
    exact fun _ => hv
  · exact returns_measuredReset P hP zero next UA Ub h _

theorem retrySolver_branchwise (tree : FiniteOracleProgram A B m w)
    (E : (Fin d ⊕ Fin d) ≃ Fin m) (zero : Fin w) (out : Fin d)
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ)
    (x : EuclideanSpace ℂ (Fin d)) {ε : ℝ} (hx : ‖x‖=1)
    (hε0 : 0<ε) (hε1 : ε<1/2)
    (h : Returns (CloseDoubledState E x ε) UA Ub tree (basis zero)) (n : ℕ) :
    Returns (CloseState x ε) UA Ub
      (retrySolver tree (extractRightEmbedding E) zero out n) (basis zero) := by
  have hP : ∀ v (c : ℂ), CloseState x ε v → CloseState x ε (c • v) :=
    fun _ c hv => hv.smul c
  induction n with
  | zero =>
    intro i hf
    contradiction
  | succ n ih =>
    apply returns_bindOutput (CloseState x ε) (CloseDoubledState E x ε)
      tree _ UA Ub _ h
    intro flag v hv
    cases flag
    · exact returns_measuredReset _ hP zero _ UA Ub ih v
    · exact returns_measureExtract _ hP _ zero out _ UA Ub ih v
        (extract_closeDoubledState E x hx hε0 hε1 v (hv rfl)).1

/-- Generality-complete successful-output conclusion of Proposition 2.3.
Every actual success leaf is close, and the same concrete retry program has
success probability strictly greater than 2/3 and the displayed query costs. -/
theorem proposition23_branchwise (tree : FiniteOracleProgram A B m w)
    (E : (Fin d ⊕ Fin d) ≃ Fin m) (zero : Fin w) (out : Fin d)
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ)
    (x : EuclideanSpace ℂ (Fin d)) {ε : ℝ} (hx : ‖x‖=1)
    (hε0 : 0<ε) (hε1 : ε<1/2)
    (h : Returns (CloseDoubledState E x ε) UA Ub tree (basis zero))
    (hp : 2/3≤tree.successProbability UA Ub (basis zero)) :
    let result := retrySolver tree (extractRightEmbedding E) zero out 3
    (2:ℝ)/3 < result.successProbability UA Ub (basis zero) ∧
    (∀ k : result.Terminal, result.terminalSuccess k=true →
      CloseState x ε ((result.terminalPath (.initial (basis zero)) k).state UA Ub)) ∧
    matrixDepth result ≤ 3*matrixDepth tree ∧
    result.vectorDepth ≤ 3*tree.vectorDepth ∧
    instrumentDepth result ≤ 3*(instrumentDepth tree+2)+1 := by
  dsimp only
  refine ⟨three_attempts_success tree _ zero out UA Ub
    (attemptMass_branchwise E x hx hε0 hε1 tree zero UA Ub h hp),?_,
    retrySolver_matrixDepth tree _ zero out 3,
    retrySolver_vectorDepth tree _ zero out 3,
    retrySolver_instrumentDepth tree _ zero out 3⟩
  exact (returns_iff_terminal _ _ (.initial (basis zero)) UA Ub).mp
    (retrySolver_branchwise tree E zero out UA Ub x hx hε0 hε1 h 3)

/-- The original inverse solution is the target. Input normalization and its
promises remain the independently proved `Reduction.proposition23_input`. -/
theorem proposition23_branchwise_solution (tree : FiniteOracleProgram A B m w)
    (E : (Fin d ⊕ Fin d) ≃ Fin m) (zero : Fin w) (out : Fin d)
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ)
    (M : Matrix (Fin d) (Fin d) ℂ) (b : Fin d → ℂ)
    (hM : IsUnit M) (hb : ‖WithLp.toLp 2 b‖=1) {ε : ℝ}
    (hε0 : 0<ε) (hε1 : ε<1/2)
    (h : Returns (CloseDoubledState E
      (NormedSpace.normalize (WithLp.toLp 2 (M⁻¹ *ᵥ b))) ε) UA Ub tree (basis zero))
    (hp : 2/3≤tree.successProbability UA Ub (basis zero)) :
    let result := retrySolver tree (extractRightEmbedding E) zero out 3
    (2:ℝ)/3 < result.successProbability UA Ub (basis zero) ∧
    (∀ k : result.Terminal, result.terminalSuccess k=true →
      CloseState (NormedSpace.normalize (WithLp.toLp 2 (M⁻¹ *ᵥ b))) ε
        ((result.terminalPath (.initial (basis zero)) k).state UA Ub)) ∧
    matrixDepth result ≤ 3*matrixDepth tree ∧
    result.vectorDepth ≤ 3*tree.vectorDepth ∧
    instrumentDepth result ≤ 3*(instrumentDepth tree+2)+1 :=
  proposition23_branchwise tree E zero out UA Ub _
    (normalized_original_solution_unit M hM b hb) hε0 hε1 h hp

end OptimalQLS.Reduction.GenericSolver
