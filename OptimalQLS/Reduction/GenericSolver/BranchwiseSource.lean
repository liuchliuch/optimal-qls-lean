import OptimalQLS.Reduction.GenericSolver.BranchwiseMixture

/-! Entry points matching the source's successful-output premise. Unreachable
zero-mass branches impose no extra accuracy promise. The target is the actual
normalized inverse of the Hermitian dilation, transported by a proved identity. -/
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
namespace OptimalQLS.Reduction.GenericSolver
open Matrix LowerBounds Refinement.Repetition
set_option maxHeartbeats 500000
universe u v
variable {A : Type u} {B : Type v} [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B] {d m w : ℕ}

theorem returns_iff_positive_terminals (P : (Fin d → ℂ) → Prop) (hP : P 0)
    (tree : FiniteOracleProgram A B d w) (UA : Matrix.unitaryGroup A ℂ)
    (Ub : Matrix.unitaryGroup B ℂ) (v : Fin w → ℂ) :
    Returns P UA Ub tree v ↔ ∀ k : tree.Terminal, tree.terminalSuccess k=true →
      0<bornMass ((tree.terminalPath (.initial v) k).state UA Ub) →
      P ((tree.terminalPath (.initial v) k).state UA Ub) := by
  have he := returns_iff_terminal P tree (.initial v) UA Ub
  simp only [VariableQueryPath.state] at he
  rw [he]
  constructor
  · exact fun h k hk _ => h k hk
  · intro h k hk
    let state := (tree.terminalPath (.initial v) k).state UA Ub
    by_cases hp : 0<bornMass state
    · exact h k hk hp
    · have hn : ‖WithLp.toLp 2 state‖=0 := by
        rw [bornMass_eq_norm_sq] at hp
        nlinarith [norm_nonneg (WithLp.toLp 2 state)]
      have hz : state=0 := by
        have hh := norm_eq_zero.mp hn
        exact congrArg WithLp.ofLp hh
      change P state
      rw [hz]
      exact hP

theorem closeDoubledState_zero (E : (Fin d ⊕ Fin d) ≃ Fin m)
    (x : EuclideanSpace ℂ (Fin d)) {ε : ℝ} (hx : ‖x‖=1) (hε : 0≤ε) :
    CloseDoubledState E x ε 0 := by
  refine ⟨WithLp.toLp 2 (rightState (fun i=>x i)),?_,?_,?_⟩
  · simpa only [rightState,sumElim_norm_right] using hx
  · simp only [sub_self,norm_zero]
    positivity
  · simp [pureDensity,ketBra,bornMass]

def CloseNormalizedSolution (E : (Fin d ⊕ Fin d) ≃ Fin m)
    (α : ℝ) (M : Matrix (Fin d) (Fin d) ℂ) (b : Fin d → ℂ) (ε : ℝ)
    (v : Fin m → ℂ) : Prop :=
  ∃ y : EuclideanSpace ℂ (Fin d ⊕ Fin d), ‖y‖=1 ∧
    ‖y-NormedSpace.normalize (WithLp.toLp 2 ((normalizedMatrix α M)⁻¹ *ᵥ source b))‖≤ε/2 ∧
    pureDensity v=bornMass v • pureDensity (fun i=>y (E.symm i))

theorem closeNormalizedSolution_iff (E : (Fin d ⊕ Fin d) ≃ Fin m)
    {α : ℝ} (hα : 0<α) (M : Matrix (Fin d) (Fin d) ℂ) (hM : IsUnit M)
    (b : Fin d → ℂ) (ε : ℝ) (v : Fin m → ℂ) :
    CloseNormalizedSolution E α M b ε v ↔ CloseDoubledState E
      (NormedSpace.normalize (WithLp.toLp 2 (M⁻¹ *ᵥ b))) ε v := by
  unfold CloseNormalizedSolution CloseDoubledState
  rw [normalized_solution_direction hα M hM b]

/-- The source statement, allowing a different close ket on every positive
successful branch and imposing no restriction on the other oracle columns. -/
theorem proposition23_reachable_solution (tree : FiniteOracleProgram A B m w)
    (E : (Fin d ⊕ Fin d) ≃ Fin m) (zero : Fin w) (out : Fin d)
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ)
    {α ε : ℝ} (hα : 0<α) (M : Matrix (Fin d) (Fin d) ℂ) (b : Fin d → ℂ)
    (hM : IsUnit M) (hb : ‖WithLp.toLp 2 b‖=1)
    (hε0 : 0<ε) (hε1 : ε<1/2)
    (h : ∀ k : tree.Terminal, tree.terminalSuccess k=true →
      0<bornMass ((tree.terminalPath (.initial (basis zero)) k).state UA Ub) →
      CloseNormalizedSolution E α M b ε
        ((tree.terminalPath (.initial (basis zero)) k).state UA Ub))
    (hp : 2/3≤tree.successProbability UA Ub (basis zero)) :
    let result := retrySolver tree (extractRightEmbedding E) zero out 3
    (2:ℝ)/3 < result.successProbability UA Ub (basis zero) ∧
    (∀ k : result.Terminal, result.terminalSuccess k=true →
      CloseState (NormedSpace.normalize (WithLp.toLp 2 (M⁻¹ *ᵥ b))) ε
        ((result.terminalPath (.initial (basis zero)) k).state UA Ub)) ∧
    matrixDepth result ≤ 3*matrixDepth tree ∧
    result.vectorDepth ≤ 3*tree.vectorDepth ∧
    instrumentDepth result ≤ 3*(instrumentDepth tree+2)+1 := by
  apply proposition23_branchwise_solution tree E zero out UA Ub M b hM hb hε0 hε1
  · apply (returns_iff_positive_terminals _
      (closeDoubledState_zero E _ (normalized_original_solution_unit M hM b hb) hε0.le)
      tree UA Ub (basis zero)).mpr
    intro k hk hm
    exact (closeNormalizedSolution_iff E hα M hM b ε _).mp (h k hk hm)
  · exact hp

end OptimalQLS.Reduction.GenericSolver
