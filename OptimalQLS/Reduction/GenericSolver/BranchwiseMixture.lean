import OptimalQLS.Reduction.GenericSolver.BranchwiseRepetition

/-! The actual conditional density is a convex mixture of branch-dependent
accurate pure outputs. This theorem deliberately does not assert purity. -/
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
namespace OptimalQLS.Reduction.GenericSolver
open Matrix LowerBounds Refinement.Repetition
set_option maxHeartbeats 500000
universe u v
variable {A : Type u} {B : Type v} [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B] {d w : ℕ}

theorem conditionalOutput_mixture (tree : FiniteOracleProgram A B d w)
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ)
    (v : Fin w → ℂ) (x : EuclideanSpace ℂ (Fin d)) {ε : ℝ}
    (hx : ‖x‖=1) (hε : 0≤ε) (h : Returns (CloseState x ε) UA Ub tree v)
    (hp : 0<tree.successProbability UA Ub v) :
    ∃ weight : tree.Terminal → ℝ, ∃ y : tree.Terminal → EuclideanSpace ℂ (Fin d),
      (∀ k, 0≤weight k) ∧ (∑ k, weight k)=1 ∧
      (∀ k, ‖y k‖=1 ∧ ‖y k-x‖≤ε) ∧
      tree.conditionalOutput UA Ub v =
        ∑ k, weight k • pureDensity (fun i => y k i) := by
  classical
  let state := fun k : tree.Terminal =>
    (tree.terminalPath (.initial v) k).state UA Ub
  have ht := (returns_iff_terminal _ tree (.initial v) UA Ub).mp h
  let y := fun k : tree.Terminal =>
    if hk : tree.terminalSuccess k=true then (ht k hk).choose else x
  let weight := fun k : tree.Terminal =>
    if tree.terminalSuccess k then
      (tree.successProbability UA Ub v)⁻¹ * bornMass (state k) else 0
  have hy : ∀ k, ‖y k‖=1 ∧ ‖y k-x‖≤ε := by
    intro k
    by_cases hk : tree.terminalSuccess k=true
    · exact ⟨by simpa [y,hk] using (ht k hk).choose_spec.1,
        by simpa [y,hk] using (ht k hk).choose_spec.2.1⟩
    · simp [y,hk,hx,hε]
  have hd : tree.conditionalOutput UA Ub v =
      ∑ k, weight k • pureDensity (fun i => y k i) := by
    have he := tree.terminalDensity_eq_execute (.initial v) UA Ub id
    simp only [VariableQueryPath.state] at he
    rw [FiniteOracleProgram.conditionalOutput,←he,Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro k _
    by_cases hk : tree.terminalSuccess k=true
    · have hs := (ht k hk).choose_spec.2.2
      simpa only [id_eq,hk,ite_true,weight,smul_smul,y,dif_pos hk,state] using
        congrArg (fun X : Matrix (Fin d) (Fin d) ℂ =>
          (tree.successProbability UA Ub v)⁻¹ • X) hs
    · simp [id_eq,hk,weight]
  have hw : ∀ k, 0≤weight k := by
    intro k
    dsimp only [weight]
    split_ifs
    · exact mul_nonneg (inv_nonneg.mpr hp.le) (by rw [bornMass_eq_norm_sq]; positivity)
    · rfl
  have htr : traceReal (tree.conditionalOutput UA Ub v)=1 := by
    change (tree.conditionalOutput UA Ub v).trace.re=1
    rw [FiniteOracleProgram.conditionalOutput,Matrix.trace_smul,Complex.smul_re]
    exact inv_mul_cancel₀ hp.ne'
  have ht' := congrArg traceReal hd
  rw [htr,map_sum] at ht'
  have htrace (k : tree.Terminal) : traceReal (weight k • pureDensity (fun i => y k i))=weight k := by
    change (weight k • pureDensity (fun i => y k i)).trace.re=weight k
    rw [Matrix.trace_smul,Complex.smul_re,pureDensity_trace,Complex.ofReal_re]
    change weight k * ‖y k‖^2=weight k
    rw [(hy k).1]
    ring
  simp only [htrace] at ht'
  exact ⟨weight,y,hw,ht'.symm,hy,hd⟩

end OptimalQLS.Reduction.GenericSolver
