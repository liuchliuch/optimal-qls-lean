import OptimalQLS.Reduction.GenericSolver.Branchwise

/-! Literal right-data-qubit extraction on every successful branch. -/
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
namespace OptimalQLS.Reduction.GenericSolver
open Matrix LowerBounds Refinement.Repetition
set_option maxHeartbeats 500000
universe u v
variable {d m w : ℕ}

def CloseDoubledState (E : (Fin d ⊕ Fin d) ≃ Fin m)
    (x : EuclideanSpace ℂ (Fin d)) (ε : ℝ) (v : Fin m → ℂ) : Prop :=
  ∃ y : EuclideanSpace ℂ (Fin d ⊕ Fin d), ‖y‖=1 ∧
    ‖y-WithLp.toLp 2 (rightState (fun i => x i))‖ ≤ ε/2 ∧
    pureDensity v = bornMass v • pureDensity (fun i => y (E.symm i))

theorem CloseDoubledState.smul {E : (Fin d ⊕ Fin d) ≃ Fin m}
    {x : EuclideanSpace ℂ (Fin d)} {ε : ℝ} {v : Fin m → ℂ}
    (h : CloseDoubledState E x ε v) (c : ℂ) : CloseDoubledState E x ε (c • v) := by
  obtain ⟨y,hy,he,hv⟩ := h
  refine ⟨y,hy,he,?_⟩
  rw [pureDensity_complex_smul,bornMass_smul,hv,smul_smul]

theorem extract_closeDoubledState (E : (Fin d ⊕ Fin d) ≃ Fin m)
    (x : EuclideanSpace ℂ (Fin d)) {ε : ℝ} (hx : ‖x‖=1)
    (hε0 : 0<ε) (hε1 : ε<1/2) (v : Fin m → ℂ)
    (h : CloseDoubledState E x ε v) :
    CloseState x ε (fun i => v (extractRightEmbedding E i)) ∧
    (9:ℝ)/16 * bornMass v ≤ bornMass (fun i => v (extractRightEmbedding E i)) := by
  obtain ⟨y,hy,he,hv⟩ := h
  have hg := extraction_guarantee y x hy hx hε0 hε1 he
  have hd : pureDensity (fun i => v (extractRightEmbedding E i)) =
      bornMass v • pureDensity (fun i => y (.inr i)) := by
    have hh := congrArg (extractDensity (extractRightEmbedding E)) hv
    simpa only [extractDensity_pure,map_smul,extractRightEmbedding,
      Function.Embedding.coeFn_mk,Equiv.symm_apply_apply] using hh
  have hm : bornMass (fun i => v (extractRightEmbedding E i)) =
      bornMass v * ‖rightPart y‖^2 := by
    rw [bornMass_eq_trace,hd,Matrix.trace_smul,Complex.smul_re,
      ←bornMass_eq_trace]
    rw [bornMass_eq_norm_sq (fun i => y (.inr i))]
    rfl
  have hp : 0<‖rightPart y‖^2 := by linarith [hg.2.2.2.1]
  constructor
  · refine ⟨NormedSpace.normalize (rightPart y),hg.2.2.2.2.2,hg.2.2.2.2.1,?_⟩
    rw [hd,hm]
    have hz := normalized_density (fun i => y (.inr i))
    change pureDensity (fun i => NormedSpace.normalize (rightPart y) i) = _ at hz
    rw [hz,bornMass_eq_norm_sq (fun i => y (.inr i)),smul_smul]
    change bornMass v • pureDensity (fun i => y (.inr i)) =
      (bornMass v * ‖rightPart y‖^2 * (‖rightPart y‖^2)⁻¹) • _
    rw [mul_assoc,mul_inv_cancel₀ hp.ne',mul_one]
  · rw [hm]
    have hv0 : 0≤bornMass v := by rw [bornMass_eq_norm_sq]; positivity
    nlinarith [mul_le_mul_of_nonneg_left hg.2.2.2.1 hv0]

variable {A : Type u} {B : Type v} [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B]

/-- A pointwise successful-leaf inequality sums to the corresponding bound on
actual unnormalized execution; neither purity nor a convexity assumption is used. -/
theorem returns_extraction_mass (P : (Fin m → ℂ) → Prop)
    (e : Fin d ↪ Fin m) (c : ℝ)
    (hP : ∀ v, P v → c * bornMass v ≤ bornMass (fun i => v (e i)))
    (tree : FiniteOracleProgram A B m w)
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ)
    (v : Fin w → ℂ) (h : Returns P UA Ub tree v) :
    c * traceReal (tree.executeDensity UA Ub id v) ≤
      traceReal (extractDensity e (tree.executeDensity UA Ub id v)) := by
  induction tree with
  | output flag aborted =>
    cases flag
    · simp [FiniteOracleProgram.executeDensity]
    · simpa only [FiniteOracleProgram.executeDensity,id_eq,ite_true,
        extractDensity_pure,traceReal,LinearMap.coe_mk,AddHom.coe_mk,
        ←bornMass_eq_trace] using hP v (h rfl)
  | matrixQuery p adj tree ih => exact ih _ h
  | vectorQuery p adj tree ih => exact ih _ h
  | instrument r dims K hn tree ih =>
    simp only [FiniteOracleProgram.executeDensity,map_sum,Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ => ih i _ (h i))

theorem attemptMass_branchwise (E : (Fin d ⊕ Fin d) ≃ Fin m)
    (x : EuclideanSpace ℂ (Fin d)) {ε : ℝ} (hx : ‖x‖=1)
    (hε0 : 0<ε) (hε1 : ε<1/2) (tree : FiniteOracleProgram A B m w)
    (zero : Fin w) (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ)
    (h : Returns (CloseDoubledState E x ε) UA Ub tree (basis zero))
    (hp : 2/3≤tree.successProbability UA Ub (basis zero)) :
    3/8≤attemptMass tree (extractRightEmbedding E) zero UA Ub := by
  have hm := returns_extraction_mass (CloseDoubledState E x ε)
    (extractRightEmbedding E) (9/16)
    (fun v hv => (extract_closeDoubledState E x hx hε0 hε1 v hv).2)
    tree UA Ub (basis zero) h
  change 9/16*tree.successProbability UA Ub (basis zero) ≤
    attemptMass tree (extractRightEmbedding E) zero UA Ub at hm
  linarith

end OptimalQLS.Reduction.GenericSolver
