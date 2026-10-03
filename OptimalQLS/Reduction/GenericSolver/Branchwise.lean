import OptimalQLS.Reduction.Complete

/-! Branchwise output guarantees for arbitrary finite solvers.  A ket is
represented by its rank-one density, so an irrelevant path amplitude/global
phase does not change the guarantee.  Different successful branches may have
different close unit representatives; their conditional output may be mixed. -/
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
namespace OptimalQLS.Reduction.GenericSolver
open Matrix LowerBounds Refinement.Repetition
set_option maxHeartbeats 500000
universe u v

variable {D : Type*} [Fintype D] [DecidableEq D]

def CloseState (x : EuclideanSpace ℂ D) (ε : ℝ) (v : D → ℂ) : Prop :=
  ∃ y : EuclideanSpace ℂ D, ‖y‖ = 1 ∧ ‖y-x‖ ≤ ε ∧
    pureDensity v = bornMass v • pureDensity (fun i => y i)

theorem CloseState.smul {d : ℕ} {x : EuclideanSpace ℂ (Fin d)} {ε : ℝ}
    {v : Fin d → ℂ} (h : CloseState x ε v) (c : ℂ) : CloseState x ε (c • v) := by
  obtain ⟨y,hy,he,hv⟩ := h
  refine ⟨y,hy,he,?_⟩
  rw [pureDensity_complex_smul, bornMass_smul, hv, smul_smul]

theorem closeState_zero (x : EuclideanSpace ℂ D) {ε : ℝ}
    (hx : ‖x‖=1) (hε : 0≤ε) : CloseState x ε 0 := by
  refine ⟨x,hx,by simpa using hε,?_⟩
  simp [pureDensity,ketBra,bornMass]

variable {A : Type u} {B : Type v} [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B] {d m w : ℕ}

/-- The predicate is checked on each actual executed successful leaf. -/
def Returns (P : (Fin d → ℂ) → Prop)
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) :
    {w : ℕ} → FiniteOracleProgram A B d w → (Fin w → ℂ) → Prop
  | _, .output flag _, v => flag=true → P v
  | _, .matrixQuery p adj next, v => Returns P UA Ub next
      ((p.apply (if adj then UA⁻¹ else UA)).val *ᵥ v)
  | _, .vectorQuery p adj next, v => Returns P UA Ub next
      ((p.apply (if adj then Ub⁻¹ else Ub)).val *ᵥ v)
  | _, .instrument _ _ K _ next, v => ∀ i, Returns P UA Ub (next i) (K i *ᵥ v)

theorem returns_iff_terminal (P : (Fin d → ℂ) → Prop)
    (tree : FiniteOracleProgram A B d w) (path : VariableQueryPath A B w)
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) :
    Returns P UA Ub tree (path.state UA Ub) ↔ ∀ k : tree.Terminal,
      tree.terminalSuccess k=true → P ((tree.terminalPath path k).state UA Ub) := by
  induction tree with
  | output flag aborted => simp [Returns,FiniteOracleProgram.Terminal,
      FiniteOracleProgram.terminalSuccess,FiniteOracleProgram.terminalPath]
  | matrixQuery p adj next ih => exact ih (.matrixQuery p adj path)
  | vectorQuery p adj next ih => exact ih (.vectorQuery p adj path)
  | instrument r dims K hn next ih =>
    simp only [Returns,FiniteOracleProgram.Terminal,FiniteOracleProgram.terminalSuccess,
      FiniteOracleProgram.terminalPath,Sigma.forall]
    exact forall_congr' (fun i => ih i (.work (K i) path))

theorem returns_smul (P : (Fin d → ℂ) → Prop)
    (hP : ∀ v (c : ℂ), P v → P (c • v)) (tree : FiniteOracleProgram A B d w)
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ)
    (v : Fin w → ℂ) (h : Returns P UA Ub tree v) (c : ℂ) :
    Returns P UA Ub tree (c • v) := by
  induction tree with
  | output flag aborted => exact fun hf => hP v c (h hf)
  | matrixQuery p adj next ih =>
    simpa only [Returns,Matrix.mulVec_smul] using ih _ h
  | vectorQuery p adj next ih =>
    simpa only [Returns,Matrix.mulVec_smul] using ih _ h
  | instrument r dims K hn next ih =>
    intro i
    simpa only [Matrix.mulVec_smul] using ih i _ (h i)

theorem returns_bindOutput (P : (Fin d → ℂ) → Prop) (Q : (Fin m → ℂ) → Prop)
    (tree : FiniteOracleProgram A B m w) (next : Bool → FiniteOracleProgram A B d m)
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ)
    (v : Fin w → ℂ) (h : Returns Q UA Ub tree v)
    (hn : ∀ flag v, (flag=true → Q v) → Returns P UA Ub (next flag) v) :
    Returns P UA Ub (bindOutput tree next) v := by
  induction tree with
  | output flag aborted => exact hn flag v h
  | matrixQuery p adj tree ih => exact ih _ h
  | vectorQuery p adj tree ih => exact ih _ h
  | instrument r dims K hc tree ih => exact fun i => ih i _ (h i)

theorem returns_measuredReset (P : (Fin d → ℂ) → Prop)
    (hP : ∀ v (c : ℂ), P v → P (c • v)) (zero : Fin w)
    (next : FiniteOracleProgram A B d w)
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ)
    (h : Returns P UA Ub next (basis zero)) (v : Fin m → ℂ) :
    Returns P UA Ub (measuredReset zero next) v := by
  intro i
  have hk : abortBasisKraus zero i *ᵥ v = v i • basis zero := by
    ext j
    simp [abortBasisKraus,Matrix.mulVec,dotProduct,basis]
  rw [hk]
  exact returns_smul P hP next UA Ub _ h _

end OptimalQLS.Reduction.GenericSolver
