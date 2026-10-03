import OptimalQLS.OracleCircuit
import Mathlib.Tactic

/-! # Literal control, adjoint and oracle substitution for query programs -/
noncomputable section
namespace OptimalQLS
open Matrix
variable {S A B W : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B] [Fintype W] [DecidableEq W]

def QueryPort.comp (p : QueryPort A W) (q : QueryPort S A) : QueryPort S W where
  multiplicity := q.multiplicity * p.multiplicity
  wiring := (Equiv.prodCongr (Equiv.refl S) finProdFinEquiv.symm).trans
    ((Equiv.prodAssoc S (Fin q.multiplicity) (Fin p.multiplicity)).symm.trans
      ((Equiv.prodCongr q.wiring (Equiv.refl (Fin p.multiplicity))).trans p.wiring))
  control k := q.control (finProdFinEquiv.symm k).1 && p.control (finProdFinEquiv.symm k).2

theorem QueryPort.comp_wiring (p : QueryPort A W) (q : QueryPort S A)
    (i : S) (j : Fin q.multiplicity) (k : Fin p.multiplicity) :
    (p.comp q).wiring (i,finProdFinEquiv (j,k)) = p.wiring (q.wiring (i,j),k) := by
  simp [QueryPort.comp]

theorem QueryPort.apply_entries (p : QueryPort S W) (U : Matrix.unitaryGroup S ℂ)
    (i j : S) (k l : Fin p.multiplicity) :
    (p.apply U : Matrix W W ℂ) (p.wiring (i,k)) (p.wiring (j,l)) =
      if k = l then (if p.control k then U i j else if i = j then 1 else 0) else 0 := by
  by_cases h : k = l
  · subst l; cases hc : p.control k <;> simp [hc, QueryPort.apply, rewireUnitary, controlledUnitary,
      Matrix.blockDiagonal_apply, Matrix.one_apply]
  · simp [QueryPort.apply, rewireUnitary, controlledUnitary,
      Matrix.blockDiagonal_apply, h, Ne.symm h]

theorem QueryPort.comp_apply (p : QueryPort A W) (q : QueryPort S A)
    (U : Matrix.unitaryGroup S ℂ) : (p.comp q).apply U = p.apply (q.apply U) := by
  apply Subtype.ext
  ext w w'
  obtain ⟨⟨a,k⟩,rfl⟩ := p.wiring.surjective w
  obtain ⟨⟨a',k'⟩,rfl⟩ := p.wiring.surjective w'
  obtain ⟨⟨i,j⟩,rfl⟩ := q.wiring.surjective a
  obtain ⟨⟨i',j'⟩,rfl⟩ := q.wiring.surjective a'
  rw [← p.comp_wiring q i j k, ← p.comp_wiring q i' j' k']
  rw [QueryPort.apply_entries, QueryPort.comp_wiring, QueryPort.comp_wiring,
    QueryPort.apply_entries]
  simp only [QueryPort.comp, Equiv.apply_symm_apply, Equiv.symm_apply_apply]
  by_cases hk : k = k' <;> by_cases hj : j = j' <;> by_cases hi : i = i' <;>
    cases hp : p.control k <;> cases hq : q.control j <;>
      simp_all [QueryPort.apply_entries, q.wiring.injective.eq_iff,
        finProdFinEquiv.injective.eq_iff]

/-- Lift a literal instruction to a controlled, explicitly wired workspace. -/
def QueryInstruction.lift (p : QueryPort A W) : QueryInstruction S B A → QueryInstruction S B W
  | .work U => .work (p.apply U)
  | .matrixCall q b => .matrixCall (p.comp q) b
  | .vectorCall q b => .vectorCall (p.comp q) b

def QueryCircuit.lift (p : QueryPort A W) (c : QueryCircuit S B A) : QueryCircuit S B W :=
  c.map (QueryInstruction.lift p)

theorem QueryInstruction.lift_eval (p : QueryPort A W) (g : QueryInstruction S B A)
    (UA : Matrix.unitaryGroup S ℂ) (Ub : Matrix.unitaryGroup B ℂ) :
    (g.lift p).eval UA Ub = p.apply (g.eval UA Ub) := by
  cases g <;> simp [QueryInstruction.lift, QueryInstruction.eval, QueryPort.comp_apply]

theorem QueryCircuit.lift_eval (p : QueryPort A W) (c : QueryCircuit S B A)
    (UA : Matrix.unitaryGroup S ℂ) (Ub : Matrix.unitaryGroup B ℂ) :
    (c.lift p).eval UA Ub = p.apply (c.eval UA Ub) := by
  induction c with
  | nil => exact (p.unitaryHom.map_one).symm
  | cons g c ih =>
    change QueryCircuit.eval UA Ub (QueryCircuit.lift p c) * (g.lift p).eval UA Ub =
      p.apply (QueryCircuit.eval UA Ub c * g.eval UA Ub)
    rw [ih, QueryInstruction.lift_eval]
    exact (p.unitaryHom.map_mul _ _).symm

theorem QueryCircuit.lift_counts (p : QueryPort A W) (c : QueryCircuit S B A) :
    (c.lift p).matrixQueries = c.matrixQueries ∧ (c.lift p).vectorQueries = c.vectorQueries := by
  induction c with
  | nil => simp [QueryCircuit.lift, matrixQueries, vectorQueries]
  | cons g c ih =>
    cases g <;> simp_all [QueryCircuit.lift, QueryInstruction.lift, matrixQueries, vectorQueries]

def QueryInstruction.adjoint : QueryInstruction A B W → QueryInstruction A B W
  | .work U => .work U⁻¹
  | .matrixCall p b => .matrixCall p (!b)
  | .vectorCall p b => .vectorCall p (!b)

def QueryCircuit.adjoint : QueryCircuit A B W → QueryCircuit A B W
  | [] => []
  | g :: c => QueryCircuit.adjoint c ++ [g.adjoint]

theorem QueryInstruction.adjoint_eval (g : QueryInstruction A B W)
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) :
    g.adjoint.eval UA Ub = (g.eval UA Ub)⁻¹ := by
  cases g with
  | work U => rfl
  | matrixCall p b => cases b <;> simp [adjoint, eval, QueryPort.apply_inv]
  | vectorCall p b => cases b <;> simp [adjoint, eval, QueryPort.apply_inv]

theorem QueryCircuit.adjoint_eval (c : QueryCircuit A B W)
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) :
    c.adjoint.eval UA Ub = (c.eval UA Ub)⁻¹ := by
  induction c with
  | nil => simp [adjoint, eval]
  | cons g c ih => simp [adjoint, eval_append, eval, ih, QueryInstruction.adjoint_eval]

theorem QueryCircuit.adjoint_counts (c : QueryCircuit A B W) :
    c.adjoint.matrixQueries = c.matrixQueries ∧ c.adjoint.vectorQueries = c.vectorQueries := by
  induction c with
  | nil => simp [adjoint, matrixQueries, vectorQueries]
  | cons g c ih =>
    cases g <;> simp [adjoint, matrixQueries_append, vectorQueries_append,
      QueryInstruction.adjoint, matrixQueries, vectorQueries, ih.1, ih.2]

/-- Replace one matrix-oracle instruction by the actual realizing program,
including its explicit control, wiring and possible adjoint. -/
def QueryInstruction.substituteMatrix (d : QueryCircuit S B A) :
    QueryInstruction A B W → QueryCircuit S B W
  | .work U => [.work U]
  | .matrixCall p b => QueryCircuit.lift p (if b then d.adjoint else d)
  | .vectorCall p b => [.vectorCall p b]

def QueryCircuit.substituteMatrix (c : QueryCircuit A B W) (d : QueryCircuit S B A) :
    QueryCircuit S B W := c.flatMap (QueryInstruction.substituteMatrix d)

theorem QueryInstruction.substituteMatrix_eval (d : QueryCircuit S B A)
    (g : QueryInstruction A B W) (UA : Matrix.unitaryGroup S ℂ)
    (Ub : Matrix.unitaryGroup B ℂ) :
    (g.substituteMatrix d).eval UA Ub = g.eval (d.eval UA Ub) Ub := by
  cases g with
  | work U => simp [substituteMatrix, QueryCircuit.eval, eval]
  | matrixCall p b =>
    cases b <;> simp [substituteMatrix, QueryCircuit.lift_eval, QueryCircuit.adjoint_eval, eval]
  | vectorCall p b => simp [substituteMatrix, QueryCircuit.eval, eval]

/-- Operational substitution holds for the whole input unitary, not only its block. -/
theorem QueryCircuit.substituteMatrix_eval (d : QueryCircuit S B A)
    (c : QueryCircuit A B W) (UA : Matrix.unitaryGroup S ℂ) (Ub : Matrix.unitaryGroup B ℂ) :
    (c.substituteMatrix d).eval UA Ub = c.eval (d.eval UA Ub) Ub := by
  induction c with
  | nil => rfl
  | cons g c ih =>
    simp only [substituteMatrix, List.flatMap_cons, eval_append, QueryInstruction.substituteMatrix_eval]
    change QueryCircuit.eval UA Ub (QueryCircuit.substituteMatrix c d) *
      g.eval (d.eval UA Ub) Ub = _
    rw [ih]
    rfl

/-- Each outer matrix query is charged the exact two-oracle cost of its
implementing circuit. Controls and adjoints do not conceal extra queries. -/
theorem QueryCircuit.substituteMatrix_counts (d : QueryCircuit S B A)
    (c : QueryCircuit A B W) :
    (c.substituteMatrix d).matrixQueries = c.matrixQueries * d.matrixQueries ∧
    (c.substituteMatrix d).vectorQueries =
      c.matrixQueries * d.vectorQueries + c.vectorQueries := by
  induction c with
  | nil => simp [substituteMatrix, matrixQueries, vectorQueries]
  | cons g c ih =>
    have hL (p : QueryPort A W) (b : Bool) :
        (QueryCircuit.lift p (if b then d.adjoint else d)).matrixQueries = d.matrixQueries ∧
        (QueryCircuit.lift p (if b then d.adjoint else d)).vectorQueries = d.vectorQueries := by
      cases b <;> simp [(lift_counts _ _).1, (lift_counts _ _).2,
        (adjoint_counts _).1, (adjoint_counts _).2]
    cases g with
    | work U =>
      simpa [substituteMatrix, QueryInstruction.substituteMatrix, matrixQueries_append,
        vectorQueries_append, matrixQueries, vectorQueries] using ih
    | matrixCall p b =>
      simp only [substituteMatrix, List.flatMap_cons, QueryInstruction.substituteMatrix,
        matrixQueries_append, vectorQueries_append, (hL p b).1, (hL p b).2]
      change d.matrixQueries + (QueryCircuit.substituteMatrix c d).matrixQueries = _ ∧
        d.vectorQueries + (QueryCircuit.substituteMatrix c d).vectorQueries = _
      rw [ih.1, ih.2]
      simp [matrixQueries, vectorQueries, Nat.add_mul, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
    | vectorCall p b =>
      simp only [substituteMatrix, List.flatMap_cons, QueryInstruction.substituteMatrix,
        matrixQueries_append, vectorQueries_append, matrixQueries, vectorQueries]
      change 0 + (QueryCircuit.substituteMatrix c d).matrixQueries = _ ∧
        1 + (QueryCircuit.substituteMatrix c d).vectorQueries = _
      rw [ih.1, ih.2]
      simp [Nat.add_comm, Nat.add_left_comm]

end OptimalQLS
