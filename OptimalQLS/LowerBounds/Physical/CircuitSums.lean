import OptimalQLS.LowerBounds.Physical.Embedding
import OptimalQLS.OracleComposition

/-! Literal gate-list wiring and direct-sum construction for bit simulations. -/
noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
namespace OptimalQLS.LowerBounds.Physical
open Matrix
variable {S B W V X : Type*} [Fintype S] [DecidableEq S] [Fintype B] [DecidableEq B]
  [Fintype W] [DecidableEq W] [Fintype V] [DecidableEq V] [Fintype X] [DecidableEq X]

/-- Known basis rewiring of every actual gate in a query list. -/
def rewireInstruction (e : W ≃ V) : QueryInstruction S B W → QueryInstruction S B V
  | .work U => .work (rewireUnitary e U)
  | .matrixCall p b => .matrixCall { p with wiring := p.wiring.trans e } b
  | .vectorCall p b => .vectorCall { p with wiring := p.wiring.trans e } b

def rewireCircuit (e : W ≃ V) (c : QueryCircuit S B W) : QueryCircuit S B V :=
  c.map (rewireInstruction e)

theorem rewireInstruction_eval (e : W ≃ V) (g : QueryInstruction S B W)
    (U : Matrix.unitaryGroup S ℂ) (T : Matrix.unitaryGroup B ℂ) :
    (rewireInstruction e g).eval U T = rewireUnitary e (g.eval U T) := by
  cases g <;> apply Subtype.ext <;> rfl

theorem rewireCircuit_eval (e : W ≃ V) (c : QueryCircuit S B W)
    (U : Matrix.unitaryGroup S ℂ) (T : Matrix.unitaryGroup B ℂ) :
    (rewireCircuit e c).eval U T = rewireUnitary e (c.eval U T) := by
  induction c with
  | nil => exact (rewireUnitary_one e).symm
  | cons g c ih =>
    change (rewireCircuit e c).eval U T * (rewireInstruction e g).eval U T = _
    rw [ih, rewireInstruction_eval, ← rewireUnitary_mul]
    rfl

theorem rewireCircuit_counts (e : W ≃ V) (c : QueryCircuit S B W) :
    (rewireCircuit e c).matrixQueries = c.matrixQueries ∧
      (rewireCircuit e c).vectorQueries = c.vectorQueries := by
  induction c with
  | nil => exact ⟨rfl,rfl⟩
  | cons g c ih => cases g <;> simp_all [rewireCircuit, rewireInstruction,
      QueryCircuit.matrixQueries, QueryCircuit.vectorQueries]

def inactivePort (p : QueryPort S W) : QueryPort S W := {p with control := fun _ => false}

@[simp] theorem inactivePort_apply (p : QueryPort S W) (U : Matrix.unitaryGroup S ℂ) :
    (inactivePort p).apply U = 1 := by
  apply Subtype.ext
  simp only [inactivePort, QueryPort.apply, rewireUnitary, controlledUnitary, Bool.false_eq_true, if_false]
  rw [show (fun _ : Fin p.multiplicity => (1 : Matrix S S ℂ)) = 1 from rfl, Matrix.blockDiagonal_one]
  simp

/-- A literal query port on a disjoint union, preserving both sector controls. -/
def sumPort (p : QueryPort S W) (q : QueryPort S V) : QueryPort S (W ⊕ V) where
  multiplicity := p.multiplicity + q.multiplicity
  wiring := (Equiv.prodCongr (Equiv.refl S) finSumFinEquiv.symm).trans
    ((Equiv.prodSumDistrib S (Fin p.multiplicity) (Fin q.multiplicity)).trans
      (Equiv.sumCongr p.wiring q.wiring))
  control k := Sum.elim p.control q.control (finSumFinEquiv.symm k)

@[simp] theorem sumPort_wiring_left (p : QueryPort S W) (q : QueryPort S V)
    (i : S) (k : Fin p.multiplicity) :
    (sumPort p q).wiring (i,finSumFinEquiv (.inl k)) = .inl (p.wiring (i,k)) := by
  simp [sumPort]

@[simp] theorem sumPort_wiring_right (p : QueryPort S W) (q : QueryPort S V)
    (i : S) (k : Fin q.multiplicity) :
    (sumPort p q).wiring (i,finSumFinEquiv (.inr k)) = .inr (q.wiring (i,k)) := by
  simp [sumPort]

theorem sumPort_apply (p : QueryPort S W) (q : QueryPort S V) (U : Matrix.unitaryGroup S ℂ) :
    (sumPort p q).apply U = blockSumUnitary (p.apply U) (q.apply U) := by
  apply Subtype.ext
  ext x y
  cases x with
  | inl x =>
    obtain ⟨⟨i,k⟩,rfl⟩ := p.wiring.surjective x
    cases y with
    | inl y =>
      obtain ⟨⟨j,l⟩,rfl⟩ := p.wiring.surjective y
      rw [← sumPort_wiring_left p q i k, ← sumPort_wiring_left p q j l, QueryPort.apply_entries]
      simp [sumPort, blockSumUnitary, QueryPort.apply_entries, finSumFinEquiv.injective.eq_iff]
    | inr y =>
      obtain ⟨⟨j,l⟩,rfl⟩ := q.wiring.surjective y
      rw [← sumPort_wiring_left p q i k, ← sumPort_wiring_right p q j l, QueryPort.apply_entries]
      simp [sumPort, blockSumUnitary, finSumFinEquiv.injective.eq_iff]
      intro he
      have hv := congrArg Fin.val he
      simp at hv
      omega
  | inr x =>
    obtain ⟨⟨i,k⟩,rfl⟩ := q.wiring.surjective x
    cases y with
    | inl y =>
      obtain ⟨⟨j,l⟩,rfl⟩ := p.wiring.surjective y
      rw [← sumPort_wiring_right p q i k, ← sumPort_wiring_left p q j l, QueryPort.apply_entries]
      simp [sumPort, blockSumUnitary, finSumFinEquiv.injective.eq_iff]
      intro he
      have hv := congrArg Fin.val he
      simp at hv
      omega
    | inr y =>
      obtain ⟨⟨j,l⟩,rfl⟩ := q.wiring.surjective y
      rw [← sumPort_wiring_right p q i k, ← sumPort_wiring_right p q j l, QueryPort.apply_entries]
      simp [sumPort, blockSumUnitary, QueryPort.apply_entries, finSumFinEquiv.injective.eq_iff]

def sumLeftInstruction (p : QueryPort S V) (q : QueryPort B V) :
    QueryInstruction S B W → QueryInstruction S B (W ⊕ V)
  | .work U => .work (blockSumUnitary U 1)
  | .matrixCall r b => .matrixCall (sumPort r (inactivePort p)) b
  | .vectorCall r b => .vectorCall (sumPort r (inactivePort q)) b

def sumLeftCircuit (p : QueryPort S V) (q : QueryPort B V) (c : QueryCircuit S B W) :
    QueryCircuit S B (W ⊕ V) := c.map (sumLeftInstruction p q)

theorem blockSumUnitary_mul (U U' : Matrix.unitaryGroup W ℂ) (R R' : Matrix.unitaryGroup V ℂ) :
    blockSumUnitary (U*U') (R*R') = blockSumUnitary U R * blockSumUnitary U' R' := by
  apply Subtype.ext
  simp [blockSumUnitary, Matrix.fromBlocks_multiply]

@[simp] theorem blockSumUnitary_one :
    blockSumUnitary (1 : Matrix.unitaryGroup W ℂ) (1 : Matrix.unitaryGroup V ℂ) = 1 := by
  apply Subtype.ext
  simp [blockSumUnitary]

theorem sumLeftInstruction_eval (p : QueryPort S V) (q : QueryPort B V)
    (g : QueryInstruction S B W) (U : Matrix.unitaryGroup S ℂ) (T : Matrix.unitaryGroup B ℂ) :
    (sumLeftInstruction p q g).eval U T = blockSumUnitary (g.eval U T) 1 := by
  cases g <;> simp [sumLeftInstruction, QueryInstruction.eval, sumPort_apply]

theorem sumLeftCircuit_eval (p : QueryPort S V) (q : QueryPort B V)
    (c : QueryCircuit S B W) (U : Matrix.unitaryGroup S ℂ) (T : Matrix.unitaryGroup B ℂ) :
    (sumLeftCircuit p q c).eval U T = blockSumUnitary (c.eval U T) 1 := by
  induction c with
  | nil => exact blockSumUnitary_one.symm
  | cons g c ih =>
    change (sumLeftCircuit p q c).eval U T * (sumLeftInstruction p q g).eval U T = _
    rw [ih, sumLeftInstruction_eval, ← blockSumUnitary_mul, mul_one]
    rfl

theorem sumLeftCircuit_counts (p : QueryPort S V) (q : QueryPort B V) (c : QueryCircuit S B W) :
    (sumLeftCircuit p q c).matrixQueries = c.matrixQueries ∧
      (sumLeftCircuit p q c).vectorQueries = c.vectorQueries := by
  induction c with
  | nil => exact ⟨rfl,rfl⟩
  | cons g c ih => cases g <;> simp_all [sumLeftCircuit, sumLeftInstruction,
      QueryCircuit.matrixQueries, QueryCircuit.vectorQueries]

end OptimalQLS.LowerBounds.Physical
