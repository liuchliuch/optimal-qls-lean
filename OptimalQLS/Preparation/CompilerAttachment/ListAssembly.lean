import OptimalQLS.Preparation.CompilerAttachment.LocalAttach
import OptimalQLS.Preparation.Finite

/-! # Literal macro expansion of the actual synthesized compiler list

This bookkeeping applies only to instruction lists supplied with their exact
clean-subspace semantics and counts. It never treats a charged matrix as a gate.
-/
noncomputable section
set_option synthInstance.maxSize 4096
namespace OptimalQLS.Preparation.CompilerAttachment
open Matrix TransducerCompiler PolynomialTransform
variable {G H A B P N : Type*} [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B] [Fintype P] [DecidableEq P]
  [Fintype N] [DecidableEq N]

def mapNamedInstruction (f : G → H) : NamedInstruction G A B P → NamedInstruction H A B P
  | .gate g => .gate (f g)
  | .matrixCall p b => .matrixCall p b
  | .vectorCall p b => .vectorCall p b

def mapNamed (f : G → H) (c : NamedCircuit G A B P) : NamedCircuit H A B P :=
  c.map (mapNamedInstruction f)

theorem mapNamed_toQuery (f : G → H) (g : G → Matrix.unitaryGroup P ℂ)
    (h : H → Matrix.unitaryGroup P ℂ) (hf : ∀ x, h (f x)=g x)
    (c : NamedCircuit G A B P) : (mapNamed f c).toQuery h=c.toQuery g := by
  induction c with
  | nil => rfl
  | cons i c ih => cases i <;> simp_all [mapNamed,mapNamedInstruction,NamedCircuit.toQuery,
      NamedInstruction.toQuery]

theorem mapNamed_workGates (f : G → H) (c : NamedCircuit G A B P) :
    (mapNamed f c).workGates=c.workGates := by
  induction c with
  | nil => rfl
  | cons i c ih => cases i <;> simpa [mapNamed,mapNamedInstruction,NamedCircuit.workGates] using ih

def macroCompile {ℓ : ℕ} (p : SynthInstruction ℓ → NamedCircuit G A B P)
    (c : SynthCircuit ℓ) : NamedCircuit G A B P := c.flatMap p

def instructionGateBudget {ℓ : ℕ} (W F R : ℕ) : SynthInstruction ℓ → ℕ
  | .query₁ => F
  | .query₂ => R
  | .work => W
  | .elementary _ => 1
  | .clock _ => ℓ

theorem instructionGateBudget_eq {ℓ : ℕ} (W F R : ℕ) (g : SynthInstruction ℓ) :
    instructionGateBudget W F R g=g.auxCost+W*g.workCost+F*g.firstCost+R*g.secondCost := by
  cases g <;> simp [instructionGateBudget,SynthInstruction.auxCost,SynthInstruction.workCost,
    SynthInstruction.firstCost,SynthInstruction.secondCost]


def listGateBudget {ℓ : ℕ} (W F R : ℕ) (c : SynthCircuit ℓ) : ℕ :=
  (c.map (instructionGateBudget W F R)).sum

theorem listGateBudget_eq {ℓ : ℕ} (W F R : ℕ) (c : SynthCircuit ℓ) :
    listGateBudget W F R c=c.auxGates+W*c.workCalls+F*c.firstCalls+R*c.secondCalls := by
  induction c with
  | nil => simp [listGateBudget,SynthCircuit.auxGates,SynthCircuit.workCalls,
      SynthCircuit.firstCalls,SynthCircuit.secondCalls]
  | cons g c ih =>
    simp only [listGateBudget,List.map_cons,List.sum_cons] at *
    rw [ih]
    simp only [SynthCircuit.auxGates,SynthCircuit.workCalls,SynthCircuit.firstCalls,
      SynthCircuit.secondCalls,List.map_cons,List.sum_cons,instructionGateBudget_eq]
    ring

/-- All oracle counts and the bound refer to the emitted finite instruction list. -/
theorem macroCompile_counts {ℓ : ℕ} (gate : G → Matrix.unitaryGroup P ℂ)
    (p : SynthInstruction ℓ → NamedCircuit G A B P) (W F R : ℕ)
    (hp : ∀ g, (p g |>.toQuery gate).matrixQueries=2*g.firstCost ∧
      (p g |>.toQuery gate).vectorQueries=2*g.secondCost ∧
      (p g).workGates ≤ instructionGateBudget W F R g)
    (c : SynthCircuit ℓ) :
    ((macroCompile p c).toQuery gate).matrixQueries=2*c.firstCalls ∧
      ((macroCompile p c).toQuery gate).vectorQueries=2*c.secondCalls ∧
      (macroCompile p c).workGates≤c.auxGates+W*c.workCalls+F*c.firstCalls+R*c.secondCalls := by
  have aux (c : SynthCircuit ℓ) :
      ((macroCompile p c).toQuery gate).matrixQueries=2*c.firstCalls ∧
      ((macroCompile p c).toQuery gate).vectorQueries=2*c.secondCalls ∧
      (macroCompile p c).workGates≤listGateBudget W F R c := by
    induction c with
    | nil => simp [macroCompile,NamedCircuit.toQuery,QueryCircuit.matrixQueries,
        QueryCircuit.vectorQueries,SynthCircuit.firstCalls,SynthCircuit.secondCalls,
        NamedCircuit.workGates,listGateBudget]
    | cons g c ih =>
      have hg := hp g
      simp only [macroCompile,List.flatMap_cons,NamedCircuit.toQuery_append,
        QueryCircuit.matrixQueries_append,QueryCircuit.vectorQueries_append,
        NamedCircuit.workGates_append]
      change (p g |>.toQuery gate).matrixQueries+((macroCompile p c).toQuery gate).matrixQueries=_ ∧
        (p g |>.toQuery gate).vectorQueries+((macroCompile p c).toQuery gate).vectorQueries=_ ∧
        (p g).workGates+(macroCompile p c).workGates≤_
      rw [hg.1,ih.1,hg.2.1,ih.2.1]
      simp only [SynthCircuit.firstCalls,SynthCircuit.secondCalls,List.map_cons,List.sum_cons,
        listGateBudget,Nat.mul_add]
      exact ⟨trivial,trivial,Nat.add_le_add hg.2.2 ih.2.2⟩
  simpa only [listGateBudget_eq] using aux c

/-- Whole-unitary clean intertwining, retaining all original oracle columns. -/
theorem macroCompile_intertwines {ℓ : ℕ} (gate : G → Matrix.unitaryGroup P ℂ)
    (p : SynthInstruction ℓ → NamedCircuit G A B P)
    (S : Matrix.unitaryGroup (Base N) ℂ)
    (U₁ : Matrix.unitaryGroup A ℂ → Matrix.unitaryGroup N ℂ)
    (U₂ : Matrix.unitaryGroup B ℂ → Matrix.unitaryGroup N ℂ)
    (J : Matrix P (SynthSpace N ℓ) ℂ)
    (hp : ∀ g UA Ub, (((p g).toQuery gate).eval UA Ub).val*J=
      J*(g.eval S (U₁ UA) (U₂ Ub)).val) (c : SynthCircuit ℓ)
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) :
    (((macroCompile p c).toQuery gate).eval UA Ub).val*J=
      J*(c.eval S (U₁ UA) (U₂ Ub)).val := by
  induction c with
  | nil => simp [macroCompile,NamedCircuit.toQuery,QueryCircuit.eval,SynthCircuit.eval]
  | cons g c ih =>
    simp only [macroCompile,List.flatMap_cons,NamedCircuit.toQuery_append,
      QueryCircuit.eval_append,Submonoid.coe_mul,SynthCircuit.eval]
    exact intertwines_mul J _ _ _ _ (hp g UA Ub) ih

end OptimalQLS.Preparation.CompilerAttachment
