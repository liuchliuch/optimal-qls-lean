import OptimalQLS.Refinement.Program
import OptimalQLS.PolynomialTransform.SingleFlagEncoding
import OptimalQLS.PolynomialTransform.PaperTheorems

/-! # Concrete work gates of coherent refinement with disjoint registers -/
noncomputable section
namespace OptimalQLS.Refinement
open Matrix PolynomialTransform DirtyAncilla
set_option synthInstance.maxSize 4096
variable {P D B : Type*} [Fintype P] [DecidableEq P] [Fintype D] [DecidableEq D]
  [Fintype B] [DecidableEq B]

abbrev FilterSignal (a : ℕ) := PolynomialTransform.PhysicalSignal (a+4)
abbrev CorrectionSignal (a : ℕ) := PolynomialTransform.PhysicalSignal a
abbrev RunSpace (a : ℕ) (P D : Type*) := Space P (FilterSignal a) (CorrectionSignal a) D

/-- The only work families are the physically checked filter and correction
gates, tensored with untouched, disjoint registers by literal product rewiring. -/
inductive RefinementGate (a : ℕ) where
  | filter (g : GraphAttachedGate a)
  | correction (g : SingleFlagGate a)

def RefinementGate.eval (a : ℕ) : RefinementGate a → Matrix.unitaryGroup (RunSpace a P D) ℂ
  | .filter g => filterPort.apply (GraphAttachedGate.eval a g)
  | .correction g => correctionPort.apply (SingleFlagGate.eval a g)

def RefinementGate.arity {a : ℕ} : RefinementGate a → ℕ
  | .filter g => g.arity
  | .correction g => g.arity

theorem RefinementGate.arity_le_two {a : ℕ} (g : RefinementGate a) : g.arity≤2 := by
  cases g with
  | filter g => exact GraphAttachedGate.arity_le_two g
  | correction g => exact SingleFlagGate.arity_le_two g

abbrev NamedRefinementCircuit (a : ℕ) (P D B : Type*) :=
  NamedCircuit (RefinementGate a) ((Fin a → Bool) × D) B (RunSpace a P D)

def attachFilterInstruction (a : ℕ) :
    NamedInstruction (GraphAttachedGate a) ((Fin a → Bool) × D) B (FilterSignal a × (Fin 4 × D)) →
      NamedInstruction (RefinementGate a) ((Fin a → Bool) × D) B (RunSpace a P D)
  | .gate g => .gate (.filter g)
  | .matrixCall p adj => .matrixCall (filterPort.comp p) adj
  | .vectorCall p adj => .vectorCall (filterPort.comp p) adj

def attachCorrectionInstruction (a : ℕ) :
    NamedInstruction (SingleFlagGate a) ((Fin a → Bool) × D) B (CorrectionSignal a × D) →
      NamedInstruction (RefinementGate a) ((Fin a → Bool) × D) B (RunSpace a P D)
  | .gate g => .gate (.correction g)
  | .matrixCall p adj => .matrixCall (correctionPort.comp p) adj
  | .vectorCall p adj => .vectorCall (correctionPort.comp p) adj

def namedRefinementProgram (a : ℕ) (cf : GraphAttachedCircuit a D B)
    (cc : SingleFlagCircuit a D B) : NamedRefinementCircuit a P D B :=
  cf.map (attachFilterInstruction a) ++ cc.map (attachCorrectionInstruction a)

theorem attachFilter_toQuery (a : ℕ) (cf : GraphAttachedCircuit a D B) :
    NamedCircuit.toQuery (RefinementGate.eval a) (cf.map (attachFilterInstruction (P := P) a))=
      (cf.toQuery (GraphAttachedGate.eval a)).lift filterPort := by
  induction cf with
  | nil => rfl
  | cons g cf ih =>
    cases g <;> simp_all [NamedCircuit.toQuery,NamedInstruction.toQuery,attachFilterInstruction,
      RefinementGate.eval,QueryCircuit.lift,QueryInstruction.lift]

theorem attachCorrection_toQuery (a : ℕ)
    (cc : SingleFlagCircuit a D B) :
    NamedCircuit.toQuery (RefinementGate.eval a) (cc.map (attachCorrectionInstruction (P := P) a))=
      (cc.toQuery (SingleFlagGate.eval a)).lift correctionPort := by
  induction cc with
  | nil => rfl
  | cons g cc ih =>
    cases g <;> simp_all [NamedCircuit.toQuery,NamedInstruction.toQuery,attachCorrectionInstruction,
      RefinementGate.eval,QueryCircuit.lift,QueryInstruction.lift]

theorem namedRefinementProgram_toQuery (a : ℕ) (cf : GraphAttachedCircuit a D B)
    (cc : SingleFlagCircuit a D B) :
    (namedRefinementProgram (P := P) a cf cc).toQuery (RefinementGate.eval a)=
      refinementProgram (cf.toQuery (GraphAttachedGate.eval a)) (cc.toQuery (SingleFlagGate.eval a)) := by
  rw [namedRefinementProgram,NamedCircuit.toQuery_append,attachFilter_toQuery,attachCorrection_toQuery]
  rfl

theorem namedRefinementProgram_gates (a : ℕ) (cf : GraphAttachedCircuit a D B)
    (cc : SingleFlagCircuit a D B) :
    (namedRefinementProgram (P := P) a cf cc).workGates=cf.workGates+cc.workGates := by
  have hf : NamedCircuit.workGates (cf.map (attachFilterInstruction (P := P) a))=cf.workGates := by
    induction cf with
    | nil => rfl
    | cons g cf ih => cases g <;> simp_all [NamedCircuit.workGates,attachFilterInstruction]
  have hc : NamedCircuit.workGates (cc.map (attachCorrectionInstruction (P := P) a))=cc.workGates := by
    induction cc with
    | nil => rfl
    | cons g cc ih => cases g <;> simp_all [NamedCircuit.workGates,attachCorrectionInstruction]
  rw [namedRefinementProgram,NamedCircuit.workGates_append,hf,hc]

end OptimalQLS.Refinement
