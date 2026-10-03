import OptimalQLS.PolynomialTransform.WorkClassification

/-! # Exact work-instruction accounting under concrete oracle substitution -/
namespace OptimalQLS.PolynomialTransform
open Matrix
variable {A B S W ι D : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype S] [DecidableEq S] [Fintype W] [DecidableEq W]
  [Fintype ι] [DecidableEq ι] [Fintype D] [DecidableEq D]

theorem ElementaryCircuit.workInstructions_toQuery (c : ElementaryCircuit A B ι D) :
    workInstructions c.toQuery=c.workGates := by
  induction c with
  | nil => rfl
  | cons g c ih =>
    cases g <;> simpa [ElementaryCircuit.toQuery,ElementaryInstruction.toQuery,
      workInstructions,ElementaryCircuit.workGates] using ih

theorem workInstructions_adjoint (c : QueryCircuit A B W) :
    workInstructions c.adjoint=workInstructions c := by
  induction c with
  | nil => rfl
  | cons g c ih => cases g <;> simp [QueryCircuit.adjoint,workInstructions_append,
      QueryInstruction.adjoint,workInstructions,ih]

/-- A control or adjoint changes no instruction counts; this statement does
not identify controlled work matrices with their elementary lowering. -/
theorem workInstructions_substituteMatrix (c : QueryCircuit A B W) (d : QueryCircuit S B A) :
    workInstructions (c.substituteMatrix d)=workInstructions c+c.matrixQueries*workInstructions d := by
  induction c with
  | nil => simp [QueryCircuit.substituteMatrix,workInstructions,QueryCircuit.matrixQueries]
  | cons g c ih =>
    cases g with
    | work U =>
      simp only [QueryCircuit.substituteMatrix,List.flatMap_cons,QueryInstruction.substituteMatrix,
        workInstructions_append,workInstructions,QueryCircuit.matrixQueries] at *
      omega
    | matrixCall p b =>
      cases b <;> simp only [QueryCircuit.substituteMatrix,List.flatMap_cons,
        QueryInstruction.substituteMatrix,Bool.false_eq_true,ite_false,ite_true,
        workInstructions_append,workInstructions_lift,workInstructions_adjoint,
        workInstructions,QueryCircuit.matrixQueries,Nat.add_mul,Nat.one_mul] at * <;> omega
    | vectorCall p b =>
      simp only [QueryCircuit.substituteMatrix,List.flatMap_cons,QueryInstruction.substituteMatrix,
        workInstructions_append,workInstructions,QueryCircuit.matrixQueries] at *
      omega

end OptimalQLS.PolynomialTransform
