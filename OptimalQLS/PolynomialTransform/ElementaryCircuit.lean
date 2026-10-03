import OptimalQLS.PolynomialTransform.CleanEmbedding

/-! # Actual elementary gates and separate matrix/vector oracle calls -/
noncomputable section
namespace OptimalQLS.PolynomialTransform
open Matrix DirtyAncilla OptimalQLS.TransducerCompiler
variable {A B ι D L : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype ι] [DecidableEq ι] [Fintype D] [DecidableEq D]
  [Fintype L] [DecidableEq L]

abbrev ElementarySpace (ι D : Type*) := GateSynthesis.Space ι × D

def elementaryPlacement : Matrix.unitaryGroup (GateSynthesis.Space ι) ℂ →*
    Matrix.unitaryGroup (ElementarySpace ι D) ℂ := GateSynthesis.placeHom (Equiv.refl _)

/-- Every work instruction is a physically placed one- or two-qubit gate. -/
inductive ElementaryInstruction (A B ι D : Type*) [Fintype ι] [DecidableEq ι]
    [Fintype D] [DecidableEq D] where
  | gate (g : PhaseGate ι)
  | matrixCall (port : QueryPort A (ElementarySpace ι D)) (adjoint : Bool)
  | vectorCall (port : QueryPort B (ElementarySpace ι D)) (adjoint : Bool)

abbrev ElementaryCircuit (A B ι D : Type*) [Fintype ι] [DecidableEq ι]
    [Fintype D] [DecidableEq D] := List (ElementaryInstruction A B ι D)

def ElementaryInstruction.toQuery : ElementaryInstruction A B ι D →
    QueryInstruction A B (ElementarySpace ι D)
  | .gate g => .work (elementaryPlacement g.eval)
  | .matrixCall p b => .matrixCall p b
  | .vectorCall p b => .vectorCall p b

def ElementaryCircuit.toQuery (c : ElementaryCircuit A B ι D) :
    QueryCircuit A B (ElementarySpace ι D) := c.map ElementaryInstruction.toQuery

def ElementaryCircuit.workGates : ElementaryCircuit A B ι D → ℕ
  | [] => 0
  | .gate _::c => ElementaryCircuit.workGates c+1
  | _::c => ElementaryCircuit.workGates c

@[simp] theorem ElementaryCircuit.toQuery_append (c d : ElementaryCircuit A B ι D) :
    (c++d).toQuery=c.toQuery++d.toQuery := List.map_append ..

@[simp] theorem ElementaryCircuit.workGates_append (c d : ElementaryCircuit A B ι D) :
    (c++d).workGates=c.workGates+d.workGates := by
  induction c with
  | nil => simp [workGates]
  | cons g c ih => cases g <;> simp [workGates,ih,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

/-- A primitive macro carries an actual finite elementary instruction list. -/
def elementaryMacro (code : List (PhaseGate ι)) : ElementaryCircuit A B ι D :=
  code.map ElementaryInstruction.gate

@[simp] theorem elementaryMacro_workGates (code : List (PhaseGate ι)) :
    (elementaryMacro (A := A) (B := B) (D := D) code).workGates=code.length := by
  induction code <;> simp_all [elementaryMacro,ElementaryCircuit.workGates]

@[simp] theorem elementaryMacro_queries (code : List (PhaseGate ι)) :
    (elementaryMacro (A := A) (B := B) (D := D) code).toQuery.matrixQueries=0 ∧
    (elementaryMacro (A := A) (B := B) (D := D) code).toQuery.vectorQueries=0 := by
  induction code <;> simp_all [elementaryMacro,ElementaryCircuit.toQuery,
    ElementaryInstruction.toQuery,QueryCircuit.matrixQueries,QueryCircuit.vectorQueries]

@[simp] theorem elementaryMacro_eval (code : List (PhaseGate ι))
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) :
    (elementaryMacro (D := D) code).toQuery.eval UA Ub=elementaryPlacement (phaseEval code) := by
  induction code with
  | nil => simp [elementaryMacro,ElementaryCircuit.toQuery,QueryCircuit.eval,phaseEval]
  | cons g code ih =>
    simp only [elementaryMacro,List.map_cons,ElementaryCircuit.toQuery,ElementaryInstruction.toQuery,
      QueryCircuit.eval,QueryInstruction.eval,phaseEval,map_mul]
    change (elementaryMacro code).toQuery.eval UA Ub * _ = _
    rw [ih]

/-- Given verified local implementations for the work instructions, replacement
preserves both oracle counts and the entire action on the clean subspace. -/
theorem refine_query_circuit (c : QueryCircuit A B L)
    (J : Matrix (ElementarySpace ι D) L ℂ) (port : QueryPort L (ElementarySpace ι D))
    (hport : ∀ U : Matrix.unitaryGroup L ℂ, (port.apply U).val*J=J*U.val)
    (C : ℕ)
    (hwork : ∀ U, QueryInstruction.work U ∈ c → ∃ code : List (PhaseGate ι),
      code.length ≤ C ∧ (elementaryPlacement (D := D) (phaseEval code)).val*J=J*U.val) :
    ∃ out : ElementaryCircuit A B ι D,
      out.toQuery.matrixQueries=c.matrixQueries ∧ out.toQuery.vectorQueries=c.vectorQueries ∧
      out.workGates ≤ C*workInstructions c ∧
      ∀ (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ),
        (out.toQuery.eval UA Ub).val*J=J*(QueryCircuit.eval UA Ub c).val := by
  induction c with
  | nil =>
    refine ⟨[],rfl,rfl,by simp [ElementaryCircuit.workGates,workInstructions],?_⟩
    intro UA Ub
    simp [ElementaryCircuit.toQuery,QueryCircuit.eval]
  | cons g c ih =>
    obtain ⟨out,hm,hv,hg,he⟩ := ih (fun U hU => hwork U (List.mem_cons_of_mem _ hU))
    cases g with
    | work U =>
      obtain ⟨code,hcode,himpl⟩ := hwork U (by simp)
      refine ⟨elementaryMacro code ++ out,?_,?_,?_,?_⟩
      · simp [QueryCircuit.matrixQueries_append,hm,QueryCircuit.matrixQueries]
      · simp [QueryCircuit.vectorQueries_append,hv,QueryCircuit.vectorQueries]
      · simp only [ElementaryCircuit.workGates_append,elementaryMacro_workGates,workInstructions,Nat.mul_add,Nat.mul_one]
        omega
      · intro UA Ub
        simp only [ElementaryCircuit.toQuery_append,QueryCircuit.eval_append,
          elementaryMacro_eval,Submonoid.coe_mul,QueryCircuit.eval,QueryInstruction.eval]
        exact intertwines_mul J _ _ _ _ himpl (he UA Ub)
    | matrixCall p adj =>
      refine ⟨.matrixCall (port.comp p) adj :: out,?_,?_,?_,?_⟩
      · simpa [ElementaryCircuit.toQuery,ElementaryInstruction.toQuery,QueryCircuit.matrixQueries] using congrArg Nat.succ hm
      · simpa [ElementaryCircuit.toQuery,ElementaryInstruction.toQuery,QueryCircuit.vectorQueries] using hv
      · simpa [ElementaryCircuit.workGates,workInstructions] using hg
      · intro UA Ub
        change ((out.toQuery.eval UA Ub).val*(QueryInstruction.matrixCall (port.comp p) adj |>.eval UA Ub).val)*J=
          J*((QueryCircuit.eval UA Ub c).val*(QueryInstruction.matrixCall p adj |>.eval UA Ub).val)
        apply intertwines_mul J _ _ _ _ _ (he UA Ub)
        simpa only [QueryInstruction.eval,QueryPort.comp_apply] using hport (p.apply (if adj then UA⁻¹ else UA))
    | vectorCall p adj =>
      refine ⟨.vectorCall (port.comp p) adj :: out,?_,?_,?_,?_⟩
      · simpa [ElementaryCircuit.toQuery,ElementaryInstruction.toQuery,QueryCircuit.matrixQueries] using hm
      · simpa [ElementaryCircuit.toQuery,ElementaryInstruction.toQuery,QueryCircuit.vectorQueries] using congrArg Nat.succ hv
      · simpa [ElementaryCircuit.workGates,workInstructions] using hg
      · intro UA Ub
        change ((out.toQuery.eval UA Ub).val*(QueryInstruction.vectorCall (port.comp p) adj |>.eval UA Ub).val)*J=
          J*((QueryCircuit.eval UA Ub c).val*(QueryInstruction.vectorCall p adj |>.eval UA Ub).val)
        apply intertwines_mul J _ _ _ _ _ (he UA Ub)
        simpa only [QueryInstruction.eval,QueryPort.comp_apply] using hport (p.apply (if adj then Ub⁻¹ else Ub))

end OptimalQLS.PolynomialTransform
