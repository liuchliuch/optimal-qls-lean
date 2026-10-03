import OptimalQLS.PolynomialTransform.SubstitutionCounts

/-! # Typed physical work gates with coherent matrix-oracle macro replacement -/
noncomputable section
namespace OptimalQLS.PolynomialTransform
open Matrix
variable {G A B Q L P : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype Q] [DecidableEq Q] [Fintype L] [DecidableEq L] [Fintype P] [DecidableEq P]

/-- The work-gate parameter is a concrete gate syntax at each instantiation. -/
inductive NamedInstruction (G A B P : Type*) where
  | gate (g : G)
  | matrixCall (port : QueryPort A P) (adjoint : Bool)
  | vectorCall (port : QueryPort B P) (adjoint : Bool)

abbrev NamedCircuit (G A B P : Type*) := List (NamedInstruction G A B P)

def NamedInstruction.toQuery (gate : G → Matrix.unitaryGroup P ℂ) :
    NamedInstruction G A B P → QueryInstruction A B P
  | .gate g => .work (gate g)
  | .matrixCall p b => .matrixCall p b
  | .vectorCall p b => .vectorCall p b

def NamedCircuit.toQuery (gate : G → Matrix.unitaryGroup P ℂ) (c : NamedCircuit G A B P) :
    QueryCircuit A B P := c.map (NamedInstruction.toQuery gate)

def NamedCircuit.workGates : NamedCircuit G A B P → ℕ
  | [] => 0
  | .gate _::c => NamedCircuit.workGates c+1
  | _::c => NamedCircuit.workGates c

@[simp] theorem NamedCircuit.toQuery_append (gate : G → Matrix.unitaryGroup P ℂ)
    (c d : NamedCircuit G A B P) : (c++d).toQuery gate=c.toQuery gate++d.toQuery gate := List.map_append ..

@[simp] theorem NamedCircuit.workGates_append (c d : NamedCircuit G A B P) :
    (c++d).workGates=c.workGates+d.workGates := by
  induction c with
  | nil => simp [workGates]
  | cons g c ih => cases g <;> simp [workGates,ih,Nat.add_comm,Nat.add_left_comm]

/-- Recover the concrete gate syntax of a classified work list without
altering a single oracle instruction or its evaluation. -/
theorem name_work_gates (gate : G → Matrix.unitaryGroup P ℂ) (c : QueryCircuit A B P)
    (h : ∀ U, QueryInstruction.work U ∈ c → ∃ g : G, gate g=U) :
    ∃ out : NamedCircuit G A B P, out.toQuery gate=c ∧ out.workGates=workInstructions c := by
  induction c with
  | nil => exact ⟨[],rfl,rfl⟩
  | cons g c ih =>
    obtain ⟨tail,ht,hw⟩ := ih (fun U hU => h U (List.mem_cons_of_mem _ hU))
    cases g with
    | work U =>
      obtain ⟨g,rfl⟩ := h U (by simp)
      refine ⟨.gate g::tail,?_,?_⟩
      · simpa [NamedCircuit.toQuery,NamedInstruction.toQuery] using congrArg (List.cons (.work (gate g))) ht
      · simpa [NamedCircuit.workGates,workInstructions] using congrArg Nat.succ hw
    | matrixCall p b =>
      refine ⟨.matrixCall p b::tail,?_,?_⟩
      · simpa [NamedCircuit.toQuery,NamedInstruction.toQuery] using congrArg (List.cons (.matrixCall p b)) ht
      · simpa [NamedCircuit.workGates,workInstructions] using hw
    | vectorCall p b =>
      refine ⟨.vectorCall p b::tail,?_,?_⟩
      · simpa [NamedCircuit.toQuery,NamedInstruction.toQuery] using congrArg (List.cons (.vectorCall p b)) ht
      · simpa [NamedCircuit.workGates,workInstructions] using hw

/-- Replacing whole macros preserves clean scratch at the query boundaries.
Both work and matrix-call implementations are actual instruction lists. -/
theorem refine_matrix_and_work (gate : G → Matrix.unitaryGroup P ℂ)
    (c : QueryCircuit Q B L) (hzero : c.vectorQueries=0)
    (J : Matrix P L ℂ) (graphOracle : Matrix.unitaryGroup A ℂ → Matrix.unitaryGroup Q ℂ)
    (workCost queryCost queriesPerCall : ℕ)
    (hwork : ∀ U, QueryInstruction.work U ∈ c → ∃ code : NamedCircuit G A B P,
      (code.toQuery gate).matrixQueries=0 ∧ (code.toQuery gate).vectorQueries=0 ∧
      code.workGates ≤ workCost ∧ ∀ UA Ub, ((code.toQuery gate).eval UA Ub).val*J=J*U.val)
    (hquery : ∀ p adj, QueryInstruction.matrixCall p adj ∈ c → ∃ code : NamedCircuit G A B P,
      (code.toQuery gate).matrixQueries=queriesPerCall ∧ (code.toQuery gate).vectorQueries=0 ∧
      code.workGates ≤ queryCost ∧ ∀ UA Ub, ((code.toQuery gate).eval UA Ub).val*J=
        J*(p.apply (if adj then (graphOracle UA)⁻¹ else graphOracle UA)).val) :
    ∃ out : NamedCircuit G A B P,
      (out.toQuery gate).matrixQueries=queriesPerCall*c.matrixQueries ∧
      (out.toQuery gate).vectorQueries=0 ∧
      out.workGates ≤ workCost*workInstructions c+queryCost*c.matrixQueries ∧
      ∀ UA Ub, ((out.toQuery gate).eval UA Ub).val*J=J*(c.eval (graphOracle UA) Ub).val := by
  induction c with
  | nil =>
    refine ⟨[],by simp [NamedCircuit.toQuery,QueryCircuit.matrixQueries],rfl,
      by simp [NamedCircuit.workGates,workInstructions,QueryCircuit.matrixQueries],?_⟩
    intro UA Ub
    simp [NamedCircuit.toQuery,QueryCircuit.eval]
  | cons g c ih =>
    have hz : QueryCircuit.vectorQueries c=0 := by
      cases g <;> simp only [QueryCircuit.vectorQueries] at hzero <;> omega
    obtain ⟨tail,hm,hv,hg,he⟩ := ih hz
      (fun U h => hwork U (List.mem_cons_of_mem _ h))
      (fun p adj h => hquery p adj (List.mem_cons_of_mem _ h))
    cases g with
    | work U =>
      obtain ⟨code,hcm,hcv,hcg,hce⟩ := hwork U (by simp)
      refine ⟨code++tail,?_,?_,?_,?_⟩
      · simp only [NamedCircuit.toQuery_append,QueryCircuit.matrixQueries_append,hcm,hm,zero_add,QueryCircuit.matrixQueries]
      · simp [QueryCircuit.vectorQueries_append,hcv,hv]
      · simp only [NamedCircuit.workGates_append,workInstructions,QueryCircuit.matrixQueries,
          Nat.mul_add,Nat.mul_one]
        omega
      · intro UA Ub
        simp only [NamedCircuit.toQuery_append,QueryCircuit.eval_append,Submonoid.coe_mul,
          QueryCircuit.eval,QueryInstruction.eval]
        exact intertwines_mul J _ _ _ _ (hce UA Ub) (he UA Ub)
    | matrixCall p adj =>
      obtain ⟨code,hcm,hcv,hcg,hce⟩ := hquery p adj (by simp)
      refine ⟨code++tail,?_,?_,?_,?_⟩
      · simp only [NamedCircuit.toQuery_append,QueryCircuit.matrixQueries_append,hcm,hm,
          QueryCircuit.matrixQueries,Nat.mul_add,Nat.mul_one]
        omega
      · simp [QueryCircuit.vectorQueries_append,hcv,hv]
      · simp only [NamedCircuit.workGates_append,workInstructions,QueryCircuit.matrixQueries,
          Nat.mul_add,Nat.mul_one]
        omega
      · intro UA Ub
        simp only [NamedCircuit.toQuery_append,QueryCircuit.eval_append,Submonoid.coe_mul,
          QueryCircuit.eval,QueryInstruction.eval]
        exact intertwines_mul J _ _ _ _ (hce UA Ub) (he UA Ub)
    | vectorCall p adj =>
      simp only [QueryCircuit.vectorQueries] at hzero
      omega

end OptimalQLS.PolynomialTransform
