import OptimalQLS.PolynomialTransform.QueryControls

/-! # Elementary replacement retains exact provenance of every matrix query -/
noncomputable section
namespace OptimalQLS.PolynomialTransform
open Matrix DirtyAncilla
variable {A B ι D L : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype ι] [DecidableEq ι] [Fintype D] [DecidableEq D] [Fintype L] [DecidableEq L]

/-- Strengthened replacement theorem: besides resource and clean-subspace
semantics, each emitted query is the scratch lift of an actual original query. -/
theorem refine_query_circuit_with_ports (c : QueryCircuit A B L)
    (J : Matrix (ElementarySpace ι D) L ℂ) (port : QueryPort L (ElementarySpace ι D))
    (hport : ∀ U : Matrix.unitaryGroup L ℂ, (port.apply U).val*J=J*U.val)
    (C : ℕ)
    (hwork : ∀ U, QueryInstruction.work U ∈ c → ∃ code : List (PhaseGate ι),
      code.length ≤ C ∧ (elementaryPlacement (D := D) (phaseEval code)).val*J=J*U.val) :
    ∃ out : ElementaryCircuit A B ι D,
      out.toQuery.matrixQueries=c.matrixQueries ∧ out.toQuery.vectorQueries=c.vectorQueries ∧
      out.workGates ≤ C*workInstructions c ∧
      (∀ p adj, ElementaryInstruction.matrixCall p adj ∈ out →
        ∃ q, QueryInstruction.matrixCall q adj ∈ c ∧ p=port.comp q) ∧
      ∀ (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ),
        (out.toQuery.eval UA Ub).val*J=J*(c.eval UA Ub).val := by
  induction c with
  | nil =>
    refine ⟨[],rfl,rfl,by simp [ElementaryCircuit.workGates,workInstructions],?_,?_⟩
    · intro p adj h; simp at h
    · intro UA Ub; simp [ElementaryCircuit.toQuery,QueryCircuit.eval]
  | cons g c ih =>
    obtain ⟨out,hm,hv,hg,hp,he⟩ := ih (fun U hU => hwork U (List.mem_cons_of_mem _ hU))
    cases g with
    | work U =>
      obtain ⟨code,hcode,himpl⟩ := hwork U (by simp)
      refine ⟨elementaryMacro code ++ out,?_,?_,?_,?_,?_⟩
      · simp [QueryCircuit.matrixQueries_append,hm,QueryCircuit.matrixQueries]
      · simp [QueryCircuit.vectorQueries_append,hv,QueryCircuit.vectorQueries]
      · simp only [ElementaryCircuit.workGates_append,elementaryMacro_workGates,workInstructions,Nat.mul_add,Nat.mul_one]
        omega
      · intro p adj h
        have ht : ElementaryInstruction.matrixCall p adj ∈ out := by
          simpa [elementaryMacro] using h
        obtain ⟨q,hq,hpq⟩ := hp p adj ht
        exact ⟨q,List.mem_cons_of_mem _ hq,hpq⟩
      · intro UA Ub
        simp only [ElementaryCircuit.toQuery_append,QueryCircuit.eval_append,
          elementaryMacro_eval,Submonoid.coe_mul,QueryCircuit.eval,QueryInstruction.eval]
        exact intertwines_mul J _ _ _ _ himpl (he UA Ub)
    | matrixCall p adj =>
      refine ⟨.matrixCall (port.comp p) adj :: out,?_,?_,?_,?_,?_⟩
      · simpa [ElementaryCircuit.toQuery,ElementaryInstruction.toQuery,QueryCircuit.matrixQueries] using congrArg Nat.succ hm
      · simpa [ElementaryCircuit.toQuery,ElementaryInstruction.toQuery,QueryCircuit.vectorQueries] using hv
      · simpa [ElementaryCircuit.workGates,workInstructions] using hg
      · intro p' adj' h
        simp only [List.mem_cons,ElementaryInstruction.matrixCall.injEq] at h
        rcases h with ⟨rfl,rfl⟩|h
        · exact ⟨p,by simp,rfl⟩
        · obtain ⟨q,hq,hpq⟩ := hp p' adj' h
          exact ⟨q,List.mem_cons_of_mem _ hq,hpq⟩
      · intro UA Ub
        change ((out.toQuery.eval UA Ub).val*(QueryInstruction.matrixCall (port.comp p) adj |>.eval UA Ub).val)*J=
          J*((QueryCircuit.eval UA Ub c).val*(QueryInstruction.matrixCall p adj |>.eval UA Ub).val)
        apply intertwines_mul J _ _ _ _ _ (he UA Ub)
        simpa only [QueryInstruction.eval,QueryPort.comp_apply] using hport (p.apply (if adj then UA⁻¹ else UA))
    | vectorCall p adj =>
      refine ⟨.vectorCall (port.comp p) adj :: out,?_,?_,?_,?_,?_⟩
      · simpa [ElementaryCircuit.toQuery,ElementaryInstruction.toQuery,QueryCircuit.matrixQueries] using hm
      · simpa [ElementaryCircuit.toQuery,ElementaryInstruction.toQuery,QueryCircuit.vectorQueries] using congrArg Nat.succ hv
      · simpa [ElementaryCircuit.workGates,workInstructions] using hg
      · intro p' adj' h
        have ht : ElementaryInstruction.matrixCall p' adj' ∈ out := by simpa using h
        obtain ⟨q,hq,hpq⟩ := hp p' adj' ht
        exact ⟨q,List.mem_cons_of_mem _ hq,hpq⟩
      · intro UA Ub
        change ((out.toQuery.eval UA Ub).val*(QueryInstruction.vectorCall (port.comp p) adj |>.eval UA Ub).val)*J=
          J*((QueryCircuit.eval UA Ub c).val*(QueryInstruction.vectorCall p adj |>.eval UA Ub).val)
        apply intertwines_mul J _ _ _ _ _ (he UA Ub)
        simpa only [QueryInstruction.eval,QueryPort.comp_apply] using hport (p.apply (if adj then Ub⁻¹ else Ub))

end OptimalQLS.PolynomialTransform
