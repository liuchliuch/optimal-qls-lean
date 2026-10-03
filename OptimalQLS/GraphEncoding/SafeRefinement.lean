import OptimalQLS.GraphEncoding.SingleFlagOracle

/-! # Real elementary refinement with a literal single-flag oracle interface -/
noncomputable section
set_option synthInstance.maxSize 2048
set_option maxHeartbeats 1000000
namespace OptimalQLS.GraphEncoding
open Matrix PolynomialTransform DirtyAncilla
variable {ι A B L : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] [Fintype L] [DecidableEq L]

def SingleFlagRealCircuit (t : ι) (c : ElementaryCircuit A B ι A) : Prop :=
  (∀ g, ElementaryInstruction.gate g ∈ c → RealPhaseGate g) ∧
  ∀ p b, ElementaryInstruction.matrixCall p b ∈ c → p=singleFlagOraclePort A t

theorem SingleFlagRealCircuit.append (t : ι) (c d : ElementaryCircuit A B ι A)
    (hc : SingleFlagRealCircuit t c) (hd : SingleFlagRealCircuit t d) :
    SingleFlagRealCircuit t (c++d) := by
  constructor
  · intro g hg
    rcases List.mem_append.mp hg with h|h
    · exact hc.1 g h
    · exact hd.1 g h
  · intro p b hp
    rcases List.mem_append.mp hp with h|h
    · exact hc.2 p b h
    · exact hd.2 p b h

theorem elementaryMacro_safe (t : ι) (code : List (PhaseGate ι))
    (hc : ∀ g, g ∈ code → RealPhaseGate g) :
    SingleFlagRealCircuit t (elementaryMacro (A := A) (B := B) (D := A) code) := by
  constructor
  · intro g hg
    obtain ⟨r,hr,hEq⟩ := List.mem_map.mp hg
    have he : r=g := ElementaryInstruction.gate.inj hEq
    subst g
    exact hc r hr
  · intro p b hp
    simp [elementaryMacro] at hp

theorem realProgramCircuit_safe (t : ι) (p : TransducerCompiler.BinaryClock.Program ι) :
    SingleFlagRealCircuit t (realProgramCircuit A B p) := by
  apply elementaryMacro_safe
  intro g hg
  obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hg
  exact realPhaseGate_real r

theorem flagQuery_safe (t : ι) (adj : Bool) :
    SingleFlagRealCircuit t ([.matrixCall (singleFlagOraclePort A t) adj] : ElementaryCircuit A B ι A) := by
  constructor
  · intro g hg; simp at hg
  · intro p b hp
    simpa using (show p=singleFlagOraclePort A t ∧ b=adj from by simpa using hp).1

theorem maskedOracleCircuit_safe (n : ℕ) (f : SmallWire n → ι) (hf : Function.Injective f)
    (mask : Fin n → Bool) (adj : Bool) :
    SingleFlagRealCircuit (f (smallTarget n)) (maskedOracleCircuit (A := A) (B := B) n f hf mask adj) := by
  exact SingleFlagRealCircuit.append _ _ _
    (SingleFlagRealCircuit.append _ _ _ (realProgramCircuit_safe _ _) (flagQuery_safe _ _))
    (realProgramCircuit_safe _ _)

/-- Replace both work and original oracle instructions while retaining real
work-gate syntax and the exact designated single flag of every emitted query. -/
theorem refine_real_single_flag (c : QueryCircuit A B L) (hzero : c.vectorQueries=0)
    (J : Matrix (ElementarySpace ι A) L ℂ) (t : ι) (W Q : ℕ)
    (hwork : ∀ U, QueryInstruction.work U ∈ c → ∃ code : ElementaryCircuit A B ι A,
      code.toQuery.matrixQueries=0 ∧ code.toQuery.vectorQueries=0 ∧ code.workGates≤W ∧
      SingleFlagRealCircuit t code ∧ ∀ UA Ub, (code.toQuery.eval UA Ub).val*J=J*U.val)
    (hquery : ∀ p adj, QueryInstruction.matrixCall p adj ∈ c → ∃ code : ElementaryCircuit A B ι A,
      code.toQuery.matrixQueries=1 ∧ code.toQuery.vectorQueries=0 ∧ code.workGates≤Q ∧
      SingleFlagRealCircuit t code ∧ ∀ UA Ub, (code.toQuery.eval UA Ub).val*J=
        J*(p.apply (if adj then UA⁻¹ else UA)).val) :
    ∃ out : ElementaryCircuit A B ι A,
      out.toQuery.matrixQueries=c.matrixQueries ∧ out.toQuery.vectorQueries=0 ∧
      out.workGates≤W*workInstructions c+Q*c.matrixQueries ∧ SingleFlagRealCircuit t out ∧
      ∀ UA Ub, (out.toQuery.eval UA Ub).val*J=J*(c.eval UA Ub).val := by
  induction c with
  | nil =>
    refine ⟨[],rfl,rfl,by simp [ElementaryCircuit.workGates,workInstructions,QueryCircuit.matrixQueries],?_,?_⟩
    · constructor <;> simp
    · intro UA Ub; simp [ElementaryCircuit.toQuery,QueryCircuit.eval]
  | cons g c ih =>
    have hz : QueryCircuit.vectorQueries c=0 := by
      cases g <;> simp only [QueryCircuit.vectorQueries] at hzero <;> omega
    obtain ⟨tail,hm,hv,hg,hs,he⟩ := ih hz
      (fun U h => hwork U (List.mem_cons_of_mem _ h))
      (fun p adj h => hquery p adj (List.mem_cons_of_mem _ h))
    cases g with
    | work U =>
      obtain ⟨code,hcm,hcv,hcg,hcs,hce⟩ := hwork U (by simp)
      refine ⟨code++tail,?_,?_,?_,SingleFlagRealCircuit.append t code tail hcs hs,?_⟩
      · simp [ElementaryCircuit.toQuery_append,QueryCircuit.matrixQueries_append,hcm,hm,QueryCircuit.matrixQueries]
      · simp [ElementaryCircuit.toQuery_append,QueryCircuit.vectorQueries_append,hcv,hv]
      · simp only [ElementaryCircuit.workGates_append,workInstructions,QueryCircuit.matrixQueries,Nat.mul_add,Nat.mul_one]
        omega
      · intro UA Ub
        simp only [ElementaryCircuit.toQuery_append,QueryCircuit.eval_append,Submonoid.coe_mul,
          QueryCircuit.eval,QueryInstruction.eval]
        exact intertwines_mul J _ _ _ _ (hce UA Ub) (he UA Ub)
    | matrixCall p adj =>
      obtain ⟨code,hcm,hcv,hcg,hcs,hce⟩ := hquery p adj (by simp)
      refine ⟨code++tail,?_,?_,?_,SingleFlagRealCircuit.append t code tail hcs hs,?_⟩
      · simp [ElementaryCircuit.toQuery_append,QueryCircuit.matrixQueries_append,hcm,hm,QueryCircuit.matrixQueries,Nat.add_comm]
      · simp [ElementaryCircuit.toQuery_append,QueryCircuit.vectorQueries_append,hcv,hv]
      · simp only [ElementaryCircuit.workGates_append,workInstructions,QueryCircuit.matrixQueries,Nat.mul_add,Nat.mul_one]
        omega
      · intro UA Ub
        simp only [ElementaryCircuit.toQuery_append,QueryCircuit.eval_append,Submonoid.coe_mul,
          QueryCircuit.eval,QueryInstruction.eval]
        exact intertwines_mul J _ _ _ _ (hce UA Ub) (he UA Ub)
    | vectorCall p adj =>
      simp only [QueryCircuit.vectorQueries] at hzero
      omega

end OptimalQLS.GraphEncoding
