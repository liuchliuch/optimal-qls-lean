import OptimalQLS.GraphEncoding.SingleFlagTheorem
import OptimalQLS.PolynomialTransform.GraphOracleWiring
import OptimalQLS.PolynomialTransform.NamedCircuit
import OptimalQLS.PolynomialTransform.CleanTransport

/-! # QSVT with literal singly controlled original-oracle instructions -/
noncomputable section
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace OptimalQLS.PolynomialTransform
open Matrix Polynomial DirtyAncilla
open scoped Matrix.Norms.L2Operator
variable {D B : Type*} [Fintype D] [DecidableEq D] [Fintype B] [DecidableEq B]

abbrev OracleLocalWire := SmallWire 2
abbrev OracleLocalState := TransducerCompiler.GateSynthesis.Space OracleLocalWire

def oracleLocalWiring (A : Type*) : OracleLocalState × A ≃ ((Bool × Bool) × A) × PhaseScratch where
  toFun p := (((p.1.2 (.inl 0),p.1.2 (.inl 1)),p.2),p.1.1,p.1.2 (.inr 0),p.1.2 (.inr 1))
  invFun p := ((p.2.1,fun i => match i with
    | .inl i => if i=0 then p.1.1.1 else p.1.1.2
    | .inr i => if i=0 then p.2.2.1 else p.2.2.2),p.1.2)
  left_inv p := by
    rcases p with ⟨⟨z,b⟩,x⟩
    apply Prod.ext
    · apply Prod.ext
      · rfl
      · funext i; cases i with
        | inl i => fin_cases i <;> simp
        | inr i => fin_cases i <;> simp
    · rfl
  right_inv p := by rcases p with ⟨⟨⟨a,b⟩,x⟩,z,f,r⟩; simp

def oracleLocalClean {A : Type*} (x : (Bool × Bool) × A) : OracleLocalState × A :=
  (oracleLocalWiring A).symm (x,(false,false,false))

def oracleLocalCode (a : ℕ) (mask : Bool × Bool) (adj : Bool) :
    ElementaryCircuit ((Fin a → Bool) × D) B OracleLocalWire ((Fin a → Bool) × D) :=
  GraphEncoding.maskedOracleCircuit 2 id Function.injective_id ![mask.1,mask.2] adj

theorem oracleLocalCode_counts (a : ℕ) (mask : Bool × Bool) (adj : Bool) :
    (oracleLocalCode (D := D) (B := B) a mask adj).toQuery.matrixQueries=1 ∧
      (oracleLocalCode (D := D) (B := B) a mask adj).toQuery.vectorQueries=0 ∧
      (oracleLocalCode (D := D) (B := B) a mask adj).workGates ≤ 2400 :=
  GraphEncoding.maskedOracleCircuit_counts 2 id Function.injective_id ![mask.1,mask.2] adj

theorem singleFlag_basisInsertion_col {X Y : Type*} [DecidableEq Y]
    (f : X → Y) (x : X) : (basisInsertion f).col x = (Pi.single (f x) 1 : Y → ℂ) := by
  ext y
  simp [basisInsertion,Matrix.col_apply,Pi.single_apply]

theorem oracleLocalCode_intertwines (a : ℕ) (mask : Bool × Bool) (adj : Bool)
    (U : Matrix.unitaryGroup ((Fin a → Bool) × D) ℂ) (Ub : Matrix.unitaryGroup B ℂ) :
    ((oracleLocalCode a mask adj).toQuery.eval U Ub).val*basisInsertion oracleLocalClean =
      basisInsertion oracleLocalClean *
        ((GraphEncoding.maskedGraphPort ((Fin a → Bool) × D) mask).apply (if adj then U⁻¹ else U)).val := by
  apply basisInsertion_intertwines
  intro j
  rcases j with ⟨m,i⟩
  have he (V : Matrix.unitaryGroup ((Fin a → Bool) × D) ℂ) :
      V.val *ᵥ Pi.single i 1 = ∑ k, V.val k i • (Pi.single k 1 : ((Fin a → Bool) × D) → ℂ) := by
    ext k
    simp [Matrix.mulVec_single_one,Pi.single_apply]
  rw [GraphEncoding.maskedGraphPort_basis_expansion mask m _ _ _ _ (he _)]
  have hclean (i : (Fin a → Bool) × D) : oracleLocalClean (m,i) =
      ((false,fun k : SmallWire 2 => match k with
        | .inl k => if k=0 then m.1 else m.2 | .inr _ => false),i) := by
    simp [oracleLocalClean,oracleLocalWiring]
    funext k
    cases k <;> rfl
  rw [hclean i]
  change ((GraphEncoding.maskedOracleCircuit (A := (Fin a → Bool) × D) (B := B)
    2 id Function.injective_id ![mask.1,mask.2] adj).toQuery.eval U Ub).val *ᵥ
      Pi.single ((false,fun k : SmallWire 2 => match k with
        | .inl k => if k=0 then m.1 else m.2 | .inr _ => false),i) 1 = _
  rw [GraphEncoding.maskedOracleCircuit_basis _ _ _ _ _ _ (by rfl)]
  by_cases hm : m=mask
  · subst m
    simp [Fin.forall_fin_succ,Matrix.mulVec_sum,Matrix.mulVec_smul,basisInsertion_basis,
      singleFlag_basisInsertion_col,hclean]
  · have hn : ¬(m.1=mask.1 ∧ m.2=mask.2) := fun h => hm (Prod.ext h.1 h.2)
    simp [Fin.forall_fin_succ,hm,hn,basisInsertion_basis,singleFlag_basisInsertion_col,hclean]

/-- Pure regrouping of the two tested labels and three scratch bits; original
signal qubits remain part of the original-oracle target register. -/
def oracleAttachWiring (a : ℕ) (D : Type*) :
    OracleLocalState × ((Fin a → Bool) × D) ≃ PhysicalSignal a × D :=
  (oracleLocalWiring ((Fin a → Bool) × D)).trans
    (maskedPhysicalWiring a (Equiv.refl (Fin a → Bool)))

theorem oracleAttach_clean (a : ℕ) (x : LogicalSignal a × D) :
    oracleAttachWiring a D
      (oracleLocalClean ((maskSignalEquiv (D := D) a (Equiv.refl (Fin a → Bool))).symm x)) =
        physicalClean a x := by
  simp only [oracleAttachWiring,oracleLocalClean,Equiv.trans_apply,Equiv.apply_symm_apply]
  change physicalEquiv a D ((maskSignalEquiv a (Equiv.refl (Fin a → Bool)))
    ((maskSignalEquiv a (Equiv.refl (Fin a → Bool))).symm x),(false,false,false)) = _
  rw [Equiv.apply_symm_apply]
  rfl

/-- The original oracle reads exactly one named flag after this wire regrouping. -/
def originalSingleFlagPort (a : ℕ) (D : Type*) [Fintype D] [DecidableEq D] :
    QueryPort ((Fin a → Bool) × D) (PhysicalSignal a × D) :=
  (relabelPort (oracleAttachWiring a D)).comp
    (GraphEncoding.singleFlagOraclePort ((Fin a → Bool) × D) (smallTarget 2))

/-- The two elementary families have fixed physical placements, not arbitrary
work-matrix constructors. -/
inductive SingleFlagGate (a : ℕ) where
  | qsp (g : PhaseGate (QSVTWire a))
  | oracle (g : PhaseGate OracleLocalWire)

def SingleFlagGate.eval (a : ℕ) : SingleFlagGate a → Matrix.unitaryGroup (PhysicalSignal a × D) ℂ
  | .qsp g => elementaryPlacement g.eval
  | .oracle g => rewireUnitary (oracleAttachWiring a D) (elementaryPlacement g.eval)

def SingleFlagGate.arity {a : ℕ} : SingleFlagGate a → ℕ
  | .qsp g => g.arity
  | .oracle g => g.arity

theorem SingleFlagGate.arity_le_two {a : ℕ} (g : SingleFlagGate a) : g.arity≤2 := by
  cases g <;> exact PhaseGate.arity_le_two _

abbrev SingleFlagCircuit (a : ℕ) (D B : Type*) :=
  NamedCircuit (SingleFlagGate a) ((Fin a → Bool) × D) B (PhysicalSignal a × D)

def singleFlagQSPMacro (a : ℕ) (code : List (PhaseGate (QSVTWire a))) : SingleFlagCircuit a D B :=
  code.map (fun g => .gate (.qsp g))

theorem singleFlagQSPMacro_toQuery (a : ℕ) (code : List (PhaseGate (QSVTWire a))) :
    (singleFlagQSPMacro (D := D) (B := B) a code).toQuery (SingleFlagGate.eval a) =
      (elementaryMacro (A := (Fin a → Bool) × D) (B := B) (D := D) code).toQuery := by
  induction code with
  | nil => rfl
  | cons g code ih =>
    simpa [singleFlagQSPMacro,NamedCircuit.toQuery,NamedInstruction.toQuery,SingleFlagGate.eval,
      elementaryMacro,ElementaryCircuit.toQuery,ElementaryInstruction.toQuery] using
      congrArg (List.cons (.work (elementaryPlacement g.eval))) ih

theorem singleFlagQSPMacro_workGates (a : ℕ) (code : List (PhaseGate (QSVTWire a))) :
    (singleFlagQSPMacro (D := D) (B := B) a code).workGates=code.length := by
  induction code <;> simp_all [singleFlagQSPMacro,NamedCircuit.workGates]

def attachOracleInstruction (a : ℕ) :
    ElementaryInstruction ((Fin a → Bool) × D) B OracleLocalWire ((Fin a → Bool) × D) →
      NamedInstruction (SingleFlagGate a) ((Fin a → Bool) × D) B (PhysicalSignal a × D)
  | .gate g => .gate (.oracle g)
  | .matrixCall p b => .matrixCall ((relabelPort (oracleAttachWiring a D)).comp p) b
  | .vectorCall p b => .vectorCall ((relabelPort (oracleAttachWiring a D)).comp p) b

def attachOracleCircuit (a : ℕ)
    (c : ElementaryCircuit ((Fin a → Bool) × D) B OracleLocalWire ((Fin a → Bool) × D)) :
    SingleFlagCircuit a D B := c.map (attachOracleInstruction a)

theorem attachOracleCircuit_toQuery (a : ℕ)
    (c : ElementaryCircuit ((Fin a → Bool) × D) B OracleLocalWire ((Fin a → Bool) × D)) :
    (attachOracleCircuit a c).toQuery (SingleFlagGate.eval a)=
      c.toQuery.lift (relabelPort (oracleAttachWiring a D)) := by
  induction c with
  | nil => rfl
  | cons g c ih =>
    cases g <;> simp_all [attachOracleCircuit,attachOracleInstruction,NamedCircuit.toQuery,
      NamedInstruction.toQuery,SingleFlagGate.eval,ElementaryCircuit.toQuery,
      ElementaryInstruction.toQuery,QueryCircuit.lift,QueryInstruction.lift]

theorem attachOracleCircuit_workGates (a : ℕ)
    (c : ElementaryCircuit ((Fin a → Bool) × D) B OracleLocalWire ((Fin a → Bool) × D)) :
    (attachOracleCircuit a c).workGates=c.workGates := by
  induction c with
  | nil => rfl
  | cons g c ih =>
    cases g <;> simp_all [attachOracleCircuit,attachOracleInstruction,NamedCircuit.workGates,ElementaryCircuit.workGates]

theorem attachedOracle_intertwines (a : ℕ) (mask : Bool × Bool) (adj : Bool)
    (U : Matrix.unitaryGroup ((Fin a → Bool) × D) ℂ) (Ub : Matrix.unitaryGroup B ℂ) :
    (((attachOracleCircuit a (oracleLocalCode a mask adj)).toQuery (SingleFlagGate.eval a)).eval U Ub).val *
      basisInsertion (physicalClean a) = basisInsertion (physicalClean a) *
        (rewireUnitary (maskSignalEquiv a (Equiv.refl (Fin a → Bool)))
          ((GraphEncoding.maskedGraphPort ((Fin a → Bool) × D) mask).apply (if adj then U⁻¹ else U))).val := by
  rw [attachOracleCircuit_toQuery,QueryCircuit.lift_eval,relabelPort_apply]
  have hh := clean_intertwines_transport (oracleAttachWiring a D)
    (maskSignalEquiv a (Equiv.refl (Fin a → Bool))) oracleLocalClean
    ((oracleLocalCode a mask adj).toQuery.eval U Ub)
    ((GraphEncoding.maskedGraphPort ((Fin a → Bool) × D) mask).apply (if adj then U⁻¹ else U))
    (oracleLocalCode_intertwines a mask adj U Ub)
  simpa only [oracleAttach_clean] using hh


section FixedPortRefinement
variable {G A Q L P : Type*} [Fintype A] [DecidableEq A] [Fintype Q] [DecidableEq Q]
  [Fintype L] [DecidableEq L] [Fintype P] [DecidableEq P]

def NamedCircuit.CallsOnly (c : NamedCircuit G A B P) (fixed : QueryPort A P) : Prop :=
  ∀ p adj, NamedInstruction.matrixCall p adj ∈ c → p=fixed

theorem callsOnly_append (fixed : QueryPort A P) (c d : NamedCircuit G A B P)
    (hc : c.CallsOnly fixed) (hd : d.CallsOnly fixed) : (c++d).CallsOnly fixed := by
  intro p adj hp
  rcases List.mem_append.mp hp with h|h
  · exact hc p adj h
  · exact hd p adj h

/-- Whole-macro replacement retaining the exact single-flag query port in the
final emitted program, rather than merely retaining a count of query calls. -/
theorem refine_named_single_port (gate : G → Matrix.unitaryGroup P ℂ)
    (c : QueryCircuit Q B L) (hzero : c.vectorQueries=0) (J : Matrix P L ℂ)
    (oracle : Matrix.unitaryGroup A ℂ → Matrix.unitaryGroup Q ℂ)
    (fixed : QueryPort A P) (W C N : ℕ)
    (hwork : ∀ U, QueryInstruction.work U ∈ c → ∃ code : NamedCircuit G A B P,
      (code.toQuery gate).matrixQueries=0 ∧ (code.toQuery gate).vectorQueries=0 ∧
      code.workGates≤W ∧ code.CallsOnly fixed ∧
      ∀ UA Ub, ((code.toQuery gate).eval UA Ub).val*J=J*U.val)
    (hquery : ∀ p adj, QueryInstruction.matrixCall p adj ∈ c → ∃ code : NamedCircuit G A B P,
      (code.toQuery gate).matrixQueries=N ∧ (code.toQuery gate).vectorQueries=0 ∧
      code.workGates≤C ∧ code.CallsOnly fixed ∧
      ∀ UA Ub, ((code.toQuery gate).eval UA Ub).val*J=
        J*(p.apply (if adj then (oracle UA)⁻¹ else oracle UA)).val) :
    ∃ out : NamedCircuit G A B P,
      (out.toQuery gate).matrixQueries=N*c.matrixQueries ∧ (out.toQuery gate).vectorQueries=0 ∧
      out.workGates≤W*workInstructions c+C*c.matrixQueries ∧ out.CallsOnly fixed ∧
      ∀ UA Ub, ((out.toQuery gate).eval UA Ub).val*J=J*(c.eval (oracle UA) Ub).val := by
  induction c with
  | nil =>
    refine ⟨[],by simp [NamedCircuit.toQuery,QueryCircuit.matrixQueries],rfl,
      by simp [NamedCircuit.workGates,workInstructions,QueryCircuit.matrixQueries],?_,?_⟩
    · intro p adj hp; simp at hp
    · intro UA Ub; simp [NamedCircuit.toQuery,QueryCircuit.eval]
  | cons g c ih =>
    have hz : QueryCircuit.vectorQueries c=0 := by
      cases g <;> simp only [QueryCircuit.vectorQueries] at hzero <;> omega
    obtain ⟨tail,hm,hv,hg,hs,he⟩ := ih hz
      (fun U h => hwork U (List.mem_cons_of_mem _ h))
      (fun p adj h => hquery p adj (List.mem_cons_of_mem _ h))
    cases g with
    | work U =>
      obtain ⟨code,hcm,hcv,hcg,hcs,hce⟩ := hwork U (by simp)
      refine ⟨code++tail,?_,?_,?_,callsOnly_append fixed code tail hcs hs,?_⟩
      · simp [NamedCircuit.toQuery_append,QueryCircuit.matrixQueries_append,hcm,hm,QueryCircuit.matrixQueries]
      · simp [NamedCircuit.toQuery_append,QueryCircuit.vectorQueries_append,hcv,hv]
      · simp only [NamedCircuit.workGates_append,workInstructions,QueryCircuit.matrixQueries,Nat.mul_add,Nat.mul_one]
        omega
      · intro UA Ub
        simp only [NamedCircuit.toQuery_append,QueryCircuit.eval_append,Submonoid.coe_mul,
          QueryCircuit.eval,QueryInstruction.eval]
        exact intertwines_mul J _ _ _ _ (hce UA Ub) (he UA Ub)
    | matrixCall p adj =>
      obtain ⟨code,hcm,hcv,hcg,hcs,hce⟩ := hquery p adj (by simp)
      refine ⟨code++tail,?_,?_,?_,callsOnly_append fixed code tail hcs hs,?_⟩
      · simp [NamedCircuit.toQuery_append,QueryCircuit.matrixQueries_append,hcm,hm,QueryCircuit.matrixQueries,Nat.mul_add,Nat.add_comm]
      · simp [NamedCircuit.toQuery_append,QueryCircuit.vectorQueries_append,hcv,hv]
      · simp only [NamedCircuit.workGates_append,workInstructions,QueryCircuit.matrixQueries,Nat.mul_add,Nat.mul_one]
        omega
      · intro UA Ub
        simp only [NamedCircuit.toQuery_append,QueryCircuit.eval_append,Submonoid.coe_mul,
          QueryCircuit.eval,QueryInstruction.eval]
        exact intertwines_mul J _ _ _ _ (hce UA Ub) (he UA Ub)
    | vectorCall p adj =>
      simp only [QueryCircuit.vectorQueries] at hzero
      omega
end FixedPortRefinement

theorem attachedOracle_callsOnly (a : ℕ) (mask : Bool × Bool) (adj : Bool) :
    (attachOracleCircuit (D := D) (B := B) a (oracleLocalCode a mask adj)).CallsOnly
      (originalSingleFlagPort a D) := by
  intro p b hp
  obtain ⟨g,hg,hEq⟩ := List.mem_map.mp hp
  cases g with
  | gate g => cases hEq
  | vectorCall p b => cases hEq
  | matrixCall q c =>
    obtain ⟨rfl,rfl⟩ := NamedInstruction.matrixCall.inj hEq
    have h := GraphEncoding.maskedOracleCircuit_single_flag _ _ _ _ _ q c hg
    rw [h.1]
    rfl

theorem singleFlag_prod_refl {S : Type*} [Fintype S] [DecidableEq S]
    (U : Matrix.unitaryGroup (S × D) ℂ) :
    rewireUnitary (Equiv.prodCongr (Equiv.refl S) (Equiv.refl D)) U=U := by
  apply Subtype.ext
  rfl

/-- Full QSVT synthesis with only a single physical flag controlling each
original oracle invocation; every query retains this provenance in the result. -/
theorem boundedTransform_single_flag_synthesis (a : ℕ) (z₀ : Circle) (zs : List Circle) :
    ∃ out : SingleFlagCircuit a D B,
      (out.toQuery (SingleFlagGate.eval a)).matrixQueries=4*zs.length ∧
      (out.toQuery (SingleFlagGate.eval a)).vectorQueries=0 ∧
      out.workGates≤15848*(zs.length+1)*(a+1) ∧ out.CallsOnly (originalSingleFlagPort a D) ∧
      ∀ (UA : Matrix.unitaryGroup ((Fin a → Bool) × D) ℂ) (Ub : Matrix.unitaryGroup B ℂ),
        ((out.toQuery (SingleFlagGate.eval a)).eval UA Ub).val*basisInsertion (physicalClean a)=
          basisInsertion (physicalClean a)*(boundedTransformUnitary (fun _ : Fin a => false) UA z₀ zs).val := by
  let c := boundedTransformCircuit (D := D) (B := B) (fun _ : Fin a => false) z₀ zs
  have hw : ∀ U, QueryInstruction.work U ∈ c → ∃ code : SingleFlagCircuit a D B,
      (code.toQuery (SingleFlagGate.eval a)).matrixQueries=0 ∧
      (code.toQuery (SingleFlagGate.eval a)).vectorQueries=0 ∧ code.workGates≤781*(a+1) ∧
      code.CallsOnly (originalSingleFlagPort a D) ∧
      ∀ UA Ub, ((code.toQuery (SingleFlagGate.eval a)).eval UA Ub).val*basisInsertion (physicalClean a)=
        basisInsertion (physicalClean a)*U.val := by
    intro U hU
    obtain ⟨code,hlen,he⟩ := bounded_work_synthesis a z₀ zs U hU
    refine ⟨singleFlagQSPMacro a code,?_,?_,?_,?_,?_⟩
    · rw [singleFlagQSPMacro_toQuery]; exact (elementaryMacro_queries _).1
    · rw [singleFlagQSPMacro_toQuery]; exact (elementaryMacro_queries _).2
    · rw [singleFlagQSPMacro_workGates]; exact hlen
    · intro p adj hp; simp [singleFlagQSPMacro] at hp
    · intro UA Ub; rw [singleFlagQSPMacro_toQuery,elementaryMacro_eval]; exact he
  have hq : ∀ p adj, QueryInstruction.matrixCall p adj ∈ c → ∃ code : SingleFlagCircuit a D B,
      (code.toQuery (SingleFlagGate.eval a)).matrixQueries=1 ∧
      (code.toQuery (SingleFlagGate.eval a)).vectorQueries=0 ∧ code.workGates≤2400 ∧
      code.CallsOnly (originalSingleFlagPort a D) ∧
      ∀ UA Ub, ((code.toQuery (SingleFlagGate.eval a)).eval UA Ub).val*basisInsertion (physicalClean a)=
        basisInsertion (physicalClean a)*(p.apply (if adj then UA⁻¹ else UA)).val := by
    intro p adj hp
    obtain ⟨branch,hbranch⟩ := bounded_query_controls _ z₀ zs p adj hp
    refine ⟨attachOracleCircuit a (oracleLocalCode a (branch,adj) adj),?_,?_,?_,attachedOracle_callsOnly _ _ _,?_⟩
    · rw [attachOracleCircuit_toQuery,(QueryCircuit.lift_counts _ _).1]
      exact (oracleLocalCode_counts _ _ _).1
    · rw [attachOracleCircuit_toQuery,(QueryCircuit.lift_counts _ _).2]
      exact (oracleLocalCode_counts _ _ _).2.1
    · rw [attachOracleCircuit_workGates]; exact (oracleLocalCode_counts _ _ _).2.2
    · intro UA Ub
      rw [hbranch]
      have hr := nested_mask_relabel a (Equiv.refl (Fin a → Bool)) branch adj (if adj then UA⁻¹ else UA)
      simp only [singleFlag_prod_refl] at hr
      rw [hr]
      exact attachedOracle_intertwines a (branch,adj) adj UA Ub
  obtain ⟨out,hm,hv,hg,hp,he⟩ := refine_named_single_port (SingleFlagGate.eval a) c
    (boundedTransformCircuit_counts _ z₀ zs).2 (basisInsertion (physicalClean a)) id
    (originalSingleFlagPort a D) (781*(a+1)) 2400 1 hw hq
  refine ⟨out,?_,hv,?_,hp,?_⟩
  · rw [(boundedTransformCircuit_counts _ z₀ zs).1] at hm
    simpa using hm
  · have hcw := bounded_work_count (D := D) (B := B) a z₀ zs
    change workInstructions c=8*zs.length+4 at hcw
    have hcq := (boundedTransformCircuit_counts (D := D) (B := B) (fun _ : Fin a => false) z₀ zs).1
    change c.matrixQueries=4*zs.length at hcq
    rw [hcw,hcq] at hg
    nlinarith
  · intro UA Ub
    simpa only [c,boundedTransformCircuit_eval] using he UA Ub

/-- Lemma2.4 in the literal single-controlled-oracle model, preserving a+5
signal width, exact polynomial block, and every original query's single flag. -/
theorem lemma24_single_flag_encoding [Nonempty D] (a : ℕ) (p : ℝ[X])
    (hp : Function.Even p.eval) (hbound : ∀ x : ℝ, |x|≤1 → |p.eval x|≤1) :
    ∃ out : SingleFlagCircuit a D B,
      (out.toQuery (SingleFlagGate.eval a)).matrixQueries≤4*p.natDegree ∧
      (out.toQuery (SingleFlagGate.eval a)).vectorQueries=0 ∧
      out.workGates≤15848*(p.natDegree+1)*(a+1) ∧ out.CallsOnly (originalSingleFlagPort a D) ∧
      ∀ (UA : Matrix.unitaryGroup ((Fin a → Bool) × D) ℂ) (Ub : Matrix.unitaryGroup B ℂ)
        (A : Matrix D D ℂ), A.IsHermitian → IsBlockEncoding (fun _ : Fin a => false) 1 0 UA A →
        IsBlockEncoding (physicalZero a) 1 0 ((out.toQuery (SingleFlagGate.eval a)).eval UA Ub)
          (Polynomial.aeval A (liftReal p)) := by
  obtain ⟨z₀,zs,hlen,henc⟩ := bounded_even_exact_encoding (D := D) (fun _ : Fin a => false) p hp hbound
  obtain ⟨out,hm,hv,hg,hports,he⟩ := boundedTransform_single_flag_synthesis (D := D) (B := B) a z₀ zs
  refine ⟨out,by omega,hv,hg.trans ?_,hports,?_⟩
  · exact Nat.mul_le_mul_right (a+1) (Nat.mul_le_mul_left 15848 (by omega))
  · intro UA Ub A hA hUA
    have hb := henc UA A hA hUA
    have hc := signalBlock_of_clean_intertwines (physicalCleanSignal a)
      (physicalCleanSignal_injective a) ((false,false),fun _ : Fin a => false)
      ((out.toQuery (SingleFlagGate.eval a)).eval UA Ub).val
      (boundedTransformUnitary (fun _ : Fin a => false) UA z₀ zs).val (he UA Ub)
    rw [physicalClean_zero] at hc
    simpa only [IsBlockEncoding,hc] using hb

end OptimalQLS.PolynomialTransform
