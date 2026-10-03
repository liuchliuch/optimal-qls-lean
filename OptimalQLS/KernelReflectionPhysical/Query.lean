import OptimalQLS.KernelReflectionPhysical.Work
import OptimalQLS.Preparation.CompilerAttachment.LocalOracle

/-! # One literal single-flag query for the kernel transducer

The tested label bits are computed into a clean flag by real elementary gates.
The original oracle acts on its entire signal/data register, including arbitrary
off-signal columns. All three shared scratch bits return to zero.
-/
noncomputable section
namespace OptimalQLS.KernelReflectionPhysical
open Matrix TransducerCompiler BinaryClock PolynomialTransform DirtyAncilla
open Preparation Preparation.WorkGates
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false

/-- Label bit0 and the external work-control bit are query spectators. -/
def querySourceFrame (a : ℕ) (D : Type*) :
    (((Bool × Bool) × (Bits a × D)) × (Bool × Bool)) ≃ Source a D where
  toFun p := ((labelNumber ![p.2.1,p.1.1.1,p.1.1.2],p.1.2),p.2.2)
  invFun p := (((labelBits p.1.1 1,labelBits p.1.1 2),p.1.2),(labelBits p.1.1 0,p.2))
  left_inv p := by rcases p with ⟨⟨⟨b,c⟩,x⟩,d,e⟩; simp
  right_inv p := by
    rcases p with ⟨⟨j,x⟩,c⟩
    have hj : ![labelBits j 0,labelBits j 1,labelBits j 2]=labelBits j := by
      funext i; fin_cases i <;> rfl
    simp only [hj,labelNumber_labelBits]

/-- A literal regrouping of label bits1,2, the original oracle register, and scratch. -/
def queryFrame (a : ℕ) (D : Type*) :
    ((OracleLocalState × (Bits a × D)) × (Bool × Bool)) ≃ Physical a D :=
  (Equiv.prodCongr (oracleLocalWiring (Bits a × D)) (Equiv.refl (Bool × Bool))).trans
    ((Preparation.CompilerAttachment.scratchFrame (querySourceFrame a D)).trans
      (registerEquiv a D))

theorem queryFrame_clean (a : ℕ) (x : (Bool × Bool) × (Bits a × D)) (r : Bool × Bool) :
    queryFrame a D (oracleLocalClean x,r) = sourceInsertion false (querySourceFrame a D (x,r)) := by
  simp only [queryFrame,oracleLocalClean,Equiv.trans_apply,Equiv.prodCongr_apply,
    Prod.map_apply,Equiv.apply_symm_apply]
  rfl

variable {D B : Type*} [Fintype D] [DecidableEq D] [Fintype B] [DecidableEq B]

/-- Full source oracle: exactly labels2 and3 receive UH. -/
def sourceQuery {a : ℕ} (U : Matrix.unitaryGroup (Bits a × D) ℂ) :
    Matrix.unitaryGroup (Source a D) ℂ :=
  GateSynthesis.placeHom (querySourceFrame a D)
    ((GraphEncoding.maskedGraphPort (Bits a × D) (true,false)).apply U)

def queryGateEval (a : ℕ) (g : PhaseGate OracleLocalWire) :
    Matrix.unitaryGroup (Physical a D) ℂ :=
  GateSynthesis.placeHom (queryFrame a D) (elementaryPlacement g.eval)

def queryProgram (a : ℕ) :
    NamedCircuit (PhaseGate OracleLocalWire) (Bits a × D) B (Physical a D) :=
  Preparation.CompilerAttachment.attachList (queryFrame a D) id
    (Preparation.CompilerAttachment.localOracleCode (true,false) false)

theorem queryProgram_eval (a : ℕ) (U : Matrix.unitaryGroup (Bits a × D) ℂ)
    (Ub : Matrix.unitaryGroup B ℂ) :
    ((queryProgram a).toQuery (queryGateEval a)).eval U Ub =
      GateSynthesis.placeHom (queryFrame a D)
        ((Preparation.CompilerAttachment.localOracleCode (true,false) false).toQuery.eval U Ub) :=
  Preparation.CompilerAttachment.attachList_eval _ id _ (fun _=>rfl) _ U Ub

theorem queryProgram_counts (a : ℕ) :
    ((queryProgram (D := D) (B := B) a).toQuery (queryGateEval a)).matrixQueries=1 ∧
      ((queryProgram (D := D) (B := B) a).toQuery (queryGateEval a)).vectorQueries=0 ∧
      (queryProgram (D := D) (B := B) a).workGates ≤ 2400 := by
  have h := Preparation.CompilerAttachment.localOracleCode_counts
    (A := Bits a × D) (B := B) (true,false) false
  rw [queryProgram,Preparation.CompilerAttachment.attachList_toQuery
    (queryFrame a D) id (queryGateEval a) (fun _=>rfl)]
  exact ⟨(QueryCircuit.lift_counts _ _).1.trans h.1,
    (QueryCircuit.lift_counts _ _).2.trans h.2.1,
    (Preparation.CompilerAttachment.attachList_workGates _ _ _).le.trans h.2.2⟩

theorem queryProgram_intertwines (a : ℕ) (U : Matrix.unitaryGroup (Bits a × D) ℂ)
    (Ub : Matrix.unitaryGroup B ℂ) :
    (((queryProgram a).toQuery (queryGateEval a)).eval U Ub).val *
        basisInsertion (sourceInsertion false) =
      basisInsertion (sourceInsertion false) * (sourceQuery U).val := by
  rw [queryProgram_eval]
  have ht := tensor_intertwines (D := Bool × Bool) oracleLocalClean
    ((Preparation.CompilerAttachment.localOracleCode (true,false) false).toQuery.eval U Ub)
    ((GraphEncoding.maskedGraphPort (Bits a × D) (true,false)).apply U)
    (Preparation.CompilerAttachment.localOracleCode_intertwines (true,false) false U Ub)
  have he := clean_intertwines_transport (queryFrame a D) (querySourceFrame a D)
    (fun x => (oracleLocalClean x.1,x.2)) _ _ ht
  have hc : (fun x => queryFrame a D
      (oracleLocalClean ((querySourceFrame a D).symm x).1,
        ((querySourceFrame a D).symm x).2)) = sourceInsertion false := by
    funext x
    rw [queryFrame_clean,Equiv.apply_symm_apply]
  rw [hc] at he
  exact he

/-- The only query port reads the one scratch flag after its literal computation. -/
def singleFlagPort (a : ℕ) : QueryPort (Bits a × D) (Physical a D) :=
  (scratchPort (queryFrame a D)).comp
    (GraphEncoding.singleFlagOraclePort (Bits a × D) (smallTarget 2))

theorem queryProgram_single_flag (a : ℕ) (p : QueryPort (Bits a × D) (Physical a D))
    (adj : Bool) (hp : NamedInstruction.matrixCall p adj ∈ queryProgram (B := B) a) :
    p=singleFlagPort a ∧ adj=false := by
  obtain ⟨i,hi,hEq⟩ := List.mem_map.mp hp
  cases i with
  | gate g => cases hEq
  | matrixCall q b =>
    obtain ⟨hq,hb⟩ := GraphEncoding.maskedOracleCircuit_single_flag
      2 id Function.injective_id ![true,false] false q b hi
    subst q; subst b; cases hEq
    exact ⟨rfl,rfl⟩
  | vectorCall q b => cases hEq

theorem queryProgram_real (a : ℕ) (g : PhaseGate OracleLocalWire)
    (hg : NamedInstruction.gate g ∈ queryProgram (D := D) (B := B) a) :
    GraphEncoding.RealPhaseGate g := by
  obtain ⟨i,hi,hEq⟩ := List.mem_map.mp hg
  cases i with
  | gate p =>
    cases hEq
    exact (GraphEncoding.maskedOracleCircuit_safe 2 id Function.injective_id
      ![true,false] false).1 p hi
  | matrixCall q b => cases hEq
  | vectorCall q b => cases hEq

/-- Explicit entries preserve all unused labels and all oracle columns. -/
theorem sourceQuery_entries {a : ℕ} (U : Matrix.unitaryGroup (Bits a × D) ℂ)
    (j k : Fin 8) (x y : Bits a × D) (c d : Bool) :
    (sourceQuery U).val ((j,x),c) ((k,y),d) =
      if j=k ∧ c=d then
        (if j=2 ∨ j=3 then U.val x y else if x=y then 1 else 0) else 0 := by
  rw [sourceQuery,GraphEncoding.placeHom_entries]
  simp only [querySourceFrame,GraphEncoding.maskedGraphPort_apply_entries]
  fin_cases j <;> fin_cases k <;> simp [labelBits,Prod.mk.injEq,Matrix.one_apply,GraphEncoding.maskedGraphPort_apply_entries]

/-- On every coherent vector, UH is applied to the two full private sectors. -/
theorem sourceQuery_apply {a : ℕ} (U : Matrix.unitaryGroup (Bits a × D) ℂ)
    (v : Source a D → ℂ) (j : Fin 8) (x : Bits a × D) (c : Bool) :
    ((sourceQuery U).val *ᵥ v) ((j,x),c) =
      if j=2 ∨ j=3 then (U.val *ᵥ (fun y => v ((j,y),c))) x else v ((j,x),c) := by
  simp only [Matrix.mulVec, dotProduct,Fintype.sum_prod_type,sourceQuery_entries]
  by_cases h : j=2 ∨ j=3
  · simp [h,ite_and,Matrix.mulVec,dotProduct]
  · rcases x with ⟨s,d⟩
    simp [h,ite_and,Prod.mk.injEq]

end OptimalQLS.KernelReflectionPhysical
