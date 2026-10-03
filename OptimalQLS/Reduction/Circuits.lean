import OptimalQLS.PolynomialTransform.SingleFlagEncoding
import OptimalQLS.LowerBounds.HermitianDilation

/-! # Literal original-oracle circuits for Hermitian input reduction

The external control and the dilation bit are actual wires. Two masked-query
adapters compute their conjunction into one clean flag, query that flag only,
and uncompute. Every work instruction is a real one- or two-qubit gate.
-/
noncomputable section
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
namespace OptimalQLS.Reduction
open Matrix TransducerCompiler BinaryClock PolynomialTransform DirtyAncilla
variable {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

abbrev DilationWire := OracleLocalWire
abbrev DilationSpace (A : Type*) := ElementarySpace DilationWire A

/-- Clean computational insertion, with two live bits and three scratch bits. -/
def dilationClean (x : (Bool × Bool) × A) : DilationSpace A := oracleLocalClean x

theorem dilationClean_eq (e d : Bool) (i : A) :
    dilationClean ((e,d),i) =
      ((false,fun k : DilationWire => match k with
        | .inl k => if k=0 then e else d | .inr _ => false),i) := by
  simp [dilationClean,oracleLocalClean,oracleLocalWiring]
  funext k
  cases k <;> rfl

def dilationMaskCode (mask : Bool × Bool) (adj : Bool) :
    ElementaryCircuit A B DilationWire A :=
  GraphEncoding.maskedOracleCircuit 2 id Function.injective_id ![mask.1,mask.2] adj

theorem dilationMaskCode_intertwines (mask : Bool × Bool) (adj : Bool)
    (U : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) :
    ((dilationMaskCode mask adj).toQuery.eval U Ub).val*basisInsertion dilationClean =
      basisInsertion dilationClean *((GraphEncoding.maskedGraphPort A mask).apply
        (if adj then U⁻¹ else U)).val := by
  apply basisInsertion_intertwines
  rintro ⟨⟨e,d⟩,i⟩
  have he (V : Matrix.unitaryGroup A ℂ) :
      V.val *ᵥ Pi.single i 1 = ∑ k, V.val k i • (Pi.single k 1 : A → ℂ) := by
    ext k
    simp [Matrix.mulVec_single_one,Pi.single_apply]
  rw [GraphEncoding.maskedGraphPort_basis_expansion mask (e,d) _ _ _ _ (he _)]
  rw [dilationClean_eq]
  change ((GraphEncoding.maskedOracleCircuit (A := A) (B := B)
    2 id Function.injective_id ![mask.1,mask.2] adj).toQuery.eval U Ub).val *ᵥ
      Pi.single ((false,fun k : DilationWire => match k with
        | .inl k => if k=0 then e else d | .inr _ => false),i) 1 = _
  rw [GraphEncoding.maskedOracleCircuit_basis _ _ _ _ _ _ (by rfl)]
  by_cases hm : (e,d)=mask
  · rcases mask with ⟨m,n⟩
    rcases Prod.mk.inj hm with ⟨rfl,rfl⟩
    simp [Fin.forall_fin_succ,Matrix.mulVec_sum,Matrix.mulVec_smul,basisInsertion_basis,
      singleFlag_basisInsertion_col,dilationClean_eq]
  · have hn : ¬(e=mask.1 ∧ d=mask.2) := fun h => hm (Prod.ext h.1 h.2)
    simp [Fin.forall_fin_succ,hm,hn,basisInsertion_basis,
      singleFlag_basisInsertion_col,dilationClean_eq]

def dilationFlipEquiv (A : Type*) : Equiv.Perm ((Bool × Bool) × A) where
  toFun x := ((x.1.1,Bool.xor x.1.2 x.1.1),x.2)
  invFun x := ((x.1.1,Bool.xor x.1.2 x.1.1),x.2)
  left_inv x := by rcases x with ⟨⟨e,d⟩,i⟩; cases e <;> cases d <;> rfl
  right_inv x := by rcases x with ⟨⟨e,d⟩,i⟩; cases e <;> cases d <;> rfl

def dilationFlipProgram : Program DilationWire :=
  [.cx (.inl 0) (.inl 1) (by decide)]

def dilationFlipCode : ElementaryCircuit A B DilationWire A :=
  GraphEncoding.realProgramCircuit A B dilationFlipProgram

theorem dilationFlipCode_intertwines (U : Matrix.unitaryGroup A ℂ)
    (Ub : Matrix.unitaryGroup B ℂ) :
    ((dilationFlipCode (A := A) (B := B)).toQuery.eval U Ub).val*basisInsertion dilationClean =
      basisInsertion dilationClean *(permutation (dilationFlipEquiv A)).val := by
  apply basisInsertion_intertwines
  rintro ⟨⟨e,d⟩,i⟩
  have hv : (permutation (dilationFlipEquiv A)).val *ᵥ Pi.single ((e,d),i) 1 =
      Pi.single ((e,Bool.xor d e),i) 1 := by
    rw [permutation_apply]
    ext ⟨⟨r,s⟩,j⟩
    cases e <;> cases d <;> cases r <;> cases s <;>
      simp [dilationFlipEquiv,Pi.single_apply]
  rw [hv,basisInsertion_basis,dilationClean_eq,dilationClean_eq]
  rw [dilationFlipCode,GraphEncoding.realProgramCircuit_basis]
  congr 2
  apply congrArg (fun b : DilationWire → Bool => (false,b))
  funext k
  cases k with
  | inl k => fin_cases k <;> simp [dilationFlipProgram,run,Gate.act]
  | inr k => simp [dilationFlipProgram,run,Gate.act]

/-- A single physical control on an arbitrary oracle target. -/
def bitControlPort (Q : Type*) : QueryPort Q (Bool × Q) where
  multiplicity := Fintype.card Bool
  wiring := (Equiv.prodCongr (Equiv.refl Q) (Fintype.equivFin Bool).symm).trans
    (Equiv.prodComm Q Bool)
  control := fun k => (Fintype.equivFin Bool).symm k

theorem bitControlPort_entries {Q : Type*} [Fintype Q] [DecidableEq Q]
    (U : Matrix.unitaryGroup Q ℂ) (e f : Bool) (i j : Q) :
    ((bitControlPort Q).apply U).val (e,i) (f,j) =
      if e=f then (if e then U.val i j else if i=j then 1 else 0) else 0 := by
  simp [bitControlPort,QueryPort.apply,rewireUnitary,controlledUnitary,
    Matrix.blockDiagonal_apply,Matrix.one_apply]
  split_ifs <;> simp_all [Matrix.one_apply]

/-- Merely regard the dilation bit as the left/right sum label. -/
def dilationLogicalWiring (A : Type*) : ((Bool × Bool) × A) ≃ Bool × (A ⊕ A) :=
  (Equiv.prodAssoc Bool Bool A).trans
    (Equiv.prodCongr (Equiv.refl Bool) (GraphEncoding.sumBitWiring A))

def controlledDilation (U : Matrix.unitaryGroup A ℂ) :
    Matrix.unitaryGroup ((Bool × Bool) × A) ℂ :=
  rewireUnitary (dilationLogicalWiring A).symm
    ((bitControlPort (A ⊕ A)).apply (LowerBounds.hermitianUnitaryDilation U))

theorem controlledDilation_factor (U : Matrix.unitaryGroup A ℂ) :
    controlledDilation U =
      (GraphEncoding.maskedGraphPort A (true,true)).apply U⁻¹ *
      ((GraphEncoding.maskedGraphPort A (true,false)).apply U *
        permutation (dilationFlipEquiv A)) := by
  apply Subtype.ext
  ext ⟨⟨e,d⟩,i⟩ ⟨⟨f,c⟩,j⟩
  cases e <;> cases d <;> cases f <;> cases c <;>
    simp [controlledDilation,rewireUnitary,dilationLogicalWiring,
      GraphEncoding.sumBitWiring,bitControlPort_entries,LowerBounds.hermitianUnitaryDilation,
      LowerBounds.hermitianDilation,Matrix.mul_apply,Fintype.sum_prod_type,
      GraphEncoding.maskedGraphPort_apply_entries,permutation,dilationFlipEquiv,
      PEquiv.toMatrix,Matrix.one_apply]

/-- Two calls to the supplied original oracle, with a literal CNOT and two
compute-query-uncompute adapters. The same word implements the adjoint. -/
def dilationOracleCircuit (_adj : Bool) : ElementaryCircuit A B DilationWire A :=
  dilationFlipCode ++ dilationMaskCode (true,false) false ++ dilationMaskCode (true,true) true

theorem dilationOracleCircuit_intertwines (adj : Bool) (U : Matrix.unitaryGroup A ℂ)
    (Ub : Matrix.unitaryGroup B ℂ) :
    ((dilationOracleCircuit adj).toQuery.eval U Ub).val*basisInsertion dilationClean =
      basisInsertion dilationClean *(controlledDilation U).val := by
  rw [controlledDilation_factor]
  simp only [dilationOracleCircuit,ElementaryCircuit.toQuery_append,
    QueryCircuit.eval_append,Submonoid.coe_mul]
  exact intertwines_mul _ _ _ _ _
    (intertwines_mul _ _ _ _ _ (dilationFlipCode_intertwines U Ub)
      (dilationMaskCode_intertwines (true,false) false U Ub))
    (dilationMaskCode_intertwines (true,true) true U Ub)

theorem hermitianUnitaryDilation_inv (U : Matrix.unitaryGroup A ℂ) :
    (LowerBounds.hermitianUnitaryDilation U)⁻¹=LowerBounds.hermitianUnitaryDilation U := by
  apply Subtype.ext
  exact LowerBounds.hermitianDilation_hermitian U.val

/-- Clean inclusion in the manuscript's sum-label notation. -/
def dilationSumClean (x : Bool × (A ⊕ A)) : DilationSpace A :=
  dilationClean ((dilationLogicalWiring A).symm x)

/-- Entire controlled/adjoint oracle semantics, including every target column
and the disabled control sector, with all three scratch qubits returned. -/
theorem dilationOracleCircuit_sum_intertwines (adj : Bool)
    (U : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) :
    ((dilationOracleCircuit adj).toQuery.eval U Ub).val*basisInsertion dilationSumClean =
      basisInsertion dilationSumClean *
        ((bitControlPort (A ⊕ A)).apply
          (if adj then (LowerBounds.hermitianUnitaryDilation U)⁻¹
            else LowerBounds.hermitianUnitaryDilation U)).val := by
  simp only [hermitianUnitaryDilation_inv,ite_self]
  have h := clean_intertwines_transport (Equiv.refl (DilationSpace A))
    (dilationLogicalWiring A) dilationClean
    ((dilationOracleCircuit adj).toQuery.eval U Ub) (controlledDilation U)
    (dilationOracleCircuit_intertwines adj U Ub)
  have he : rewireUnitary (dilationLogicalWiring A) (controlledDilation U) =
      (bitControlPort (A ⊕ A)).apply (LowerBounds.hermitianUnitaryDilation U) := by
    apply Subtype.ext
    ext i j
    simp [controlledDilation,rewireUnitary]
  rw [he] at h
  exact h

theorem dilationMaskCode_counts (mask : Bool × Bool) (adj : Bool) :
    (dilationMaskCode (A := A) (B := B) mask adj).toQuery.matrixQueries=1 ∧
      (dilationMaskCode (A := A) (B := B) mask adj).toQuery.vectorQueries=0 ∧
      (dilationMaskCode (A := A) (B := B) mask adj).workGates≤2400 :=
  GraphEncoding.maskedOracleCircuit_counts 2 id Function.injective_id ![mask.1,mask.2] adj

theorem dilationFlipCode_counts :
    (dilationFlipCode (A := A) (B := B)).toQuery.matrixQueries=0 ∧
      (dilationFlipCode (A := A) (B := B)).toQuery.vectorQueries=0 ∧
      (dilationFlipCode (A := A) (B := B)).workGates=1 := by
  simp [dilationFlipCode,GraphEncoding.realProgramCircuit,dilationFlipProgram,
    GateSynthesis.lowerProgram,GateSynthesis.lowerGate]

theorem dilationOracleCircuit_counts (adj : Bool) :
    (dilationOracleCircuit (A := A) (B := B) adj).toQuery.matrixQueries=2 ∧
      (dilationOracleCircuit (A := A) (B := B) adj).toQuery.vectorQueries=0 ∧
      (dilationOracleCircuit (A := A) (B := B) adj).workGates≤4801 := by
  have hf := dilationFlipCode_counts (A := A) (B := B)
  have h₀ := dilationMaskCode_counts (A := A) (B := B) (true,false) false
  have h₁ := dilationMaskCode_counts (A := A) (B := B) (true,true) true
  simp only [dilationOracleCircuit,ElementaryCircuit.toQuery_append,
    QueryCircuit.matrixQueries_append,QueryCircuit.vectorQueries_append,
    ElementaryCircuit.workGates_append]
  omega

/-- No emitted original-matrix query can hide a Boolean predicate in its port. -/
theorem dilationOracleCircuit_single_flag (adj : Bool)
    (p : QueryPort A (DilationSpace A)) (b : Bool)
    (h : ElementaryInstruction.matrixCall p b ∈ dilationOracleCircuit (B := B) adj) :
    p=GraphEncoding.singleFlagOraclePort A (smallTarget 2) := by
  simp only [dilationOracleCircuit,List.mem_append] at h
  rcases h with (h|h)|h
  · simp [dilationFlipCode,GraphEncoding.realProgramCircuit,elementaryMacro] at h
  · exact (GraphEncoding.maskedOracleCircuit_single_flag _ _ _ _ _ p b h).1
  · exact (GraphEncoding.maskedOracleCircuit_single_flag _ _ _ _ _ p b h).1

theorem realProgramCircuit_real {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : Program ι) (g : PhaseGate ι)
    (h : ElementaryInstruction.gate g ∈ GraphEncoding.realProgramCircuit A B p) :
    GraphEncoding.RealPhaseGate g ∧ g.arity≤2 := by
  simp only [GraphEncoding.realProgramCircuit,elementaryMacro,List.mem_map] at h
  obtain ⟨_,⟨q,_,rfl⟩,he⟩ := h
  cases he
  exact ⟨GraphEncoding.realPhaseGate_real q,(PhaseGate.real q).arity_le_two⟩

theorem dilationMaskCode_real (mask : Bool × Bool) (adj : Bool) (g : PhaseGate DilationWire)
    (h : ElementaryInstruction.gate g ∈ dilationMaskCode (A := A) (B := B) mask adj) :
    GraphEncoding.RealPhaseGate g ∧ g.arity≤2 := by
  simp only [dilationMaskCode,GraphEncoding.maskedOracleCircuit,List.mem_append,
    List.mem_singleton] at h
  rcases h with (h|h)|h
  · exact realProgramCircuit_real _ g h
  · cases h
  · exact realProgramCircuit_real _ g h

/-- Real elementary matrices and arity are proved for every actual emitted
work instruction; arbitrary work matrices do not count as elementary gates. -/
theorem dilationOracleCircuit_real (adj : Bool) (g : PhaseGate DilationWire)
    (h : ElementaryInstruction.gate g ∈ dilationOracleCircuit (A := A) (B := B) adj) :
    GraphEncoding.RealPhaseGate g ∧ g.arity≤2 := by
  simp only [dilationOracleCircuit,List.mem_append] at h
  rcases h with (h|h)|h
  · exact realProgramCircuit_real dilationFlipProgram g h
  · exact dilationMaskCode_real _ _ g h
  · exact dilationMaskCode_real _ _ g h

/-- The state-preparation dilation is precisely I tensor the supplied oracle,
written in sum coordinates. -/
def vectorDilation (U : Matrix.unitaryGroup B ℂ) : Matrix.unitaryGroup (B ⊕ B) ℂ :=
  sumUnitary U U

theorem vectorDilation_tensor (U : Matrix.unitaryGroup B ℂ) :
    vectorDilation U = rewireUnitary (GraphEncoding.sumBitWiring B)
      (HadamardClock.tensorUnitary (1 : Matrix.unitaryGroup Bool ℂ) U) := by
  apply Subtype.ext
  ext i j
  cases i <;> cases j <;>
    simp [vectorDilation,sumUnitary,rewireUnitary,GraphEncoding.sumBitWiring,
      HadamardClock.tensorUnitary,Matrix.one_apply]

def controlledVectorDilation (U : Matrix.unitaryGroup B ℂ) :
    Matrix.unitaryGroup ((Bool × Bool) × B) ℂ :=
  rewireUnitary (dilationLogicalWiring B).symm
    ((bitControlPort (B ⊕ B)).apply (vectorDilation U))

theorem controlledVectorDilation_basis (U : Matrix.unitaryGroup B ℂ)
    (e d : Bool) (i : B) :
    (controlledVectorDilation U).val *ᵥ Pi.single ((e,d),i) 1 =
      if e then ∑ j : B, U.val j i • (Pi.single ((e,d),j) 1 : ((Bool × Bool) × B) → ℂ)
      else Pi.single ((e,d),i) 1 := by
  ext ⟨⟨f,c⟩,j⟩
  cases e <;> cases d <;> cases f <;> cases c <;>
    simp [controlledVectorDilation,rewireUnitary,dilationLogicalWiring,
      GraphEncoding.sumBitWiring,bitControlPort_entries,vectorDilation,sumUnitary,
      Matrix.mulVec_single_one,Pi.single_apply]

/-- A single vector-oracle call reads only the external control bit; the
dilation bit and all scratch wires are untouched. -/
def vectorDilationCircuit (adj : Bool) : ElementaryCircuit A B DilationWire B :=
  [.vectorCall (GraphEncoding.singleFlagOraclePort B (.inl 0)) adj]

theorem vectorDilationCircuit_intertwines (adj : Bool)
    (U : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) :
    ((vectorDilationCircuit adj).toQuery.eval U Ub).val*basisInsertion dilationClean =
      basisInsertion dilationClean *(controlledVectorDilation (if adj then Ub⁻¹ else Ub)).val := by
  apply basisInsertion_intertwines
  rintro ⟨⟨e,d⟩,i⟩
  rw [controlledVectorDilation_basis,dilationClean_eq]
  simp only [vectorDilationCircuit,ElementaryCircuit.toQuery,List.map_cons,List.map_nil,
    ElementaryInstruction.toQuery,QueryCircuit.eval,QueryInstruction.eval,one_mul]
  rw [GraphEncoding.singleFlagOracle_basis]
  cases e <;>
    simp [Matrix.mulVec_sum,Matrix.mulVec_smul,basisInsertion_basis,
      singleFlag_basisInsertion_col,dilationClean_eq]

theorem vectorDilation_inv (U : Matrix.unitaryGroup B ℂ) :
    vectorDilation U⁻¹ = (vectorDilation U)⁻¹ := by
  apply Subtype.ext
  simp [vectorDilation,sumUnitary,Matrix.star_eq_conjTranspose,Matrix.fromBlocks_conjTranspose]

theorem vectorDilationCircuit_sum_intertwines (adj : Bool)
    (U : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) :
    ((vectorDilationCircuit adj).toQuery.eval U Ub).val*basisInsertion dilationSumClean =
      basisInsertion dilationSumClean *
        ((bitControlPort (B ⊕ B)).apply
          (if adj then (vectorDilation Ub)⁻¹ else vectorDilation Ub)).val := by
  have h := clean_intertwines_transport (Equiv.refl (DilationSpace B))
    (dilationLogicalWiring B) dilationClean
    ((vectorDilationCircuit adj).toQuery.eval U Ub)
    (controlledVectorDilation (if adj then Ub⁻¹ else Ub))
    (vectorDilationCircuit_intertwines adj U Ub)
  have he : rewireUnitary (dilationLogicalWiring B)
      (controlledVectorDilation (if adj then Ub⁻¹ else Ub)) =
      (bitControlPort (B ⊕ B)).apply
        (if adj then (vectorDilation Ub)⁻¹ else vectorDilation Ub) := by
    apply Subtype.ext
    ext i j
    cases adj <;> simp [controlledVectorDilation,rewireUnitary,vectorDilation_inv]
  rw [he] at h
  exact h

theorem vectorDilationCircuit_counts (adj : Bool) :
    (vectorDilationCircuit (A := A) (B := B) adj).toQuery.matrixQueries=0 ∧
      (vectorDilationCircuit (A := A) (B := B) adj).toQuery.vectorQueries=1 ∧
      (vectorDilationCircuit (A := A) (B := B) adj).workGates=0 := by
  exact ⟨rfl,rfl,rfl⟩

theorem vectorDilationCircuit_single_flag (adj : Bool)
    (p : QueryPort B (DilationSpace B)) (b : Bool)
    (h : ElementaryInstruction.vectorCall p b ∈ vectorDilationCircuit (A := A) adj) :
    p=GraphEncoding.singleFlagOraclePort B (.inl 0) ∧ b=adj := by
  simpa [vectorDilationCircuit] using h

theorem dilationClean_injective : Function.Injective (dilationClean (A := A)) := by
  intro x y h
  have hh := congrArg (oracleLocalWiring A) h
  simpa [dilationClean,oracleLocalClean] using hh

theorem dilationSumClean_injective : Function.Injective (dilationSumClean (A := A)) :=
  dilationClean_injective.comp (dilationLogicalWiring A).symm.injective

/-- The clean implementation is an isometric embedding of the entire logical
oracle workspace, not a promise about one prepared state. -/
theorem dilationSumClean_isometry :
    (basisInsertion (dilationSumClean (A := A)))ᴴ*
      basisInsertion (dilationSumClean (A := A))=1 :=
  basisInsertion_isometry _ (dilationSumClean_injective (A := A))

theorem active_control_intertwines {P Q : Type*} [Fintype P] [DecidableEq P]
    [Fintype Q] [DecidableEq Q] (U : Matrix.unitaryGroup P ℂ)
    (V : Matrix.unitaryGroup Q ℂ) (f : Bool × Q → P)
    (h : U.val*basisInsertion f=basisInsertion f*((bitControlPort Q).apply V).val) :
    U.val*basisInsertion (fun x => f (true,x))=
      basisInsertion (fun x => f (true,x))*V.val := by
  ext p j
  have hh := congrFun (congrFun h p) (true,j)
  simpa [Matrix.mul_apply,basisInsertion,Fintype.sum_prod_type,bitControlPort_entries] using hh

/-- Fixing the external control to one implements an ordinary dilation query. -/
theorem dilationOracleCircuit_uncontrolled_intertwines (adj : Bool)
    (U : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) :
    ((dilationOracleCircuit adj).toQuery.eval U Ub).val *
        basisInsertion (fun x => dilationSumClean (true,x)) =
      basisInsertion (fun x => dilationSumClean (true,x)) *
        (if adj then (LowerBounds.hermitianUnitaryDilation U)⁻¹
          else LowerBounds.hermitianUnitaryDilation U).val :=
  active_control_intertwines _ _ _ (dilationOracleCircuit_sum_intertwines adj U Ub)

theorem vectorDilationCircuit_uncontrolled_intertwines (adj : Bool)
    (U : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) :
    ((vectorDilationCircuit adj).toQuery.eval U Ub).val *
        basisInsertion (fun x => dilationSumClean (true,x)) =
      basisInsertion (fun x => dilationSumClean (true,x)) *
        (if adj then (vectorDilation Ub)⁻¹ else vectorDilation Ub).val :=
  active_control_intertwines _ _ _ (vectorDilationCircuit_sum_intertwines adj U Ub)

end OptimalQLS.Reduction
