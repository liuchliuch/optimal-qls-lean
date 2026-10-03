import OptimalQLS.Refinement.PhysicalProgram.Selection

/-! # Actual single-bit control readout for every oracle in the complete run -/
noncomputable section
set_option synthInstance.maxSize 16384
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
open scoped Classical
namespace OptimalQLS.Refinement.PhysicalProgram
open Matrix Preparation TransducerCompiler BinaryClock PolynomialTransform

/-- Exactly the three distinct signal-flag wires used by the three procedures. -/
inductive Flag where
  | preparation | filter | correction

def flagValue (a n ℓ : ℕ) : Flag → Register a n ℓ → Bool
  | .preparation, x => x.2.1.2.2.1
  | .filter, x => x.2.2.1.2 (PolynomialTransform.flagWire (a+4))
  | .correction, x => x.1.2 (PolynomialTransform.flagWire a)

def ReadsFlag {A P : Type*} (p : QueryPort A P) (f : P→Bool) : Prop :=
  ∀ i k, p.control k=f (p.wiring (i,k))

theorem readsFlag_lift {A Q P : Type*} [Fintype A] [DecidableEq A]
    [Fintype Q] [DecidableEq Q] [Fintype P] [DecidableEq P] (p : QueryPort Q P) (q : QueryPort A Q)
    (f : Q→Bool) (g : P→Bool) (hp : ∀ k,p.control k=true)
    (hw : ∀ i k,g (p.wiring (i,k))=f i) (hq : ReadsFlag q f) :
    ReadsFlag (p.comp q) g := by
  intro i k
  obtain ⟨⟨u,v⟩,rfl⟩ := (finProdFinEquiv (m := q.multiplicity) (n := p.multiplicity)).surjective k
  have hc : (p.comp q).control (finProdFinEquiv (u,v))=q.control u := by
    simp only [QueryPort.comp,Equiv.symm_apply_apply,hp,Bool.and_true]
  rw [hc,QueryPort.comp_wiring p q i u v,hw]
  exact hq i u

def preparationMatrixPort (a n ℓ : ℕ) : QueryPort (Bits a × Bits n) (Register a n ℓ) :=
  (preparationPort a n ℓ).comp (CompilerAttachment.graphSingleFlagPort a n ℓ)
def preparationVectorPort (a n ℓ : ℕ) : QueryPort (Bits n) (Register a n ℓ) :=
  (preparationPort a n ℓ).comp (CompilerAttachment.sourceSingleFlagPort a n ℓ)
def filterMatrixPort (a n ℓ : ℕ) : QueryPort (Bits a × Bits n) (Register a n ℓ) :=
  filterPort.comp (graphOriginalSingleFlagPort a (Bits n))
def correctionMatrixPort (a n ℓ : ℕ) : QueryPort (Bits a × Bits n) (Register a n ℓ) :=
  correctionPort.comp (originalSingleFlagPort a (Bits n))

theorem preparationMatrixPort_reads (a n ℓ : ℕ) :
    ReadsFlag (preparationMatrixPort a n ℓ) (flagValue a n ℓ .preparation) := by
  apply readsFlag_lift _ _ (fun x=>x.2.2.1) _ (fun _=>rfl) (fun _ _=>rfl)
  exact CompilerAttachment.graphSingleFlagPort_reads_flag a n ℓ

theorem preparationVectorPort_reads (a n ℓ : ℕ) :
    ReadsFlag (preparationVectorPort a n ℓ) (flagValue a n ℓ .preparation) := by
  apply readsFlag_lift _ _ (fun x=>x.2.2.1) _ (fun _=>rfl) (fun _ _=>rfl)
  exact CompilerAttachment.sourceSingleFlagPort_reads_flag a n ℓ

theorem graphOriginalSingleFlagPort_reads (a n : ℕ) :
    ReadsFlag (graphOriginalSingleFlagPort a (Bits n))
      (fun x=>x.1.2 (PolynomialTransform.flagWire (a+4))) := by
  intro i k
  simp only [graphOriginalSingleFlagPort,QueryPort.comp,relabelPort,
    GraphEncoding.singleFlagOraclePort,Equiv.trans_apply,Equiv.prodCongr_apply,
    Equiv.refl_apply,Equiv.prodComm_apply,Prod.map_apply,Prod.swap,Bool.and_true,
    Equiv.prodAssoc_symm_apply,Equiv.prodAssoc_apply,graphAttachWiring,graphLocalWiring,
    maskedPhysicalWiring,physicalEquiv,physicalSignalEquiv,PolynomialTransform.flagWire]
  rfl

theorem originalSingleFlagPort_reads (a n : ℕ) :
    ReadsFlag (originalSingleFlagPort a (Bits n))
      (fun x=>x.1.2 (PolynomialTransform.flagWire a)) := by
  intro i k
  simp only [originalSingleFlagPort,QueryPort.comp,relabelPort,
    GraphEncoding.singleFlagOraclePort,Equiv.trans_apply,Equiv.prodCongr_apply,
    Equiv.refl_apply,Equiv.prodComm_apply,Prod.map_apply,Prod.swap,Bool.and_true,
    Equiv.prodAssoc_symm_apply,Equiv.prodAssoc_apply,oracleAttachWiring,oracleLocalWiring,
    maskedPhysicalWiring,physicalEquiv,physicalSignalEquiv,PolynomialTransform.flagWire]
  rfl

theorem filterMatrixPort_reads (a n ℓ : ℕ) :
    ReadsFlag (filterMatrixPort a n ℓ) (flagValue a n ℓ .filter) := by
  apply readsFlag_lift _ _ (fun x=>x.1.2 (PolynomialTransform.flagWire (a+4))) _ (fun _=>rfl) (fun _ _=>rfl)
  exact graphOriginalSingleFlagPort_reads a n

theorem correctionMatrixPort_reads (a n ℓ : ℕ) :
    ReadsFlag (correctionMatrixPort a n ℓ) (flagValue a n ℓ .correction) := by
  apply readsFlag_lift _ _ (fun x=>x.1.2 (PolynomialTransform.flagWire a)) _ (fun _=>rfl) (fun _ _=>rfl)
  exact originalSingleFlagPort_reads a n

theorem program_matrix_ports (a n ℓ : ℕ)
    (cp : CompilerAttachment.Circuit a n ℓ) (hps : CompilerAttachment.strictCircuit cp)
    (cf : GraphAttachedCircuit a (Bits n) (Bits n))
    (hfs : cf.CallsOnly (graphOriginalSingleFlagPort a (Bits n)))
    (cc : SingleFlagCircuit a (Bits n) (Bits n))
    (hcs : cc.CallsOnly (originalSingleFlagPort a (Bits n)))
    (p : QueryPort (Bits a × Bits n) (Register a n ℓ)) (adj : Bool)
    (hp : NamedInstruction.matrixCall p adj∈program a n ℓ cp cf cc) :
    p=preparationMatrixPort a n ℓ ∨ p=filterMatrixPort a n ℓ ∨ p=correctionMatrixPort a n ℓ := by
  rcases List.mem_append.mp hp with hp|hp
  · rcases List.mem_append.mp hp with hp|hp
    · obtain ⟨i,hi,hEq⟩ := List.mem_map.mp hp
      cases i with
      | gate g => cases hEq
      | matrixCall q b =>
        cases hEq
        left
        rw [(CompilerAttachment.strictCircuit_ports cp hps).1 q adj hi]
        rfl
      | vectorCall q b => cases hEq
    · obtain ⟨i,hi,hEq⟩ := List.mem_map.mp hp
      cases i with
      | gate g => cases hEq
      | matrixCall q b =>
        cases hEq
        right; left
        rw [hfs q adj hi]
        rfl
      | vectorCall q b => cases hEq
  · obtain ⟨i,hi,hEq⟩ := List.mem_map.mp hp
    cases i with
    | gate g => cases hEq
    | matrixCall q b =>
      cases hEq
      right; right
      rw [hcs q adj hi]
      rfl
    | vectorCall q b => cases hEq

theorem program_vector_ports (a n ℓ : ℕ)
    (cp : CompilerAttachment.Circuit a n ℓ) (hps : CompilerAttachment.strictCircuit cp)
    (cf : GraphAttachedCircuit a (Bits n) (Bits n))
    (hfv : (cf.toQuery (GraphAttachedGate.eval a)).vectorQueries=0)
    (cc : SingleFlagCircuit a (Bits n) (Bits n))
    (hcv : (cc.toQuery (SingleFlagGate.eval a)).vectorQueries=0)
    (p : QueryPort (Bits n) (Register a n ℓ)) (adj : Bool)
    (hp : NamedInstruction.vectorCall p adj∈program a n ℓ cp cf cc) :
    p=preparationVectorPort a n ℓ := by
  rcases List.mem_append.mp hp with hp|hp
  · rcases List.mem_append.mp hp with hp|hp
    · obtain ⟨i,hi,hEq⟩ := List.mem_map.mp hp
      cases i with
      | gate g => cases hEq
      | matrixCall q b => cases hEq
      | vectorCall q b =>
        cases hEq
        rw [(CompilerAttachment.strictCircuit_ports cp hps).2.1 q adj hi]
        rfl
    · obtain ⟨i,hi,hEq⟩ := List.mem_map.mp hp
      cases i with
      | gate g => cases hEq
      | matrixCall q b => cases hEq
      | vectorCall q b => exact False.elim (CompilerAttachment.named_no_vector _ cf hfv q b hi)
  · obtain ⟨i,hi,hEq⟩ := List.mem_map.mp hp
    cases i with
    | gate g => cases hEq
    | matrixCall q b => cases hEq
    | vectorCall q b => exact False.elim (CompilerAttachment.named_no_vector _ cc hcv q b hi)

/-- Locality is a property of the actual port control functions and actual leaves. -/
def SingleControlled {a n ℓ : ℕ} (c : Circuit a n ℓ) : Prop :=
  (∀ p adj,NamedInstruction.matrixCall p adj∈c → ∃ f : Flag,ReadsFlag p (flagValue a n ℓ f)) ∧
  (∀ p adj,NamedInstruction.vectorCall p adj∈c → ReadsFlag p (flagValue a n ℓ .preparation))

theorem program_single_controlled (a n ℓ : ℕ)
    (cp : CompilerAttachment.Circuit a n ℓ) (hps : CompilerAttachment.strictCircuit cp)
    (cf : GraphAttachedCircuit a (Bits n) (Bits n))
    (hfs : cf.CallsOnly (graphOriginalSingleFlagPort a (Bits n)))
    (hfv : (cf.toQuery (GraphAttachedGate.eval a)).vectorQueries=0)
    (cc : SingleFlagCircuit a (Bits n) (Bits n))
    (hcs : cc.CallsOnly (originalSingleFlagPort a (Bits n)))
    (hcv : (cc.toQuery (SingleFlagGate.eval a)).vectorQueries=0) :
    SingleControlled (program a n ℓ cp cf cc) := by
  constructor
  · intro p adj hp
    rcases program_matrix_ports a n ℓ cp hps cf hfs cc hcs p adj hp with h|h|h
    · subst p; exact ⟨.preparation,preparationMatrixPort_reads a n ℓ⟩
    · subst p; exact ⟨.filter,filterMatrixPort_reads a n ℓ⟩
    · subst p; exact ⟨.correction,correctionMatrixPort_reads a n ℓ⟩
  · intro p adj hp
    rw [program_vector_ports a n ℓ cp hps cf hfv cc hcv p adj hp]
    exact preparationVectorPort_reads a n ℓ

end OptimalQLS.Refinement.PhysicalProgram
