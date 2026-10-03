import OptimalQLS.KernelReflectionPhysical.Locality
import OptimalQLS.Preparation.CompilerAttachment.ListAssembly

/-! # The complete oracle-applied kernel-reflection transducer -/
noncomputable section
namespace OptimalQLS.KernelReflectionPhysical
open Matrix TransducerCompiler BinaryClock PolynomialTransform DirtyAncilla
open Preparation Preparation.WorkGates Refinement.CostedExecution
set_option maxHeartbeats 250000
set_option maxRecDepth 4096
set_option synthInstance.maxSize 16384
set_option linter.unusedSectionVars false

abbrev Gate (a : ℕ) := PhaseGate OracleLocalWire ⊕ PhaseGate (Wire (LogicalWire a))

def gateEval {D : Type*} [Fintype D] [DecidableEq D] (a : ℕ) :
    Gate a → Matrix.unitaryGroup (Physical a D) ℂ
  | .inl g => queryGateEval a g
  | .inr g => elementaryPlacement g.eval

variable {D B : Type*} [Fintype D] [DecidableEq D] [Fintype B] [DecidableEq B]

def workMacro (a : ℕ) (code : List (PhaseGate (Wire (LogicalWire a)))) :
    NamedCircuit (Gate a) (Bits a × D) B (Physical a D) :=
  code.map (fun g => .gate (.inr g))


theorem workMacro_eval (a : ℕ) (code : List (PhaseGate (Wire (LogicalWire a))))
    (U : Matrix.unitaryGroup (Bits a × D) ℂ) (Ub : Matrix.unitaryGroup B ℂ) :
    ((workMacro a code).toQuery (gateEval a)).eval U Ub =
      elementaryPlacement (phaseEval code) := by
  induction code with
  | nil => simp [workMacro,NamedCircuit.toQuery,QueryCircuit.eval,phaseEval]
  | cons g c ih =>
    simp only [workMacro,List.map_cons,NamedCircuit.toQuery,NamedInstruction.toQuery,
      QueryCircuit.eval,QueryInstruction.eval,phaseEval,map_mul]
    exact congrArg (fun W => W * elementaryPlacement g.eval) ih


theorem workMacro_counts (a : ℕ) (code : List (PhaseGate (Wire (LogicalWire a)))) :
    ((workMacro (D := D) (B := B) a code).toQuery (gateEval a)).matrixQueries=0 ∧
      ((workMacro (D := D) (B := B) a code).toQuery (gateEval a)).vectorQueries=0 ∧
      (workMacro (D := D) (B := B) a code).workGates=code.length := by
  induction code with
  | nil => exact ⟨rfl,rfl,rfl⟩
  | cons g c ih => exact ⟨ih.1,ih.2.1,congrArg Nat.succ ih.2.2⟩

/-- Compute the label predicate, query full UH once, uncompute, then four work factors. -/
def transducerProgram (a : ℕ) {μ : ℝ} (hμ : 0<μ) :
    NamedCircuit (Gate a) (Bits a × D) B (Physical a D) :=
  Preparation.CompilerAttachment.mapNamed Sum.inl (queryProgram a) ++
    workMacro a (workProgram a hμ false)

def sourceTransducer {a : ℕ} {μ : ℝ} (hμ : 0<μ)
    (U : Matrix.unitaryGroup (Bits a × D) ℂ) : Matrix.unitaryGroup (Source a D) ℂ :=
  sourceWork hμ false * sourceQuery U


theorem transducerProgram_eval (a : ℕ) {μ : ℝ} (hμ : 0<μ)
    (U : Matrix.unitaryGroup (Bits a × D) ℂ) (Ub : Matrix.unitaryGroup B ℂ) :
    ((transducerProgram a hμ).toQuery (gateEval a)).eval U Ub =
      physicalWork hμ false * (((queryProgram a).toQuery (queryGateEval a)).eval U Ub) := by
  rw [transducerProgram,NamedCircuit.toQuery_append,QueryCircuit.eval_append,
    Preparation.CompilerAttachment.mapNamed_toQuery Sum.inl (queryGateEval a)
      (gateEval a) (fun _=>rfl),workMacro_eval]
  rfl

/-- Exact full-column correctness, including unused labels and off-signal columns. -/

theorem transducerProgram_intertwines (a : ℕ) {μ : ℝ} (hμ : 0<μ)
    (U : Matrix.unitaryGroup (Bits a × D) ℂ) (Ub : Matrix.unitaryGroup B ℂ) :
    (((transducerProgram a hμ).toQuery (gateEval a)).eval U Ub).val *
        basisInsertion (sourceInsertion false) =
      basisInsertion (sourceInsertion false) * (sourceTransducer hμ U).val := by
  rw [transducerProgram_eval]
  exact intertwines_mul _ _ _ _ _ (queryProgram_intertwines a U Ub)
    (workProgram_intertwines hμ false false)


theorem transducerProgram_counts (a : ℕ) {μ : ℝ} (hμ : 0<μ) :
    ((transducerProgram (D := D) (B := B) a hμ).toQuery (gateEval a)).matrixQueries=1 ∧
      ((transducerProgram (D := D) (B := B) a hμ).toQuery (gateEval a)).vectorQueries=0 ∧
      (transducerProgram (D := D) (B := B) a hμ).workGates ≤ 18620*(a+1) := by
  have hq := queryProgram_counts (D := D) (B := B) a
  have hw := workMacro_counts (D := D) (B := B) a (workProgram a hμ false)
  have hl := workProgram_length a hμ false
  simp only [transducerProgram,NamedCircuit.toQuery_append,
    Preparation.CompilerAttachment.mapNamed_toQuery Sum.inl (queryGateEval a)
      (gateEval a) (fun _=>rfl),QueryCircuit.matrixQueries_append,QueryCircuit.vectorQueries_append,
    NamedCircuit.workGates_append,Preparation.CompilerAttachment.mapNamed_workGates,
    hq.1,hq.2.1,hw.1,hw.2.1,hw.2.2,add_zero]
  exact ⟨True.intro,True.intro,by omega⟩


theorem transducerProgram_single_flag (a : ℕ) {μ : ℝ} (hμ : 0<μ)
    (p : QueryPort (Bits a × D) (Physical a D)) (adj : Bool)
    (hp : NamedInstruction.matrixCall p adj ∈ transducerProgram (B := B) a hμ) :
    p=singleFlagPort a ∧ adj=false := by
  rcases List.mem_append.mp hp with hp|hp
  · obtain ⟨i,hi,hEq⟩ := List.mem_map.mp hp
    cases i with
    | gate g => cases hEq
    | matrixCall q b => cases hEq; exact queryProgram_single_flag a _ _ hi
    | vectorCall q b => cases hEq
  · simp [workMacro] at hp

/-- Select one external-control sector without duplicating or rescaling any norm. -/
def sourceLift {a : ℕ} (c : Bool) (v : Fin 8 × (Bits a × D) → ℂ) : Source a D → ℂ :=
  fun x => if x.2=c then v x.1 else 0

def sourceState {a : ℕ} (c : Bool) (ξ ω₁ ω₂ : Bits a × D → ℂ) : Source a D → ℂ :=
  sourceLift c (bundle8 0 ξ ω₁ ω₂ 0)


theorem sourceQuery_state {a : ℕ} (U : Matrix.unitaryGroup (Bits a × D) ℂ)
    (c : Bool) (ξ ω₁ ω₂ : Bits a × D → ℂ) :
    (sourceQuery U).val *ᵥ sourceState c ξ ω₁ ω₂ =
      sourceState c ξ (U.val *ᵥ ω₁) (U.val *ᵥ ω₂) := by
  funext ⟨⟨j,x⟩,d⟩
  rw [sourceQuery_apply]
  by_cases hd : d=c
  · fin_cases j <;> simp [sourceState,sourceLift,bundle8,hd]
  · simp [sourceState,sourceLift,hd,Matrix.mulVec,dotProduct]


theorem sourceWork_lift {a : ℕ} {μ : ℝ} (hμ : 0<μ) (c : Bool)
    (v : Fin 8 × (Bits a × D) → ℂ) :
    (sourceWork hμ false).val *ᵥ sourceLift c v =
      sourceLift c ((kernelWork8 (signalProjector (D := D) (fun _ : Fin a=>false))
        (signalProjector_star _) (signalProjector_idempotent _) hμ).val *ᵥ v) := by
  funext ⟨i,d⟩
  change ((controlledOn _ _).val *ᵥ _) (i,d)=_
  rw [controlledOn_apply]
  by_cases hd : d=c
  · simp [sourceLift,hd]
  · simp [sourceLift,hd,Matrix.mulVec,dotProduct]

/-- Exact catalytic restoration by the concrete padded source transducer. -/

theorem sourceTransducer_restoration {a : ℕ} (U : Matrix.unitaryGroup (Bits a × D) ℂ)
    (hU : star (U.val) = U.val) (H : Matrix D D ℂ) (hH : star H=H)
    {α τ : ℝ} (hα : 0<α) (hτ : 0<τ)
    (hblock : H=α • signalBlock (fun _ : Fin a=>false) U) (ξ : D→ℂ) (c : Bool) :
    let p := signalInjection (fun _ : Fin a=>false) *ᵥ (matrixKernelProjection H *ᵥ ξ)
    let z := signalInjection (fun _ : Fin a=>false) *ᵥ (matrixPseudoInverse H hH *ᵥ ξ)
    (sourceTransducer (mul_pos hα hτ) U).val *ᵥ
      sourceState c (signalInjection (fun _ : Fin a=>false) *ᵥ ξ)
        (kernelCatalystOne U (α*τ) α p z) (kernelCatalystTwo U (α*τ) α p z) =
      sourceState c ((2:ℝ) • p - signalInjection (fun _ : Fin a=>false) *ᵥ ξ)
        (kernelCatalystOne U (α*τ) α p z) (kernelCatalystTwo U (α*τ) α p z) := by
  dsimp only
  have hUU : U.val*U.val=1 := by simpa only [hU] using U.property.1
  obtain ⟨hp,hz⟩ := kernel_compression_from_encoding (fun _ : Fin a=>false) U H
    (matrixKernelProjection H) (matrixPseudoInverse H hH) hα.ne' hblock
    (matrix_mul_kernel H) (matrix_mul_pseudoInverse H hH) ξ
  simp only [sourceTransducer,Submonoid.coe_mul,← Matrix.mulVec_mulVec,sourceQuery_state]
  simp only [sourceState]
  rw [sourceWork_lift]
  apply congrArg (sourceLift c)
  exact kernelWork8_restoration
    (signalProjector (D := D) (fun _ : Fin a=>false)) U.val
    (signalProjector_star (D := D) (fun _ : Fin a=>false))
    (signalProjector_idempotent (D := D) (fun _ : Fin a=>false)) hUU
    (μ := α*τ) (α := α) (mul_pos hα hτ) hα.ne'
    (0 : Bits a × D → ℂ)
    (signalInjection (fun _ : Fin a=>false) *ᵥ ξ)
    (signalInjection (fun _ : Fin a=>false) *ᵥ (matrixKernelProjection H *ᵥ ξ))
    (signalInjection (fun _ : Fin a=>false) *ᵥ (matrixPseudoInverse H hH *ᵥ ξ))
    (0 : Bits a × D → ℂ)
    (signalProjector_injection (fun _ : Fin a=>false) ξ)
    (signalProjector_injection (fun _ : Fin a=>false) (matrixKernelProjection H *ᵥ ξ))
    (signalProjector_injection (fun _ : Fin a=>false) (matrixPseudoInverse H hH *ᵥ ξ)) hp hz


end OptimalQLS.KernelReflectionPhysical
