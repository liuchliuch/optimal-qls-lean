import OptimalQLS.Reduction.GenericSolver.PhysicalComplete

/-! Plain calls use one shared initially-zero enable qubit, flipped once.
All supplied work acts identically on that qubit. The layouts contain literal
wire identities; the clean simulation and its cost are proved below. -/
noncomputable section
open scoped Classical
namespace OptimalQLS.Reduction.GenericSolver.Physical
open Matrix TransducerCompiler BinaryClock PolynomialTransform DirtyAncilla LowerBounds
open Refinement.CostedExecution Refinement.PhysicalMeasurement Preparation.CompilerAttachment
set_option synthInstance.maxSize 32768
set_option maxHeartbeats 800000
set_option maxRecDepth 8192
variable {P W : Type} [Fintype P] [DecidableEq P]
  {chart : P ≃ (W → Bool)} {a n : ℕ}

def enableCoordinates (chart : P ≃ (W → Bool)) : Bool × P ≃ ((Unit ⊕ W) → Bool) :=
  productBits boolCoordinates chart

def enabledFrame {Q R : Type} (f : Q × R ≃ P) : (Bool × Q) × R ≃ Bool × P where
  toFun x := (x.1.1,f (x.1.2,x.2))
  invFun x := ((x.1,(f.symm x.2).1),(f.symm x.2).2)
  left_inv x := by rcases x with ⟨⟨b,q⟩,r⟩; simp
  right_inv x := by rcases x with ⟨b,p⟩; simp

/-- The only extra layout information is where each literal wire of the
ordinary port lies after adding a fresh control wire. No unitary equation is an input. -/
structure PlainMatrixFrame (chart : P ≃ (W → Bool)) (a n : ℕ) where
  Rest : Type
  [finiteRest : Fintype Rest]
  [decidableRest : DecidableEq Rest]
  frame : (Bits a × (Bits n ⊕ Bits n)) × Rest ≃ P
  wires : WireEmbedding (matrixCoordinates a n) (coordinates (enableCoordinates chart))
    (matrixWiring a n (enabledFrame frame))
structure PlainVectorFrame (chart : P ≃ (W → Bool)) (n : ℕ) where
  Rest : Type
  [finiteRest : Fintype Rest]
  [decidableRest : DecidableEq Rest]
  frame : (Bits n ⊕ Bits n) × Rest ≃ P
  wires : WireEmbedding (vectorCoordinates n) (coordinates (enableCoordinates chart))
    (vectorWiring n (enabledFrame frame))
attribute [instance] PlainMatrixFrame.finiteRest PlainMatrixFrame.decidableRest
attribute [instance] PlainVectorFrame.finiteRest PlainVectorFrame.decidableRest

def PlainMatrixFrame.controlled (F : PlainMatrixFrame chart a n) :
    MatrixFrame (enableCoordinates chart) a n where
  Rest := F.Rest
  frame := enabledFrame F.frame
  wires := F.wires

def PlainVectorFrame.controlled (F : PlainVectorFrame chart n) :
    VectorFrame (enableCoordinates chart) n where
  Rest := F.Rest
  frame := enabledFrame F.frame
  wires := F.wires

def enabled {P : Type} (x : P) : Bool × P := (true,x)

theorem insertion_comp {D Q R : Type} [Fintype Q] [DecidableEq Q] [DecidableEq R]
    (f : Q → R) (g : D → Q) : basisInsertion f*basisInsertion g=basisInsertion (f ∘ g) := by
  ext i j
  simp [basisInsertion,Matrix.mul_apply]

theorem enabledFrame_apply {Q R : Type} [Fintype Q] [DecidableEq Q]
    [Fintype R] [DecidableEq R] (f : Q × R ≃ P) (U : Matrix.unitaryGroup Q ℂ) :
    GateSynthesis.placeHom (enabledFrame f) ((bitControlPort Q).apply U)=
      (bitControlPort P).apply (GateSynthesis.placeHom f U) := by
  apply Subtype.ext
  ext ⟨c,p⟩ ⟨d,q⟩
  obtain ⟨⟨x,r⟩,rfl⟩ := f.surjective p
  obtain ⟨⟨y,t⟩,rfl⟩ := f.surjective q
  change (GateSynthesis.placeHom (enabledFrame f) ((bitControlPort Q).apply U)).val
    ((enabledFrame f) ((c,x),r)) ((enabledFrame f) ((d,y),t)) = _
  rw [placeHom_entry,bitControlPort_entries,bitControlPort_entries,placeHom_entry]
  cases c <;> cases d <;> by_cases hr : r=t <;>
    simp [hr,f.injective.eq_iff,Prod.mk.injEq]

theorem enabledFrame_intertwines {Q R : Type} [Fintype Q] [DecidableEq Q]
    [Fintype R] [DecidableEq R] (f : Q × R ≃ P) (U : Matrix.unitaryGroup Q ℂ) :
    (GateSynthesis.placeHom (enabledFrame f) ((bitControlPort Q).apply U)).val *
      basisInsertion enabled = basisInsertion enabled * (GateSynthesis.placeHom f U).val := by
  rw [enabledFrame_apply]
  ext ⟨c,p⟩ q
  cases c <;> simp [Matrix.mul_apply,basisInsertion,Fintype.sum_prod_type,
    enabled,bitControlPort_entries]

theorem plainMatrix_intertwines (F : PlainMatrixFrame chart a n) (adj : Bool)
    (UA : Matrix.unitaryGroup (Bits a × Bits n) ℂ) (Ub : Matrix.unitaryGroup (Bits n) ℂ) :
    (((matrixCode F.controlled adj).toQuery gateEval).eval UA Ub).val *
      basisInsertion (fun x : P => clean (enabled x)) =
      basisInsertion (fun x : P => clean (enabled x)) *
        ((scratchPort F.frame).apply (if adj then (dilationEncoding UA)⁻¹ else dilationEncoding UA)).val := by
  have h₁ := matrixCode_intertwines F.controlled adj UA Ub
  have h₂ := enabledFrame_intertwines F.frame
    (if adj then (dilationEncoding UA)⁻¹ else dilationEncoding UA)
  rw [MatrixFrame.port_apply] at h₁
  simp only [PlainMatrixFrame.controlled] at h₁
  rw [scratchPort_apply]
  have hh := congrArg (fun M => M*basisInsertion (enabled (P := P))) h₁
  simp only [Matrix.mul_assoc] at hh
  rw [h₂] at hh
  have hc : basisInsertion (clean (P := Bool × P))*basisInsertion (enabled (P := P)) =
      basisInsertion (fun x : P => clean (enabled x)) := insertion_comp _ _
  rw [hc] at hh
  rw [←Matrix.mul_assoc,hc] at hh
  exact hh

theorem plainVector_intertwines (F : PlainVectorFrame chart n) (adj : Bool)
    (UA : Matrix.unitaryGroup (Bits a × Bits n) ℂ) (Ub : Matrix.unitaryGroup (Bits n) ℂ) :
    (((vectorCode F.controlled adj).toQuery gateEval).eval UA Ub).val *
      basisInsertion (fun x : P => clean (enabled x)) =
      basisInsertion (fun x : P => clean (enabled x)) *
        ((scratchPort F.frame).apply (if adj then (preparation Ub)⁻¹ else preparation Ub)).val := by
  have h₁ := vectorCode_intertwines F.controlled adj UA Ub
  have h₂ := enabledFrame_intertwines F.frame (if adj then (preparation Ub)⁻¹ else preparation Ub)
  rw [VectorFrame.port_apply] at h₁
  simp only [PlainVectorFrame.controlled] at h₁
  rw [scratchPort_apply]
  have hh := congrArg (fun M => M*basisInsertion (enabled (P := P))) h₁
  simp only [Matrix.mul_assoc] at hh
  rw [h₂] at hh
  have hc : basisInsertion (clean (P := Bool × P))*basisInsertion (enabled (P := P)) =
      basisInsertion (fun x : P => clean (enabled x)) := insertion_comp _ _
  rw [hc] at hh
  rw [←Matrix.mul_assoc,hc] at hh
  exact hh

end OptimalQLS.Reduction.GenericSolver.Physical
