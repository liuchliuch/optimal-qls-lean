import OptimalQLS.Refinement.CostedExecution.AdapterLocalityFrames

/-! # Locality and actual single-bit controls of the general-input adapter -/
noncomputable section
namespace OptimalQLS.Refinement.CostedExecution
open Matrix Preparation TransducerCompiler BinaryClock PolynomialTransform DirtyAncilla
open PhysicalProgram PhysicalMeasurement
open Reduction PhysicalAdapter
open scoped Classical
set_option synthInstance.maxSize 32768
set_option maxHeartbeats 1000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false

/-- Fixed wire renaming transports locality without inserting any operation. -/
theorem IsTwoLocal.wire_equiv {P W V : Type} [Fintype P] [DecidableEq P]
    {c : P → W → Bool} {d : P → V → Bool} {U : Matrix.unitaryGroup P ℂ}
    (e : W ≃ V) (he : ∀ x i, d x (e i)=c x i) (hU : IsTwoLocal c U) :
    IsTwoLocal d U := by
  cases hU with
  | tensor hS q f hf M =>
    refine .tensor hS q f ?_ M
    refine ⟨hf.wire.trans e.toEmbedding,?_,?_⟩
    · intro x r i
      rw [show (hf.wire.trans e.toEmbedding) i=e (hf.wire i) from rfl,he]
      exact hf.read x r i
    · intro x y r j hj
      obtain ⟨j,rfl⟩ := e.surjective j
      rw [he,he]
      apply hf.outside x y r j
      intro i hi
      exact hj i (congrArg e hi)

/-- The old leaves retain the normalized locality proof, while every adapter
leaf is placed on the old flag, literal data head, and distinct fresh scratch. -/
theorem adapter_gate_local (a n ℓ : ℕ) (hℓ : 0<ℓ) (g : PhysicalAdapter.Gate a n ℓ) :
    IsTwoLocal (adapterCoordinates a n ℓ) (PhysicalAdapter.gateEval a n ℓ hℓ g) := by
  cases g with
  | old g =>
    change IsTwoLocal _ ((scratchPort (Equiv.refl _)).apply
      (PhysicalProgram.gateEval a (n+1) ℓ hℓ g))
    rw [scratchPort_apply]
    exact IsTwoLocal.place _ (oldRegisterEmbedding a n ℓ) _ (physical_gate_local a (n+1) ℓ hℓ g)
  | matrix f g =>
    change IsTwoLocal _ (GateSynthesis.placeHom (matrixWiring a n ℓ f)
      (GateSynthesis.placeHom (Equiv.refl _) g.eval))
    rw [placeHom_comp]
    exact IsTwoLocal.place _ (adapterMatrixEmbedding a n ℓ f) _ (phase_leaf_local g)
  | vector g =>
    change IsTwoLocal _ (GateSynthesis.placeHom (vectorWiring a n ℓ)
      (GateSynthesis.placeHom (Equiv.refl _) g.eval))
    rw [placeHom_comp]
    exact IsTwoLocal.place _ (adapterVectorEmbedding a n ℓ) _ (phase_leaf_local g)

def adapterMatrixControl (a n ℓ : ℕ) : AdapterWire a n ℓ := .inr (.inr (.inl ()))
def adapterVectorControl (a n ℓ : ℕ) : AdapterWire a n ℓ :=
  .inl (controlWire a (n+1) ℓ .preparation)

theorem originalMatrixPort_reads_adapter_coordinate (a n ℓ : ℕ) (f : PhysicalProgram.Flag) :
    PhysicalProgram.ReadsFlag (originalMatrixPort a n ℓ f)
      (fun x=>adapterCoordinates a n ℓ x (adapterMatrixControl a n ℓ)) := by
  intro i k
  exact (originalMatrixPort_reads a n ℓ f i k).trans (matrixFlag_shared a n ℓ f _)

theorem vectorFlag_is_adapter_coordinate (a n ℓ : ℕ) (x : PhysicalAdapter.Space a n ℓ) :
    vectorFlag a n ℓ x=adapterCoordinates a n ℓ x (adapterVectorControl a n ℓ) := by
  obtain ⟨⟨x,⟨d,r⟩⟩,rfl⟩ := (adapterVectorFrame a n ℓ).surjective x
  change ((vectorWiring a n ℓ).symm ((vectorWiring a n ℓ) ((x,d),r))).1.1.2 (.inl 0) = _
  rw [Equiv.symm_apply_apply]
  exact ((adapterVectorEmbedding a n ℓ).read x (d,r) (.inr (.inl 0))).symm

theorem originalVectorPort_reads_adapter_coordinate (a n ℓ : ℕ) :
    PhysicalProgram.ReadsFlag (originalVectorPort a n ℓ)
      (fun x=>adapterCoordinates a n ℓ x (adapterVectorControl a n ℓ)) := by
  intro i k
  exact (originalVectorPort_reads a n ℓ i k).trans (vectorFlag_is_adapter_coordinate a n ℓ _)

variable {a n : ℕ} {κ s ŝ ε : ℝ} {h : BudgetParameters κ s ŝ}

theorem adapted_gate_reads_actual_wires
    (I : PhysicalProgram.Implementation a (n+1) (ε := ε) h)
    (g : PhysicalAdapter.Gate a n (preparationExponent κ))
    (_hg : NamedInstruction.gate g ∈ adapted I) :
    IsTwoLocal (adapterCoordinates a n (preparationExponent κ))
      (PhysicalAdapter.gateEval a n (preparationExponent κ)
        (CompilerAttachment.preparationExponent_pos h) g) :=
  adapter_gate_local a n _ _ g

theorem adapted_matrixCall_reads_coordinate
    (I : PhysicalProgram.Implementation a (n+1) (ε := ε) h)
    (p : QueryPort (Bits a × Bits n) (PhysicalAdapter.Space a n (preparationExponent κ)))
    (adj : Bool) (hp : NamedInstruction.matrixCall p adj ∈ adapted I) :
    PhysicalProgram.ReadsFlag p (fun x=>adapterCoordinates a n (preparationExponent κ) x
      (adapterMatrixControl a n (preparationExponent κ))) := by
  obtain ⟨f,rfl⟩ := (adapted_safe I).2.1 p adj hp
  exact originalMatrixPort_reads_adapter_coordinate a n _ f

theorem adapted_vectorCall_reads_coordinate
    (I : PhysicalProgram.Implementation a (n+1) (ε := ε) h)
    (p : QueryPort (Bits n) (PhysicalAdapter.Space a n (preparationExponent κ)))
    (adj : Bool) (hp : NamedInstruction.vectorCall p adj ∈ adapted I) :
    PhysicalProgram.ReadsFlag p (fun x=>adapterCoordinates a n (preparationExponent κ) x
      (adapterVectorControl a n (preparationExponent κ))) := by
  rw [(adapted_safe I).2.2 p adj hp]
  exact originalVectorPort_reads_adapter_coordinate a n _

end OptimalQLS.Refinement.CostedExecution
