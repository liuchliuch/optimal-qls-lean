import OptimalQLS.Refinement.CostedExecution.WorkLocalityFrame

/-! # Matrix-level locality of every actual full-run gate

These theorems use the emitted gate matrices, their actual tensor factors, and
verified physical wire placements. No arity tag is used as a premise. -/
noncomputable section
namespace OptimalQLS.Refinement.CostedExecution
open Matrix Preparation TransducerCompiler BinaryClock PolynomialTransform DirtyAncilla
open PhysicalProgram PhysicalMeasurement
open scoped Classical
set_option synthInstance.maxSize 16384
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

private theorem rewire_tensor {Q R P : Type} [Fintype Q] [DecidableEq Q]
    [Fintype R] [DecidableEq R] [Fintype P] [DecidableEq P]
    (e : Q × R ≃ P) (U : Matrix.unitaryGroup Q ℂ) :
    rewireUnitary e (GateSynthesis.placeHom (Equiv.refl _) U) = GateSynthesis.placeHom e U := by
  apply Subtype.ext
  rfl

/-- Every actual named work leaf is a ≤2-qubit tensor in the measurement chart. -/
theorem physical_gate_local (a n ℓ : ℕ) (hℓ : 0<ℓ) (g : PhysicalProgram.Gate a n ℓ) :
    IsTwoLocal (registerBits a n ℓ) (PhysicalProgram.gateEval a n ℓ hℓ g) := by
  cases g with
  | correction g =>
    cases g with
    | qsp g =>
      change IsTwoLocal _ (correctionPort.apply (elementaryPlacement g.eval))
      rw [correctionPort,namedPort_eval]
      change IsTwoLocal _ (GateSynthesis.placeHom correctionWiring
        (GateSynthesis.placeHom (Equiv.refl _) g.eval))
      rw [placeHom_comp]
      exact IsTwoLocal.place _ (correctionQspEmbedding a n ℓ) _ (phase_leaf_local g)
    | oracle g =>
      change IsTwoLocal _ (correctionPort.apply (rewireUnitary (oracleAttachWiring a (Bits n))
        (elementaryPlacement g.eval)))
      rw [correctionPort,namedPort_eval]
      change IsTwoLocal _ (GateSynthesis.placeHom correctionWiring
        (rewireUnitary (oracleAttachWiring a (Bits n)) (GateSynthesis.placeHom (Equiv.refl _) g.eval)))
      rw [rewire_tensor,placeHom_comp]
      exact IsTwoLocal.place _ (correctionOracleEmbedding a n ℓ) _ (phase_leaf_local g)
  | filter g =>
    cases g with
    | qsp g =>
      change IsTwoLocal _ (filterPort.apply (elementaryPlacement g.eval))
      rw [filterPort,namedPort_eval]
      change IsTwoLocal _ (GateSynthesis.placeHom filterWiring
        (GateSynthesis.placeHom (Equiv.refl _) g.eval))
      rw [placeHom_comp]
      exact IsTwoLocal.place _ (filterQspEmbedding a n ℓ) _ (phase_leaf_local g)
    | graph g =>
      change IsTwoLocal _ (filterPort.apply (rewireUnitary (graphAttachWiring a (Bits n))
        (elementaryPlacement g.eval)))
      rw [filterPort,namedPort_eval]
      change IsTwoLocal _ (GateSynthesis.placeHom filterWiring
        (rewireUnitary (graphAttachWiring a (Bits n)) (GateSynthesis.placeHom (Equiv.refl _) g.eval)))
      rw [rewire_tensor,placeHom_comp]
      exact IsTwoLocal.place _ (filterGraphEmbedding a n ℓ) _ (phase_leaf_local g)
  | preparation g =>
    change IsTwoLocal _ ((scratchPort (PhysicalProgram.preparationFrame a n ℓ)).apply
      (CompilerAttachment.gateEval a n ℓ hℓ g))
    rw [scratchPort_apply]
    cases g with
    | auxiliary g =>
      change IsTwoLocal _ (GateSynthesis.placeHom (PhysicalProgram.preparationFrame a n ℓ)
        (GateSynthesis.placeHom (CompilerAttachment.auxFrame a n ℓ) g.eval))
      rw [placeHom_comp]
      exact IsTwoLocal.place _ (preparationAuxEmbedding a n ℓ) _ (phase_leaf_local g)
    | graph g =>
      change IsTwoLocal _ (GateSynthesis.placeHom (PhysicalProgram.preparationFrame a n ℓ)
        (GateSynthesis.placeHom (CompilerAttachment.graphFrame a n ℓ)
          (GateSynthesis.placeHom (Equiv.refl _) g.eval)))
      rw [placeHom_comp,placeHom_comp]
      exact IsTwoLocal.place _ (preparationGraphEmbedding a n ℓ) _ (phase_leaf_local g)
    | source g =>
      cases g with
      | oracle g =>
        change IsTwoLocal _ (GateSynthesis.placeHom (PhysicalProgram.preparationFrame a n ℓ)
          (GateSynthesis.placeHom (CompilerAttachment.vectorFrame a n ℓ)
            (GateSynthesis.placeHom (Equiv.refl _) g.eval)))
        rw [placeHom_comp,placeHom_comp]
        exact IsTwoLocal.place _ (preparationOracleEmbedding a n ℓ) _ (phase_leaf_local g)
      | phase g =>
        change IsTwoLocal _ (GateSynthesis.placeHom (PhysicalProgram.preparationFrame a n ℓ)
          (GateSynthesis.placeHom (CompilerAttachment.reflectionFrame a n ℓ) g.eval))
        rw [placeHom_comp]
        exact IsTwoLocal.place _ (preparationReflectionEmbedding a n ℓ) _ (phase_leaf_local g)
    | work g =>
      cases ℓ with
      | zero => omega
      | succ ℓ =>
        change IsTwoLocal _ (GateSynthesis.placeHom (PhysicalProgram.preparationFrame a n (ℓ+1))
          (GateSynthesis.placeHom (CompilerAttachment.workFrame a n ℓ)
            (GateSynthesis.placeHom (Equiv.refl _) g.eval)))
        rw [placeHom_comp,placeHom_comp]
        exact IsTwoLocal.place _ (preparationWorkEmbedding a n ℓ) _ (phase_leaf_local g)

/-- Renaming the matrix indices leaves the physical bit chart unchanged. -/
theorem IsTwoLocal.reindex {P Q W : Type} [Fintype P] [DecidableEq P]
    [Fintype Q] [DecidableEq Q] {c : P → W → Bool} {U : Matrix.unitaryGroup P ℂ}
    (e : P ≃ Q) (hU : IsTwoLocal c U) :
    IsTwoLocal (fun x=>c (e.symm x)) (rewireUnitary e U) := by
  cases hU with
  | tensor hS q f hf V =>
    have hmat : rewireUnitary e (GateSynthesis.placeHom f V) =
        GateSynthesis.placeHom (f.trans e) V := by
      apply Subtype.ext
      rfl
    rw [hmat]
    refine .tensor hS q (f.trans e) ?_ V
    refine ⟨hf.wire,?_,?_⟩
    · intro x r i
      simpa using hf.read x r i
    · intro x y r j hj
      simpa using hf.outside x y r j hj

theorem physical_gate_finite_local (a n ℓ : ℕ) (hℓ : 0<ℓ) (g : PhysicalProgram.Gate a n ℓ) :
    IsTwoLocal (finiteRegisterCoordinates a n ℓ).symm
      (rewireUnitary (Fintype.equivFin (Register a n ℓ)) (PhysicalProgram.gateEval a n ℓ hℓ g)) :=
  (physical_gate_local a n ℓ hℓ g).reindex (Fintype.equivFin _)

variable {a n : ℕ} {κ s ŝ ε : ℝ} {h : BudgetParameters κ s ŝ}

/-- The locality theorem is attached to every actual emitted leaf of I.circuit. -/
theorem Implementation.gate_reads_actual_wires
    (I : PhysicalProgram.Implementation a n (ε := ε) h)
    (g : PhysicalProgram.Gate a n (preparationExponent κ))
    (_hg : NamedInstruction.gate g ∈ I.circuit) :
    IsTwoLocal (finiteRegisterCoordinates a n (preparationExponent κ)).symm
      (rewireUnitary (Fintype.equivFin (Register a n (preparationExponent κ)))
        (PhysicalProgram.gateEval a n (preparationExponent κ)
          (CompilerAttachment.preparationExponent_pos h) g)) :=
  physical_gate_finite_local a n _ _ g

end OptimalQLS.Refinement.CostedExecution
