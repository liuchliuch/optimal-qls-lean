import OptimalQLS.Preparation.CompilerAttachment.GlobalSafety
import OptimalQLS.Preparation.CompilerAttachment.GraphGates
import OptimalQLS.Preparation.CompilerAttachment.SourceGates

/-! # The physical original-oracle control is exactly the shared flag qubit -/
noncomputable section
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 700000
set_option linter.unusedSimpArgs false
open scoped Classical
namespace OptimalQLS.Preparation.CompilerAttachment
open Matrix TransducerCompiler BinaryClock PolynomialTransform DirtyAncilla

/-- Even after spectator attachment, the matrix primitive reads only the one
shared flag coordinate. No compiler-label or data predicate is built into it. -/
theorem graphSingleFlagPort_reads_flag (a n ℓ : ℕ) (i : Bits a × Bits n)
    (k : Fin (graphSingleFlagPort a n ℓ).multiplicity) :
    (graphSingleFlagPort a n ℓ).control k=
      ((graphSingleFlagPort a n ℓ).wiring (i,k)).2.2.1 := by
  obtain ⟨⟨u,v⟩,rfl⟩ := (finProdFinEquiv (m := Fintype.card (GateSynthesis.Space GraphLocalWire))
    (n := Fintype.card (CompilerRest ℓ))).surjective k
  dsimp only [graphSingleFlagPort]
  simp only [QueryPort.comp,Equiv.apply_symm_apply,scratchPort,GraphEncoding.singleFlagOraclePort,
    Equiv.trans_apply,Equiv.prodCongr_apply,Equiv.refl_apply,Equiv.prodComm_apply,
    Prod.map_apply,Prod.swap,Bool.and_true,Equiv.prodAssoc_symm_apply,Equiv.prodAssoc_apply,
    graphFrame,vectorFrame,graphLocalWiring,oracleLocalWiring,scratchFrame]
  rfl

/-- The vector primitive reads the very same physical flag coordinate, including
both Ub and Ub-dagger occurrences and the initial public-sector source call. -/
theorem sourceSingleFlagPort_reads_flag (a n ℓ : ℕ) (i : Bits n)
    (k : Fin (sourceSingleFlagPort a n ℓ).multiplicity) :
    (sourceSingleFlagPort a n ℓ).control k=
      ((sourceSingleFlagPort a n ℓ).wiring (i,k)).2.2.1 := by
  obtain ⟨⟨u,v⟩,rfl⟩ := (finProdFinEquiv (m := Fintype.card OracleLocalState)
    (n := Fintype.card (SourceRest a ℓ))).surjective k
  dsimp only [sourceSingleFlagPort]
  simp only [QueryPort.comp,Equiv.apply_symm_apply,scratchPort,GraphEncoding.singleFlagOraclePort,
    Equiv.trans_apply,Equiv.prodCongr_apply,Equiv.refl_apply,Equiv.prodComm_apply,
    Prod.map_apply,Prod.swap,Bool.and_true,Equiv.prodAssoc_symm_apply,Equiv.prodAssoc_apply,
    graphFrame,vectorFrame,graphLocalWiring,oracleLocalWiring,scratchFrame]
  rfl

/-- Every matrix call in a strict emitted list reads exactly one physical qubit. -/
theorem strictCircuit_matrix_reads_flag {a n ℓ : ℕ} (c : Circuit a n ℓ)
    (hc : strictCircuit c) (p : QueryPort (Bits a × Bits n) (Physical a n ℓ)) (adj : Bool)
    (hp : NamedInstruction.matrixCall p adj∈c) (i : Bits a × Bits n) (k : Fin p.multiplicity) :
    p.control k=(p.wiring (i,k)).2.2.1 := by
  have he := (strictCircuit_ports c hc).1 p adj hp
  subst p
  exact graphSingleFlagPort_reads_flag a n ℓ i k

/-- Every vector call reads the same qubit; neither labels nor data are free predicates. -/
theorem strictCircuit_vector_reads_flag {a n ℓ : ℕ} (c : Circuit a n ℓ)
    (hc : strictCircuit c) (p : QueryPort (Bits n) (Physical a n ℓ)) (adj : Bool)
    (hp : NamedInstruction.vectorCall p adj∈c) (i : Bits n) (k : Fin p.multiplicity) :
    p.control k=(p.wiring (i,k)).2.2.1 := by
  have he := (strictCircuit_ports c hc).2.1 p adj hp
  subst p
  exact sourceSingleFlagPort_reads_flag a n ℓ i k

end OptimalQLS.Preparation.CompilerAttachment
