import OptimalQLS.Preparation.CompilerAttachment.LocalAttach
import OptimalQLS.GraphEncoding.SingleFlagTheorem
import OptimalQLS.PolynomialTransform.GraphAttachmentWiring

/-! # Exact graph-call attachment on the compiler label and physical graph wires -/
noncomputable section
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 150000
set_option maxRecDepth 2048
set_option linter.unusedSimpArgs false
open scoped Classical
namespace OptimalQLS.Preparation.CompilerAttachment
open Matrix TransducerCompiler BinaryClock PolynomialTransform DirtyAncilla

/-- The two graph masks are the existing compiler-label bits, with no derived
predicate hidden in the interface to the original matrix oracle. -/
def graphFrame (a n ℓ : ℕ) :
    (GraphLocalState × (Bits a × Bits n)) × CompilerRest ℓ ≃ Physical a n ℓ :=
  (Equiv.prodCongr (graphLocalWiring (Bits a) (Bits n)) (Equiv.refl (CompilerRest ℓ))).trans
    (scratchFrame (labelDataFrame a n ℓ))

theorem graphFrame_clean (a n ℓ : ℕ)
    (x : (Bool × Bool) × (GraphEncoding.PhysicalSignal (Bits a) × (Fin 4 × Bits n)))
    (r : CompilerRest ℓ) :
    graphFrame a n ℓ (graphLocalClean x,r)=clean a n ℓ (labelDataFrame a n ℓ (x,r)) := by
  simp [graphFrame,graphLocalClean,scratchFrame,clean]

def graphGateEval (a n ℓ : ℕ) (g : PhaseGate GraphLocalWire) :
    Matrix.unitaryGroup (Physical a n ℓ) ℂ :=
  GateSynthesis.placeHom (graphFrame a n ℓ) (elementaryPlacement g.eval)

def attachedGraph (a n ℓ : ℕ)
    (c : ElementaryCircuit (Bits a × Bits n) (Bits n) GraphLocalWire (Bits a × Bits n)) :
    NamedCircuit (PhaseGate GraphLocalWire) (Bits a × Bits n) (Bits n) (Physical a n ℓ) :=
  attachList (graphFrame a n ℓ) id c

theorem attachedGraph_counts (a n ℓ : ℕ)
    (c : ElementaryCircuit (Bits a × Bits n) (Bits n) GraphLocalWire (Bits a × Bits n)) :
    ((attachedGraph a n ℓ c).toQuery (graphGateEval a n ℓ)).matrixQueries=c.toQuery.matrixQueries ∧
      ((attachedGraph a n ℓ c).toQuery (graphGateEval a n ℓ)).vectorQueries=c.toQuery.vectorQueries ∧
      (attachedGraph a n ℓ c).workGates=c.workGates := by
  rw [attachedGraph,attachList_toQuery (graphFrame a n ℓ) id (graphGateEval a n ℓ) (fun _=>rfl)]
  exact ⟨(QueryCircuit.lift_counts _ _).1,(QueryCircuit.lift_counts _ _).2,
    attachList_workGates _ _ _⟩

theorem graphFrame_intertwines (a n ℓ : ℕ)
    (U : Matrix.unitaryGroup (GraphLocalState × (Bits a × Bits n)) ℂ)
    (V : Matrix.unitaryGroup ((Bool × Bool) ×
      (GraphEncoding.PhysicalSignal (Bits a) × (Fin 4 × Bits n))) ℂ)
    (h : U.val*basisInsertion graphLocalClean=basisInsertion graphLocalClean*V.val) :
    (GateSynthesis.placeHom (graphFrame a n ℓ) U).val*basisInsertion (clean a n ℓ)=
      basisInsertion (clean a n ℓ)*(GateSynthesis.placeHom (labelDataFrame a n ℓ) V).val := by
  have ht := tensor_intertwines (D := CompilerRest ℓ) graphLocalClean U V h
  have he := clean_intertwines_transport (graphFrame a n ℓ) (labelDataFrame a n ℓ)
    (fun x => (graphLocalClean x.1,x.2)) _ _ ht
  have hc : (fun x => graphFrame a n ℓ
      (graphLocalClean ((labelDataFrame a n ℓ).symm x).1,((labelDataFrame a n ℓ).symm x).2))=
      clean a n ℓ := by
    funext x
    rw [graphFrame_clean,Equiv.apply_symm_apply]
  rw [hc] at he
  exact he

/-- This identity is only physical register association, not the nonlinear
compiler-work label permutation. It retains every source-oracle column. -/

theorem labelDataFrame_oracle (a n ℓ : ℕ) (l : Label)
    (U : Matrix.unitaryGroup (GraphEncoding.PhysicalSignal (Bits a) × (Fin 4 × Bits n)) ℂ) :
    GateSynthesis.placeHom (labelDataFrame a n ℓ)
      ((GraphEncoding.maskedGraphPort _ (labelBitsEquiv l)).apply U)=
      (compilerDataPort (PreparationData (Bits a) (Bits n)) ℓ l).apply (doubleOracle U) := by
  trans padHom (dataQuery (a := Bits ℓ × Bits ℓ) l (doubleOracle U))
  swap
  · exact (compilerDataPort_eval (N := PreparationData (Bits a) (Bits n)) (ℓ := ℓ) l (doubleOracle U)).symm
  apply Subtype.ext
  ext x y
  obtain ⟨⟨⟨m,w⟩,r⟩,rfl⟩ := (labelDataFrame a n ℓ).surjective x
  obtain ⟨⟨⟨m',w'⟩,r'⟩,rfl⟩ := (labelDataFrame a n ℓ).surjective y
  rw [placeHom_entry,GraphEncoding.maskedGraphPort_apply_entries]
  rcases r with ⟨z,b,t,c⟩
  rcases r' with ⟨z',b',t',c'⟩
  simp only [padHom,GraphEncoding.placeHom_entries,labelDataFrame,Equiv.prodComm_symm,
    Equiv.prodComm_apply,Prod.swap,dataQuery,doubleOracle,signalLift,rewireUnitary,
    controlledOn,Matrix.blockDiagonal_apply,Matrix.submatrix_apply,Equiv.prodAssoc_symm_apply,
    Equiv.prodAssoc_apply]
  by_cases hz : z=z' <;> by_cases hb : b=b' <;> by_cases ht : t=t' <;>
    by_cases hc : c=c' <;> by_cases hm : m=m' <;> by_cases hl : m=labelBitsEquiv l <;>
    simp_all [Matrix.one_apply,Matrix.blockDiagonal_apply,Prod.mk.injEq,labelBitsEquiv.symm.injective.eq_iff,
      Equiv.symm_apply_eq,Equiv.eq_symm_apply]

def graphSingleFlagPort (a n ℓ : ℕ) : QueryPort (Bits a × Bits n) (Physical a n ℓ) :=
  (scratchPort (graphFrame a n ℓ)).comp
    (GraphEncoding.singleFlagOraclePort (Bits a × Bits n) GraphEncoding.flagWire)

theorem attachedGraph_single_flag (a n ℓ : ℕ)
    (c : ElementaryCircuit (Bits a × Bits n) (Bits n) GraphLocalWire (Bits a × Bits n))
    (hc : GraphEncoding.SingleFlagRealCircuit GraphEncoding.flagWire c)
    (p : QueryPort (Bits a × Bits n) (Physical a n ℓ)) (b : Bool)
    (hp : NamedInstruction.matrixCall p b ∈ attachedGraph a n ℓ c) :
    p=graphSingleFlagPort a n ℓ := by
  obtain ⟨i,hi,hEq⟩ := List.mem_map.mp hp
  cases i with
  | gate g => cases hEq
  | matrixCall q d =>
    have hq := hc.2 q d hi
    subst q
    cases hEq
    rfl
  | vectorCall q d => cases hEq

/-- Two original matrix calls, actual elementary work, and coherent cleanup on
all compiler labels, spare bits, clock/cache values, and data columns. -/
theorem graphCompilerCall (a n ℓ : ℕ) (κ : ℝ) (hκ : 0<κ) :
    ∃ c : NamedCircuit (PhaseGate GraphLocalWire) (Bits a × Bits n) (Bits n) (Physical a n ℓ),
      (c.toQuery (graphGateEval a n ℓ)).matrixQueries=2 ∧
      (c.toQuery (graphGateEval a n ℓ)).vectorQueries=0 ∧ c.workGates≤252304 ∧
      (∀ g, NamedInstruction.gate g ∈ c → GraphEncoding.RealPhaseGate g) ∧
      (∀ p b, NamedInstruction.matrixCall p b ∈ c → p=graphSingleFlagPort a n ℓ) ∧
      ∀ UA Ub, ((c.toQuery (graphGateEval a n ℓ)).eval UA Ub).val*basisInsertion (clean a n ℓ)=
        basisInsertion (clean a n ℓ)*
          ((compilerDataPort (PreparationData (Bits a) (Bits n)) ℓ .first).apply
            (doubleOracle (GraphEncoding.physicalEncoding κ hκ UA))).val := by
  obtain ⟨c,hm,hv,hg,hs,he⟩ := GraphEncoding.controlled_graph_single_flag
    (S := Bits a) (D := Bits n) (B := Bits n) κ hκ (true,false)
  refine ⟨attachedGraph a n ℓ c,(attachedGraph_counts _ _ _ _).1.trans hm,
    (attachedGraph_counts _ _ _ _).2.1.trans hv,?_,?_,?_,?_⟩
  · rw [(attachedGraph_counts _ _ _ _).2.2]
    exact hg
  · intro g hg
    obtain ⟨i,hi,hEq⟩ := List.mem_map.mp hg
    cases i with
    | gate p => cases hEq; exact hs.1 p hi
    | matrixCall p b => cases hEq
    | vectorCall p b => cases hEq
  · exact attachedGraph_single_flag a n ℓ c hs
  · intro UA Ub
    rw [attachedGraph,attachList_eval (graphFrame a n ℓ) id (graphGateEval a n ℓ) (fun _=>rfl)]
    have hh := graphFrame_intertwines a n ℓ _ _ (he false UA Ub)
    erw [labelDataFrame_oracle a n ℓ .first] at hh
    exact hh

end OptimalQLS.Preparation.CompilerAttachment
