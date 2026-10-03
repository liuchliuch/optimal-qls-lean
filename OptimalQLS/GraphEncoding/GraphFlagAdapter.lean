import OptimalQLS.GraphEncoding.SingleFlagOracle
import OptimalQLS.GraphEncoding.QueryPredicates

/-! # Four literal graph controls lowered to one actual oracle flag -/
noncomputable section
set_option synthInstance.maxSize 2048
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace OptimalQLS.GraphEncoding
open Matrix PolynomialTransform TransducerCompiler DirtyAncilla
variable {S D B : Type*} [Fintype S] [DecidableEq S]
  [Fintype D] [DecidableEq D] [Fintype B] [DecidableEq B]

def graphOracleControls : SmallWire 4 → ControlledGraphWire
  | .inl i => ![maskWire 0,maskWire 1,coreWire (some 0),coreWire (some 4)] i
  | .inr i => .inr i

theorem graphOracleControls_injective : Function.Injective graphOracleControls := by
  intro i j h
  rcases i with i|i <;> rcases j with j|j
  · fin_cases i <;> fin_cases j <;> simp_all [graphOracleControls,maskWire,coreWire]
  · fin_cases i <;> simp_all [graphOracleControls,maskWire,coreWire]
  · fin_cases j <;> simp_all [graphOracleControls,maskWire,coreWire]
  · simpa [graphOracleControls] using h

def graphFlagOracleCircuit (mask : Bool × Bool) (adj : Bool) :
    ElementaryCircuit (S × D) B ControlledGraphWire (S × D) :=
  maskedOracleCircuit 4 graphOracleControls graphOracleControls_injective
    ![mask.1,mask.2,false,adj] adj

theorem originalGraphPort_basis (adj : Bool) (U : Matrix.unitaryGroup (S × D) ℂ)
    (x : CoreWire → Bool) (i : S × D) :
    ((originalGraphPort S D adj).apply U).val *ᵥ Pi.single (corePhysicalWiring S D (x,i)) 1 =
      ∑ j : S × D, (if x (some 0)=false ∧ x (some 4)=adj then U.val j i else if j=i then 1 else 0) •
        (Pi.single (corePhysicalWiring S D (x,j)) 1 : PhysicalSignal S × (Fin 4 × D) → ℂ) := by
  ext w
  obtain ⟨⟨y,j⟩,rfl⟩ := (corePhysicalWiring S D).surjective w
  simp only [Matrix.mulVec_single_one,Matrix.col_apply,originalGraphPort_entries,
    Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Pi.single_apply]
  by_cases h : y=x
  · subst y
    simp [(corePhysicalWiring S D).injective.eq_iff]
  · simp [h,Ne.symm h,(corePhysicalWiring S D).injective.eq_iff,Prod.mk.injEq]

theorem originalMaskedGraph_basis (mask m : Bool × Bool) (adj : Bool)
    (U : Matrix.unitaryGroup (S × D) ℂ) (x : CoreWire → Bool) (i : S × D) :
    ((maskedGraphPort (PhysicalSignal S × (Fin 4 × D)) mask).apply
      ((originalGraphPort S D adj).apply U)).val *ᵥ Pi.single (m,corePhysicalWiring S D (x,i)) 1 =
      ∑ j : S × D,
        (if m=mask ∧ x (some 0)=false ∧ x (some 4)=adj then U.val j i else if j=i then 1 else 0) •
          (Pi.single (m,corePhysicalWiring S D (x,j)) 1 :
            (Bool × Bool) × (PhysicalSignal S × (Fin 4 × D)) → ℂ) := by
  rw [maskedGraphPort_basis_expansion mask m _ _ _ _ (originalGraphPort_basis adj U x i)]
  by_cases h : m=mask
  · simp only [h,ite_true,true_and]
  · simp [h]

/-- Exact compute-flag/query/uncompute implementation of an actual graph query. -/
theorem graphFlagOracleCircuit_intertwines (mask : Bool × Bool) (adj : Bool)
    (U : Matrix.unitaryGroup (S × D) ℂ) (Ub : Matrix.unitaryGroup B ℂ) :
    ((graphFlagOracleCircuit (S := S) (D := D) (B := B) mask adj).toQuery.eval U Ub).val *
      basisInsertion (graphLocalClean (S := S) (D := D)) =
    basisInsertion (graphLocalClean (S := S) (D := D)) *
      ((maskedGraphPort (PhysicalSignal S × (Fin 4 × D)) mask).apply
        ((originalGraphPort S D adj).apply (if adj then U⁻¹ else U))).val := by
  apply basisInsertion_intertwines
  intro w
  rcases w with ⟨m,w⟩
  obtain ⟨⟨x,i⟩,rfl⟩ := (corePhysicalWiring S D).surjective w
  rw [graphLocalClean_core,originalMaskedGraph_basis,Matrix.mulVec_sum]
  unfold graphFlagOracleCircuit
  rw [maskedOracleCircuit_basis _ _ _ _ _ _ (by rfl)]
  simp only [Matrix.mulVec_smul,basisInsertion_basis,graphLocalClean_core]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  simp [controlledAssignment,graphOracleControls,Fin.forall_fin_succ,maskWire,coreWire,
    Prod.ext_iff,and_assoc]

theorem graphFlagOracleCircuit_counts (mask : Bool × Bool) (adj : Bool) :
    (graphFlagOracleCircuit (S := S) (D := D) (B := B) mask adj).toQuery.matrixQueries=1 ∧
      (graphFlagOracleCircuit (S := S) (D := D) (B := B) mask adj).toQuery.vectorQueries=0 ∧
      (graphFlagOracleCircuit (S := S) (D := D) (B := B) mask adj).workGates ≤ 4020 := by
  exact maskedOracleCircuit_counts 4 graphOracleControls graphOracleControls_injective
    ![mask.1,mask.2,false,adj] adj

theorem graphFlagOracleCircuit_single_flag (mask : Bool × Bool) (adj : Bool)
    (p : QueryPort (S × D) (ElementarySpace ControlledGraphWire (S × D))) (b : Bool)
    (h : ElementaryInstruction.matrixCall p b ∈ graphFlagOracleCircuit (B := B) mask adj) :
    p=singleFlagOraclePort (S × D) flagWire ∧ b=adj := by
  exact maskedOracleCircuit_single_flag _ _ _ _ _ p b h

end OptimalQLS.GraphEncoding
