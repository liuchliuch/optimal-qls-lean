import OptimalQLS.GraphEncoding.ControlledIntertwining

/-! # The exact constant-size predicates of the two original graph queries -/
noncomputable section
set_option synthInstance.maxSize 2048
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace OptimalQLS.GraphEncoding
open Matrix PolynomialTransform TransducerCompiler
variable {S D B : Type*} [Fintype S] [DecidableEq S]
  [Fintype D] [DecidableEq D] [Fintype B] [DecidableEq B]

def originalGraphPort (S D : Type*) [Fintype S] [DecidableEq S]
    [Fintype D] [DecidableEq D] (adj : Bool) :
    QueryPort (S × D) (PhysicalSignal S × (Fin 4 × D)) :=
  (rewirePort (realizedPhysicalWiring S D)).comp
    ((tensorPort (BranchSpace S D ⊕ BranchSpace S D) Bool).comp
      ((leftOraclePort (BranchSpace S D)).comp
        ((tensorPort ((S × D) ⊕ (S × D)) Label).comp
          (if adj then rightOraclePort (S × D) else leftOraclePort (S × D)))))

/-- Every original query has exactly its named oracle-dilation selector. -/
theorem elementaryGraph_query_port (κ : ℝ) (hκ : 0 < κ)
    (p : QueryPort (S × D) (PhysicalSignal S × (Fin 4 × D))) (adj : Bool)
    (h : QueryInstruction.matrixCall p adj ∈ elementaryGraphCircuit S D B κ hκ) :
    p=originalGraphPort S D adj := by
  simp [elementaryGraphCircuit,realizedSelectCircuit,controlledSignalCircuit,
    signalCircuit,hermitianizationCircuit,labelLowerCircuit,QueryCircuit.lift,
    QueryInstruction.lift,List.mem_map] at h
  rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> rfl

theorem allowedGraph_query_port (κ : ℝ) (hκ : 0 < κ) (mask : Bool × Bool)
    (p : QueryPort (S × D) ((Bool × Bool) × (PhysicalSignal S × (Fin 4 × D))))
    (adj : Bool) (h : QueryInstruction.matrixCall p adj ∈ allowedGraphCall S D B κ hκ mask false) :
    p=(maskedGraphPort (PhysicalSignal S × (Fin 4 × D)) mask).comp (originalGraphPort S D adj) := by
  obtain ⟨q,hq,hEq⟩ := List.mem_map.mp h
  cases q with
  | work U => cases hEq
  | vectorCall p b => cases hEq
  | matrixCall q b =>
    obtain ⟨rfl,rfl⟩ := QueryInstruction.matrixCall.inj hEq
    rw [elementaryGraph_query_port κ hκ q b hq]

/-- Only SELECT and the oracle-Hermitianization bit control an unmasked
original-U_A call; no original signal or data predicate is concealed. -/
theorem originalGraphPort_entries (adj : Bool) (U : Matrix.unitaryGroup (S × D) ℂ)
    (x y : CoreWire → Bool) (i j : S × D) :
    ((originalGraphPort S D adj).apply U).val
      (corePhysicalWiring S D (x,i)) (corePhysicalWiring S D (y,j)) =
      if x=y then (if x (some 0)=false ∧ x (some 4)=adj then U.val i j
        else if i=j then 1 else 0) else 0 := by
  cases adj <;> cases hx0 : x (some 0) <;> cases hy0 : y (some 0) <;>
    cases hx4 : x (some 4) <;> cases hy4 : y (some 4) <;>
    simp [originalGraphPort,QueryPort.comp_apply,rewirePort_apply,tensorPort_apply,
      leftOraclePort_apply,rightOraclePort_apply,rewireUnitary,corePhysicalWiring,
      realizedPhysicalWiring,coreWiring,labelDistribution,labelWiring,coreLabels,coreInner,
      tensorUnitary,HadamardClock.tensorUnitary,sumUnitary,Matrix.one_apply,
      graphBits.injective.eq_iff,funext_iff,Option.forall,Fin.forall_fin_succ,
      hx0,hy0,hx4,hy4,and_assoc,and_left_comm,and_comm] <;>
    split_ifs <;> simp_all [Prod.mk.injEq,funext_iff,Option.forall,Fin.forall_fin_succ]

end OptimalQLS.GraphEncoding
