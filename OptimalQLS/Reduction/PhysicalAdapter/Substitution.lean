import OptimalQLS.Reduction.PhysicalAdapter.Macros

/-! Whole-list substitution, independent of the supplied oracle matrices. -/
noncomputable section
set_option synthInstance.maxSize 16384
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
open scoped Classical
namespace OptimalQLS.Reduction.PhysicalAdapter
open Matrix PolynomialTransform TransducerCompiler BinaryClock Refinement.PhysicalProgram

/-- Only the three proven physical placements can be selected. -/
def chooseFlag (a n ℓ : ℕ) (p : QueryPort (Bits a × Bits (n+1)) (Register a (n+1) ℓ)) : Flag :=
  if p=matrixPort a (n+1) ℓ .preparation then .preparation
  else if p=matrixPort a (n+1) ℓ .filter then .filter else .correction

theorem chooseFlag_correct (a n ℓ : ℕ)
    (p : QueryPort (Bits a × Bits (n+1)) (Register a (n+1) ℓ))
    (hp : p=matrixPort a (n+1) ℓ .preparation ∨ p=matrixPort a (n+1) ℓ .filter ∨
      p=matrixPort a (n+1) ℓ .correction) : matrixPort a (n+1) ℓ (chooseFlag a n ℓ p)=p := by
  unfold chooseFlag
  split_ifs with h₀ h₁
  · exact h₀.symm
  · exact h₁.symm
  · rcases hp with hp|hp|hp
    · exact False.elim (h₀ hp)
    · exact False.elim (h₁ hp)
    · exact hp.symm

def substituteInstruction (a n ℓ : ℕ) :
    NamedInstruction (Refinement.PhysicalProgram.Gate a (n+1) ℓ)
      (Bits a × Bits (n+1)) (Bits (n+1)) (Register a (n+1) ℓ) → Circuit a n ℓ
  | .gate g => [.gate (.old g)]
  | .matrixCall p adj => matrixCode a n ℓ (chooseFlag a n ℓ p) adj
  | .vectorCall _ adj => vectorCode a n ℓ adj

def substitute (a n ℓ : ℕ) (c : Refinement.PhysicalProgram.Circuit a (n+1) ℓ) : Circuit a n ℓ :=
  c.flatMap (substituteInstruction a n ℓ)

def Allowed {a n ℓ : ℕ} (c : Refinement.PhysicalProgram.Circuit a (n+1) ℓ) : Prop :=
  (∀ p adj,NamedInstruction.matrixCall p adj∈c →
    p=matrixPort a (n+1) ℓ .preparation ∨ p=matrixPort a (n+1) ℓ .filter ∨
      p=matrixPort a (n+1) ℓ .correction) ∧
  (∀ p adj,NamedInstruction.vectorCall p adj∈c → p=preparationVectorPort a (n+1) ℓ)

theorem substitute_counts (a n ℓ : ℕ) (hℓ : 0<ℓ)
    (c : Refinement.PhysicalProgram.Circuit a (n+1) ℓ) :
    ((substitute a n ℓ c).toQuery (gateEval a n ℓ hℓ)).matrixQueries=
      2*(c.toQuery (Refinement.PhysicalProgram.gateEval a (n+1) ℓ hℓ)).matrixQueries ∧
    ((substitute a n ℓ c).toQuery (gateEval a n ℓ hℓ)).vectorQueries=
      (c.toQuery (Refinement.PhysicalProgram.gateEval a (n+1) ℓ hℓ)).vectorQueries ∧
    (substitute a n ℓ c).workGates≤c.workGates+
      4801*(c.toQuery (Refinement.PhysicalProgram.gateEval a (n+1) ℓ hℓ)).matrixQueries := by
  induction c with
  | nil => exact ⟨rfl,rfl,by simp [substitute,NamedCircuit.workGates,NamedCircuit.toQuery,QueryCircuit.matrixQueries]⟩
  | cons i c ih =>
    change (((substituteInstruction a n ℓ i)++substitute a n ℓ c).toQuery _).matrixQueries=_ ∧
      (((substituteInstruction a n ℓ i)++substitute a n ℓ c).toQuery _).vectorQueries=_ ∧
      ((substituteInstruction a n ℓ i)++substitute a n ℓ c).workGates≤_
    simp only [NamedCircuit.toQuery_append,QueryCircuit.matrixQueries_append,
      QueryCircuit.vectorQueries_append,NamedCircuit.workGates_append]
    cases i with
    | gate g =>
      simp only [substituteInstruction,NamedCircuit.toQuery,List.map_cons,List.map_nil,
        NamedInstruction.toQuery,QueryCircuit.matrixQueries,QueryCircuit.vectorQueries,
        NamedCircuit.workGates,zero_add] at *
      omega
    | matrixCall p adj =>
      have hm := matrixCode_counts a n ℓ hℓ (chooseFlag a n ℓ p) adj
      simp only [substituteInstruction,NamedCircuit.toQuery,List.map_cons,
        NamedInstruction.toQuery,QueryCircuit.matrixQueries,QueryCircuit.vectorQueries,
        NamedCircuit.workGates] at *
      omega
    | vectorCall p adj =>
      have hv := vectorCode_counts a n ℓ hℓ adj
      simp only [substituteInstruction,NamedCircuit.toQuery,List.map_cons,
        NamedInstruction.toQuery,QueryCircuit.matrixQueries,QueryCircuit.vectorQueries,
        NamedCircuit.workGates] at *
      omega

theorem substitute_intertwines (a n ℓ : ℕ) (hℓ : 0<ℓ)
    (c : Refinement.PhysicalProgram.Circuit a (n+1) ℓ) (hc : Allowed c)
    (UA : Matrix.unitaryGroup (Bits a × Bits n) ℂ) (Ub : Matrix.unitaryGroup (Bits n) ℂ) :
    (((substitute a n ℓ c).toQuery (gateEval a n ℓ hℓ)).eval UA Ub).val*basisInsertion (clean a n ℓ)=
      basisInsertion (clean a n ℓ)*
        ((c.toQuery (Refinement.PhysicalProgram.gateEval a (n+1) ℓ hℓ)).eval
          (matrixOracle UA) (vectorOracle Ub)).val := by
  induction c with
  | nil => simp [substitute,NamedCircuit.toQuery,QueryCircuit.eval]
  | cons i c ih =>
    have ht : Allowed c := ⟨fun p adj hp=>hc.1 p adj (List.mem_cons_of_mem _ hp),
      fun p adj hp=>hc.2 p adj (List.mem_cons_of_mem _ hp)⟩
    have hi : (((substituteInstruction a n ℓ i).toQuery (gateEval a n ℓ hℓ)).eval UA Ub).val*
        basisInsertion (clean a n ℓ)=basisInsertion (clean a n ℓ)*
          ((i.toQuery (Refinement.PhysicalProgram.gateEval a (n+1) ℓ hℓ)).eval
            (matrixOracle UA) (vectorOracle Ub)).val := by
      cases i with
      | gate g =>
        simpa [substituteInstruction,NamedCircuit.toQuery,NamedInstruction.toQuery,
          QueryCircuit.eval,QueryInstruction.eval,gateEval,clean] using
          scratchPort_intertwines (Equiv.refl (Space a n ℓ)) (false,false,false)
            (Refinement.PhysicalProgram.gateEval a (n+1) ℓ hℓ g)
      | matrixCall p adj =>
        have h := matrixCode_intertwines a n ℓ hℓ (chooseFlag a n ℓ p) adj UA Ub
        rw [chooseFlag_correct a n ℓ p (hc.1 p adj (by simp))] at h
        exact h
      | vectorCall p adj =>
        have hp := hc.2 p adj (by simp)
        subst p
        exact vectorCode_intertwines a n ℓ hℓ adj UA Ub
    have h := intertwines_mul (basisInsertion (clean a n ℓ)) _ _ _ _ hi (ih ht)
    simpa only [substitute,List.flatMap_cons,NamedCircuit.toQuery,List.map_append,
      List.map_cons,QueryCircuit.eval_append,QueryCircuit.eval,Submonoid.coe_mul] using h

end OptimalQLS.Reduction.PhysicalAdapter
