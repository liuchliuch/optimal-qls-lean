import OptimalQLS.PolynomialTransform.WorkIdentities

/-! # The complete QSVT list uses only the two synthesized work families -/
noncomputable section
namespace OptimalQLS.PolynomialTransform
open Matrix DirtyAncilla
variable {W D B A V : Type*} [Fintype W] [DecidableEq W] [Fintype D] [DecidableEq D]
  [Fintype B] [DecidableEq B] [Fintype A] [DecidableEq A] [Fintype V] [DecidableEq V]

theorem workInstructions_append (c d : QueryCircuit A B W) :
    workInstructions (c++d)=workInstructions c+workInstructions d := by
  induction c with
  | nil => simp [workInstructions]
  | cons g c ih => cases g <;> simp [workInstructions,ih,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

theorem workInstructions_lift (port : QueryPort W V) (c : QueryCircuit A B W) :
    workInstructions (c.lift port)=workInstructions c := by
  induction c with
  | nil => rfl
  | cons g c ih => cases g <;> simpa [QueryCircuit.lift,QueryInstruction.lift,workInstructions] using ih

theorem work_mem_lift (port : QueryPort W V) (c : QueryCircuit A B W)
    (U : Matrix.unitaryGroup V ℂ) (h : QueryInstruction.work U ∈ c.lift port) :
    ∃ T : Matrix.unitaryGroup W ℂ, QueryInstruction.work T ∈ c ∧ port.apply T=U := by
  obtain ⟨g,hg,he⟩ := List.mem_map.mp h
  cases g with
  | work T => exact ⟨T,hg,by simpa [QueryInstruction.lift] using he⟩
  | matrixCall p b => simp [QueryInstruction.lift] at he
  | vectorCall p b => simp [QueryInstruction.lift] at he

theorem dilated_work_shape (E : Matrix W D ℂ) (hE : Eᴴ*E=1) (z₀ : Circle) (zs : List Circle)
    (U : Matrix.unitaryGroup (W ⊕ W) ℂ)
    (hU : QueryInstruction.work U ∈ dilatedQSPCircuit (B := B) E hE z₀ zs) :
    (∃ z w : Circle, U=insertionPhases (duplicateInsertion E) (duplicateInsertion_isometry E hE) z w) ∨
      U=swapPublicPrivate := by
  induction zs generalizing U with
  | nil =>
    simp [dilatedQSPCircuit,hermitianQSPCircuit,QueryCircuit.substituteMatrix,
      QueryInstruction.substituteMatrix] at hU
    subst U
    exact Or.inl ⟨z₀,z₀⁻¹,rfl⟩
  | cons z zs ih =>
    simp only [dilatedQSPCircuit,hermitianQSPCircuit,QueryCircuit.substituteMatrix,
      List.flatMap_cons,QueryInstruction.substituteMatrix,Bool.false_eq_true,ite_false,
      hermitianizationCircuit,QueryCircuit.lift,List.map_cons,List.map_nil,QueryInstruction.lift,
      wholeOraclePort_apply,List.singleton_append,List.cons_append,List.nil_append,
      List.mem_cons,QueryInstruction.work.injEq,QueryInstruction.noConfusion] at hU
    simp only [reduceCtorEq,false_or] at hU
    rcases hU with hU|hU|hU|hU|hU
    · subst U; exact Or.inl ⟨z,z⁻¹,rfl⟩
    · subst U; exact Or.inl ⟨1,circleI,rfl⟩
    · subst U; exact Or.inr rfl
    · subst U; exact Or.inl ⟨1,circleI,rfl⟩
    · exact ih U hU

theorem dilated_work_count (E : Matrix W D ℂ) (hE : Eᴴ*E=1) (z₀ : Circle) (zs : List Circle) :
    workInstructions (dilatedQSPCircuit (B := B) E hE z₀ zs)=4*zs.length+1 := by
  induction zs with
  | nil => simp [dilatedQSPCircuit,hermitianQSPCircuit,QueryCircuit.substituteMatrix,
      QueryInstruction.substituteMatrix,workInstructions]
  | cons z zs ih =>
    simp only [dilatedQSPCircuit,hermitianQSPCircuit,QueryCircuit.substituteMatrix,
      List.flatMap_cons,QueryInstruction.substituteMatrix,Bool.false_eq_true,ite_false,
      hermitianizationCircuit,QueryCircuit.lift,List.map_cons,List.map_nil,QueryInstruction.lift,
      List.singleton_append,List.cons_append,List.nil_append,workInstructions] at *
    simp only [List.length_cons]
    omega

/-- Every work instruction of the final, relabeled list has a concrete
linear-size implementation proved in PhysicalPhases or PhysicalLabels. -/
theorem bounded_work_shape (a : ℕ) (z₀ : Circle) (zs : List Circle)
    (U : Matrix.unitaryGroup (LogicalSignal a × D) ℂ)
    (hU : QueryInstruction.work U ∈ boundedTransformCircuit (D := D) (B := B)
      (fun _ : Fin a => false) z₀ zs) :
    (∃ branch z w, U=logicalPhase (D := D) a branch z w) ∨
      (∃ V : Matrix.unitaryGroup (Bool × Bool) ℂ, U=logicalLabels (D := D) a V) := by
  obtain ⟨V,hV,rfl⟩ := work_mem_lift _ _ U hU
  simp only [relabelPort_apply]
  simp only [evenQSVTCircuit,List.mem_append,List.mem_singleton,QueryInstruction.work.injEq] at hV
  rcases hV with ((hV|hV)|hV)|hV
  · subst V; exact Or.inr ⟨labelHadamard,relabel_hadamard a⟩
  · obtain ⟨T,hT,rfl⟩ := work_mem_lift _ _ V hV
    rw [leftOraclePort_apply]
    rcases dilated_work_shape _ _ _ _ T hT with ⟨z,w,rfl⟩|rfl
    · exact Or.inl ⟨false,z,w,by simpa using relabel_controlled_phase (D := D) a false z w⟩
    · exact Or.inr ⟨labelSwap false,by simpa using relabel_swap (D := D) a false⟩
  · obtain ⟨T,hT,rfl⟩ := work_mem_lift _ _ V hV
    rw [rightOraclePort_apply]
    rcases dilated_work_shape _ _ _ _ T hT with ⟨z,w,rfl⟩|rfl
    · exact Or.inl ⟨true,z,w,by simpa using relabel_controlled_phase (D := D) a true z w⟩
    · exact Or.inr ⟨labelSwap true,by simpa using relabel_swap (D := D) a true⟩
  · subst V; exact Or.inr ⟨labelHadamard,relabel_hadamard a⟩

theorem bounded_work_count (a : ℕ) (z₀ : Circle) (zs : List Circle) :
    workInstructions (boundedTransformCircuit (D := D) (B := B) (fun _ : Fin a => false) z₀ zs)=
      8*zs.length+4 := by
  simp only [boundedTransformCircuit,workInstructions_lift,evenQSVTCircuit,
    workInstructions_append,workInstructions,dilated_work_count,List.length_map]
  omega

theorem bounded_work_synthesis (a : ℕ) (z₀ : Circle) (zs : List Circle)
    (U : Matrix.unitaryGroup (LogicalSignal a × D) ℂ)
    (hU : QueryInstruction.work U ∈ boundedTransformCircuit (D := D) (B := B)
      (fun _ : Fin a => false) z₀ zs) :
    ∃ code : List (PhaseGate (QSVTWire a)), code.length ≤ 781*(a+1) ∧
      (elementaryPlacement (D := D) (phaseEval code)).val*basisInsertion (physicalClean a)=
        basisInsertion (physicalClean a)*U.val := by
  rcases bounded_work_shape a z₀ zs U hU with ⟨branch,z,w,rfl⟩|⟨V,rfl⟩
  · exact logicalPhase_synthesis a branch z w
  · exact logicalLabels_synthesis a V

end OptimalQLS.PolynomialTransform
