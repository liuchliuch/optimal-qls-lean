import OptimalQLS.PolynomialTransform.WorkClassification

/-! # The exact two-label control predicates used by QSVT oracle calls -/
noncomputable section
namespace OptimalQLS.PolynomialTransform
open Matrix
variable {W D S B A V : Type*} [Fintype W] [DecidableEq W] [Fintype D] [DecidableEq D]
  [Fintype S] [DecidableEq S] [Fintype B] [DecidableEq B]
  [Fintype A] [DecidableEq A] [Fintype V] [DecidableEq V]

theorem matrix_mem_lift (port : QueryPort W V) (c : QueryCircuit A B W)
    (p : QueryPort A V) (adj : Bool) (h : QueryInstruction.matrixCall p adj ∈ c.lift port) :
    ∃ q : QueryPort A W, QueryInstruction.matrixCall q adj ∈ c ∧ p=port.comp q := by
  obtain ⟨g,hg,he⟩ := List.mem_map.mp h
  cases g with
  | work T => simp [QueryInstruction.lift] at he
  | matrixCall q b =>
    simp only [QueryInstruction.lift,QueryInstruction.matrixCall.injEq] at he
    obtain ⟨rfl,rfl⟩ := he
    exact ⟨q,hg,rfl⟩
  | vectorCall q b => simp [QueryInstruction.lift] at he

theorem dilated_query_shape (E : Matrix W D ℂ) (hE : Eᴴ*E=1) (z₀ : Circle) (zs : List Circle)
    (p : QueryPort W (W ⊕ W)) (adj : Bool)
    (hp : QueryInstruction.matrixCall p adj ∈ dilatedQSPCircuit (B := B) E hE z₀ zs) :
    ∀ U : Matrix.unitaryGroup W ℂ,
      p.apply U=if adj then sumUnitary 1 U else sumUnitary U 1 := by
  induction zs generalizing p adj with
  | nil =>
    simp [dilatedQSPCircuit,hermitianQSPCircuit,QueryCircuit.substituteMatrix,
      QueryInstruction.substituteMatrix] at hp
  | cons z zs ih =>
    simp only [dilatedQSPCircuit,hermitianQSPCircuit,QueryCircuit.substituteMatrix,
      List.flatMap_cons,QueryInstruction.substituteMatrix,Bool.false_eq_true,ite_false,
      hermitianizationCircuit,QueryCircuit.lift,List.map_cons,List.map_nil,QueryInstruction.lift,
      List.cons_append,List.nil_append,List.mem_cons,reduceCtorEq,false_or,
      QueryInstruction.matrixCall.injEq] at hp
    rcases hp with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|hp
    · intro U; simp [QueryPort.comp_apply]
    · intro U; simp [QueryPort.comp_apply]
    · exact ih p adj hp

/-- The four possible calls select one averaging label and one dilation label.
The selected dilation label is also the actual adjoint flag. -/
theorem bounded_query_controls (s₀ : S) (z₀ : Circle) (zs : List Circle)
    (p : QueryPort (S × D) (((Bool × Bool) × S) × D)) (adj : Bool)
    (hp : QueryInstruction.matrixCall p adj ∈ boundedTransformCircuit (B := B) s₀ z₀ zs) :
    ∃ branch : Bool, ∀ U : Matrix.unitaryGroup (S × D) ℂ,
      p.apply U=rewireUnitary (twoLabelSignalEquiv S D)
        (if branch then
          sumUnitary 1 (if adj then sumUnitary 1 U else sumUnitary U 1)
        else
          sumUnitary (if adj then sumUnitary 1 U else sumUnitary U 1) 1) := by
  obtain ⟨q,hq,rfl⟩ := matrix_mem_lift _ _ p adj hp
  simp only [evenQSVTCircuit,List.mem_append,List.mem_singleton,reduceCtorEq,false_or,or_false] at hq
  rcases hq with hq|hq
  · obtain ⟨r,hr,rfl⟩ := matrix_mem_lift _ _ q adj hq
    refine ⟨false,?_⟩
    intro U
    simp only [QueryPort.comp_apply,relabelPort_apply,leftOraclePort_apply,Bool.false_eq_true,ite_false]
    rw [dilated_query_shape _ _ _ _ r adj hr U]
  · obtain ⟨r,hr,rfl⟩ := matrix_mem_lift _ _ q adj hq
    refine ⟨true,?_⟩
    intro U
    simp only [QueryPort.comp_apply,relabelPort_apply,rightOraclePort_apply,ite_true]
    rw [dilated_query_shape _ _ _ _ r adj hr U]

end OptimalQLS.PolynomialTransform
