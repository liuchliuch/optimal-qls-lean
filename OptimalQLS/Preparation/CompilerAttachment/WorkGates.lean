import OptimalQLS.Preparation.CompilerAttachment.WorkFrames
import OptimalQLS.Preparation.CompilerAttachment.ListAssembly

/-! # Actual emitted work words in the complete physical preparation frame -/
noncomputable section
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 700000
set_option maxRecDepth 4096
open scoped Classical
namespace OptimalQLS.Preparation.CompilerAttachment
open Matrix TransducerCompiler BinaryClock PolynomialTransform DirtyAncilla

abbrev WorkGate (a : ℕ) := PhaseGate (WorkGates.Wire (WorkGates.LogicalWire (a+4)))

def workGateEval (a n ℓ : ℕ) (g : WorkGate a) : Matrix.unitaryGroup (Physical a n (ℓ+1)) ℂ :=
  GateSynthesis.placeHom (workFrame a n ℓ) (elementaryPlacement g.eval)

def workMacro (a n ℓ : ℕ) (code : List (WorkGate a)) :
    NamedCircuit (WorkGate a) (Bits a × Bits n) (Bits n) (Physical a n (ℓ+1)) := code.map .gate

theorem workMacro_counts (a n ℓ : ℕ) (code : List (WorkGate a)) :
    ((workMacro a n ℓ code).toQuery (workGateEval a n ℓ)).matrixQueries=0 ∧
    ((workMacro a n ℓ code).toQuery (workGateEval a n ℓ)).vectorQueries=0 ∧
    (workMacro a n ℓ code).workGates=code.length := by
  induction code with
  | nil => exact ⟨rfl,rfl,rfl⟩
  | cons g c ih => exact ⟨ih.1,ih.2.1,congrArg Nat.succ ih.2.2⟩

theorem workMacro_eval (a n ℓ : ℕ) (code : List (WorkGate a))
    (UA : Matrix.unitaryGroup (Bits a × Bits n) ℂ) (Ub : Matrix.unitaryGroup (Bits n) ℂ) :
    ((workMacro a n ℓ code).toQuery (workGateEval a n ℓ)).eval UA Ub=
      GateSynthesis.placeHom (workFrame a n ℓ) (placedPhaseWord (D := Fin 4 × Bits n) code) := by
  induction code with
  | nil => simp [workMacro,NamedCircuit.toQuery,QueryCircuit.eval,placedPhaseWord,phaseEval]
  | cons g c ih =>
    simp only [workMacro,List.map_cons,NamedCircuit.toQuery,NamedInstruction.toQuery,
      QueryCircuit.eval,QueryInstruction.eval,placedPhaseWord,phaseEval,map_mul]
    exact congrArg (fun U=>U * workGateEval a n ℓ g) ih

def preparationWorkCode (a : ℕ) {κ s ŝ : ℝ} (h : BudgetParameters κ s ŝ) : List (WorkGate a) :=
  compiledWorkProgram (a+4)
    (mul_pos (by have := h.kappa_pos; positivity : 0<1+κ⁻¹) h.estimate_pos)
    (preparation_mix_abs h) true

theorem preparationWorkCode_length (a : ℕ) {κ s ŝ : ℝ} (h : BudgetParameters κ s ŝ) :
    (preparationWorkCode a h).length≤183375*(a+1) := by
  exact (compiledWorkProgram_length (a+4) _ _ true).trans (by omega)

theorem workMacro_intertwines (a n ℓ : ℕ) {κ s ŝ : ℝ} (h : BudgetParameters κ s ŝ)
    (UA : Matrix.unitaryGroup (Bits a × Bits n) ℂ) (Ub : Matrix.unitaryGroup (Bits n) ℂ) :
    (((workMacro a n ℓ (preparationWorkCode a h)).toQuery (workGateEval a n ℓ)).eval UA Ub).val *
        basisInsertion (clean a n (ℓ+1))=
      basisInsertion (clean a n (ℓ+1))*
        (padHom (cachedWork (finitePreparationWork (D := Fin 4 × Bits n)
          (GraphEncoding.physicalSignalZero (fun _ : Fin a=>false)) h
          (by have := h.kappa_pos; positivity : 0<1+κ⁻¹)))).val := by
  rw [workMacro_eval]
  have ht := workFrame_intertwines a n ℓ
    (mul_pos (by have := h.kappa_pos; positivity : 0<1+κ⁻¹) h.estimate_pos)
    (preparation_mix_abs h)
  rw [workSourceFrame_compilerWork] at ht
  exact ht

def positiveWorkGateEval (a n ℓ : ℕ) (hℓ : 0<ℓ) (g : WorkGate a) :
    Matrix.unitaryGroup (Physical a n ℓ) ℂ := by
  cases ℓ with
  | zero => exact False.elim (Nat.lt_irrefl 0 hℓ)
  | succ ℓ => exact workGateEval a n ℓ g

def positiveWorkMacro (a n ℓ : ℕ) (code : List (WorkGate a)) :
    NamedCircuit (WorkGate a) (Bits a × Bits n) (Bits n) (Physical a n ℓ) := code.map .gate

theorem positiveWorkGateEval_succ (a n ℓ : ℕ) (hℓ : 0<ℓ+1) :
    positiveWorkGateEval a n (ℓ+1) hℓ=workGateEval a n ℓ := rfl

theorem positiveWorkMacro_succ (a n ℓ : ℕ) (code : List (WorkGate a)) :
    positiveWorkMacro a n (ℓ+1) code=workMacro a n ℓ code := rfl

theorem positiveWorkMacro_counts (a n ℓ : ℕ) (hℓ : 0<ℓ) (code : List (WorkGate a)) :
    ((positiveWorkMacro a n ℓ code).toQuery (positiveWorkGateEval a n ℓ hℓ)).matrixQueries=0 ∧
    ((positiveWorkMacro a n ℓ code).toQuery (positiveWorkGateEval a n ℓ hℓ)).vectorQueries=0 ∧
    (positiveWorkMacro a n ℓ code).workGates=code.length := by
  cases ℓ with
  | zero => omega
  | succ ℓ => exact workMacro_counts a n ℓ code

theorem positiveWorkMacro_intertwines (a n ℓ : ℕ) (hℓ : 0<ℓ)
    {κ s ŝ : ℝ} (h : BudgetParameters κ s ŝ)
    (UA : Matrix.unitaryGroup (Bits a × Bits n) ℂ) (Ub : Matrix.unitaryGroup (Bits n) ℂ) :
    (((positiveWorkMacro a n ℓ (preparationWorkCode a h)).toQuery
      (positiveWorkGateEval a n ℓ hℓ)).eval UA Ub).val * basisInsertion (clean a n ℓ)=
      basisInsertion (clean a n ℓ)*
        (padHom (cachedWork (finitePreparationWork (D := Fin 4 × Bits n)
          (GraphEncoding.physicalSignalZero (fun _ : Fin a=>false)) h
          (by have := h.kappa_pos; positivity : 0<1+κ⁻¹)))).val := by
  cases ℓ with
  | zero => omega
  | succ ℓ =>
    rw [positiveWorkMacro_succ,positiveWorkGateEval_succ]
    exact workMacro_intertwines a n ℓ h UA Ub

end OptimalQLS.Preparation.CompilerAttachment
