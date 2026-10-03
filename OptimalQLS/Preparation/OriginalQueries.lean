import OptimalQLS.Preparation.CompilerQueries
import OptimalQLS.GraphEncoding.Proposition43

/-! # Original matrix/source oracle substitution for finite preparation -/
noncomputable section
set_option synthInstance.maxSize 2048
namespace OptimalQLS.Preparation
open Matrix TransducerCompiler GraphEncoding
variable {S D : Type*} [Fintype S] [DecidableEq S] [Fintype D] [DecidableEq D]

abbrev PreparationData (S D : Type*) := Bool × (PhysicalSignal S × (Fin 4 × D))

def preparationGraphCircuit (S D : Type*) [Fintype S] [DecidableEq S]
    [Fintype D] [DecidableEq D] (κ : ℝ) (hκ : 0<κ) :
    QueryCircuit (S × D) (PreparationData S D) (PreparationData S D) :=
  (elementaryGraphCircuit S D (PreparationData S D) κ hκ).lift
    (signalLiftPort Bool (PhysicalSignal S × (Fin 4 × D)))

def preparationReflectionCircuit (S : Type*) [Fintype S] [DecidableEq S] (i₀ : D) :
    QueryCircuit (S × D) D (PreparationData S D) :=
  ((inputReflectionOnSignalCircuit (A := S × D) (1 : Fin 4) i₀).lift
    (signalLiftPort (PhysicalSignal S) (Fin 4 × D))).lift
      (signalLiftPort Bool (PhysicalSignal S × (Fin 4 × D)))

theorem preparationGraphCircuit_eval (κ : ℝ) (hκ : 0<κ)
    (UA : Matrix.unitaryGroup (S × D) ℂ) (U₂ : Matrix.unitaryGroup (PreparationData S D) ℂ) :
    (preparationGraphCircuit S D κ hκ).eval UA U₂=doubleOracle (physicalEncoding κ hκ UA) := by
  rw [preparationGraphCircuit,QueryCircuit.lift_eval,elementaryGraphCircuit_eval,signalLiftPort_apply]
  rfl

theorem preparationReflectionCircuit_eval (i₀ : D)
    (UA : Matrix.unitaryGroup (S × D) ℂ) (Ub : Matrix.unitaryGroup D ℂ) :
    (preparationReflectionCircuit S i₀).eval UA Ub=
      doubleOracle (signalLift (S := PhysicalSignal S)
        (preparedReflection (signalLift (S := Fin 4) Ub) (1,i₀))) := by
  rw [preparationReflectionCircuit,QueryCircuit.lift_eval,QueryCircuit.lift_eval,
    inputReflectionOnSignalCircuit_eval,signalLiftPort_apply,signalLiftPort_apply]
  rfl

theorem preparationGraphCircuit_counts (κ : ℝ) (hκ : 0<κ) :
    (preparationGraphCircuit S D κ hκ).matrixQueries=2 ∧
      (preparationGraphCircuit S D κ hκ).vectorQueries=0 := by
  simpa only [preparationGraphCircuit,(QueryCircuit.lift_counts _ _).1,
    (QueryCircuit.lift_counts _ _).2] using (elementaryGraphCircuit_counts
      (S := S) (D := D) (B := PreparationData S D) κ hκ).elim (fun ha hb => And.intro ha hb.1)

theorem preparationReflectionCircuit_counts (i₀ : D) :
    (preparationReflectionCircuit S i₀).matrixQueries=0 ∧
      (preparationReflectionCircuit S i₀).vectorQueries=2 := by
  simpa only [preparationReflectionCircuit,(QueryCircuit.lift_counts _ _).1,
    (QueryCircuit.lift_counts _ _).2] using inputReflectionOnSignalCircuit_counts
      (A := S × D) (1 : Fin 4) i₀

/-- The final preparation instruction list calls the original full U_A and U_b. -/
def originalPreparationCircuit (s₀ : S) (i₀ : D) {κ s ŝ : ℝ} (h : BudgetParameters κ s ŝ) :
    QueryCircuit (S × D) D (SynthSpace (PreparationData S D) (preparationExponent κ)) :=
  ((compilerQueryCircuit
    (finitePreparationWork (D := Fin 4 × D) (physicalSignalZero s₀) h
      (by have := h.kappa_pos; positivity : 0<1+κ⁻¹)) (preparationCompiler κ ŝ)).substituteMatrix
        (preparationGraphCircuit S D κ h.kappa_pos)).substituteVector
          (preparationReflectionCircuit S i₀)

/-- Whole-unitary equality retains all off-block oracle behavior. -/
theorem originalPreparationCircuit_eval (s₀ : S) (i₀ : D) {κ s ŝ : ℝ}
    (h : BudgetParameters κ s ŝ) (UA : Matrix.unitaryGroup (S × D) ℂ)
    (Ub : Matrix.unitaryGroup D ℂ) :
    (originalPreparationCircuit s₀ i₀ h).eval UA Ub=
      (preparationCompiler κ ŝ).eval
        (finitePreparationWork (D := Fin 4 × D) (physicalSignalZero s₀) h
          (by have := h.kappa_pos; positivity : 0<1+κ⁻¹))
        (doubleOracle (physicalEncoding κ h.kappa_pos UA))
        (doubleOracle (signalLift (S := PhysicalSignal S)
          (preparedReflection (signalLift (S := Fin 4) Ub) (1,i₀)))) := by
  rw [originalPreparationCircuit,QueryCircuit.substituteVector_eval,
    QueryCircuit.substituteMatrix_eval,preparationGraphCircuit_eval,
    preparationReflectionCircuit_eval,compilerQueryCircuit_eval]

/-- Exact independent counts after both literal substitutions. -/
theorem originalPreparationCircuit_counts (s₀ : S) (i₀ : D) {κ s ŝ : ℝ}
    (h : BudgetParameters κ s ŝ) :
    (originalPreparationCircuit s₀ i₀ h).matrixQueries=2*mainBudget κ ∧
      (originalPreparationCircuit s₀ i₀ h).vectorQueries=2*reflectionBudget κ ŝ := by
  have hc := complete_exact_counts h.layout 0 (preparationPeriod κ ŝ)
    h.layout_D₁_dyadic h.layout_D₂_dyadic
  have ho := compile_exact_counts h.layout
  have h₁ : (preparationCompiler κ ŝ).firstCalls=mainBudget κ :=
    hc.2.1.trans (ho.2.1.symm.trans h.layout_exact_counts.2.1)
  have h₂ : (preparationCompiler κ ŝ).secondCalls=reflectionBudget κ ŝ :=
    hc.2.2.trans (ho.2.2.symm.trans h.layout_exact_counts.2.2)
  simp only [originalPreparationCircuit,(QueryCircuit.substituteVector_counts _ _).1,
    (QueryCircuit.substituteVector_counts _ _).2,(QueryCircuit.substituteMatrix_counts _ _).1,
    (QueryCircuit.substituteMatrix_counts _ _).2,(compilerQueryCircuit_counts _ _).1,
    (compilerQueryCircuit_counts _ _).2,(preparationGraphCircuit_counts (S := S) (D := D) κ h.kappa_pos).1,
    (preparationGraphCircuit_counts (S := S) (D := D) κ h.kappa_pos).2,
    (preparationReflectionCircuit_counts (S := S) i₀).1,
    (preparationReflectionCircuit_counts (S := S) i₀).2,h₁,h₂,mul_zero,zero_add,add_zero]
  omega


/-- The one initial U_b call is explicit, independently of all reflection calls. -/
def preparationSourcePort (S D : Type*) [Fintype S] [DecidableEq S]
    [Fintype D] [DecidableEq D] (ℓ : ℕ) :
    QueryPort D (SynthSpace (PreparationData S D) ℓ) :=
  (compilerDataPort (PreparationData S D) ℓ .pub).comp
    ((signalLiftPort Bool (PhysicalSignal S × (Fin 4 × D))).comp
      ((signalLiftPort (PhysicalSignal S) (Fin 4 × D)).comp (signalLiftPort (Fin 4) D)))

theorem preparationSourcePort_eval {ℓ : ℕ} (Ub : Matrix.unitaryGroup D ℂ) :
    (preparationSourcePort S D ℓ).apply Ub=
      (compilerDataPort (PreparationData S D) ℓ .pub).apply
        (doubleOracle (signalLift (S := PhysicalSignal S) (signalLift (S := Fin 4) Ub))) := by
  simp only [preparationSourcePort,QueryPort.comp_apply,signalLiftPort_apply]
  rfl

theorem preparationSourcePort_input {ℓ : ℕ} (s₀ : S) (b : Layout (2^ℓ))
    (Ub : Matrix.unitaryGroup D ℂ) (x : D → ℂ) :
    ((preparationSourcePort S D ℓ).apply Ub).val*ᵥ
      synthInput b (preparationInternal (physicalSignalZero s₀)
        (signalInjection (1 : Fin 4)*ᵥx)) =
      synthInput b (preparationInternal (physicalSignalZero s₀)
        (signalInjection (1 : Fin 4)*ᵥ(Ub.val*ᵥx))) := by
  rw [preparationSourcePort_eval,compilerDataPort_input]
  congr 1
  rw [preparationInternal,doubleOracle_apply,Matrix.mulVec_zero,
    signalLift_injection,signalLift_injection]
  rfl

def originalPreparationAlgorithm (s₀ : S) (i₀ : D) {κ s ŝ : ℝ} (h : BudgetParameters κ s ŝ) :
    QueryCircuit (S × D) D (SynthSpace (PreparationData S D) (preparationExponent κ)) :=
  [.vectorCall (preparationSourcePort S D (preparationExponent κ)) false] ++
    originalPreparationCircuit s₀ i₀ h

theorem originalPreparationAlgorithm_counts (s₀ : S) (i₀ : D) {κ s ŝ : ℝ}
    (h : BudgetParameters κ s ŝ) :
    (originalPreparationAlgorithm s₀ i₀ h).matrixQueries=2*mainBudget κ ∧
      (originalPreparationAlgorithm s₀ i₀ h).vectorQueries=2*reflectionBudget κ ŝ+1 := by
  have hc := originalPreparationCircuit_counts s₀ i₀ h
  simp [originalPreparationAlgorithm,QueryCircuit.matrixQueries_append,
    QueryCircuit.vectorQueries_append,QueryCircuit.matrixQueries,QueryCircuit.vectorQueries,
    hc.1,hc.2,Nat.add_comm]

theorem originalPreparationAlgorithm_budgets (s₀ : S) (i₀ : D) {κ s ŝ : ℝ}
    (h : BudgetParameters κ s ŝ) :
    ((originalPreparationAlgorithm s₀ i₀ h).matrixQueries : ℝ)<512000000*κ ∧
      ((originalPreparationAlgorithm s₀ i₀ h).vectorQueries : ℝ)<120000001*(κ/s) := by
  rw [(originalPreparationAlgorithm_counts s₀ i₀ h).1,
    (originalPreparationAlgorithm_counts s₀ i₀ h).2]
  have hs : 0<s := by linarith [h.scale_ge_one]
  have hk : 1≤κ/s := (le_div_iff₀ hs).mpr (by simpa using h.scale_le_kappa)
  push_cast
  constructor
  · linarith [h.mainBudget_bounds.2]
  · linarith [h.reflectionBudget_scale_bound]


/-- The code depends on the supplied estimate, never on the hidden exact
solution norm used only to verify its budgets. -/
theorem originalPreparationAlgorithm_uniform_in_scale (s₀ : S) (i₀ : D)
    {κ s t ŝ : ℝ} (h : BudgetParameters κ s ŝ) (h' : BudgetParameters κ t ŝ) :
    originalPreparationAlgorithm s₀ i₀ h=originalPreparationAlgorithm s₀ i₀ h' := rfl

end OptimalQLS.Preparation
