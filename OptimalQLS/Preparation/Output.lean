import OptimalQLS.Alignment.FiniteAlignment
import OptimalQLS.Preparation.GraphPromises
import OptimalQLS.RefinementAnalytic

noncomputable section
set_option synthInstance.maxSize 2048
namespace OptimalQLS.Preparation
open Matrix TransducerCompiler BinaryClock Alignment
variable {S D : Type*} [Fintype S] [DecidableEq S] [Fintype D] [DecidableEq D]

/-- Any actual coordinate subspace measurement is contractive in Hilbert norm. -/
theorem coordinate_slice_norm_le {I J : Type*} [Fintype I] [Fintype J]
    (f : I ↪ J) (v : EuclideanSpace ℂ J) :
    ‖WithLp.toLp 2 (fun i => v (f i))‖≤‖v‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.norm_sq_eq,EuclideanSpace.norm_sq_eq]
  change (∑ i : I, ‖v (f i)‖^2)≤∑ j : J, ‖v j‖^2
  classical
  simpa only [Finset.sum_map] using
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ (Finset.univ.map f))
      (fun j _ _ => sq_nonneg ‖v j‖))

def preparationInputIndex {ℓ : ℕ} (s₀ : S) : D ↪ SynthSpace (Bool × (S × D)) ℓ where
  toFun i := (false,(((false,(s₀,i)),.pub),(fun _ => false),(fun _ => false)))
  inj' := by intro i j h; exact congrArg (fun p => p.2.1.1.2.2) h

theorem zeroAuxiliaryOutput_norm_le {ℓ : ℕ} (s₀ : S)
    (v : SynthSpace (Bool × (S × D)) ℓ → ℂ) :
    ‖WithLp.toLp 2 (zeroAuxiliaryOutput s₀ v)‖≤‖WithLp.toLp 2 v‖ :=
  coordinate_slice_norm_le (preparationInputIndex s₀) (WithLp.toLp 2 v)

theorem zeroAuxiliaryOutput_target {ℓ : ℕ} (s₀ : S) (b : Layout (2^ℓ)) (x : D → ℂ) :
    zeroAuxiliaryOutput s₀ (synthInput b (preparationInternal s₀ x))=x := by
  ext i
  simp [zeroAuxiliaryOutput,synthInput,synthClean,cachedInput,cleanVector,inputToBits,
    spaceBitsEquiv,inputState,preparationInternal,doubleVector,Layout.zero]

theorem zeroAuxiliaryOutput_sub {ℓ : ℕ} (s₀ : S)
    (v w : SynthSpace (Bool × (S × D)) ℓ → ℂ) :
    zeroAuxiliaryOutput s₀ (v-w)=zeroAuxiliaryOutput s₀ v-zeroAuxiliaryOutput s₀ w := rfl

/-- The actual accepted component is close to the ideal coarse vector. -/
theorem zeroAuxiliaryOutput_distance {ℓ : ℕ} (s₀ : S) (b : Layout (2^ℓ))
    (v : SynthSpace (Bool × (S × D)) ℓ → ℂ) (x : D → ℂ) :
    ‖WithLp.toLp 2 (zeroAuxiliaryOutput s₀ v-x)‖≤
      ‖WithLp.toLp 2 (v-synthInput b (preparationInternal s₀ x))‖ := by
  have h := zeroAuxiliaryOutput_norm_le s₀ (v-synthInput b (preparationInternal s₀ x))
  rwa [zeroAuxiliaryOutput_sub,zeroAuxiliaryOutput_target] at h

/-- Exact normalization of the clean-clock input. -/
theorem inputState_norm {N : Type*} [Fintype N] [DecidableEq N] {K : ℕ}
    (k : Fin K) (x : N → ℂ) :
    ‖WithLp.toLp 2 (inputState k x)‖=‖WithLp.toLp 2 x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  have hu : (Finset.univ : Finset Label)={.pub,.internal,.first,.second} := by decide
  simp [EuclideanSpace.norm_sq_eq,Fintype.sum_prod_type,hu,inputState,apply_ite]

theorem synthInput_norm {N : Type*} [Fintype N] [DecidableEq N] {ℓ : ℕ}
    (b : Layout (2^ℓ)) (x : N → ℂ) :
    ‖WithLp.toLp 2 (synthInput b x)‖=‖WithLp.toLp 2 x‖ := by
  rw [synthInput,synthClean_norm,cachedInput,cleanVector_norm,inputToBits_norm,inputState_norm]

theorem preparationInternal_norm (s₀ : S) (x : D → ℂ) :
    ‖WithLp.toLp 2 (preparationInternal s₀ x)‖=‖WithLp.toLp 2 x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simpa only [energy_eq_norm_sq] using preparationInternal_energy s₀ x

theorem finitePreparedState_norm (s₀ : S) {κ s ŝ α : ℝ}
    (h : BudgetParameters κ s ŝ) (hα : 0<α)
    (V : Matrix.unitaryGroup (S × D) ℂ) (Ub : Matrix.unitaryGroup D ℂ)
    (i₀ : D) (e : D → ℂ) :
    ‖WithLp.toLp 2 (finitePreparedState s₀ h hα V Ub i₀ e)‖=‖WithLp.toLp 2 e‖ := by
  exact (unitary_norm ((preparationCompiler κ ŝ).eval (finitePreparationWork s₀ h hα)
    (doubleOracle V) (doubleOracle (signalLift (S := S) (preparedReflection Ub i₀))))
      (WithLp.toLp 2 (synthInput h.layout (preparationInternal s₀ e)))).trans
        ((synthInput_norm h.layout _).trans (preparationInternal_norm s₀ e))

end OptimalQLS.Preparation
