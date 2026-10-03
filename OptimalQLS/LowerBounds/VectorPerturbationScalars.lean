import OptimalQLS.LowerBounds.HistoryPowerBounds

/-!
# Exact scalar constants for the pointwise vector perturbation

These are the numerical calculations in Lemma6.5. They do not assert a query
lower bound or assume a hybrid theorem. Matrix-vector and oracle-rotation
constructions must still connect the concrete quantities to the QLS model.
-/
noncomputable section
namespace OptimalQLS.LowerBounds

def vectorPerturbationSize (kappa estimate : ℝ) : ℝ := 5 * estimate / (4 * kappa)

def pairedSolutionNormSquared (kappa estimate sourceNorm : ℝ) : ℝ :=
  (sourceNorm ^ 2 + 25 * estimate ^ 2 / 16) /
    (1 + 25 * estimate ^ 2 / (16 * kappa ^ 2))

def pairedDirectionWeight (estimate sourceNorm : ℝ) : ℝ :=
  (25 * estimate ^ 2 / 16) / (sourceNorm ^ 2 + 25 * estimate ^ 2 / 16)

theorem perturbation_denominator_bounds {kappa estimate : ℝ}
    (hk : 0 < kappa) (he : 0 ≤ estimate) (hek : estimate ≤ kappa) :
    1 ≤ 1 + 25 * estimate ^ 2 / (16 * kappa ^ 2) ∧
      1 + 25 * estimate ^ 2 / (16 * kappa ^ 2) ≤ 41 / 16 := by
  have hk2 : 0 < 16 * kappa ^ 2 := by positivity
  have hs2 : estimate ^ 2 ≤ kappa ^ 2 := by nlinarith
  constructor
  · have hq : 0 ≤ 25 * estimate ^ 2 / (16 * kappa ^ 2) := by positivity
    linarith
  · have hq : 25 * estimate ^ 2 / (16 * kappa ^ 2) ≤ 25 / 16 := by
      apply (div_le_iff₀ hk2).mpr
      nlinarith
    linarith

/-- The manuscript's exact29/41 and61/16 squared-norm bounds. -/
theorem pairedSolutionNormSquared_bounds {kappa estimate sourceNorm : ℝ}
    (hk : 0 < kappa) (he : 0 ≤ estimate) (hek : estimate ≤ kappa)
    (hslo : estimate / 2 ≤ sourceNorm) (hshi : sourceNorm ≤ 3 * estimate / 2) :
    (29 / 41) * estimate ^ 2 ≤ pairedSolutionNormSquared kappa estimate sourceNorm ∧
      pairedSolutionNormSquared kappa estimate sourceNorm ≤ (61 / 16) * estimate ^ 2 := by
  have hd := perturbation_denominator_bounds hk he hek
  have hdpos : 0 < 1 + 25 * estimate ^ 2 / (16 * kappa ^ 2) := by linarith [hd.1]
  have hnumlo : (29 / 16) * estimate ^ 2 ≤ sourceNorm ^ 2 + 25 * estimate ^ 2 / 16 := by
    nlinarith
  have hnumhi : sourceNorm ^ 2 + 25 * estimate ^ 2 / 16 ≤ (61 / 16) * estimate ^ 2 := by
    nlinarith
  unfold pairedSolutionNormSquared
  constructor
  · apply (le_div_iff₀ hdpos).mpr
    calc
      (29 / 41) * estimate ^ 2 * (1 + 25 * estimate ^ 2 / (16 * kappa ^ 2)) ≤
          (29 / 41) * estimate ^ 2 * (41 / 16) :=
        mul_le_mul_of_nonneg_left hd.2 (by positivity)
      _ = (29 / 16) * estimate ^ 2 := by ring
      _ ≤ _ := hnumlo
  · apply (div_le_iff₀ hdpos).mpr
    exact hnumhi.trans (le_mul_of_one_le_right (by positivity) hd.1)

/-- The same supplied estimate remains valid for the perturbed solution norm. -/
theorem pairedSolutionNorm_factor_two {kappa estimate sourceNorm : ℝ}
    (hk : 0 < kappa) (he : 0 < estimate) (hek : estimate ≤ kappa)
    (hslo : estimate / 2 ≤ sourceNorm) (hshi : sourceNorm ≤ 3 * estimate / 2) :
    Real.sqrt (pairedSolutionNormSquared kappa estimate sourceNorm) / 2 ≤ estimate ∧
      estimate ≤ 2 * Real.sqrt (pairedSolutionNormSquared kappa estimate sourceNorm) := by
  have hb := pairedSolutionNormSquared_bounds hk he.le hek hslo hshi
  have hnonneg : 0 ≤ pairedSolutionNormSquared kappa estimate sourceNorm := by
    linarith [sq_nonneg estimate]
  have hs := Real.sq_sqrt hnonneg
  have hn := Real.sqrt_nonneg (pairedSolutionNormSquared kappa estimate sourceNorm)
  constructor <;> nlinarith

/-- Measuring the fixed least-eigenvalue direction distinguishes the perturbed
normalized solution with probability at least25/61. -/
theorem pairedDirectionWeight_lower {estimate sourceNorm : ℝ} (he : 0 < estimate)
    (hslo : 0 ≤ sourceNorm) (hshi : sourceNorm ≤ 3 * estimate / 2) :
    (25 / 61 : ℝ) ≤ pairedDirectionWeight estimate sourceNorm := by
  have hd : 0 < sourceNorm ^ 2 + 25 * estimate ^ 2 / 16 := by positivity
  unfold pairedDirectionWeight
  apply (le_div_iff₀ hd).mpr
  nlinarith

/-- A useful fixed constant strictly below the pure-state separation. -/
theorem pairedDirectionSeparation_gt_five_eighths {estimate sourceNorm : ℝ}
    (he : 0 < estimate) (hslo : 0 ≤ sourceNorm) (hshi : sourceNorm ≤ 3 * estimate / 2) :
    (5 / 8 : ℝ) < Real.sqrt (pairedDirectionWeight estimate sourceNorm) := by
  have h := pairedDirectionWeight_lower he hslo hshi
  have hn : 0 ≤ pairedDirectionWeight estimate sourceNorm := by linarith
  have hs := Real.sq_sqrt hn
  have hp := Real.sqrt_nonneg (pairedDirectionWeight estimate sourceNorm)
  nlinarith

/-- A success-and-direction event gives constant separation even with a
1/32 conditional probability error and2/3 success on each input. -/
theorem success_direction_event_gap {eps p oldEvent newEvent : ℝ}
    (heps : eps ≤ 1 / 32) (hp : 2 / 3 ≤ p) (hp1 : p ≤ 1)
    (hold : oldEvent ≤ eps) (hnew : p * (25 / 61 - eps) ≤ newEvent) :
    (1 / 5 : ℝ) ≤ newEvent - oldEvent := by
  have hbase : 0 ≤ 25 / 61 - eps := by linarith
  have hmul := mul_le_mul_of_nonneg_right hp hbase
  nlinarith

end OptimalQLS.LowerBounds
