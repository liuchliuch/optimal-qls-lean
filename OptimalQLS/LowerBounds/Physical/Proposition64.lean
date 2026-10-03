import OptimalQLS.LowerBounds.Physical.HardFamilyBitCircuit
import OptimalQLS.LowerBounds.Physical.ControlledSimulation

/-! Full Proposition 6.4, including literal controlled/adjoint bit simulation. -/
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 4096
set_option maxRecDepth 2048
namespace OptimalQLS.LowerBounds.Physical
open Matrix PolynomialTransform

/-- Every complete UA call, including arbitrary workspace control, placement,
and adjoint, has one fixed four-query circuit in the controlled-bit QueryPort
model for all z. OrdinaryBitSimulation removes these controls explicitly. -/
theorem proposition64_query_simulation {N m : ℕ} [NeZero N] [NeZero m] {kappa : ℝ}
    (hk : 4 ≤ kappa) (hN : N = 2 * historyPadding kappa + 2 * m)
    {W : Type*} [Fintype W] [DecidableEq W]
    (p : QueryPort (Bool × HardFamilyIndex N) W) (adjoint : Bool) :
    (simulatedQuery p adjoint (hardFamilyBitCircuit hk hN)).matrixQueries = 4 ∧
    (simulatedQuery p adjoint (hardFamilyBitCircuit hk hN)).vectorQueries = 0 ∧
    ∀ z : BitString m,
      ((simulatedQuery p adjoint (hardFamilyBitCircuit hk hN)).eval (standardBitOracle z) 1).val *
        basisInsertion (queryClean (hardOracleClean (N := N) (m := m)) p) =
      basisInsertion (queryClean (hardOracleClean (N := N) (m := m)) p) *
        (p.apply (if adjoint then (hardFamilyEncoding (N := N) hk z)⁻¹ else hardFamilyEncoding hk z)).val := by
  refine ⟨(simulatedQuery_counts _ _ _).1.trans (hardFamilyBitCircuit_counts hk hN).1,
    (simulatedQuery_counts _ _ _).2.trans (hardFamilyBitCircuit_counts hk hN).2, ?_⟩
  intro z
  exact simulatedQuery_intertwines hardOracleClean p adjoint _ _ _ _ (hardFamilyBitCircuit_clean hk hN z)

/-- The simulation scratch embedding is an actual computational isometry. -/
theorem proposition64_query_clean_isometry {N m : ℕ} [NeZero m]
    {W : Type*} [Fintype W] [DecidableEq W]
    (p : QueryPort (Bool × HardFamilyIndex N) W) :
    (basisInsertion (queryClean (hardOracleClean (N := N) (m := m)) p))ᴴ *
      basisInsertion (queryClean (hardOracleClean (N := N) (m := m)) p) = 1 :=
  basisInsertion_isometry _ (queryClean _ _).injective

/-- All source, norm, observable, direction, and complete-oracle clauses at
one concrete history length. Source, full Ub, and s-star have no z argument. -/
theorem proposition64 {N m : ℕ} [NeZero N] [NeZero m] {kappa estimate : ℝ}
    (hk : 4 ≤ kappa) (he : 1 ≤ estimate) (hek : estimate ≤ kappa)
    (hN : N = 2 * historyPadding kappa + 2 * m) :
    (hardFamilyBitCircuit hk hN).matrixQueries = 4 ∧
    (hardFamilyBitCircuit hk hN).vectorQueries = 0 ∧
    Fintype.card (HardFamilyIndex N) = 8 * historyPadding kappa + 8 * m + 4 ∧
    ‖WithLp.toLp 2 (hardFamilySource N m kappa estimate)‖ = 1 ∧
    (∀ i, hardFamilyPreparation hk he hek hN i (.inl (.inl ())) = hardFamilySource N m kappa estimate i) ∧
    estimate / 2 ≤ commonAdjustedScale N m kappa estimate ∧
    commonAdjustedScale N m kappa estimate ≤ 3 * estimate / 2 ∧
    (hardFamilyObservable hk hN).IsHermitian ∧ ‖hardFamilyObservable hk hN‖ ≤ 1 ∧
    ‖WithLp.toLp 2 (dilatedLastDirection (D := HistoryBasis N))‖ = 1 ∧
    ∀ z : BitString m,
      EntrywiseReal (hardFamilyMatrix N kappa z) ∧ (hardFamilyMatrix N kappa z).IsHermitian ∧
      ‖hardFamilyMatrix N kappa z‖ = 1 ∧ ‖(hardFamilyMatrix N kappa z)⁻¹‖ = kappa ∧
      ‖WithLp.toLp 2 ((hardFamilyMatrix N kappa z)⁻¹ *ᵥ hardFamilySource N m kappa estimate)‖ =
        commonAdjustedScale N m kappa estimate ∧
      IsBlockEncoding false 1 0 (hardFamilyEncoding (N := N) hk z) (hardFamilyMatrix N kappa z) ∧
      hardFamilyMatrix N kappa z *ᵥ dilatedLastDirection = kappa⁻¹ • dilatedLastDirection ∧
      inner ℂ (WithLp.toLp 2 (hardFamilySource N m kappa estimate))
        (WithLp.toLp 2 (dilatedLastDirection (D := HistoryBasis N))) = 0 ∧
      inner ℂ (WithLp.toLp 2 ((hardFamilyMatrix N kappa z)⁻¹ *ᵥ hardFamilySource N m kappa estimate))
        (WithLp.toLp 2 (dilatedLastDirection (D := HistoryBasis N))) = 0 ∧
      (5 / 2304 : ℝ) * historyLambda kappa ^ (2*m) ≤
        paritySign z * pureExpectation (hardFamilyObservable hk hN)
          (normalizedHardFamilySolution N kappa estimate z) ∧
      ((hardFamilyBitCircuit hk hN).eval (standardBitOracle z) 1).val *
        basisInsertion (hardOracleClean (N := N) (m := m)) =
      basisInsertion (hardOracleClean (N := N) (m := m)) * (hardFamilyEncoding (N := N) hk z).val := by
  have hs := commonAdjustedScale_bounds hk he hek hN
  refine ⟨(hardFamilyBitCircuit_counts hk hN).1, (hardFamilyBitCircuit_counts hk hN).2,
    ?_, hardFamilySource_norm hk he hek hN, hardFamilyPreparation_prepares hk he hek hN,
    hs.1, hs.2.1, hardFamilyObservable_hermitian hk hN,
    hardFamilyObservable_norm_le_one hk hN, dilatedLastDirection_norm, ?_⟩
  · rw [hardFamily_dimension, hN]
    omega
  · intro z
    exact ⟨hardFamilyMatrix_entrywiseReal kappa z, hardFamilyMatrix_hermitian kappa z,
      hardFamilyMatrix_norm hk hN z, hardFamilyMatrix_inverse_norm hk z,
      hardFamily_solution_norm hk he hek hN z, hardFamilyEncoding_exact hk z,
      (hardFamily_fixed_direction kappa z).2, hardFamily_source_orthogonal_direction kappa estimate,
      hardFamily_solution_orthogonal_direction hk estimate z, hardFamily_observable_signal hk he hek hN z,
      hardFamilyBitCircuit_clean hk hN z⟩

/-- The concrete history length always exists in the proposition's range;
this supplies the arithmetic length parameter of `proposition64`. -/
theorem proposition64_history_length {m : ℕ} [NeZero m] {kappa : ℝ} :
    ∃ N : ℕ, 0 < N ∧ N = 2 * historyPadding kappa + 2 * m := by
  refine ⟨2 * historyPadding kappa + 2 * m, ?_, rfl⟩
  have hm := NeZero.pos m
  omega

end OptimalQLS.LowerBounds.Physical
