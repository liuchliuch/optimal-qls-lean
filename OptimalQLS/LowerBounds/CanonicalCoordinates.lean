import OptimalQLS.LowerBounds.FiniteCoordinates
import OptimalQLS.Problem

/-!
# Conventional zero-input and zero-signal coordinates for the hard family

The data equivalence explicitly sends the computational input0 to the common
source-preparation input. Signal0 is explicitly the Boolean false sector.
All matrices and full oracles are transported by these fixed permutations.
-/
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
namespace OptimalQLS.LowerBounds
open Matrix

theorem hardOutputDimension_pos (N : ℕ) : 0 < hardOutputDimension N := by
  rw [hardOutputDimension, hardFamily_dimension]
  omega

instance hardOutputDimension_neZero (N : ℕ) : NeZero (hardOutputDimension N) :=
  ⟨Nat.ne_of_gt (hardOutputDimension_pos N)⟩

def hardPreparationInput (N : ℕ) : HardFamilyIndex N := .inl (.inl ())

def canonicalDataCoordinates (N : ℕ) : Fin (hardOutputDimension N) ≃ HardFamilyIndex N :=
  (Equiv.swap 0 ((hardOutputCoordinates N).symm (hardPreparationInput N))).trans (hardOutputCoordinates N)

@[simp] theorem canonicalDataCoordinates_zero (N : ℕ) :
    canonicalDataCoordinates N 0 = hardPreparationInput N := by
  simp [canonicalDataCoordinates]

def canonicalSignalCoordinates (N : ℕ) :
    (OptimalQLS.SignalIndex 1 × Fin (hardOutputDimension N)) ≃ (Bool × HardFamilyIndex N) :=
  Equiv.prodCongr finTwoEquiv (canonicalDataCoordinates N)

@[simp] theorem canonicalSignalCoordinates_zero (N : ℕ) (i : Fin (hardOutputDimension N)) :
    canonicalSignalCoordinates N (0, i) = (false, canonicalDataCoordinates N i) := rfl

def canonicalHardMatrix (N : ℕ) [NeZero N] {m : ℕ} (kappa : ℝ) (z : BitString m) :
    Matrix (Fin (hardOutputDimension N)) (Fin (hardOutputDimension N)) ℂ :=
  (hardFamilyMatrix N kappa z).submatrix (canonicalDataCoordinates N) (canonicalDataCoordinates N)

def canonicalHardSource (N m : ℕ) [NeZero N] (kappa estimate : ℝ) : OptimalQLS.DataSpace (hardOutputDimension N) :=
  WithLp.toLp 2 (hardFamilySource N m kappa estimate ∘ canonicalDataCoordinates N)

def canonicalPerturbedSource (N m : ℕ) [NeZero N] (kappa estimate : ℝ) : OptimalQLS.DataSpace (hardOutputDimension N) :=
  WithLp.toLp 2 (hardFamilyPerturbedSource N m kappa estimate ∘ canonicalDataCoordinates N)

def canonicalHardEncoding {N m : ℕ} [NeZero N] {kappa : ℝ} (hk : 4 ≤ kappa) (z : BitString m) :
    Matrix.unitaryGroup (OptimalQLS.SignalIndex 1 × Fin (hardOutputDimension N)) ℂ :=
  OptimalQLS.rewireUnitary (canonicalSignalCoordinates N).symm (hardFamilyEncoding (N := N) hk z)

def canonicalHardPreparation {N m : ℕ} [NeZero N] {kappa estimate : ℝ}
    (hk : 4 ≤ kappa) (he : 1 ≤ estimate) (hek : estimate ≤ kappa)
    (hN : N = 2 * historyPadding kappa + 2 * m) : Matrix.unitaryGroup (Fin (hardOutputDimension N)) ℂ :=
  OptimalQLS.rewireUnitary (canonicalDataCoordinates N).symm (hardFamilyPreparation hk he hek hN)

def canonicalPerturbedPreparation {N m : ℕ} [NeZero N] {kappa estimate : ℝ}
    (hk : 4 ≤ kappa) (he : 1 ≤ estimate) (hek : estimate ≤ kappa)
    (hN : N = 2 * historyPadding kappa + 2 * m) : Matrix.unitaryGroup (Fin (hardOutputDimension N)) ℂ :=
  OptimalQLS.rewireUnitary (canonicalDataCoordinates N).symm (hardFamilyPerturbedPreparation hk he hek hN)

theorem canonicalHardPreparation_prepares {N m : ℕ} [NeZero N] {kappa estimate : ℝ}
    (hk : 4 ≤ kappa) (he : 1 ≤ estimate) (hek : estimate ≤ kappa)
    (hN : N = 2 * historyPadding kappa + 2 * m) (i : Fin (hardOutputDimension N)) :
    canonicalHardPreparation hk he hek hN i 0 = canonicalHardSource N m kappa estimate i := by
  change (hardFamilyPreparation hk he hek hN) (canonicalDataCoordinates N i) (canonicalDataCoordinates N 0) = _
  rw [canonicalDataCoordinates_zero]
  exact hardFamilyPreparation_prepares hk he hek hN _

theorem canonicalPerturbedPreparation_prepares {N m : ℕ} [NeZero N] {kappa estimate : ℝ}
    (hk : 4 ≤ kappa) (he : 1 ≤ estimate) (hek : estimate ≤ kappa)
    (hN : N = 2 * historyPadding kappa + 2 * m) (i : Fin (hardOutputDimension N)) :
    canonicalPerturbedPreparation hk he hek hN i 0 = canonicalPerturbedSource N m kappa estimate i := by
  change (hardFamilyPerturbedPreparation hk he hek hN) (canonicalDataCoordinates N i) (canonicalDataCoordinates N 0) = _
  rw [canonicalDataCoordinates_zero]
  exact hardFamilyPerturbedPreparation_prepares hk he hek hN _

theorem canonicalHardEncoding_signalBlock {N m : ℕ} [NeZero N] {kappa : ℝ} (hk : 4 ≤ kappa) (z : BitString m) :
    OptimalQLS.signalBlock (0 : OptimalQLS.SignalIndex 1) (canonicalHardEncoding (N := N) hk z) = canonicalHardMatrix N kappa z := by
  ext i j
  rw [OptimalQLS.signalBlock_entries]
  change (hardFamilyEncoding (N := N) hk z) (canonicalSignalCoordinates N (0, i))
    (canonicalSignalCoordinates N (0, j)) = _
  rw [canonicalSignalCoordinates_zero, canonicalSignalCoordinates_zero,
    ← OptimalQLS.signalBlock_entries false (hardFamilyEncoding (N := N) hk z) (canonicalDataCoordinates N i) (canonicalDataCoordinates N j)]
  have h := OptimalQLS.exact_block_eq (hardFamilyEncoding_exact (N := N) hk z)
  simp only [one_smul] at h
  rw [← h]
  rfl

theorem canonicalHardEncoding_exact {N m : ℕ} [NeZero N] {kappa : ℝ} (hk : 4 ≤ kappa) (z : BitString m) :
    OptimalQLS.IsBlockEncoding (0 : OptimalQLS.SignalIndex 1) 1 0 (canonicalHardEncoding (N := N) hk z) (canonicalHardMatrix N kappa z) := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  rw [one_smul, canonicalHardEncoding_signalBlock]
  simp

theorem canonicalHardMatrix_inverse {N m : ℕ} [NeZero N] (kappa : ℝ) (z : BitString m) :
    (canonicalHardMatrix N kappa z)⁻¹ =
      ((hardFamilyMatrix N kappa z)⁻¹).submatrix (canonicalDataCoordinates N) (canonicalDataCoordinates N) :=
  Matrix.inv_submatrix_equiv _ _ _

theorem inverse_mulVec_reindex {D E : Type*} [Fintype D] [DecidableEq D] [Fintype E] [DecidableEq E]
    (M : Matrix D D ℂ) (b : D → ℂ) (e : E ≃ D) :
    (M.submatrix e e)⁻¹ *ᵥ (b ∘ e) = (M⁻¹ *ᵥ b) ∘ e := by
  rw [Matrix.inv_submatrix_equiv, Matrix.submatrix_mulVec_equiv]
  have hb : (b ∘ e) ∘ e.symm = b := by funext i; simp
  rw [hb]

theorem canonicalHardMatrix_isUnit {N m : ℕ} [NeZero N] {kappa : ℝ} (hk : 4 ≤ kappa) (z : BitString m) :
    IsUnit (canonicalHardMatrix N kappa z) := by
  rw [canonicalHardMatrix, Matrix.isUnit_submatrix_equiv]
  exact hardFamilyMatrix_isUnit hk z

theorem canonicalHardMatrix_inverse_norm {N m : ℕ} [NeZero N] {kappa : ℝ} (hk : 4 ≤ kappa) (z : BitString m) :
    ‖Ring.inverse (canonicalHardMatrix N kappa z)‖ = kappa := by
  rw [← Matrix.nonsing_inv_eq_ringInverse, canonicalHardMatrix_inverse, matrix_norm_reindex]
  exact hardFamilyMatrix_inverse_norm hk z

theorem canonicalHardMatrix_norm {N m : ℕ} [NeZero N] {kappa : ℝ} (hk : 4 ≤ kappa)
    (hN : N = 2 * historyPadding kappa + 2 * m) (z : BitString m) :
    ‖canonicalHardMatrix N kappa z‖ = 1 := by
  rw [canonicalHardMatrix, matrix_norm_reindex]
  exact hardFamilyMatrix_norm hk hN z

theorem canonicalHardMatrix_hermitian {N m : ℕ} [NeZero N] (kappa : ℝ) (z : BitString m) :
    (canonicalHardMatrix N kappa z).IsHermitian := (hardFamilyMatrix_hermitian kappa z).submatrix _

theorem canonicalHardMatrix_real {N m : ℕ} [NeZero N] (kappa : ℝ) (z : BitString m) :
    EntrywiseReal (canonicalHardMatrix N kappa z) := fun i j => hardFamilyMatrix_entrywiseReal kappa z _ _

end OptimalQLS.LowerBounds
