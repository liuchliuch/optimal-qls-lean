import OptimalQLS.Refinement.PhysicalMeasurement
import OptimalQLS.PolynomialTransform.NamedCircuit

/-! Normalized primitives of a costed physical program. A discarded auxiliary
register is implemented by its full partial-trace Kraus family. -/
noncomputable section
open scoped BigOperators
namespace OptimalQLS.Refinement.CostedExecution
open Matrix LowerBounds Repetition.Physical
set_option maxHeartbeats 600000
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
variable {Aux Data : Type*} [Fintype Aux] [DecidableEq Aux]
  [Fintype Data] [DecidableEq Data] {d w : ℕ}

abbrev Wire (Aux Data : Type*) := Aux ⊕ Data
abbrev State (Aux Data : Type*) := Wire Aux Data → Bool

/-- Reindexing is a coordinate convention, not an extra unitary. -/
def bitKraus (E : State Aux Data ≃ Fin w) (i : Wire Aux Data) (b : Bool) :
    Matrix (Fin w) (Fin w) ℂ :=
  (bitProjector i b).submatrix E.symm E.symm

theorem bitKraus_complete (E : State Aux Data ≃ Fin w) (i : Wire Aux Data) :
    (bitKraus E i false).conjTranspose * bitKraus E i false +
      (bitKraus E i true).conjTranspose * bitKraus E i true = 1 := by
  simp only [bitKraus, Matrix.conjTranspose_submatrix]
  rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]
  change ((bitProjector i false).conjTranspose * bitProjector i false +
    (bitProjector i true).conjTranspose * bitProjector i true).submatrix E.symm E.symm = _
  rw [bitProjector_complete, Matrix.submatrix_one_equiv]

/-- Outcome 0 is false, outcome 1 is true. -/
def outcome : Fin 2 ≃ Bool where
  toFun i := i == 1
  invFun b := if b then 1 else 0
  left_inv i := by fin_cases i <;> rfl
  right_inv b := by cases b <;> rfl

theorem bitKraus_normalized (E : State Aux Data ≃ Fin w) (i : Wire Aux Data) :
    (∑ b : Fin 2, (bitKraus E i (outcome b)).conjTranspose * bitKraus E i (outcome b)) = 1 := by
  rw [Fin.sum_univ_two]
  exact bitKraus_complete E i

/-- Splitting the workspace into the existing auxiliary and data factors. -/
def split (E : State Aux Data ≃ Fin w) (F : (Data → Bool) ≃ Fin d) :
    Fin w ≃ (Aux → Bool) × Fin d where
  toFun j := (fun i => E.symm j (.inl i), F (fun i => E.symm j (.inr i)))
  invFun p := E (Sum.elim p.1 (F.symm p.2))
  left_inv j := by apply E.symm.injective; simp; funext i; cases i <;> rfl
  right_inv p := by rcases p with ⟨a,x⟩; simp

/-- The a-th Kraus map of ordinary partial trace over all auxiliary bits. -/
def discardKraus (E : State Aux Data ≃ Fin w) (F : (Data → Bool) ≃ Fin d)
    (a : Aux → Bool) : Matrix (Fin d) (Fin w) ℂ :=
  fun i j => if split E F j = (a,i) then 1 else 0

theorem discardKraus_mulVec (E : State Aux Data ≃ Fin w) (F : (Data → Bool) ≃ Fin d)
    (a : Aux → Bool) (v : Fin w → ℂ) :
    discardKraus E F a *ᵥ v = fun i => v ((split E F).symm (a,i)) := by
  ext i
  simp [discardKraus, Matrix.mulVec, dotProduct, Equiv.apply_eq_iff_eq_symm_apply]

theorem discardKraus_gram (E : State Aux Data ≃ Fin w) (F : (Data → Bool) ≃ Fin d)
    (a : Aux → Bool) (i j : Fin w) :
    ((discardKraus E F a).conjTranspose * discardKraus E F a) i j =
      if (split E F i).1 = a then if i = j then 1 else 0 else 0 := by
  simp only [discardKraus, Matrix.mul_apply, Matrix.conjTranspose_apply, apply_ite,
    star_one, star_zero, Prod.ext_iff, Prod.fst, Prod.snd]
  by_cases ha : (split E F i).1 = a
  · by_cases hij : i = j
    · subst j; simp [ha]
    · have hj : ¬((split E F j).1 = a ∧ (split E F i).2 = (split E F j).2) := by
        rintro ⟨hja,hjd⟩
        exact hij ((split E F).injective (Prod.ext (ha.trans hja.symm) hjd))
      simp only [ha, true_and, hij, if_false, ite_mul, one_mul, zero_mul]
      rw [Finset.sum_eq_single ((split E F i).2)]
      · simp only [ite_true]
        split_ifs with h
        · exact False.elim (hj ⟨h.1,h.2.symm⟩)
        · simp
      · intro b _ hb; simp [Ne.symm hb]
      · simp
  · simp [ha]

theorem discardKraus_complete (E : State Aux Data ≃ Fin w) (F : (Data → Bool) ≃ Fin d) :
    (∑ a : Aux → Bool, (discardKraus E F a).conjTranspose * discardKraus E F a) = 1 := by
  ext i j
  simp [Matrix.sum_apply, discardKraus_gram, Matrix.one_apply, eq_comm]

/-- This family is exactly partial trace, including for entangled inputs. -/
theorem discard_partialTrace (E : State Aux Data ≃ Fin w) (F : (Data → Bool) ≃ Fin d)
    (X : Matrix (Fin w) (Fin w) ℂ) (i j : Fin d) :
    (∑ a : Aux → Bool, discardKraus E F a * X * (discardKraus E F a).conjTranspose) i j =
      ∑ a : Aux → Bool, X ((split E F).symm (a,i)) ((split E F).symm (a,j)) := by
  simp [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    discardKraus, Equiv.apply_eq_iff_eq_symm_apply]

/-- A physical one-bit Pauli X, with no allocated workspace. -/
def xGate (E : State Aux Data ≃ Fin w) (i : Wire Aux Data) : Matrix.unitaryGroup (Fin w) ℂ :=
  rewireUnitary E (TransducerCompiler.permutation (bitFlipEquiv i))

end OptimalQLS.Refinement.CostedExecution
