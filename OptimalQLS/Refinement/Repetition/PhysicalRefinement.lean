import OptimalQLS.Refinement.Repetition.Physical
import OptimalQLS.Refinement.Repetition.Transport

/-! The measured/reset branch matrices are exactly the matrices used by the
finite repeat program, after a mere computational-basis reindexing. -/
noncomputable section
namespace OptimalQLS.Refinement.Repetition.Physical
open Matrix LowerBounds
set_option maxHeartbeats 200000
variable {Aux Data : Type*} [Fintype Aux] [DecidableEq Aux]
  [Fintype Data] [DecidableEq Data] {d w : ℕ}

theorem physicalReset_matrix {I : Type*} [Fintype I] [DecidableEq I]
    (target observed : Bits I) :
    feedbackMatrix target Finset.univ.toList observed *
      patternMeasurement Finset.univ.toList observed =
      (fun i j => if i = target then if j = observed then 1 else 0 else 0) := by
  ext i j
  have h := congrFun (physical_reset_branch target observed (Pi.single j 1)) i
  by_cases hi : i = target <;> by_cases hj : j = observed <;>
    simpa [Matrix.mulVec_single_one, ket, Pi.single_apply, hi, hj, eq_comm] using h

def physicalReject (a : Bits Aux) (target observed : Bits (Aux ⊕ Data)) :
    Matrix (Bits (Aux ⊕ Data)) (Bits (Aux ⊕ Data)) ℂ :=
  if ∀ i, observed (.inl i) = a i then 0 else
    feedbackMatrix target Finset.univ.toList observed *
      patternMeasurement Finset.univ.toList observed

theorem reindexed_aux_range (E : Bits (Aux ⊕ Data) ≃ Fin w) (F : Bits Data ≃ Fin d)
    (a : Bits Aux) (observed : Bits (Aux ⊕ Data)) :
    (∃ k, reindexEmbedding E F (auxEmbedding a) k = E observed) ↔
      ∀ i, observed (.inl i) = a i := by
  constructor
  · rintro ⟨k, hk⟩
    apply (auxEmbedding_range a observed).mp
    exact ⟨F.symm k, E.injective hk⟩
  · intro h
    obtain ⟨x, hx⟩ := (auxEmbedding_range a observed).mpr h
    refine ⟨F x, ?_⟩
    simp [reindexEmbedding, hx]

theorem physicalAccept_matrix (a : Bits Aux) :
    auxAccept (Data := Data) a * auxMeasurement a = auxAccept a := by
  ext i j
  rw [auxMeasurement_exact, Matrix.mul_diagonal]
  by_cases h : auxEmbedding a i = j
  · subst j; simp [auxAccept]
  · simp [auxAccept, h]

/-- The accepted Kraus matrix in the actual program is the coherent data
extraction after single-bit auxiliary measurements. -/
theorem physicalAccept_reindex (E : Bits (Aux ⊕ Data) ≃ Fin w) (F : Bits Data ≃ Fin d)
    (a : Bits Aux) :
    (auxAccept (Data := Data) a * auxMeasurement a).submatrix F.symm E.symm = acceptMatrix (reindexEmbedding E F (auxEmbedding a)) := by
  rw [physicalAccept_matrix]
  ext i j
  simp [auxAccept, acceptMatrix, reindexEmbedding, Equiv.eq_symm_apply]

/-- Every rejected branch of the actual repeat-program instrument is realized
by computational-basis measurements and at most one conditional X per wire.
This is literal matrix equality, not a supplied channel-correctness premise. -/
theorem physicalReject_reindex (E : Bits (Aux ⊕ Data) ≃ Fin w) (F : Bits Data ≃ Fin d)
    (a : Bits Aux) (target observed : Bits (Aux ⊕ Data)) :
    (physicalReject a target observed).submatrix E.symm E.symm =
      resetMatrix (reindexEmbedding E F (auxEmbedding a)) (E target) (E observed) := by
  unfold physicalReject resetMatrix
  simp only [reindexed_aux_range]
  split_ifs with h
  · rfl
  · rw [physicalReset_matrix]
    ext i j
    simp [Matrix.submatrix, abortBasisKraus, Equiv.symm_apply_eq]

end OptimalQLS.Refinement.Repetition.Physical
