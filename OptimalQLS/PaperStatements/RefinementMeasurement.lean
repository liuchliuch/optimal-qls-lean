import OptimalQLS.PaperStatements.Proposition56
import OptimalQLS.Refinement.PhysicalMeasurement

/-! The success matrix appearing in Proposition 5.6 is a literal product of
one-bit auxiliary measurements on any binary preparation register. -/
noncomputable section
namespace OptimalQLS.PaperStatements
open Matrix PolynomialTransform Refinement Refinement.Repetition
open TransducerCompiler BinaryClock PhysicalMeasurement
set_option synthInstance.maxSize 8192

abbrev RefinementAuxWire (a p : ℕ) := QWire a ⊕ (Fin p ⊕ (QWire (a+4) ⊕ Fin 2))
abbrev RefinementAuxState (a p : ℕ) := CorrectionSignal a × (Bits p × (FilterSignal a × Fin 4))

def refinementAuxCoordinates (a p : ℕ) :
    RefinementAuxState a p ≃ (RefinementAuxWire a p → Bool) :=
  productBits (qCoordinates a) (productBits (Equiv.refl (Bits p))
    (productBits (qCoordinates (a+4)) (HadamardClock.bitsFinEquiv 2).symm))

def refinementSplit (a p n : ℕ) :
    RunSpace a (Bits p) (Bits n) ≃ RefinementAuxState a p × Bits n where
  toFun x := ((x.1,(x.2.1,(x.2.2.1,x.2.2.2.1))),x.2.2.2.2)
  invFun x := (x.1.1,(x.1.2.1,(x.1.2.2.1,(x.1.2.2.2,x.2))))
  left_inv _ := rfl
  right_inv _ := rfl

def refinementCoordinates (a p n : ℕ) :
    (RefinementAuxWire a p ⊕ Fin n → Bool) ≃ RunSpace a (Bits p) (Bits n) :=
  (productBits (refinementAuxCoordinates a p) (Equiv.refl (Bits n))).symm.trans
    (refinementSplit a p n).symm

def refinementPattern (a p : ℕ) (p₀ : Bits p) : RefinementAuxWire a p → Bool :=
  refinementAuxCoordinates a p (physicalZero a,(p₀,(physicalZero (a+4),2)))

theorem refinementCoordinates_accept (a p n : ℕ) (p₀ : Bits p) (x : Bits n) :
    refinementCoordinates a p n (Repetition.Physical.auxEmbedding (refinementPattern a p p₀) x) =
      (physicalZero a,(p₀,(physicalZero (a+4),(2,x)))) := by
  change (refinementSplit a p n).symm
    ((refinementAuxCoordinates a p).symm (refinementAuxCoordinates a p _),x) = _
  rw [Equiv.symm_apply_apply]
  rfl

/-- This is the very `acceptMatrix` used by `proposition56`, not another
existential measurement witness. All preparation, filter and correction bits
are tested only at this final step. -/
theorem refinementSuccess_is_bit_measurement (a p n : ℕ) (p₀ : Bits p) :
    (Repetition.Physical.auxAccept (Data := Fin n) (refinementPattern a p p₀) *
      Repetition.Physical.auxMeasurement (refinementPattern a p p₀)).submatrix
        (Fintype.equivFin (Bits n)).symm
        ((refinementCoordinates a p n).trans (Fintype.equivFin _)).symm =
      acceptMatrix (refinementSuccessEmbedding (D := Bits n) a p₀) := by
  rw [Repetition.Physical.physicalAccept_reindex]
  congr 1
  ext i
  simp only [reindexEmbedding, refinementSuccessEmbedding, Function.Embedding.coeFn_mk,
    Equiv.trans_apply, refinementCoordinates_accept]

/-- Standalone binary-register version of Proposition 5.6. The selected code,
all success/error/resource statements, and the literal bit-measurement matrix
are in one conjunction and use the same success embedding. -/
theorem proposition56_physical (a p n : ℕ) (p₀ : Bits p) {κ ε : ℝ}
    (hκ : 2 ≤ κ) (hε0 : 0 < ε) (hε1 : ε < 1/2) :
    ∃ out : NamedRefinementCircuit a (Bits p) (Bits n) (Bits n),
      RefinementGuarantee a p₀ κ ε out ∧
      (Repetition.Physical.auxAccept (Data := Fin n) (refinementPattern a p p₀) *
        Repetition.Physical.auxMeasurement (refinementPattern a p p₀)).submatrix
          (Fintype.equivFin (Bits n)).symm
          ((refinementCoordinates a p n).trans (Fintype.equivFin _)).symm =
        acceptMatrix (refinementSuccessEmbedding (D := Bits n) a p₀) := by
  obtain ⟨out, hout⟩ := proposition56 (D := Bits n) (B := Bits n) a p₀ hκ hε0 hε1
  exact ⟨out, hout, refinementSuccess_is_bit_measurement a p n p₀⟩

end OptimalQLS.PaperStatements
