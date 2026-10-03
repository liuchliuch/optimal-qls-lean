import OptimalQLS.Transduction.Matrix

noncomputable section
namespace OptimalQLS.Transduction

open Matrix
open scoped InnerProductSpace
set_option maxHeartbeats 200000
set_option linter.unusedSectionVars false

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- Equivalence between the Hilbert equation and the literal matrix-vector equation. -/
theorem matrix_transduction_iff (S : Matrix.unitaryGroup (ι ⊕ κ) ℂ)
    (x y : ι → ℂ) (w : κ → ℂ) :
    matrixTransducer S (pair (WithLp.toLp 2 x) (WithLp.toLp 2 w)) =
      pair (WithLp.toLp 2 y) (WithLp.toLp 2 w) ↔
    (S : Matrix (ι ⊕ κ) (ι ⊕ κ) ℂ) *ᵥ Sum.elim x w = Sum.elim y w := by
  constructor
  · intro h
    have hh := congrArg (fun z => WithLp.ofLp (sumIsometry.symm z)) h
    simpa [matrixTransducer, LinearIsometryEquiv.trans_apply] using hh
  · intro h
    apply sumIsometry.symm.injective
    simpa [matrixTransducer, LinearIsometryEquiv.trans_apply] using
      congrArg (WithLp.toLp 2) h

@[simp] theorem sumIsometry_snd_apply (v : (ι ⊕ κ) → ℂ) :
    (sumIsometry (WithLp.toLp 2 v)).snd = WithLp.toLp 2 (fun j => v (Sum.inr j)) := rfl

/-- Explicit action of the transported matrix on a pair of coordinate vectors. -/
theorem matrixTransducer_pair (S : Matrix.unitaryGroup (ι ⊕ κ) ℂ)
    (x : ι → ℂ) (w : κ → ℂ) :
    matrixTransducer S (pair (WithLp.toLp 2 x) (WithLp.toLp 2 w)) =
      sumIsometry (WithLp.toLp 2
        ((S : Matrix (ι ⊕ κ) (ι ⊕ κ) ℂ) *ᵥ Sum.elim x w)) := by
  simp [matrixTransducer, LinearIsometryEquiv.trans_apply]

/-- The private compression's 1-eigenspace, with the Euclidean-space inner product. -/
def matrixFixedSpace (S : Matrix.unitaryGroup (ι ⊕ κ) ℂ) :
    Submodule ℂ (EuclideanSpace ℂ κ) := fixedSpace (H := EuclideanSpace ℂ ι) (L := EuclideanSpace ℂ κ) (matrixTransducer S)

/-- Literal coordinate description of the private fixed-point kernel. -/
theorem matrixFixedSpace_mem (S : Matrix.unitaryGroup (ι ⊕ κ) ℂ) (w : κ → ℂ) :
    WithLp.toLp 2 w ∈ matrixFixedSpace S ↔
      ∀ j, ((S : Matrix (ι ⊕ κ) (ι ⊕ κ) ℂ) *ᵥ Sum.elim 0 w) (Sum.inr j) = w j := by
  change WithLp.toLp 2 w ∈ fixedSpace (H := EuclideanSpace ℂ ι) (L := EuclideanSpace ℂ κ) (matrixTransducer S) ↔ _
  rw [mem_fixedSpace]
  change (matrixTransducer S
    (pair (WithLp.toLp 2 (0 : ι → ℂ)) (WithLp.toLp 2 w))).snd = WithLp.toLp 2 w ↔ _
  rw [matrixTransducer_pair, sumIsometry_snd_apply]
  constructor
  · intro h j
    exact congrArg (fun u : EuclideanSpace ℂ κ => u j) h
  · intro h
    exact congrArg (WithLp.toLp 2) (funext h)

/-- All possible matrix catalysts yield the same constructed public output. -/
theorem matrix_output_unique (S : Matrix.unitaryGroup (ι ⊕ κ) ℂ)
    {x y : ι → ℂ} {w : κ → ℂ}
    (h : (S : Matrix (ι ⊕ κ) (ι ⊕ κ) ℂ) *ᵥ Sum.elim x w = Sum.elim y w) :
    y = (publicMatrix S : Matrix ι ι ℂ) *ᵥ x := by
  have he := output_unique (H := EuclideanSpace ℂ ι) (L := EuclideanSpace ℂ κ) (matrixTransducer S) ((matrix_transduction_iff S x y w).mpr h)
  have hf := congrArg WithLp.ofLp he
  simpa [publicMatrix] using hf

/-- The constructed matrix catalyst is orthogonal to the private 1-eigenspace. -/
theorem matrixCatalyst_orthogonal (S : Matrix.unitaryGroup (ι ⊕ κ) ℂ) (x : ι → ℂ) :
    WithLp.toLp 2 (matrixCatalyst S x) ∈ (matrixFixedSpace S)ᗮ := by
  exact catalyst_mem (H := EuclideanSpace ℂ ι) (L := EuclideanSpace ℂ κ) (matrixTransducer S) (WithLp.toLp 2 x)

/-- Uniqueness among catalysts orthogonal to the private 1-eigenspace. -/
theorem matrixCatalyst_orthogonal_unique (S : Matrix.unitaryGroup (ι ⊕ κ) ℂ)
    {x y : ι → ℂ} {w : κ → ℂ}
    (h : (S : Matrix (ι ⊕ κ) (ι ⊕ κ) ℂ) *ᵥ Sum.elim x w = Sum.elim y w)
    (ho : WithLp.toLp 2 w ∈ (matrixFixedSpace S)ᗮ) : w = matrixCatalyst S x := by
  have he := catalyst_orthogonal_unique (H := EuclideanSpace ℂ ι) (L := EuclideanSpace ℂ κ) (matrixTransducer S)
    ((matrix_transduction_iff S x y w).mpr h) ho
  exact congrArg WithLp.ofLp he

/-- Minimum norm refers to the Euclidean private norm, not the coordinate max norm. -/
theorem matrixCatalyst_minimum_norm (S : Matrix.unitaryGroup (ι ⊕ κ) ℂ)
    {x y : ι → ℂ} {w : κ → ℂ}
    (h : (S : Matrix (ι ⊕ κ) (ι ⊕ κ) ℂ) *ᵥ Sum.elim x w = Sum.elim y w) :
    ‖(WithLp.toLp 2 (matrixCatalyst S x) : EuclideanSpace ℂ κ)‖ ≤
      ‖(WithLp.toLp 2 w : EuclideanSpace ℂ κ)‖ := by
  exact catalyst_minimum_norm (H := EuclideanSpace ℂ ι) (L := EuclideanSpace ℂ κ) (matrixTransducer S) ((matrix_transduction_iff S x y w).mpr h)

/-- The Euclidean minimum-norm catalyst is unique. -/
theorem matrixCatalyst_minimum_norm_unique (S : Matrix.unitaryGroup (ι ⊕ κ) ℂ)
    {x y : ι → ℂ} {w : κ → ℂ}
    (h : (S : Matrix (ι ⊕ κ) (ι ⊕ κ) ℂ) *ᵥ Sum.elim x w = Sum.elim y w)
    (hn : ‖(WithLp.toLp 2 w : EuclideanSpace ℂ κ)‖ =
      ‖(WithLp.toLp 2 (matrixCatalyst S x) : EuclideanSpace ℂ κ)‖) :
    w = matrixCatalyst S x := by
  have he := catalyst_minimum_norm_unique (H := EuclideanSpace ℂ ι) (L := EuclideanSpace ℂ κ) (matrixTransducer S)
    ((matrix_transduction_iff S x y w).mpr h) hn
  exact congrArg WithLp.ofLp he

end OptimalQLS.Transduction
