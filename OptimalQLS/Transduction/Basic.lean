import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Tactic

/-! The Hilbert direct sum used in the general transduction theorem. Its norm is
`‖(x,w)‖² = ‖x‖² + ‖w‖²`, not the Banach-product maximum norm. -/
noncomputable section
namespace OptimalQLS.Transduction
set_option linter.unusedSectionVars false

open scoped InnerProductSpace

variable {H L : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup L] [InnerProductSpace ℂ L]

abbrev HilbertSum (H L : Type*) := WithLp 2 (H × L)

/-- The actual public/private Hilbert direct-sum vector. -/
def pair (x : H) (w : L) : HilbertSum H L := WithLp.toLp 2 (x, w)

@[simp] theorem pair_fst (x : H) (w : L) : (pair x w).fst = x := rfl
@[simp] theorem pair_snd (x : H) (w : L) : (pair x w).snd = w := rfl
@[simp] theorem pair_add (x y : H) (w v : L) :
    pair (x + y) (w + v) = pair x w + pair y v := rfl
@[simp] theorem pair_smul (a : ℂ) (x : H) (w : L) :
    pair (a • x) (a • w) = a • pair x w := rfl
@[simp] theorem pair_sub (x y : H) (w v : L) :
    pair (x - y) (w - v) = pair x w - pair y v := rfl
@[simp] theorem pair_inner (x y : H) (w v : L) :
    inner ℂ (pair x w) (pair y v) = inner ℂ x y + inner ℂ w v := rfl
@[simp] theorem pair_norm_sq (x : H) (w : L) :
    ‖pair x w‖ ^ 2 = ‖x‖ ^ 2 + ‖w‖ ^ 2 := WithLp.prod_norm_sq_eq_of_L2 _

variable (S : HilbertSum H L ≃ₗᵢ[ℂ] HilbertSum H L)

/-- The private-to-private block `D` of the unitary. -/
def privateBlock : L →ₗ[ℂ] L where
  toFun w := (S (pair 0 w)).snd
  map_add' x y := by
    simpa only [add_zero, map_add, WithLp.add_snd] using
      congrArg (fun z => (S z).snd) (pair_add (0 : H) 0 x y)
  map_smul' a x := by
    simpa only [smul_zero, map_smul, WithLp.smul_snd, RingHom.id_apply] using
      congrArg (fun z => (S z).snd) (pair_smul a (0 : H) x)

/-- The public-to-private block `C` of the unitary. -/
def publicToPrivate : H →ₗ[ℂ] L where
  toFun x := (S (pair x 0)).snd
  map_add' x y := by
    simpa only [add_zero, map_add, WithLp.add_snd] using
      congrArg (fun z => (S z).snd) (pair_add x y (0 : L) 0)
  map_smul' a x := by
    simpa only [smul_zero, map_smul, WithLp.smul_snd, RingHom.id_apply] using
      congrArg (fun z => (S z).snd) (pair_smul a x (0 : L))

/-- The feedback equation is `(I-D)w=Cx`. -/
def feedback : L →ₗ[ℂ] L := LinearMap.id - privateBlock S

/-- The private fixed-point kernel, equivalently the 1-eigenspace of `D`. -/
def fixedSpace : Submodule ℂ L := (feedback S).ker

@[simp] theorem privateBlock_apply (w : L) : privateBlock S w = (S (pair 0 w)).snd := rfl
@[simp] theorem publicToPrivate_apply (x : H) : publicToPrivate S x = (S (pair x 0)).snd := rfl
@[simp] theorem feedback_apply (w : L) : feedback S w = w - (S (pair 0 w)).snd := rfl
@[simp] theorem mem_fixedSpace (w : L) : w ∈ fixedSpace S ↔ (S (pair 0 w)).snd = w := by
  change w - (S (pair 0 w)).snd = 0 ↔ _
  exact sub_eq_zero.trans eq_comm

/-- A private fixed point of the compression is an actual fixed point of `S`.
This is a consequence of the Hilbert norm and unitarity, not an assumption. -/
theorem fixedSpace_fixed {w : L} (hw : w ∈ fixedSpace S) : S (pair 0 w) = pair 0 w := by
  have hs : (S (pair 0 w)).snd = w := (mem_fixedSpace S w).mp hw
  have hn := congrArg (fun r : ℝ => r ^ 2) (S.norm_map (pair 0 w))
  dsimp only at hn
  rw [WithLp.prod_norm_sq_eq_of_L2, pair_norm_sq, norm_zero, zero_pow (by decide), zero_add,
    hs] at hn
  have hf : (S (pair 0 w)).fst = 0 := by
    apply norm_eq_zero.mp
    nlinarith [norm_nonneg (S (pair 0 w)).fst]
  apply WithLp.ofLp_injective
  exact Prod.ext hf hs

/-- Private fixed points have zero inner product with the public-to-private block. -/
theorem publicToPrivate_orthogonal (x : H) : publicToPrivate S x ∈ (fixedSpace S)ᗮ := by
  rw [Submodule.mem_orthogonal]
  intro w hw
  have h := S.inner_map_map (pair 0 w) (pair x 0)
  rw [fixedSpace_fixed S hw] at h
  simpa [WithLp.prod_inner_apply, pair] using h

/-- The range of `I-D` is orthogonal to the private fixed space. -/
theorem feedback_range_le_orthogonal : (feedback S).range ≤ (fixedSpace S)ᗮ := by
  rintro _ ⟨v, rfl⟩
  rw [Submodule.mem_orthogonal]
  intro w hw
  have h := S.inner_map_map (pair 0 w) (pair 0 v)
  rw [fixedSpace_fixed S hw] at h
  have hi : inner ℂ w ((S (pair 0 v)).snd) = inner ℂ w v := by
    simpa [WithLp.prod_inner_apply, pair] using h
  simp [inner_sub_right, hi]

/-- Fredholm obstruction: a vector orthogonal to `range(I-D)` is a fixed point.
The proof uses the norm of `S(0,w)-(0,w)` and unitarity. -/
theorem orthogonal_feedback_range_le_fixed : (feedback S).rangeᗮ ≤ fixedSpace S := by
  intro w hw
  have hi := ((feedback S).range.mem_orthogonal w).mp hw
    (feedback S w) (LinearMap.mem_range_self _ _)
  have hz : inner ℂ ((S (pair 0 w)).snd) w = inner ℂ w w := by
    change inner ℂ (w - (S (pair 0 w)).snd) w = 0 at hi
    rw [inner_sub_left] at hi
    exact (sub_eq_zero.mp hi).symm
  have hp : inner ℂ (S (pair 0 w)) (pair 0 w) = inner ℂ w w := by
    simpa [WithLp.prod_inner_apply, pair] using hz
  have hn : ‖S (pair 0 w) - pair 0 w‖ ^ 2 = 0 := by
    rw [norm_sub_sq (𝕜 := ℂ), S.norm_map, hp, pair_norm_sq]
    simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_add]
    rw [← norm_sq_eq_re_inner]
    ring
  have he : S (pair 0 w) = pair 0 w := by
    apply sub_eq_zero.mp
    apply norm_eq_zero.mp
    nlinarith [norm_nonneg (S (pair 0 w) - pair 0 w)]
  exact (mem_fixedSpace S w).mpr (congrArg WithLp.snd he)

/-- Exact finite-dimensional Fredholm range identity. -/
theorem feedback_range_eq_orthogonal [FiniteDimensional ℂ L] :
    (feedback S).range = (fixedSpace S)ᗮ := by
  apply le_antisymm (feedback_range_le_orthogonal S)
  have h := Submodule.orthogonal_le (orthogonal_feedback_range_le_fixed S)
  simpa using h

/-- Solvability of the catalyst equation follows from unitarity. -/
theorem publicToPrivate_mem_range [FiniteDimensional ℂ L] (x : H) :
    publicToPrivate S x ∈ (feedback S).range := by
  rw [feedback_range_eq_orthogonal]
  exact publicToPrivate_orthogonal S x

end OptimalQLS.Transduction
