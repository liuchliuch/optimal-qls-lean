import OptimalQLS.OracleCircuit
import Mathlib.Data.Matrix.Composition
import Mathlib.Tactic

/-!
# Concrete work unitary for the kernel-reflection transducer

The public space is embedded in a shared workspace by the signal projector Q.
The unused public Q-perpendicular sector is extended by the identity. This
keeps all three label sectors the same finite size and makes the circuit a
literal unitary on an ordinary register space.
-/
noncomputable section
set_option linter.unusedSimpArgs false
namespace OptimalQLS
open Matrix
variable {n : Type*} [Fintype n] [DecidableEq n]

def kernelWorkBlocks (Q : Matrix n n ℂ) (a b : ℝ) :
    Matrix (Fin 3) (Fin 3) (Matrix n n ℂ) :=
  !![a • Q + (1 - Q), 0, b • Q;
     b • Q, 0, (-a) • Q - (1 - Q);
     0, 1 - (2 : ℝ) • Q, 0]

theorem kernelWorkBlocks_unitary (Q : Matrix n n ℂ) (hQ : star Q = Q)
    (hQQ : Q * Q = Q) {a b : ℝ} (hab : a * a + b * b = 1) :
    kernelWorkBlocks Q a b ∈ unitary (Matrix (Fin 3) (Fin 3) (Matrix n n ℂ)) := by
  constructor
  all_goals
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.star_apply,
        kernelWorkBlocks, Matrix.of_apply, star_add, star_sub, star_smul, hQ,
        mul_add, add_mul, mul_sub, sub_mul, smul_mul_assoc, mul_smul_comm, hQQ]
  all_goals
    first
    | module
    | calc
        _ = (a * a + b * b) • Q + (1 - Q) := by module
        _ = 1 := by rw [hab]; module

theorem compMatrix_star (M : Matrix (Fin 3) (Fin 3) (Matrix n n ℂ)) :
    Matrix.compRingEquiv (Fin 3) n ℂ (star M) =
      star (Matrix.compRingEquiv (Fin 3) n ℂ M) := by
  ext ⟨i,k⟩ ⟨j,l⟩
  rfl

/-- Flattening the three-by-three block matrix gives an actual unitary on
the label register tensored with the finite shared workspace. -/
def kernelWorkUnitary (Q : Matrix n n ℂ) (hQ : star Q = Q) (hQQ : Q * Q = Q)
    (a b : ℝ) (hab : a * a + b * b = 1) : Matrix.unitaryGroup (Fin 3 × n) ℂ :=
  ⟨Matrix.compRingEquiv (Fin 3) n ℂ (kernelWorkBlocks Q a b), by
    have h := kernelWorkBlocks_unitary Q hQ hQQ hab
    constructor
    · rw [← compMatrix_star, ← map_mul, h.1, map_one]
    · rw [← compMatrix_star, ← map_mul, h.2, map_one]⟩

def kernelMixA (μ : ℝ) := (1 - μ) / (1 + μ)
def kernelMixB (μ : ℝ) := 2 * Real.sqrt μ / (1 + μ)

theorem kernelMix_normalized {μ : ℝ} (hμ : 0 < μ) :
    kernelMixA μ * kernelMixA μ + kernelMixB μ * kernelMixB μ = 1 := by
  have hden : 1 + μ ≠ 0 := by linarith
  have hs := Real.sq_sqrt hμ.le
  unfold kernelMixA kernelMixB
  field_simp
  nlinarith


def kernelTriple (x y z : n → ℂ) : Fin 3 × n → ℂ :=
  fun ji => (![x, y, z] ji.1) ji.2

theorem flattened_block_apply (M : Matrix (Fin 3) (Fin 3) (Matrix n n ℂ))
    (v : Fin 3 → n → ℂ) (i : Fin 3) (j : n) :
    (Matrix.compRingEquiv (Fin 3) n ℂ M *ᵥ (fun ki => v ki.1 ki.2)) (i,j) =
      (∑ k : Fin 3, M i k *ᵥ v k) j := by
  simp [Matrix.compRingEquiv_apply, Matrix.comp_apply, Matrix.mulVec, dotProduct,
    Fintype.sum_prod_type, Finset.sum_apply]

/-- Exact component action of the signal-controlled work unitary. -/
theorem kernelWork_apply (Q : Matrix n n ℂ) (hQ : star Q = Q) (hQQ : Q * Q = Q)
    (a b : ℝ) (hab : a * a + b * b = 1) (x y z : n → ℂ) :
    (kernelWorkUnitary Q hQ hQQ a b hab : Matrix (Fin 3 × n) (Fin 3 × n) ℂ) *ᵥ
      kernelTriple x y z =
    kernelTriple (a • (Q *ᵥ x) + (x - Q *ᵥ x) + b • (Q *ᵥ z))
      (b • (Q *ᵥ x) + (-a) • (Q *ᵥ z) - (z - Q *ᵥ z))
      (y - (2 : ℝ) • (Q *ᵥ y)) := by
  funext ji
  rcases ji with ⟨i,j⟩
  change (Matrix.compRingEquiv (Fin 3) n ℂ (kernelWorkBlocks Q a b) *ᵥ
    (fun ki => (![x,y,z] ki.1) ki.2)) (i,j) = _
  rw [flattened_block_apply]
  fin_cases i <;> simp [Fin.sum_univ_three, kernelWorkBlocks, kernelTriple,
    Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.neg_mulVec] <;> abel


/-- The two exact scalar identities behind catalyst restoration. -/
theorem kernelMix_relations {μ : ℝ} (hμ : 0 < μ) :
    kernelMixB μ * Real.sqrt μ = 1 - kernelMixA μ ∧
    kernelMixB μ * (Real.sqrt μ)⁻¹ = 1 + kernelMixA μ := by
  have hd : 1 + μ ≠ 0 := by linarith
  have hg : Real.sqrt μ ≠ 0 := (Real.sqrt_pos.mpr hμ).ne'
  have hs := Real.sq_sqrt hμ.le
  constructor
  · unfold kernelMixA kernelMixB
    field_simp
    nlinarith
  · unfold kernelMixA kernelMixB
    field_simp
    ring

section VectorAlgebra
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- The public component is the exact reflection, without approximation. -/
theorem kernelMix_public {μ : ℝ} (hμ : 0 < μ) (ξ p : E) :
    kernelMixA μ • ξ + kernelMixB μ •
      (Real.sqrt μ • p - (Real.sqrt μ)⁻¹ • (ξ - p)) = (2 : ℝ) • p - ξ := by
  obtain ⟨h₁,h₂⟩ := kernelMix_relations hμ
  calc
    _ = (kernelMixA μ - kernelMixB μ * (Real.sqrt μ)⁻¹) • ξ +
        (kernelMixB μ * Real.sqrt μ + kernelMixB μ * (Real.sqrt μ)⁻¹) • p := by module
    _ = (2 : ℝ) • p - ξ := by rw [h₁,h₂]; module

/-- The first private component has exactly the correction needed to
restore the catalyst after one controlled oracle layer. -/
theorem kernelMix_private {μ : ℝ} (hμ : 0 < μ) (ξ p : E) :
    kernelMixB μ • ξ + (1 - kernelMixA μ) •
      (Real.sqrt μ • p - (Real.sqrt μ)⁻¹ • (ξ - p)) =
      (2 * Real.sqrt μ) • p := by
  obtain ⟨h₁,h₂⟩ := kernelMix_relations hμ
  have hg : Real.sqrt μ ≠ 0 := (Real.sqrt_pos.mpr hμ).ne'
  have hb : kernelMixB μ = (1 + kernelMixA μ) * Real.sqrt μ := by
    have hh := congrArg (fun r : ℝ => r * Real.sqrt μ) h₂
    simpa [mul_assoc, hg] using hh
  have hc : (1 - kernelMixA μ) * (Real.sqrt μ)⁻¹ = kernelMixB μ := by
    rw [← h₁, mul_assoc, mul_inv_cancel₀ hg, mul_one]
  calc
    _ = (kernelMixB μ - (1 - kernelMixA μ) * (Real.sqrt μ)⁻¹) • ξ +
        ((1 - kernelMixA μ) * Real.sqrt μ +
          (1 - kernelMixA μ) * (Real.sqrt μ)⁻¹) • p := by module
    _ = (2 * Real.sqrt μ) • p := by rw [hc, hb]; module
end VectorAlgebra

/-- The explicit catalyst, with the square-root coefficient written as
`α / sqrt μ` so its exact scalar cancellation is exposed. -/
def kernelCatalystOne (V : Matrix n n ℂ) (μ α : ℝ) (p z : n → ℂ) : n → ℂ :=
  Real.sqrt μ • p + (α / Real.sqrt μ) • (V *ᵥ z)

def kernelCatalystTwo (V : Matrix n n ℂ) (μ α : ℝ) (p z : n → ℂ) : n → ℂ :=
  Real.sqrt μ • (V *ᵥ p) - (α / Real.sqrt μ) • z

/-- Direct verification of the actual work matrix on the explicit catalyst.
The compression identities used here will be obtained from the signal block
and the canonical Moore–Penrose inverse, rather than postulated for the QLSA. -/
theorem kernel_catalyst_restoration (Q V : Matrix n n ℂ)
    (hQ : star Q = Q) (hQQ : Q * Q = Q) (hV : V * V = 1)
    {μ α : ℝ} (hμ : 0 < μ) (hα : α ≠ 0) (ξ p z : n → ℂ)
    (hξ : Q *ᵥ ξ = ξ) (hp : Q *ᵥ p = p) (hz : Q *ᵥ z = z)
    (hVp : Q *ᵥ (V *ᵥ p) = 0)
    (hVz : Q *ᵥ (V *ᵥ z) = α⁻¹ • (ξ - p)) :
    (kernelWorkUnitary Q hQ hQQ (kernelMixA μ) (kernelMixB μ)
      (kernelMix_normalized hμ) : Matrix (Fin 3 × n) (Fin 3 × n) ℂ) *ᵥ
      kernelTriple ξ (V *ᵥ kernelCatalystOne V μ α p z)
        (V *ᵥ kernelCatalystTwo V μ α p z) =
      kernelTriple ((2 : ℝ) • p - ξ)
        (kernelCatalystOne V μ α p z) (kernelCatalystTwo V μ α p z) := by
  have hVV (x : n → ℂ) : V *ᵥ (V *ᵥ x) = x := by
    rw [Matrix.mulVec_mulVec, hV, Matrix.one_mulVec]
  have hcoef : α / Real.sqrt μ * α⁻¹ = (Real.sqrt μ)⁻¹ := by
    field_simp
  have hv₁ : V *ᵥ kernelCatalystOne V μ α p z =
      Real.sqrt μ • (V *ᵥ p) + (α / Real.sqrt μ) • z := by
    simp [kernelCatalystOne, Matrix.mulVec_add, Matrix.mulVec_smul, hVV]
  have hv₂ : V *ᵥ kernelCatalystTwo V μ α p z =
      Real.sqrt μ • p - (α / Real.sqrt μ) • (V *ᵥ z) := by
    simp [kernelCatalystTwo, Matrix.mulVec_sub, Matrix.mulVec_smul, hVV]
  have hq₁ : Q *ᵥ (V *ᵥ kernelCatalystOne V μ α p z) =
      (α / Real.sqrt μ) • z := by
    rw [hv₁, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hVp, hz]
    simp
  have hq₂ : Q *ᵥ (V *ᵥ kernelCatalystTwo V μ α p z) =
      Real.sqrt μ • p - (Real.sqrt μ)⁻¹ • (ξ - p) := by
    rw [hv₂, Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul,
      hp, hVz, smul_smul, hcoef]
  rw [kernelWork_apply, hξ, hq₁, hq₂]
  congr 1
  · simpa using kernelMix_public hμ ξ p
  · calc
      _ = (kernelMixB μ • ξ + (1 - kernelMixA μ) •
          (Real.sqrt μ • p - (Real.sqrt μ)⁻¹ • (ξ - p))) -
            V *ᵥ kernelCatalystTwo V μ α p z := by module
      _ = (2 * Real.sqrt μ) • p - V *ᵥ kernelCatalystTwo V μ α p z := by
        rw [kernelMix_private hμ]
      _ = kernelCatalystOne V μ α p z := by
        rw [hv₂, kernelCatalystOne]
        module
  · rw [hv₁, kernelCatalystTwo]
    module

end OptimalQLS
