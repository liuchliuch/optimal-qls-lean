import OptimalQLS.TransducerCompiler.Reservoir

/-! # Exact reservoir energy for the finite transducer compiler -/

noncomputable section
namespace OptimalQLS.TransducerCompiler
open Matrix

variable {n : Type*} [Fintype n] {K : ℕ}

/-- Unnormalized public uniform-clock state. -/
def publicState (ξ : n → ℂ) : Space n K → ℂ
  | ((i,.pub),_) => ξ i
  | ((_,.internal),_) => 0
  | ((_,.first),_) => 0
  | ((_,.second),_) => 0

/-- The finite private reservoir used only in the proof, never prepared by the circuit. -/
def catalyst (D₁ D₂ : ℕ) (v₀ v₁ v₂ : n → ℂ) : Space n K → ℂ
  | ((_,.pub),_) => 0
  | ((i,.internal),k) => if k.val = 0 then v₀ i else 0
  | ((i,.first),k) => if k.val < D₁ then v₁ i else 0
  | ((i,.second),k) => if k.val < D₂ then v₂ i else 0

/-- Euclidean energy of a data vector. -/
def energy (v : n → ℂ) : ℝ := ∑ i, ‖v i‖ ^ 2

theorem energy_eq_norm_sq (v : n → ℂ) : energy v = ‖WithLp.toLp 2 v‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  rfl

private theorem sum_fin_lt (D : ℕ) (hD : D ≤ K) (x : ℝ) :
    (∑ k : Fin K, if k.val < D then x else 0) = D * x := by
  rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => if k < D then x else 0)]
  calc
    (∑ k ∈ Finset.range K, if k < D then x else 0) =
        ∑ k ∈ Finset.range D, x := by
      rw [← Finset.sum_filter]
      congr 1
      ext k
      simp only [Finset.mem_filter, Finset.mem_range]
      omega
    _ = D * x := by simp

private theorem sum_label (f : Label → ℝ) :
    (∑ l, f l) = f .pub + f .internal + f .first + f .second := by
  have hu : (Finset.univ : Finset Label) = {.pub, .internal, .first, .second} := by decide
  rw [hu]
  simp
  ring

/-- Energy splits exactly across the four mutually orthogonal labels. -/
theorem bundle_norm_sq (ξ v₀ v₁ v₂ : n → ℂ) :
    ‖WithLp.toLp 2 (bundle ξ v₀ v₁ v₂)‖ ^ 2 =
      energy ξ + energy v₀ + energy v₁ + energy v₂ := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [Fintype.sum_prod_type]
  simp_rw [sum_label]
  simp [bundle, energy, Finset.sum_add_distrib]

/-- Private work energy is the sum of its three private-label components. -/
theorem private_bundle_norm_sq (v₀ v₁ v₂ : n → ℂ) :
    ‖WithLp.toLp 2 (bundle 0 v₀ v₁ v₂)‖ ^ 2 =
      energy v₀ + energy v₁ + energy v₂ := by
  simpa [energy] using bundle_norm_sq (0 : n → ℂ) v₀ v₁ v₂

/-- The public state places one copy of the data in every clock slot. -/
theorem publicState_norm_sq (ξ : n → ℂ) :
    ‖WithLp.toLp 2 (publicState (K := K) ξ)‖ ^ 2 = K * energy ξ := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [Fintype.sum_prod_type]
  simp_rw [sum_label]
  simp [publicState, energy, ← Finset.mul_sum]

theorem energy_nonneg (v : n → ℂ) : 0 ≤ energy v := by
  rw [energy_eq_norm_sq]
  positivity

/-- The exact reservoir energy produces the K/Ki query savings. -/
theorem catalyst_norm_sq (hK : 0 < K) (D₁ D₂ : ℕ)
    (h₁K : D₁ ≤ K) (h₂K : D₂ ≤ K) (v₀ v₁ v₂ : n → ℂ) :
    ‖WithLp.toLp 2 (catalyst (K := K) D₁ D₂ v₀ v₁ v₂)‖ ^ 2 =
      energy v₀ + D₁ * energy v₁ + D₂ * energy v₂ := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [Fintype.sum_prod_type]
  simp_rw [sum_label]
  simp only [catalyst, norm_zero, zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero,
    zero_add, apply_ite, norm_zero]
  simp_rw [ite_pow, zero_pow (by decide : 2 ≠ 0)]
  have hzero : ∀ i : n, (∑ k : Fin K, if k.val = 0 then ‖v₀ i‖ ^ 2 else 0) = ‖v₀ i‖ ^ 2 := by
    intro i
    have he : ∀ k : Fin K, k.val = 0 ↔ k = (⟨0, hK⟩ : Fin K) := fun k => by
      constructor
      · intro h; apply Fin.ext; exact h
      · intro h; subst k; rfl
    simp_rw [he]
    simp
  simp_rw [hzero, sum_fin_lt D₁ h₁K, sum_fin_lt D₂ h₂K]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, energy]


end OptimalQLS.TransducerCompiler
