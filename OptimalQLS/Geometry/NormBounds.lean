import OptimalQLS.Geometry.Diagonal

noncomputable section
namespace OptimalQLS.Geometry
variable {ι : Type*} [Fintype ι]

/-- Explicit squared L2 norm of a triple. -/
theorem triple_norm_sq (x y z : Vec ι) :
    ‖triple x y z‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2 + ‖z‖ ^ 2 := by
  simp [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type, Fin.sum_univ_three, triple]

/-- Parseval for the concrete real diagonal operator. -/
theorem diagonal_real_norm_sq (f : ι → ℝ) (b : Vec ι) :
    ‖diagonal (fun i => (f i : ℂ)) b‖ ^ 2 = ∑ i, f i ^ 2 * ‖b i‖ ^ 2 := by
  simp [EuclideanSpace.norm_sq_eq, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, mul_pow, sq_abs]

/-- The exact expectation identity used by Lemma 4.2. -/
theorem kernelProjector_input_norm_sq (a : ι → ℝ) {t : ℝ} (ht : 0 < t) (b : Vec ι) :
    ‖kernelProjector a t (triple 0 b 0)‖ ^ 2 =
      ∑ i, (t ^ 2 / (a i ^ 2 + t ^ 2)) * ‖b i‖ ^ 2 := by
  rw [kernelProjector_input, triple_norm_sq]
  simp only [norm_zero, zero_pow (by decide : 2 ≠ 0), zero_add]
  have h₁ : (fun i => (t : ℂ)^2 / ((a i : ℂ)^2 + (t : ℂ)^2)) =
      fun i => ((t ^ 2 / (a i ^ 2 + t ^ 2) : ℝ) : ℂ) := by ext; push_cast; rfl
  have h₂ : (fun i => t * (a i : ℂ) / ((a i : ℂ)^2 + (t : ℂ)^2)) =
      fun i => ((t * a i / (a i ^ 2 + t ^ 2) : ℝ) : ℂ) := by ext; push_cast; rfl
  rw [h₁, h₂, diagonal_real_norm_sq, diagonal_real_norm_sq, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← add_mul, projection_coefficient_identity ht]

/-- Both solution-dependent bounds and the universal half bound. -/
theorem kernelProjector_norm_bounds (a : ι → ℝ) {t : ℝ} (ht : 0 < t)
    (ha : ∀ i, t ≤ |a i|) (b : Vec ι) :
    (t ^ 2 / 2) * ‖diagonal (fun i => ((a i)⁻¹ : ℂ)) b‖ ^ 2 ≤
      ‖kernelProjector a t (triple 0 b 0)‖ ^ 2 ∧
    ‖kernelProjector a t (triple 0 b 0)‖ ^ 2 ≤
      t ^ 2 * ‖diagonal (fun i => ((a i)⁻¹ : ℂ)) b‖ ^ 2 ∧
    ‖kernelProjector a t (triple 0 b 0)‖ ^ 2 ≤ (1 / 2) * ‖b‖ ^ 2 := by
  have hinv : (fun i => ((a i)⁻¹ : ℂ)) = fun i => (((a i)⁻¹ : ℝ) : ℂ) := by
    ext; simp
  rw [hinv, kernelProjector_input_norm_sq a ht, diagonal_real_norm_sq,
    EuclideanSpace.norm_sq_eq, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine ⟨Finset.sum_le_sum ?_, Finset.sum_le_sum ?_, Finset.sum_le_sum ?_⟩
  · intro i _
    have h := (projection_coefficient_bounds ht (ha i)).1
    have heq : t ^ 2 / 2 * ((a i)⁻¹) ^ 2 = t ^ 2 / (2 * a i ^ 2) := by
      rw [inv_pow]; field_simp
    rw [← mul_assoc, heq]
    exact mul_le_mul_of_nonneg_right h (sq_nonneg _)
  · intro i _
    have h := (projection_coefficient_bounds ht (ha i)).2.1
    have heq : t ^ 2 * ((a i)⁻¹) ^ 2 = t ^ 2 / a i ^ 2 := by
      rw [inv_pow, div_eq_mul_inv]
    rw [← mul_assoc, heq]
    exact mul_le_mul_of_nonneg_right h (sq_nonneg _)
  · intro i _
    exact mul_le_mul_of_nonneg_right (projection_coefficient_bounds ht (ha i)).2.2
      (sq_nonneg _)

/-- Pseudoinverse solution-vector bound, in the Euclidean norm. -/
theorem pseudoInverse_input_norm_le (a : ι → ℝ) {t : ℝ} (ht : 0 < t)
    (ha : ∀ i, t ≤ |a i|) (b : Vec ι) :
    ‖pseudoInverse a t (triple 0 b 0)‖ ≤ ‖diagonal (fun i => ((a i)⁻¹ : ℂ)) b‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [pseudoInverse_input, triple_norm_sq]
  simp only [norm_zero, zero_pow (by decide : 2 ≠ 0), add_zero]
  have h₁ : (fun i => (a i : ℂ) / ((a i : ℂ)^2 + (t : ℂ)^2)) =
      fun i => ((a i / (a i ^ 2 + t ^ 2) : ℝ) : ℂ) := by ext; push_cast; rfl
  have h₂ : (fun i => ((a i)⁻¹ : ℂ)) = fun i => (((a i)⁻¹ : ℝ) : ℂ) := by ext; simp
  rw [h₁, h₂, diagonal_real_norm_sq, diagonal_real_norm_sq]
  apply Finset.sum_le_sum
  intro i _
  exact mul_le_mul_of_nonneg_right (pseudoinverse_coefficient_bound ht (ha i)) (sq_nonneg _)

/-- Inverse application is nonzero for any nonzero input. -/
theorem diagonal_inverse_ne_zero (a : ι → ℝ) (ha : ∀ i, a i ≠ 0)
    {b : Vec ι} (hb : b ≠ 0) : diagonal (fun i => ((a i)⁻¹ : ℂ)) b ≠ 0 := by
  intro h
  apply hb
  ext i
  have hi := congrArg (fun v : Vec ι => v i) h
  have hai : (a i : ℂ) ≠ 0 := by exact_mod_cast ha i
  simpa [hai] using hi

/-- Nonzero inputs have strictly positive kernel weight. -/
theorem kernelProjector_input_norm_pos (a : ι → ℝ) {t : ℝ} (ht : 0 < t)
    (ha : ∀ i, t ≤ |a i|) {b : Vec ι} (hb : b ≠ 0) :
    0 < ‖kernelProjector a t (triple 0 b 0)‖ ^ 2 := by
  have hane : ∀ i, a i ≠ 0 := by
    intro i hi
    have h := ha i
    simp [hi] at h
    linarith
  have hn : 0 < ‖diagonal (fun i => ((a i)⁻¹ : ℂ)) b‖ :=
    norm_pos_iff.mpr (diagonal_inverse_ne_zero a hane hb)
  exact lt_of_lt_of_le (mul_pos (by positivity) (sq_pos_of_pos hn))
    (kernelProjector_norm_bounds a ht ha b).1

/-- The paper's displayed κ form, with an actual normalized input. -/
theorem lemma42_diagonal_norms (a : ι → ℝ) {κ : ℝ} (hκ : 0 < κ)
    (ha : ∀ i, κ⁻¹ ≤ |a i|) (b : Vec ι) (hb : ‖b‖ = 1) :
    let s := ‖diagonal (fun i => ((a i)⁻¹ : ℂ)) b‖
    let γsq := ‖kernelProjector a κ⁻¹ (triple 0 b 0)‖ ^ 2
    s ^ 2 / (2 * κ ^ 2) ≤ γsq ∧ γsq ≤ s ^ 2 / κ ^ 2 ∧
      0 < γsq ∧ γsq ≤ 1 / 2 := by
  dsimp only
  have h := kernelProjector_norm_bounds a (inv_pos.mpr hκ) ha b
  have hne : b ≠ 0 := by intro he; simpa [he] using hb
  have hpos := kernelProjector_input_norm_pos a (inv_pos.mpr hκ) ha hne
  have he₁ (s : ℝ) : (κ⁻¹ ^ 2 / 2) * s ^ 2 = s ^ 2 / (2 * κ ^ 2) := by
    field_simp
  have he₂ (s : ℝ) : κ⁻¹ ^ 2 * s ^ 2 = s ^ 2 / κ ^ 2 := by
    field_simp
  rw [he₁] at h
  rw [he₂] at h
  refine ⟨h.1, h.2.1, hpos, ?_⟩
  simpa [hb] using h.2.2

end OptimalQLS.Geometry
