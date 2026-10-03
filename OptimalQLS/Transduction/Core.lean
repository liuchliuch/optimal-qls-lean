import OptimalQLS.Transduction.Basic

/-! Universal finite-dimensional transduction, including the canonical
minimum-norm catalyst. No existence or induced-unitarity certificate is assumed. -/
noncomputable section
namespace OptimalQLS.Transduction

open scoped InnerProductSpace
set_option linter.unusedSectionVars false

variable {H L : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup L] [InnerProductSpace ℂ L] [FiniteDimensional ℂ L]
  (S : HilbertSum H L ≃ₗᵢ[ℂ] HilbertSum H L)

/-- Project any Fredholm solution off the private fixed space. -/
theorem exists_orthogonal_catalyst (x : H) :
    ∃ w : L, w ∈ (fixedSpace S)ᗮ ∧ feedback S w = publicToPrivate S x := by
  obtain ⟨w, hw⟩ := publicToPrivate_mem_range S x
  refine ⟨w - (fixedSpace S).starProjection w,
    (fixedSpace S).sub_starProjection_mem_orthogonal w, ?_⟩
  have hz : feedback S ((fixedSpace S).starProjection w) = 0 :=
    (fixedSpace S).starProjection_apply_mem w
  rw [map_sub, hz, sub_zero, hw]

/-- The canonical catalyst is selected from the proved nonempty solution set. -/
def canonicalCatalyst (x : H) : L := (exists_orthogonal_catalyst S x).choose

theorem canonicalCatalyst_mem (x : H) : canonicalCatalyst S x ∈ (fixedSpace S)ᗮ :=
  (exists_orthogonal_catalyst S x).choose_spec.1

theorem canonicalCatalyst_feedback (x : H) :
    feedback S (canonicalCatalyst S x) = publicToPrivate S x :=
  (exists_orthogonal_catalyst S x).choose_spec.2

/-- Orthogonality removes exactly the ambiguity in the catalyst equation. -/
theorem orthogonal_catalyst_unique {x : H} {w : L}
    (hm : w ∈ (fixedSpace S)ᗮ) (he : feedback S w = publicToPrivate S x) :
    w = canonicalCatalyst S x := by
  apply sub_eq_zero.mp
  have hk : w - canonicalCatalyst S x ∈ fixedSpace S := by
    change feedback S (w - canonicalCatalyst S x) = 0
    rw [map_sub, he, canonicalCatalyst_feedback, sub_self]
  have hp := (fixedSpace S)ᗮ.sub_mem hm (canonicalCatalyst_mem S x)
  exact inner_self_eq_zero.mp ((fixedSpace S).inner_right_of_mem_orthogonal hk hp)

/-- The canonical catalyst depends linearly on the public input. -/
def catalyst : H →ₗ[ℂ] L where
  toFun := canonicalCatalyst S
  map_add' x y := by
    symm
    apply orthogonal_catalyst_unique S
    · exact (fixedSpace S)ᗮ.add_mem (canonicalCatalyst_mem S x) (canonicalCatalyst_mem S y)
    · rw [map_add, canonicalCatalyst_feedback, canonicalCatalyst_feedback, map_add]
  map_smul' a x := by
    symm
    apply orthogonal_catalyst_unique S
    · exact (fixedSpace S)ᗮ.smul_mem a (canonicalCatalyst_mem S x)
    · rw [map_smul, canonicalCatalyst_feedback, map_smul]
      rfl

@[simp] theorem catalyst_apply (x : H) : catalyst S x = canonicalCatalyst S x := rfl

theorem catalyst_mem (x : H) : catalyst S x ∈ (fixedSpace S)ᗮ :=
  canonicalCatalyst_mem S x

theorem catalyst_feedback (x : H) : feedback S (catalyst S x) = publicToPrivate S x :=
  canonicalCatalyst_feedback S x

/-- The feedback equation is exactly the condition that the private state returns. -/
theorem feedback_eq_iff (x : H) (w : L) :
    feedback S w = publicToPrivate S x ↔ (S (pair x w)).snd = w := by
  have hp : pair x w = pair x 0 + pair 0 w := by simp [← pair_add]
  rw [hp, map_add, WithLp.add_snd]
  change w - (S (pair 0 w)).snd = (S (pair x 0)).snd ↔ _
  exact sub_eq_iff_eq_add.trans eq_comm

/-- Linear public action, before proving that it is unitary. -/
def publicLinear : H →ₗ[ℂ] H where
  toFun x := (S (pair x (catalyst S x))).fst
  map_add' x y := by rw [map_add, pair_add, map_add, WithLp.add_fst]
  map_smul' a x := by rw [map_smul, pair_smul, map_smul, WithLp.smul_fst]; rfl

/-- Exact transduction equation for the constructed catalyst. -/
theorem transduction_eq_linear (x : H) :
    S (pair x (catalyst S x)) = pair (publicLinear S x) (catalyst S x) := by
  apply WithLp.ofLp_injective
  refine Prod.ext ?_ ?_
  · rfl
  · exact (feedback_eq_iff S x _).mp (catalyst_feedback S x)

/-- Norm preservation of the public action is derived by cancellation of the
returned catalyst's squared Hilbert norm. -/
theorem publicLinear_norm (x : H) : ‖publicLinear S x‖ = ‖x‖ := by
  have h := S.norm_map (pair x (catalyst S x))
  rw [transduction_eq_linear] at h
  have hh := congrArg (fun r : ℝ => r ^ 2) h
  dsimp only at hh
  rw [pair_norm_sq, pair_norm_sq] at hh
  nlinarith [norm_nonneg (publicLinear S x), norm_nonneg x]

/-- Constructed isometry on the public space. -/
def publicIsometry : H →ₗᵢ[ℂ] H where
  __ := publicLinear S
  norm_map' := publicLinear_norm S

variable [FiniteDimensional ℂ H]

/-- The universal unitary transduction action. Surjectivity follows from finite
public dimension and the injectivity of the constructed isometry. -/
def publicAction : H ≃ₗᵢ[ℂ] H :=
  LinearIsometryEquiv.ofSurjective (publicIsometry S)
    (LinearMap.surjective_of_injective (publicIsometry S).injective)

@[simp] theorem publicAction_apply (x : H) : publicAction S x = publicLinear S x := rfl

/-- Definition 2.6 / BJY24 Theorem 5.1: every public input admits a catalyst. -/
theorem transduction_eq (x : H) :
    S (pair x (catalyst S x)) = pair (publicAction S x) (catalyst S x) :=
  transduction_eq_linear S x

/-- Any other catalyst differs from the canonical catalyst by a private fixed point. -/
theorem catalyst_sub_mem_fixed {x y : H} {w : L}
    (h : S (pair x w) = pair y w) : w - catalyst S x ∈ fixedSpace S := by
  have hw : feedback S w = publicToPrivate S x :=
    (feedback_eq_iff S x w).mpr (congrArg WithLp.snd h)
  change feedback S (w - catalyst S x) = 0
  rw [map_sub, hw, catalyst_feedback, sub_self]

/-- Public outputs do not depend on the choice of catalyst. -/
theorem output_unique {x y : H} {w : L}
    (h : S (pair x w) = pair y w) : y = publicAction S x := by
  have hf := fixedSpace_fixed S (catalyst_sub_mem_fixed S h)
  have he : S (pair 0 (w - catalyst S x)) =
      pair (y - publicAction S x) (w - catalyst S x) := by
    calc
      _ = S (pair x w - pair x (catalyst S x)) := by rw [← pair_sub, sub_self]
      _ = _ := by rw [map_sub, h, transduction_eq, ← pair_sub]
  have hh := congrArg WithLp.fst (hf.symm.trans he)
  exact sub_eq_zero.mp hh.symm

/-- The public unitary itself is uniquely characterized by transduction. -/
theorem publicAction_unique (U : H ≃ₗᵢ[ℂ] H)
    (h : ∀ x, ∃ w, S (pair x w) = pair (U x) w) : U = publicAction S := by
  ext x
  obtain ⟨w, hw⟩ := h x
  exact output_unique S hw

/-- Orthogonality to the private fixed-point kernel uniquely selects the catalyst. -/
theorem catalyst_orthogonal_unique {x y : H} {w : L}
    (h : S (pair x w) = pair y w) (hm : w ∈ (fixedSpace S)ᗮ) :
    w = catalyst S x := by
  apply orthogonal_catalyst_unique S hm
  exact (feedback_eq_iff S x w).mpr (congrArg WithLp.snd h)

/-- Every possible catalyst has exactly the canonical squared norm plus the
squared norm of its private-fixed-point component. -/
theorem catalyst_norm_sq_decomposition {x y : H} {w : L}
    (h : S (pair x w) = pair y w) :
    ‖w‖ ^ 2 = ‖catalyst S x‖ ^ 2 + ‖w - catalyst S x‖ ^ 2 := by
  have hz := (fixedSpace S).inner_left_of_mem_orthogonal
    (catalyst_sub_mem_fixed S h) (catalyst_mem S x)
  have hn := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
    (catalyst S x) (w - catalyst S x) hz
  simpa only [add_sub_cancel, pow_two] using hn

/-- The canonical catalyst has minimum norm among all catalysts. -/
theorem catalyst_minimum_norm {x y : H} {w : L}
    (h : S (pair x w) = pair y w) : ‖catalyst S x‖ ≤ ‖w‖ := by
  have hd := catalyst_norm_sq_decomposition S h
  nlinarith [norm_nonneg w, norm_nonneg (catalyst S x), sq_nonneg ‖w - catalyst S x‖]

/-- Equality in the minimum-norm bound uniquely characterizes the canonical catalyst. -/
theorem catalyst_minimum_norm_unique {x y : H} {w : L}
    (h : S (pair x w) = pair y w) (hn : ‖w‖ = ‖catalyst S x‖) :
    w = catalyst S x := by
  have hd := catalyst_norm_sq_decomposition S h
  rw [hn] at hd
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  nlinarith [norm_nonneg (w - catalyst S x)]

/-- Canonical orthogonality and minimum norm as one source-level theorem. -/
theorem universal_public_transduction :
    ∃ U : H ≃ₗᵢ[ℂ] H, ∃ V : H →ₗ[ℂ] L,
      (∀ x, S (pair x (V x)) = pair (U x) (V x)) ∧
      (∀ x, V x ∈ (fixedSpace S)ᗮ) ∧
      (∀ x y w, S (pair x w) = pair y w → y = U x) ∧
      (∀ x y w, S (pair x w) = pair y w → ‖V x‖ ≤ ‖w‖) ∧
      (∀ x y w, S (pair x w) = pair y w → ‖w‖ = ‖V x‖ → w = V x) := by
  exact ⟨publicAction S, catalyst S, transduction_eq S, catalyst_mem S,
    fun _ _ _ h => output_unique S h,
    fun _ _ _ h => catalyst_minimum_norm S h,
    fun _ _ _ h hn => catalyst_minimum_norm_unique S h hn⟩

end OptimalQLS.Transduction
