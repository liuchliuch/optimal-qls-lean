import OptimalQLS.PhysicalRobustness.SpectralCutoff
import OptimalQLS.Perturbation.Lemma71

/-! The actual noisy low-spectral subspace has controlled overlap with the
original invertible support.  No padded inverse and no global invertibility
of the actual encoded matrix are used. -/
noncomputable section
namespace OptimalQLS.PhysicalRobustness

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]

/-- A dimension-free low-subspace bound, obtained from the Sylvester identity
`QJA = BQJ − Q(B−H)J` and the original inverse norm. -/
theorem lowProjector_active_norm
    (J : E →ₗᵢ[ℂ] F) (A : E →L[ℂ] E) (hA : IsUnit A)
    (H B : F →L[ℂ] F) (hB : B.toLinearMap.IsSymmetric)
    (hHJ : ∀ x, H (J x) = J (A x))
    {κ δ : ℝ} (hκ : 0 ≤ κ) (hδ : 0 ≤ δ)
    (hinv : ‖Ring.inverse A‖ ≤ κ) (hpert : ‖B-H‖ ≤ δ) (hsmall : κ*δ < 1) :
    ‖(lowProjector B hB δ).comp J.toContinuousLinearMap‖ ≤ κ*δ/(1-κ*δ) := by
  let Q := lowProjector B hB δ
  let L := Q.comp J.toContinuousLinearMap
  have hQ : ‖Q‖ ≤ 1 := lowProjector_norm_le_one B hB δ
  have hQB : ‖B*Q‖ ≤ δ := lowPart_norm B hB hδ
  have hq (v : F) : Q (Q v) = Q v := by
    exact congrArg (fun T : F →L[ℂ] F => T v) (lowProjector_idempotent B hB δ)
  have hcomm (v : F) : Q (B v) = B (Q v) := by
    exact congrArg (fun T : F →L[ℂ] F => T v) (lowProjector_commutes B hB δ)
  have hidentity (x : E) :
      L x = (B*Q) (L (Ring.inverse A x)) - Q ((B-H) (J (Ring.inverse A x))) := by
    change Q (J x) = B (Q (Q (J (Ring.inverse A x)))) -
      Q (B (J (Ring.inverse A x))-H (J (Ring.inverse A x)))
    rw [hq, map_sub, hcomm, hHJ, Perturbation.apply_inverse A hA]
    abel
  have hinvx (x : E) : ‖Ring.inverse A x‖ ≤ κ*‖x‖ :=
    ((Ring.inverse A).le_opNorm x).trans (mul_le_mul_of_nonneg_right hinv (norm_nonneg x))
  have hbound : ‖L‖ ≤ δ*‖L‖*κ+δ*κ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro x
    rw [hidentity]
    calc
      _ ≤ ‖(B*Q) (L (Ring.inverse A x))‖ + ‖Q ((B-H) (J (Ring.inverse A x)))‖ := norm_sub_le _ _
      _ ≤ δ*‖L (Ring.inverse A x)‖ + ‖(B-H) (J (Ring.inverse A x))‖ := by
        apply add_le_add
        · exact ((B*Q).le_opNorm _).trans (mul_le_mul_of_nonneg_right hQB (norm_nonneg _))
        · exact (Q.le_opNorm _).trans ((mul_le_mul_of_nonneg_right hQ (norm_nonneg _)).trans_eq (one_mul _))
      _ ≤ δ*(‖L‖*(κ*‖x‖)) + δ*(κ*‖x‖) := by
        apply add_le_add
        · apply mul_le_mul_of_nonneg_left _ hδ
          exact (L.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hinvx x) (norm_nonneg _))
        · exact ((B-H).le_opNorm _).trans (by
            rw [J.norm_map]
            exact mul_le_mul hpert (hinvx x) (norm_nonneg _) hδ)
      _ = (δ*‖L‖*κ+δ*κ)*‖x‖ := by ring
  change ‖L‖ ≤ _
  apply (le_div_iff₀ (sub_pos.mpr hsmall)).mpr
  nlinarith

/-- Pointwise version on any original active vector. -/
theorem lowProjector_active_apply
    (J : E →ₗᵢ[ℂ] F) (A : E →L[ℂ] E) (hA : IsUnit A)
    (H B : F →L[ℂ] F) (hB : B.toLinearMap.IsSymmetric)
    (hHJ : ∀ x, H (J x) = J (A x))
    {κ δ : ℝ} (hκ : 0 ≤ κ) (hδ : 0 ≤ δ)
    (hinv : ‖Ring.inverse A‖ ≤ κ) (hpert : ‖B-H‖ ≤ δ) (hsmall : κ*δ < 1)
    (x : E) : ‖lowProjector B hB δ (J x)‖ ≤ (κ*δ/(1-κ*δ))*‖x‖ := by
  exact (((lowProjector B hB δ).comp J.toContinuousLinearMap).le_opNorm x).trans
    (mul_le_mul_of_nonneg_right
      (lowProjector_active_norm J A hA H B hB hHJ hκ hδ hinv hpert hsmall) (norm_nonneg x))

end OptimalQLS.PhysicalRobustness
