import OptimalQLS.Geometry.Lemma42

noncomputable section
namespace OptimalQLS.Geometry
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Hermitian operators reverse a Hermitian product. -/
theorem symmetric_reverse_product (S T R : E →L[ℂ] E)
    (hS : S.toLinearMap.IsSymmetric) (hT : T.toLinearMap.IsSymmetric)
    (hR : R.toLinearMap.IsSymmetric) (h : S * T = R) : T * S = R := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_right ℂ
  intro y
  have hy : S (T y) = R y := by
    simpa using congrArg (fun L : E →L[ℂ] E => L y) h
  calc
    inner ℂ ((T * S) x) y = inner ℂ (S x) (T y) := hT _ _
    _ = inner ℂ x (S (T y)) := hS _ _
    _ = inner ℂ x (R y) := by rw [hy]
    _ = inner ℂ (R x) y := (hR _ _).symm

/-- The four defining Moore–Penrose equations determine at most one
bounded operator. No diagonalization or nonsingularity is assumed. -/
theorem moore_penrose_unique (H Q R : E →L[ℂ] E)
    (hQ₁ : H * Q * H = H) (hQ₂ : Q * H * Q = Q)
    (hQ₃ : (H * Q).toLinearMap.IsSymmetric)
    (hQ₄ : (Q * H).toLinearMap.IsSymmetric)
    (hR₁ : H * R * H = H) (hR₂ : R * H * R = R)
    (hR₃ : (H * R).toLinearMap.IsSymmetric)
    (hR₄ : (R * H).toLinearMap.IsSymmetric) : Q = R := by
  have hHQHR : (H * Q) * (H * R) = H * R := by
    rw [← mul_assoc, hQ₁]
  have hHRHQ : (H * R) * (H * Q) = H * Q := by
    rw [← mul_assoc, hR₁]
  have hrange : H * Q = H * R :=
    hHRHQ.symm.trans (symmetric_reverse_product _ _ _ hQ₃ hR₃ hR₃ hHQHR)
  have hQHRH : (Q * H) * (R * H) = Q * H := by
    calc
      (Q * H) * (R * H) = Q * (H * R * H) := by simp only [mul_assoc]
      _ = Q * H := by rw [hR₁]
  have hRHQH : (R * H) * (Q * H) = R * H := by
    calc
      (R * H) * (Q * H) = R * (H * Q * H) := by simp only [mul_assoc]
      _ = R * H := by rw [hQ₁]
  have hdomain : Q * H = R * H :=
    (symmetric_reverse_product _ _ _ hQ₄ hR₄ hQ₄ hQHRH).symm.trans hRHQH
  calc
    Q = Q * H * Q := hQ₂.symm
    _ = Q * (H * Q) := mul_assoc _ _ _
    _ = Q * (H * R) := by rw [hrange]
    _ = (Q * H) * R := (mul_assoc _ _ _).symm
    _ = (R * H) * R := by rw [hdomain]
    _ = R := hR₂

variable [FiniteDimensional ℂ E]

/-- Unambiguous semantics endpoint: any Moore–Penrose inverse of the paper's
auxiliary matrix equals `auxiliaryPseudoInverse`. -/
theorem lemma42_pseudoinverse_unique (A : E →L[ℂ] E)
    (hA : A.toLinearMap.IsSymmetric) {κ : ℝ} (hκ : 0 < κ)
    (R : Block E →L[ℂ] Block E)
    (hR₁ : blockAuxiliary A κ⁻¹ * R * blockAuxiliary A κ⁻¹ = blockAuxiliary A κ⁻¹)
    (hR₂ : R * blockAuxiliary A κ⁻¹ * R = R)
    (hR₃ : (blockAuxiliary A κ⁻¹ * R).toLinearMap.IsSymmetric)
    (hR₄ : (R * blockAuxiliary A κ⁻¹).toLinearMap.IsSymmetric) :
    R = auxiliaryPseudoInverse A hA κ⁻¹ := by
  obtain ⟨hQ₁,hQ₂,hQ₃,hQ₄⟩ := lemma42_moore_penrose A hA hκ
  exact moore_penrose_unique _ _ _ hR₁ hR₂ hR₃ hR₄ hQ₁ hQ₂ hQ₃ hQ₄

end OptimalQLS.Geometry
