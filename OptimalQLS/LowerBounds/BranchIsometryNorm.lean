import OptimalQLS.LowerBounds.FiniteProgramKraus

/-! Operator norms of literal branch stacks after a normalized instrument. -/
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
namespace OptimalQLS.LowerBounds
open Matrix

variable {I D J : Type*} [Fintype I] [Fintype D] [DecidableEq D] [Fintype J]
  {E : I → Type*} [∀ i, Fintype (E i)]

def branchComposition (dim : I → ℕ) (F : ∀ i, Matrix (E i × J) (Fin (dim i)) ℂ)
    (K : ∀ i, Matrix (Fin (dim i)) D ℂ) : Matrix (((i : I) × E i) × J) D ℂ :=
  fun row col => (F row.1.1 * K row.1.1) (row.1.2, row.2) col

set_option maxHeartbeats 1000000 in
theorem branchComposition_norm_le (dim : I → ℕ) (F : ∀ i, Matrix (E i × J) (Fin (dim i)) ℂ)
    (K : ∀ i, Matrix (Fin (dim i)) D ℂ) (hK : ∑ i, (K i).conjTranspose * K i = 1)
    (c : ℝ) (hc : 0 ≤ c) (hF : ∀ i, ‖F i‖ ≤ c) : ‖branchComposition dim F K‖ ≤ c := by
  classical
  rw [Matrix.l2_opNorm_def]
  apply ContinuousLinearMap.opNorm_le_bound _ hc
  intro x
  have hbound (i : I) : ‖WithLp.toLp 2 ((F i) *ᵥ ((K i) *ᵥ (fun j => x j)))‖ ≤
      c * ‖WithLp.toLp 2 ((K i) *ᵥ (fun j => x j))‖ :=
    ((F i).l2_opNorm_mulVec (WithLp.toLp 2 ((K i) *ᵥ (fun j => x j)))).trans (mul_le_mul_of_nonneg_right (hF i) (norm_nonneg _))
  have hsum : (∑ i, ‖WithLp.toLp 2 ((K i) *ᵥ (fun j => x j))‖ ^ 2) = ‖x‖ ^ 2 := by
    simpa only [bornMass_eq_norm_sq] using varying_instrument_bornMass dim K hK (fun j => x j)
  have hout : ‖WithLp.toLp 2 ((branchComposition dim F K) *ᵥ (fun j => x j))‖ ^ 2 =
      ∑ i, ‖WithLp.toLp 2 ((F i) *ᵥ ((K i) *ᵥ (fun j => x j)))‖ ^ 2 := by
    simp only [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type, Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro e _
    apply Finset.sum_congr rfl
    intro j _
    congr 2
    change ((F i * K i) *ᵥ (fun j => x j)) (e, j) = _
    rw [← Matrix.mulVec_mulVec]
  change ‖WithLp.toLp 2 ((branchComposition dim F K) *ᵥ (fun j => x j))‖ ≤ c * ‖x‖
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hc (norm_nonneg _))).mp
  rw [hout, mul_pow]
  calc
    _ ≤ ∑ i, (c * ‖WithLp.toLp 2 ((K i) *ᵥ (fun j => x j))‖) ^ 2 :=
      Finset.sum_le_sum (fun i _ => pow_le_pow_left₀ (norm_nonneg _) (hbound i) 2)
    _ = c ^ 2 * ∑ i, ‖WithLp.toLp 2 ((K i) *ᵥ (fun j => x j))‖ ^ 2 := by simp [mul_pow, Finset.mul_sum]
    _ = _ := by rw [hsum]

end OptimalQLS.LowerBounds
