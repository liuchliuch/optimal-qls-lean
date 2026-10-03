import QuantumChannelStein.TraceNormBounds
import OptimalQLS.LowerBounds.BlockNorms

/-!
# Genuine trace distance and concrete finite Kraus channels

The imported norm is literally Re tr sqrt(X†X), with preserved provenance.
All channel actions below are finite Kraus sums with proved normalization.
These lemmas supply the actual one-query, channel-contraction and abort-mass
estimates for the stopping-time argument.
-/
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
namespace OptimalQLS.LowerBounds
open Matrix QuantumChannelStein.TraceNorm

variable {D E : Type*} [Fintype D] [DecidableEq D] [Fintype E] [DecidableEq E]

lemma traceNorm_positive_eq_trace (X : Matrix D D ℂ) (hX : X.PosSemidef) :
    traceNorm X = X.trace.re := by
  rw [traceNorm, hX.isHermitian.eq, ← pow_two, CFC.sqrt_sq X hX.nonneg]

@[simp] lemma traceNorm_negative (X : Matrix D D ℂ) : traceNorm (-X) = traceNorm X := by
  simp [traceNorm]

def traceDistance (X Y : Matrix D D ℂ) : ℝ := traceNorm (X - Y) / 2

theorem traceDistance_nonneg (X Y : Matrix D D ℂ) : 0 ≤ traceDistance X Y := by
  exact div_nonneg (traceNorm_nonneg _) (by norm_num)

@[simp] theorem traceDistance_self (X : Matrix D D ℂ) : traceDistance X X = 0 := by simp [traceDistance]

theorem traceDistance_symm (X Y : Matrix D D ℂ) : traceDistance X Y = traceDistance Y X := by
  have h : X - Y = -(Y - X) := by abel
  simp only [traceDistance, h, traceNorm_negative]

theorem traceDistance_triangle (X Y Z : Matrix D D ℂ) :
    traceDistance X Z ≤ traceDistance X Y + traceDistance Y Z := by
  have heq : X - Z = (X - Y) + (Y - Z) := by abel
  have h := traceNorm_add_le (X - Y) (Y - Z)
  rw [← heq] at h
  unfold traceDistance
  linarith

/-- A finite, explicit Kraus channel on arbitrary finite basis types. -/
structure FiniteChannel (D E : Type*) [Fintype D] [DecidableEq D] [Fintype E] where
  rank : ℕ
  kraus : Fin rank → Matrix E D ℂ
  normalized : ∑ i, (kraus i).conjTranspose * kraus i = 1

def FiniteChannel.apply (F : FiniteChannel D E) (X : Matrix D D ℂ) : Matrix E E ℂ :=
  ∑ i, F.kraus i * X * (F.kraus i).conjTranspose

@[simp] theorem FiniteChannel.apply_zero (F : FiniteChannel D E) : F.apply 0 = 0 := by simp [FiniteChannel.apply]

theorem FiniteChannel.apply_add (F : FiniteChannel D E) (X Y : Matrix D D ℂ) :
    F.apply (X + Y) = F.apply X + F.apply Y := by
  simp [FiniteChannel.apply, Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib]

theorem FiniteChannel.apply_sub (F : FiniteChannel D E) (X Y : Matrix D D ℂ) :
    F.apply (X - Y) = F.apply X - F.apply Y := by
  simp [FiniteChannel.apply, Matrix.mul_sub, Matrix.sub_mul, Finset.sum_sub_distrib]

theorem FiniteChannel.apply_positive (F : FiniteChannel D E) {X : Matrix D D ℂ} (hX : X.PosSemidef) :
    (F.apply X).PosSemidef := by
  unfold FiniteChannel.apply
  exact Finset.sum_induction _ _ (fun _ _ hA hB => hA.add hB) Matrix.PosSemidef.zero
    (fun i _ => hX.mul_mul_conjTranspose_same (F.kraus i))

theorem FiniteChannel.trace_apply (F : FiniteChannel D E) (X : Matrix D D ℂ) :
    (F.apply X).trace = X.trace := by
  unfold FiniteChannel.apply
  rw [Matrix.trace_sum]
  conv_lhs => arg 2; ext i; rw [Matrix.trace_mul_cycle]
  rw [← Matrix.trace_sum, ← Matrix.sum_mul, F.normalized, Matrix.one_mul]

/-- Convert any actual finite normalized Kraus family, without changing its action. -/
def FiniteChannel.ofKraus {I : Type*} [Fintype I]
    (K : I → Matrix E D ℂ) (hK : ∑ i, (K i).conjTranspose * K i = 1) : FiniteChannel D E where
  rank := Fintype.card I
  kraus := fun i => K ((Fintype.equivFin I).symm i)
  normalized := by
    exact (Equiv.sum_comp (Fintype.equivFin I).symm
      (fun i => (K i).conjTranspose * K i)).trans hK

theorem FiniteChannel.ofKraus_apply {I : Type*} [Fintype I]
    (K : I → Matrix E D ℂ) (hK : ∑ i, (K i).conjTranspose * K i = 1) (X : Matrix D D ℂ) :
    (FiniteChannel.ofKraus K hK).apply X = ∑ i, K i * X * (K i).conjTranspose := by
  unfold FiniteChannel.apply FiniteChannel.ofKraus
  exact Equiv.sum_comp (Fintype.equivFin I).symm (fun i => K i * X * (K i).conjTranspose)

def FiniteChannel.stinespring (F : FiniteChannel D E) : Matrix (E × Fin F.rank) D ℂ :=
  fun x j => F.kraus x.2 x.1 j

theorem FiniteChannel.stinespring_isometry (F : FiniteChannel D E) :
    F.stinespring.conjTranspose * F.stinespring = 1 := by
  ext i j
  have h := congrFun (congrFun F.normalized i) j
  simp only [FiniteChannel.stinespring, Matrix.sum_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Fintype.sum_prod_type] at h ⊢
  rw [Finset.sum_comm]
  exact h

theorem matrix_isometry_norm_le_one (V : Matrix E D ℂ) (hV : V.conjTranspose * V = 1) : ‖V‖ ≤ 1 := by
  cases isEmpty_or_nonempty D with
  | inl hD =>
    letI := hD
    have hz : V = 0 := Subsingleton.elim _ _
    simp [hz]
  | inr hD =>
    letI := hD
    have h := Matrix.l2_opNorm_conjTranspose_mul_self V
    rw [hV, norm_one] at h
    nlinarith [norm_nonneg V]

theorem FiniteChannel.stinespring_norm_le_one (F : FiniteChannel D E) : ‖F.stinespring‖ ≤ 1 :=
  matrix_isometry_norm_le_one _ F.stinespring_isometry

theorem FiniteChannel.traceEnvironment_stinespring (F : FiniteChannel D E) (X : Matrix D D ℂ) :
    QuantumChannelStein.ReferenceAcceptance.traceEnvironment
      (F.stinespring * X * F.stinespring.conjTranspose) = F.apply X := by
  ext i j
  simp [QuantumChannelStein.ReferenceAcceptance.traceEnvironment, FiniteChannel.stinespring,
    FiniteChannel.apply, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]

/-- Actual CPTP contraction for every matrix, obtained from its explicit Stinespring matrix. -/
theorem FiniteChannel.traceNorm_contract (F : FiniteChannel D E) (X : Matrix D D ℂ) :
    traceNorm (F.apply X) ≤ traceNorm X := by
  rw [← F.traceEnvironment_stinespring]
  apply (traceNorm_partialTrace_le _).trans
  apply (traceNorm_sandwich_le _ _ _).trans
  rw [Matrix.l2_opNorm_conjTranspose]
  have hV := F.stinespring_norm_le_one
  have hX := traceNorm_nonneg X
  calc
    _ ≤ 1 * traceNorm X * 1 := by gcongr
    _ = traceNorm X := by ring

theorem FiniteChannel.traceDistance_contract (F : FiniteChannel D E) (X Y : Matrix D D ℂ) :
    traceDistance (F.apply X) (F.apply Y) ≤ traceDistance X Y := by
  unfold traceDistance
  rw [← F.apply_sub]
  exact div_le_div_of_nonneg_right (F.traceNorm_contract (X - Y)) (by norm_num)

/-- Literal one-query trace-distance bound for an arbitrary density matrix. -/
theorem unitary_query_traceDistance (U V : Matrix.unitaryGroup D ℂ) (rho : Matrix D D ℂ)
    (hrho : rho.PosSemidef) (htrace : rho.trace = 1) :
    traceDistance ((U : Matrix D D ℂ) * rho * (U : Matrix D D ℂ).conjTranspose)
      ((V : Matrix D D ℂ) * rho * (V : Matrix D D ℂ).conjTranspose) ≤
      ‖(U : Matrix D D ℂ) - (V : Matrix D D ℂ)‖ := by
  have h := traceNorm_dilation_difference_le (U : Matrix D D ℂ) (V : Matrix D D ℂ) rho
  rw [traceNorm_positive_eq_trace rho hrho, htrace] at h
  have hU := unitary_opNorm_le_one U
  have hV := unitary_opNorm_le_one V
  have hd := norm_nonneg ((U : Matrix D D ℂ) - (V : Matrix D D ℂ))
  unfold traceDistance
  simp only [Complex.one_re, mul_one] at h
  nlinarith

/-- An actual bounded observable controls probability differences. The factor2
is enough for the stopping proof and avoids requiring tracelessness here. -/
theorem bounded_observable_difference (T X Y : Matrix D D ℂ) (hT : ‖T‖ ≤ 1) :
    |(T * X).trace.re - (T * Y).trace.re| ≤ 2 * traceDistance X Y := by
  have heq : (T * X).trace.re - (T * Y).trace.re = (T * (X - Y)).trace.re := by
    simp [Matrix.mul_sub, Matrix.trace_sub]
  rw [heq]
  have h := (Complex.abs_re_le_norm ((T * (X - Y)).trace)).trans (norm_trace_mul_le T (X - Y))
  have ht := mul_le_of_le_one_left (traceNorm_nonneg (X - Y)) hT
  unfold traceDistance
  nlinarith

/-- Agreement off an abort event is a PSD-residual identity, not a coupling
assumption: once those actual residuals have equal trace r, distance≤r. -/
theorem traceDistance_common_positive_residual (G R S : Matrix D D ℂ)
    (hR : R.PosSemidef) (hS : S.PosSemidef) (r : ℝ)
    (hRt : R.trace.re = r) (hSt : S.trace.re = r) :
    traceDistance (G + R) (G + S) ≤ r := by
  have heq : (G + R) - (G + S) = R + (-S) := by abel
  have h := traceNorm_add_le R (-S)
  rw [traceNorm_negative, traceNorm_positive_eq_trace R hR, traceNorm_positive_eq_trace S hS,
    hRt, hSt] at h
  unfold traceDistance
  rw [heq]
  linarith

end OptimalQLS.LowerBounds
