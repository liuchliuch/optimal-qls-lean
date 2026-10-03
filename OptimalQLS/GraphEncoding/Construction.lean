import OptimalQLS.PolynomialTransform.QSVTCircuit
import OptimalQLS.TransducerCompiler.HadamardClock

/-! # Literal Hermitian block encoding of the padded auxiliary graph -/
noncomputable section
set_option synthInstance.maxSize 512
namespace OptimalQLS.GraphEncoding
open Matrix PolynomialTransform
open scoped Kronecker ComplexConjugate Matrix.Norms.L2Operator

variable {S D W B : Type*} [Fintype S] [DecidableEq S]
  [Fintype D] [DecidableEq D] [Fintype W] [DecidableEq W]
  [Fintype B] [DecidableEq B]

/-- The graph occupies exactly labels 0, 1, 2; label 3 is a zero sector. -/
def graphMatrix (A : Matrix D D ℂ) (κ : ℝ) : Matrix (Fin 4 × D) (Fin 4 × D) ℂ :=
  fun i j => if (i.1 = 0 ∧ j.1 = 1) ∨ (i.1 = 1 ∧ j.1 = 0) then A i.2 j.2
    else if (i.1 = 0 ∧ j.1 = 2) ∨ (i.1 = 2 ∧ j.1 = 0) then
      -(κ⁻¹ : ℂ) * (1 : Matrix D D ℂ) i.2 j.2 else 0

@[simp] theorem graphMatrix_unused_row (A : Matrix D D ℂ) (κ : ℝ) (d : D) (j : Fin 4 × D) :
    graphMatrix A κ (3,d) j = 0 := by simp [graphMatrix]
@[simp] theorem graphMatrix_unused_column (A : Matrix D D ℂ) (κ : ℝ) (d : D) (i : Fin 4 × D) :
    graphMatrix A κ i (3,d) = 0 := by simp [graphMatrix]

def hermitianSignal (U : Matrix.unitaryGroup W ℂ) : Matrix.unitaryGroup (W ⊕ W) ℂ :=
  sumHadamard W * LowerBounds.hermitianUnitaryDilation U * (sumHadamard W)⁻¹

theorem hermitianSignal_hermitian (U : Matrix.unitaryGroup W ℂ) :
    (hermitianSignal U : Matrix (W ⊕ W) (W ⊕ W) ℂ).IsHermitian := by
  change ((sumHadamard W).val *
    (LowerBounds.hermitianUnitaryDilation U).val *
    (sumHadamard W).valᴴ).IsHermitian
  simp only [Matrix.IsHermitian, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  rw [LowerBounds.hermitianUnitaryDilation,
    LowerBounds.hermitianDilation_hermitian]
  simp [Matrix.mul_assoc]

theorem sumHadamard_inv : (sumHadamard W)⁻¹ = sumHadamard W := by
  apply Subtype.ext
  change (fractionalMix (-halfAmplitude))ᴴ = fractionalMix (-halfAmplitude)
  exact fractionalMix_selfAdjoint _

theorem hermitianSignal_left_entries (U : Matrix.unitaryGroup W ℂ) (i j : W) :
    (hermitianSignal U).val (.inl i) (.inl j) =
      (1/2 : ℂ) * ((U : Matrix W W ℂ) i j + (U : Matrix W W ℂ)ᴴ i j) := by
  unfold hermitianSignal
  rw [sumHadamard_inv]
  change ((sumHadamard W).val *
    LowerBounds.hermitianDilation (U : Matrix W W ℂ) *
    (sumHadamard W).val) (.inl i) (.inl j) = _
  rw [sumHadamard_matrix, LowerBounds.hermitianDilation,
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp only [Matrix.zero_mul, Matrix.mul_zero, Matrix.one_mul, Matrix.mul_one,
    zero_add, add_zero, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    ← pow_two, halfAmplitude_sq, Matrix.fromBlocks_apply₁₁]
  simp only [Matrix.add_apply, Matrix.smul_apply, Complex.real_smul]
  push_cast
  ring

/-- Oracle Hermitianization does not assume that the input unitary is Hermitian. -/
theorem hermitianSignal_block (s : S) (U : Matrix.unitaryGroup (S × D) ℂ)
    (A : Matrix D D ℂ) (hA : A.IsHermitian)
    (h : IsBlockEncoding s 1 0 U A) (i j : D) :
    (hermitianSignal U).val (.inl (s,i)) (.inl (s,j)) = A i j := by
  have hb : signalBlock s U.val = A := by simpa using (exact_block_eq h).symm
  have he (i j : D) : U.val (s,i) (s,j) = A i j := by
    simpa only [signalBlock_entries] using congrFun (congrFun hb i) j
  rw [hermitianSignal_left_entries]
  simp only [Matrix.conjTranspose_apply, he]
  have ha : star (A j i) = A i j := congrFun (congrFun hA i) j
  rw [ha]
  ring

abbrev Label := Bool × Fin 4

/-- An involution swapping 0 and j in the clean sector, and flipping the
signal bit on the two unused labels. -/
def labelAction (j : Fin 4) (p : Label) : Label :=
  if p.2 = 0 then (p.1,j) else if p.2 = j then (p.1,0) else (!p.1,p.2)

theorem labelAction_involutive (j : Fin 4) (hj : j ≠ 0) : Function.Involutive (labelAction j) := by
  intro p
  rcases p with ⟨z,g⟩
  by_cases h0 : g = 0
  · subst g; simp [labelAction, hj]
  · by_cases hgj : g = j
    · subst g; simp [labelAction, hj]
    · simp [labelAction, h0, hgj]

def labelPermutation (j : Fin 4) (hj : j ≠ 0) : Equiv.Perm Label :=
  (labelAction_involutive j hj).toPerm

def labelUnitary (j : Fin 4) (hj : j ≠ 0) : Matrix.unitaryGroup Label ℂ :=
  TransducerCompiler.permutation (labelPermutation j hj)

theorem labelUnitary_hermitian (j : Fin 4) (hj : j ≠ 0) :
    (labelUnitary j hj : Matrix Label Label ℂ).IsHermitian := by
  change ((labelPermutation j hj).permMatrix ℂ)ᴴ = _
  rw [Matrix.conjTranspose_permMatrix]
  rfl

@[simp] theorem labelUnitary_entries (j : Fin 4) (hj : j ≠ 0) (p q : Label) :
    (labelUnitary j hj : Matrix Label Label ℂ) p q = if labelAction j p = q then 1 else 0 := by
  simp [labelUnitary, TransducerCompiler.permutation, labelPermutation, Function.Involutive.toPerm, PEquiv.toMatrix, eq_comm]

/-- The signal-zero block is exactly the rank-two X edge, including zero on label 3. -/
theorem labelUnitary_zero_block (j : Fin 4) (hj : j ≠ 0) (g h : Fin 4) :
    (labelUnitary j hj : Matrix Label Label ℂ) (false,g) (false,h) =
      if (g = 0 ∧ h = j) ∨ (g = j ∧ h = 0) then 1 else 0 := by
  rw [labelUnitary_entries]
  by_cases hg0 : g = 0
  · subst g; simp [labelAction, hj, eq_comm]
  · by_cases hgj : g = j
    · subst g; simp [labelAction, hj, eq_comm]
    · simp [labelAction, hg0, hgj]

abbrev tensorUnitary := @TransducerCompiler.HadamardClock.tensorUnitary

/-- First branch: an edge dilation tensor the Hermitianized arbitrary oracle. -/
def branchA (U : Matrix.unitaryGroup (S × D) ℂ) :
    Matrix.unitaryGroup (Label × ((S × D) ⊕ (S × D))) ℂ :=
  tensorUnitary (labelUnitary 1 (by decide)) (hermitianSignal U)

/-- Second branch: the negative edge, with identity on all oracle registers. -/
def branchI (S D : Type*) [Fintype S] [DecidableEq S] [Fintype D] [DecidableEq D] :
    Matrix.unitaryGroup (Label × ((S × D) ⊕ (S × D))) ℂ :=
  tensorUnitary (-(labelUnitary 2 (by decide))) 1

theorem branchA_hermitian (U : Matrix.unitaryGroup (S × D) ℂ) :
    (branchA U).val.IsHermitian := by
  change (_ ⊗ₖ _).IsHermitian
  rw [Matrix.IsHermitian, Matrix.conjTranspose_kronecker,
    labelUnitary_hermitian, hermitianSignal_hermitian]

theorem branchI_hermitian : (branchI S D).val.IsHermitian := by
  change ((-(labelUnitary 2 (by decide) : Matrix Label Label ℂ)) ⊗ₖ (1 : Matrix _ _ ℂ)).IsHermitian
  rw [Matrix.IsHermitian, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_neg,
    labelUnitary_hermitian, Matrix.conjTranspose_one]

/-- Weighted mixing amplitudes use only κ. -/
def mixAmplitude (κ : ℝ) : ℝ := Real.sqrt ((1 + κ⁻¹)⁻¹)

theorem mixAmplitude_properties {κ : ℝ} (hκ : 0 < κ) :
    mixAmplitude κ ^ 2 = (1 + κ⁻¹)⁻¹ ∧ |(-mixAmplitude κ)| < 1 := by
  have ht : 0 < κ⁻¹ := inv_pos.mpr hκ
  have hα : 0 < 1 + κ⁻¹ := by linarith
  have hs : mixAmplitude κ ^ 2 = (1 + κ⁻¹)⁻¹ := Real.sq_sqrt (inv_nonneg.mpr hα.le)
  refine ⟨hs, ?_⟩
  rw [abs_neg, abs_of_nonneg (show 0 ≤ mixAmplitude κ from Real.sqrt_nonneg _)]
  have hi : (1 + κ⁻¹)⁻¹ < 1 := by rw [inv_lt_one₀ hα]; linarith
  nlinarith [Real.sqrt_nonneg ((1 + κ⁻¹)⁻¹)]

def weightedMix (W : Type*) [Fintype W] [DecidableEq W] (κ : ℝ) (hκ : 0 < κ) :
    Matrix.unitaryGroup (W ⊕ W) ℂ :=
  ⟨fractionalMix (-mixAmplitude κ), fractionalMix_unitary (mixAmplitude_properties hκ).2⟩

theorem weightedMix_hermitian (κ : ℝ) (hκ : 0 < κ) :
    (weightedMix W κ hκ).val.IsHermitian := fractionalMix_selfAdjoint _

/-- Two literal SELECT branches conjugated by a one-qubit real mixing. -/
def weightedSelect (κ : ℝ) (hκ : 0 < κ) (U V : Matrix.unitaryGroup W ℂ) :
    Matrix.unitaryGroup (W ⊕ W) ℂ :=
  weightedMix W κ hκ * sumUnitary U V * (weightedMix W κ hκ)⁻¹

theorem weightedSelect_hermitian (κ : ℝ) (hκ : 0 < κ) (U V : Matrix.unitaryGroup W ℂ)
    (hU : (U : Matrix W W ℂ).IsHermitian) (hV : (V : Matrix W W ℂ).IsHermitian) :
    (weightedSelect κ hκ U V).val.IsHermitian := by
  change ((weightedMix W κ hκ).val *
    Matrix.fromBlocks (U : Matrix W W ℂ) 0 0 (V : Matrix W W ℂ) *
    (weightedMix W κ hκ).valᴴ).IsHermitian
  simp only [Matrix.IsHermitian, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_zero]
  rw [hU, hV]
  simp [Matrix.mul_assoc]

theorem weightedSelect_left_entries (κ : ℝ) (hκ : 0 < κ)
    (U V : Matrix.unitaryGroup W ℂ) (i j : W) :
    (weightedSelect κ hκ U V).val (.inl i) (.inl j) =
      ((1 + κ⁻¹)⁻¹ : ℂ) * (U : Matrix W W ℂ) i j +
        ((1 + κ⁻¹)⁻¹ * κ⁻¹ : ℂ) * (V : Matrix W W ℂ) i j := by
  have hs := (mixAmplitude_properties hκ).1
  have hn : 0 ≤ 1 - (-mixAmplitude κ)^2 := by
    have hb := (mixAmplitude_properties hκ).2
    nlinarith [(abs_lt.mp hb).1, (abs_lt.mp hb).2]
  have ht := Real.sq_sqrt hn
  simp only [neg_sq, hs] at ht
  have ht' : Real.sqrt (1 - (1 + κ⁻¹)⁻¹) ^ 2 = (1 + κ⁻¹)⁻¹ * κ⁻¹ := by
    rw [ht]
    field_simp
    ring
  have hα : 1 + κ⁻¹ ≠ 0 := ne_of_gt (by positivity : 0 < 1 + κ⁻¹)
  have hw : 1 - mixAmplitude κ ^ 2 = (1 + κ⁻¹)⁻¹ * κ⁻¹ := by
    rw [hs]; field_simp; ring
  change ((fractionalMix (n := W) (-mixAmplitude κ)) *
    Matrix.fromBlocks (U : Matrix W W ℂ) 0 0 (V : Matrix W W ℂ) *
    (fractionalMix (n := W) (-mixAmplitude κ))ᴴ) (Sum.inl i) (Sum.inl j) = _
  rw [show (fractionalMix (n := W) (-mixAmplitude κ))ᴴ = fractionalMix (-mixAmplitude κ) from fractionalMix_selfAdjoint _]
  unfold fractionalMix
  rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp only [neg_neg, Matrix.zero_mul, Matrix.mul_zero, Matrix.one_mul, Matrix.mul_one,
    zero_add, add_zero, Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← pow_two,
    hs, ht', neg_sq, hw, Matrix.fromBlocks_apply₁₁]
  simp only [Matrix.add_apply, Matrix.smul_apply, Complex.real_smul]
  push_cast
  rfl


abbrev BranchSpace (S D : Type*) := Label × ((S × D) ⊕ (S × D))
abbrev Signal (S : Type*) := Bool × Bool × Bool × S

def signalZero (s : S) : Signal S := (false,false,false,s)

/-- Register rearrangement only: SELECT bit, edge-dilation bit, oracle-dilation
bit, and the original signal register. The graph is two actual qubits. -/
def physicalWiring (S D : Type*) :
    ((Label × ((S × D) ⊕ (S × D))) ⊕ (Label × ((S × D) ⊕ (S × D)))) ≃ Signal S × (Fin 4 × D) where
  toFun x := match x with
    | .inl ((z,g), .inl (s,d)) => ((false,z,false,s),(g,d))
    | .inl ((z,g), .inr (s,d)) => ((false,z,true,s),(g,d))
    | .inr ((z,g), .inl (s,d)) => ((true,z,false,s),(g,d))
    | .inr ((z,g), .inr (s,d)) => ((true,z,true,s),(g,d))
  invFun x := match x with
    | ((false,z,false,s),(g,d)) => .inl ((z,g),.inl (s,d))
    | ((false,z,true,s),(g,d)) => .inl ((z,g),.inr (s,d))
    | ((true,z,false,s),(g,d)) => .inr ((z,g),.inl (s,d))
    | ((true,z,true,s),(g,d)) => .inr ((z,g),.inr (s,d))
  left_inv x := by
    rcases x with ⟨⟨z,g⟩,x⟩ | ⟨⟨z,g⟩,x⟩ <;> cases x <;> rfl
  right_inv x := by
    rcases x with ⟨⟨b,z,h,s⟩,g,d⟩
    cases b <;> cases h <;> rfl

/-- The output oracle is a literal globally Hermitian unitary. -/
def graphEncoding (κ : ℝ) (hκ : 0 < κ) (U : Matrix.unitaryGroup (S × D) ℂ) :
    Matrix.unitaryGroup (Signal S × (Fin 4 × D)) ℂ :=
  @rewireUnitary _ _ inferInstance inferInstance inferInstance inferInstance (physicalWiring S D) (weightedSelect κ hκ (branchA U) (branchI S D))

theorem graphEncoding_hermitian (κ : ℝ) (hκ : 0 < κ)
    (U : Matrix.unitaryGroup (S × D) ℂ) : (graphEncoding κ hκ U).val.IsHermitian := by
  change (weightedSelect κ hκ (branchA U) (branchI S D)).val.submatrix
    (physicalWiring S D).symm (physicalWiring S D).symm |>.IsHermitian
  exact (weightedSelect_hermitian κ hκ _ _ (branchA_hermitian U) branchI_hermitian).submatrix _

theorem graphEncoding_signal_entries (κ : ℝ) (hκ : 0 < κ) (s : S)
    (U : Matrix.unitaryGroup (S × D) ℂ) (A : Matrix D D ℂ)
    (hA : A.IsHermitian) (henc : IsBlockEncoding s 1 0 U A)
    (g h : Fin 4) (i j : D) :
    signalBlock (signalZero s) (graphEncoding κ hκ U).val (g,i) (h,j) =
      ((1+κ⁻¹)⁻¹ : ℂ) * graphMatrix A κ (g,i) (h,j) := by
  rw [signalBlock_entries]
  change (weightedSelect κ hκ (branchA U) (branchI S D)).val
    (.inl ((false,g),.inl (s,i))) (.inl ((false,h),.inl (s,j))) = _
  rw [weightedSelect_left_entries]
  change ((1+κ⁻¹)⁻¹ : ℂ) *
      ((labelUnitary 1 (by decide)).val (false,g) (false,h) *
        (hermitianSignal U).val (.inl (s,i)) (.inl (s,j))) +
    ((1+κ⁻¹)⁻¹ * κ⁻¹ : ℂ) *
      (-((labelUnitary 2 (by decide)).val (false,g) (false,h)) *
        (1 : Matrix ((S × D) ⊕ (S × D)) ((S × D) ⊕ (S × D)) ℂ)
          (.inl (s,i)) (.inl (s,j))) = _
  rw [labelUnitary_zero_block, labelUnitary_zero_block, hermitianSignal_block s U A hA henc]
  fin_cases g <;> fin_cases h <;> simp [graphMatrix, Matrix.one_apply] <;> ring

theorem graphEncoding_exact [Nonempty D] (κ : ℝ) (hκ : 0 < κ) (s : S)
    (U : Matrix.unitaryGroup (S × D) ℂ) (A : Matrix D D ℂ)
    (hA : A.IsHermitian) (henc : IsBlockEncoding s 1 0 U A) :
    IsBlockEncoding (signalZero s) (1+κ⁻¹) 0 (graphEncoding κ hκ U) (graphMatrix A κ) := by
  have hp : 0 < 1+κ⁻¹ := by positivity
  refine ⟨hp, le_rfl, ?_⟩
  have he : graphMatrix A κ = (1+κ⁻¹) • signalBlock (signalZero s) (graphEncoding κ hκ U).val := by
    ext ⟨g,i⟩ ⟨h,j⟩
    rw [Matrix.smul_apply, graphEncoding_signal_entries κ hκ s U A hA henc]
    rw [Complex.real_smul]
    have hn : (1 + (κ⁻¹ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hp
    push_cast at hn ⊢
    field_simp [hn]
  rw [he]
  simp

theorem signal_cardinality : Fintype.card (Signal S) = 8 * Fintype.card S := by
  simp [Signal, Fintype.card_prod]
  omega

/-- If the input signal has a qubit count a, this construction adds exactly three. -/
theorem signal_qubits (a : ℕ) (hS : Fintype.card S = 2^a) :
    Fintype.card (Signal S) = 2^(a+3) := by
  rw [signal_cardinality, hS, pow_add]
  norm_num
  omega

end OptimalQLS.GraphEncoding
