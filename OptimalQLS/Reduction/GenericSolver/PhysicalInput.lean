import OptimalQLS.Reduction.Physical
import OptimalQLS.Reduction.GenericSolver.FreshCopiesHeadFinite

/-! Arbitrary full input-oracle promises and the logical inverse target in
physical data coordinates. All inverses act on the logical active space. -/
noncomputable section
open scoped Classical Matrix.Norms.L2Operator
namespace OptimalQLS.Reduction.GenericSolver.Physical
open Matrix LowerBounds PhysicalPadding TransducerCompiler BinaryClock PolynomialTransform
open FreshCopies
set_option synthInstance.maxSize 32768
set_option maxHeartbeats 800000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false

variable {D : Type} [Fintype D] [DecidableEq D] {a n : ℕ}

def solutionTarget (f : D ↪ Bits n) (A : Matrix D D ℂ) (b : EuclideanSpace ℂ D) :
    EuclideanSpace ℂ (Bits n) :=
  coordinateIsometry f (NormedSpace.normalize (WithLp.toLp 2 (A⁻¹ *ᵥ WithLp.ofLp b)))

def dilationTarget (f : D ↪ Bits n) (α : ℝ) (A : Matrix D D ℂ) (b : EuclideanSpace ℂ D) :
    EuclideanSpace ℂ (Bits n ⊕ Bits n) :=
  coordinateIsometry (sumIndex f)
    (NormedSpace.normalize (WithLp.toLp 2 ((normalizedMatrix α A)⁻¹ *ᵥ source (WithLp.ofLp b))))

theorem dilationTarget_eq_right (f : D ↪ Bits n) {α : ℝ} (hα : 0<α)
    (A : Matrix D D ℂ) (hA : IsUnit A) (b : EuclideanSpace ℂ D) :
    dilationTarget f α A b=WithLp.toLp 2 (rightState (WithLp.ofLp (solutionTarget f A b))) := by
  unfold dilationTarget
  rw [normalized_solution_direction hα A hA]
  exact sumIndex_source_right f _

theorem activeInverse_solutionTarget (f : D ↪ Bits n) {α : ℝ} (hα : 0<α)
    (A : Matrix D D ℂ) (hA : IsUnit A) (b : EuclideanSpace ℂ D) :
    NormedSpace.normalize
      (Matrix.toEuclideanCLM (n := Bits n ⊕ Bits n) (𝕜 := ℂ)
        (activeInverse (sumIndex f) (normalizedMatrix α A))
        (coordinateIsometry (sumIndex f) (WithLp.toLp 2 (source (WithLp.ofLp b)))))=
      WithLp.toLp 2 (rightState (WithLp.ofLp (solutionTarget f A b))) := by
  rw [activeInverse_apply,isometry_normalize,←Matrix.nonsing_inv_eq_ringInverse]
  exact dilationTarget_eq_right f hα A hA b

theorem solutionTarget_unit (f : D ↪ Bits n) (A : Matrix D D ℂ) (hA : IsUnit A)
    (b : EuclideanSpace ℂ D) (hb : ‖b‖=1) : ‖solutionTarget f A b‖=1 := by
  rw [solutionTarget,(coordinateIsometry f).norm_map]
  exact normalized_original_solution_unit A hA (WithLp.ofLp b) hb

theorem dilationTarget_unit (f : D ↪ Bits n) {α : ℝ} (hα : 0<α)
    (A : Matrix D D ℂ) (hA : IsUnit A) (b : EuclideanSpace ℂ D) (hb : ‖b‖=1) :
    ‖dilationTarget f α A b‖=1 := by
  rw [dilationTarget_eq_right f hα A hA,rightState,sumElim_norm_right]
  exact solutionTarget_unit f A hA b hb

theorem input_encoding (f : D ↪ Bits n) {α : ℝ} (A : Matrix D D ℂ)
    (UA : Matrix.unitaryGroup (Bits a × Bits n) ℂ)
    (henc : IsBlockEncoding (fun _ : Fin a=>false) α 0 UA (zeroExtend f A)) :
    IsBlockEncoding (fun _ : Fin a=>false) 1 0 (dilationEncoding UA)
      (zeroExtend (sumIndex f) (normalizedMatrix α A)) := by
  rw [physical_normalization_commutes]
  exact normalized_encoding (fun _ : Fin a=>false) (zeroExtend f A) UA henc

theorem input_preparation (f : D ↪ Bits n) (b : EuclideanSpace ℂ D)
    (Ub : Matrix.unitaryGroup (Bits n) ℂ)
    (hcol : ∀ i,Ub i (fun _ : Fin n=>false)=coordinateIsometry f b i) :
    ∀ i,preparation Ub i (.inl (fun _ : Fin n=>false))=
      coordinateIsometry (sumIndex f) (WithLp.toLp 2 (source (WithLp.ofLp b))) i := by
  intro i
  rw [physical_source]
  exact preparation_prepares Ub (fun _ : Fin n=>false) (WithLp.ofLp (coordinateIsometry f b)) hcol i

/-- The full supplied unitaries are retained. Only their exact signal block and
one preparation column are premises. The target uses the original logical inverse. -/
theorem input_promises (f : D ↪ Bits n) {α : ℝ}
    (A : Matrix D D ℂ) (hA : IsUnit A) (b : EuclideanSpace ℂ D) (hb : ‖b‖=1)
    (UA : Matrix.unitaryGroup (Bits a × Bits n) ℂ)
    (henc : IsBlockEncoding (fun _ : Fin a=>false) α 0 UA (zeroExtend f A))
    (Ub : Matrix.unitaryGroup (Bits n) ℂ)
    (hcol : ∀ i,Ub i (fun _ : Fin n=>false)=coordinateIsometry f b i) :
    (normalizedMatrix α A).IsHermitian ∧ IsUnit (normalizedMatrix α A) ∧
    IsBlockEncoding (fun _ : Fin a=>false) 1 0 (dilationEncoding UA)
      (zeroExtend (sumIndex f) (normalizedMatrix α A)) ∧
    (∀ i,preparation Ub i (.inl (fun _ : Fin n=>false))=
      coordinateIsometry (sumIndex f) (WithLp.toLp 2 (source (WithLp.ofLp b))) i) ∧
    ‖coordinateIsometry (sumIndex f) (WithLp.toLp 2 (source (WithLp.ofLp b)))‖=1 ∧
    ‖solutionTarget f A b‖=1 ∧
    dilationTarget f α A b=WithLp.toLp 2 (rightState (WithLp.ofLp (solutionTarget f A b))) := by
  refine ⟨normalizedMatrix_hermitian α A,normalizedMatrix_isUnit henc.1 A hA,
    input_encoding f A UA henc,input_preparation f b Ub hcol,?_,
    solutionTarget_unit f A hA b hb,dilationTarget_eq_right f henc.1 A hA b⟩
  rw [(coordinateIsometry (sumIndex f)).norm_map,source_norm]
  exact hb

def finiteSolutionTarget (f : D ↪ Bits n) (A : Matrix D D ℂ) (b : EuclideanSpace ℂ D) :
    EuclideanSpace ℂ (Fin (dataRegister n).dimension) :=
  WithLp.toLp 2 (indexedVector (dataRegister n) (WithLp.ofLp (solutionTarget f A b)))

theorem finiteSolutionTarget_unit (f : D ↪ Bits n) (A : Matrix D D ℂ) (hA : IsUnit A)
    (b : EuclideanSpace ℂ D) (hb : ‖b‖=1) : ‖finiteSolutionTarget f A b‖=1 := by
  have hh:=indexedVector_bornMass (dataRegister n) (WithLp.ofLp (solutionTarget f A b))
  rw [bornMass_eq_norm_sq,bornMass_eq_norm_sq] at hh
  change ‖finiteSolutionTarget f A b‖^2=‖solutionTarget f A b‖^2 at hh
  rw [solutionTarget_unit f A hA b hb] at hh
  nlinarith [norm_nonneg (finiteSolutionTarget f A b)]

theorem finite_dilation_right (f : D ↪ Bits n) {α : ℝ} (hα : 0<α)
    (A : Matrix D D ℂ) (hA : IsUnit A) (b : EuclideanSpace ℂ D) :
    (fun i=>indexedVector (doubledRegister n) (WithLp.ofLp (dilationTarget f α A b))
      (extractRightEmbedding (doubledIndex n) i))=WithLp.ofLp (finiteSolutionTarget f A b) := by
  rw [indexedRight,dilationTarget_eq_right f hα A hA]
  rfl


theorem indexed_dilationTarget (f : D ↪ Bits n) {α : ℝ} (hα : 0<α)
    (A : Matrix D D ℂ) (hA : IsUnit A) (b : EuclideanSpace ℂ D) :
    indexedVector (doubledRegister n) (WithLp.ofLp (dilationTarget f α A b))=
      fun i=>rightState (WithLp.ofLp (finiteSolutionTarget f A b)) ((doubledIndex n).symm i) := by
  rw [dilationTarget_eq_right f hα A hA]
  ext i
  obtain ⟨j,rfl⟩:=(doubledIndex n).surjective i
  rw [(doubledIndex n).symm_apply_apply]
  cases j with
  | inl j =>
    change rightState (WithLp.ofLp (solutionTarget f A b))
      ((doubledRegister n).index.symm ((doubledRegister n).index (.inl ((dataRegister n).index.symm j))))=0
    rw [(doubledRegister n).index.symm_apply_apply]
    rfl
  | inr j =>
    change rightState (WithLp.ofLp (solutionTarget f A b))
      ((doubledRegister n).index.symm ((doubledRegister n).index (.inr ((dataRegister n).index.symm j))))=
      solutionTarget f A b ((dataRegister n).index.symm j)
    rw [(doubledRegister n).index.symm_apply_apply]
    rfl


/-- The logical norm estimate follows from the actual padded signal block;
no assumption is imposed on any other column of the full matrix oracle. -/
theorem input_bounds (f : D ↪ Bits n) {α κ : ℝ}
    (A : Matrix D D ℂ) (hA : IsUnit A)
    (UA : Matrix.unitaryGroup (Bits a × Bits n) ℂ)
    (henc : IsBlockEncoding (fun _ : Fin a=>false) α 0 UA (zeroExtend f A))
    (hinv : α*‖A⁻¹‖≤κ) :
    ‖normalizedMatrix α A‖≤1 ∧ ‖(normalizedMatrix α A)⁻¹‖≤κ := by
  have hnorm : ‖A‖≤α := by
    cases isEmpty_or_nonempty D with
    | inl he =>
      letI := he
      have hzero : A=0 := Subsingleton.elim _ _
      simpa only [hzero,norm_zero] using henc.1.le
    | inr hn =>
      letI := hn
      rw [←zeroExtend_norm f A]
      exact norm_le_of_exact_block henc
  constructor
  · rw [normalizedMatrix_norm henc.1]
    calc α⁻¹*‖A‖≤α⁻¹*α := mul_le_mul_of_nonneg_left hnorm (inv_nonneg.mpr henc.1.le)
         _=1 := inv_mul_cancel₀ henc.1.ne'
  · rwa [normalizedMatrix_inverse_norm henc.1 A hA]

theorem input_solution_scale (f : D ↪ Bits n) {α : ℝ} (hα : 0<α)
    (A : Matrix D D ℂ) (hA : IsUnit A) (b : EuclideanSpace ℂ D) :
    ‖WithLp.toLp 2 ((normalizedMatrix α A)⁻¹ *ᵥ source (WithLp.ofLp b))‖=
      α*‖WithLp.toLp 2 (A⁻¹ *ᵥ WithLp.ofLp b)‖ ∧
    ‖Matrix.toEuclideanCLM (n := Bits n ⊕ Bits n) (𝕜 := ℂ)
      (activeInverse (sumIndex f) (normalizedMatrix α A))
      (coordinateIsometry (sumIndex f) (WithLp.toLp 2 (source (WithLp.ofLp b))))‖=
      α*‖WithLp.toLp 2 (A⁻¹ *ᵥ WithLp.ofLp b)‖ :=
  ⟨normalized_solution_scale hα A hA (WithLp.ofLp b),
    activeInverse_dilation_scale f hα A hA (WithLp.ofLp b)⟩

/-- The given relaxed estimate is unchanged for both the logical normalized
problem and its actual padded active-space realization. -/
theorem input_relaxed_estimate (f : D ↪ Bits n) {α estimate : ℝ} (hα : 0<α)
    (A : Matrix D D ℂ) (hA : IsUnit A) (b : EuclideanSpace ℂ D)
    (hlo : 3*(α*‖WithLp.toLp 2 (A⁻¹ *ᵥ WithLp.ofLp b)‖)/8≤estimate)
    (hhi : estimate≤5*(α*‖WithLp.toLp 2 (A⁻¹ *ᵥ WithLp.ofLp b)‖)/2) :
    (3*‖WithLp.toLp 2 ((normalizedMatrix α A)⁻¹ *ᵥ source (WithLp.ofLp b))‖/8≤estimate ∧
      estimate≤5*‖WithLp.toLp 2 ((normalizedMatrix α A)⁻¹ *ᵥ source (WithLp.ofLp b))‖/2) ∧
    (3*‖Matrix.toEuclideanCLM (n := Bits n ⊕ Bits n) (𝕜 := ℂ)
      (activeInverse (sumIndex f) (normalizedMatrix α A))
      (coordinateIsometry (sumIndex f) (WithLp.toLp 2 (source (WithLp.ofLp b))))‖/8≤estimate ∧
      estimate≤5*‖Matrix.toEuclideanCLM (n := Bits n ⊕ Bits n) (𝕜 := ℂ)
      (activeInverse (sumIndex f) (normalizedMatrix α A))
      (coordinateIsometry (sumIndex f) (WithLp.toLp 2 (source (WithLp.ofLp b))))‖/2) := by
  rw [(input_solution_scale f hα A hA b).1,(input_solution_scale f hα A hA b).2]
  exact ⟨⟨hlo,hhi⟩,⟨hlo,hhi⟩⟩

end OptimalQLS.Reduction.GenericSolver.Physical
