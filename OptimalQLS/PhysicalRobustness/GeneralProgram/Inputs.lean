import OptimalQLS.PhysicalRobustness.PhysicalProgram.Bounds
import OptimalQLS.PhysicalRobustness.Parity
import OptimalQLS.Reduction.AdaptedInputs

/-! Actual noisy non-Hermitian inputs, normalized through the literal head bit. -/
noncomputable section
set_option synthInstance.maxSize 16384
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
open scoped Classical Matrix.Norms.L2Operator
namespace OptimalQLS.PhysicalRobustness.GeneralProgram
open Matrix LowerBounds PhysicalPadding Reduction TransducerCompiler BinaryClock PolynomialTransform
variable {D : Type*} [Fintype D] [DecidableEq D] {a n : ℕ}

/-- The full supplied signal block, including all cross-support entries. -/
def noisyMatrix (UA : Matrix.unitaryGroup (Bits a × Bits n) ℂ) :
    Matrix (Bits (n+1)) (Bits (n+1)) ℂ :=
  (hermitianDilation (signalBlock (fun _ : Fin a=>false) UA)).submatrix
    (PhysicalAdapter.sumBits n) (PhysicalAdapter.sumBits n)

theorem noisyMatrix_hermitian (UA : Matrix.unitaryGroup (Bits a × Bits n) ℂ) :
    (noisyMatrix UA).IsHermitian :=
  (hermitianDilation_hermitian _).submatrix _

theorem noisyMatrix_encoding (UA : Matrix.unitaryGroup (Bits a × Bits n) ℂ) :
    IsBlockEncoding (fun _ : Fin a=>false) 1 0 (PhysicalAdapter.matrixOracle UA) (noisyMatrix UA) := by
  refine ⟨by norm_num,by norm_num,?_⟩
  have hw : PhysicalAdapter.matrixOracle UA=
      rewireUnitary (Equiv.prodCongr (Equiv.refl (Bits a)) (PhysicalAdapter.sumBits n).symm)
        (dilationEncoding UA) := rfl
  rw [hw,dataCoordinates_signalBlock,dilationEncoding_signalBlock,one_smul]
  simp [noisyMatrix]

theorem hermitianDilation_sub (A B : Matrix D D ℂ) :
    hermitianDilation (A-B)=hermitianDilation A-hermitianDilation B := by
  ext i j
  cases i <;> cases j <;> simp [hermitianDilation]

/-- Normalization retains the original absolute input precision δ/α. -/
theorem noisyMatrix_error (f : D ↪ Bits n) {α δ : ℝ}
    (A : Matrix D D ℂ) (UA : Matrix.unitaryGroup (Bits a × Bits n) ℂ)
    (henc : IsBlockEncoding (fun _ : Fin a=>false) α δ UA (zeroExtend f A)) :
    ‖noisyMatrix UA-zeroExtend (dilationActive f) (normalizedMatrix α A)‖≤δ/α := by
  rw [dilationActive_matrix]
  have he : noisyMatrix UA-(normalizedMatrix α (zeroExtend f A)).submatrix
      (PhysicalAdapter.sumBits n) (PhysicalAdapter.sumBits n)=
      (hermitianDilation (signalBlock (fun _ : Fin a=>false) UA-α⁻¹ • zeroExtend f A)).submatrix
        (PhysicalAdapter.sumBits n) (PhysicalAdapter.sumBits n) := by
    rw [hermitianDilation_sub]
    rfl
  rw [he]
  apply (matrix_norm_submatrix_equiv_le _ (PhysicalAdapter.sumBits n)).trans
  rw [hermitianDilation_norm]
  have hs : signalBlock (fun _ : Fin a=>false) UA-α⁻¹ • zeroExtend f A=
      α⁻¹ • (α • signalBlock (fun _ : Fin a=>false) UA-zeroExtend f A) := by
    rw [smul_sub,smul_smul,inv_mul_cancel₀ henc.1.ne',one_smul]
  rw [hs,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr henc.1)]
  calc
    _≤α⁻¹*δ := mul_le_mul_of_nonneg_left (by simpa only [norm_sub_rev] using henc.2.2)
      (inv_nonneg.mpr henc.1.le)
    _=δ/α := by ring

theorem normalized_norm_of_bound {α : ℝ} (hα : 0<α)
    (A : Matrix D D ℂ) (hn : ‖A‖≤α) : ‖normalizedMatrix α A‖≤1 := by
  rw [normalizedMatrix_norm hα]
  calc
    _≤α⁻¹*α := mul_le_mul_of_nonneg_left hn (inv_nonneg.mpr hα.le)
    _=1 := inv_mul_cancel₀ hα.ne'

/-- Every promise needed by the noisy Hermitian program follows from the
original input. The supplied unitary columns other than zero remain arbitrary. -/
theorem normalize_input (f : D ↪ Bits n) {α κ δ ŝ : ℝ}
    (A : Matrix D D ℂ) (hu : IsUnit A) (hn : ‖A‖≤α)
    (UA : Matrix.unitaryGroup (Bits a × Bits n) ℂ)
    (henc : IsBlockEncoding (fun _ : Fin a=>false) α δ UA (zeroExtend f A))
    (Ub : Matrix.unitaryGroup (Bits n) ℂ) (b : EuclideanSpace ℂ D) (hb : ‖b‖=1)
    (hcol : ∀ i,Ub i (fun _ : Fin n=>false)=coordinateIsometry f b i)
    (hi : α*‖Ring.inverse A‖≤κ) (hs : κ*δ/α≤1/4)
    (hlo : solutionScale α A b/2≤ŝ) (hhi : ŝ≤2*solutionScale α A b) :
    (normalizedMatrix α A).IsHermitian ∧ IsUnit (normalizedMatrix α A) ∧
    ‖normalizedMatrix α A‖≤1 ∧ ‖Ring.inverse (normalizedMatrix α A)‖≤κ ∧
    0≤δ/α ∧ ‖noisyMatrix UA-zeroExtend (dilationActive f) (normalizedMatrix α A)‖≤δ/α ∧
    κ*(δ/α)≤1/4 ∧ ‖WithLp.toLp 2 (source (WithLp.ofLp b))‖=1 ∧
    (∀ i,PhysicalAdapter.vectorOracle Ub i (fun _ : Fin (n+1)=>false)=
      coordinateIsometry (dilationActive f) (WithLp.toLp 2 (source (WithLp.ofLp b))) i) ∧
    solutionScale 1 (normalizedMatrix α A) (WithLp.toLp 2 (source (WithLp.ofLp b)))/2≤ŝ ∧
    ŝ≤2*solutionScale 1 (normalizedMatrix α A) (WithLp.toLp 2 (source (WithLp.ofLp b))) := by
  refine ⟨normalizedMatrix_hermitian α A,normalizedMatrix_isUnit henc.1 A hu,
    normalized_norm_of_bound henc.1 A hn,normalized_inverse_bound henc.1 A hu hi,
    div_nonneg henc.2.1 henc.1.le,noisyMatrix_error f A UA henc,?_,?_,
    vectorOracle_prepares f Ub b hcol,?_,?_⟩
  · simpa only [mul_div_assoc] using hs
  · rwa [source_norm]
  · rwa [normalized_scale henc.1 A hu b]
  · rwa [normalized_scale henc.1 A hu b]

end OptimalQLS.PhysicalRobustness.GeneralProgram
