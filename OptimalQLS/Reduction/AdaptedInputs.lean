import OptimalQLS.Reduction.OutputCoordinates
import OptimalQLS.Reduction.PhysicalAdapter.Complete

/-! # Actual supplied original inputs in the physical Hermitian-reduced program -/
noncomputable section
namespace OptimalQLS.Reduction
open Matrix PhysicalPadding TransducerCompiler BinaryClock PolynomialTransform
open scoped Matrix.Norms.L2Operator
set_option synthInstance.maxSize 16384
set_option maxHeartbeats 500000
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
variable {D P Q S : Type*} [Fintype D] [DecidableEq D] [Fintype P] [DecidableEq P]
  [Fintype Q] [DecidableEq Q] [Fintype S] [DecidableEq S]

theorem dataCoordinates_signalBlock (e : P ≃ Q) (s₀ : S)
    (U : Matrix.unitaryGroup (S × P) ℂ) :
    signalBlock s₀ (rewireUnitary (Equiv.prodCongr (Equiv.refl S) e) U).val=
      (signalBlock s₀ U.val).submatrix e.symm e.symm := by
  ext i j
  simp [signalBlock_entries,rewireUnitary]

theorem matrixOracle_encoding {a n : ℕ} (f : D ↪ Bits n) {α : ℝ}
    (A : Matrix D D ℂ) (UA : Matrix.unitaryGroup (Bits a × Bits n) ℂ)
    (henc : IsBlockEncoding (fun _ : Fin a=>false) α 0 UA (zeroExtend f A)) :
    IsBlockEncoding (fun _ : Fin a=>false) 1 0 (PhysicalAdapter.matrixOracle UA)
      (zeroExtend (dilationActive f) (normalizedMatrix α A)) := by
  have hd := normalized_encoding (fun _ : Fin a=>false) (zeroExtend f A) UA henc
  have he := exact_block_eq hd
  rw [one_smul] at he
  refine ⟨by norm_num,by norm_num,?_⟩
  change ‖zeroExtend (dilationActive f) (normalizedMatrix α A)-
    (1 : ℝ) • signalBlock (fun _ : Fin a=>false) (PhysicalAdapter.matrixOracle UA).val‖≤0
  rw [one_smul,dilationActive_matrix]
  have hw : PhysicalAdapter.matrixOracle UA=
      rewireUnitary (Equiv.prodCongr (Equiv.refl (Bits a)) (PhysicalAdapter.sumBits n).symm)
        (LowerBounds.dilationEncoding UA) := rfl
  rw [hw,dataCoordinates_signalBlock,←he]
  simp

theorem vectorOracle_prepares {n : ℕ} (f : D ↪ Bits n)
    (Ub : Matrix.unitaryGroup (Bits n) ℂ) (b : EuclideanSpace ℂ D)
    (hcol : ∀ i,Ub i (fun _ : Fin n=>false)=coordinateIsometry f b i) (i : Bits (n+1)) :
    PhysicalAdapter.vectorOracle Ub i (fun _ : Fin (n+1)=>false)=
      coordinateIsometry (dilationActive f) (WithLp.toLp 2 (source (WithLp.ofLp b))) i := by
  have hp := preparation_prepares Ub (fun _ : Fin n=>false)
    (WithLp.ofLp (coordinateIsometry f b)) hcol (PhysicalAdapter.sumBits n i)
  change preparation Ub (PhysicalAdapter.sumBits n i)
      (PhysicalAdapter.sumBits n (fun _=>false))=_
  rw [PhysicalAdapter.sumBits_zero,hp,dilationActive,coordinateIsometry_postEquiv,physical_source]
  rfl

theorem normalized_scale {α : ℝ} (hα : 0<α) (A : Matrix D D ℂ) (hA : IsUnit A)
    (b : EuclideanSpace ℂ D) :
    solutionScale 1 (normalizedMatrix α A) (WithLp.toLp 2 (source (WithLp.ofLp b)))=
      solutionScale α A b := by
  simp only [solutionScale,one_mul,←Matrix.nonsing_inv_eq_ringInverse]
  exact normalized_solution_scale hα A hA (WithLp.ofLp b)

theorem normalized_inverse_bound {α κ : ℝ} (hα : 0<α) (A : Matrix D D ℂ) (hA : IsUnit A)
    (hi : α*‖Ring.inverse A‖≤κ) : ‖Ring.inverse (normalizedMatrix α A)‖≤κ := by
  rw [←Matrix.nonsing_inv_eq_ringInverse,normalizedMatrix_inverse_norm hα A hA]
  simpa only [Matrix.nonsing_inv_eq_ringInverse] using hi

/-- Logical scale bounds use the true original inverse, even when its physical
zero extension is singular. No whole-oracle restriction is imposed. -/
theorem scale_bounds_of_norm {α κ : ℝ} (hα : 0<α)
    (A : Matrix D D ℂ) (hA : IsUnit A) (hAnorm : ‖A‖≤α)
    (hi : α*‖Ring.inverse A‖≤κ) (b : EuclideanSpace ℂ D) (hb : ‖b‖=1) :
    1≤solutionScale α A b ∧ solutionScale α A b≤κ := by
  let φ := Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ)
  have hφA : IsUnit (φ A) := hA.map φ.toMonoidHom
  have heq : φ A (φ (Ring.inverse A) b)=b := by
    rw [Perturbation.toEuclideanCLM_inverse A hA]
    exact Perturbation.apply_inverse (φ A) hφA b
  constructor
  · calc
      1=‖φ A (φ (Ring.inverse A) b)‖ := by rw [heq,hb]
      _≤‖φ A‖*‖φ (Ring.inverse A) b‖ := (φ A).le_opNorm _
      _≤α*‖φ (Ring.inverse A) b‖ := mul_le_mul_of_nonneg_right hAnorm (norm_nonneg _)
  · have hn := (φ (Ring.inverse A)).le_opNorm b
    rw [hb,mul_one] at hn
    exact (mul_le_mul_of_nonneg_left hn hα.le).trans hi

theorem active_input_normalization [Nonempty D] {a n : ℕ} (f : D ↪ Bits n) {α κ ŝ : ℝ}
    (A : Matrix D D ℂ) (hA : IsUnit A) (b : EuclideanSpace ℂ D) (hb : ‖b‖=1)
    (UA : Matrix.unitaryGroup (Bits a × Bits n) ℂ)
    (henc : IsBlockEncoding (fun _ : Fin a=>false) α 0 UA (zeroExtend f A))
    (Ub : Matrix.unitaryGroup (Bits n) ℂ)
    (hcol : ∀ i,Ub i (fun _ : Fin n=>false)=coordinateIsometry f b i)
    (hκ : 2≤κ) (hi : α*‖Ring.inverse A‖≤κ)
    (hlo : 3*solutionScale α A b/8≤ŝ) (hhi : ŝ≤5*solutionScale α A b/2) :
    (normalizedMatrix α A).IsHermitian ∧ IsUnit (normalizedMatrix α A) ∧
    ‖Ring.inverse (normalizedMatrix α A)‖≤κ ∧
    IsBlockEncoding (fun _ : Fin a=>false) 1 0 (PhysicalAdapter.matrixOracle UA)
      (zeroExtend (dilationActive f) (normalizedMatrix α A)) ∧
    ‖WithLp.toLp 2 (source (WithLp.ofLp b))‖=1 ∧
    (∀ i,PhysicalAdapter.vectorOracle Ub i (fun _ : Fin (n+1)=>false)=
      coordinateIsometry (dilationActive f) (WithLp.toLp 2 (source (WithLp.ofLp b))) i) ∧
    BudgetParameters κ (solutionScale α A b) ŝ ∧
    solutionScale α A b=solutionScale 1 (normalizedMatrix α A)
      (WithLp.toLp 2 (source (WithLp.ofLp b))) := by
  have hn : ‖A‖≤α := by rw [←zeroExtend_norm f A]; exact norm_le_of_exact_block henc
  have hs := scale_bounds_of_norm henc.1 A hA hn hi b hb
  refine ⟨normalizedMatrix_hermitian α A,normalizedMatrix_isUnit henc.1 A hA,
    normalized_inverse_bound henc.1 A hA hi,matrixOracle_encoding f A UA henc,?_,
    vectorOracle_prepares f Ub b hcol,⟨hκ,hs.1,hs.2,hlo,hhi⟩,(normalized_scale henc.1 A hA b).symm⟩
  rwa [source_norm]

end OptimalQLS.Reduction
