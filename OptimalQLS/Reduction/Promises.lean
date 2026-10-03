import OptimalQLS.Reduction.Normalized
import OptimalQLS.LowerBounds.QueryPortDistance

/-! The normalization theorem in the exact conventional Problem 2.2 records.
Only a basis equivalence sending computational zero to the source half is used. -/
noncomputable section
open scoped Matrix.Norms.L2Operator
namespace OptimalQLS.Reduction
open Matrix LowerBounds
variable {d m : ℕ} [NeZero d] [NeZero m]

def doubledCoordinates (d : ℕ) : Fin (d+d) ≃ Fin d ⊕ Fin d := finSumFinEquiv.symm

theorem doubledCoordinates_zero (d : ℕ) [NeZero d] :
    doubledCoordinates d 0 = .inl 0 := by
  exact finSumFinEquiv_symm_apply_castAdd (n := d) (0 : Fin d)

def normalizedParameters (p : QLSParameters) : QLSParameters :=
  { p with alpha := 1, epsilon := p.epsilon/2 }

def finiteMatrix (p : QLSParameters) (A : Matrix (Fin d) (Fin d) ℂ)
    (E : Fin m ≃ Fin d ⊕ Fin d) : Matrix (Fin m) (Fin m) ℂ :=
  (normalizedMatrix p.alpha A).submatrix E E

def finiteSource (b : DataSpace d) (E : Fin m ≃ Fin d ⊕ Fin d) : DataSpace m :=
  WithLp.toLp 2 (source (fun i => b i) ∘ E)

def finiteEncoding (p : QLSParameters)
    (UA : Matrix.unitaryGroup (SignalIndex p.signalQubits × Fin d) ℂ)
    (E : Fin m ≃ Fin d ⊕ Fin d) :
    Matrix.unitaryGroup (SignalIndex p.signalQubits × Fin m) ℂ :=
  rewireUnitary (Equiv.prodCongr (Equiv.refl _) E).symm (dilationEncoding UA)

def finitePreparation (Ub : Matrix.unitaryGroup (Fin d) ℂ)
    (E : Fin m ≃ Fin d ⊕ Fin d) : Matrix.unitaryGroup (Fin m) ℂ :=
  rewireUnitary E.symm (preparation Ub)

theorem finiteEncoding_exact {p : QLSParameters} {A : Matrix (Fin d) (Fin d) ℂ}
    {UA : Matrix.unitaryGroup (SignalIndex p.signalQubits × Fin d) ℂ}
    (henc : IsBlockEncoding 0 p.alpha 0 UA A) (E : Fin m ≃ Fin d ⊕ Fin d) :
    IsBlockEncoding 0 1 0 (finiteEncoding p UA E) (finiteMatrix p A E) := by
  have hh := exact_block_eq (normalized_encoding 0 A UA henc)
  simp only [one_smul] at hh
  have he : signalBlock (0 : SignalIndex p.signalQubits) (finiteEncoding p UA E) = finiteMatrix p A E := by
    ext i j
    rw [signalBlock_entries]
    change (dilationEncoding UA) (0,E i) (0,E j) = normalizedMatrix p.alpha A (E i) (E j)
    have hj := congrArg (fun M : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) ℂ => M (E i) (E j)) hh
    simpa only [signalBlock_entries] using hj.symm
  refine ⟨by norm_num, by norm_num, ?_⟩
  rw [one_smul, he]
  simp

theorem finite_solutionScale {p : QLSParameters} (hα : 0 < p.alpha)
    (A : Matrix (Fin d) (Fin d) ℂ) (hA : IsUnit A)
    (b : DataSpace d) (E : Fin m ≃ Fin d ⊕ Fin d) :
    solutionScale 1 (finiteMatrix p A E) (finiteSource b E) = solutionScale p.alpha A b := by
  rw [solutionScale, one_mul, ← Matrix.nonsing_inv_eq_ringInverse]
  change ‖WithLp.toLp 2 ((finiteMatrix p A E)⁻¹ *ᵥ (source (fun i => b i) ∘ E))‖ = _
  rw [finiteMatrix, Matrix.inv_submatrix_equiv, Matrix.submatrix_mulVec_equiv,
    euclidean_norm_comp_equiv]
  have he : (source (fun i => b i) ∘ E) ∘ E.symm = source (fun i => b i) := by
    funext i; simp
  rw [he, normalized_solution_scale hα A hA]
  rw [solutionScale, ← Matrix.nonsing_inv_eq_ringInverse]
  rfl

theorem basePromise_transport {p : QLSParameters} {A : Matrix (Fin d) (Fin d) ℂ}
    {b : DataSpace d} {UA : Matrix.unitaryGroup (SignalIndex p.signalQubits × Fin d) ℂ}
    {Ub : Matrix.unitaryGroup (Fin d) ℂ} (h : BaseQLSPromise p A b UA Ub)
    (E : Fin m ≃ Fin d ⊕ Fin d) (hE : E 0 = .inl 0) :
    BaseQLSPromise (normalizedParameters p) (finiteMatrix p A E) (finiteSource b E)
      (finiteEncoding p UA E) (finitePreparation Ub E) := by
  refine ⟨?_,?_,finiteEncoding_exact h.exactEncoding E,?_,h.kappaLower,?_,?_,?_⟩
  · rw [finiteMatrix, Matrix.isUnit_submatrix_equiv]
    exact normalizedMatrix_isUnit h.exactEncoding.1 A h.invertible
  · rw [finiteSource, euclidean_norm_comp_equiv, source_norm]
    exact h.unitVector
  · intro i
    change preparation Ub (E i) (E 0) = source (fun i => b i) (E i)
    rw [hE]
    exact preparation_prepares Ub 0 (fun i => b i) h.statePreparation (E i)
  · change 1 * ‖Ring.inverse (finiteMatrix p A E)‖ ≤ p.kappa
    rw [one_mul, ← Matrix.nonsing_inv_eq_ringInverse, finiteMatrix, Matrix.inv_submatrix_equiv]
    apply (matrix_norm_submatrix_equiv_le _ E).trans
    rw [normalizedMatrix_inverse_norm h.exactEncoding.1 A h.invertible,
      Matrix.nonsing_inv_eq_ringInverse]
    exact h.inverseBound
  · change 0 < p.epsilon/2
    linarith [h.epsilonPositive]
  · change p.epsilon/2 < 1/2
    linarith [h.epsilonUpper]

theorem relaxedPromise_transport {p : QLSParameters} {A : Matrix (Fin d) (Fin d) ℂ}
    {b : DataSpace d} {UA : Matrix.unitaryGroup (SignalIndex p.signalQubits × Fin d) ℂ}
    {Ub : Matrix.unitaryGroup (Fin d) ℂ} (h : RelaxedQLSPromise p A b UA Ub)
    (E : Fin m ≃ Fin d ⊕ Fin d) (hE : E 0 = .inl 0) :
    RelaxedQLSPromise (normalizedParameters p) (finiteMatrix p A E) (finiteSource b E)
      (finiteEncoding p UA E) (finitePreparation Ub E) := by
  refine ⟨basePromise_transport h.toBaseQLSPromise E hE, ?_, ?_⟩
  · change 3 * solutionScale 1 _ _ / 8 ≤ p.normEstimate
    rw [finite_solutionScale h.exactEncoding.1 A h.invertible b E]
    exact h.estimateLower
  · change p.normEstimate ≤ 5 * solutionScale 1 _ _ / 2
    rw [finite_solutionScale h.exactEncoding.1 A h.invertible b E]
    exact h.estimateUpper

theorem exactPromise_transport {p : QLSParameters} {A : Matrix (Fin d) (Fin d) ℂ}
    {b : DataSpace d} {UA : Matrix.unitaryGroup (SignalIndex p.signalQubits × Fin d) ℂ}
    {Ub : Matrix.unitaryGroup (Fin d) ℂ} (h : ExactQLSPromise p A b UA Ub)
    (E : Fin m ≃ Fin d ⊕ Fin d) (hE : E 0 = .inl 0) :
    ExactQLSPromise (normalizedParameters p) (finiteMatrix p A E) (finiteSource b E)
      (finiteEncoding p UA E) (finitePreparation Ub E) := by
  refine ⟨basePromise_transport h.toBaseQLSPromise E hE, ?_, ?_⟩
  · change solutionScale 1 _ _ / 2 ≤ p.normEstimate
    rw [finite_solutionScale h.exactEncoding.1 A h.invertible b E]
    exact h.estimateLower
  · change p.normEstimate ≤ 2 * solutionScale 1 _ _
    rw [finite_solutionScale h.exactEncoding.1 A h.invertible b E]
    exact h.estimateUpper

theorem doubled_relaxedPromise {p : QLSParameters} {A : Matrix (Fin d) (Fin d) ℂ}
    {b : DataSpace d} {UA : Matrix.unitaryGroup (SignalIndex p.signalQubits × Fin d) ℂ}
    {Ub : Matrix.unitaryGroup (Fin d) ℂ} (h : RelaxedQLSPromise p A b UA Ub) :
    RelaxedQLSPromise (normalizedParameters p) (finiteMatrix p A (doubledCoordinates d))
      (finiteSource b (doubledCoordinates d)) (finiteEncoding p UA (doubledCoordinates d))
      (finitePreparation Ub (doubledCoordinates d)) :=
  relaxedPromise_transport h (doubledCoordinates d) (doubledCoordinates_zero d)

theorem doubled_exactPromise {p : QLSParameters} {A : Matrix (Fin d) (Fin d) ℂ}
    {b : DataSpace d} {UA : Matrix.unitaryGroup (SignalIndex p.signalQubits × Fin d) ℂ}
    {Ub : Matrix.unitaryGroup (Fin d) ℂ} (h : ExactQLSPromise p A b UA Ub) :
    ExactQLSPromise (normalizedParameters p) (finiteMatrix p A (doubledCoordinates d))
      (finiteSource b (doubledCoordinates d)) (finiteEncoding p UA (doubledCoordinates d))
      (finitePreparation Ub (doubledCoordinates d)) :=
  exactPromise_transport h (doubledCoordinates d) (doubledCoordinates_zero d)

end OptimalQLS.Reduction
