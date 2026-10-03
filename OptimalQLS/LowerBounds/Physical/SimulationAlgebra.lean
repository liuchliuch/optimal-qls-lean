import OptimalQLS.LowerBounds.Physical.CircuitBuilders

/-! Proved clean-subspace closure for the actual encoding operations. -/
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
namespace OptimalQLS.LowerBounds.Physical
open Matrix PolynomialTransform
variable {D E P Q D' P' S : Type*}
  [Fintype D] [DecidableEq D] [Fintype E] [DecidableEq E]
  [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]
  [Fintype D'] [DecidableEq D'] [Fintype P'] [DecidableEq P']
  [Fintype S] [DecidableEq S]

@[simp] theorem basisInsertion_sum (f : D → P) (g : E → Q) :
    basisInsertion (Sum.map f g) = Matrix.fromBlocks (basisInsertion f) 0 0 (basisInsertion g) := by
  ext i j
  cases i <;> cases j <;> simp [basisInsertion]

@[simp] theorem basisInsertion_rewire (f : D → P) (e : P ≃ P') (a : D ≃ D') :
    basisInsertion (fun x => e (f (a.symm x))) = (basisInsertion f).submatrix e.symm a.symm := by
  ext i j
  simp [basisInsertion, Equiv.symm_apply_eq]

theorem rewire_intertwines (f : D → P) (e : P ≃ P') (a : D ≃ D')
    (U : Matrix.unitaryGroup P ℂ) (V : Matrix.unitaryGroup D ℂ)
    (h : U.val * basisInsertion f = basisInsertion f * V.val) :
    (rewireUnitary e U).val * basisInsertion (fun x => e (f (a.symm x))) =
      basisInsertion (fun x => e (f (a.symm x))) * (rewireUnitary a V).val := by
  simp only [basisInsertion_rewire, rewireUnitary, Matrix.submatrix_mul_equiv]
  rw [h]

theorem adjoint_intertwines (f : D → P) (U : Matrix.unitaryGroup P ℂ)
    (V : Matrix.unitaryGroup D ℂ) (h : U.val * basisInsertion f = basisInsertion f * V.val) :
    U.valᴴ * basisInsertion f = basisInsertion f * V.valᴴ := by
  have hu : U.valᴴ * U.val = 1 := U.property.1
  have hv : V.val * V.valᴴ = 1 := V.property.2
  calc
    U.valᴴ * basisInsertion f = U.valᴴ * basisInsertion f * (V.val * V.valᴴ) := by rw [hv, Matrix.mul_one]
    _ = U.valᴴ * (basisInsertion f * V.val) * V.valᴴ := by simp only [Matrix.mul_assoc]
    _ = U.valᴴ * (U.val * basisInsertion f) * V.valᴴ := by rw [← h]
    _ = basisInsertion f * V.valᴴ := by rw [← Matrix.mul_assoc U.valᴴ U.val, hu, Matrix.one_mul]

theorem sum_intertwines (f : D → P) (g : E → Q)
    (U : Matrix.unitaryGroup P ℂ) (V : Matrix.unitaryGroup D ℂ)
    (R : Matrix.unitaryGroup Q ℂ) (T : Matrix.unitaryGroup E ℂ)
    (h : U.val * basisInsertion f = basisInsertion f * V.val)
    (k : R.val * basisInsertion g = basisInsertion g * T.val) :
    (blockSumUnitary U R).val * basisInsertion (Sum.map f g) =
      basisInsertion (Sum.map f g) * (blockSumUnitary V T).val := by
  simp only [basisInsertion_sum, blockSumUnitary, Matrix.fromBlocks_multiply,
    Matrix.mul_zero, Matrix.zero_mul, zero_add, add_zero]
  rw [h,k]

theorem sumEncoding_intertwines (f : D → P) (g : E → Q)
    (U : Matrix.unitaryGroup (S × P) ℂ) (V : Matrix.unitaryGroup (S × D) ℂ)
    (R : Matrix.unitaryGroup (S × Q) ℂ) (T : Matrix.unitaryGroup (S × E) ℂ)
    (h : U.val * basisInsertion (fun x : S × D => (x.1,f x.2)) =
      basisInsertion (fun x : S × D => (x.1,f x.2)) * V.val)
    (k : R.val * basisInsertion (fun x : S × E => (x.1,g x.2)) =
      basisInsertion (fun x : S × E => (x.1,g x.2)) * T.val) :
    (sumEncoding U R).val * basisInsertion (fun x : S × (D ⊕ E) => (x.1,Sum.map f g x.2)) =
      basisInsertion (fun x : S × (D ⊕ E) => (x.1,Sum.map f g x.2)) * (sumEncoding V T).val := by
  have hh := rewire_intertwines _ (distributeSignalSum S P Q) (distributeSignalSum S D E)
    _ _ (sum_intertwines _ _ U V R T h k)
  have hf : (fun x : S × (D ⊕ E) => distributeSignalSum S P Q
      (Sum.map (fun y : S × D => (y.1,f y.2)) (fun y : S × E => (y.1,g y.2))
        ((distributeSignalSum S D E).symm x))) =
      (fun x : S × (D ⊕ E) => (x.1,Sum.map f g x.2)) := by
    funext x
    rcases x with ⟨s,x⟩
    cases x <;> rfl
  rw [hf] at hh
  exact hh

theorem fractionalMix_intertwines (f : D → P) (r : ℝ) :
    fractionalMix (n := P) r * basisInsertion (Sum.map f f) =
      basisInsertion (Sum.map f f) * fractionalMix (n := D) r := by
  simp [basisInsertion_sum, fractionalMix, Matrix.fromBlocks_multiply,
    Matrix.smul_mul, Matrix.mul_smul]

theorem twoTermLCU_intertwines (f : D → P) (U : Matrix.unitaryGroup P ℂ)
    (V : Matrix.unitaryGroup D ℂ) (h : U.val * basisInsertion f = basisInsertion f * V.val)
    (r : ℝ) (hr : |r| < 1) :
    (twoTermLCU U r hr).val * basisInsertion (fun x : Bool × D => (x.1,f x.2)) =
      basisInsertion (fun x : Bool × D => (x.1,f x.2)) * (twoTermLCU V r hr).val := by
  have hp : (privateOracle (negativeUnitary U)).val * basisInsertion (Sum.map f f) =
      basisInsertion (Sum.map f f) * (privateOracle (negativeUnitary V)).val := by
    simp only [privateOracle, negativeUnitary, basisInsertion_sum, Matrix.fromBlocks_multiply,
      Matrix.mul_zero, Matrix.zero_mul, Matrix.one_mul, Matrix.mul_one, zero_add, add_zero,
      Matrix.neg_mul, Matrix.mul_neg]
    rw [h]
    simp
  have hfull : (fractionalMix (n := P) r * (privateOracle (negativeUnitary U)).val * fractionalMix r) *
      basisInsertion (Sum.map f f) = basisInsertion (Sum.map f f) *
        (fractionalMix (n := D) r * (privateOracle (negativeUnitary V)).val * fractionalMix r) := by
    have hx := intertwines_mul (basisInsertion (Sum.map f f))
      (fractionalMix (n := P) r) (privateOracle (negativeUnitary U)).val
      (fractionalMix (n := D) r) (privateOracle (negativeUnitary V)).val
      (fractionalMix_intertwines f r) hp
    have hy := intertwines_mul (basisInsertion (Sum.map f f)) _ (fractionalMix (n := P) r)
      _ (fractionalMix (n := D) r) hx (fractionalMix_intertwines f r)
    simpa only [Matrix.mul_assoc] using hy
  have hh := rewire_intertwines (Sum.map f f) (sumBoolEquiv P) (sumBoolEquiv D)
    (⟨fractionalMix (n := P) r, fractionalMix_unitary hr⟩ * privateOracle (negativeUnitary U) *
      ⟨fractionalMix (n := P) r, fractionalMix_unitary hr⟩)
    (⟨fractionalMix (n := D) r, fractionalMix_unitary hr⟩ * privateOracle (negativeUnitary V) *
      ⟨fractionalMix (n := D) r, fractionalMix_unitary hr⟩) (by
        simpa only [Submonoid.coe_mul] using hfull)
  have hf : (fun x : Bool × D => sumBoolEquiv P (Sum.map f f ((sumBoolEquiv D).symm x))) =
      (fun x : Bool × D => (x.1,f x.2)) := by
    funext x
    rcases x with ⟨s,x⟩
    cases s <;> rfl
  rw [hf] at hh
  exact hh

theorem dilationEncoding_intertwines (f : D → P)
    (U : Matrix.unitaryGroup (S × P) ℂ) (V : Matrix.unitaryGroup (S × D) ℂ)
    (h : U.val * basisInsertion (fun x : S × D => (x.1,f x.2)) =
      basisInsertion (fun x : S × D => (x.1,f x.2)) * V.val) :
    (dilationEncoding U).val * basisInsertion (fun x : S × (D ⊕ D) => (x.1,Sum.map f f x.2)) =
      basisInsertion (fun x : S × (D ⊕ D) => (x.1,Sum.map f f x.2)) * (dilationEncoding V).val := by
  let g := fun x : S × D => (x.1,f x.2)
  have hp : (hermitianUnitaryDilation U).val * basisInsertion (Sum.map g g) =
      basisInsertion (Sum.map g g) * (hermitianUnitaryDilation V).val := by
    simp only [hermitianUnitaryDilation, hermitianDilation, basisInsertion_sum,
      Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, zero_add, add_zero]
    rw [h, adjoint_intertwines g U V h]
  have hh := rewire_intertwines (Sum.map g g) (distributeSignal S P) (distributeSignal S D) _ _ hp
  have hf : (fun x : S × (D ⊕ D) => distributeSignal S P
      (Sum.map g g ((distributeSignal S D).symm x))) =
      (fun x : S × (D ⊕ D) => (x.1,Sum.map f f x.2)) := by
    funext x
    rcases x with ⟨s,x⟩
    cases x <;> rfl
  rw [hf] at hh
  exact hh

end OptimalQLS.LowerBounds.Physical
