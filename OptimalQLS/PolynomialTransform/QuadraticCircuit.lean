import OptimalQLS.BlockEncoding
import OptimalQLS.PolynomialTransform.PhaseCircuit

/-!
# An exact two-query quadratic eigenvalue transformation

The compression 2 Aᴴ A - I is derived from the actual oracle and signal
reflection, and the implementing instruction list is explicit. For a
Hermitian block A this is precisely T₂(A). This is a proved special case,
complementing the general QSVT phase-factorization theorem proved separately.
-/
noncomputable section
namespace OptimalQLS.PolynomialTransform
open Matrix
open scoped Matrix.Norms.L2Operator

variable {W D B : Type*} [Fintype W] [DecidableEq W]
  [Fintype D] [DecidableEq D] [Fintype B] [DecidableEq B]

/-- The entire oracle space, with its sole multiplicity sector enabled. -/
def wholeOraclePort (W : Type*) : QueryPort W W where
  multiplicity := 1
  wiring :=
    { toFun := Prod.fst
      invFun := fun w => (w, 0)
      left_inv := by
        intro ⟨w,j⟩
        apply Prod.ext
        · rfl
        · exact Subsingleton.elim _ _
      right_inv := by intro w; rfl }
  control := fun _ => true

@[simp] theorem wholeOraclePort_apply (U : Matrix.unitaryGroup W ℂ) :
    (wholeOraclePort W).apply U = U := by
  apply Subtype.ext
  ext i j
  simp [wholeOraclePort, QueryPort.apply, rewireUnitary, controlledUnitary,
    Matrix.blockDiagonal]

/-- Reflection about the actual image of an isometric signal insertion. -/
def insertionReflection (E : Matrix W D ℂ) (hE : Eᴴ * E = 1) : Matrix.unitaryGroup W ℂ := by
  let P := E * Eᴴ
  have hP : P * P = P := by
    dsimp only [P]
    calc
      E * Eᴴ * (E * Eᴴ) = E * (Eᴴ * E) * Eᴴ := by simp only [Matrix.mul_assoc]
      _ = E * Eᴴ := by rw [hE, Matrix.mul_one]
  have hPs : Pᴴ = P := by simp [P]
  refine ⟨P + P - 1, ?_⟩
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
  have hr : (P + P - 1)ᴴ = P + P - 1 := by simp [hPs]
  rw [hr]
  calc
    (P + P - 1) * (P + P - 1) =
        P * P + P * P + P * P + P * P - (P + P + P + P) + 1 := by noncomm_ring
    _ = 1 := by rw [hP]; noncomm_ring

/-- Concrete circuit: apply U, reflect the signal sector, apply U-adjoint. -/
def quadraticCircuit (E : Matrix W D ℂ) (hE : Eᴴ * E = 1) : QueryCircuit W B W :=
  [.matrixCall (wholeOraclePort W) false,
    .work (insertionReflection E hE), .matrixCall (wholeOraclePort W) true]

omit [Fintype B] [DecidableEq B] in
theorem quadraticCircuit_counts (E : Matrix W D ℂ) (hE : Eᴴ * E = 1) :
    (quadraticCircuit (B := B) E hE).matrixQueries = 2 ∧
    (quadraticCircuit (B := B) E hE).vectorQueries = 0 ∧
    workInstructions (quadraticCircuit (B := B) E hE) = 1 := by
  simp [quadraticCircuit, QueryCircuit.matrixQueries, QueryCircuit.vectorQueries, workInstructions]

theorem quadraticCircuit_eval (E : Matrix W D ℂ) (hE : Eᴴ * E = 1)
    (U : Matrix.unitaryGroup W ℂ) (Ub : Matrix.unitaryGroup B ℂ) :
    (quadraticCircuit E hE).eval U Ub = U⁻¹ * insertionReflection E hE * U := by
  simp [quadraticCircuit, QueryCircuit.eval, QueryInstruction.eval]

/-- The compressed operator is calculated from concrete matrices. -/
theorem quadraticCircuit_compression (E : Matrix W D ℂ) (hE : Eᴴ * E = 1)
    (U : Matrix.unitaryGroup W ℂ) (Ub : Matrix.unitaryGroup B ℂ) :
    Eᴴ * ((quadraticCircuit E hE).eval U Ub : Matrix W W ℂ) * E =
      (Eᴴ * (U : Matrix W W ℂ) * E)ᴴ * (Eᴴ * (U : Matrix W W ℂ) * E) +
      (Eᴴ * (U : Matrix W W ℂ) * E)ᴴ * (Eᴴ * (U : Matrix W W ℂ) * E) - 1 := by
  rw [quadraticCircuit_eval]
  have hU : (U : Matrix W W ℂ)ᴴ * (U : Matrix W W ℂ) = 1 := U.property.1
  change Eᴴ * ((U : Matrix W W ℂ)ᴴ *
    (E * Eᴴ + E * Eᴴ - 1) * (U : Matrix W W ℂ)) * E = _
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  calc
    Eᴴ * ((U : Matrix W W ℂ)ᴴ * (E * Eᴴ + E * Eᴴ - 1) * (U : Matrix W W ℂ)) * E =
      (Eᴴ * (U : Matrix W W ℂ)ᴴ * E) * (Eᴴ * (U : Matrix W W ℂ) * E) +
      (Eᴴ * (U : Matrix W W ℂ)ᴴ * E) * (Eᴴ * (U : Matrix W W ℂ) * E) -
      Eᴴ * ((U : Matrix W W ℂ)ᴴ * (U : Matrix W W ℂ)) * E := by
        simp only [Matrix.mul_add, Matrix.mul_sub, Matrix.add_mul, Matrix.sub_mul,
          Matrix.mul_assoc, Matrix.mul_one]
    _ = _ := by rw [hU, Matrix.mul_one, hE]; simp only [Matrix.mul_assoc]

/-- An exact Hermitian block A is transformed into the actual matrix T₂(A). -/
theorem quadraticCircuit_hermitian_block (E : Matrix W D ℂ) (hE : Eᴴ * E = 1)
    (U : Matrix.unitaryGroup W ℂ) (Ub : Matrix.unitaryGroup B ℂ)
    (A : Matrix D D ℂ) (hA : Aᴴ = A) (hblock : Eᴴ * (U : Matrix W W ℂ) * E = A) :
    Eᴴ * ((quadraticCircuit E hE).eval U Ub : Matrix W W ℂ) * E = A * A + A * A - 1 := by
  rw [quadraticCircuit_compression, hblock, hA]

/-- The quadratic instance of Lemma 2.4, stated in the project's exact
block-encoding convention and with the standard zero-signal insertion. -/
theorem quadraticCircuit_exact_encoding {S : Type*} [Fintype S] [DecidableEq S]
    [Nonempty D] (s₀ : S) (U : Matrix.unitaryGroup (S × D) ℂ)
    (Ub : Matrix.unitaryGroup B ℂ) (A : Matrix D D ℂ) (hA : Aᴴ = A)
    (henc : IsBlockEncoding s₀ 1 0 U A) :
    IsBlockEncoding s₀ 1 0
      ((quadraticCircuit (signalInjection s₀) (signalInjection_isometry s₀)).eval U Ub)
      (A * A + A * A - 1) := by
  have hb : (signalInjection (D := D) s₀)ᴴ * (U : Matrix (S × D) (S × D) ℂ) *
      signalInjection s₀ = A := by
    have he := exact_block_eq henc
    simpa only [one_smul, signalBlock] using he.symm
  have hc := quadraticCircuit_hermitian_block (signalInjection s₀)
    (signalInjection_isometry s₀) U Ub A hA hb
  refine ⟨by norm_num, by norm_num, ?_⟩
  rw [one_smul]
  change ‖A * A + A * A - 1 -
    (signalInjection s₀)ᴴ * ((quadraticCircuit (signalInjection s₀)
      (signalInjection_isometry s₀)).eval U Ub : Matrix (S × D) (S × D) ℂ) *
      signalInjection s₀‖ ≤ 0
  rw [hc, sub_self, norm_zero]


end OptimalQLS.PolynomialTransform
