import OptimalQLS.KernelReflectionEncoding
import OptimalQLS.TransducerCompiler.Basic

noncomputable section
namespace OptimalQLS
open Matrix
variable {n B : Type*} [Fintype n] [DecidableEq n] [Fintype B] [DecidableEq B]

/-- One oracle call controls the two private labels simultaneously. -/
def kernelQueryPort (n : Type*) : QueryPort n (Fin 3 × n) where
  multiplicity := 3
  wiring := Equiv.prodComm n (Fin 3)
  control := fun j => decide (j ≠ 0)

omit [Fintype B] [DecidableEq B] in
theorem kernelQueryPort_apply (V : Matrix.unitaryGroup n ℂ) (ξ y z : n → ℂ) :
    ((kernelQueryPort n).apply V : Matrix (Fin 3 × n) (Fin 3 × n) ℂ) *ᵥ
      kernelTriple ξ y z =
      kernelTriple ξ ((V : Matrix n n ℂ) *ᵥ y) ((V : Matrix n n ℂ) *ᵥ z) := by
  rw [QueryPort.apply, TransducerCompiler.rewire_apply]
  funext ji
  rcases ji with ⟨j,i⟩
  change ((controlledUnitary 3 _ V : Matrix (n × Fin 3) (n × Fin 3) ℂ) *ᵥ _)
    (i,j) = _
  rw [TransducerCompiler.controlled_apply]
  fin_cases j <;> simp [kernelQueryPort, kernelTriple, Function.comp_def]

/-- Work depends only on the known signal projector and classical parameter μ;
no matrix entries of the input oracle occur in this instruction list. -/
def kernelReflectionCircuit (Q : Matrix n n ℂ) (hQ : star Q = Q) (hQQ : Q * Q = Q)
    {μ : ℝ} (hμ : 0 < μ) : QueryCircuit n B (Fin 3 × n) :=
  [.matrixCall (kernelQueryPort n) false,
   .work (kernelWorkUnitary Q hQ hQQ (kernelMixA μ) (kernelMixB μ)
     (kernelMix_normalized hμ))]

omit [Fintype B] [DecidableEq B] in
theorem kernelReflectionCircuit_counts (Q : Matrix n n ℂ) (hQ : star Q = Q)
    (hQQ : Q * Q = Q) {μ : ℝ} (hμ : 0 < μ) :
    (kernelReflectionCircuit (B := B) Q hQ hQQ hμ).matrixQueries = 1 ∧
    (kernelReflectionCircuit (B := B) Q hQ hQQ hμ).vectorQueries = 0 := by
  simp [kernelReflectionCircuit, QueryCircuit.matrixQueries, QueryCircuit.vectorQueries]

/-- A concrete finite query circuit realizes the catalyst identity using
one controlled Hermitian matrix-oracle call and no vector-oracle call. -/
theorem kernelReflectionCircuit_restoration (Q : Matrix n n ℂ)
    (hQ : star Q = Q) (hQQ : Q * Q = Q) (V : Matrix.unitaryGroup n ℂ)
    (hV : (V : Matrix n n ℂ) * V = 1) (Ub : Matrix.unitaryGroup B ℂ)
    {μ α : ℝ} (hμ : 0 < μ) (hα : α ≠ 0) (ξ p z : n → ℂ)
    (hξ : Q *ᵥ ξ = ξ) (hp : Q *ᵥ p = p) (hz : Q *ᵥ z = z)
    (hVp : Q *ᵥ ((V : Matrix n n ℂ) *ᵥ p) = 0)
    (hVz : Q *ᵥ ((V : Matrix n n ℂ) *ᵥ z) = α⁻¹ • (ξ - p)) :
    ((kernelReflectionCircuit Q hQ hQQ hμ).eval V Ub :
      Matrix (Fin 3 × n) (Fin 3 × n) ℂ) *ᵥ
      kernelTriple ξ (kernelCatalystOne V μ α p z) (kernelCatalystTwo V μ α p z) =
      kernelTriple ((2 : ℝ) • p - ξ)
        (kernelCatalystOne V μ α p z) (kernelCatalystTwo V μ α p z) := by
  simp only [kernelReflectionCircuit, QueryCircuit.eval, QueryInstruction.eval,
    Bool.false_eq_true, ↓reduceIte, one_mul, Submonoid.coe_mul,
    ← Matrix.mulVec_mulVec, kernelQueryPort_apply]
  exact kernel_catalyst_restoration Q V hQ hQQ hV hμ hα ξ p z hξ hp hz hVp hVz

end OptimalQLS
