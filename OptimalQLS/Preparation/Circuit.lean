import OptimalQLS.Preparation.LabelOperations

/-! # The actual two-oracle instruction list for the preparation transducer -/
noncomputable section
namespace OptimalQLS.Preparation
open Matrix
variable {F : Type*} [Fintype F] [DecidableEq F]

/-- The two UH private copies share one controlled call. -/
def historyPort (F : Type*) : QueryPort F (Fin 8 × F) where
  multiplicity := 8
  wiring := Equiv.prodComm F (Fin 8)
  control j := decide (j=2 ∨ j=3)

/-- The second intermediate oracle is Re, not the original vector oracle.
Its implementation uses the proved two-vector-query reflection circuit. -/
def reflectionPort (F : Type*) : QueryPort F (Fin 8 × F) where
  multiplicity := 8
  wiring := Equiv.prodComm F (Fin 8)
  control j := decide (j=4)

theorem historyPort_apply (V : Matrix.unitaryGroup F ℂ) (ξ q ω₁ ω₂ z : F → ℂ) :
    ((historyPort F).apply V : Matrix (Fin 8 × F) (Fin 8 × F) ℂ) *ᵥ
      bundle8 ξ q ω₁ ω₂ z =
      bundle8 ξ q ((V : Matrix F F ℂ)*ᵥω₁) ((V : Matrix F F ℂ)*ᵥω₂) z := by
  rw [QueryPort.apply,TransducerCompiler.rewire_apply]
  ext ⟨j,i⟩
  change ((controlledUnitary 8 _ V : Matrix (F × Fin 8) (F × Fin 8) ℂ)*ᵥ_) (i,j) = _
  rw [TransducerCompiler.controlled_apply]
  fin_cases j <;> simp [historyPort,bundle8,Function.comp_def]

theorem reflectionPort_apply (R : Matrix.unitaryGroup F ℂ) (ξ q ω₁ ω₂ z : F → ℂ) :
    ((reflectionPort F).apply R : Matrix (Fin 8 × F) (Fin 8 × F) ℂ) *ᵥ
      bundle8 ξ q ω₁ ω₂ z = bundle8 ξ q ω₁ ω₂ ((R : Matrix F F ℂ)*ᵥz) := by
  rw [QueryPort.apply,TransducerCompiler.rewire_apply]
  ext ⟨j,i⟩
  change ((controlledUnitary 8 _ R : Matrix (F × Fin 8) (F × Fin 8) ℂ)*ᵥ_) (i,j) = _
  rw [TransducerCompiler.controlled_apply]
  fin_cases j <;> simp [reflectionPort,bundle8,Function.comp_def]

/-- Every work coefficient depends only on Q and the classical parameters. -/
def preparationCircuit (Q : Matrix F F ℂ) (hQ : star Q=Q) (hQQ : Q*Q=Q)
    {μ r : ℝ} (hμ : 0<μ) (hr : |r|<1) : QueryCircuit F F (Fin 8 × F) :=
  [.matrixCall (historyPort F) false, .vectorCall (reflectionPort F) false,
    .work (preparationWork Q hQ hQQ hμ hr)]

theorem preparationCircuit_counts (Q : Matrix F F ℂ) (hQ : star Q=Q) (hQQ : Q*Q=Q)
    {μ r : ℝ} (hμ : 0<μ) (hr : |r|<1) :
    (preparationCircuit Q hQ hQQ hμ hr).matrixQueries=1 ∧
    (preparationCircuit Q hQ hQQ hμ hr).vectorQueries=1 := by
  simp [preparationCircuit,QueryCircuit.matrixQueries,QueryCircuit.vectorQueries]

/-- The explicit finite query list restores every catalyst component. -/
theorem preparationCircuit_restoration (Q : Matrix F F ℂ)
    (V R : Matrix.unitaryGroup F ℂ) (hQ : star Q=Q) (hQQ : Q*Q=Q)
    (hV : (V : Matrix F F ℂ)*(V : Matrix F F ℂ)=1)
    {μ α r : ℝ} (hμ : 0<μ) (hα : α≠0) (hr : |r|<1)
    (ξ ψ q p z : F → ℂ) (hq : Q*ᵥq=q) (hp : Q*ᵥp=p) (hz : Q*ᵥz=z)
    (hVp : Q*ᵥ((V : Matrix F F ℂ)*ᵥp)=0)
    (hVz : Q*ᵥ((V : Matrix F F ℂ)*ᵥz)=α⁻¹ • (q-p))
    (hfirst : (-r) • ξ + Real.sqrt (1-r^2) • (-((R : Matrix F F ℂ)*ᵥ((2:ℝ) • p-q))) = ψ)
    (hsecond : Real.sqrt (1-r^2) • ξ + r • (-((R : Matrix F F ℂ)*ᵥ((2:ℝ) • p-q))) = q) :
    ((preparationCircuit Q hQ hQQ hμ hr).eval V R : Matrix (Fin 8 × F) (Fin 8 × F) ℂ)*ᵥ
      bundle8 ξ q (kernelCatalystOne V μ α p z) (kernelCatalystTwo V μ α p z) ((2:ℝ) • p-q) =
      bundle8 ψ q (kernelCatalystOne V μ α p z) (kernelCatalystTwo V μ α p z) ((2:ℝ) • p-q) := by
  simp only [preparationCircuit,QueryCircuit.eval,QueryInstruction.eval,Bool.false_eq_true,
    ite_false,one_mul,Submonoid.coe_mul,← Matrix.mulVec_mulVec]
  rw [historyPort_apply,reflectionPort_apply]
  exact preparationWork_apply Q V R hQ hQQ hV hμ hα hr ξ ψ q p z hq hp hz hVp hVz hfirst hsecond

end OptimalQLS.Preparation
