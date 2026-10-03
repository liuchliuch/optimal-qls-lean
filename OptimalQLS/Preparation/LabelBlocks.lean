import OptimalQLS.KernelReflectionTheorem
import Mathlib.Logic.Equiv.Fin.Basic

noncomputable section
namespace OptimalQLS.Preparation
open Matrix
variable {F G : Type*} [Fintype F] [DecidableEq F] [Fintype G] [DecidableEq G]

def directSumUnitary (U : Matrix.unitaryGroup F ℂ) (V : Matrix.unitaryGroup G ℂ) :
    Matrix.unitaryGroup (F ⊕ G) ℂ :=
  ⟨Matrix.fromBlocks U 0 0 V, by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
      Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply]
    have hu : (U : Matrix F F ℂ) * (U : Matrix F F ℂ)ᴴ = 1 := U.property.2
    have hv : (V : Matrix G G ℂ) * (V : Matrix G G ℂ)ᴴ = 1 := V.property.2
    simp [hu,hv]⟩

def labelSumEquiv (m n : ℕ) (F : Type*) :
    (Fin m × F) ⊕ (Fin n × F) ≃ Fin (m+n) × F :=
  (Equiv.sumProdDistrib (Fin m) (Fin n) F).symm.trans
    (Equiv.prodCongr finSumFinEquiv (Equiv.refl F))

def labelSumUnitary {m n : ℕ} (U : Matrix.unitaryGroup (Fin m × F) ℂ)
    (V : Matrix.unitaryGroup (Fin n × F) ℂ) : Matrix.unitaryGroup (Fin (m+n) × F) ℂ :=
  rewireUnitary (labelSumEquiv m n F) (directSumUnitary U V)

def labelJoin {m n : ℕ} (x : Fin m × F → ℂ) (y : Fin n × F → ℂ) : Fin (m+n) × F → ℂ :=
  (Sum.elim x y) ∘ (labelSumEquiv m n F).symm

theorem labelSumUnitary_apply {m n : ℕ} (U : Matrix.unitaryGroup (Fin m × F) ℂ)
    (V : Matrix.unitaryGroup (Fin n × F) ℂ) (x : Fin m × F → ℂ) (y : Fin n × F → ℂ) :
    (labelSumUnitary U V : Matrix (Fin (m+n) × F) (Fin (m+n) × F) ℂ) *ᵥ
      labelJoin x y = labelJoin ((U : Matrix (Fin m × F) (Fin m × F) ℂ) *ᵥ x)
        ((V : Matrix (Fin n × F) (Fin n × F) ℂ) *ᵥ y) := by
  rw [labelSumUnitary, TransducerCompiler.rewire_apply]
  have he : labelJoin x y ∘ labelSumEquiv m n F = Sum.elim x y := by
    funext z; simp [labelJoin]
  rw [he]
  change (Matrix.fromBlocks _ _ _ _ *ᵥ Sum.elim x y) ∘ _ = _
  rw [Matrix.fromBlocks_mulVec]
  simp [labelJoin]

/-- Five active sectors and three unused sectors of the physical label register. -/
def bundle8 (ξ q ω₁ ω₂ z : F → ℂ) : Fin 8 × F → ℂ :=
  fun ji => (![ξ,q,ω₁,ω₂,z,0,0,0] ji.1) ji.2

theorem bundle8_labelJoin (ξ q ω₁ ω₂ z : F → ℂ) :
    bundle8 ξ q ω₁ ω₂ z =
      labelJoin (labelJoin (fun ji : Fin 1 × F => ξ ji.2) (kernelTriple q ω₁ ω₂))
        (fun ji : Fin 4 × F => (![z,0,0,0] ji.1) ji.2) := by
  ext ⟨j,i⟩
  fin_cases j <;> simp [bundle8, labelJoin, labelSumEquiv, kernelTriple,
    finSumFinEquiv, Fin.addCases]

/-- Kernel-reflection work acts on labels1,2,3, and fixes every other label. -/
def kernelWork8 (Q : Matrix F F ℂ) (hQ : star Q = Q) (hQQ : Q*Q=Q)
    {μ : ℝ} (hμ : 0 < μ) : Matrix.unitaryGroup (Fin 8 × F) ℂ :=
  labelSumUnitary (labelSumUnitary (1 : Matrix.unitaryGroup (Fin 1 × F) ℂ)
    (kernelWorkUnitary Q hQ hQQ (kernelMixA μ) (kernelMixB μ) (kernelMix_normalized hμ)))
      (1 : Matrix.unitaryGroup (Fin 4 × F) ℂ)

theorem kernelWork8_restoration (Q V : Matrix F F ℂ)
    (hQ : star Q=Q) (hQQ : Q*Q=Q) (hV : V*V=1)
    {μ α : ℝ} (hμ : 0 < μ) (hα : α≠0) (ξ q p z y : F → ℂ)
    (hq : Q*ᵥq=q) (hp : Q*ᵥp=p) (hz : Q*ᵥz=z)
    (hVp : Q*ᵥ(V*ᵥp)=0) (hVz : Q*ᵥ(V*ᵥz)=α⁻¹ • (q-p)) :
    (kernelWork8 Q hQ hQQ hμ : Matrix (Fin 8 × F) (Fin 8 × F) ℂ) *ᵥ
      bundle8 ξ q (V*ᵥkernelCatalystOne V μ α p z) (V*ᵥkernelCatalystTwo V μ α p z) y =
      bundle8 ξ ((2 : ℝ) • p-q) (kernelCatalystOne V μ α p z)
        (kernelCatalystTwo V μ α p z) y := by
  rw [bundle8_labelJoin, bundle8_labelJoin, kernelWork8,
    labelSumUnitary_apply, labelSumUnitary_apply]
  simp only [OneMemClass.coe_one, Matrix.one_mulVec]
  rw [kernel_catalyst_restoration Q V hQ hQQ hV hμ hα q p z hq hp hz hVp hVz]

end OptimalQLS.Preparation
