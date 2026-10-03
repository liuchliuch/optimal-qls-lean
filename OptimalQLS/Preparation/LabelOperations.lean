import OptimalQLS.Preparation.LabelBlocks
import OptimalQLS.FractionalTransducer

noncomputable section
namespace OptimalQLS.Preparation
open Matrix
variable {F : Type*} [Fintype F] [DecidableEq F]

def swap14 : Matrix.unitaryGroup (Fin 8 × F) ℂ :=
  TransducerCompiler.permutation (Equiv.prodCongr (Equiv.swap 1 4) (Equiv.refl F))

theorem swap14_apply (ξ q ω₁ ω₂ z : F → ℂ) :
    (swap14 (F := F) : Matrix (Fin 8 × F) (Fin 8 × F) ℂ) *ᵥ bundle8 ξ q ω₁ ω₂ z =
      bundle8 ξ z ω₁ ω₂ q := by
  rw [swap14, TransducerCompiler.permutation_apply]
  ext ⟨j,i⟩
  fin_cases j <;> simp [bundle8, Function.comp_def, Equiv.swap_apply_def]

def sign1 : Matrix.unitaryGroup (Fin 8 × F) ℂ :=
  ⟨Matrix.diagonal (fun ji => if ji.1 = 1 then (-1 : ℂ) else 1), by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
      Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
    have h : (fun ji : Fin 8 × F => (if ji.1=1 then (-1:ℂ) else 1) *
        star (if ji.1=1 then (-1:ℂ) else 1)) = 1 := by
      funext ji; split_ifs <;> simp
    simp only [Pi.star_apply]
    rw [h]
    exact Matrix.diagonal_one⟩

theorem sign1_apply (ξ q ω₁ ω₂ z : F → ℂ) :
    (sign1 (F := F) : Matrix (Fin 8 × F) (Fin 8 × F) ℂ) *ᵥ bundle8 ξ q ω₁ ω₂ z =
      bundle8 ξ (-q) ω₁ ω₂ z := by
  ext ⟨j,i⟩
  fin_cases j <;> simp [sign1, bundle8, Matrix.mulVec_diagonal]

def twoLabelEquiv (F : Type*) : F ⊕ F ≃ Fin 2 × F where
  toFun v := match v with | .inl x => (0,x) | .inr x => (1,x)
  invFun ji := if ji.1=0 then .inl ji.2 else .inr ji.2
  left_inv v := by cases v <;> simp
  right_inv ji := by rcases ji with ⟨j,i⟩; fin_cases j <;> simp

def pairVector (x y : F → ℂ) : Fin 2 × F → ℂ := fun ji => (![x,y] ji.1) ji.2

theorem pairVector_sum (x y : F → ℂ) : pairVector x y = Sum.elim x y ∘ (twoLabelEquiv F).symm := by
  ext ⟨j,i⟩; fin_cases j <;> simp [pairVector,twoLabelEquiv]

def mixFirstTwo {r : ℝ} (hr : |r|<1) : Matrix.unitaryGroup (Fin 2 × F) ℂ :=
  rewireUnitary (twoLabelEquiv F) ⟨fractionalMix r, fractionalMix_unitary hr⟩

theorem mixFirstTwo_apply {r : ℝ} (hr : |r|<1) (x y : F → ℂ) :
    (mixFirstTwo (F := F) hr : Matrix (Fin 2 × F) (Fin 2 × F) ℂ) *ᵥ pairVector x y =
      pairVector ((-r) • x + Real.sqrt (1-r^2) • y)
        (Real.sqrt (1-r^2) • x + r • y) := by
  rw [mixFirstTwo, TransducerCompiler.rewire_apply, pairVector_sum, pairVector_sum]
  have he : (Sum.elim x y ∘ (twoLabelEquiv F).symm) ∘ twoLabelEquiv F = Sum.elim x y := by
    funext v; simp
  rw [he]
  unfold fractionalMix
  rw [Matrix.fromBlocks_mulVec]
  simp [Matrix.smul_mulVec, Matrix.neg_mulVec]

def mix8 {r : ℝ} (hr : |r|<1) : Matrix.unitaryGroup (Fin 8 × F) ℂ :=
  labelSumUnitary (mixFirstTwo hr) (1 : Matrix.unitaryGroup (Fin 6 × F) ℂ)

theorem bundle8_firstTwoJoin (ξ q ω₁ ω₂ z : F → ℂ) :
    bundle8 ξ q ω₁ ω₂ z = labelJoin (pairVector ξ q)
      (fun ji : Fin 6 × F => (![ω₁,ω₂,z,0,0,0] ji.1) ji.2) := by
  ext ⟨j,i⟩
  fin_cases j <;> simp [bundle8,labelJoin,labelSumEquiv,pairVector,finSumFinEquiv,Fin.addCases]

theorem mix8_apply {r : ℝ} (hr : |r|<1) (ξ q ω₁ ω₂ z : F → ℂ) :
    (mix8 (F := F) hr : Matrix (Fin 8 × F) (Fin 8 × F) ℂ) *ᵥ bundle8 ξ q ω₁ ω₂ z =
      bundle8 ((-r) • ξ + Real.sqrt (1-r^2) • q)
        (Real.sqrt (1-r^2) • ξ + r • q) ω₁ ω₂ z := by
  rw [bundle8_firstTwoJoin,bundle8_firstTwoJoin,mix8,labelSumUnitary_apply,mixFirstTwo_apply]
  simp

/-- The literal order of the four work operations in the manuscript. -/
def preparationWork (Q : Matrix F F ℂ) (hQ : star Q=Q) (hQQ : Q*Q=Q)
    {μ r : ℝ} (hμ : 0<μ) (hr : |r|<1) : Matrix.unitaryGroup (Fin 8 × F) ℂ :=
  mix8 hr * sign1 * swap14 * kernelWork8 Q hQ hQQ hμ

/-- Component-by-component restoration by the full explicit work unitary.
The two scalar rows are supplied by the already-proved fractional transducer. -/
theorem preparationWork_apply (Q V R : Matrix F F ℂ)
    (hQ : star Q=Q) (hQQ : Q*Q=Q) (hV : V*V=1)
    {μ α r : ℝ} (hμ : 0<μ) (hα : α≠0) (hr : |r|<1)
    (ξ ψ q p z : F → ℂ) (hq : Q*ᵥq=q) (hp : Q*ᵥp=p) (hz : Q*ᵥz=z)
    (hVp : Q*ᵥ(V*ᵥp)=0) (hVz : Q*ᵥ(V*ᵥz)=α⁻¹ • (q-p))
    (hfirst : (-r) • ξ + Real.sqrt (1-r^2) • (-(R*ᵥ((2:ℝ) • p-q))) = ψ)
    (hsecond : Real.sqrt (1-r^2) • ξ + r • (-(R*ᵥ((2:ℝ) • p-q))) = q) :
    (preparationWork Q hQ hQQ hμ hr : Matrix (Fin 8 × F) (Fin 8 × F) ℂ) *ᵥ
      bundle8 ξ q (V*ᵥkernelCatalystOne V μ α p z) (V*ᵥkernelCatalystTwo V μ α p z)
        (R*ᵥ((2:ℝ) • p-q)) =
      bundle8 ψ q (kernelCatalystOne V μ α p z) (kernelCatalystTwo V μ α p z)
        ((2:ℝ) • p-q) := by
  simp only [preparationWork,Submonoid.coe_mul,← Matrix.mulVec_mulVec]
  rw [kernelWork8_restoration Q V hQ hQQ hV hμ hα ξ q p z _ hq hp hz hVp hVz,
    swap14_apply,sign1_apply,mix8_apply,hfirst,hsecond]

end OptimalQLS.Preparation
