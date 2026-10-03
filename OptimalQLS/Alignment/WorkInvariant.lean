import OptimalQLS.Preparation.LabelOperations
import OptimalQLS.Krylov
import OptimalQLS.SignalIsometry

/-! Exact real-subspace invariance of the literal eight-label preparation work. -/
noncomputable section
namespace OptimalQLS.Alignment
open Matrix Preparation
variable {F : Type*} [Fintype F] [DecidableEq F]

/-- Rectangular matrix action, regarded as a real-linear map. -/
def realMatrixMap {D : Type*} [Fintype D] (A : Matrix F D ℂ) :
    (D → ℂ) →ₗ[ℝ] (F → ℂ) where
  toFun := A.mulVec
  map_add' := Matrix.mulVec_add A
  map_smul' := by intro r v; exact Matrix.mulVec_smul A r v

@[simp] theorem realMatrixMap_apply {D : Type*} [Fintype D]
    (A : Matrix F D ℂ) (v : D → ℂ) : realMatrixMap A v = A *ᵥ v := rfl

/-- The inactive physical labels are exactly zero; the five active labels
carry the two real subspaces used in Lemma 4.9. -/
def eightInvariant (N M : Submodule ℝ (F → ℂ)) (v : Fin 8 × F → ℂ) : Prop :=
  ∃ ξ q ω₁ ω₂ z : F → ℂ,
    v = bundle8 ξ q ω₁ ω₂ z ∧ ξ ∈ N ∧ q ∈ N ∧ ω₁ ∈ M ∧ ω₂ ∈ M ∧ z ∈ N

theorem eightInvariant_bundle (N M : Submodule ℝ (F → ℂ))
    {ξ q ω₁ ω₂ z : F → ℂ} (hξ : ξ ∈ N) (hq : q ∈ N)
    (hω₁ : ω₁ ∈ M) (hω₂ : ω₂ ∈ M) (hz : z ∈ N) :
    eightInvariant N M (bundle8 ξ q ω₁ ω₂ z) :=
  ⟨ξ,q,ω₁,ω₂,z,rfl,hξ,hq,hω₁,hω₂,hz⟩

/-- Formula valid on every vector in the five active sectors, not only a
canonical catalyst. -/
theorem kernelWork8_apply (Q : Matrix F F ℂ) (hQ : star Q=Q) (hQQ : Q*Q=Q)
    {μ : ℝ} (hμ : 0<μ) (ξ q ω₁ ω₂ z : F → ℂ) :
    (kernelWork8 Q hQ hQQ hμ).val *ᵥ bundle8 ξ q ω₁ ω₂ z =
      bundle8 ξ (kernelMixA μ • (Q *ᵥ q) + (q-Q*ᵥq) + kernelMixB μ • (Q*ᵥω₂))
        (kernelMixB μ • (Q*ᵥq) + (-kernelMixA μ) • (Q*ᵥω₂) - (ω₂-Q*ᵥω₂))
        (ω₁-(2:ℝ) • (Q*ᵥω₁)) z := by
  rw [bundle8_labelJoin,bundle8_labelJoin,kernelWork8,labelSumUnitary_apply,
    labelSumUnitary_apply]
  simp only [OneMemClass.coe_one,Matrix.one_mulVec]
  rw [kernelWork_apply]

/-- The concrete signal-controlled kernel work preserves the stated real
subspaces whenever the compression sends the query subspace into the public one. -/
theorem kernelWork8_preserves (N M : Submodule ℝ (F → ℂ)) (hNM : N ≤ M)
    (Q : Matrix F F ℂ) (hQ : star Q=Q) (hQQ : Q*Q=Q)
    (hQN : ∀ x ∈ N, Q*ᵥx=x) (hQM : ∀ x ∈ M, Q*ᵥx∈N)
    {μ : ℝ} (hμ : 0<μ) {v : Fin 8 × F → ℂ} (hv : eightInvariant N M v) :
    eightInvariant N M ((kernelWork8 Q hQ hQQ hμ).val *ᵥ v) := by
  obtain ⟨ξ,q,ω₁,ω₂,z,rfl,hξ,hq,hω₁,hω₂,hz⟩ := hv
  rw [kernelWork8_apply, hQN q hq, sub_self, add_zero]
  apply eightInvariant_bundle N M hξ
  · exact N.add_mem (N.smul_mem _ hq) (N.smul_mem _ (hQM _ hω₂))
  · exact M.sub_mem (M.add_mem (M.smul_mem _ (hNM hq))
      (M.smul_mem _ (hNM (hQM _ hω₂)))) (M.sub_mem hω₂ (hNM (hQM _ hω₂)))
  · exact M.sub_mem hω₁ (M.smul_mem _ (hNM (hQM _ hω₁)))
  · exact hz

/-- All four actual work factors preserve the real invariant. -/
theorem preparationWork_preserves (N M : Submodule ℝ (F → ℂ)) (hNM : N ≤ M)
    (Q : Matrix F F ℂ) (hQ : star Q=Q) (hQQ : Q*Q=Q)
    (hQN : ∀ x ∈ N, Q*ᵥx=x) (hQM : ∀ x ∈ M, Q*ᵥx∈N)
    {μ r : ℝ} (hμ : 0<μ) (hr : |r|<1)
    {v : Fin 8 × F → ℂ} (hv : eightInvariant N M v) :
    eightInvariant N M ((preparationWork Q hQ hQQ hμ hr).val *ᵥ v) := by
  have hk := kernelWork8_preserves N M hNM Q hQ hQQ hQN hQM hμ hv
  obtain ⟨ξ,q,ω₁,ω₂,z,hv',hξ,hq,hω₁,hω₂,hz⟩ := hk
  simp only [preparationWork,Submonoid.coe_mul,← Matrix.mulVec_mulVec]
  rw [hv',swap14_apply,sign1_apply,mix8_apply]
  exact eightInvariant_bundle N M
    (N.add_mem (N.smul_mem _ hξ) (N.smul_mem _ (N.neg_mem hz)))
    (N.add_mem (N.smul_mem _ hξ) (N.smul_mem _ (N.neg_mem hz))) hω₁ hω₂ hq

/-- The two-term real orbit under an involution. -/
def oracleSpan (N : Submodule ℝ (F → ℂ)) (V : Matrix F F ℂ) : Submodule ℝ (F → ℂ) :=
  N ⊔ N.map (realMatrixMap V)

theorem le_oracleSpan (N : Submodule ℝ (F → ℂ)) (V : Matrix F F ℂ) : N ≤ oracleSpan N V :=
  le_sup_left

theorem oracleSpan_preserves (N : Submodule ℝ (F → ℂ)) (V : Matrix F F ℂ)
    (hV : V*V=1) {x : F → ℂ} (hx : x ∈ oracleSpan N V) : V*ᵥx∈oracleSpan N V := by
  obtain ⟨a,ha,b,hb,rfl⟩ := Submodule.mem_sup.mp hx
  obtain ⟨c,hc,rfl⟩ := hb
  rw [Matrix.mulVec_add]
  apply (oracleSpan N V).add_mem
  · exact (show N.map (realMatrixMap V) ≤ oracleSpan N V from le_sup_right) (Submodule.mem_map.mpr ⟨a,ha,rfl⟩)
  · simpa only [realMatrixMap_apply,Matrix.mulVec_mulVec,hV,Matrix.one_mulVec]
      using (le_oracleSpan N V hc)

/-- Q fixes N and sends VN back into N; hence it sends their real sum into N. -/
theorem compression_oracleSpan (N : Submodule ℝ (F → ℂ)) (Q V : Matrix F F ℂ)
    (hQN : ∀ x ∈ N, Q*ᵥx=x) (hQVN : ∀ x ∈ N, Q*ᵥ(V*ᵥx)∈N)
    {x : F → ℂ} (hx : x ∈ oracleSpan N V) : Q*ᵥx∈N := by
  obtain ⟨a,ha,b,hb,rfl⟩ := Submodule.mem_sup.mp hx
  obtain ⟨c,hc,rfl⟩ := hb
  rw [Matrix.mulVec_add,hQN a ha]
  exact N.add_mem ha (hQVN c hc)

end OptimalQLS.Alignment
