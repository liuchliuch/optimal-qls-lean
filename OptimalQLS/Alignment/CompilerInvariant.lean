import OptimalQLS.TransducerCompiler.HadamardFinite
import OptimalQLS.TransducerCompiler.Complete

/-! Real subspace invariance of the actual finite compiler, including its clocks. -/
noncomputable section
namespace OptimalQLS.Alignment
open Matrix TransducerCompiler

variable {n : Type*} [Fintype n] [DecidableEq n] {K : ℕ}

/-- Each label of the work space belongs to its prescribed real submodule. -/
def baseInvariant (P : Label → Submodule ℝ (n → ℂ)) (v : Base n → ℂ) : Prop :=
  ∀ l, (fun i => v (i,l)) ∈ P l

/-- The same real submodule condition holds separately at every clock address. -/
def sectorInvariant (P : Label → Submodule ℝ (n → ℂ)) (v : Space n K → ℂ) : Prop :=
  ∀ l k, (fun i => v ((i,l),k)) ∈ P l

theorem routedWork_preserves (P : Label → Submodule ℝ (n → ℂ))
    (zero : Fin K) (f : Label → Fin K) (S : Matrix.unitaryGroup (Base n) ℂ)
    (hS : ∀ v, baseInvariant P v → baseInvariant P (S.val *ᵥ v))
    {v : Space n K → ℂ} (hv : sectorInvariant P v) :
    sectorInvariant P ((routedWork zero (fun a => f a.2) S).val *ᵥ v) := by
  have hselected : baseInvariant P (fun a => v (a,f a.2)) := fun l => hv l (f l)
  intro l k
  by_cases hk : k = f l
  · simpa only [routedWork_apply, hk, ite_true] using hS _ hselected l
  · simpa only [routedWork_apply, hk, ite_false] using hv l k

theorem query_preserves (P : Label → Submodule ℝ (n → ℂ))
    (l : Label) (U : Matrix.unitaryGroup n ℂ)
    (hU : ∀ x ∈ P l, U.val *ᵥ x ∈ P l)
    {v : Space n K → ℂ} (hv : sectorInvariant P v) :
    sectorInvariant P ((query l U).val *ᵥ v) := by
  intro j k
  by_cases hj : j = l
  · subst j
    simpa only [query_apply, ite_true] using hU _ (hv l k)
  · simpa only [query_apply, hj, ite_false] using hv j k

/-- A real clock matrix combines slices only with real coefficients. -/
theorem clockLift_preserves (P : Label → Submodule ℝ (n → ℂ))
    (C : Matrix.unitaryGroup (Fin K) ℂ) (hC : ∀ i j, (C.val i j).im = 0)
    {v : Space n K → ℂ} (hv : sectorInvariant P v) :
    sectorInvariant P ((clockLift C).val *ᵥ v) := by
  intro l k
  have heq : (fun i => ((clockLift C).val *ᵥ v) ((i,l),k)) =
      ∑ j : Fin K, (C.val k j).re • (fun i => v ((i,l),j)) := by
    funext i
    rw [clockLift_apply]
    simp only [Matrix.mulVec, dotProduct, Finset.sum_apply,
      Pi.smul_apply, Complex.real_smul]
    apply Finset.sum_congr rfl
    intro j _
    have hc : ((C.val k j).re : ℂ) = C.val k j := by
      apply Complex.ext <;> simp [hC]
    rw [hc]
  rw [heq]
  exact (P l).sum_mem (fun j _ => (P l).smul_mem _ (hv l j))

theorem real_unitary_inverse {a : Type*} [Fintype a] [DecidableEq a]
    (C : Matrix.unitaryGroup a ℂ) (hC : ∀ i j, (C.val i j).im = 0) (i j : a) :
    ((C⁻¹).val i j).im = 0 := by
  change ((star C.val) i j).im = 0
  simp [hC]

theorem clockLift_inverse (C : Matrix.unitaryGroup (Fin K) ℂ) :
    (clockLift (n := n) C)⁻¹ = clockLift (C⁻¹) := by
  apply Subtype.ext
  ext ⟨a,i⟩ ⟨b,j⟩
  change star (if b = a then C.val j i else (0 : ℂ)) =
    if a = b then star (C.val j i) else 0
  by_cases hab : a = b
  · simp [hab]
  · simp [hab, Ne.symm hab]

theorem clockLift_inverse_preserves (P : Label → Submodule ℝ (n → ℂ))
    (C : Matrix.unitaryGroup (Fin K) ℂ) (hC : ∀ i j, (C.val i j).im = 0)
    {v : Space n K → ℂ} (hv : sectorInvariant P v) :
    sectorInvariant P (((clockLift C)⁻¹).val *ᵥ v) := by
  rw [clockLift_inverse]
  exact clockLift_preserves P C⁻¹ (real_unitary_inverse C hC) hv

theorem instruction_preserves (P : Label → Submodule ℝ (n → ℂ))
    (b : Layout K) (S : Matrix.unitaryGroup (Base n) ℂ)
    (U₁ U₂ : Matrix.unitaryGroup n ℂ)
    (hS : ∀ v, baseInvariant P v → baseInvariant P (S.val *ᵥ v))
    (hU₁ : ∀ x ∈ P .first, U₁.val *ᵥ x ∈ P .first)
    (hU₂ : ∀ x ∈ P .second, U₂.val *ᵥ x ∈ P .second)
    (g : Instruction) {v : Space n K → ℂ} (hv : sectorInvariant P v) :
    sectorInvariant P ((g.eval b S U₁ U₂).val *ᵥ v) := by
  cases g with
  | query₁ => exact query_preserves P .first U₁ hU₁ hv
  | query₂ => exact query_preserves P .second U₂ hU₂ hv
  | clock adj =>
    cases adj with
    | false => exact clockLift_preserves P _ (clockPrepare_real b.zero) hv
    | true => exact clockLift_inverse_preserves P _ (clockPrepare_real b.zero) hv
  | work t =>
    let f : Label → Fin K
      | .pub => b.time t
      | .internal => b.zero
      | .first => ⟨(b.time t).val % b.D₁,
          (Nat.mod_lt _ b.positive₁).trans_le b.le₁⟩
      | .second => ⟨(b.time t).val % b.D₂,
          (Nat.mod_lt _ b.positive₂).trans_le b.le₂⟩
    have hf : address (n := n) b.zero b.D₁ b.D₂ (b.time t)
        b.positive₁ b.positive₂ b.le₁ b.le₂ = fun a => f a.2 := by
      funext ⟨i,l⟩
      cases l <;> rfl
    simpa only [Instruction.eval, hf] using routedWork_preserves P b.zero f S hS hv

/-- Induction on the literal circuit, including general real clock preparation. -/
theorem circuit_preserves (P : Label → Submodule ℝ (n → ℂ))
    (b : Layout K) (S : Matrix.unitaryGroup (Base n) ℂ)
    (U₁ U₂ : Matrix.unitaryGroup n ℂ)
    (hS : ∀ v, baseInvariant P v → baseInvariant P (S.val *ᵥ v))
    (hU₁ : ∀ x ∈ P .first, U₁.val *ᵥ x ∈ P .first)
    (hU₂ : ∀ x ∈ P .second, U₂.val *ᵥ x ∈ P .second)
    (c : Circuit) {v : Space n K → ℂ} (hv : sectorInvariant P v) :
    sectorInvariant P ((c.eval b S U₁ U₂).val *ᵥ v) := by
  induction c generalizing v with
  | nil => simpa only [Circuit.eval, OneMemClass.coe_one, Matrix.one_mulVec] using hv
  | cons g gs ih =>
    simp only [Circuit.eval, Submonoid.coe_mul, ← Matrix.mulVec_mulVec]
    exact ih (instruction_preserves P b S U₁ U₂ hS hU₁ hU₂ g hv)

theorem hadamardFiniteUnitary_preserves (P : Label → Submodule ℝ (n → ℂ))
    {ℓ : ℕ} (b : Layout (2^ℓ)) (S : Matrix.unitaryGroup (Base n) ℂ)
    (U₁ U₂ : Matrix.unitaryGroup n ℂ)
    (hS : ∀ v, baseInvariant P v → baseInvariant P (S.val *ᵥ v))
    (hU₁ : ∀ x ∈ P .first, U₁.val *ᵥ x ∈ P .first)
    (hU₂ : ∀ x ∈ P .second, U₂.val *ᵥ x ∈ P .second)
    {v : Space n (2^ℓ) → ℂ} (hv : sectorInvariant P v) :
    sectorInvariant P ((hadamardFiniteUnitary b S U₁ U₂).val *ᵥ v) := by
  simp only [hadamardFiniteUnitary, Submonoid.coe_mul, ← Matrix.mulVec_mulVec]
  apply clockLift_inverse_preserves P _ (HadamardClock.finHadamard_real ℓ)
  apply circuit_preserves P b S U₁ U₂ hS hU₁ hU₂
  exact clockLift_preserves P _ (HadamardClock.finHadamard_real ℓ) hv

theorem finiteUnitary_preserves (P : Label → Submodule ℝ (n → ℂ))
    (b : Layout K) (S : Matrix.unitaryGroup (Base n) ℂ)
    (U₁ U₂ : Matrix.unitaryGroup n ℂ)
    (hS : ∀ v, baseInvariant P v → baseInvariant P (S.val *ᵥ v))
    (hU₁ : ∀ x ∈ P .first, U₁.val *ᵥ x ∈ P .first)
    (hU₂ : ∀ x ∈ P .second, U₂.val *ᵥ x ∈ P .second)
    {v : Space n K → ℂ} (hv : sectorInvariant P v) :
    sectorInvariant P ((finiteUnitary b S U₁ U₂).val *ᵥ v) := by
  simp only [finiteUnitary, Submonoid.coe_mul, ← Matrix.mulVec_mulVec]
  apply clockLift_inverse_preserves P _ (clockPrepare_real b.zero)
  apply circuit_preserves P b S U₁ U₂ hS hU₁ hU₂
  exact clockLift_preserves P _ (clockPrepare_real b.zero) hv

omit [Fintype n] [DecidableEq n] in
theorem inputState_invariant (P : Label → Submodule ℝ (n → ℂ))
    (zero : Fin K) {ξ : n → ℂ} (hξ : ξ ∈ P .pub) :
    sectorInvariant P (inputState zero ξ) := by
  intro l k
  cases l with
  | pub =>
    by_cases hk : k = zero
    · simpa only [inputState, hk, ite_true] using hξ
    · simpa only [inputState, hk, ite_false] using (P .pub).zero_mem
  | internal => exact (P .internal).zero_mem
  | first => exact (P .first).zero_mem
  | second => exact (P .second).zero_mem

/-- In particular the public output slice remains in the real public subspace. -/
theorem hadamardFiniteUnitary_public_mem (P : Label → Submodule ℝ (n → ℂ))
    {ℓ : ℕ} (b : Layout (2^ℓ)) (S : Matrix.unitaryGroup (Base n) ℂ)
    (U₁ U₂ : Matrix.unitaryGroup n ℂ)
    (hS : ∀ v, baseInvariant P v → baseInvariant P (S.val *ᵥ v))
    (hU₁ : ∀ x ∈ P .first, U₁.val *ᵥ x ∈ P .first)
    (hU₂ : ∀ x ∈ P .second, U₂.val *ᵥ x ∈ P .second)
    {ξ : n → ℂ} (hξ : ξ ∈ P .pub) (k : Fin (2^ℓ)) :
    (fun i => ((hadamardFiniteUnitary b S U₁ U₂).val *ᵥ inputState b.zero ξ)
      ((i,.pub),k)) ∈ P .pub :=
  hadamardFiniteUnitary_preserves P b S U₁ U₂ hS hU₁ hU₂
    (inputState_invariant P b.zero hξ) .pub k

/-- Exact cleanup transfers the real invariant to the literal synthesized output,
with any retained clock string and with all returned ancillas zero. -/
theorem synthesized_clock_slice_mem (P : Label → Submodule ℝ (n → ℂ))
    {ℓ : ℕ} (b : Layout (2^ℓ)) (d₁ d₂ : ℕ)
    (h₁ : b.D₁ = 2^d₁) (h₂ : b.D₂ = 2^d₂)
    (S : Matrix.unitaryGroup (Base n) ℂ) (U₁ U₂ : Matrix.unitaryGroup n ℂ)
    (hS : ∀ v, baseInvariant P v → baseInvariant P (S.val *ᵥ v))
    (hU₁ : ∀ x ∈ P .first, U₁.val *ᵥ x ∈ P .first)
    (hU₂ : ∀ x ∈ P .second, U₂.val *ᵥ x ∈ P .second)
    {ξ : n → ℂ} (hξ : ξ ∈ P .pub) (l : Label) (x : BinaryClock.Bits ℓ) :
    (fun i => (((synthesize (cachedCompile ℓ d₁ d₂)).eval S U₁ U₂).val *ᵥ
      synthInput b ξ) (false,((i,l),x,(fun _ => false)))) ∈ P l := by
  have hv := hadamardFiniteUnitary_preserves P b S U₁ U₂ hS hU₁ hU₂
    (inputState_invariant P b.zero hξ) l (HadamardClock.bitsFinEquiv ℓ x)
  simp only [synthInput, cachedInput]
  rw [complete_cleanup b d₁ d₂ h₁ h₂, toBit_mulVec]
  simpa only [synthClean, cleanVector, ite_true, inputToBits,
    Function.comp_apply, spaceBitsEquiv, Equiv.prodCongr_apply, Equiv.refl_apply] using hv

/-- The all-zero auxiliary output component of the actual finite implementation
belongs to its prescribed real label submodule. -/
theorem synthesized_zero_slice_mem (P : Label → Submodule ℝ (n → ℂ))
    {ℓ : ℕ} (b : Layout (2^ℓ)) (d₁ d₂ : ℕ)
    (h₁ : b.D₁ = 2^d₁) (h₂ : b.D₂ = 2^d₂)
    (S : Matrix.unitaryGroup (Base n) ℂ) (U₁ U₂ : Matrix.unitaryGroup n ℂ)
    (hS : ∀ v, baseInvariant P v → baseInvariant P (S.val *ᵥ v))
    (hU₁ : ∀ x ∈ P .first, U₁.val *ᵥ x ∈ P .first)
    (hU₂ : ∀ x ∈ P .second, U₂.val *ᵥ x ∈ P .second)
    {ξ : n → ℂ} (hξ : ξ ∈ P .pub) (l : Label) :
    (fun i => (((synthesize (cachedCompile ℓ d₁ d₂)).eval S U₁ U₂).val *ᵥ
      synthInput b ξ) (false,((i,l),(fun _ => false),(fun _ => false)))) ∈ P l :=
  synthesized_clock_slice_mem P b d₁ d₂ h₁ h₂ S U₁ U₂ hS hU₁ hU₂ hξ l _

end OptimalQLS.Alignment
