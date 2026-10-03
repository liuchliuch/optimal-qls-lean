import OptimalQLS.TransducerCompiler.Basic
import OptimalQLS.TransducerCompiler.Schedule

noncomputable section
namespace OptimalQLS.TransducerCompiler
open Matrix

inductive Label where
  | pub | internal | first | second
  deriving DecidableEq, Fintype

abbrev Base (n : Type*) := n × Label
abbrev Space (n : Type*) (K : ℕ) := Base n × Fin K

variable {n : Type*} [Fintype n] [DecidableEq n] {K : ℕ}

/-- The oracle is called on its entire query label, sharing one call over all clocks. -/
def query (l : Label) (U : Matrix.unitaryGroup n ℂ) : Matrix.unitaryGroup (Space n K) ℂ :=
  rewireUnitary (Equiv.prodAssoc n Label (Fin K)).symm
    (controlledOn (fun p : Label × Fin K => decide (p.1 = l)) U)

@[simp] theorem query_apply (l : Label) (U : Matrix.unitaryGroup n ℂ)
    (v : Space n K → ℂ) (i : n) (j : Label) (k : Fin K) :
    ((query (K := K) l U : Matrix (Space n K) (Space n K) ℂ) *ᵥ v) ((i,j),k) =
      if j = l then ((U : Matrix n n ℂ) *ᵥ fun x => v ((x,j),k)) i else v ((i,j),k) := by
  rw [query, rewire_apply]
  simp [Function.comp_def]

/-- Concrete public/private vector, with the catalyst relation supplied separately. -/
def bundle (ξ v₀ v₁ v₂ : n → ℂ) : Base n → ℂ
  | (i, .pub) => ξ i
  | (i, .internal) => v₀ i
  | (i, .first) => v₁ i
  | (i, .second) => v₂ i

/-- Exact state immediately before iteration t, without the common normalization. -/
def state (D₁ D₂ t : ℕ) (ξ τ v₀ v₁ v₂ q₁ q₂ : n → ℂ) : Space n K → ℂ
  | ((i,.pub),k) => if k.val < t then τ i else ξ i
  | ((i,.internal),k) => if k.val = 0 then v₀ i else 0
  | ((i,.first),k) => track D₁ t k.val (v₁ i) (q₁ i)
  | ((i,.second),k) => track D₂ t k.val (v₂ i) (q₂ i)

/-- Same state after the two scheduled oracle calls. -/
def beforeWork (D₁ D₂ t : ℕ) (ξ τ v₀ v₁ v₂ q₁ q₂ : n → ℂ) : Space n K → ℂ
  | ((i,.pub),k) => if k.val < t then τ i else ξ i
  | ((i,.internal),k) => if k.val = 0 then v₀ i else 0
  | ((i,.first),k) => queriedTrack D₁ t k.val (v₁ i) (q₁ i)
  | ((i,.second),k) => queriedTrack D₂ t k.val (v₂ i) (q₂ i)

/-- Routing uses only label and clock and is independent of every catalyst. -/
def address (zero : Fin K) (D₁ D₂ : ℕ) (t : Fin K)
    (h₁ : 0 < D₁) (h₂ : 0 < D₂) (h₁K : D₁ ≤ K) (h₂K : D₂ ≤ K) : Base n → Fin K
  | (_, .pub) => t
  | (_, .internal) => zero
  | (_, .first) => ⟨t.val % D₁, (Nat.mod_lt _ h₁).trans_le h₁K⟩
  | (_, .second) => ⟨t.val % D₂, (Nat.mod_lt _ h₂).trans_le h₂K⟩

/-- The two independent query schedules. -/
def oracleStage (D₁ D₂ t : ℕ) (U₁ U₂ : Matrix.unitaryGroup n ℂ) :
    Matrix.unitaryGroup (Space n K) ℂ :=
  (if t % D₂ = 0 then query .second U₂ else 1) *
  (if t % D₁ = 0 then query .first U₁ else 1)

theorem oracleStage_apply (D₁ D₂ t : ℕ) (U₁ U₂ : Matrix.unitaryGroup n ℂ)
    (ξ τ v₀ v₁ v₂ : n → ℂ) :
    (oracleStage (K := K) D₁ D₂ t U₁ U₂ : Matrix (Space n K) (Space n K) ℂ) *ᵥ
      state D₁ D₂ t ξ τ v₀ v₁ v₂ (U₁.val *ᵥ v₁) (U₂.val *ᵥ v₂) =
    beforeWork D₁ D₂ t ξ τ v₀ v₁ v₂ (U₁.val *ᵥ v₁) (U₂.val *ᵥ v₂) := by
  ext ⟨⟨i,l⟩,k⟩
  cases l <;> by_cases h₁ : t % D₁ = 0 <;> by_cases h₂ : t % D₂ = 0 <;>
    simp [oracleStage, h₁, h₂, ← Matrix.mulVec_mulVec, query_apply,
      state, beforeWork, track, queriedTrack] <;>
    split_ifs <;> simp_all [Matrix.mulVec, dotProduct]

/-- The selected component is exactly the canonical oracle-transformed input. -/
theorem beforeWork_selected (zero : Fin K) (hzero : zero.val = 0)
    (D₁ D₂ : ℕ) (t : Fin K) (h₁ : 0 < D₁) (h₂ : 0 < D₂)
    (h₁K : D₁ ≤ K) (h₂K : D₂ ≤ K) (ξ τ v₀ v₁ v₂ q₁ q₂ : n → ℂ) :
    (fun j => beforeWork D₁ D₂ t.val ξ τ v₀ v₁ v₂ q₁ q₂
      (j, address zero D₁ D₂ t h₁ h₂ h₁K h₂K j)) = bundle ξ v₀ q₁ q₂ := by
  ext ⟨i,l⟩
  cases l <;> simp [beforeWork, address, bundle, hzero,
    queriedTrack_selected, h₁, h₂]

/-- One exact work step, derived from the catalyst relation for the actual work matrix. -/
theorem work_step (zero : Fin K) (hzero : zero.val = 0)
    (D₁ D₂ : ℕ) (t : Fin K) (h₁ : 0 < D₁) (h₂ : 0 < D₂)
    (h₁K : D₁ ≤ K) (h₂K : D₂ ≤ K) (S : Matrix.unitaryGroup (Base n) ℂ)
    (ξ τ v₀ v₁ v₂ q₁ q₂ : n → ℂ)
    (hS : S.val *ᵥ bundle ξ v₀ q₁ q₂ = bundle τ v₀ v₁ v₂) :
    (routedWork zero (address zero D₁ D₂ t h₁ h₂ h₁K h₂K) S :
      Matrix (Space n K) (Space n K) ℂ) *ᵥ
      beforeWork D₁ D₂ t.val ξ τ v₀ v₁ v₂ q₁ q₂ =
      state D₁ D₂ (t.val+1) ξ τ v₀ v₁ v₂ q₁ q₂ := by
  ext ⟨⟨i,l⟩,k⟩
  rw [routedWork_apply, beforeWork_selected zero hzero D₁ D₂ t h₁ h₂ h₁K h₂K,
    hS]
  cases l with
  | pub =>
    simp only [address, bundle, beforeWork, state]
    by_cases hkt : k = t
    · subst k; simp
    · have hv : k.val ≠ t.val := fun h => hkt (Fin.ext h)
      have he : k.val < t.val + 1 ↔ k.val < t.val := by omega
      simp [hkt, he]
  | internal =>
    simp only [address, bundle, beforeWork, state]
    by_cases hk : k = zero
    · subst k; simp [hzero]
    · simp [hk]
  | first =>
    simp only [address, bundle, beforeWork, state]
    split_ifs with hk
    · have hkv : k.val = t.val % D₁ := congrArg Fin.val hk
      rw [hkv, track_step_selected D₁ t.val _ _ h₁]
    · have hkv : k.val ≠ t.val % D₁ := fun h => hk (Fin.ext h)
      exact (track_step_other D₁ t.val k.val _ _ h₁ hkv).symm
  | second =>
    simp only [address, bundle, beforeWork, state]
    split_ifs with hk
    · have hkv : k.val = t.val % D₂ := congrArg Fin.val hk
      rw [hkv, track_step_selected D₂ t.val _ _ h₂]
    · have hkv : k.val ≠ t.val % D₂ := fun h => hk (Fin.ext h)
      exact (track_step_other D₂ t.val k.val _ _ h₂ hkv).symm

end OptimalQLS.TransducerCompiler
