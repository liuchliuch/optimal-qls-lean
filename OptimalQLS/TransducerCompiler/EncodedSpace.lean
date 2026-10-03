import OptimalQLS.TransducerCompiler.ReservoirClock
import OptimalQLS.TransducerCompiler.HadamardClock
import OptimalQLS.TransducerCompiler.BinaryClock.Quantum

/-! # Exact encoded-subspace semantics for the cached comparator -/

noncomputable section
namespace OptimalQLS.TransducerCompiler
open Matrix
open BinaryClock

abbrev BitSpace (n : Type*) (ℓ : ℕ) := Base n × Bits ℓ
abbrev CachedSpace (n : Type*) (ℓ : ℕ) := Base n × (Bits ℓ × Bits ℓ)

variable {n : Type*} [Fintype n] [DecidableEq n] {ℓ : ℕ}

/-- The cache's exact Boolean contents on a given clock string. -/
def cache (x : Bits ℓ) : Bits ℓ := fun i => suffixZero x i.val

/-- Embed a clock vector in the valid comparator graph. -/
def encodeVector (v : BitSpace n ℓ → ℂ) : CachedSpace n ℓ → ℂ :=
  fun ⟨b,x,a⟩ => if a = cache x then v (b,x) else 0

/-- Embed a clock vector with every comparator ancilla zero. -/
def cleanVector (v : BitSpace n ℓ → ℂ) : CachedSpace n ℓ → ℂ :=
  fun ⟨b,x,a⟩ => if a = (fun _ => false) then v (b,x) else 0

/-- Only one physical cache bit controls the work circuit. Width zero is unconditional. -/
def cacheFlag (a : Bits ℓ) : Bool := if h : 0 < ℓ then a ⟨0,h⟩ else true

theorem cacheFlag_cache (x : Bits ℓ) : cacheFlag (cache x) = decide (x = fun _ => false) := by
  by_cases h : 0 < ℓ
  · simp only [cacheFlag, dif_pos h, cache, suffixZero]
    rw [Bool.eq_iff_iff]
    simp only [decide_eq_true_eq]
    constructor
    · intro hx
      funext i
      exact hx i (Nat.zero_le _)
    · intro hx
      subst x
      simp
  · have hx : x = fun _ => false := by
      funext i
      have hi := i.isLt
      omega
    simp [cacheFlag, h, hx]

/-- Literal single-cache-bit controlled work matrix. -/
def cachedWork (S : Matrix.unitaryGroup (Base n) ℂ) : Matrix.unitaryGroup (CachedSpace n ℓ) ℂ :=
  controlledOn (fun p : Bits ℓ × Bits ℓ => cacheFlag p.2) S

/-- The corresponding ideal zero-clock-controlled matrix. -/
def bitWork (S : Matrix.unitaryGroup (Base n) ℂ) : Matrix.unitaryGroup (BitSpace n ℓ) ℂ :=
  controlledOn (fun x : Bits ℓ => decide (x = fun _ => false)) S

/-- The one-bit-controlled work matrix preserves the entire valid encoded subspace. -/
theorem cachedWork_encodeVector (S : Matrix.unitaryGroup (Base n) ℂ)
    (v : BitSpace n ℓ → ℂ) :
    (cachedWork (ℓ := ℓ) S).val *ᵥ encodeVector v = encodeVector ((bitWork S).val *ᵥ v) := by
  ext ⟨b,x,a⟩
  rw [cachedWork, controlledOn_apply]
  by_cases ha : a = cache x
  · subst a
    simp only [cacheFlag_cache, encodeVector, ite_true, bitWork, controlledOn_apply]
  · simp [encodeVector, ha, Matrix.mulVec, dotProduct]

/-- A data oracle on a label, with arbitrary finite non-data multiplicity. -/
def dataQuery {a : Type*} [Fintype a] [DecidableEq a]
    (l : Label) (U : Matrix.unitaryGroup n ℂ) : Matrix.unitaryGroup (Base n × a) ℂ :=
  rewireUnitary (Equiv.prodAssoc n Label a).symm
    (controlledOn (fun p : Label × a => decide (p.1 = l)) U)

theorem dataQuery_apply {a : Type*} [Fintype a] [DecidableEq a]
    (l : Label) (U : Matrix.unitaryGroup n ℂ) (v : Base n × a → ℂ)
    (i : n) (j : Label) (k : a) :
    ((dataQuery (a := a) l U).val *ᵥ v) ((i,j),k) =
      if j = l then (U.val *ᵥ fun x => v ((x,j),k)) i else v ((i,j),k) := by
  rw [dataQuery, rewire_apply]
  simp [Function.comp_def]

/-- Querying data never invalidates the clock comparator. -/
theorem dataQuery_encodeVector (l : Label) (U : Matrix.unitaryGroup n ℂ)
    (v : BitSpace n ℓ → ℂ) :
    (dataQuery (a := Bits ℓ × Bits ℓ) l U).val *ᵥ encodeVector v =
      encodeVector ((dataQuery (a := Bits ℓ) l U).val *ᵥ v) := by
  ext ⟨⟨i,j⟩,x,a⟩
  rw [dataQuery_apply]
  by_cases ha : a = cache x
  · simp only [encodeVector, ha, ite_true, dataQuery_apply]
  · simp [encodeVector, ha, Matrix.mulVec, dotProduct]

/-- Encoded and clean embeddings both preserve the Hilbert-space norm exactly. -/
theorem encodeVector_norm (v : BitSpace n ℓ → ℂ) :
    ‖WithLp.toLp 2 (encodeVector v)‖ = ‖WithLp.toLp 2 v‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  simp [encodeVector, apply_ite]

theorem cleanVector_norm (v : BitSpace n ℓ → ℂ) :
    ‖WithLp.toLp 2 (cleanVector v)‖ = ‖WithLp.toLp 2 v‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  simp [cleanVector, apply_ite]

/-- Physical label bits are a complete computational-basis encoding. -/
def labelBitsEquiv : Label ≃ LabelBits where
  toFun := labelCode
  invFun p := match p with
    | (false,false) => .pub
    | (false,true) => .internal
    | (true,false) => .first
    | (true,true) => .second
  left_inv l := by cases l <;> rfl
  right_inv p := by rcases p with ⟨a,b⟩; cases a <;> cases b <;> rfl

/-- Explicit wiring of the label, clock, and cache wires to their product coordinates. -/
def labelStateEquiv : LabelState ℓ ≃ Label × (Bits ℓ × Bits ℓ) where
  toFun b := (labelBitsEquiv.symm (b (.inl 0),b (.inl 1)),
    (fun i => b (.inr (.inl i))), (fun i => b (.inr (.inr i))))
  invFun p := extend (labelCode p.1) (Sum.elim p.2.1 p.2.2)
  left_inv b := by
    funext w
    cases w with
    | inl i =>
      cases h₀ : b (.inl 0) <;> cases h₁ : b (.inl 1) <;> fin_cases i <;>
        simp [extend, labelCode, labelBitsEquiv, h₀, h₁]
    | inr i => cases i <;> rfl
  right_inv p := by
    rcases p with ⟨l,x,a⟩
    cases l <;> simp [extend, labelCode, labelBitsEquiv]

theorem labelStateEquiv_encode (l : Label) (x : Bits ℓ) :
    labelStateEquiv (extend (labelCode l) (encode x)) = (l,x,cache x) := by
  cases l <;> simp [labelStateEquiv, labelBitsEquiv, extend, labelCode,
    encode, partialEncode, cache, -partialEncode_zero] <;> rfl

/-- Expansion in the actual encoded computational basis. -/
theorem encodeVector_eq_sum (v : BitSpace n ℓ → ℂ) :
    encodeVector v = ∑ z : BitSpace n ℓ, v z • (Pi.single (z.1,z.2,cache z.2) (1 : ℂ) : CachedSpace n ℓ → ℂ) := by
  ext ⟨⟨i,l⟩,x,a⟩
  simp [encodeVector, Fintype.sum_prod_type, Pi.single_apply, Prod.mk.injEq,
    eq_comm, Finset.mul_sum, ite_and]

/-- Expansion in the actual clean computational basis. -/
theorem cleanVector_eq_sum (v : BitSpace n ℓ → ℂ) :
    cleanVector v = ∑ z : BitSpace n ℓ,
      v z • (Pi.single (z.1,z.2,(fun _ : Fin ℓ => false)) (1 : ℂ) : CachedSpace n ℓ → ℂ) := by
  ext ⟨⟨i,l⟩,x,a⟩
  simp [cleanVector, Fintype.sum_prod_type, Pi.single_apply, Prod.mk.injEq,
    eq_comm, Finset.mul_sum, ite_and]

end OptimalQLS.TransducerCompiler
