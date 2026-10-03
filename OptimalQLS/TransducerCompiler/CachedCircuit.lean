import OptimalQLS.TransducerCompiler.QuantumProgram
import OptimalQLS.TransducerCompiler.QueryCounts

/-! # A literal cached-comparator compiler circuit

The classical operations below are actual reversible primitive programs.
The quantum work call is controlled by a single cached bit. All comparator
ancillas are initialized and cleaned coherently on every data/clock vector.
-/

noncomputable section
namespace OptimalQLS.TransducerCompiler
open Matrix BinaryClock

inductive CachedInstruction (ℓ : ℕ) where
  | query₁
  | query₂
  | work
  | classical (p : Program (LabelWire ℓ))

abbrev CachedCircuit (ℓ : ℕ) := List (CachedInstruction ℓ)

variable {n : Type*} [Fintype n] [DecidableEq n] {ℓ : ℕ}

def CachedInstruction.eval (S : Matrix.unitaryGroup (Base n) ℂ)
    (U₁ U₂ : Matrix.unitaryGroup n ℂ) : CachedInstruction ℓ → Matrix.unitaryGroup (CachedSpace n ℓ) ℂ
  | .query₁ => dataQuery .first U₁
  | .query₂ => dataQuery .second U₂
  | .work => cachedWork S
  | .classical p => programOnSpace p

def CachedCircuit.eval (S : Matrix.unitaryGroup (Base n) ℂ)
    (U₁ U₂ : Matrix.unitaryGroup n ℂ) : CachedCircuit ℓ → Matrix.unitaryGroup (CachedSpace n ℓ) ℂ
  | [] => 1
  | g :: gs => CachedCircuit.eval S U₁ U₂ gs * g.eval S U₁ U₂

theorem CachedCircuit.eval_append (S : Matrix.unitaryGroup (Base n) ℂ)
    (U₁ U₂ : Matrix.unitaryGroup n ℂ) (c d : CachedCircuit ℓ) :
    (c ++ d).eval S U₁ U₂ = d.eval S U₁ U₂ * c.eval S U₁ U₂ := by
  induction c with
  | nil => simp [eval]
  | cons g gs ih => simp [eval, ih, mul_assoc]

/-- Scheduled queries, one cached-bit-controlled work call, and one frame update. -/
def cachedRound (ℓ d₁ d₂ t : ℕ) : CachedCircuit ℓ :=
  (if t % 2 ^ d₁ = 0 then [.query₁] else []) ++
  (if t % 2 ^ d₂ = 0 then [.query₂] else []) ++
  [.work, .classical (reservoirUpdate ℓ d₁ d₂ t)]

def cachedPrefix (ℓ d₁ d₂ : ℕ) : ℕ → CachedCircuit ℓ
  | 0 => []
  | t + 1 => cachedPrefix ℓ d₁ d₂ t ++ cachedRound ℓ d₁ d₂ t

/-- The corresponding ideal oracle stage on the clock without its comparator cache. -/
def idealBitOracleStage (ℓ d₁ d₂ t : ℕ) (U₁ U₂ : Matrix.unitaryGroup n ℂ) :
    Matrix.unitaryGroup (BitSpace n ℓ) ℂ :=
  (if t % 2 ^ d₂ = 0 then dataQuery .second U₂ else 1) *
  (if t % 2 ^ d₁ = 0 then dataQuery .first U₁ else 1)

/-- Ideal bit-space round, with the explicit XOR address difference. -/
def idealBitRound (ℓ d₁ d₂ t : ℕ) (S : Matrix.unitaryGroup (Base n) ℂ)
    (U₁ U₂ : Matrix.unitaryGroup n ℂ) : Matrix.unitaryGroup (BitSpace n ℓ) ℂ :=
  bitUpdate ℓ d₁ d₂ t * bitWork S * idealBitOracleStage ℓ d₁ d₂ t U₁ U₂

def idealBitPrefix (ℓ d₁ d₂ : ℕ) (S : Matrix.unitaryGroup (Base n) ℂ)
    (U₁ U₂ : Matrix.unitaryGroup n ℂ) : ℕ → Matrix.unitaryGroup (BitSpace n ℓ) ℂ
  | 0 => 1
  | t + 1 => idealBitRound ℓ d₁ d₂ t S U₁ U₂ * idealBitPrefix ℓ d₁ d₂ S U₁ U₂ t

/-- One physical primitive round exactly intertwines with its ideal bit-space round. -/
theorem cachedRound_encodeVector (ℓ d₁ d₂ t : ℕ) (S : Matrix.unitaryGroup (Base n) ℂ)
    (U₁ U₂ : Matrix.unitaryGroup n ℂ) (v : BitSpace n ℓ → ℂ) :
    ((cachedRound ℓ d₁ d₂ t).eval S U₁ U₂).val *ᵥ encodeVector v =
      encodeVector ((idealBitRound ℓ d₁ d₂ t S U₁ U₂).val *ᵥ v) := by
  by_cases h₁ : t % 2 ^ d₁ = 0 <;> by_cases h₂ : t % 2 ^ d₂ = 0 <;>
    simp [cachedRound, h₁, h₂, CachedCircuit.eval, CachedInstruction.eval,
      idealBitRound, idealBitOracleStage, ← Matrix.mulVec_mulVec,
      dataQuery_encodeVector, cachedWork_encodeVector, reservoirUpdate_encodeVector]

/-- The complete physical prefix preserves the encoded subspace on arbitrary superpositions. -/
theorem cachedPrefix_encodeVector (ℓ d₁ d₂ : ℕ) (S : Matrix.unitaryGroup (Base n) ℂ)
    (U₁ U₂ : Matrix.unitaryGroup n ℂ) (t : ℕ) (v : BitSpace n ℓ → ℂ) :
    ((cachedPrefix ℓ d₁ d₂ t).eval S U₁ U₂).val *ᵥ encodeVector v =
      encodeVector ((idealBitPrefix ℓ d₁ d₂ S U₁ U₂ t).val *ᵥ v) := by
  induction t with
  | zero => simp [cachedPrefix, CachedCircuit.eval, idealBitPrefix]
  | succ t ih =>
    rw [cachedPrefix, CachedCircuit.eval_append, Submonoid.coe_mul,
      ← Matrix.mulVec_mulVec, ih, cachedRound_encodeVector]
    simp only [idealBitPrefix, Submonoid.coe_mul, ← Matrix.mulVec_mulVec]

/-- Actual cache initialization, one full loop, and exact cache uncomputation. -/
def cachedCompile (ℓ d₁ d₂ : ℕ) : CachedCircuit ℓ :=
  [.classical (cachePrepareProgram ℓ)] ++ cachedPrefix ℓ d₁ d₂ (2 ^ ℓ) ++
    [.classical (cacheUnprepareProgram ℓ)]

/-- Exact clean-cache semantics of the entire physically specified compiler body. -/
theorem cachedCompile_cleanVector (ℓ d₁ d₂ : ℕ) (S : Matrix.unitaryGroup (Base n) ℂ)
    (U₁ U₂ : Matrix.unitaryGroup n ℂ) (v : BitSpace n ℓ → ℂ) :
    ((cachedCompile ℓ d₁ d₂).eval S U₁ U₂).val *ᵥ cleanVector v =
      cleanVector ((idealBitPrefix ℓ d₁ d₂ S U₁ U₂ (2 ^ ℓ)).val *ᵥ v) := by
  simp only [cachedCompile, CachedCircuit.eval_append, CachedCircuit.eval,
    CachedInstruction.eval, one_mul, Submonoid.coe_mul, ← Matrix.mulVec_mulVec,
    cachePrepare_cleanVector, cachedPrefix_encodeVector, cacheUnprepare_encodeVector]

def CachedInstruction.workCost : CachedInstruction ℓ → ℕ
  | .work => 1
  | _ => 0

def CachedInstruction.firstCost : CachedInstruction ℓ → ℕ
  | .query₁ => 1
  | _ => 0

def CachedInstruction.secondCost : CachedInstruction ℓ → ℕ
  | .query₂ => 1
  | _ => 0

/-- Count literal NOT/CNOT/Toffoli instructions, not arbitrary classical matrices. -/
def CachedInstruction.primitiveCost : CachedInstruction ℓ → ℕ
  | .classical p => p.length
  | _ => 0

def CachedCircuit.workCalls (c : CachedCircuit ℓ) : ℕ := (c.map CachedInstruction.workCost).sum
def CachedCircuit.firstCalls (c : CachedCircuit ℓ) : ℕ := (c.map CachedInstruction.firstCost).sum
def CachedCircuit.secondCalls (c : CachedCircuit ℓ) : ℕ := (c.map CachedInstruction.secondCost).sum
def CachedCircuit.primitiveGates (c : CachedCircuit ℓ) : ℕ := (c.map CachedInstruction.primitiveCost).sum

theorem cachedPrefix_workCalls (ℓ d₁ d₂ t : ℕ) : (cachedPrefix ℓ d₁ d₂ t).workCalls = t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    by_cases h₁ : t % 2 ^ d₁ = 0 <;> by_cases h₂ : t % 2 ^ d₂ = 0 <;>
      simpa [cachedPrefix, CachedCircuit.workCalls, cachedRound,
        CachedInstruction.workCost, h₁, h₂] using ih

theorem cachedPrefix_firstCalls (ℓ d₁ d₂ t : ℕ) :
    (cachedPrefix ℓ d₁ d₂ t).firstCalls = scheduledCount (2 ^ d₁) t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    by_cases h₁ : t % 2 ^ d₁ = 0 <;> by_cases h₂ : t % 2 ^ d₂ = 0 <;>
      simp_all [cachedPrefix, CachedCircuit.firstCalls, cachedRound,
        CachedInstruction.firstCost, scheduledCount]

theorem cachedPrefix_secondCalls (ℓ d₁ d₂ t : ℕ) :
    (cachedPrefix ℓ d₁ d₂ t).secondCalls = scheduledCount (2 ^ d₂) t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    by_cases h₁ : t % 2 ^ d₁ = 0 <;> by_cases h₂ : t % 2 ^ d₂ = 0 <;>
      simp_all [cachedPrefix, CachedCircuit.secondCalls, cachedRound,
        CachedInstruction.secondCost, scheduledCount]

theorem cachedPrefix_primitiveGates (ℓ d₁ d₂ t : ℕ) :
    (cachedPrefix ℓ d₁ d₂ t).primitiveGates =
      ∑ u ∈ Finset.range t, (reservoirUpdate ℓ d₁ d₂ u).length := by
  induction t with
  | zero => rfl
  | succ t ih =>
    by_cases h₁ : t % 2 ^ d₁ = 0 <;> by_cases h₂ : t % 2 ^ d₂ = 0 <;>
      simpa [cachedPrefix, CachedCircuit.primitiveGates, cachedRound,
        CachedInstruction.primitiveCost, h₁, h₂, Finset.sum_range_succ] using
        congrArg (· + (reservoirUpdate ℓ d₁ d₂ t).length) ih

/-- Exact black-box counts for the complete cached implementation. -/
theorem cachedCompile_exact_counts (ℓ d₁ d₂ : ℕ) (h₁ : d₁ ≤ ℓ) (h₂ : d₂ ≤ ℓ) :
    (cachedCompile ℓ d₁ d₂).workCalls = 2 ^ ℓ ∧
    (cachedCompile ℓ d₁ d₂).firstCalls = 2 ^ ℓ / 2 ^ d₁ ∧
    (cachedCompile ℓ d₁ d₂).secondCalls = 2 ^ ℓ / 2 ^ d₂ := by
  have hw := cachedPrefix_workCalls ℓ d₁ d₂ (2 ^ ℓ)
  have hf := cachedPrefix_firstCalls ℓ d₁ d₂ (2 ^ ℓ)
  have hs := cachedPrefix_secondCalls ℓ d₁ d₂ (2 ^ ℓ)
  rw [scheduledCount_eq_div (by positivity) (pow_dvd_pow 2 h₁)] at hf
  rw [scheduledCount_eq_div (by positivity) (pow_dvd_pow 2 h₂)] at hs
  simpa [cachedCompile, CachedCircuit.workCalls, CachedCircuit.firstCalls,
    CachedCircuit.secondCalls, CachedInstruction.workCost, CachedInstruction.firstCost,
    CachedInstruction.secondCost] using And.intro hw (And.intro hf hs)

/-- At most `66K+6ℓ` actual reversible primitives, including exact cache initialization/cleanup. -/
theorem cachedCompile_primitive_bound (ℓ d₁ d₂ : ℕ) :
    (cachedCompile ℓ d₁ d₂).primitiveGates ≤ 66 * 2 ^ ℓ + 6 * ℓ := by
  have hp := cachePrepareProgram_length ℓ
  have hu := cacheUnprepareProgram_length ℓ
  have hb : (cachedPrefix ℓ d₁ d₂ (2 ^ ℓ)).primitiveGates ≤ 66 * 2 ^ ℓ := by
    rw [cachedPrefix_primitiveGates]
    exact sum_reservoirUpdate_length ℓ d₁ d₂
  simp only [cachedCompile, CachedCircuit.primitiveGates, List.map_append, List.sum_append,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, CachedInstruction.primitiveCost,
    add_zero]
  change (cachePrepareProgram ℓ).length + (cachedPrefix ℓ d₁ d₂ (2 ^ ℓ)).primitiveGates +
    (cacheUnprepareProgram ℓ).length ≤ _
  omega

end OptimalQLS.TransducerCompiler
