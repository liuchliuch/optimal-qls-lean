import OptimalQLS.TransducerCompiler.LoweredCircuit

noncomputable section
namespace OptimalQLS.TransducerCompiler
open BinaryClock
variable {ℓ : ℕ}

def SynthInstruction.workCost : SynthInstruction ℓ → ℕ
  | .work => 1
  | _ => 0

def SynthInstruction.firstCost : SynthInstruction ℓ → ℕ
  | .query₁ => 1
  | _ => 0

def SynthInstruction.secondCost : SynthInstruction ℓ → ℕ
  | .query₂ => 1
  | _ => 0

/-- Count actual lower auxiliary gates and leaves of the explicit Hadamard circuits. -/
def SynthInstruction.auxCost : SynthInstruction ℓ → ℕ
  | .elementary _ => 1
  | .clock _ => (HadamardClock.circuit ℓ).gateCount
  | _ => 0

def SynthCircuit.workCalls (c : SynthCircuit ℓ) : ℕ := (c.map SynthInstruction.workCost).sum
def SynthCircuit.firstCalls (c : SynthCircuit ℓ) : ℕ := (c.map SynthInstruction.firstCost).sum
def SynthCircuit.secondCalls (c : SynthCircuit ℓ) : ℕ := (c.map SynthInstruction.secondCost).sum
def SynthCircuit.auxGates (c : SynthCircuit ℓ) : ℕ := (c.map SynthInstruction.auxCost).sum

theorem lowerInstruction_counts (g : CachedInstruction ℓ) :
    (lowerInstruction g).workCalls = g.workCost ∧
    (lowerInstruction g).firstCalls = g.firstCost ∧
    (lowerInstruction g).secondCalls = g.secondCost ∧
    (lowerInstruction g).auxGates ≤ 15 * g.primitiveCost := by
  cases g with
  | query₁ => simp [lowerInstruction, SynthCircuit.workCalls, SynthCircuit.firstCalls,
      SynthCircuit.secondCalls, SynthCircuit.auxGates, SynthInstruction.workCost,
      SynthInstruction.firstCost, SynthInstruction.secondCost, SynthInstruction.auxCost,
      CachedInstruction.workCost, CachedInstruction.firstCost, CachedInstruction.secondCost,
      CachedInstruction.primitiveCost]
  | query₂ => simp [lowerInstruction, SynthCircuit.workCalls, SynthCircuit.firstCalls,
      SynthCircuit.secondCalls, SynthCircuit.auxGates, SynthInstruction.workCost,
      SynthInstruction.firstCost, SynthInstruction.secondCost, SynthInstruction.auxCost,
      CachedInstruction.workCost, CachedInstruction.firstCost, CachedInstruction.secondCost,
      CachedInstruction.primitiveCost]
  | work => simp [lowerInstruction, SynthCircuit.workCalls, SynthCircuit.firstCalls,
      SynthCircuit.secondCalls, SynthCircuit.auxGates, SynthInstruction.workCost,
      SynthInstruction.firstCost, SynthInstruction.secondCost, SynthInstruction.auxCost,
      CachedInstruction.workCost, CachedInstruction.firstCost, CachedInstruction.secondCost,
      CachedInstruction.primitiveCost]
  | classical p =>
    simpa [lowerInstruction, SynthCircuit.workCalls, SynthCircuit.firstCalls,
      SynthCircuit.secondCalls, SynthCircuit.auxGates, SynthInstruction.workCost,
      SynthInstruction.firstCost, SynthInstruction.secondCost, SynthInstruction.auxCost,
      CachedInstruction.workCost, CachedInstruction.firstCost, CachedInstruction.secondCost,
      CachedInstruction.primitiveCost, List.map_map, Function.comp_def] using
      GateSynthesis.lowerProgram_length p

theorem lowerCached_counts (c : CachedCircuit ℓ) :
    (lowerCached c).workCalls = c.workCalls ∧
    (lowerCached c).firstCalls = c.firstCalls ∧
    (lowerCached c).secondCalls = c.secondCalls ∧
    (lowerCached c).auxGates ≤ 15 * c.primitiveGates := by
  induction c with
  | nil => simp [lowerCached, SynthCircuit.workCalls, SynthCircuit.firstCalls,
      SynthCircuit.secondCalls, SynthCircuit.auxGates, CachedCircuit.workCalls,
      CachedCircuit.firstCalls, CachedCircuit.secondCalls, CachedCircuit.primitiveGates]
  | cons g gs ih =>
    have hg := lowerInstruction_counts g
    have hdefs : lowerCached (g::gs) = lowerInstruction g ++ lowerCached gs := rfl
    simp only [hdefs, SynthCircuit.workCalls, SynthCircuit.firstCalls, SynthCircuit.secondCalls,
      SynthCircuit.auxGates, CachedCircuit.workCalls, CachedCircuit.firstCalls,
      CachedCircuit.secondCalls, CachedCircuit.primitiveGates, List.map_append,
      List.sum_append, List.map_cons, List.sum_cons] at *
    omega

/-- Complete synthesis preserves all independent black-box counts. -/
theorem synthesize_counts (c : CachedCircuit ℓ) :
    (synthesize c).workCalls = c.workCalls ∧
    (synthesize c).firstCalls = c.firstCalls ∧
    (synthesize c).secondCalls = c.secondCalls ∧
    (synthesize c).auxGates ≤ 15 * (c.primitiveGates + 2 * ℓ) := by
  have h := lowerCached_counts c
  simp only [synthesize, SynthCircuit.workCalls, SynthCircuit.firstCalls, SynthCircuit.secondCalls,
    SynthCircuit.auxGates, List.map_append, List.sum_append, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, SynthInstruction.workCost, SynthInstruction.firstCost,
    SynthInstruction.secondCost, SynthInstruction.auxCost, HadamardClock.circuit_gateCount,
    zero_add, add_zero] at *
  omega

/-- Linear real one- and two-qubit auxiliary-gate overhead, with no hidden logarithm. -/
theorem synthesized_aux_bound (ℓ d₁ d₂ : ℕ) :
    (synthesize (cachedCompile ℓ d₁ d₂)).auxGates ≤ 1110 * 2^ℓ := by
  have hs := (synthesize_counts (cachedCompile ℓ d₁ d₂)).2.2.2
  have hp := cachedFinite_primitive_bound ℓ d₁ d₂
  rw [HadamardClock.circuit_gateCount] at hp
  omega

/-- Replacing every controlled work call by a g-gate work circuit has explicit linear cost. -/
def SynthCircuit.chargedGates (c : SynthCircuit ℓ) (g : ℕ) : ℕ := c.auxGates + c.workCalls * g

theorem synthesized_work_gate_bound (ℓ d₁ d₂ g : ℕ) :
    (synthesize (cachedCompile ℓ d₁ d₂)).chargedGates g ≤ (1110 + g) * 2^ℓ := by
  have ha := synthesized_aux_bound ℓ d₁ d₂
  have hw : (cachedCompile ℓ d₁ d₂).workCalls = 2^ℓ := by
    simpa [cachedCompile, CachedCircuit.workCalls, CachedInstruction.workCost] using
      cachedPrefix_workCalls ℓ d₁ d₂ (2^ℓ)
  have hs := (synthesize_counts (cachedCompile ℓ d₁ d₂)).1
  simp only [SynthCircuit.chargedGates, hs, hw]
  nlinarith

end OptimalQLS.TransducerCompiler
