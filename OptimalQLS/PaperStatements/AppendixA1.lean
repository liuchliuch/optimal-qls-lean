import OptimalQLS.TransducerCompiler.BJYTheorem
import OptimalQLS.TransducerCompiler.CompleteTheorems
import OptimalQLS.TransducerCompiler.Physical.Resources

/-! # Appendix A.1: real clock and control gates

The controlled work unitary and the two complete input unitaries are supplied
primitives, as in the source statement.  One concrete word, chosen before those
unitaries and every catalyst, has all the claimed properties.  The zero-clock
case is included.  Cleanup concerns the comparator and synthesis work bits;
the live clock is retained in the finite unitary and is only approximately zero.
-/

noncomputable section
set_option synthInstance.maxSize 32768
set_option maxHeartbeats 1000000
set_option maxRecDepth 8192
open scoped Classical
namespace OptimalQLS.PaperStatements
open Matrix TransducerCompiler TransducerCompiler.BinaryClock

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Source Appendix A.1, including the BJY implementation's unrelaxed error
formula.  Every dyadic budget is allowed, including `K = K₁ = K₂ = 1`.
The elementary leaves have arity at most two; each clock layer is the literal
`ℓ`-gate one-qubit Hadamard circuit. -/
theorem appendixA1 (ℓ k₁ k₂ : ℕ) (h₁ : k₁ ≤ ℓ) (h₂ : k₂ ≤ ℓ) :
    ∃ c : SynthCircuit ℓ,
      c = synthesize (cachedCompile ℓ (ℓ-k₁) (ℓ-k₂)) ∧
      c.workCalls = 2^ℓ ∧ c.firstCalls = 2^k₁ ∧ c.secondCalls = 2^k₂ ∧
      c.auxGates ≤ 1110 * 2^ℓ ∧
      Fintype.card (SynthSpace n ℓ) = Fintype.card n * 2^(2*ℓ+3) ∧
      (HadamardClock.circuit ℓ).gateCount = ℓ ∧
      (∀ g : GateSynthesis.LowerGate (LabelWire ℓ),
        SynthInstruction.elementary g ∈ c → g.arity ≤ 2) ∧
      (∀ (S : Matrix.unitaryGroup (Base n) ℂ) (U₁ U₂ : Matrix.unitaryGroup n ℂ),
        (∀ g ∈ c, g.isAuxiliary = true →
          ∀ i j : SynthSpace n ℓ, ((g.eval S U₁ U₂).val i j).im = 0) ∧
        (∀ v : BitSpace n ℓ → ℂ,
          (c.eval S U₁ U₂).val *ᵥ synthClean (cleanVector v) =
            synthClean (cleanVector
              ((toBitUnitary (hadamardFiniteUnitary (dyadicLayout ℓ k₁ k₂ h₁ h₂)
                S U₁ U₂)).val *ᵥ v))) ∧
        ∀ ξ τ v₀ v₁ v₂ : n → ℂ,
          S.val *ᵥ bundle ξ v₀ (U₁.val *ᵥ v₁) (U₂.val *ᵥ v₂) = bundle τ v₀ v₁ v₂ →
          ‖WithLp.toLp 2 ((c.eval S U₁ U₂).val *ᵥ
            synthInput (dyadicLayout ℓ k₁ k₂ h₁ h₂) ξ -
            synthInput (dyadicLayout ℓ k₁ k₂ h₁ h₂) τ)‖ ≤
            2 / Real.sqrt ((2^ℓ : ℕ) : ℝ) *
              Real.sqrt (‖WithLp.toLp 2 (bundle (0 : n → ℂ) v₀ v₁ v₂)‖^2 +
                ((2 : ℝ)^ℓ / (2 : ℝ)^k₁ - 1) * ‖WithLp.toLp 2 v₁‖^2 +
                ((2 : ℝ)^ℓ / (2 : ℝ)^k₂ - 1) * ‖WithLp.toLp 2 v₂‖^2)) := by
  let b := dyadicLayout ℓ k₁ k₂ h₁ h₂
  have hd₁ : b.D₁ = 2^(ℓ-k₁) := two_pow_div_two_pow h₁
  have hd₂ : b.D₂ = 2^(ℓ-k₂) := two_pow_div_two_pow h₂
  let c := synthesize (cachedCompile ℓ (ℓ-k₁) (ℓ-k₂))
  have hc := complete_exact_counts b (ℓ-k₁) (ℓ-k₂) hd₁ hd₂
  have ho := compile_exact_counts b
  have hx := Layout.ofBudgets_exact_counts (show 0 < 2^ℓ by positivity) (2^k₁) (2^k₂)
    (by positivity) (by positivity) (pow_dvd_pow 2 h₁) (pow_dvd_pow 2 h₂)
  refine ⟨c,rfl,hc.1,hc.2.1.trans (ho.2.1.symm.trans hx.2.1),
    hc.2.2.trans (ho.2.2.symm.trans hx.2.2),synthesized_aux_bound _ _ _,?_,
    HadamardClock.circuit_gateCount ℓ,?_,?_⟩
  · simpa only [auxiliaryQubits] using (synthSpace_card (n := n) ℓ)
  · intro g _
    exact GateSynthesis.LowerGate.arity_le_two g
  intro S U₁ U₂
  refine ⟨?_,?_,?_⟩
  · intro g _ hg i j
    exact auxiliary_real g hg S U₁ U₂ i j
  · intro v
    exact complete_cleanup b (ℓ-k₁) (ℓ-k₂) hd₁ hd₂ S U₁ U₂ v
  intro ξ τ v₀ v₁ v₂ hS
  have he := complete_error b (ℓ-k₁) (ℓ-k₂) hd₁ hd₂ S U₁ U₂ ξ τ v₀ v₁ v₂ hS
  have hr₁ : (b.D₁ : ℝ) = (2 : ℝ)^ℓ / (2 : ℝ)^k₁ := by
    change ((2^ℓ / 2^k₁ : ℕ) : ℝ) = _
    rw [Nat.cast_div_charZero (pow_dvd_pow 2 h₁)]
    simp
  have hr₂ : (b.D₂ : ℝ) = (2 : ℝ)^ℓ / (2 : ℝ)^k₂ := by
    change ((2^ℓ / 2^k₂ : ℕ) : ℝ) = _
    rw [Nat.cast_div_charZero (pow_dvd_pow 2 h₂)]
    simp
  rw [hr₁,hr₂] at he
  rw [private_bundle_norm_sq,← energy_eq_norm_sq,← energy_eq_norm_sq]
  have halg : energy v₀ + energy v₁ + energy v₂ +
      ((2 : ℝ)^ℓ / (2 : ℝ)^k₁ - 1) * energy v₁ +
      ((2 : ℝ)^ℓ / (2 : ℝ)^k₂ - 1) * energy v₂ =
      energy v₀ + (2 : ℝ)^ℓ / (2 : ℝ)^k₁ * energy v₁ +
        (2 : ℝ)^ℓ / (2 : ℝ)^k₂ * energy v₂ := by ring
  rw [halg]
  exact he


/-! The query labels in `SynthInstruction` are two-bit masks.  The following
all-clock-width adapter expands them to one physical control flag, with real
local compute/uncompute gates.  Controlled work remains an expressly exempt
supplied primitive, so no positive-clock hypothesis is introduced. -/
namespace AppendixA1
open PolynomialTransform PolynomialTransform.DirtyAncilla
open Preparation.CompilerAttachment Refinement.CostedExecution

inductive Gate (ℓ : ℕ) where
  | work
  | auxiliary (g : PhaseGate (LabelWire ℓ))
  | query (g : PhaseGate OracleLocalWire)

abbrev Circuit (m ℓ : ℕ) :=
  NamedCircuit (Gate ℓ) (Bits m) (Bits m) (Physical.Space m ℓ)

def gateEval (m ℓ : ℕ) (S : Matrix.unitaryGroup (Base (Bits m)) ℂ) :
    Gate ℓ → Matrix.unitaryGroup (Physical.Space m ℓ) ℂ
  | .work => Physical.padded m ℓ (padHom (cachedWork S))
  | .auxiliary g => Physical.auxGateEval m ℓ g
  | .query g => Physical.queryGateEval m ℓ g

def instruction (m ℓ : ℕ) : SynthInstruction ℓ → Circuit m ℓ
  | .query₁ => mapNamed Gate.query (Physical.queryCode m ℓ .first false)
  | .query₂ => mapNamed Gate.query (Physical.queryCode m ℓ .second true)
  | .work => [.gate .work]
  | .elementary g => mapNamed Gate.auxiliary (Physical.auxCode m ℓ [.real g])
  | .clock _ => mapNamed Gate.auxiliary (Physical.auxCode m ℓ (ClockGates.labelCode ℓ))

def compile (m ℓ : ℕ) (c : SynthCircuit ℓ) : Circuit m ℓ :=
  macroCompile (instruction m ℓ) c

/-- Count exactly the emitted elementary leaves, excluding supplied work calls. -/
def extraGates {m ℓ : ℕ} : Circuit m ℓ → ℕ
  | [] => 0
  | .gate .work :: c => extraGates c
  | .gate _ :: c => extraGates c + 1
  | _ :: c => extraGates c

theorem extraGates_le_workGates {m ℓ : ℕ} (c : Circuit m ℓ) :
    extraGates c ≤ c.workGates := by
  induction c with
  | nil => exact Nat.le_refl 0
  | cons i c ih =>
    cases i with
    | gate g => cases g <;> simp_all [extraGates,NamedCircuit.workGates] <;> omega
    | matrixCall p adj => exact ih
    | vectorCall p adj => exact ih

theorem instruction_counts (m ℓ : ℕ) (S : Matrix.unitaryGroup (Base (Bits m)) ℂ)
    (g : SynthInstruction ℓ) :
    ((instruction m ℓ g).toQuery (gateEval m ℓ S)).matrixQueries = g.firstCost ∧
    ((instruction m ℓ g).toQuery (gateEval m ℓ S)).vectorQueries = g.secondCost ∧
    (instruction m ℓ g).workGates ≤ instructionGateBudget 1 2400 2400 g := by
  cases g with
  | query₁ =>
    rw [instruction,mapNamed_toQuery Gate.query (Physical.queryGateEval m ℓ)
      (gateEval m ℓ S) (fun _ => rfl),mapNamed_workGates]
    exact Physical.queryCode_counts m ℓ .first false
  | query₂ =>
    rw [instruction,mapNamed_toQuery Gate.query (Physical.queryGateEval m ℓ)
      (gateEval m ℓ S) (fun _ => rfl),mapNamed_workGates]
    exact Physical.queryCode_counts m ℓ .second true
  | work => exact ⟨rfl,rfl,Nat.le_refl 1⟩
  | elementary g =>
    rw [instruction,mapNamed_toQuery Gate.auxiliary (Physical.auxGateEval m ℓ)
      (gateEval m ℓ S) (fun _ => rfl),mapNamed_workGates]
    have h := Physical.auxCode_counts m ℓ [.real g]
    exact ⟨h.1,h.2.1,h.2.2.le⟩
  | clock adj =>
    rw [instruction,mapNamed_toQuery Gate.auxiliary (Physical.auxGateEval m ℓ)
      (gateEval m ℓ S) (fun _ => rfl),mapNamed_workGates]
    have h := Physical.auxCode_counts m ℓ (ClockGates.labelCode ℓ)
    exact ⟨h.1,h.2.1,by simpa only [ClockGates.labelCode,ClockGates.code_length,
      instructionGateBudget] using h.2.2.le⟩

theorem compile_counts (m ℓ : ℕ) (S : Matrix.unitaryGroup (Base (Bits m)) ℂ)
    (c : SynthCircuit ℓ) :
    ((compile m ℓ c).toQuery (gateEval m ℓ S)).matrixQueries = c.firstCalls ∧
    ((compile m ℓ c).toQuery (gateEval m ℓ S)).vectorQueries = c.secondCalls ∧
    (compile m ℓ c).workGates ≤ c.auxGates+c.workCalls+2400*c.firstCalls+2400*c.secondCalls := by
  simpa only [one_mul] using Physical.macroCompile_single_counts (gateEval m ℓ S)
    (instruction m ℓ) 1 2400 2400 (instruction_counts m ℓ S) c

theorem instruction_intertwines (m ℓ : ℕ) (S : Matrix.unitaryGroup (Base (Bits m)) ℂ)
    (g : SynthInstruction ℓ) (U₁ U₂ : Matrix.unitaryGroup (Bits m) ℂ) :
    (((instruction m ℓ g).toQuery (gateEval m ℓ S)).eval U₁ U₂).val *
        basisInsertion (Physical.clean m ℓ) =
      basisInsertion (Physical.clean m ℓ) * (g.eval S U₁ U₂).val := by
  cases g with
  | query₁ =>
    rw [instruction,mapNamed_toQuery Gate.query (Physical.queryGateEval m ℓ)
      (gateEval m ℓ S) (fun _ => rfl)]
    exact Physical.queryCode_intertwines m ℓ .first false U₁ U₂
  | query₂ =>
    rw [instruction,mapNamed_toQuery Gate.query (Physical.queryGateEval m ℓ)
      (gateEval m ℓ S) (fun _ => rfl)]
    exact Physical.queryCode_intertwines m ℓ .second true U₁ U₂
  | work =>
    simpa only [instruction,NamedCircuit.toQuery,List.map_cons,List.map_nil,
      NamedInstruction.toQuery,QueryCircuit.eval,QueryInstruction.eval,one_mul,
      gateEval,SynthInstruction.eval] using
      Physical.padded_clean m ℓ (padHom (cachedWork S))
  | elementary g =>
    rw [instruction,mapNamed_toQuery Gate.auxiliary (Physical.auxGateEval m ℓ)
      (gateEval m ℓ S) (fun _ => rfl)]
    simpa only [phaseEval,one_mul,PhaseGate.eval] using
      Physical.auxCode_intertwines m ℓ [.real g] U₁ U₂
  | clock adj =>
    rw [instruction,mapNamed_toQuery Gate.auxiliary (Physical.auxGateEval m ℓ)
      (gateEval m ℓ S) (fun _ => rfl)]
    exact Physical.clock_intertwines m ℓ adj S U₁ U₂

theorem compile_intertwines (m ℓ : ℕ) (S : Matrix.unitaryGroup (Base (Bits m)) ℂ)
    (c : SynthCircuit ℓ) (U₁ U₂ : Matrix.unitaryGroup (Bits m) ℂ) :
    (((compile m ℓ c).toQuery (gateEval m ℓ S)).eval U₁ U₂).val *
        basisInsertion (Physical.clean m ℓ) =
      basisInsertion (Physical.clean m ℓ) * (c.eval S U₁ U₂).val :=
  macroCompile_intertwines (gateEval m ℓ S) (instruction m ℓ) S id id
    (basisInsertion (Physical.clean m ℓ)) (instruction_intertwines m ℓ S) c U₁ U₂

def Gate.RealAuxiliary {ℓ : ℕ} : Gate ℓ → Prop
  | .work => True
  | .auxiliary g => GraphEncoding.RealPhaseGate g
  | .query g => GraphEncoding.RealPhaseGate g

theorem instruction_safe (m ℓ : ℕ) (g : SynthInstruction ℓ) :
    safeCircuit Gate.RealAuxiliary (Physical.singleFlagPort m ℓ) (Physical.singleFlagPort m ℓ)
      (instruction m ℓ g) := by
  cases g with
  | query₁ =>
    exact safeCircuit_map _ _ _ _ Gate.query (fun _ h => h) _
      (Physical.queryCode_safe m ℓ .first false)
  | query₂ =>
    exact safeCircuit_map _ _ _ _ Gate.query (fun _ h => h) _
      (Physical.queryCode_safe m ℓ .second true)
  | work =>
    intro i hi
    simp only [instruction,List.mem_singleton] at hi
    subst i
    trivial
  | elementary g =>
    apply safeCircuit_map GraphEncoding.RealPhaseGate Gate.RealAuxiliary _ _ Gate.auxiliary (fun _ h => h)
    apply gates_only_safe
    intro k hk
    simp only [List.mem_singleton] at hk
    subst k
    exact GraphEncoding.realPhaseGate_real g
  | clock adj =>
    apply safeCircuit_map GraphEncoding.RealPhaseGate Gate.RealAuxiliary _ _ Gate.auxiliary (fun _ h => h)
    exact gates_only_safe _ _ _ _ (ClockGates.code_real _)

theorem compile_safe (m ℓ : ℕ) (c : SynthCircuit ℓ) :
    safeCircuit Gate.RealAuxiliary (Physical.singleFlagPort m ℓ) (Physical.singleFlagPort m ℓ)
      (compile m ℓ c) := by
  intro i hi
  obtain ⟨g,_,hi⟩ := List.mem_flatMap.mp hi
  exact instruction_safe m ℓ g i hi

theorem gate_local_real (m ℓ : ℕ) (S : Matrix.unitaryGroup (Base (Bits m)) ℂ)
    (g : Gate ℓ) (hg : g ≠ .work) (hr : g.RealAuxiliary) :
    IsTwoLocal (Physical.coordinates m ℓ) (gateEval m ℓ S g) ∧
      ∀ i j, ((gateEval m ℓ S g).val i j).im = 0 := by
  cases g with
  | work => exact False.elim (hg rfl)
  | auxiliary g => exact ⟨Physical.aux_gate_local m ℓ g,Physical.auxiliary_gate_real m ℓ g hr⟩
  | query g => exact ⟨Physical.query_gate_local m ℓ g,Physical.query_gate_real m ℓ g hr⟩

theorem compile_apply (m ℓ : ℕ) (S : Matrix.unitaryGroup (Base (Bits m)) ℂ)
    (c : SynthCircuit ℓ) (U₁ U₂ : Matrix.unitaryGroup (Bits m) ℂ)
    (v : SynthSpace (Bits m) ℓ → ℂ) :
    (((compile m ℓ c).toQuery (gateEval m ℓ S)).eval U₁ U₂).val *ᵥ Physical.cleanVector m ℓ v =
      Physical.cleanVector m ℓ ((c.eval S U₁ U₂).val *ᵥ v) := by
  have he := congrArg (fun M => M *ᵥ v) (compile_intertwines m ℓ S c U₁ U₂)
  simpa only [Matrix.mulVec_mulVec,Physical.cleanVector] using he

theorem compile_error_eq (m ℓ : ℕ) (S : Matrix.unitaryGroup (Base (Bits m)) ℂ)
    (c : SynthCircuit ℓ) (U₁ U₂ : Matrix.unitaryGroup (Bits m) ℂ)
    (v w : SynthSpace (Bits m) ℓ → ℂ) :
    ‖WithLp.toLp 2 ((((compile m ℓ c).toQuery (gateEval m ℓ S)).eval U₁ U₂).val *ᵥ
      Physical.cleanVector m ℓ v - Physical.cleanVector m ℓ w)‖ =
      ‖WithLp.toLp 2 ((c.eval S U₁ U₂).val *ᵥ v-w)‖ := by
  rw [compile_apply]
  have he : Physical.cleanVector m ℓ ((c.eval S U₁ U₂).val *ᵥ v) - Physical.cleanVector m ℓ w =
      Physical.cleanVector m ℓ ((c.eval S U₁ U₂).val *ᵥ v-w) := by
    unfold Physical.cleanVector
    rw [Matrix.mulVec_sub]
  rw [he,Physical.cleanVector_norm]

end AppendixA1

/-- Strongest operational A.1 endpoint.  The same dyadic word is literally
expanded to strict single-flag queries and real two-local extra gates, on every
clock width including zero.  The only exempt constructor is the supplied
controlled work primitive.  The extra-gate bound harmlessly overcounts its
`K` occurrences, and includes both `2400 Kᵢ` query-adapter costs. -/
theorem appendixA1_strict (m ℓ k₁ k₂ : ℕ) (h₁ : k₁ ≤ ℓ) (h₂ : k₂ ≤ ℓ) :
    ∃ (c : SynthCircuit ℓ) (out : AppendixA1.Circuit m ℓ),
      c = synthesize (cachedCompile ℓ (ℓ-k₁) (ℓ-k₂)) ∧
      out = AppendixA1.compile m ℓ c ∧ c.workCalls = 2^ℓ ∧
      AppendixA1.extraGates out ≤ 1111*2^ℓ+2400*2^k₁+2400*2^k₂ ∧
      Fintype.card (Physical.Space m ℓ) = 2^(m+2*ℓ+6) ∧
      (∀ p adj, PolynomialTransform.NamedInstruction.matrixCall p adj ∈ out →
        p = Physical.singleFlagPort m ℓ ∧
        Nonempty (Refinement.CostedExecution.LiteralQueryPlacement (Equiv.refl (Bits m))
          (Physical.coordinates m ℓ) p)) ∧
      (∀ p adj, PolynomialTransform.NamedInstruction.vectorCall p adj ∈ out →
        p = Physical.singleFlagPort m ℓ ∧
        Nonempty (Refinement.CostedExecution.LiteralQueryPlacement (Equiv.refl (Bits m))
          (Physical.coordinates m ℓ) p)) ∧
      ∀ S : Matrix.unitaryGroup (Base (Bits m)) ℂ,
        (out.toQuery (AppendixA1.gateEval m ℓ S)).matrixQueries = 2^k₁ ∧
        (out.toQuery (AppendixA1.gateEval m ℓ S)).vectorQueries = 2^k₂ ∧
        (∀ g, PolynomialTransform.NamedInstruction.gate g ∈ out → g ≠ .work →
          Refinement.CostedExecution.IsTwoLocal (Physical.coordinates m ℓ) (AppendixA1.gateEval m ℓ S g) ∧
          ∀ i j, ((AppendixA1.gateEval m ℓ S g).val i j).im = 0) ∧
        ∀ U₁ U₂ : Matrix.unitaryGroup (Bits m) ℂ,
          ((out.toQuery (AppendixA1.gateEval m ℓ S)).eval U₁ U₂).val *
              PolynomialTransform.basisInsertion (Physical.clean m ℓ) =
            PolynomialTransform.basisInsertion (Physical.clean m ℓ) * (c.eval S U₁ U₂).val ∧
          (∀ v : BitSpace (Bits m) ℓ → ℂ,
            ((out.toQuery (AppendixA1.gateEval m ℓ S)).eval U₁ U₂).val *ᵥ
                Physical.cleanVector m ℓ (synthClean (cleanVector v)) =
              Physical.cleanVector m ℓ (synthClean (cleanVector
                ((toBitUnitary (hadamardFiniteUnitary (dyadicLayout ℓ k₁ k₂ h₁ h₂) S U₁ U₂)).val *ᵥ v)))) ∧
          ∀ ξ τ v₀ v₁ v₂ : Bits m → ℂ,
            S.val *ᵥ bundle ξ v₀ (U₁.val *ᵥ v₁) (U₂.val *ᵥ v₂) = bundle τ v₀ v₁ v₂ →
            ‖WithLp.toLp 2
              (((out.toQuery (AppendixA1.gateEval m ℓ S)).eval U₁ U₂).val *ᵥ
                Physical.cleanVector m ℓ (synthInput (dyadicLayout ℓ k₁ k₂ h₁ h₂) ξ) -
                Physical.cleanVector m ℓ (synthInput (dyadicLayout ℓ k₁ k₂ h₁ h₂) τ))‖ ≤
              2 / Real.sqrt ((2^ℓ : ℕ) : ℝ) *
                Real.sqrt (‖WithLp.toLp 2 (bundle (0 : Bits m → ℂ) v₀ v₁ v₂)‖^2 +
                  ((2 : ℝ)^ℓ / (2 : ℝ)^k₁-1) * ‖WithLp.toLp 2 v₁‖^2 +
                  ((2 : ℝ)^ℓ / (2 : ℝ)^k₂-1) * ‖WithLp.toLp 2 v₂‖^2) := by
  obtain ⟨c,hc,hw,hf,hs,ha,_,_,_,he⟩ := appendixA1 (n := Bits m) ℓ k₁ k₂ h₁ h₂
  let out := AppendixA1.compile m ℓ c
  have hsafe := AppendixA1.compile_safe m ℓ c
  have hg := (AppendixA1.extraGates_le_workGates out).trans
    (AppendixA1.compile_counts m ℓ 1 c).2.2
  rw [hw,hf,hs] at hg
  have hg' : AppendixA1.extraGates out ≤ 1111*2^ℓ+2400*2^k₁+2400*2^k₂ := by omega
  refine ⟨c,out,hc,rfl,hw,hg',Physical.space_card m ℓ,?_,?_,?_⟩
  · intro p adj hp
    have he := hsafe (.matrixCall p adj) hp
    change p = Physical.singleFlagPort m ℓ at he
    refine ⟨he,?_⟩
    rw [he]
    exact ⟨Physical.queryPlacement m ℓ⟩
  · intro p adj hp
    have he := hsafe (.vectorCall p adj) hp
    change p = Physical.singleFlagPort m ℓ at he
    refine ⟨he,?_⟩
    rw [he]
    exact ⟨Physical.queryPlacement m ℓ⟩
  intro S
  have hcount := AppendixA1.compile_counts m ℓ S c
  refine ⟨hcount.1.trans hf,hcount.2.1.trans hs,?_,?_⟩
  · intro g hg hwork
    exact AppendixA1.gate_local_real m ℓ S g hwork (hsafe (.gate g) hg)
  intro U₁ U₂
  refine ⟨AppendixA1.compile_intertwines m ℓ S c U₁ U₂,?_,?_⟩
  · intro v
    rw [AppendixA1.compile_apply,(he S U₁ U₂).2.1 v]
  · intro ξ τ v₀ v₁ v₂ hS
    rw [AppendixA1.compile_error_eq]
    exact (he S U₁ U₂).2.2 ξ τ v₀ v₁ v₂ hS

end OptimalQLS.PaperStatements
