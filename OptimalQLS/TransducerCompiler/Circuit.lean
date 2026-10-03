import OptimalQLS.TransducerCompiler.Reservoir
import OptimalQLS.TransducerCompiler.QueryCounts
import OptimalQLS.TransducerCompiler.ClockUnitary

noncomputable section
namespace OptimalQLS.TransducerCompiler
open Matrix

/-- Structural budgets. These are arithmetic facts, not error or compiler certificates. -/
structure Layout (K : ℕ) where
  positive : 0 < K
  D₁ : ℕ
  D₂ : ℕ
  positive₁ : 0 < D₁
  positive₂ : 0 < D₂
  le₁ : D₁ ≤ K
  le₂ : D₂ ≤ K
  divides₁ : D₁ ∣ K
  divides₂ : D₂ ∣ K

def Layout.zero {K : ℕ} (b : Layout K) : Fin K := ⟨0,b.positive⟩
def Layout.time {K : ℕ} (b : Layout K) (t : ℕ) : Fin K :=
  ⟨t % K,Nat.mod_lt _ b.positive⟩

/-- A finite two-oracle program. The work instruction expands into two real
routing permutations and one clock-controlled call to S. -/
inductive Instruction where
  | query₁ | query₂ | work (t : ℕ) | clock (adjoint : Bool)
  deriving DecidableEq

abbrev Circuit := List Instruction

variable {n : Type*} [Fintype n] [DecidableEq n] {K : ℕ}

def Instruction.eval (b : Layout K) (S : Matrix.unitaryGroup (Base n) ℂ)
    (U₁ U₂ : Matrix.unitaryGroup n ℂ) : Instruction → Matrix.unitaryGroup (Space n K) ℂ
  | .query₁ => query .first U₁
  | .query₂ => query .second U₂
  | .clock adj => if adj then (clockLift (clockPrepare b.zero))⁻¹ else
      clockLift (clockPrepare b.zero)
  | .work t => routedWork b.zero
      (address b.zero b.D₁ b.D₂ (b.time t) b.positive₁ b.positive₂ b.le₁ b.le₂) S

def Circuit.eval (b : Layout K) (S : Matrix.unitaryGroup (Base n) ℂ)
    (U₁ U₂ : Matrix.unitaryGroup n ℂ) : Circuit → Matrix.unitaryGroup (Space n K) ℂ
  | [] => 1
  | g :: gs => Circuit.eval b S U₁ U₂ gs * g.eval b S U₁ U₂

theorem Circuit.eval_append (b : Layout K) (S : Matrix.unitaryGroup (Base n) ℂ)
    (U₁ U₂ : Matrix.unitaryGroup n ℂ) (c d : Circuit) :
    (c ++ d).eval b S U₁ U₂ = d.eval b S U₁ U₂ * c.eval b S U₁ U₂ := by
  induction c with
  | nil => simp [eval]
  | cons g gs ih => simp [eval, ih, mul_assoc]

def round (b : Layout K) (t : ℕ) : Circuit :=
  (if t % b.D₁ = 0 then [.query₁] else []) ++
  (if t % b.D₂ = 0 then [.query₂] else []) ++ [.work t]

/-- Prefix of the program; its definition has no vector or catalyst argument. -/
def compilePrefix (b : Layout K) : ℕ → Circuit
  | 0 => []
  | t+1 => compilePrefix b t ++ round b t

def compile (b : Layout K) : Circuit := compilePrefix b K

theorem round_eval (b : Layout K) (S : Matrix.unitaryGroup (Base n) ℂ)
    (U₁ U₂ : Matrix.unitaryGroup n ℂ) (t : ℕ) :
    (round b t).eval b S U₁ U₂ =
      routedWork b.zero
        (address b.zero b.D₁ b.D₂ (b.time t) b.positive₁ b.positive₂ b.le₁ b.le₂) S *
      oracleStage b.D₁ b.D₂ t U₁ U₂ := by
  by_cases h₁ : t % b.D₁ = 0 <;> by_cases h₂ : t % b.D₂ = 0 <;>
    simp [round, h₁, h₂, Circuit.eval, Instruction.eval, oracleStage, mul_assoc]

/-- Exact catalyst-assisted invariant for every prefix of the finite circuit. -/
theorem prefix_invariant (b : Layout K) (S : Matrix.unitaryGroup (Base n) ℂ)
    (U₁ U₂ : Matrix.unitaryGroup n ℂ) (ξ τ v₀ v₁ v₂ : n → ℂ)
    (hS : S.val *ᵥ bundle ξ v₀ (U₁.val *ᵥ v₁) (U₂.val *ᵥ v₂) = bundle τ v₀ v₁ v₂)
    (t : ℕ) (ht : t ≤ K) :
    ((compilePrefix b t).eval b S U₁ U₂ : Matrix (Space n K) (Space n K) ℂ) *ᵥ
      state b.D₁ b.D₂ 0 ξ τ v₀ v₁ v₂ (U₁.val *ᵥ v₁) (U₂.val *ᵥ v₂) =
      state b.D₁ b.D₂ t ξ τ v₀ v₁ v₂ (U₁.val *ᵥ v₁) (U₂.val *ᵥ v₂) := by
  induction t with
  | zero => simp [compilePrefix, Circuit.eval]
  | succ t ih =>
    have hlt : t < K := by omega
    have htime : (b.time t).val = t := Nat.mod_eq_of_lt hlt
    rw [compilePrefix, Circuit.eval_append, Submonoid.coe_mul,
      ← Matrix.mulVec_mulVec, ih (by omega), round_eval, Submonoid.coe_mul,
      ← Matrix.mulVec_mulVec, oracleStage_apply]
    simpa only [htime] using
      work_step b.zero rfl b.D₁ b.D₂ (b.time t) b.positive₁ b.positive₂ b.le₁ b.le₂
        S ξ τ v₀ v₁ v₂ (U₁.val *ᵥ v₁) (U₂.val *ᵥ v₂) hS

/-- Syntactic work-call count. -/
def Instruction.workCost : Instruction → ℕ
  | .work _ => 1
  | _ => 0

def Instruction.firstCost : Instruction → ℕ
  | .query₁ => 1
  | _ => 0

def Instruction.secondCost : Instruction → ℕ
  | .query₂ => 1
  | _ => 0

def Circuit.workCalls (c : Circuit) : ℕ := (c.map Instruction.workCost).sum

def Circuit.firstCalls (c : Circuit) : ℕ := (c.map Instruction.firstCost).sum

def Circuit.secondCalls (c : Circuit) : ℕ := (c.map Instruction.secondCost).sum

theorem prefix_workCalls (b : Layout K) (t : ℕ) :
    (compilePrefix b t).workCalls = t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    by_cases h₁ : t % b.D₁ = 0 <;> by_cases h₂ : t % b.D₂ = 0 <;>
      simpa [compilePrefix, Circuit.workCalls, round, Instruction.workCost,
        h₁, h₂] using ih

theorem prefix_firstCalls (b : Layout K) (t : ℕ) :
    (compilePrefix b t).firstCalls = scheduledCount b.D₁ t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    by_cases h₁ : t % b.D₁ = 0 <;> by_cases h₂ : t % b.D₂ = 0 <;>
      simp_all [compilePrefix, Circuit.firstCalls, round, Instruction.firstCost,
        scheduledCount]

theorem prefix_secondCalls (b : Layout K) (t : ℕ) :
    (compilePrefix b t).secondCalls = scheduledCount b.D₂ t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    by_cases h₁ : t % b.D₁ = 0 <;> by_cases h₂ : t % b.D₂ = 0 <;>
      simp_all [compilePrefix, Circuit.secondCalls, round, Instruction.secondCost,
        scheduledCount]

/-- Exactly the advertised three independent black-box budgets. -/
theorem compile_exact_counts (b : Layout K) :
    (compile b).workCalls = K ∧
    (compile b).firstCalls = K / b.D₁ ∧
    (compile b).secondCalls = K / b.D₂ := by
  refine ⟨prefix_workCalls b K, ?_, ?_⟩
  · rw [compile, prefix_firstCalls]
    exact scheduledCount_eq_div b.positive₁ b.divides₁
  · rw [compile, prefix_secondCalls]
    exact scheduledCount_eq_div b.positive₂ b.divides₂

/-- The complete circuit, including real preparation and unpreparation. -/
def fullCompile (b : Layout K) : Circuit := [.clock false] ++ compile b ++ [.clock true]

theorem fullCompile_eval (b : Layout K) (S : Matrix.unitaryGroup (Base n) ℂ)
    (U₁ U₂ : Matrix.unitaryGroup n ℂ) :
    (fullCompile b).eval b S U₁ U₂ =
      (clockLift (clockPrepare b.zero))⁻¹ * (compile b).eval b S U₁ U₂ *
        clockLift (clockPrepare b.zero) := by
  simp [fullCompile, Circuit.eval_append, Circuit.eval, Instruction.eval, mul_assoc]

theorem fullCompile_counts (b : Layout K) :
    (fullCompile b).workCalls = (compile b).workCalls ∧
    (fullCompile b).firstCalls = (compile b).firstCalls ∧
    (fullCompile b).secondCalls = (compile b).secondCalls := by
  simp [fullCompile, Circuit.workCalls, Circuit.firstCalls, Circuit.secondCalls,
    Instruction.workCost, Instruction.firstCost, Instruction.secondCost]

end OptimalQLS.TransducerCompiler
