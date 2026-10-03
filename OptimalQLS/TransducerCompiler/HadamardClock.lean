import OptimalQLS.TransducerCompiler.ClockPreparation
import OptimalQLS.TransducerCompiler.BinaryClock.Quantum
import Mathlib.Algebra.BigOperators.Fin

/-! # A literal tensor-Hadamard clock-preparation circuit

Each recursive circuit constructor applies one one-qubit Hadamard on the
new head wire in parallel with the circuit on the remaining wires.
The gate count is therefore the actual number of one-qubit gates.
-/

noncomputable section
namespace OptimalQLS.TransducerCompiler.HadamardClock
open Matrix
open scoped Kronecker

abbrev Bits (ℓ : ℕ) := Fin ℓ → Bool

/-- The real entries of the standard one-qubit Hadamard matrix. -/
def hadamardEntry (i j : Bool) : ℝ :=
  if i && j then -(Real.sqrt 2)⁻¹ else (Real.sqrt 2)⁻¹

def hadamardReal : Matrix.unitaryGroup Bool ℝ := by
  refine ⟨hadamardEntry, ?_⟩
  rw [Matrix.mem_unitaryGroup_iff]
  have hc : ((Real.sqrt 2)⁻¹) ^ 2 = (1 : ℝ) / 2 := by
    rw [inv_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  ext i j
  cases i <;> cases j <;>
    simp [Matrix.mul_apply, Matrix.star_eq_conjTranspose, hadamardEntry] <;> nlinarith

/-- One actual real one-qubit unitary gate. -/
def hadamard : Matrix.unitaryGroup Bool ℂ := complexifyRealUnitary hadamardReal

theorem hadamard_real (i j : Bool) : ((hadamard : Matrix Bool Bool ℂ) i j).im = 0 := rfl

@[simp] theorem hadamard_zero_column (i : Bool) :
    (hadamard : Matrix Bool Bool ℂ) i false = ((Real.sqrt 2)⁻¹ : ℝ) := by
  cases i <;> rfl

/-- Tensor placement of two concrete unitaries on disjoint registers. -/
def tensorUnitary {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (U : Matrix.unitaryGroup a ℂ) (V : Matrix.unitaryGroup b ℂ) :
    Matrix.unitaryGroup (a × b) ℂ :=
  ⟨(U : Matrix a a ℂ) ⊗ₖ (V : Matrix b b ℂ), Matrix.kronecker_mem_unitary U.property V.property⟩

/-- A tensor-Hadamard circuit, with one explicit Hadamard node per qubit. -/
inductive Circuit : ℕ → Type where
  | nil : Circuit 0
  | head {ℓ : ℕ} (tail : Circuit ℓ) : Circuit (ℓ + 1)

/-- Exact matrix semantics of this one-qubit-gate circuit. -/
def Circuit.eval : {ℓ : ℕ} → Circuit ℓ → Matrix.unitaryGroup (Bits ℓ) ℂ
  | 0, .nil => 1
  | _ + 1, .head c => rewireUnitary (Fin.consEquiv (fun _ => Bool))
      (tensorUnitary hadamard c.eval)

def Circuit.gateCount : {ℓ : ℕ} → Circuit ℓ → ℕ
  | 0, .nil => 0
  | _ + 1, .head c => c.gateCount + 1

/-- The circuit of exactly one Hadamard on each clock bit. -/
def circuit : (ℓ : ℕ) → Circuit ℓ
  | 0 => .nil
  | ℓ + 1 => .head (circuit ℓ)

@[simp] theorem circuit_gateCount (ℓ : ℕ) : (circuit ℓ).gateCount = ℓ := by
  induction ℓ with
  | zero => rfl
  | succ ℓ ih => simp [circuit, Circuit.gateCount, ih]

def tensorHadamard (ℓ : ℕ) : Matrix.unitaryGroup (Bits ℓ) ℂ := (circuit ℓ).eval

theorem tensorHadamard_real (ℓ : ℕ) (i j : Bits ℓ) :
    ((tensorHadamard ℓ : Matrix (Bits ℓ) (Bits ℓ) ℂ) i j).im = 0 := by
  induction ℓ with
  | zero =>
    have hij : i = j := Subsingleton.elim _ _
    simp [tensorHadamard, circuit, Circuit.eval, hij]
  | succ ℓ ih =>
    change ((hadamard : Matrix Bool Bool ℂ) (i 0) (j 0) *
      (tensorHadamard ℓ : Matrix (Bits ℓ) (Bits ℓ) ℂ) (Fin.tail i) (Fin.tail j)).im = 0
    simp [Complex.mul_im, hadamard_real, ih]

theorem tensorHadamard_zero_column (ℓ : ℕ) (i : Bits ℓ) :
    (tensorHadamard ℓ : Matrix (Bits ℓ) (Bits ℓ) ℂ) i (fun _ => false) =
      (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) ^ ℓ := by
  induction ℓ with
  | zero =>
    have hi : i = fun _ => false := Subsingleton.elim _ _
    simp [tensorHadamard, circuit, Circuit.eval, hi]
  | succ ℓ ih =>
    change (hadamard : Matrix Bool Bool ℂ) (i 0) false *
      (tensorHadamard ℓ : Matrix (Bits ℓ) (Bits ℓ) ℂ) (Fin.tail i) (fun _ => false) = _
    rw [hadamard_zero_column, ih, pow_succ]
    ring

theorem sqrt_two_pow (ℓ : ℕ) : Real.sqrt ((2 : ℝ) ^ ℓ) = Real.sqrt 2 ^ ℓ := by
  induction ℓ with
  | zero => simp
  | succ ℓ ih => rw [pow_succ, Real.sqrt_mul' _ (by norm_num : (0 : ℝ) ≤ 2), ih, pow_succ]

theorem tensorHadamard_uniform_column (ℓ : ℕ) (i : Bits ℓ) :
    (tensorHadamard ℓ : Matrix (Bits ℓ) (Bits ℓ) ℂ) i (fun _ => false) =
      ((Real.sqrt (2 ^ ℓ : ℕ))⁻¹ : ℝ) := by
  rw [tensorHadamard_zero_column]
  simp only [Nat.cast_pow, Nat.cast_ofNat, sqrt_two_pow]
  exact_mod_cast (inv_pow (Real.sqrt 2) ℓ)

theorem tensorHadamard_prepare (ℓ : ℕ) :
    (tensorHadamard ℓ : Matrix (Bits ℓ) (Bits ℓ) ℂ) *ᵥ Pi.single (fun _ => false) 1 =
      fun _ => (((Real.sqrt (2 ^ ℓ : ℕ))⁻¹ : ℝ) : ℂ) := by
  funext i
  simp only [Matrix.mulVec_single_one]
  exact tensorHadamard_uniform_column ℓ i

/-- Explicit low-first binary wiring from bit strings to the finite clock basis. -/
def bitsFinEquiv (ℓ : ℕ) : Bits ℓ ≃ Fin (2 ^ ℓ) :=
  (Equiv.piCongrRight (fun _ : Fin ℓ => finTwoEquiv.symm)).trans finFunctionFinEquiv

@[simp] theorem bitsFinEquiv_zero (ℓ : ℕ) :
    bitsFinEquiv ℓ (fun _ => false) = (⟨0, by positivity⟩ : Fin (2 ^ ℓ)) := by
  apply Fin.ext
  change (∑ i : Fin ℓ, (finTwoEquiv.symm false).val * 2 ^ i.val) = 0
  simp [finTwoEquiv]

/-- The explicit wiring uses precisely the standard low-first binary digits. -/
theorem bitsFinEquiv_symm_apply (ℓ : ℕ) (t : Fin (2 ^ ℓ)) (i : Fin ℓ) :
    (bitsFinEquiv ℓ).symm t i = Nat.testBit t.val i.val := by
  rw [Nat.testBit_eq_decide_div_mod_eq, Bool.eq_iff_iff]
  simp [bitsFinEquiv, finFunctionFinEquiv, finTwoEquiv, Fin.ext_iff]

/-- The same `ℓ`-gate preparation circuit in the `Fin (2^ℓ)` clock convention. -/
def finHadamard (ℓ : ℕ) : Matrix.unitaryGroup (Fin (2 ^ ℓ)) ℂ :=
  rewireUnitary (bitsFinEquiv ℓ) (tensorHadamard ℓ)

theorem finHadamard_real (ℓ : ℕ) (i j : Fin (2 ^ ℓ)) :
    ((finHadamard ℓ : Matrix (Fin (2 ^ ℓ)) (Fin (2 ^ ℓ)) ℂ) i j).im = 0 :=
  tensorHadamard_real ℓ _ _

theorem finHadamard_prepare (ℓ : ℕ) :
    (finHadamard ℓ : Matrix (Fin (2 ^ ℓ)) (Fin (2 ^ ℓ)) ℂ) *ᵥ
        Pi.single (⟨0, by positivity⟩ : Fin (2 ^ ℓ)) 1 =
      fun _ => (((Real.sqrt (2 ^ ℓ : ℕ))⁻¹ : ℝ) : ℂ) := by
  funext i
  simp only [Matrix.mulVec_single_one]
  change (tensorHadamard ℓ : Matrix (Bits ℓ) (Bits ℓ) ℂ)
    ((bitsFinEquiv ℓ).symm i) ((bitsFinEquiv ℓ).symm ⟨0, by positivity⟩) = _
  have hz : (bitsFinEquiv ℓ).symm ⟨0, by positivity⟩ = fun _ => false := by
    apply (bitsFinEquiv ℓ).injective
    simp
  rw [hz, tensorHadamard_uniform_column]

theorem hadamard_symmetric (i j : Bool) :
    (hadamard : Matrix Bool Bool ℂ) i j = (hadamard : Matrix Bool Bool ℂ) j i := by
  change (hadamardEntry i j : ℂ) = (hadamardEntry j i : ℂ)
  simp [hadamardEntry, Bool.and_comm]

theorem tensorHadamard_symmetric (ℓ : ℕ) (i j : Bits ℓ) :
    (tensorHadamard ℓ : Matrix (Bits ℓ) (Bits ℓ) ℂ) i j =
      (tensorHadamard ℓ : Matrix (Bits ℓ) (Bits ℓ) ℂ) j i := by
  induction ℓ with
  | zero => exact congrArg (fun k => (tensorHadamard 0).val i k) (Subsingleton.elim j i)
  | succ ℓ ih =>
    change (hadamard : Matrix Bool Bool ℂ) (i 0) (j 0) *
      (tensorHadamard ℓ : Matrix (Bits ℓ) (Bits ℓ) ℂ) (Fin.tail i) (Fin.tail j) =
        (hadamard : Matrix Bool Bool ℂ) (j 0) (i 0) *
          (tensorHadamard ℓ : Matrix (Bits ℓ) (Bits ℓ) ℂ) (Fin.tail j) (Fin.tail i)
    rw [hadamard_symmetric, ih]

theorem tensorHadamard_selfAdjoint (ℓ : ℕ) :
    star (tensorHadamard ℓ : Matrix (Bits ℓ) (Bits ℓ) ℂ) =
      (tensorHadamard ℓ : Matrix (Bits ℓ) (Bits ℓ) ℂ) := by
  ext i j
  change star ((tensorHadamard ℓ).val j i) = (tensorHadamard ℓ).val i j
  rw [tensorHadamard_symmetric ℓ j i]
  exact Complex.conj_eq_iff_im.2 (tensorHadamard_real ℓ i j)

theorem finHadamard_selfAdjoint (ℓ : ℕ) :
    star (finHadamard ℓ : Matrix (Fin (2 ^ ℓ)) (Fin (2 ^ ℓ)) ℂ) =
      (finHadamard ℓ : Matrix (Fin (2 ^ ℓ)) (Fin (2 ^ ℓ)) ℂ) := by
  ext i j
  exact congrFun (congrFun (tensorHadamard_selfAdjoint ℓ) ((bitsFinEquiv ℓ).symm i))
    ((bitsFinEquiv ℓ).symm j)

/-- The same `ℓ` one-qubit gates unprepare the clock exactly. -/
theorem finHadamard_unprepare (ℓ : ℕ) :
    (finHadamard ℓ : Matrix (Fin (2 ^ ℓ)) (Fin (2 ^ ℓ)) ℂ) *ᵥ
        (fun _ => (((Real.sqrt (2 ^ ℓ : ℕ))⁻¹ : ℝ) : ℂ)) =
      Pi.single (⟨0, by positivity⟩ : Fin (2 ^ ℓ)) 1 := by
  rw [← finHadamard_prepare ℓ, Matrix.mulVec_mulVec]
  have hh : (finHadamard ℓ).val * (finHadamard ℓ).val = 1 := by
    calc
      _ = star (finHadamard ℓ).val * (finHadamard ℓ).val := by rw [finHadamard_selfAdjoint]
      _ = 1 := (finHadamard ℓ).property.1
  rw [hh, Matrix.one_mulVec]

end OptimalQLS.TransducerCompiler.HadamardClock
