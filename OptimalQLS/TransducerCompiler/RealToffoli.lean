import OptimalQLS.TransducerCompiler.ClockPreparation
import OptimalQLS.TransducerCompiler.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-! # A real fifteen-gate Toffoli implementation with one clean ancilla

The seven-gate controlled computation has sectors I, I, Z, X. On a clean
ancilla it computes the AND without phase. Copying this bit to an arbitrary
target and reversing the computation implements Toffoli and cleans the ancilla.
-/

noncomputable section
namespace OptimalQLS.TransducerCompiler.RealToffoli
open Matrix

/-- Real planar rotation, in the false/true computational basis. -/
def rotationEntry (θ : ℝ) : Bool → Bool → ℝ
  | false, false => Real.cos θ
  | false, true => -Real.sin θ
  | true, false => Real.sin θ
  | true, true => Real.cos θ

def rotationReal (θ : ℝ) : Matrix.unitaryGroup Bool ℝ := by
  refine ⟨rotationEntry θ, ?_⟩
  rw [Matrix.mem_unitaryGroup_iff]
  ext i j
  cases i <;> cases j <;>
    simp [Matrix.mul_apply, Matrix.star_eq_conjTranspose, rotationEntry] <;>
    nlinarith [Real.cos_sq_add_sin_sq θ]

def xEntry (i j : Bool) : ℝ := if i = j then 0 else 1

def xReal : Matrix.unitaryGroup Bool ℝ := by
  refine ⟨xEntry, ?_⟩
  rw [Matrix.mem_unitaryGroup_iff]
  ext i j
  cases i <;> cases j <;> simp [Matrix.mul_apply, Matrix.star_eq_conjTranspose, xEntry]

theorem rotation_mul (α β : ℝ) : rotationReal α * rotationReal β = rotationReal (α + β) := by
  apply Subtype.ext
  ext i j
  cases i <;> cases j <;>
    simp [rotationReal, rotationEntry, Matrix.mul_apply, Real.cos_add, Real.sin_add] <;> ring

@[simp] theorem rotation_zero : rotationReal 0 = 1 := by
  apply Subtype.ext
  ext i j
  cases i <;> cases j <;> simp [rotationReal, rotationEntry]

@[simp] theorem xReal_sq : xReal * xReal = 1 := by
  apply Subtype.ext
  ext i j
  cases i <;> cases j <;> simp [xReal, xEntry, Matrix.mul_apply]

theorem x_rotation (θ : ℝ) : xReal * rotationReal θ = rotationReal (-θ) * xReal := by
  apply Subtype.ext
  ext i j
  cases i <;> cases j <;>
    simp [xReal, xEntry, rotationReal, rotationEntry, Matrix.mul_apply]

theorem rotation_x_rotation (α β : ℝ) :
    rotationReal α * xReal * rotationReal β = rotationReal (α - β) * xReal := by
  rw [mul_assoc, x_rotation, ← mul_assoc, rotation_mul]
  rfl

theorem rotation_neg (θ : ℝ) : rotationReal (-θ) = (rotationReal θ)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [rotation_mul, neg_add_cancel, rotation_zero]

@[simp] theorem xReal_inv : xReal⁻¹ = xReal := by
  symm
  apply eq_inv_of_mul_eq_one_left
  exact xReal_sq

/-- The prescribed angle of the real ancilla computation. -/
def angle : ℝ := Real.pi / 8

def controlledX (b : Bool) : Matrix.unitaryGroup Bool ℝ := if b then xReal else 1

/-- Exact control-sector matrix of the seven gates, in execution order. -/
def computeReal (a b : Bool) : Matrix.unitaryGroup Bool ℝ :=
  rotationReal (-angle) * controlledX b * rotationReal (-angle) * controlledX a *
    rotationReal angle * controlledX b * rotationReal angle

theorem x_rotation_x (θ : ℝ) : xReal * rotationReal θ * xReal = rotationReal (-θ) := by
  rw [x_rotation, mul_assoc, xReal_sq, mul_one]

/-- The clean ancilla receives the AND of the two controls with no phase. -/
theorem computeReal_zero_column (a b z : Bool) :
    (computeReal a b : Matrix Bool Bool ℝ) z false = if z = (a && b) then 1 else 0 := by
  cases a <;> cases b
  · have h : computeReal false false = 1 := by simp [computeReal, controlledX, rotation_mul]
    rw [h]
    cases z <;> rfl
  · have h : computeReal false true = 1 := by
      simp [computeReal, controlledX, rotation_x_rotation, x_rotation_x, rotation_mul]
    rw [h]
    cases z <;> rfl
  · have h : computeReal true false = rotationReal (-(Real.pi / 2)) * xReal := by
      change rotationReal (-angle) * 1 * rotationReal (-angle) * xReal *
        rotationReal angle * 1 * rotationReal angle = _
      rw [mul_one, mul_one, rotation_mul, rotation_x_rotation, rotation_x_rotation]
      congr 2
      dsimp [angle]
      ring
    rw [h]
    cases z <;> simp [rotationReal, rotationEntry, xReal, xEntry, Matrix.mul_apply]
  · have h : computeReal true true = xReal := by
      simp [computeReal, controlledX, rotation_x_rotation]
    rw [h]
    cases z <;> simp [xReal, xEntry]

/-- Entrywise complexification is a genuine group representation. -/
def complexifyHom : Matrix.unitaryGroup Bool ℝ →* Matrix.unitaryGroup Bool ℂ where
  toFun := complexifyRealUnitary
  map_one' := by
    apply Subtype.ext
    ext i j
    simp [complexifyRealUnitary, Matrix.one_apply]
  map_mul' U V := by
    apply Subtype.ext
    ext i j
    simp [complexifyRealUnitary, Matrix.mul_apply, Complex.ofReal_mul]

/-- Sectors are the two controls and the arbitrary target bit. -/
abbrev Sector := Bool × Bool × Bool
/-- The ancilla is the outer coordinate. -/
abbrev State := Bool × Sector

def block (U : Sector → Matrix.unitaryGroup Bool ℂ) : Matrix.unitaryGroup State ℂ :=
  ⟨Matrix.blockDiagonal (fun s => (U s).val), by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
      Matrix.blockDiagonal_conjTranspose, ← Matrix.blockDiagonal_mul]
    have h : (fun s => (U s).val * (U s).valᴴ) = 1 := by
      funext s
      exact (U s).property.2
    rw [h, Matrix.blockDiagonal_one]⟩

theorem block_mul (U V : Sector → Matrix.unitaryGroup Bool ℂ) :
    block (fun s => U s * V s) = block U * block V := by
  apply Subtype.ext
  change Matrix.blockDiagonal (fun s => (U s).val * (V s).val) =
    Matrix.blockDiagonal (fun s => (U s).val) * Matrix.blockDiagonal (fun s => (V s).val)
  rw [Matrix.blockDiagonal_mul]

@[simp] theorem block_one : block (fun _ => 1) = 1 := by
  apply Subtype.ext
  change Matrix.blockDiagonal (1 : Sector → Matrix Bool Bool ℂ) = 1
  exact Matrix.blockDiagonal_one

def blockHom : (Sector → Matrix.unitaryGroup Bool ℂ) →* Matrix.unitaryGroup State ℂ where
  toFun := block
  map_one' := block_one
  map_mul' := block_mul

/-- Each constructor is a literal one-qubit rotation or one CNOT gate. -/
inductive ComputeGate where
  | rotate (θ : ℝ)
  | controlA
  | controlB

def ComputeGate.small (a b : Bool) : ComputeGate → Matrix.unitaryGroup Bool ℝ
  | .rotate θ => rotationReal θ
  | .controlA => controlledX a
  | .controlB => controlledX b

def ComputeGate.eval (g : ComputeGate) : Matrix.unitaryGroup State ℂ :=
  block (fun s => complexifyHom (g.small s.1 s.2.1))

def ComputeGate.inverse : ComputeGate → ComputeGate
  | .rotate θ => .rotate (-θ)
  | .controlA => .controlA
  | .controlB => .controlB

theorem ComputeGate.small_inverse (g : ComputeGate) (a b : Bool) :
    g.inverse.small a b = (g.small a b)⁻¹ := by
  cases g with
  | rotate θ => exact rotation_neg θ
  | controlA => cases a <;> simp [inverse, small, controlledX]
  | controlB => cases b <;> simp [inverse, small, controlledX]

theorem ComputeGate.eval_inverse (g : ComputeGate) : g.inverse.eval = g.eval⁻¹ := by
  simp only [eval, small_inverse, map_inv]
  exact map_inv blockHom _

def computeGates : List ComputeGate :=
  [.rotate angle, .controlB, .rotate angle, .controlA,
    .rotate (-angle), .controlB, .rotate (-angle)]

def evalCompute : List ComputeGate → Matrix.unitaryGroup State ℂ
  | [] => 1
  | g :: gs => evalCompute gs * g.eval

theorem evalCompute_append (c d : List ComputeGate) :
    evalCompute (c ++ d) = evalCompute d * evalCompute c := by
  induction c with
  | nil => simp [evalCompute]
  | cons g gs ih => simp [evalCompute, ih, mul_assoc]

theorem evalCompute_inverse (c : List ComputeGate) :
    evalCompute (c.reverse.map ComputeGate.inverse) = (evalCompute c)⁻¹ := by
  induction c with
  | nil => simp [evalCompute]
  | cons g gs ih =>
    rw [List.reverse_cons, List.map_append, evalCompute_append]
    simp only [List.map_cons, List.map_nil, evalCompute, one_mul,
      ComputeGate.eval_inverse, ih, _root_.mul_inv_rev]

theorem compute_block : evalCompute computeGates =
    block (fun s => complexifyHom (computeReal s.1 s.2.1)) := by
  simp only [computeGates, evalCompute, ComputeGate.eval, ComputeGate.small, one_mul]
  simp only [← block_mul, ← map_mul]
  rfl

/-- The actual seven-gate matrix computes the AND into a clean ancilla, without phase. -/
theorem compute_basis (a b y : Bool) :
    (evalCompute computeGates : Matrix State State ℂ) *ᵥ Pi.single (false, (a, b, y)) 1 =
      Pi.single (a && b, (a, b, y)) 1 := by
  rw [compute_block]
  funext p
  rcases p with ⟨z, s⟩
  simp only [Matrix.mulVec_single_one]
  by_cases hs : s = (a, b, y)
  · subst s
    simp [block, Matrix.blockDiagonal_apply, complexifyHom, complexifyRealUnitary,
      computeReal_zero_column, Pi.single_apply]
    split_ifs <;> simp_all
  · simp [block, Matrix.blockDiagonal_apply, hs, Prod.mk.injEq]

theorem uncompute_basis (a b y : Bool) :
    ((evalCompute computeGates)⁻¹).val *ᵥ Pi.single (a && b, (a, b, y)) 1 =
      Pi.single (false, (a, b, y)) 1 := by
  rw [← compute_basis a b y, Matrix.mulVec_mulVec]
  have hh : ((evalCompute computeGates)⁻¹).val *
      (evalCompute computeGates : Matrix State State ℂ) = 1 :=
    (evalCompute computeGates).property.1
  rw [hh, Matrix.one_mulVec]

/-- The middle operation is precisely one CNOT from ancilla z to target y. -/
def copyEquiv : Equiv.Perm State where
  toFun p := (p.1, (p.2.1, p.2.2.1, Bool.xor p.2.2.2 p.1))
  invFun p := (p.1, (p.2.1, p.2.2.1, Bool.xor p.2.2.2 p.1))
  left_inv p := by rcases p with ⟨z, a, b, y⟩; cases z <;> cases y <;> rfl
  right_inv p := by rcases p with ⟨z, a, b, y⟩; cases z <;> cases y <;> rfl

def copyUnitary : Matrix.unitaryGroup State ℂ := permutation copyEquiv

theorem copy_basis (z a b y : Bool) :
    (copyUnitary : Matrix State State ℂ) *ᵥ Pi.single (z, (a, b, y)) 1 =
      Pi.single (z, (a, b, Bool.xor y z)) 1 := by
  rw [copyUnitary, permutation_apply]
  funext p
  have he : copyEquiv p = (z, (a, b, y)) ↔ p = (z, (a, b, Bool.xor y z)) :=
    copyEquiv.apply_eq_iff_eq_symm_apply
  simp only [Function.comp_apply, Pi.single_apply, he]

/-- A literal one- or two-bit gate instruction: a rotation, one of the two compute CNOTs,
or the copy CNOT. -/
inductive Gate where
  | atom (g : ComputeGate)
  | copy

def Gate.eval : Gate → Matrix.unitaryGroup State ℂ
  | .atom g => g.eval
  | .copy => copyUnitary

/-- The numerical arity is fixed by the primitive instruction, not supplied as a certificate. -/
def Gate.arity : Gate → ℕ
  | .atom (.rotate _) => 1
  | _ => 2

theorem Gate.arity_le_two (g : Gate) : g.arity ≤ 2 := by
  cases g with
  | copy => decide
  | atom g => cases g <;> simp [arity]

def eval : List Gate → Matrix.unitaryGroup State ℂ
  | [] => 1
  | g :: gs => eval gs * g.eval

theorem eval_append (c d : List Gate) : eval (c ++ d) = eval d * eval c := by
  induction c with
  | nil => simp [eval]
  | cons g gs ih => simp [eval, ih, mul_assoc]

theorem eval_local (c : List ComputeGate) : eval (c.map Gate.atom) = evalCompute c := by
  induction c with
  | nil => rfl
  | cons g gs ih => simp [eval, evalCompute, Gate.eval, ih]

/-- Seven compute gates, one copy CNOT, and the seven inverse compute gates. -/
def circuit : List Gate :=
  computeGates.map Gate.atom ++ [.copy] ++
    (computeGates.reverse.map ComputeGate.inverse).map Gate.atom

@[simp] theorem circuit_length : circuit.length = 15 := by
  simp [circuit, computeGates]

def unitary : Matrix.unitaryGroup State ℂ := eval circuit

theorem unitary_eq : unitary =
    (evalCompute computeGates)⁻¹ * copyUnitary * evalCompute computeGates := by
  simp only [unitary, circuit, eval_append, eval_local, evalCompute_inverse, eval, Gate.eval,
    one_mul, mul_assoc]

/-- Exact Toffoli semantics for arbitrary target y, with the reusable ancilla returned to zero. -/
theorem clean_toffoli_basis (a b y : Bool) :
    (unitary : Matrix State State ℂ) *ᵥ Pi.single (false, (a, b, y)) 1 =
      Pi.single (false, (a, b, Bool.xor y (a && b))) 1 := by
  rw [unitary_eq]
  simp only [Submonoid.coe_mul, ← Matrix.mulVec_mulVec, compute_basis, copy_basis, uncompute_basis]

theorem ComputeGate.eval_real (g : ComputeGate) (i j : State) : (g.eval.val i j).im = 0 := by
  simp only [ComputeGate.eval, block, Matrix.blockDiagonal_apply]
  split_ifs
  · rfl
  · rfl

theorem Gate.eval_real (g : Gate) (i j : State) : (g.eval.val i j).im = 0 := by
  cases g with
  | atom g => exact g.eval_real i j
  | copy => exact permutation_real _ _ _

theorem eval_real (c : List Gate) (i j : State) : ((eval c).val i j).im = 0 := by
  induction c generalizing i j with
  | nil =>
    simp only [eval, OneMemClass.coe_one, Matrix.one_apply]
    split_ifs <;> rfl
  | cons g gs ih =>
    simp [eval, Matrix.mul_apply, Complex.mul_im, ih, Gate.eval_real]

theorem unitary_real (i j : State) : ((unitary : Matrix State State ℂ) i j).im = 0 :=
  eval_real circuit i j

/-- The intended three-bit Toffoli permutation on the data register. -/
def toffoliSector (s : Sector) : Sector :=
  (s.1, s.2.1, Bool.xor s.2.2 (s.1 && s.2.1))

/-- An arbitrary quantum data vector with a clean reusable ancilla. -/
def cleanVector (v : Sector → ℂ) : State → ℂ
  | (false, s) => v s
  | (true, _) => 0

theorem unitary_clean_column (s : Sector) (p : State) :
    (unitary : Matrix State State ℂ) p (false, s) =
      (Pi.single (false, toffoliSector s) (1 : ℂ) : State → ℂ) p := by
  have h := congrFun (clean_toffoli_basis s.1 s.2.1 s.2.2) p
  simpa only [Matrix.mulVec_single_one, toffoliSector] using h

/-- Exact semantics on arbitrary superpositions of all three data bits, with ancilla cleanup. -/
theorem clean_toffoli_vector (v : Sector → ℂ) :
    (unitary : Matrix State State ℂ) *ᵥ cleanVector v =
      cleanVector (fun s => v (toffoliSector s)) := by
  funext p
  rcases p with ⟨z, a, b, y⟩
  cases z <;> cases a <;> cases b <;> cases y <;>
    simp [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fintype.sum_bool,
      cleanVector, unitary_clean_column, toffoliSector, Pi.single_apply]

end OptimalQLS.TransducerCompiler.RealToffoli
