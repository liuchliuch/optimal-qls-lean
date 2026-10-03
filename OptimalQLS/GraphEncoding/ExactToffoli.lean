import OptimalQLS.TransducerCompiler.RealToffoli

/-! # Exact real Toffoli with a borrowed bit, including all unprepared columns -/
noncomputable section
set_option synthInstance.maxSize 1024
set_option maxHeartbeats 800000
namespace OptimalQLS.GraphEncoding.ExactToffoli
open Matrix TransducerCompiler TransducerCompiler.RealToffoli
open scoped ComplexConjugate

/-- The four exact sectors of the seven-gate computation. -/
theorem computeReal_entries (a b z r : Bool) :
    (computeReal a b).val r z =
      if r = Bool.xor z (a && b) then (if a && (!b) && z then -1 else 1) else 0 := by
  cases a <;> cases b
  · have h : computeReal false false = 1 := by simp [computeReal, controlledX, rotation_mul]
    rw [h]; cases z <;> cases r <;> rfl
  · have h : computeReal false true = 1 := by
      simp [computeReal, controlledX, rotation_x_rotation, x_rotation_x, rotation_mul]
    rw [h]; cases z <;> cases r <;> rfl
  · have h : computeReal true false = rotationReal (-(Real.pi / 2)) * xReal := by
      change rotationReal (-angle) * 1 * rotationReal (-angle) * xReal *
        rotationReal angle * 1 * rotationReal angle = _
      rw [mul_one, mul_one, rotation_mul, rotation_x_rotation, rotation_x_rotation]
      congr 2
      dsimp [angle]
      ring
    rw [h]
    cases z <;> cases r <;> simp [rotationReal, rotationEntry, xReal, xEntry, Matrix.mul_apply]
  · have h : computeReal true true = xReal := by
      simp [computeReal, controlledX, rotation_x_rotation]
    rw [h]; cases z <;> cases r <;> simp [xReal, xEntry]

theorem computeReal_selfAdjoint (a b : Bool) : (computeReal a b).valᴴ = (computeReal a b).val := by
  ext i j
  cases a <;> cases b <;> cases i <;> cases j <;>
    simp [Matrix.conjTranspose_apply, computeReal_entries]

theorem compute_inverse : (evalCompute computeGates)⁻¹ = evalCompute computeGates := by
  apply Subtype.ext
  change (evalCompute computeGates).valᴴ = (evalCompute computeGates).val
  rw [compute_block]
  ext ⟨z,s⟩ ⟨r,t⟩
  rw [Matrix.conjTranspose_apply]
  by_cases h : s=t
  · subst t
    simp [block, Matrix.blockDiagonal_apply, complexifyHom, complexifyRealUnitary,
      computeReal_entries]
    rcases s with ⟨a,b,y⟩
    cases a <;> cases b <;> cases z <;> cases r <;> norm_num
  · simp [block, Matrix.blockDiagonal_apply, h, Ne.symm h]

/-- The computation on every borrowed-bit basis state, including its sector phase. -/
theorem compute_basis_all (z a b y : Bool) :
    (evalCompute computeGates).val *ᵥ Pi.single (z,(a,b,y)) 1 =
      (if a && (!b) && z then (-1 : ℂ) else 1) •
        (Pi.single (Bool.xor z (a && b),(a,b,y)) 1 : State → ℂ) := by
  rw [compute_block]
  ext ⟨r,s⟩
  simp only [Matrix.mulVec_single_one]
  by_cases hs : s=(a,b,y)
  · subst s
    simp [block, Matrix.blockDiagonal_apply, complexifyHom, complexifyRealUnitary,
      computeReal_entries, Pi.single_apply]
    split_ifs <;> simp_all
  · simp [block, Matrix.blockDiagonal_apply, hs, Pi.single_apply, Prod.mk.injEq]

/-- Full matrix semantics: the clean template has one extra borrowed-bit CNOT. -/
theorem unitary_basis_all (z a b y : Bool) :
    RealToffoli.unitary.val *ᵥ Pi.single (z,(a,b,y)) 1 =
      Pi.single (z,(a,b,Bool.xor y (Bool.xor z (a && b)))) 1 := by
  rw [unitary_eq, compute_inverse]
  simp only [Submonoid.coe_mul, ← Matrix.mulVec_mulVec, compute_basis_all,
    Matrix.mulVec_smul, copy_basis, smul_smul]
  cases z <;> cases a <;> cases b <;> cases y <;> simp

/-- A sixteenth elementary CNOT cancels the unwanted borrowed-bit action. -/
def circuit : List RealToffoli.Gate := RealToffoli.circuit ++ [.copy]

@[simp] theorem circuit_length : circuit.length = 16 := by simp [circuit]

def exactUnitary : Matrix.unitaryGroup State ℂ := RealToffoli.eval circuit

theorem exactUnitary_basis (z a b y : Bool) :
    exactUnitary.val *ᵥ Pi.single (z,(a,b,y)) 1 =
      Pi.single (z,(a,b,Bool.xor y (a && b))) 1 := by
  simp only [exactUnitary, circuit, RealToffoli.eval_append, RealToffoli.eval,
    RealToffoli.Gate.eval, one_mul]
  change (copyUnitary * RealToffoli.unitary).val *ᵥ _ = _
  rw [Submonoid.coe_mul, ← Matrix.mulVec_mulVec, unitary_basis_all, copy_basis]
  cases z <;> cases a <;> cases b <;> cases y <;> rfl

/-- The logical Toffoli acts identically on both borrowed-bit sectors. -/
def toffoliEquiv : Equiv.Perm State where
  toFun p := (p.1,toffoliSector p.2)
  invFun p := (p.1,toffoliSector p.2)
  left_inv p := by rcases p with ⟨z,a,b,y⟩; cases a <;> cases b <;> cases y <;> rfl
  right_inv p := by rcases p with ⟨z,a,b,y⟩; cases a <;> cases b <;> cases y <;> rfl

/-- Global equality, without clean-ancilla premises or an assumed gate certificate. -/
theorem exactUnitary_eq : exactUnitary = permutation toffoliEquiv := by
  apply Subtype.ext
  ext p q
  have h := congrFun (exactUnitary_basis q.1 q.2.1 q.2.2.1 q.2.2.2) p
  rw [Matrix.mulVec_single_one] at h
  change exactUnitary.val p q = _ at h
  rw [h]
  simp only [permutation, toffoliEquiv, toffoliSector, PEquiv.toMatrix, Pi.single_apply]
  rcases p with ⟨z,a,b,y⟩
  rcases q with ⟨r,c,d,v⟩
  cases z <;> cases r <;> cases a <;> cases b <;> cases y <;>
    cases c <;> cases d <;> cases v <;> rfl

theorem circuit_real (i j : State) : (exactUnitary.val i j).im = 0 :=
  RealToffoli.eval_real circuit i j

theorem circuit_arity (g : RealToffoli.Gate) (hg : g ∈ circuit) : g.arity ≤ 2 :=
  RealToffoli.Gate.arity_le_two g

end OptimalQLS.GraphEncoding.ExactToffoli
