import OptimalQLS.GraphEncoding.LabelGates

/-! # The remaining graph work instructions are literal real one- and two-qubit gates -/
noncomputable section
set_option synthInstance.maxSize 1024
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false
namespace OptimalQLS.GraphEncoding
open Matrix PolynomialTransform TransducerCompiler
variable {W C : Type*} [Fintype W] [DecidableEq W] [Fintype C] [DecidableEq C]

theorem placeHom_entries {a b w : Type*} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b] [Fintype w] [DecidableEq w]
    (e : a × b ≃ w) (U : Matrix.unitaryGroup a ℂ) (i j : w) :
    (TransducerCompiler.GateSynthesis.placeHom e U).val i j =
      if (e.symm i).2 = (e.symm j).2 then U.val (e.symm i).1 (e.symm j).1 else 0 := by
  change (Matrix.blockDiagonal (fun _ : b => if true then U.val else 1)) (e.symm i) (e.symm j) = _
  simp [Matrix.blockDiagonal_apply]

/-- A sum-sector bit is a single computational qubit, with no basis rotation. -/
def sumBitWiring (W : Type*) : Bool × W ≃ W ⊕ W where
  toFun p := if p.1 then .inr p.2 else .inl p.2
  invFun p := match p with | .inl x => (false,x) | .inr x => (true,x)
  left_inv p := by rcases p with ⟨b,x⟩; cases b <;> rfl
  right_inv p := by cases p <;> rfl

def mixRealEntry (r : ℝ) : Matrix Bool Bool ℝ
  | false,false => -r
  | false,true => Real.sqrt (1-r^2)
  | true,false => Real.sqrt (1-r^2)
  | true,true => r

/-- A genuine2×2 real orthogonal gate. -/
def mixReal (r : ℝ) (hr : |r| < 1) : Matrix.unitaryGroup Bool ℝ := by
  refine ⟨mixRealEntry r, ?_⟩
  have hn : 0 ≤ 1-r^2 := by nlinarith [(abs_lt.mp hr).1,(abs_lt.mp hr).2]
  have hs := Real.sq_sqrt hn
  rw [Matrix.mem_unitaryGroup_iff]
  ext i j
  cases i <;> cases j <;>
    simp [Matrix.mul_apply, Matrix.star_eq_conjTranspose, mixRealEntry] <;> nlinarith

theorem mix_one_qubit (r : ℝ) (hr : |r| < 1) :
    (TransducerCompiler.GateSynthesis.placeHom (sumBitWiring W)
      (complexifyRealUnitary (mixReal r hr))).val = fractionalMix (n := W) r := by
  ext i j
  cases i <;> cases j <;>
    simp [placeHom_entries,
      rewireUnitary, controlledOn, Matrix.blockDiagonal_apply,
      sumBitWiring, complexifyRealUnitary, mixReal, mixRealEntry, fractionalMix,
      Matrix.one_apply, Matrix.smul_apply, Complex.real_smul] <;>
    split_ifs <;> simp_all

/-- SELECT=0 control turns any real one-qubit gate into one real two-qubit gate. -/
def controlledBitReal (G : Matrix.unitaryGroup Bool ℝ) : Matrix.unitaryGroup (Bool × Bool) ℝ :=
  ⟨Matrix.blockDiagonal (fun b => if b then (1 : Matrix Bool Bool ℝ) else G.val), by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
      Matrix.blockDiagonal_conjTranspose, ← Matrix.blockDiagonal_mul]
    have h : (fun b : Bool =>
        (if b then (1 : Matrix Bool Bool ℝ) else G.val) *
        (if b then (1 : Matrix Bool Bool ℝ) else G.val)ᴴ) = 1 := by
      funext b
      cases b
      · exact G.property.2
      · simp
    rw [h, Matrix.blockDiagonal_one]⟩

/-- The selected pair is exactly the Hermitianization bit and SELECT bit;
all edge and oracle registers are spectators. -/
def controlledBitWiring (C W : Type*) :
    ((Bool × Bool) × (C × W)) ≃ ((C × (W ⊕ W)) ⊕ (C × (W ⊕ W))) where
  toFun p := if p.1.2 then
    .inr (p.2.1, if p.1.1 then .inr p.2.2 else .inl p.2.2)
    else .inl (p.2.1, if p.1.1 then .inr p.2.2 else .inl p.2.2)
  invFun p := match p with
    | .inl (c,.inl w) => ((false,false),(c,w))
    | .inl (c,.inr w) => ((true,false),(c,w))
    | .inr (c,.inl w) => ((false,true),(c,w))
    | .inr (c,.inr w) => ((true,true),(c,w))
  left_inv p := by rcases p with ⟨⟨a,b⟩,c,w⟩; cases a <;> cases b <;> rfl
  right_inv p := by rcases p with ⟨c,w⟩|⟨c,w⟩ <;> cases w <;> rfl

/-- Tensor spectators and SELECT controls do not change the physical two-bit arity. -/
theorem controlled_one_is_two (G : Matrix.unitaryGroup Bool ℝ) :
    TransducerCompiler.GateSynthesis.placeHom (controlledBitWiring C W)
      (complexifyRealUnitary (controlledBitReal G)) =
    sumUnitary (tensorUnitary (1 : Matrix.unitaryGroup C ℂ)
      (TransducerCompiler.GateSynthesis.placeHom (sumBitWiring W) (complexifyRealUnitary G))) 1 := by
  apply Subtype.ext
  ext i j
  rcases i with ⟨c,i⟩|⟨c,i⟩ <;> rcases j with ⟨d,j⟩|⟨d,j⟩ <;>
    cases i <;> cases j <;>
    simp [placeHom_entries,
      rewireUnitary, controlledOn, Matrix.blockDiagonal_apply, controlledBitWiring,
      controlledBitReal, complexifyRealUnitary, sumBitWiring, sumUnitary,
      tensorUnitary, HadamardClock.tensorUnitary, Matrix.one_apply] <;>
    split_ifs <;> simp_all

/-- The swap in oracle Hermitianization is one X on that bit. -/
theorem swap_one_qubit :
    TransducerCompiler.GateSynthesis.placeHom (sumBitWiring W)
      (complexifyRealUnitary RealToffoli.xReal) = swapPublicPrivate := by
  apply Subtype.ext
  ext i j
  cases i <;> cases j <;>
    simp [placeHom_entries,
      rewireUnitary, controlledOn, Matrix.blockDiagonal_apply, sumBitWiring,
      complexifyRealUnitary, RealToffoli.xReal, RealToffoli.xEntry, swapPublicPrivate,
      Matrix.one_apply]

theorem hadamard_one_qubit :
    TransducerCompiler.GateSynthesis.placeHom (sumBitWiring W)
      (complexifyRealUnitary (mixReal (-halfAmplitude) halfAmplitude_bound)) = sumHadamard W := by
  apply Subtype.ext
  exact mix_one_qubit (-halfAmplitude) halfAmplitude_bound

theorem mixing_one_qubit (κ : ℝ) (hκ : 0 < κ) :
    TransducerCompiler.GateSynthesis.placeHom (sumBitWiring W)
      (complexifyRealUnitary (mixReal (-mixAmplitude κ) (mixAmplitude_properties hκ).2)) =
      weightedMix W κ hκ := by
  apply Subtype.ext
  exact mix_one_qubit _ _

/-- The minus sign of the second edge is a single real Z on SELECT. -/
def zReal : Matrix.unitaryGroup Bool ℝ := by
  refine ⟨fun i j => if i=j then (if i then -1 else 1) else 0, ?_⟩
  rw [Matrix.mem_unitaryGroup_iff]
  ext i j
  cases i <;> cases j <;> norm_num [Matrix.mul_apply, Matrix.star_eq_conjTranspose]

theorem phase_one_qubit :
    TransducerCompiler.GateSynthesis.placeHom (sumBitWiring W) (complexifyRealUnitary zReal) =
      sumUnitary (1 : Matrix.unitaryGroup W ℂ) (-1) := by
  apply Subtype.ext
  ext i j
  cases i <;> cases j <;>
    simp [placeHom_entries,
      rewireUnitary, controlledOn, Matrix.blockDiagonal_apply, sumBitWiring,
      complexifyRealUnitary, zReal, sumUnitary, Matrix.one_apply]
  all_goals
    change _ = -((1 : Matrix W W ℂ) _ _)
    simp only [Matrix.one_apply]
    split_ifs <;> norm_num

end OptimalQLS.GraphEncoding
