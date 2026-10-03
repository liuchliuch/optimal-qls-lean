import OptimalQLS.GraphEncoding.Circuit
import OptimalQLS.GraphEncoding.GateSynthesis

/-! # Literal elementary implementations of both controlled edge dilations -/
noncomputable section
set_option synthInstance.maxSize 1024
set_option maxHeartbeats 800000
namespace OptimalQLS.GraphEncoding
open Matrix PolynomialTransform TransducerCompiler BinaryClock

/-- The two physical graph bits, in the order high, low. -/
def graphBits : Bool × Bool ≃ Fin 4 where
  toFun p := match p with | (false,false) => 0 | (false,true) => 1 | (true,false) => 2 | (true,true) => 3
  invFun g := if g=0 then (false,false) else if g=1 then (false,true) else if g=2 then (true,false) else (true,true)
  left_inv p := by rcases p with ⟨h,l⟩; cases h <;> cases l <;> simp
  right_inv g := by fin_cases g <;> simp

abbrev LabelBits := Fin 4 → Bool

/-- Four named physical wires: SELECT, dilation, graph-high, graph-low. -/
def labelWiring : LabelBits ≃ Label ⊕ Label where
  toFun x := if x 0 then Sum.inr (x 1,graphBits (x 2,x 3)) else Sum.inl (x 1,graphBits (x 2,x 3))
  invFun p := match p with
    | .inl (z,g) => ![false,z,(graphBits.symm g).1,(graphBits.symm g).2]
    | .inr (z,g) => ![true,z,(graphBits.symm g).1,(graphBits.symm g).2]
  left_inv x := by
    funext i
    fin_cases i <;> cases hx : x 0 <;> simp [hx]
  right_inv p := by
    cases p with
    | inl p => rcases p with ⟨z,g⟩; simp
    | inr p => rcases p with ⟨z,g⟩; simp

/-- Four X gates and two Toffolis implement SELECT=0 control of the01 edge. -/
def label01Program : Program (Fin 4) :=
  [.x 0, .x 2, .ccx 0 2 3 (by decide) (by decide), .x 2,
    .ccx 0 2 1 (by decide) (by decide), .x 0]

/-- Two X gates and two Toffolis implement SELECT=1 control of the02 edge. -/
def label02Program : Program (Fin 4) :=
  [.x 3, .ccx 0 3 2 (by decide) (by decide), .x 3,
    .ccx 0 3 1 (by decide) (by decide)]

def label01Perm : Equiv.Perm (Label ⊕ Label) :=
  Equiv.sumCongr (labelPermutation 1 (by decide)) (Equiv.refl Label)
def label02Perm : Equiv.Perm (Label ⊕ Label) :=
  Equiv.sumCongr (Equiv.refl Label) (labelPermutation 2 (by decide))

@[simp] theorem label01Perm_symm : label01Perm.symm = label01Perm := rfl
@[simp] theorem label02Perm_symm : label02Perm.symm = label02Perm := rfl

theorem label01Program_run (x : LabelBits) :
    labelWiring (run label01Program x) = label01Perm (labelWiring x) := by
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    simp [label01Program, run_cons, run_nil, BinaryClock.Gate.act, Function.update_apply,
      labelWiring, graphBits, label01Perm, labelPermutation, labelAction,
      Function.Involutive.toPerm, h0,h1,h2,h3]

theorem label02Program_run (x : LabelBits) :
    labelWiring (run label02Program x) = label02Perm (labelWiring x) := by
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    simp [label02Program, run_cons, run_nil, BinaryClock.Gate.act, Function.update_apply,
      labelWiring, graphBits, label02Perm, labelPermutation, labelAction,
      Function.Involutive.toPerm, h0,h1,h2,h3]

theorem rewire_basis {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (e : a ≃ b) (U : Matrix.unitaryGroup a ℂ) (i j : a)
    (h : U.val *ᵥ Pi.single i 1 = Pi.single j 1) :
    (rewireUnitary e U).val *ᵥ Pi.single (e i) 1 = Pi.single (e j) 1 := by
  rw [TransducerCompiler.rewire_apply]
  have he : (Pi.single (e i) (1 : ℂ) : b → ℂ) ∘ e = Pi.single i 1 := by
    ext k; simp [Pi.single_apply, e.injective.eq_iff]
  rw [he,h]
  ext k
  simp [Pi.single_apply, Equiv.symm_apply_eq]

theorem rewire_program_eq {a : Type*} [Fintype a] [DecidableEq a]
    (e : LabelBits ≃ a) (p : Program (Fin 4)) (r : Equiv.Perm a)
    (hr : r.symm = r) (h : ∀ x, e (run p x) = r (e x)) :
    rewireUnitary e (programUnitary p) = permutation r := by
  apply Subtype.ext
  ext i j
  obtain ⟨x,rfl⟩ := e.surjective j
  have hh := rewire_basis e (programUnitary p) x (run p x) (programUnitary_basis p x)
  rw [h x] at hh
  have hentry := congrFun hh i
  rw [Matrix.mulVec_single_one] at hentry
  change (rewireUnitary e (programUnitary p)).val i (e x) = _ at hentry
  rw [hentry]
  have he : r i = e x ↔ i = r (e x) := by rw [Equiv.apply_eq_iff_eq_symm_apply, hr]
  simp [permutation, PEquiv.toMatrix, Pi.single_apply, he, eq_comm]

theorem label01Perm_unitary : permutation label01Perm = sumUnitary (labelUnitary 1 (by decide)) 1 := by
  apply Subtype.ext
  ext i j
  cases i <;> cases j <;>
    simp [permutation, label01Perm, sumUnitary, labelUnitary, Matrix.one_apply,
      PEquiv.toMatrix]

theorem label02Perm_unitary : permutation label02Perm = sumUnitary 1 (labelUnitary 2 (by decide)) := by
  apply Subtype.ext
  ext i j
  cases i <;> cases j <;>
    simp [permutation, label02Perm, sumUnitary, labelUnitary, Matrix.one_apply,
      PEquiv.toMatrix]

theorem label01Program_unitary :
    rewireUnitary labelWiring (programUnitary label01Program) =
      sumUnitary (labelUnitary 1 (by decide)) 1 := by
  rw [rewire_program_eq labelWiring label01Program label01Perm label01Perm_symm label01Program_run,
    label01Perm_unitary]

theorem label02Program_unitary :
    rewireUnitary labelWiring (programUnitary label02Program) =
      sumUnitary 1 (labelUnitary 2 (by decide)) := by
  rw [rewire_program_eq labelWiring label02Program label02Perm label02Perm_symm label02Program_run,
    label02Perm_unitary]

/-- These counts are lengths of the actual one/two-qubit gate lists. -/
theorem label_gate_counts :
    (GateSynthesis.lowerProgram label01Program).length = 36 ∧
    (GateSynthesis.lowerProgram label02Program).length = 34 := by
  norm_num [GateSynthesis.lowerProgram, label01Program, label02Program,
    GateSynthesis.lowerGate, ExactToffoli.circuit_length,
    show (0 : Fin 4) ≠ 2 from by decide, show (0 : Fin 4) ≠ 3 from by decide]

/-- Exact physical implementation, including every value of the borrowed bit. -/
theorem label01_elementary_matrix :
    TransducerCompiler.GateSynthesis.eval (GateSynthesis.lowerProgram label01Program) =
      TransducerCompiler.GateSynthesis.dataHom
        (rewireUnitary labelWiring.symm (sumUnitary (labelUnitary 1 (by decide)) 1)) := by
  rw [GateSynthesis.lowerProgram_eq, ← label01Program_unitary]
  congr 1
  apply Subtype.ext
  ext i j
  simp [rewireUnitary]

theorem label02_elementary_matrix :
    TransducerCompiler.GateSynthesis.eval (GateSynthesis.lowerProgram label02Program) =
      TransducerCompiler.GateSynthesis.dataHom
        (rewireUnitary labelWiring.symm (sumUnitary 1 (labelUnitary 2 (by decide)))) := by
  rw [GateSynthesis.lowerProgram_eq, ← label02Program_unitary]
  congr 1
  apply Subtype.ext
  ext i j
  simp [rewireUnitary]

end OptimalQLS.GraphEncoding
