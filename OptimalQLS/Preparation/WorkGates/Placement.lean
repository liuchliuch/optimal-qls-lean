import OptimalQLS.Preparation.WorkGates.Refinement
import OptimalQLS.Preparation.WorkGates.Foundations

/-! # Physical control placement of the nine preparation factors -/
noncomputable section
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace OptimalQLS.Preparation.WorkGates
open Matrix TransducerCompiler BinaryClock PolynomialTransform DirtyAncilla

abbrev LogicalWire (a : ℕ) := Fin 3 ⊕ (Fin a ⊕ Unit)
abbrev LogicalBits (a : ℕ) := LogicalWire a → Bool

def selectedLabel (k : Fin 9) (i : Fin 3) : Prop :=
  (![i=0 ∨ i=2, i=2, i=1 ∨ i=2, i=0 ∨ i=2,
      i=1 ∨ i=2, i=0 ∨ i=1, i=1 ∨ i=2, i=1 ∨ i=2, i=1 ∨ i=2] k)
instance (k : Fin 9) (i : Fin 3) : Decidable (selectedLabel k i) := by
  exact Classical.propDecidable _

def selected {a : ℕ} (external : Bool) (k : Fin 9) : LogicalWire a → Prop
  | .inl i => selectedLabel k i
  | .inr (.inl _) => k=0 ∨ k=1
  | .inr (.inr _) => external=true
instance {a : ℕ} (external : Bool) (k : Fin 9) (i : LogicalWire a) :
    Decidable (selected external k i) := by
  cases i with
  | inl i => exact inferInstanceAs (Decidable (selectedLabel k i))
  | inr i => cases i <;> dsimp [selected] <;> infer_instance

abbrev Controls (a : ℕ) (external : Bool) (k : Fin 9) :=
  {i : LogicalWire a // selected external k i}

def controls {a : ℕ} (external : Bool) (k : Fin 9) :
    Fin (Fintype.card (Controls a external k)) → LogicalWire a :=
  fun i => ((Fintype.equivFin (Controls a external k)).symm i).val

theorem controls_injective {a : ℕ} (external : Bool) (k : Fin 9) :
    Function.Injective (controls (a := a) external k) :=
  Subtype.val_injective.comp (Fintype.equivFin (Controls a external k)).symm.injective

def pattern {a : ℕ} (k : Fin 9) : LogicalWire a → Bool
  | .inl i => decide ((k=0 ∧ i=0) ∨ (k=2 ∧ i=1))
  | .inr (.inl _) => false
  | .inr (.inr _) => true

def target {a : ℕ} (k : Fin 9) : LogicalWire a := .inl (labelTarget k)

theorem controls_ne_target {a : ℕ} (external : Bool) (k : Fin 9) :
    ∀ i, controls (a := a) external k i ≠ target k := by
  intro i h
  have hs := ((Fintype.equivFin (Controls a external k)).symm i).property
  change selected external k (controls external k i) at hs
  rw [h] at hs
  fin_cases k <;> norm_num [selected,target,labelTarget,selectedLabel,Fin.ext_iff] at hs

theorem controls_card_le (a : ℕ) (external : Bool) (k : Fin 9) :
    Fintype.card (Controls a external k) ≤ a+4 := by
  have h := Fintype.card_subtype_le (selected (a := a) external k)
  simpa [LogicalWire,Fintype.card_sum,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using h

def workFactor {a : ℕ} {μ r : ℝ} (hμ : 0<μ) (hr : |r|<1)
    (external : Bool) (k : Fin 9) : List (PhaseGate (Wire (LogicalWire a))) :=
  targetProgram (controls external k) (controls_injective external k)
    (pattern k) (target k) (labelGate hμ hr k)

def workProgram (a : ℕ) {μ r : ℝ} (hμ : 0<μ) (hr : |r|<1)
    (external : Bool) : List (PhaseGate (Wire (LogicalWire a))) :=
  (List.ofFn (fun k : Fin 9 => workFactor (a := a) hμ hr external k)).flatten

theorem workFactor_length {a : ℕ} {μ r : ℝ} (hμ : 0<μ) (hr : |r|<1)
    (external : Bool) (k : Fin 9) : (workFactor (a := a) hμ hr external k).length ≤ 811*(a+5) := by
  have h := targetProgram_length (controls (a := a) external k) (controls_injective external k)
    (pattern k) (target k) (labelGate hμ hr k)
  have hc := controls_card_le a external k
  exact h.trans (by omega)

theorem workProgram_length (a : ℕ) {μ r : ℝ} (hμ : 0<μ) (hr : |r|<1)
    (external : Bool) : (workProgram a hμ hr external).length ≤ 36495*(a+1) := by
  have h := fun k : Fin 9 => workFactor_length (a := a) hμ hr external k
  simp only [workProgram,List.length_flatten,List.map_ofFn,List.sum_ofFn]
  calc
    ∑ k : Fin 9, (workFactor (a := a) hμ hr external k).length ≤
        ∑ _k : Fin 9, 811*(a+5) := Finset.sum_le_sum (fun k _ => h k)
    _ ≤ 36495*(a+1) := by simp; omega

theorem workProgram_arity (a : ℕ) {μ r : ℝ} (hμ : 0<μ) (hr : |r|<1)
    (external : Bool) (g : PhaseGate (Wire (LogicalWire a)))
    (_hg : g ∈ workProgram a hμ hr external) : g.arity ≤ 2 := PhaseGate.arity_le_two g

theorem workProgram_real (a : ℕ) {μ r : ℝ} (hμ : 0<μ) (hr : |r|<1)
    (external : Bool) : ∀ g ∈ workProgram a hμ hr external, RealGate g := by
  intro g hg
  obtain ⟨l,hl,hg⟩ := List.mem_flatten.mp hg
  obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hl
  exact targetProgram_real (controls external k) (controls_injective external k)
    (pattern k) (target k) (labelGate hμ hr k) (labelGate_real hμ hr k) g hg

/-- A literal computational register equivalence, with no change of basis. -/
def logicalEquiv (a : ℕ) : LogicalBits a ≃ (Fin 8 × Bits a) × Bool where
  toFun b := ((labelEquiv.symm (fun i => b (.inl i)),fun i => b (.inr (.inl i))),b (.inr (.inr ())))
  invFun b := Sum.elim (labelBits b.1.1) (Sum.elim b.1.2 (fun _ => b.2))
  left_inv b := by
    funext i
    cases i with
    | inl i => exact congrFun (labelEquiv.apply_symm_apply (fun j => b (.inl j))) i
    | inr i => cases i with
      | inl i => rfl
      | inr i => cases i; rfl
  right_inv b := by
    rcases b with ⟨⟨j,s⟩,c⟩
    change ((labelEquiv.symm (labelEquiv j),s),c)=((j,s),c)
    rw [labelEquiv.symm_apply_apply]

theorem controls_match_iff {a : ℕ} (external : Bool) (k : Fin 9) (b : LogicalBits a) :
    (∀ i, b (controls external k i)=pattern k (controls external k i)) ↔
      ∀ w : LogicalWire a, selected external k w → b w=pattern k w := by
  constructor
  · intro h w hw
    simpa only [controls,Equiv.symm_apply_apply] using
      h ((Fintype.equivFin (Controls a external k)) ⟨w,hw⟩)
  · intro h i
    exact h _ ((Fintype.equivFin (Controls a external k)).symm i).property

theorem controls_match {a : ℕ} (external : Bool) (k : Fin 9) (j : Fin 8) (s : Bits a) (c : Bool) :
    decide (∀ i, ((logicalEquiv a).symm ((j,s),c)) (controls external k i)=
      pattern k (controls external k i)) =
      ((!external || c) && labelControl k (decide (s=fun _ => false)) j) := by
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq,controls_match_iff]
  fin_cases k <;> fin_cases j <;> cases external <;> cases c <;>
    simp [selected,selectedLabel,logicalEquiv,pattern,labelControl,labelBits,
      Fin.forall_fin_succ,funext_iff]

theorem logicalEquiv_update (a : ℕ) (j : Fin 8) (s : Bits a) (c : Bool) (t : Fin 3) (y : Bool) :
    Function.update ((logicalEquiv a).symm ((j,s),c)) (.inl t) y =
      (logicalEquiv a).symm ((labelEquiv.symm (Function.update (labelBits j) t y),s),c) := by
  funext i
  cases i with
  | inl i =>
    change Function.update (Sum.elim (labelBits j) _) (.inl t) y (.inl i)=
      labelBits (labelEquiv.symm (Function.update (labelBits j) t y)) i
    have h := congrFun (labelEquiv.apply_symm_apply (Function.update (labelBits j) t y)) i
    change labelBits (labelEquiv.symm (Function.update (labelBits j) t y)) i =
      Function.update (labelBits j) t y i at h
    rw [h]
    simp [Function.update_apply]
  | inr i => cases i <;> simp [logicalEquiv,Function.update_apply]

end OptimalQLS.Preparation.WorkGates
