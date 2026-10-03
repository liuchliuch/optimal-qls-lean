import OptimalQLS.TransducerCompiler.BinaryClock.Gates
import Mathlib.Tactic

/-!
# A concrete multi-control NOT ladder with borrowed dirty bits

With n+3 controls, n+1 borrowed bits, and one target, two compute-toggle-
uncompute passes cancel all dependence on the dirty bits. Every borrowed
bit is restored, and the program has linear primitive-gate length.
-/
namespace OptimalQLS.PolynomialTransform.DirtyAncilla
open OptimalQLS.TransducerCompiler.BinaryClock

abbrev Wire (n : ℕ) := Fin (n+3) ⊕ (Fin (n+1) ⊕ Unit)
abbrev State (n : ℕ) := Wire n → Bool

def control {n : ℕ} (i : Fin (n+3)) : Wire n := .inl i
def borrowed {n : ℕ} (i : Fin (n+1)) : Wire n := .inr (.inl i)
def target (n : ℕ) : Wire n := .inr (.inr ())

def controlBit {n : ℕ} (b : State n) (i : ℕ) : Bool :=
  if hi : i<n+3 then b (control ⟨i,hi⟩) else false

def dirtyBit {n : ℕ} (b : State n) (i : ℕ) : Bool :=
  if hi : i<n+1 then b (borrowed ⟨i,hi⟩) else false

def prefixAnd {n : ℕ} (b : State n) : ℕ → Bool
  | 0 => true
  | i+1 => prefixAnd b i && controlBit b i

def dirtyValue {n : ℕ} (full : Bool) (b : State n) : ℕ → Bool
  | 0 => Bool.xor (dirtyBit b 0) (if full then controlBit b 0 && controlBit b 1 else false)
  | i+1 => Bool.xor (dirtyBit b (i+1)) (dirtyValue full b i && controlBit b (i+2))

def partialState {n : ℕ} (r : ℕ) (full : Bool) (b : State n) : State n
  | .inl i => b (.inl i)
  | .inr (.inl i) => if i.val<r then dirtyValue full b i.val else b (.inr (.inl i))
  | .inr (.inr _) => b (target n)

@[simp] theorem partialState_zero {n : ℕ} (full : Bool) (b : State n) : partialState 0 full b=b := by
  ext w
  rcases w with i | (i | u)
  · rfl
  · simp [partialState]
  · cases u
    rfl

/-- First Toffoli is included only in the full pass; the later ladder is shared. -/
def ladderStep {n : ℕ} (full : Bool) (i : Fin (n+1)) : Program (Wire n) :=
  if h0 : i.val=0 then
    if full then [.ccx (control ⟨0,by omega⟩) (control ⟨1,by omega⟩) (borrowed i) (by simp [control,borrowed]) (by simp [control,borrowed])]
    else []
  else
    [.ccx (borrowed ⟨i.val-1,by omega⟩) (control ⟨i.val+1,by omega⟩) (borrowed i)
      (by
        intro he
        have hv := congrArg Fin.val (Sum.inl.inj (Sum.inr.inj he))
        dsimp at hv
        omega)
      (by simp [control,borrowed])]

theorem ladderStep_length {n : ℕ} (full : Bool) (i : Fin (n+1)) : (ladderStep full i).length ≤ 1 := by
  unfold ladderStep
  split <;> cases full <;> simp

/-- Each listed Toffoli advances the explicit dirty-register invariant. -/
theorem ladderStep_partial {n : ℕ} (full : Bool) (i : Fin (n+1)) (b : State n) :
    run (ladderStep full i) (partialState i.val full b)=partialState (i.val+1) full b := by
  by_cases h0 : i.val=0
  · have hi : i=(0 : Fin (n+1)) := Fin.ext h0
    subst i
    cases full <;>
      ext w <;> rcases w with j | (j | u)
    all_goals try cases u
    all_goals simp [ladderStep,run,Gate.act,partialState,control,borrowed,target,
      Function.update_apply,dirtyValue,dirtyBit,controlBit]
    all_goals try { intro hj; subst j; simp [dirtyValue,dirtyBit,borrowed] }
    all_goals try { by_cases hj : j=0 <;> simp [hj,dirtyValue,dirtyBit,controlBit,borrowed,control] }
  · ext w
    rcases w with j | (j | u)
    · simp [ladderStep,h0,run,Gate.act,partialState,control,borrowed,Function.update_apply]
    · by_cases hji : j=i
      · subst j
        have hi : i.val=(i.val-1)+1 := by omega
        have hv : i.val - 1 < i.val := by omega
        simp only [ladderStep,dif_neg h0,run_cons,run_nil,Gate.act]
        simp only [borrowed,control,Function.update_self,partialState,ite_false,lt_self_iff_false]
        rw [if_pos (by omega : i.val < i.val + 1)]
        conv_rhs => rw [hi,dirtyValue]
        have hm : i.val-1<n := by omega
        have hplus : i.val-1+2=i.val+1 := by omega
        simp [partialState,hv,dirtyBit,controlBit,hm,← hi,hplus,borrowed,control,
          show i.val ≤ n by omega,show i.val < n+2 by omega]
      · have hv : j.val ≠ i.val := fun h => hji (Fin.ext h)
        have hh : j.val < i.val + 1 ↔ j.val < i.val := by omega
        simp [ladderStep,h0,run,Gate.act,partialState,control,borrowed,Function.update_apply,hji,hh]
    · cases u
      simp [ladderStep,h0,run,Gate.act,partialState,control,borrowed,target,Function.update_apply]

def compute {n : ℕ} (full : Bool) : (r : ℕ) → r≤n+1 → Program (Wire n)
  | 0,_ => []
  | r+1,hr => compute full r (by omega) ++ ladderStep full ⟨r,by omega⟩

theorem compute_run {n : ℕ} (full : Bool) (r : ℕ) (hr : r≤n+1) (b : State n) :
    run (compute full r hr) b=partialState r full b := by
  induction r with
  | zero => simp [compute]
  | succ r ih => rw [compute,run_append,ih,ladderStep_partial]

theorem compute_length {n : ℕ} (full : Bool) (r : ℕ) (hr : r≤n+1) :
    (compute full r hr).length ≤ r := by
  induction r with
  | zero => simp [compute]
  | succ r ih =>
    rw [compute,List.length_append]
    have hs := ladderStep_length full (⟨r,by omega⟩ : Fin (n+1))
    have hh := ih (by omega)
    omega

theorem dirtyValue_update_target {n : ℕ} (full : Bool) (b : State n) (v : Bool) (i : ℕ) :
    dirtyValue full (Function.update b (target n) v) i=dirtyValue full b i := by
  induction i with
  | zero => simp [dirtyValue,dirtyBit,controlBit,control,borrowed,target,Function.update_apply]
  | succ i ih =>
    rw [dirtyValue,dirtyValue,ih]
    simp [dirtyBit,controlBit,control,borrowed,target,Function.update_apply]

theorem partialState_update_target {n : ℕ} (full : Bool) (b : State n) (v : Bool) (r : ℕ) :
    partialState r full (Function.update b (target n) v)=Function.update (partialState r full b) (target n) v := by
  ext w
  rcases w with i | (i | u)
  · simp [partialState,target,Function.update_apply]
  · simp only [partialState]
    rw [dirtyValue_update_target]
    simp [target,Function.update_apply,partialState]
  · cases u
    simp [partialState,target]

theorem compute_update_target {n : ℕ} (full : Bool) (r : ℕ) (hr : r≤n+1) (b : State n) (v : Bool) :
    run (compute full r hr) (Function.update b (target n) v)=
      Function.update (run (compute full r hr) b) (target n) v := by
  rw [compute_run,compute_run,partialState_update_target]

theorem reverse_compute_update {n : ℕ} (full : Bool) (r : ℕ) (hr : r≤n+1) (b : State n) (v : Bool) :
    run (compute full r hr).reverse (Function.update (run (compute full r hr) b) (target n) v)=
      Function.update b (target n) v := by
  rw [← compute_update_target,run_reverse_run]

/-- Both passes are built only from literal primitive gates. -/
def sandwich (n : ℕ) (full : Bool) : Program (Wire n) :=
  compute full (n+1) le_rfl ++
    [.ccx (borrowed ⟨n,by omega⟩) (control ⟨n+2,by omega⟩) (target n)
      (by simp [borrowed,target]) (by simp [control,target])] ++
    (compute full (n+1) le_rfl).reverse

theorem sandwich_run {n : ℕ} (full : Bool) (b : State n) :
    run (sandwich n full) b=Function.update b (target n)
      (Bool.xor (b (target n)) (dirtyValue full b n && controlBit b (n+2))) := by
  unfold sandwich
  rw [run_append,run_append]
  have hg : run [.ccx (borrowed ⟨n,by omega⟩) (control ⟨n+2,by omega⟩) (target n)
      (by simp [borrowed,target]) (by simp [control,target])]
      (run (compute full (n+1) le_rfl) b) =
    Function.update (run (compute full (n+1) le_rfl) b) (target n)
      (Bool.xor (b (target n)) (dirtyValue full b n && controlBit b (n+2))) := by
    rw [compute_run]
    simp [run,Gate.act,partialState,borrowed,control,target,controlBit]
  rw [hg,reverse_compute_update]

theorem xor_dirty_cancel (a u v c : Bool) :
    Bool.xor (Bool.xor a (u&&c)) (Bool.xor a (v&&c)) = ((Bool.xor u v) && c) := by
  cases a <;> cases u <;> cases v <;> cases c <;> rfl

theorem dirtyValue_difference {n : ℕ} (b : State n) (i : ℕ) :
    Bool.xor (dirtyValue true b i) (dirtyValue false b i)=prefixAnd b (i+2) := by
  induction i with
  | zero =>
    simp only [dirtyValue,prefixAnd,Bool.false_eq_true,ite_false,Bool.true_eq,ite_true,Bool.xor_false,Bool.true_and]
    cases dirtyBit b 0 <;> cases controlBit b 0 <;> cases controlBit b 1 <;> rfl
  | succ i ih =>
    rw [dirtyValue,dirtyValue,xor_dirty_cancel,ih]
    rfl

/-- All dirty dependence cancels between the two exact reversible passes. -/
def dirtyControlledNot (n : ℕ) : Program (Wire n) := sandwich n true ++ sandwich n false

theorem dirtyControlledNot_run (n : ℕ) (b : State n) :
    run (dirtyControlledNot n) b=Function.update b (target n)
      (Bool.xor (b (target n)) (prefixAnd b (n+3))) := by
  rw [dirtyControlledNot,run_append,sandwich_run,sandwich_run]
  simp only [Function.update_self,dirtyValue_update_target]
  have hc : controlBit (Function.update b (target n)
      (Bool.xor (b (target n)) (dirtyValue true b n && controlBit b (n+2)))) (n+2)=controlBit b (n+2) := by
    simp [controlBit,control,target,Function.update_apply]
  rw [hc,Function.update_idem]
  congr 1
  have hid (a u v c : Bool) : Bool.xor (Bool.xor a (u&&c)) (v&&c)=Bool.xor a ((Bool.xor u v)&&c) := by
    cases a <;> cases u <;> cases v <;> cases c <;> rfl
  rw [hid,dirtyValue_difference]
  rfl

theorem dirtyControlledNot_length (n : ℕ) : (dirtyControlledNot n).length ≤ 4*(n+3) := by
  have ht := compute_length (n := n) true (n+1) le_rfl
  have hf := compute_length (n := n) false (n+1) le_rfl
  simp only [dirtyControlledNot,sandwich,List.length_append,List.length_reverse,List.length_cons,List.length_nil]
  omega

/-- The iterated conjunction is exactly the predicate on all designated controls. -/
theorem prefixAnd_characterization {n : ℕ} (b : State n) (r : ℕ) (hr : r≤n+3) :
    prefixAnd b r=true ↔ ∀ i : Fin (n+3), i.val < r → b (control i)=true := by
  induction r with
  | zero => simp [prefixAnd]
  | succ r ih =>
    rw [prefixAnd,Bool.and_eq_true,ih (by omega)]
    have hrlt : r < n+3 := by omega
    simp only [controlBit,dif_pos hrlt]
    constructor
    · rintro ⟨hp,hlast⟩ i hi
      by_cases he : i.val=r
      · have hi' : i=⟨r,hrlt⟩ := Fin.ext he
        simpa only [hi'] using hlast
      · exact hp i (by omega)
    · intro h
      exact ⟨fun i hi => h i (by omega),h ⟨r,hrlt⟩ (by simp)⟩

theorem prefixAnd_full {n : ℕ} (b : State n) :
    prefixAnd b (n+3)=decide (∀ i : Fin (n+3), b (control i)=true) := by
  apply Bool.eq_iff_iff.mpr
  rw [prefixAnd_characterization b (n+3) le_rfl]
  simp only [decide_eq_true_eq]
  exact ⟨fun h i => h i i.isLt,fun h i _ => h i⟩


end OptimalQLS.PolynomialTransform.DirtyAncilla
