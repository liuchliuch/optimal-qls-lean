import OptimalQLS.PolynomialTransform.DirtyAncilla.Many

/-! # Linear-size multi-control NOT with one globally borrowed wire -/
namespace OptimalQLS.PolynomialTransform.DirtyAncilla
open OptimalQLS.TransducerCompiler.BinaryClock

abbrev SmallWire (n : ℕ) := Fin n ⊕ Fin 2

def smallTarget (n : ℕ) : SmallWire n := .inr 0
def smallBorrowed (n : ℕ) : SmallWire n := .inr 1

/-- First group uses the other control group as local dirty storage. -/
def firstWiring (k r : ℕ) (h : k≤r+2) : ManyWire k → SmallWire (k+r)
  | .inl i => .inl ⟨i.val,by omega⟩
  | .inr (.inl j) => .inl ⟨k+j.val,by omega⟩
  | .inr (.inr _) => smallBorrowed (k+r)

theorem firstWiring_injective (k r : ℕ) (h : k≤r+2) : Function.Injective (firstWiring k r h) := by
  intro x y he
  rcases x with i | (i | u) <;> rcases y with j | (j | v)
  all_goals try cases u
  all_goals try cases v
  all_goals simp_all [firstWiring,smallBorrowed,Fin.ext_iff]
  all_goals omega

/-- Second group includes the borrowed bit as a control and borrows wires
from the restored first group. -/
def secondWiring (k r : ℕ) (h : r≤k+1) : ManyWire (r+1) → SmallWire (k+r)
  | .inl i => if h0 : i.val=0 then smallBorrowed (k+r) else .inl ⟨k+(i.val-1),by omega⟩
  | .inr (.inl j) => .inl ⟨j.val,by omega⟩
  | .inr (.inr _) => smallTarget (k+r)

theorem secondWiring_injective (k r : ℕ) (h : r≤k+1) : Function.Injective (secondWiring k r h) := by
  intro x y he
  rcases x with i | (i | u) <;> rcases y with j | (j | v)
  all_goals try cases u
  all_goals try cases v
  all_goals simp only [secondWiring] at he
  all_goals try split_ifs at he
  all_goals simp only [smallBorrowed,smallTarget,Sum.inl.injEq,Sum.inr.injEq,
    Sum.inl_ne_inr,Sum.inr_ne_inl,Fin.ext_iff] at he ⊢
  all_goals try { norm_num at he }
  all_goals try norm_num
  all_goals omega

def leftPredicate {k r : ℕ} (b : SmallWire (k+r) → Bool) : Bool :=
  decide (∀ i : Fin k, b (.inl ⟨i.val,by omega⟩)=true)

def rightPredicate {k r : ℕ} (b : SmallWire (k+r) → Bool) : Bool :=
  decide (∀ i : Fin r, b (.inl ⟨k+i.val,by omega⟩)=true)

@[simp] theorem leftPredicate_update {k r : ℕ} (b : SmallWire (k+r) → Bool) (i : Fin 2) (v : Bool) :
    leftPredicate (Function.update b (.inr i) v)=leftPredicate b := by
  simp [leftPredicate,Function.update_apply]

@[simp] theorem rightPredicate_update {k r : ℕ} (b : SmallWire (k+r) → Bool) (i : Fin 2) (v : Bool) :
    rightPredicate (Function.update b (.inr i) v)=rightPredicate b := by
  simp [rightPredicate,Function.update_apply]

theorem split_control_predicate {k r : ℕ} (b : SmallWire (k+r) → Bool) :
    (leftPredicate b && rightPredicate b)=decide (∀ i : Fin (k+r), b (.inl i)=true) := by
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true,leftPredicate,rightPredicate,decide_eq_true_eq]
  constructor
  · rintro ⟨hl,hr⟩ i
    by_cases hi : i.val<k
    · exact hl ⟨i.val,hi⟩
    · have he : k+(i.val-k)=i.val := by omega
      simpa only [he] using hr ⟨i.val-k,by omega⟩
  · intro h
    exact ⟨fun i => h ⟨i.val,by omega⟩,fun i => h ⟨k+i.val,by omega⟩⟩

def firstProgram (k r : ℕ) (h : k≤r+2) : Program (SmallWire (k+r)) :=
  mapProgram (firstWiring k r h) (firstWiring_injective k r h) (manyDirty k)

def secondProgram (k r : ℕ) (h : r≤k+1) : Program (SmallWire (k+r)) :=
  mapProgram (secondWiring k r h) (secondWiring_injective k r h) (manyDirty (r+1))

theorem firstProgram_run (k r : ℕ) (h : k≤r+2) (b : SmallWire (k+r) → Bool) :
    run (firstProgram k r h) b=Function.update b (smallBorrowed (k+r))
      (Bool.xor (b (smallBorrowed (k+r))) (leftPredicate b)) := by
  simpa only [firstProgram,firstWiring,manyTarget,leftPredicate] using
    mapped_manyDirty_run k (firstWiring k r h) (firstWiring_injective k r h) b

theorem secondProgram_run (k r : ℕ) (h : r≤k+1) (b : SmallWire (k+r) → Bool) :
    run (secondProgram k r h) b=Function.update b (smallTarget (k+r))
      (Bool.xor (b (smallTarget (k+r))) (b (smallBorrowed (k+r)) && rightPredicate b)) := by
  have hp : decide (∀ i : Fin (r+1), b (secondWiring k r h (.inl i))=true) =
      (b (smallBorrowed (k+r)) && rightPredicate b) := by
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq,Bool.and_eq_true,rightPredicate]
    constructor
    · intro hh
      constructor
      · simpa [secondWiring] using hh (0 : Fin (r+1))
      · intro i
        simpa [secondWiring] using hh ⟨i.val+1,by omega⟩
    · rintro ⟨hb,hr⟩ i
      by_cases hi : i.val=0
      · simpa [secondWiring,hi] using hb
      · simpa [secondWiring,hi] using hr ⟨i.val-1,by omega⟩
  have hh := mapped_manyDirty_run (r+1) (secondWiring k r h) (secondWiring_injective k r h) b
  rw [hp] at hh
  exact hh

/-- The four exact calls cancel the unknown borrowed bit, which is returned intact. -/
def balancedProgram (k r : ℕ) (hk : k≤r+2) (hr : r≤k+1) : Program (SmallWire (k+r)) :=
  firstProgram k r hk ++ secondProgram k r hr ++ firstProgram k r hk ++ secondProgram k r hr

theorem balancedProgram_run (k r : ℕ) (hk : k≤r+2) (hr : r≤k+1) (b : SmallWire (k+r) → Bool) :
    run (balancedProgram k r hk hr) b=Function.update b (smallTarget (k+r))
      (Bool.xor (b (smallTarget (k+r))) (decide (∀ i : Fin (k+r), b (.inl i)=true))) := by
  rw [balancedProgram,run_append,run_append,run_append,firstProgram_run,secondProgram_run,
    firstProgram_run,secondProgram_run]
  simp only [smallBorrowed,smallTarget,leftPredicate_update,rightPredicate_update]
  rw [← split_control_predicate b]
  ext w
  cases w with
  | inl i => simp [Function.update_apply]
  | inr i =>
    fin_cases i <;>
      cases ht : b (.inr 0) <;> cases hb : b (.inr 1) <;>
        cases hl : leftPredicate b <;> cases hr : rightPredicate b <;>
          simp [Function.update_apply,ht,hb,hl,hr]

theorem balancedProgram_length (k r : ℕ) (hk : k≤r+2) (hr : r≤k+1) :
    (balancedProgram k r hk hr).length ≤ 24*(k+r+1) := by
  have h1 := manyDirty_length k
  have h2 := manyDirty_length (r+1)
  simp only [balancedProgram,firstProgram,secondProgram,List.length_append,mapProgram_length]
  omega

end OptimalQLS.PolynomialTransform.DirtyAncilla
