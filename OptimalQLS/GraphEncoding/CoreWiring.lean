import OptimalQLS.GraphEncoding.ControlledGates

/-! # The six graph-work qubits, with the original S×D entirely spectator -/
noncomputable section
set_option synthInstance.maxSize 2048
namespace OptimalQLS.GraphEncoding
open Matrix PolynomialTransform TransducerCompiler
variable {S D W K R : Type*} [Fintype S] [DecidableEq S] [Fintype D] [DecidableEq D]
  [Fintype W] [DecidableEq W] [Fintype K] [DecidableEq K] [Fintype R] [DecidableEq R]

def coreAssignment (z c l h b q : Bool) : CoreWire → Bool
  | none => z
  | some i => ![c,l,h,b,q] i

def coreLabels (x : CoreWire → Bool) : LabelBits :=
  ![x (some 0),x (some 1),x (some 2),x (some 3)]

def coreInner (x : CoreWire → Bool) (sd : S × D) : (S × D) ⊕ (S × D) :=
  if x (some 4) then .inr sd else .inl sd

/-- This equivalence only names the six already present qubits. -/
def coreWiring (S D : Type*) : ((CoreWire → Bool) × (S × D)) ≃
    Bool × (BranchSpace S D ⊕ BranchSpace S D) where
  toFun p := (p.1 none, (labelDistribution ((S × D) ⊕ (S × D)))
    (labelWiring (coreLabels p.1),coreInner p.1 p.2))
  invFun p := match p with
    | (z,.inl ((l,g),.inl sd)) =>
        (coreAssignment z false l (graphBits.symm g).1 (graphBits.symm g).2 false,sd)
    | (z,.inl ((l,g),.inr sd)) =>
        (coreAssignment z false l (graphBits.symm g).1 (graphBits.symm g).2 true,sd)
    | (z,.inr ((l,g),.inl sd)) =>
        (coreAssignment z true l (graphBits.symm g).1 (graphBits.symm g).2 false,sd)
    | (z,.inr ((l,g),.inr sd)) =>
        (coreAssignment z true l (graphBits.symm g).1 (graphBits.symm g).2 true,sd)
  left_inv p := by
    rcases p with ⟨x,sd⟩
    apply Prod.ext
    · funext i
      cases hc : x (some 0) <;> cases hq : x (some 4) <;>
        cases i with
        | none => simp [labelDistribution,labelWiring,coreLabels,coreInner,coreAssignment,hc,hq]
        | some i => fin_cases i <;> simp [labelDistribution,labelWiring,coreLabels,coreInner,coreAssignment,hc,hq]
    · cases hc : x (some 0) <;> cases hq : x (some 4) <;>
        simp [labelDistribution,labelWiring,coreLabels,coreInner,coreAssignment,hc,hq]
  right_inv p := by
    rcases p with ⟨z,p⟩
    rcases p with ⟨⟨l,g⟩,sd⟩|⟨⟨l,g⟩,sd⟩ <;> cases sd <;>
      simp [labelDistribution,labelWiring,coreLabels,coreInner,coreAssignment]

/-- Add an untouched borrowed bit to an existing target placement. -/
def borrowWiring (e : K × R ≃ W) : K × (Bool × R) ≃ Bool × W where
  toFun p := (p.2.1,e (p.1,p.2.2))
  invFun p := ((e.symm p.2).1,(p.1,(e.symm p.2).2))
  left_inv p := by rcases p with ⟨k,z,r⟩; simp
  right_inv p := by rcases p with ⟨z,w⟩; simp

theorem borrow_place (e : K × R ≃ W) (U : Matrix.unitaryGroup K ℂ) :
    borrow (TransducerCompiler.GateSynthesis.placeHom e U) =
      TransducerCompiler.GateSynthesis.placeHom (borrowWiring e) U := by
  apply Subtype.ext
  ext ⟨z,i⟩ ⟨r,j⟩
  simp [placeHom_entries, borrowWiring, borrow, tensorUnitary,
    HadamardClock.tensorUnitary, Matrix.one_apply]
  split_ifs <;> simp_all

theorem core_lower_input (x : CoreWire → Bool) (sd : S × D) :
    labelLowerWiring ((S × D) ⊕ (S × D)) ((x none,coreLabels x),coreInner x sd) =
      coreWiring S D (x,sd) := rfl

theorem core_borrowed_update (x : CoreWire → Bool) (sd : S × D) (y : Bool) :
    labelLowerWiring ((S × D) ⊕ (S × D)) ((y,coreLabels x),coreInner x sd) =
      coreWiring S D (Function.update x none y,sd) := by
  simp [coreWiring,labelLowerWiring,coreLabels,coreInner,Function.update_apply]

theorem core_label_update (x : CoreWire → Bool) (sd : S × D) (t : Fin 4) (y : Bool) :
    labelLowerWiring ((S × D) ⊕ (S × D))
      ((x none,Function.update (coreLabels x) t y),coreInner x sd) =
      coreWiring S D (Function.update x (labelCore t) y,sd) := by
  fin_cases t <;>
    simp [coreWiring,labelLowerWiring,coreLabels,coreInner,labelCore,labelWiring,
      Function.update_apply]

theorem core_select_input (x : CoreWire → Bool) (sd : S × D) :
    borrowWiring (sumBitWiring (BranchSpace S D))
      (x (some 0),(x none,((x (some 1),graphBits (x (some 2),x (some 3))),coreInner x sd))) =
      coreWiring S D (x,sd) := by
  cases h : x (some 0) <;> simp [borrowWiring,sumBitWiring,coreWiring,
    labelDistribution,labelWiring,coreLabels,h]

theorem core_select_update (x : CoreWire → Bool) (sd : S × D) (y : Bool) :
    borrowWiring (sumBitWiring (BranchSpace S D))
      (y,(x none,((x (some 1),graphBits (x (some 2),x (some 3))),coreInner x sd))) =
      coreWiring S D (Function.update x (some 0) y,sd) := by
  cases y <;> simp [borrowWiring,sumBitWiring,coreWiring,
    labelDistribution,labelWiring,coreLabels,coreInner,Function.update_apply]

theorem core_dilation_input (x : CoreWire → Bool) (sd : S × D) :
    borrowWiring (controlledBitWiring Label (S × D))
      ((x (some 4),x (some 0)),(x none,((x (some 1),graphBits (x (some 2),x (some 3))),sd))) =
      coreWiring S D (x,sd) := by
  cases hc : x (some 0) <;> cases hq : x (some 4) <;>
    simp [borrowWiring,controlledBitWiring,coreWiring,labelDistribution,labelWiring,
      coreLabels,coreInner,hc,hq]

theorem core_dilation_update (x : CoreWire → Bool) (sd : S × D) (y : Bool) :
    borrowWiring (controlledBitWiring Label (S × D))
      ((y,x (some 0)),(x none,((x (some 1),graphBits (x (some 2),x (some 3))),sd))) =
      coreWiring S D (Function.update x (some 4) y,sd) := by
  cases hc : x (some 0) <;> cases y <;>
    simp [borrowWiring,controlledBitWiring,coreWiring,labelDistribution,labelWiring,
      coreLabels,coreInner,Function.update_apply,hc]

end OptimalQLS.GraphEncoding
