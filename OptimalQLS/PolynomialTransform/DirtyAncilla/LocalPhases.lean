import OptimalQLS.PolynomialTransform.DirtyAncilla.ZeroTest
import OptimalQLS.PolynomialTransform.PhaseCircuit

/-! # Physically placed elementary complex phase gates -/
noncomputable section
namespace OptimalQLS.PolynomialTransform.DirtyAncilla
open Matrix OptimalQLS.TransducerCompiler
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A one-wire selection with every other physical bit explicitly retained. -/
def singleWiring (t : ι) :
    Bool × (Bool × ({i : ι // i ≠ t} → Bool)) ≃ GateSynthesis.Space ι where
  toFun p := (p.2.1, fun i => if h : i=t then p.1 else p.2.2 ⟨i,h⟩)
  invFun b := (b.2 t,b.1,fun i => b.2 i.val)
  left_inv p := by
    rcases p with ⟨x,z,r⟩
    simp only [ite_true]
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · rfl
      · funext i; simp [i.property]
  right_inv b := by
    apply Prod.ext
    · rfl
    · funext i; dsimp; split_ifs with h <;> simp_all

/-- Select two distinct physical wires and retain their spectator register. -/
def pairWiring (c t : ι) (hct : c ≠ t) :
    (Bool × Bool) × (Bool × ({i : ι // i ≠ c ∧ i ≠ t} → Bool)) ≃
      GateSynthesis.Space ι where
  toFun p := (p.2.1, fun i => if hc : i=c then p.1.1 else
    if ht : i=t then p.1.2 else p.2.2 ⟨i,hc,ht⟩)
  invFun b := ((b.2 c,b.2 t),b.1,fun i => b.2 i.val)
  left_inv p := by
    rcases p with ⟨⟨x,y⟩,z,r⟩
    apply Prod.ext
    · simp [hct,Ne.symm hct]
    · apply Prod.ext
      · rfl
      · funext i; simp [i.property.1,i.property.2]
  right_inv b := by
    apply Prod.ext
    · rfl
    · funext i; dsimp; split_ifs with hc ht <;> simp_all

/-- Tensor placement of a diagonal gate is the expected physical-coordinate phase. -/
theorem placeHom_diagonal {a b w : Type*} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b] [Fintype w] [DecidableEq w]
    (e : a × b ≃ w) (φ : a → Circle) :
    GateSynthesis.placeHom e (diagonalPhase φ)=diagonalPhase (fun x => φ (e.symm x).1) := by
  apply Subtype.ext
  change (Matrix.blockDiagonal (fun _ : b => (diagonalPhase φ).val)).submatrix e.symm e.symm = _
  ext i j
  by_cases hij : i=j
  · subst j
    simp [Matrix.blockDiagonal,Matrix.submatrix,diagonalPhase]
  · have hp : e.symm i ≠ e.symm j := fun h => hij (e.symm.injective h)
    have hpair : (e.symm i).1 ≠ (e.symm j).1 ∨ (e.symm i).2 ≠ (e.symm j).2 := by
      by_contra h
      push_neg at h
      exact hp (Prod.ext h.1 h.2)
    rcases hpair with h|h <;>
      simp [Matrix.blockDiagonal,Matrix.submatrix,diagonalPhase,hij,h]

def localPhase (t : ι) (φ : Bool → Circle) : Matrix.unitaryGroup (GateSynthesis.Space ι) ℂ :=
  GateSynthesis.placeHom (singleWiring t) (diagonalPhase φ)

theorem localPhase_eq (t : ι) (φ : Bool → Circle) :
    localPhase t φ=diagonalPhase (fun b => φ (b.2 t)) := by
  exact placeHom_diagonal (singleWiring t) φ

def localPairPhase (c t : ι) (hct : c ≠ t) (φ : Bool × Bool → Circle) :
    Matrix.unitaryGroup (GateSynthesis.Space ι) ℂ :=
  GateSynthesis.placeHom (pairWiring c t hct) (diagonalPhase φ)

theorem localPairPhase_eq (c t : ι) (hct : c ≠ t) (φ : Bool × Bool → Circle) :
    localPairPhase c t hct φ=diagonalPhase (fun b => φ (b.2 c,b.2 t)) := by
  exact placeHom_diagonal (pairWiring c t hct) φ

theorem diagonalPhase_basis {w : Type*} [Fintype w] [DecidableEq w]
    (φ : w → Circle) (b : w) :
    (diagonalPhase φ).val *ᵥ Pi.single b (1 : ℂ)=(φ b : ℂ) • (Pi.single b 1 : w → ℂ) := by
  ext i
  simp [diagonalPhase,Pi.single_apply]

/-- An elementary instruction is either a verified real lowering gate or one
complex one-qubit gate physically placed on a selected wire. -/
inductive PhaseGate (ι : Type*) where
  | real (g : GateSynthesis.LowerGate ι)
  | phase (t : ι) (φ : Bool → Circle)
  | pairPhase (c t : ι) (hct : c ≠ t) (φ : Bool × Bool → Circle)
  | single (t : ι) (U : Matrix.unitaryGroup Bool ℂ)
  | pair (c t : ι) (hct : c ≠ t) (U : Matrix.unitaryGroup (Bool × Bool) ℂ)

def PhaseGate.eval : PhaseGate ι → Matrix.unitaryGroup (GateSynthesis.Space ι) ℂ
  | .real g => g.eval
  | .phase t φ => localPhase t φ
  | .pairPhase c t hct φ => localPairPhase c t hct φ
  | .single t U => GateSynthesis.placeHom (singleWiring t) U
  | .pair c t hct U => GateSynthesis.placeHom (pairWiring c t hct) U

def PhaseGate.arity : PhaseGate ι → ℕ
  | .real g => g.arity
  | .phase _ _ => 1
  | .pairPhase _ _ _ _ => 2
  | .single _ _ => 1
  | .pair _ _ _ _ => 2

theorem PhaseGate.arity_le_two (g : PhaseGate ι) : g.arity ≤ 2 := by
  cases g with
  | real g => exact GateSynthesis.LowerGate.arity_le_two g
  | phase t φ => simp [arity]
  | pairPhase c t hct φ => simp [arity]
  | single t U => simp [arity]
  | pair c t hct U => simp [arity]

def phaseEval : List (PhaseGate ι) → Matrix.unitaryGroup (GateSynthesis.Space ι) ℂ
  | [] => 1
  | g::gs => phaseEval gs * g.eval

theorem phaseEval_append (c d : List (PhaseGate ι)) :
    phaseEval (c++d)=phaseEval d * phaseEval c := by
  induction c with
  | nil => simp [phaseEval]
  | cons g c ih => simp [phaseEval,ih,mul_assoc]

theorem phaseEval_real (c : List (GateSynthesis.LowerGate ι)) :
    phaseEval (c.map PhaseGate.real)=GateSynthesis.eval c := by
  induction c with
  | nil => rfl
  | cons g c ih => simp [phaseEval,GateSynthesis.eval,PhaseGate.eval,ih]

end OptimalQLS.PolynomialTransform.DirtyAncilla
