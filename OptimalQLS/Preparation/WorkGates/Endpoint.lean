import OptimalQLS.Preparation.WorkGates.Semantics

/-! # Actual preparation-work endpoint and one-bit control -/
noncomputable section
namespace OptimalQLS.Preparation.WorkGates
open Matrix TransducerCompiler BinaryClock PolynomialTransform DirtyAncilla
variable {D : Type*} [Fintype D] [DecidableEq D]

def conditionalLift {L : Type*} [Fintype L] [DecidableEq L]
    (external : Bool) (M : Matrix L L ℂ) : Matrix (L × Bool) (L × Bool) ℂ :=
  Matrix.blockDiagonal (fun c : Bool => if !external || c then M else 1)

theorem conditionalLift_one {L : Type*} [Fintype L] [DecidableEq L] (external : Bool) :
    conditionalLift external (1 : Matrix L L ℂ)=1 := by
  unfold conditionalLift
  simp only [ite_self]
  exact Matrix.blockDiagonal_one

theorem conditionalLift_mul {L : Type*} [Fintype L] [DecidableEq L]
    (external : Bool) (M N : Matrix L L ℂ) :
    conditionalLift external (M*N)=conditionalLift external M*conditionalLift external N := by
  unfold conditionalLift
  rw [← Matrix.blockDiagonal_mul]
  congr 1
  funext c
  split_ifs <;> simp

theorem matrixEval_conditionalLift {L : Type*} [Fintype L] [DecidableEq L]
    (external : Bool) (l : List (Matrix L L ℂ)) :
    matrixEval (l.map (conditionalLift external))=conditionalLift external (matrixEval l) := by
  induction l with
  | nil => simp [matrixEval,conditionalLift_one]
  | cons M l ih => simp only [List.map_cons,matrixEval,ih,conditionalLift_mul]

/-- The full preparation unitary, controlled by exactly one existing cache bit.
Setting external=false makes that bit an untouched spectator. -/
def sourceWork {a : ℕ} {μ r : ℝ} (hμ : 0<μ) (hr : |r|<1)
    (external : Bool) : Matrix.unitaryGroup (Source a D) ℂ :=
  controlledOn (fun c : Bool => !external || c)
    (preparationWork (signalProjector (D := D) (fun _ : Fin a=>false))
      (signalProjector_star _) (signalProjector_idempotent _) hμ hr)

theorem sourceWork_true {a : ℕ} {μ r : ℝ} (hμ : 0<μ) (hr : |r|<1) :
    sourceWork (D := D) (a := a) hμ hr true =
      controlledOn (fun c : Bool=>c)
        (preparationWork (signalProjector (D := D) (fun _ : Fin a=>false))
          (signalProjector_star _) (signalProjector_idempotent _) hμ hr) := by
  simp [sourceWork]

theorem sourceWork_false {a : ℕ} {μ r : ℝ} (hμ : 0<μ) (hr : |r|<1) :
    sourceWork (D := D) (a := a) hμ hr false =
      GateSynthesis.placeHom (Equiv.refl _)
        (preparationWork (signalProjector (D := D) (fun _ : Fin a=>false))
          (signalProjector_star _) (signalProjector_idempotent _) hμ hr) := by
  apply Subtype.ext
  rfl

/-- A pointwise-clean implementation preserves an arbitrarily entangled borrowed bit. -/
theorem intertwines_borrowed_matrix {L P : Type*} [Fintype L] [DecidableEq L]
    [Fintype P] [DecidableEq P] (f : Bool → L → P)
    (U : Matrix P P ℂ) (V : Matrix L L ℂ)
    (h : ∀ dirty, U*basisInsertion (f dirty)=basisInsertion (f dirty)*V) :
    U*basisInsertion (fun x : L×Bool=>f x.2 x.1)=
      basisInsertion (fun x : L×Bool=>f x.2 x.1)*Matrix.blockDiagonal (fun _ : Bool=>V) := by
  ext p ⟨x,dirty⟩
  have hh := congrFun (congrFun (h dirty) p) x
  simpa [Matrix.mul_apply,basisInsertion,Fintype.sum_prod_type,Matrix.blockDiagonal,ite_and] using hh

end OptimalQLS.Preparation.WorkGates
