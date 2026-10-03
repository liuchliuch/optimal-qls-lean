import OptimalQLS.Preparation.WorkGates.Endpoint
import OptimalQLS.Preparation.WorkGates.Factorization

/-! # Literal elementary implementation of the complete preparation work -/
noncomputable section
set_option maxHeartbeats 2000000
namespace OptimalQLS.Preparation.WorkGates
open Matrix TransducerCompiler BinaryClock PolynomialTransform DirtyAncilla
variable {D : Type*} [Fintype D] [DecidableEq D]

theorem matrixEval_nine {L : Type*} [Fintype L] [DecidableEq L]
    (M : Fin 9 → Matrix L L ℂ) :
    matrixEval (List.ofFn M)=M 8*M 7*M 6*M 5*M 4*M 3*M 2*M 1*M 0 := by
  simp only [List.ofFn_succ,List.ofFn_zero,matrixEval,Matrix.one_mul]
  rfl

theorem sourceWork_product {a : ℕ} {μ r : ℝ} (hμ : 0<μ) (hr : |r|<1)
    (external : Bool) :
    matrixEval (List.ofFn (fun k : Fin 9 => sourceFactor (D := D) (a := a) hμ hr external k))=
      (sourceWork hμ hr external).val := by
  have he : (List.ofFn (fun k : Fin 9 => sourceFactor (D := D) (a := a) hμ hr external k))=
      (List.ofFn (fun k : Fin 9 => workOperation (D := D) (fun _ : Fin a=>false) hμ hr k)).map
        (conditionalLift external) := by
    rw [List.map_ofFn]
    rfl
  rw [he,matrixEval_conditionalLift]
  change conditionalLift external _=conditionalLift external
    (preparationWork (signalProjector (D := D) (fun _ : Fin a=>false))
      (signalProjector_star _) (signalProjector_idempotent _) hμ hr).val
  apply congrArg (conditionalLift external)
  rw [matrixEval_nine]
  exact (preparationWork_factorization (D := D) (fun _ : Fin a=>false) hμ hr).symm

/-- Full coherent correctness of the actual elementary list for every source vector,
including arbitrary spectator data and labels5,6,7. The borrowed bit is arbitrary. -/
theorem workProgram_intertwines {a : ℕ} {μ r : ℝ} (hμ : 0<μ) (hr : |r|<1)
    (external : Bool) (dirty : Bool) :
    (physicalWork (D := D) (a := a) hμ hr external).val*basisInsertion (sourceInsertion dirty)=
      basisInsertion (sourceInsertion dirty)*(sourceWork hμ hr external).val := by
  rw [← sourceWork_product]
  exact physicalWork_product_intertwines hμ hr external dirty

theorem workProgram_coherent {a : ℕ} {μ r : ℝ} (hμ : 0<μ) (hr : |r|<1)
    (external : Bool) (dirty : Bool) (v : Source a D→ℂ) :
    (physicalWork hμ hr external).val *ᵥ (basisInsertion (sourceInsertion dirty) *ᵥ v)=
      basisInsertion (sourceInsertion dirty) *ᵥ ((sourceWork hμ hr external).val*ᵥv) := by
  rw [Matrix.mulVec_mulVec,workProgram_intertwines,Matrix.mulVec_mulVec]

/-- Even a borrowed bit entangled with the entire source is returned coherently. -/
theorem workProgram_borrowed_intertwines {a : ℕ} {μ r : ℝ} (hμ : 0<μ) (hr : |r|<1)
    (external : Bool) :
    (physicalWork (D := D) (a := a) hμ hr external).val *
        basisInsertion (fun x : Source a D × Bool=>sourceInsertion x.2 x.1)=
      basisInsertion (fun x : Source a D × Bool=>sourceInsertion x.2 x.1) *
        (GateSynthesis.placeHom (Equiv.refl (Source a D × Bool)) (sourceWork hμ hr external)).val := by
  exact intertwines_borrowed_matrix (fun dirty=>sourceInsertion dirty) _ _
    (fun dirty=>workProgram_intertwines hμ hr external dirty)

/-- The only extra scratch is two clean bits plus one unrestricted borrowed bit. -/
theorem scratch_card (a : ℕ) :
    Fintype.card (Wire (LogicalWire a)) + 1 = a+7 := by
  simp [Wire,LogicalWire,Fintype.card_sum]
  omega

/-- A single theorem bundles semantics with the literal elementary resource bounds. -/
theorem preparationWork_lowered {a : ℕ} {μ r : ℝ} (hμ : 0<μ) (hr : |r|<1)
    (external : Bool) (dirty : Bool) :
    (physicalWork (D := D) (a := a) hμ hr external).val*basisInsertion (sourceInsertion dirty)=
        basisInsertion (sourceInsertion dirty)*(sourceWork hμ hr external).val ∧
      (workProgram a hμ hr external).length ≤ 36495*(a+1) ∧
      (∀ g ∈ workProgram a hμ hr external, g.arity≤2 ∧ RealGate g) := by
  refine ⟨workProgram_intertwines hμ hr external dirty,workProgram_length a hμ hr external,?_⟩
  intro g hg
  exact ⟨PhaseGate.arity_le_two g,workProgram_real a hμ hr external g hg⟩

end OptimalQLS.Preparation.WorkGates
