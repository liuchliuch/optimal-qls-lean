import OptimalQLS.Preparation.WorkGates.Complete
import OptimalQLS.Refinement.CostedExecution.RealLocality

/-! # Literal controlled kernel-reflection work, for every positive mixing parameter

Only the first four preparation factors are emitted. The source equality retains
all eight label sectors and every signal column. Work is chosen without an oracle.
-/
noncomputable section
namespace OptimalQLS.KernelReflectionPhysical
open Matrix TransducerCompiler BinaryClock PolynomialTransform DirtyAncilla
open Preparation Preparation.WorkGates Refinement.CostedExecution
set_option maxHeartbeats 1200000

private theorem zero_lt_one : |(0 : ℝ)| < 1 := by norm_num

/-- Literal execution order of the four kernel factors. -/
def factors : List (Fin 9) := [0,1,2,3]

/-- The actual emitted list depends only on signal width, μ, and external control. -/
def workProgram (a : ℕ) {μ : ℝ} (hμ : 0<μ) (external : Bool) :
    List (PhaseGate (Wire (LogicalWire a))) :=
  (factors.map (workFactor (a := a) hμ zero_lt_one external)).flatten

set_option maxHeartbeats 150000 in
/-- The preparation-only parameter has no influence on any emitted kernel gate. -/
theorem first_four_independent (a : ℕ) {μ r : ℝ} (hμ : 0<μ) (hr : |r|<1)
    (external : Bool) :
    workProgram a hμ external =
      (factors.map (workFactor (a := a) hμ hr external)).flatten := by
  have hg (k : Fin 9) (hk : k ∈ factors) :
      labelGate hμ zero_lt_one k=labelGate hμ hr k := by
    simp only [factors,List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl|rfl|rfl|rfl <;> simp [labelGate]
  have hm : factors.map (workFactor (a := a) hμ zero_lt_one external) =
      factors.map (workFactor (a := a) hμ hr external) :=
    List.map_congr_left (fun k hk =>
      congrArg (fun U : Matrix.unitaryGroup Bool ℂ =>
        targetProgram (controls (a := a) external k) (controls_injective external k)
          (pattern k) (target k) U) (hg k hk))
  exact congrArg List.flatten hm

/-- The controlled padded kernel work. Labels0,4,5,6,7 are spectators. -/
def sourceWork {a : ℕ} {D : Type*} [Fintype D] [DecidableEq D]
    {μ : ℝ} (hμ : 0<μ) (external : Bool) : Matrix.unitaryGroup (Source a D) ℂ :=
  controlledOn (fun c : Bool => !external || c)
    (kernelWork8 (signalProjector (D := D) (fun _ : Fin a=>false))
      (signalProjector_star _) (signalProjector_idempotent _) hμ)

def physicalWork {a : ℕ} {D : Type*} [Fintype D] [DecidableEq D]
    {μ : ℝ} (hμ : 0<μ) (external : Bool) : Matrix.unitaryGroup (Physical a D) ℂ :=
  GateSynthesis.placeHom (Equiv.refl _) (phaseEval (workProgram a hμ external))

variable {D : Type*} [Fintype D] [DecidableEq D]

theorem four_factor_product {a : ℕ} {μ : ℝ} (hμ : 0<μ) :
    matrixEval (factors.map (workOperation (D := D) (fun _ : Fin a=>false)
      hμ zero_lt_one)) =
      (kernelWork8 (signalProjector (D := D) (fun _ : Fin a=>false))
        (signalProjector_star _) (signalProjector_idempotent _) hμ).val := by
  simp only [factors,List.map_cons,List.map_nil,matrixEval,Matrix.one_mul,
    workOperation,fiberMatrix_mul]
  rw [kernelWork8_fiber]
  congr 1
  funext x
  exact kernel_four_factorization hμ zero_lt_one _

theorem sourceWork_product {a : ℕ} {μ : ℝ} (hμ : 0<μ) (external : Bool) :
    matrixEval (factors.map (sourceFactor (D := D) (a := a) hμ zero_lt_one external)) =
      (sourceWork hμ external).val := by
  have he : factors.map (sourceFactor (D := D) (a := a) hμ zero_lt_one external) =
      (factors.map (workOperation (D := D) (fun _ : Fin a=>false) hμ zero_lt_one)).map
        (conditionalLift external) := by
    rw [List.map_map]
    rfl
  rw [he,matrixEval_conditionalLift,four_factor_product]
  rfl

/-- Full coherent action, for every source column and either borrowed-bit value. -/
theorem workProgram_intertwines {a : ℕ} {μ : ℝ} (hμ : 0<μ)
    (external dirty : Bool) :
    (physicalWork (D := D) (a := a) hμ external).val * basisInsertion (sourceInsertion dirty) =
      basisInsertion (sourceInsertion dirty) * (sourceWork hμ external).val := by
  have aux (l : List (Fin 9)) :
      (GateSynthesis.placeHom (Equiv.refl (Physical a D))
        (phaseEval ((l.map (workFactor (a := a) hμ zero_lt_one external)).flatten))).val *
          basisInsertion (sourceInsertion dirty) =
      basisInsertion (sourceInsertion dirty) *
        matrixEval (l.map (sourceFactor hμ zero_lt_one external)) := by
    induction l with
    | nil => simp [phaseEval,matrixEval]
    | cons k l ih =>
      simp only [List.map_cons,List.flatten_cons,phaseEval_append,map_mul,Submonoid.coe_mul,
        matrixEval]
      exact intertwines_mul _ _ _ _ _
        (physicalFactor_intertwines hμ zero_lt_one external k dirty) ih
  simpa only [physicalWork,workProgram,sourceWork_product] using aux factors

theorem workProgram_coherent {a : ℕ} {μ : ℝ} (hμ : 0<μ)
    (external dirty : Bool) (v : Source a D → ℂ) :
    (physicalWork hμ external).val *ᵥ (basisInsertion (sourceInsertion dirty) *ᵥ v) =
      basisInsertion (sourceInsertion dirty) *ᵥ ((sourceWork hμ external).val *ᵥ v) := by
  rw [Matrix.mulVec_mulVec,workProgram_intertwines,Matrix.mulVec_mulVec]

/-- The borrowed bit can be entangled with the complete logical source. -/
theorem workProgram_borrowed_intertwines {a : ℕ} {μ : ℝ} (hμ : 0<μ)
    (external : Bool) :
    (physicalWork (D := D) (a := a) hμ external).val *
        basisInsertion (fun x : Source a D × Bool => sourceInsertion x.2 x.1) =
      basisInsertion (fun x : Source a D × Bool => sourceInsertion x.2 x.1) *
        (GateSynthesis.placeHom (Equiv.refl (Source a D × Bool)) (sourceWork hμ external)).val :=
  intertwines_borrowed_matrix (fun dirty => sourceInsertion dirty) _ _
    (fun dirty => workProgram_intertwines hμ external dirty)

theorem workProgram_length (a : ℕ) {μ : ℝ} (hμ : 0<μ) (external : Bool) :
    (workProgram a hμ external).length ≤ 16220*(a+1) := by
  have h0 := workFactor_length (a := a) hμ zero_lt_one external 0
  have h1 := workFactor_length (a := a) hμ zero_lt_one external 1
  have h2 := workFactor_length (a := a) hμ zero_lt_one external 2
  have h3 := workFactor_length (a := a) hμ zero_lt_one external 3
  simp only [workProgram,factors,List.map_cons,List.map_nil,List.flatten_cons,
    List.flatten_nil,List.length_append,List.length_nil]
  omega

theorem workProgram_real (a : ℕ) {μ : ℝ} (hμ : 0<μ) (external : Bool) :
    ∀ g ∈ workProgram a hμ external, RealGate g := by
  intro g hg
  obtain ⟨l,hl,hg⟩ := List.mem_flatten.mp hg
  obtain ⟨k,_,rfl⟩ := List.mem_map.mp hl
  exact targetProgram_real (controls external k) (controls_injective external k)
    (pattern k) (target k) (labelGate hμ zero_lt_one k)
    (labelGate_real hμ zero_lt_one k) g hg

/-- This is a genuine tensor-locality theorem on literal physical wires,
not an arity annotation. It includes the reusable synthesis bit. -/
theorem workProgram_local (a : ℕ) {μ : ℝ} (hμ : 0<μ) (external : Bool)
    (g : PhaseGate (Wire (LogicalWire a))) (_hg : g ∈ workProgram a hμ external) :
    IsTwoLocal phaseBits g.eval := phase_leaf_local g

/-- Real, semantic one/two-bit gates and an explicit linear work bound. -/
theorem kernelWork_lowered {a : ℕ} {μ : ℝ} (hμ : 0<μ) (external dirty : Bool) :
    (physicalWork (D := D) (a := a) hμ external).val * basisInsertion (sourceInsertion dirty) =
        basisInsertion (sourceInsertion dirty) * (sourceWork hμ external).val ∧
      (workProgram a hμ external).length ≤ 16220*(a+1) ∧
      (∀ g ∈ workProgram a hμ external, RealGate g ∧ IsTwoLocal phaseBits g.eval) ∧
      Fintype.card (Wire (LogicalWire a)) + 1 = a+7 := by
  refine ⟨workProgram_intertwines hμ external dirty,workProgram_length a hμ external,?_,
    scratch_card a⟩
  intro g hg
  exact ⟨workProgram_real a hμ external g hg,workProgram_local a hμ external g hg⟩

end OptimalQLS.KernelReflectionPhysical
