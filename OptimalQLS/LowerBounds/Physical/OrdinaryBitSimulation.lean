import OptimalQLS.LowerBounds.Physical.UncontrolledBitCircuit

/-! Compile an entire query list to ordinary, forward, uncontrolled bit calls. -/
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 4096
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
namespace OptimalQLS.LowerBounds.Physical
open Matrix PolynomialTransform
variable {W : Type*} [Fintype W] [DecidableEq W]

/-- Every matrix query is a forward call with no control; there is no second oracle. -/
def OrdinaryBitQueries {m : ℕ} : QueryCircuit (BitBasis m) Unit W → Prop
  | [] => True
  | .work _ :: c => OrdinaryBitQueries c
  | .matrixCall p adj :: c => (∀ i, p.control i = true) ∧ adj = false ∧ OrdinaryBitQueries c
  | .vectorCall _ _ :: _ => False

theorem ordinaryBitQueries_append {m : ℕ} (c d : QueryCircuit (BitBasis m) Unit W) :
    OrdinaryBitQueries (c++d) ↔ OrdinaryBitQueries c ∧ OrdinaryBitQueries d := by
  induction c with
  | nil => simp [OrdinaryBitQueries]
  | cons g c ih => cases g <;> simp [OrdinaryBitQueries, ih, and_assoc]

def removeBitControlInstruction {m : ℕ} :
    QueryInstruction (BitBasis m) Unit W → QueryCircuit (BitBasis m) Unit (W × Bool)
  | .work U => [.work ((scratchPort (Equiv.refl (W × Bool))).apply U)]
  | .matrixCall p _ => uncontrolledBitCall p
  | .vectorCall _ _ => [.work 1]

def removeBitControlCircuit {m : ℕ} (c : QueryCircuit (BitBasis m) Unit W) :
    QueryCircuit (BitBasis m) Unit (W × Bool) := c.flatMap removeBitControlInstruction

theorem removeBitControlInstruction_clean {m : ℕ} (g : QueryInstruction (BitBasis m) Unit W)
    (z : BitString m) :
    ((removeBitControlInstruction g).eval (standardBitOracle z) 1).val *
      basisInsertion (fun w : W => (w,false)) =
      basisInsertion (fun w : W => (w,false)) * (g.eval (standardBitOracle z) 1).val := by
  cases g with
  | work U =>
    simp only [removeBitControlInstruction, QueryCircuit.eval, QueryInstruction.eval, one_mul]
    exact scratchPort_intertwines (Equiv.refl (W × Bool)) false U
  | matrixCall p adj => exact uncontrolledBitCall_clean p adj z
  | vectorCall p adj =>
    have h1 : p.apply (1 : Matrix.unitaryGroup Unit ℂ) = 1 := p.unitaryHom.map_one
    simp [removeBitControlInstruction, QueryCircuit.eval, QueryInstruction.eval, h1]

theorem removeBitControlCircuit_clean {m : ℕ} (c : QueryCircuit (BitBasis m) Unit W)
    (z : BitString m) :
    ((removeBitControlCircuit c).eval (standardBitOracle z) 1).val *
      basisInsertion (fun w : W => (w,false)) =
      basisInsertion (fun w : W => (w,false)) * (c.eval (standardBitOracle z) 1).val := by
  induction c with
  | nil => simp [removeBitControlCircuit, QueryCircuit.eval]
  | cons g c ih =>
    simp only [removeBitControlCircuit, List.flatMap_cons, QueryCircuit.eval_append]
    change _ * basisInsertion (fun w : W => (w,false)) =
      basisInsertion (fun w : W => (w,false)) *
        ((QueryCircuit.eval (standardBitOracle z) 1 c).val * (g.eval (standardBitOracle z) 1).val)
    exact intertwines_mul _ _ _ _ _ (removeBitControlInstruction_clean g z) ih

theorem removeBitControlInstruction_ordinary {m : ℕ} (g : QueryInstruction (BitBasis m) Unit W) :
    OrdinaryBitQueries (removeBitControlInstruction g) := by
  cases g <;> simp [removeBitControlInstruction, uncontrolledBitCall, OrdinaryBitQueries]

theorem removeBitControlCircuit_ordinary {m : ℕ} (c : QueryCircuit (BitBasis m) Unit W) :
    OrdinaryBitQueries (removeBitControlCircuit c) := by
  induction c with
  | nil => trivial
  | cons g c ih =>
    rw [removeBitControlCircuit, List.flatMap_cons, ordinaryBitQueries_append]
    exact ⟨removeBitControlInstruction_ordinary g,ih⟩

theorem removeBitControlCircuit_counts {m : ℕ} (c : QueryCircuit (BitBasis m) Unit W) :
    (removeBitControlCircuit c).matrixQueries = 2*c.matrixQueries ∧
      (removeBitControlCircuit c).vectorQueries = 0 := by
  induction c with
  | nil => exact ⟨rfl,rfl⟩
  | cons g c ih =>
    cases g <;>
      simp_all [removeBitControlCircuit, removeBitControlInstruction, uncontrolledBitCall,
        QueryCircuit.matrixQueries_append, QueryCircuit.vectorQueries_append,
        QueryCircuit.matrixQueries, QueryCircuit.vectorQueries, Nat.mul_add, Nat.add_comm, Nat.add_assoc]
    omega

/-- Clean computational embeddings compose as literal rectangular matrices. -/
theorem basisInsertion_comp {D P Q : Type*} [Fintype P] [DecidableEq P] [DecidableEq Q]
    (f : P → Q) (g : D → P) : basisInsertion f * basisInsertion g = basisInsertion (f ∘ g) := by
  ext i j
  simp [basisInsertion, Matrix.mul_apply]

/-- Entire UA queries, with every outer control and adjoint, compiled down to
exactly eight ordinary calls to the literal XOR bit oracle. -/
theorem proposition64_ordinary_query_simulation {N m : ℕ} [NeZero N] [NeZero m] {kappa : ℝ}
    (hk : 4 ≤ kappa) (hN : N = 2 * historyPadding kappa + 2 * m)
    (p : QueryPort (Bool × HardFamilyIndex N) W) (adjoint : Bool) :
    let c := removeBitControlCircuit (simulatedQuery p adjoint (hardFamilyBitCircuit hk hN))
    OrdinaryBitQueries c ∧ c.matrixQueries = 8 ∧ c.vectorQueries = 0 ∧
    ∀ z : BitString m,
      (c.eval (standardBitOracle z) 1).val *
        basisInsertion (fun w => (queryClean (hardOracleClean (N := N) (m := m)) p w,false)) =
      basisInsertion (fun w => (queryClean (hardOracleClean (N := N) (m := m)) p w,false)) *
        (p.apply (if adjoint then (hardFamilyEncoding (N := N) hk z)⁻¹ else hardFamilyEncoding hk z)).val := by
  dsimp only
  refine ⟨removeBitControlCircuit_ordinary _, ?_, (removeBitControlCircuit_counts _).2, ?_⟩
  · rw [(removeBitControlCircuit_counts _).1, (proposition64_query_simulation hk hN p adjoint).1]
  · intro z
    let f := queryClean (hardOracleClean (N := N) (m := m)) p
    let c := simulatedQuery p adjoint (hardFamilyBitCircuit hk hN)
    have h₁ := removeBitControlCircuit_clean c z
    have h₂ := (proposition64_query_simulation hk hN p adjoint).2.2 z
    have hj : basisInsertion (fun w => (f w,false)) =
        basisInsertion (fun x => (x,false)) * basisInsertion f := by
      exact (basisInsertion_comp (fun x : (Bool × HardSimulationData N m) × Fin p.multiplicity =>
        (x,false)) (f : W → (Bool × HardSimulationData N m) × Fin p.multiplicity)).symm
    rw [hj, ← Matrix.mul_assoc, h₁, Matrix.mul_assoc, h₂, ← Matrix.mul_assoc]

/-- The additional response register is a genuine clean ancillary qubit. -/
theorem proposition64_ordinary_query_clean_isometry {N m : ℕ} [NeZero m]
    (p : QueryPort (Bool × HardFamilyIndex N) W) :
    (basisInsertion (fun w => (queryClean (hardOracleClean (N := N) (m := m)) p w,false)))ᴴ *
      basisInsertion (fun w => (queryClean (hardOracleClean (N := N) (m := m)) p w,false)) = 1 := by
  apply basisInsertion_isometry
  intro x y h
  exact (queryClean _ p).injective (congrArg Prod.fst h)

/-- Active extraction recovers the literal entire requested query unitary. -/
theorem proposition64_ordinary_query_extraction {N m : ℕ} [NeZero N] [NeZero m] {kappa : ℝ}
    (hk : 4 ≤ kappa) (hN : N = 2 * historyPadding kappa + 2 * m)
    (p : QueryPort (Bool × HardFamilyIndex N) W) (adjoint : Bool) (z : BitString m) :
    let c := removeBitControlCircuit (simulatedQuery p adjoint (hardFamilyBitCircuit hk hN))
    let J := basisInsertion (fun w => (queryClean (hardOracleClean (N := N) (m := m)) p w,false))
    Jᴴ * (c.eval (standardBitOracle z) 1).val * J =
      (p.apply (if adjoint then (hardFamilyEncoding (N := N) hk z)⁻¹ else hardFamilyEncoding hk z)).val := by
  dsimp only
  rw [Matrix.mul_assoc, (proposition64_ordinary_query_simulation hk hN p adjoint).2.2.2 z,
    ← Matrix.mul_assoc, proposition64_ordinary_query_clean_isometry, Matrix.one_mul]

end OptimalQLS.LowerBounds.Physical
