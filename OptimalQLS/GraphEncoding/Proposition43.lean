import OptimalQLS.GraphEncoding.RealizedCircuit
import OptimalQLS.GraphEncoding.Geometry

/-! # Proposition4.3: one uniform physical Hermitian graph oracle -/
noncomputable section
set_option synthInstance.maxSize 2048
namespace OptimalQLS.GraphEncoding
open Matrix PolynomialTransform
open scoped Kronecker Matrix.Norms.L2Operator
variable {S D B : Type*} [Fintype S] [DecidableEq S]
  [Fintype D] [DecidableEq D] [Fintype B] [DecidableEq B]

abbrev PhysicalSignal (S : Type*) := Bool × Signal S

def physicalSignalZero (s : S) : PhysicalSignal S := (false,signalZero s)

/-- One borrowed synthesis bit plus the three construction bits; every wiring
operation here is only regrouping of already named physical registers. -/
def realizedPhysicalWiring (S D : Type*) :
    Bool × (BranchSpace S D ⊕ BranchSpace S D) ≃ PhysicalSignal S × (Fin 4 × D) :=
  (Equiv.prodCongr (Equiv.refl Bool) (physicalWiring S D)).trans
    (Equiv.prodAssoc Bool (Signal S) (Fin 4 × D)).symm

/-- The actual elementary-gate-expanded circuit, chosen before either input oracle. -/
def elementaryGraphCircuit (S D B : Type*) [Fintype S] [DecidableEq S]
    [Fintype D] [DecidableEq D] (κ : ℝ) (hκ : 0 < κ) :
    QueryCircuit (S × D) B (PhysicalSignal S × (Fin 4 × D)) :=
  (realizedSelectCircuit S D B κ hκ).lift (rewirePort (realizedPhysicalWiring S D))

def physicalEncoding (κ : ℝ) (hκ : 0 < κ) (U : Matrix.unitaryGroup (S × D) ℂ) :
    Matrix.unitaryGroup (PhysicalSignal S × (Fin 4 × D)) ℂ :=
  rewireUnitary (realizedPhysicalWiring S D)
    (borrow (weightedSelect κ hκ (branchA U) (branchI S D)))

theorem elementaryGraphCircuit_eval (κ : ℝ) (hκ : 0 < κ)
    (U : Matrix.unitaryGroup (S × D) ℂ) (Ub : Matrix.unitaryGroup B ℂ) :
    (elementaryGraphCircuit S D B κ hκ).eval U Ub = physicalEncoding κ hκ U := by
  rw [elementaryGraphCircuit, QueryCircuit.lift_eval, realizedSelectCircuit_eval, rewirePort_apply]
  rfl

theorem physicalEncoding_hermitian (κ : ℝ) (hκ : 0 < κ)
    (U : Matrix.unitaryGroup (S × D) ℂ) : (physicalEncoding κ hκ U).val.IsHermitian := by
  apply Matrix.IsHermitian.submatrix
  change ((1 : Matrix Bool Bool ℂ) ⊗ₖ
    (weightedSelect κ hκ (branchA U) (branchI S D)).val).IsHermitian
  rw [Matrix.IsHermitian, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    weightedSelect_hermitian κ hκ _ _ (branchA_hermitian U) branchI_hermitian]

/-- The borrowed synthesis bit is exactly untouched, even off its zero sector. -/
theorem physicalEncoding_entries (κ : ℝ) (hκ : 0 < κ)
    (U : Matrix.unitaryGroup (S × D) ℂ) (b c : Bool)
    (s t : Signal S) (i j : Fin 4 × D) :
    (physicalEncoding κ hκ U).val ((b,s),i) ((c,t),j) =
      (if b=c then 1 else 0) * (graphEncoding κ hκ U).val (s,i) (t,j) := by
  rfl

theorem physicalEncoding_block (κ : ℝ) (hκ : 0 < κ) (s : S)
    (U : Matrix.unitaryGroup (S × D) ℂ) :
    signalBlock (physicalSignalZero s) (physicalEncoding κ hκ U).val =
      signalBlock (signalZero s) (graphEncoding κ hκ U).val := by
  ext i j
  rw [signalBlock_entries, signalBlock_entries]
  change (physicalEncoding κ hκ U).val ((false,signalZero s),i) ((false,signalZero s),j) = _
  rw [physicalEncoding_entries]
  simp

theorem physicalEncoding_exact [Nonempty D] (κ : ℝ) (hκ : 0 < κ) (s : S)
    (U : Matrix.unitaryGroup (S × D) ℂ) (A : Matrix D D ℂ)
    (hA : A.IsHermitian) (henc : IsBlockEncoding s 1 0 U A) :
    IsBlockEncoding (physicalSignalZero s) (1+κ⁻¹) 0 (physicalEncoding κ hκ U) (graphMatrix A κ) := by
  have h := graphEncoding_exact κ hκ s U A hA henc
  simpa only [IsBlockEncoding, physicalEncoding_block] using h

theorem elementaryGraphCircuit_counts (κ : ℝ) (hκ : 0 < κ) :
    (elementaryGraphCircuit S D B κ hκ).matrixQueries=2 ∧
      (elementaryGraphCircuit S D B κ hκ).vectorQueries=0 ∧
      workInstructions (elementaryGraphCircuit S D B κ hκ)=76 := by
  simpa only [elementaryGraphCircuit, (QueryCircuit.lift_counts _ _).1,
    (QueryCircuit.lift_counts _ _).2, workInstructions_lift] using
      (realizedSelectCircuit_counts (S := S) (D := D) (B := B) κ hκ)

theorem physical_signal_qubits (a : ℕ) (hS : Fintype.card S = 2^a) :
    Fintype.card (PhysicalSignal S) = 2^(a+4) := by
  simp only [PhysicalSignal, Fintype.card_prod, Fintype.card_bool, signal_cardinality, hS]
  rw [pow_add]
  norm_num
  omega

/-- Concrete Proposition4.3. The witness circuit precedes all oracle values,
encodes the genuinely zero-padded Fin4 graph, and is globally Hermitian.
Its76 work instructions are expanded real elementary gates, including
borrowed-bit identity on all unprepared sectors. -/
theorem proposition4_3 [Nonempty D] (κ : ℝ) (hκ : 2 ≤ κ) (s : S) :
    ∃ c : QueryCircuit (S × D) B (PhysicalSignal S × (Fin 4 × D)),
      c.matrixQueries=2 ∧ c.vectorQueries=0 ∧ workInstructions c=76 ∧
      (∀ (a : ℕ), Fintype.card S=2^a → Fintype.card (PhysicalSignal S)=2^(a+4)) ∧
      ∀ (U : Matrix.unitaryGroup (S × D) ℂ) (Ub : Matrix.unitaryGroup B ℂ)
        (A : Matrix D D ℂ), A.IsHermitian → IsBlockEncoding s 1 0 U A →
        (c.eval U Ub).val.IsHermitian ∧
        IsBlockEncoding (physicalSignalZero s) (1+κ⁻¹) 0 (c.eval U Ub) (graphMatrix A κ) := by
  have hp : 0 < κ := by linarith
  refine ⟨elementaryGraphCircuit S D B κ hp, (elementaryGraphCircuit_counts κ hp).1,
    (elementaryGraphCircuit_counts κ hp).2.1, (elementaryGraphCircuit_counts κ hp).2.2,
    physical_signal_qubits, ?_⟩
  intro U Ub A hA henc
  rw [elementaryGraphCircuit_eval]
  exact ⟨physicalEncoding_hermitian κ hp U, physicalEncoding_exact κ hp s U A hA henc⟩

end OptimalQLS.GraphEncoding
