import OptimalQLS.PhysicalPadding.Basis
import OptimalQLS.TransducerCompiler.HadamardClock
import OptimalQLS.PolynomialTransform.PhysicalPhases
import OptimalQLS.GraphEncoding.ElementaryLocality

/-!
# Binary physical data registers and unchanged synthesis counts

The data wiring is the existing low-first binary equivalence, not an arbitrary
choice of a finite-type equivalence.  Register sizes below are actual finite
cardinalities.  The final synthesis theorems specialize the already constructed
circuits: padding introduces no new test on a data qubit or new gate-cost model.
-/

noncomputable section
set_option synthInstance.maxSize 2048
set_option maxHeartbeats 800000
namespace OptimalQLS.PhysicalPadding

open Matrix PolynomialTransform TransducerCompiler HadamardClock DirtyAncilla

/-- Literal low-first binary coordinates of the complete physical data register. -/
def physicalDataCoordinates (d : ℕ) : Bits (dataQubits d) ≃ Fin (physicalDimension d) :=
  bitsFinEquiv (dataQubits d)

@[simp] theorem physicalDataCoordinates_zero (d : ℕ) :
    physicalDataCoordinates d (fun _ => false) = 0 :=
  bitsFinEquiv_zero (dataQubits d)

@[simp] theorem physicalDataCoordinates_symm_zero (d : ℕ) :
    (physicalDataCoordinates d).symm 0 = (fun _ => false) := by
  apply (physicalDataCoordinates d).injective
  simp

/-- The fixed active computational labels, expressed as physical data bits. -/
def activeDataBits (d : ℕ) : Fin d ↪ Bits (dataQubits d) :=
  (activeIndex d).trans (physicalDataCoordinates d).symm.toEmbedding

@[simp] theorem physicalDataCoordinates_activeDataBits (d : ℕ) (i : Fin d) :
    physicalDataCoordinates d (activeDataBits d i) = activeIndex d i := by
  simp [activeDataBits]

@[simp] theorem activeDataBits_zero (d : ℕ) [NeZero d] :
    activeDataBits d 0 = (fun _ => false) := by
  apply (physicalDataCoordinates d).injective
  simp

/-- Every active computational coordinate uses its ordinary low-first digits. -/
theorem activeDataBits_apply (d : ℕ) (i : Fin d) (k : Fin (dataQubits d)) :
    activeDataBits d i k = Nat.testBit i.val k.val :=
  bitsFinEquiv_symm_apply (dataQubits d) (activeIndex d i) k

/-- Binary signal and binary data wiring, with their register boundary explicit. -/
def oracleRegisterCoordinates (a d : ℕ) :
    Bits a × Bits (dataQubits d) ≃ SignalIndex a × Fin (physicalDimension d) :=
  Equiv.prodCongr (bitsFinEquiv a) (physicalDataCoordinates d)

@[simp] theorem oracleRegisterCoordinates_zero (a d : ℕ) :
    oracleRegisterCoordinates a d ((fun _ => false), (fun _ => false)) = (0, 0) := by
  simp [oracleRegisterCoordinates, bitsFinEquiv_zero]

/-- The graph register is two literal binary labels alongside all data bits. -/
def graphRegisterCoordinates (d : ℕ) :
    Bits 2 × Bits (dataQubits d) ≃ Fin 4 × Fin (physicalDimension d) :=
  Equiv.prodCongr (bitsFinEquiv 2) (physicalDataCoordinates d)

@[simp] theorem graphRegisterCoordinates_zero (d : ℕ) :
    graphRegisterCoordinates d ((fun _ => false), (fun _ => false)) = (0, 0) := by
  apply Prod.ext
  · exact bitsFinEquiv_zero 2
  · exact physicalDataCoordinates_zero d

theorem physical_data_cardinality (d : ℕ) :
    Fintype.card (Fin (physicalDimension d)) = 2 ^ dataQubits d := by
  simp [physicalDimension]

theorem physical_oracle_cardinality (a d : ℕ) :
    Fintype.card (SignalIndex a × Fin (physicalDimension d)) =
      2 ^ (a + dataQubits d) := by
  simp [SignalIndex, physicalDimension, Fintype.card_prod, pow_add]

theorem physical_graph_cardinality (d : ℕ) :
    Fintype.card (Fin 4 × Fin (physicalDimension d)) = 2 ^ (dataQubits d + 2) := by
  simp [physicalDimension, Fintype.card_prod, pow_add, Nat.mul_comm]

/-- The abstract graph construction adds three signal bits. -/
theorem graph_signal_cardinality (a : ℕ) :
    Fintype.card (GraphEncoding.Signal (SignalIndex a)) = 2 ^ (a + 3) :=
  GraphEncoding.signal_qubits a (by simp [SignalIndex])

/-- The elementary graph construction includes its borrowed synthesis bit. -/
theorem physical_graph_signal_cardinality (a : ℕ) :
    Fintype.card (GraphEncoding.PhysicalSignal (SignalIndex a)) = 2 ^ (a + 4) :=
  GraphEncoding.physical_signal_qubits a (by simp [SignalIndex])

theorem graph_total_cardinality (a d : ℕ) :
    Fintype.card (GraphEncoding.Signal (SignalIndex a) ×
      (Fin 4 × Fin (physicalDimension d))) = 2 ^ (a + dataQubits d + 5) := by
  rw [Fintype.card_prod, graph_signal_cardinality, physical_graph_cardinality,
    ← pow_add]
  congr 1
  omega

theorem physical_graph_total_cardinality (a d : ℕ) :
    Fintype.card (GraphEncoding.PhysicalSignal (SignalIndex a) ×
      (Fin 4 × Fin (physicalDimension d))) = 2 ^ (a + dataQubits d + 6) := by
  rw [Fintype.card_prod, physical_graph_signal_cardinality, physical_graph_cardinality,
    ← pow_add]
  congr 1
  omega

/-- The already implemented polynomial-transform register adds five signal bits. -/
theorem physical_qsvt_signal_cardinality (a : ℕ) :
    Fintype.card (PolynomialTransform.PhysicalSignal a) = 2 ^ (a + 5) :=
  PolynomialTransform.physical_signal_cardinality a

theorem physical_qsvt_total_cardinality (a d : ℕ) :
    Fintype.card (PolynomialTransform.PhysicalSignal a × Fin (physicalDimension d)) =
      2 ^ (a + dataQubits d + 5) := by
  rw [Fintype.card_prod, physical_qsvt_signal_cardinality, physical_data_cardinality,
    ← pow_add]
  congr 1
  omega

/-- Applying the existing polynomial transform to the elementary graph oracle
has a+4 input signal bits, its five synthesis bits, and n+2 graph/data bits. -/
theorem physical_graph_qsvt_total_cardinality (a d : ℕ) :
    Fintype.card (PolynomialTransform.PhysicalSignal (a + 4) ×
      (Fin 4 × Fin (physicalDimension d))) = 2 ^ (a + dataQubits d + 11) := by
  rw [Fintype.card_prod, physical_qsvt_signal_cardinality, physical_graph_cardinality,
    ← pow_add]
  congr 1
  omega

/-- Padding changes neither query count nor the existing literal work list. -/
theorem physical_graph_circuit_counts (a d : ℕ) (κ : ℝ) (hκ : 0 < κ) :
    (GraphEncoding.elementaryGraphCircuit (SignalIndex a) (Fin (physicalDimension d))
      (Fin (physicalDimension d)) κ hκ).matrixQueries = 2 ∧
    (GraphEncoding.elementaryGraphCircuit (SignalIndex a) (Fin (physicalDimension d))
      (Fin (physicalDimension d)) κ hκ).vectorQueries = 0 ∧
    workInstructions
      (GraphEncoding.elementaryGraphCircuit (SignalIndex a) (Fin (physicalDimension d))
        (Fin (physicalDimension d)) κ hκ) = 76 :=
  GraphEncoding.elementaryGraphCircuit_counts κ hκ

/-- The same signal-only phase code works on every physical data dimension.
Its length depends on a, not n; the exact matrix equation leaves the data as a
spectator and does not introduce an active-subspace or data-zero test. -/
theorem physical_phase_synthesis (a d : ℕ) (branch : Bool) (z w : Circle) :
    (physicalPhaseCode a branch z w).length ≤ 781 * (a + 1) ∧
    (elementaryPlacement (D := Fin (physicalDimension d))
      (phaseEval (physicalPhaseCode a branch z w))).val * basisInsertion (physicalClean a) =
      basisInsertion (physicalClean a) *
        (logicalPhase (D := Fin (physicalDimension d)) a branch z w).val :=
  ⟨physicalPhaseCode_length a branch z w,
    physicalPhase_intertwines a branch z w⟩

end OptimalQLS.PhysicalPadding
