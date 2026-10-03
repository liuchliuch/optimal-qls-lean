import OptimalQLS.LowerBounds.Physical.SimulationAlgebra

/-! The complete augmented and Hermitian-dilated oracle uses four bit queries. -/
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 4096
set_option maxRecDepth 2048
set_option linter.unusedSectionVars false
namespace OptimalQLS.LowerBounds.Physical
open Matrix PolynomialTransform

abbrev AuxiliaryData (m : ℕ) := BitBasis m × Unit
abbrev AugmentedSimulationData (N m : ℕ) := AuxiliaryData m ⊕ (SimulationBasis N m ⊕ AuxiliaryData m)
abbrev HardSimulationData (N m : ℕ) := AugmentedSimulationData N m ⊕ AugmentedSimulationData N m

def trivialPort (W : Type*) [Fintype W] [DecidableEq W] : QueryPort Unit W :=
  scratchPort (Equiv.uniqueProd W Unit)

def auxiliaryCoordinates (m : ℕ) : (Bool × Unit) × BitBasis m ≃ Bool × AuxiliaryData m where
  toFun x := (x.1.1,x.2,x.1.2)
  invFun x := ((x.1,x.2.2),x.2.1)
  left_inv _ := rfl
  right_inv _ := rfl

def auxiliaryBitCoordinates (m : ℕ) : BitBasis m × (Bool × Unit) ≃ Bool × AuxiliaryData m where
  toFun x := (x.2.1,x.1,x.2.2)
  invFun x := (x.2.1,x.1,x.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

def auxiliaryBitPort (m : ℕ) : QueryPort (BitBasis m) (Bool × AuxiliaryData m) :=
  scratchPort (auxiliaryBitCoordinates m)

def auxiliaryEncoding (m : ℕ) (U : Matrix.unitaryGroup (Bool × Unit) ℂ) :
    Matrix.unitaryGroup (Bool × AuxiliaryData m) ℂ :=
  (scratchPort (auxiliaryCoordinates m)).apply U

def auxiliaryClean {m : ℕ} [NeZero m] : Unit ↪ AuxiliaryData m :=
  ⟨fun x => ((0,false),x), by intro x y h; exact congrArg Prod.snd h⟩

theorem auxiliaryEncoding_clean {m : ℕ} [NeZero m] (U : Matrix.unitaryGroup (Bool × Unit) ℂ) :
    (auxiliaryEncoding m U).val * basisInsertion (fun x : Bool × Unit => (x.1,auxiliaryClean x.2)) =
      basisInsertion (fun x : Bool × Unit => (x.1,auxiliaryClean x.2)) * U.val :=
  scratchPort_intertwines (auxiliaryCoordinates m) (0,false) U

def historySignalBitPort (N m : ℕ) : QueryPort (BitBasis m) (Bool × SimulationBasis N m) :=
  (scratchPort (Equiv.prodComm (SimulationBasis N m) Bool)).comp (historyBitPort N m)

def signalSumPort {A D E : Type*} (p : QueryPort A (Bool × D)) (q : QueryPort A (Bool × E)) :
    QueryPort A (Bool × (D ⊕ E)) :=
  { sumPort p q with wiring := (sumPort p q).wiring.trans (distributeSignalSum Bool D E) }

def augmentedBitPort (N m : ℕ) : QueryPort (BitBasis m) (Bool × AugmentedSimulationData N m) :=
  signalSumPort (auxiliaryBitPort m) (signalSumPort (historySignalBitPort N m) (auxiliaryBitPort m))

def historyEncodingBitCircuit {N m : ℕ} [NeZero N] [NeZero m] {kappa : ℝ}
    (hk : 4 ≤ kappa) (hN : N = 2 * historyPadding kappa + 2 * m) :
    QueryCircuit (BitBasis m) Unit (Bool × SimulationBasis N m) :=
  lcuCircuit (historyBitPort N m) (trivialPort _)
    (historyBitCircuit (parityHistoryLabel (historyPadding_pos hk) hN))
    (lcuMixingParameter (historyLambda kappa)) (lcuMixingParameter_bound (historyLambda_pos hk))

def augmentedBitCircuit {N m : ℕ} [NeZero N] [NeZero m] {kappa : ℝ}
    (hk : 4 ≤ kappa) (hN : N = 2 * historyPadding kappa + 2 * m) :
    QueryCircuit (BitBasis m) Unit (Bool × AugmentedSimulationData N m) :=
  sumEncodingLeftCircuit (auxiliaryBitPort m) (trivialPort _) (auxiliaryEncoding m 1)
    (sumEncodingRightCircuit (auxiliaryBitPort m) (trivialPort _)
      (historyEncodingBitCircuit hk hN)
      (auxiliaryEncoding m (scalarEncoding kappa⁻¹ (kappa_inv_abs_lt_one hk))))

/-- Four standard-bit calls in the controlled-query model, with all other
gates independent of z. OrdinaryBitSimulation gives eight uncontrolled calls. -/
def hardFamilyBitCircuit {N m : ℕ} [NeZero N] [NeZero m] {kappa : ℝ}
    (hk : 4 ≤ kappa) (hN : N = 2 * historyPadding kappa + 2 * m) :
    QueryCircuit (BitBasis m) Unit (Bool × HardSimulationData N m) :=
  dilationCircuit (augmentedBitPort N m) (trivialPort _) (augmentedBitCircuit hk hN)

def augmentedClean {N m : ℕ} [NeZero m] : AugmentedIndex (HistoryBasis N) ↪ AugmentedSimulationData N m :=
  auxiliaryClean.sumMap (historyClean.sumMap auxiliaryClean)

def hardFamilyClean {N m : ℕ} [NeZero m] : HardFamilyIndex N ↪ HardSimulationData N m :=
  augmentedClean.sumMap augmentedClean

def hardOracleClean {N m : ℕ} [NeZero m] : (Bool × HardFamilyIndex N) ↪ (Bool × HardSimulationData N m) :=
  (Function.Embedding.refl Bool).prodMap hardFamilyClean

theorem historyEncodingBitCircuit_clean {N m : ℕ} [NeZero N] [NeZero m] {kappa : ℝ}
    (hk : 4 ≤ kappa) (hN : N = 2 * historyPadding kappa + 2 * m) (z : BitString m) :
    ((historyEncodingBitCircuit hk hN).eval (standardBitOracle z) 1).val *
      basisInsertion (fun x : Bool × HistoryBasis N => (x.1,historyClean (m := m) x.2)) =
      basisInsertion (fun x : Bool × HistoryBasis N => (x.1,historyClean (m := m) x.2)) *
        (historyBlockEncoding (fixedParityProfile (N := N) (historyPadding kappa) z)
          (historyLambda kappa) (historyLambda_pos hk)).val := by
  rw [historyEncodingBitCircuit, lcuCircuit_eval]
  exact twoTermLCU_intertwines historyClean _ _
    (historyBitCircuit_clean (historyPadding_pos hk) hN z) _ _

/-- Exact clean-scratch agreement with the complete previously constructed UA,
not merely agreement of its signal block or its prepared state. -/
theorem hardFamilyBitCircuit_clean {N m : ℕ} [NeZero N] [NeZero m] {kappa : ℝ}
    (hk : 4 ≤ kappa) (hN : N = 2 * historyPadding kappa + 2 * m) (z : BitString m) :
    ((hardFamilyBitCircuit hk hN).eval (standardBitOracle z) 1).val * basisInsertion (hardOracleClean (N := N) (m := m)) =
      basisInsertion (hardOracleClean (N := N) (m := m)) * (hardFamilyEncoding (N := N) hk z).val := by
  rw [hardFamilyBitCircuit, dilationCircuit_eval, augmentedBitCircuit,
    sumEncodingLeftCircuit_eval, sumEncodingRightCircuit_eval]
  apply dilationEncoding_intertwines augmentedClean
  apply sumEncoding_intertwines auxiliaryClean (historyClean.sumMap auxiliaryClean)
  · exact auxiliaryEncoding_clean 1
  · exact sumEncoding_intertwines historyClean auxiliaryClean _ _ _ _
      (historyEncodingBitCircuit_clean hk hN z) (auxiliaryEncoding_clean _)

theorem hardFamilyBitCircuit_counts {N m : ℕ} [NeZero N] [NeZero m] {kappa : ℝ}
    (hk : 4 ≤ kappa) (hN : N = 2 * historyPadding kappa + 2 * m) :
    (hardFamilyBitCircuit hk hN).matrixQueries = 4 ∧
      (hardFamilyBitCircuit hk hN).vectorQueries = 0 := by
  simp only [hardFamilyBitCircuit, (dilationCircuit_counts _ _ _).1, (dilationCircuit_counts _ _ _).2,
    augmentedBitCircuit, (sumEncodingLeftCircuit_counts _ _ _ _).1,
    (sumEncodingLeftCircuit_counts _ _ _ _).2, (sumEncodingRightCircuit_counts _ _ _ _).1,
    (sumEncodingRightCircuit_counts _ _ _ _).2, historyEncodingBitCircuit,
    (lcuCircuit_counts _ _ _ _ _).1, (lcuCircuit_counts _ _ _ _ _).2,
    (historyBitCircuit_counts _).1, (historyBitCircuit_counts _).2]
  norm_num

end OptimalQLS.LowerBounds.Physical
