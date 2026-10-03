import OptimalQLS.LowerBounds.Physical.CircuitSums
import OptimalQLS.LowerBounds.HistoryQuerySimulation

/-! A literal two-query gate word for the coherent history transition. -/
noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
namespace OptimalQLS.LowerBounds.Physical
open Matrix PolynomialTransform
variable {D : Type*} [Fintype D] [DecidableEq D]

/-- Permutations in forward state-vector convention. -/
def forwardPermutation (e : Equiv.Perm D) : Matrix.unitaryGroup D ℂ :=
  TransducerCompiler.permutation e.symm

theorem forwardPermutation_trans (e f : Equiv.Perm D) :
    forwardPermutation (e.trans f) = forwardPermutation f * forwardPermutation e := by
  apply Subtype.ext
  change Matrix.permMatrixHom (R := ℂ) (f*e) =
    Matrix.permMatrixHom (R := ℂ) f * Matrix.permMatrixHom (R := ℂ) e
  exact map_mul _ _ _

theorem forwardPermutation_basis (e : Equiv.Perm D) (i : D) :
    (forwardPermutation e).val *ᵥ Pi.single i 1 = Pi.single (e i) 1 := by
  ext j
  simp [forwardPermutation, TransducerCompiler.permutation, Matrix.permMatrix_mulVec,
    Function.comp_def, Pi.single_apply, Equiv.symm_apply_eq]

abbrev BitBasis (m : ℕ) := Fin m × Bool

def bitPermutation {m : ℕ} (z : BitString m) : Equiv.Perm (BitBasis m) :=
  (show Function.Involutive (fun p : BitBasis m => (p.1, Bool.xor p.2 (z p.1))) from by
    rintro ⟨i,a⟩; cases a <;> cases hz : z i <;> simp [hz]).toPerm

/-- Literal standard oracle |i,a> ↦ |i,a XOR z_i>. -/
def standardBitOracle {m : ℕ} (z : BitString m) : Matrix.unitaryGroup (BitBasis m) ℂ :=
  forwardPermutation (bitPermutation z)

theorem standardBitOracle_basis {m : ℕ} (z : BitString m) (i : Fin m) (a : Bool) :
    (standardBitOracle z).val *ᵥ Pi.single (i,a) 1 = Pi.single (i,Bool.xor a (z i)) 1 :=
  forwardPermutation_basis _ _

def historyBitPort (N m : ℕ) : QueryPort (BitBasis m) (SimulationBasis N m) :=
  scratchPort (Equiv.prodAssoc (Fin m) Bool (HistoryBasis N))

theorem historyBitPort_apply {N m : ℕ} (z : BitString m) :
    (historyBitPort N m).apply (standardBitOracle z) = forwardPermutation (standardBitQuery z) := by
  apply Subtype.ext
  ext ⟨i,a,x⟩ ⟨j,b,y⟩
  rw [historyBitPort, scratchPort_apply]
  change (TransducerCompiler.GateSynthesis.placeHom
    (Equiv.prodAssoc (Fin m) Bool (HistoryBasis N)) (standardBitOracle z)).val
      ((Equiv.prodAssoc (Fin m) Bool (HistoryBasis N)) ((i,a),x))
      ((Equiv.prodAssoc (Fin m) Bool (HistoryBasis N)) ((j,b),y)) = _
  rw [placeHom_entry]
  simp only [standardBitOracle, forwardPermutation, TransducerCompiler.permutation,
    PEquiv.toMatrix, Equiv.toPEquiv_apply, Equiv.symm_apply_apply]
  by_cases hij : i=j
  · subst j
    cases a <;> cases b <;> cases hz : z i <;>
      simp [bitPermutation, standardBitQuery, standardBitQueryMap, hz, eq_comm]
  · simp [bitPermutation, standardBitQuery, standardBitQueryMap, hij]

/-- Every listed work gate is independent of z; exactly two entries query z. -/
def historyBitCircuit {N m : ℕ} [NeZero N] [NeZero m]
    (label : Fin N → Option (Fin m)) : QueryCircuit (BitBasis m) Unit (SimulationBasis N m) :=
  [.work (forwardPermutation (computeHistoryIndex label)),
   .matrixCall (historyBitPort N m) false,
   .work (forwardPermutation (selectHistoryWork label)),
   .matrixCall (historyBitPort N m) false,
   .work (forwardPermutation (computeHistoryIndex label).symm),
   .work (forwardPermutation advanceHistoryClock)]

theorem historyBitCircuit_eval {N m : ℕ} [NeZero N] [NeZero m]
    (label : Fin N → Option (Fin m)) (z : BitString m) :
    (historyBitCircuit label).eval (standardBitOracle z) 1 =
      forwardPermutation (twoQueryHistoryStep label z) := by
  simp [historyBitCircuit, QueryCircuit.eval, QueryInstruction.eval, historyBitPort_apply,
    ← forwardPermutation_trans, twoQueryHistoryStep]

theorem historyBitCircuit_counts {N m : ℕ} [NeZero N] [NeZero m]
    (label : Fin N → Option (Fin m)) :
    (historyBitCircuit label).matrixQueries = 2 ∧ (historyBitCircuit label).vectorQueries = 0 := by
  constructor <;> rfl

/-- The clean scratch state fixes the actual address and response registers. -/
def historyClean {N m : ℕ} [NeZero m] : HistoryBasis N ↪ SimulationBasis N m :=
  ⟨fun x => (0,false,x), by intro x y h; exact congrArg (fun p => p.2.2) h⟩

theorem historyBitCircuit_clean {N ell m : ℕ} [NeZero N] [NeZero m]
    (hell : 0 < ell) (hN : N = 2 * ell + 2 * m) (z : BitString m) :
    ((historyBitCircuit (parityHistoryLabel hell hN)).eval (standardBitOracle z) 1).val *
      basisInsertion (historyClean (N := N) (m := m)) =
      basisInsertion historyClean * (historyStepUnitary (fixedParityProfile ell z)).val := by
  rw [historyBitCircuit_eval]
  apply basisInsertion_intertwines
  rintro ⟨j,b⟩
  rw [forwardPermutation_basis]
  change Pi.single (twoQueryHistoryStep (parityHistoryLabel hell hN) z (0,false,j,b)) 1 =
    basisInsertion historyClean *ᵥ
      ((forwardPermutation (historyPermutation (fixedParityProfile ell z))).val *ᵥ Pi.single (j,b) 1)
  rw [forwardPermutation_basis, basisInsertion_basis, parityHistoryStep_twoQuery_clean hell hN]
  rfl

end OptimalQLS.LowerBounds.Physical
