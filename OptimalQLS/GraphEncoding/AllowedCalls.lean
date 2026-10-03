import OptimalQLS.GraphEncoding.ElementaryLocality

/-! # Exact two-label controlled/adjoint call semantics

This module records the uniform controlled query word and its exact semantics.
The76 work instructions here are controlled elementary gates; their further
one- and two-qubit expansion is deliberately not asserted by these query counts.
-/
noncomputable section
set_option synthInstance.maxSize 2048
namespace OptimalQLS.GraphEncoding
open Matrix PolynomialTransform TransducerCompiler
variable {W S D B : Type*} [Fintype W] [DecidableEq W]
  [Fintype S] [DecidableEq S] [Fintype D] [DecidableEq D]
  [Fintype B] [DecidableEq B]

/-- The two QSVT label tests are the only external controls. -/
def maskedGraphPort (W : Type*) (mask : Bool × Bool) : QueryPort W ((Bool × Bool) × W) where
  multiplicity := Fintype.card (Bool × Bool)
  wiring := (Equiv.prodCongr (Equiv.refl W) (Fintype.equivFin (Bool × Bool)).symm).trans
    (Equiv.prodComm W (Bool × Bool))
  control := fun k => decide ((Fintype.equivFin (Bool × Bool)).symm k = mask)

theorem maskedGraphPort_apply_entries (mask : Bool × Bool) (U : Matrix.unitaryGroup W ℂ)
    (c d : Bool × Bool) (i j : W) :
    ((maskedGraphPort W mask).apply U).val (c,i) (d,j) =
      if c=d then (if c=mask then U.val i j else if i=j then 1 else 0) else 0 := by
  simp [maskedGraphPort, QueryPort.apply, rewireUnitary, controlledUnitary,
    Matrix.blockDiagonal_apply, Matrix.one_apply]
  split_ifs <;> simp_all [Matrix.one_apply]

theorem maskedGraphPort_hermitian (mask : Bool × Bool) (U : Matrix.unitaryGroup W ℂ)
    (hU : U.val.IsHermitian) : ((maskedGraphPort W mask).apply U).val.IsHermitian := by
  ext ⟨c,i⟩ ⟨d,j⟩
  have hu : star (U.val j i) = U.val i j := congrFun (congrFun hU i) j
  simp only [Matrix.conjTranspose_apply, maskedGraphPort_apply_entries]
  by_cases hcd : c=d
  · subst d
    by_cases hm : c=mask
    · simp [hm,hu]
    · simp [hm,Matrix.one_apply,eq_comm]
  · simp [hcd,Ne.symm hcd]

/-- One uniform word implements either permitted direction because U_H†=U_H.
The original U_A and U_A† remain separate actual oracle instructions inside it. -/
def allowedGraphCall (S D B : Type*) [Fintype S] [DecidableEq S]
    [Fintype D] [DecidableEq D] (κ : ℝ) (hκ : 0 < κ)
    (mask : Bool × Bool) (_adjoint : Bool) :
    QueryCircuit (S × D) B ((Bool × Bool) × (PhysicalSignal S × (Fin 4 × D))) :=
  (elementaryGraphCircuit S D B κ hκ).lift
    (maskedGraphPort (PhysicalSignal S × (Fin 4 × D)) mask)

theorem allowedGraphCall_eval (κ : ℝ) (hκ : 0 < κ) (mask : Bool × Bool) (adj : Bool)
    (U : Matrix.unitaryGroup (S × D) ℂ) (Ub : Matrix.unitaryGroup B ℂ) :
    (allowedGraphCall S D B κ hκ mask adj).eval U Ub =
      (maskedGraphPort (PhysicalSignal S × (Fin 4 × D)) mask).apply
        (if adj then (physicalEncoding κ hκ U)⁻¹ else physicalEncoding κ hκ U) := by
  rw [allowedGraphCall, QueryCircuit.lift_eval, elementaryGraphCircuit_eval]
  have hi : (physicalEncoding κ hκ U)⁻¹ = physicalEncoding κ hκ U := by
    apply Subtype.ext
    exact physicalEncoding_hermitian κ hκ U
  cases adj <;> simp [hi]

theorem allowedGraphCall_queries (κ : ℝ) (hκ : 0 < κ) (mask : Bool × Bool) (adj : Bool) :
    (allowedGraphCall S D B κ hκ mask adj).matrixQueries=2 ∧
      (allowedGraphCall S D B κ hκ mask adj).vectorQueries=0 := by
  simp [allowedGraphCall, (QueryCircuit.lift_counts _ _).1,
    (QueryCircuit.lift_counts _ _).2, (elementaryGraphCircuit_counts κ hκ).1,
    (elementaryGraphCircuit_counts κ hκ).2.1]

end OptimalQLS.GraphEncoding
