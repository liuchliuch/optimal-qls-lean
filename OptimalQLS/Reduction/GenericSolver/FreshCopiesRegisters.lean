import OptimalQLS.Reduction.GenericSolver.FreshCopiesSourceLower
import OptimalQLS.Refinement.CostedExecution.QueryLocalityCore

/-! Binary registers with explicit finite coordinates and literal tensor factors. -/
noncomputable section
open scoped Classical BigOperators
namespace OptimalQLS.Reduction.GenericSolver.FreshCopies
open Matrix TransducerCompiler BinaryClock PolynomialTransform
open Refinement.CostedExecution Refinement.PhysicalMeasurement
set_option synthInstance.maxSize 32768
set_option maxHeartbeats 800000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false

structure Register where
  State : Type
  Wire : Type
  [finiteState : Fintype State]
  [decidableState : DecidableEq State]
  [finiteWire : Fintype Wire]
  [decidableWire : DecidableEq Wire]
  dimension : ℕ
  index : State ≃ Fin dimension
  bits : State ≃ (Wire → Bool)
attribute [instance] Register.finiteState Register.decidableState Register.finiteWire Register.decidableWire

def Register.ofChart {P W : Type} [Fintype P] [DecidableEq P] [Fintype W] [DecidableEq W]
    (chart : P ≃ (W → Bool)) : Register :=
  { State := P, Wire := W, dimension := Fintype.card P, index := Fintype.equivFin P, bits := chart }

def Register.product (R S : Register) : Register where
  State := R.State × S.State
  Wire := R.Wire ⊕ S.Wire
  dimension := R.dimension*S.dimension
  index := (Equiv.prodCongr R.index S.index).trans finProdFinEquiv
  bits := productBits R.bits S.bits

def Register.qubits (R : Register) : ℕ := Fintype.card R.Wire

theorem Register.dimension_eq (R : Register) : R.dimension=2^R.qubits := by
  have hi:=Fintype.card_congr R.index
  have hb:=Fintype.card_congr R.bits
  simp only [Fintype.card_fin,Fintype.card_fun,Fintype.card_bool] at hi hb
  exact hi.symm.trans hb

@[simp] theorem Register.product_qubits (R S : Register) :
    (R.product S).qubits=R.qubits+S.qubits := by simp [Register.product,Register.qubits]

def indexedMatrix (R Q : Register) (M : Matrix Q.State R.State ℂ) :
    Matrix (Fin Q.dimension) (Fin R.dimension) ℂ := M.submatrix Q.index.symm R.index.symm

theorem indexedMatrix_normalized (R Q : Register) {I : Type} [Fintype I]
    (K : I → Matrix Q.State R.State ℂ) (hn : ∑ i,(K i)ᴴ*K i=1) :
    ∑ i,(indexedMatrix R Q (K i))ᴴ*indexedMatrix R Q (K i)=1 := by
  simp_rw [indexedMatrix,Matrix.conjTranspose_submatrix,Matrix.submatrix_mul_equiv]
  have hs : (∑ i,((K i)ᴴ*K i).submatrix R.index.symm R.index.symm)=
      (∑ i,(K i)ᴴ*K i).submatrix R.index.symm R.index.symm := by
    ext x y
    simp only [Matrix.sum_apply,Matrix.submatrix_apply]
  rw [hs,hn,Matrix.submatrix_one_equiv]

def TensorLayout.indexedKraus {R Q : Register} (F : TensorLayout R.bits Q.bits)
    (i : Fin (Fintype.card F.Rest)) : Matrix (Fin Q.dimension) (Fin R.dimension) ℂ :=
  indexedMatrix R Q (F.kraus ((Fintype.equivFin F.Rest).symm i))

theorem TensorLayout.indexedKraus_normalized {R Q : Register} (F : TensorLayout R.bits Q.bits) :
    ∑ i,(F.indexedKraus i)ᴴ*F.indexedKraus i=1 := by
  unfold TensorLayout.indexedKraus
  rw [(Fintype.equivFin F.Rest).symm.sum_comp
    (fun r=>(indexedMatrix R Q (F.kraus r))ᴴ*indexedMatrix R Q (F.kraus r))]
  exact indexedMatrix_normalized R Q _ F.kraus_normalized

/-- Untouched registers are actual tensor spectators for every selected wire. -/
def Register.firstEmbedding (R T : Register) :
    WireEmbedding R.bits (R.product T).bits (Equiv.refl (R.State × T.State)) where
  wire := Function.Embedding.inl
  read := by intros; rfl
  outside := by
    intro x y r j hj
    cases j with
    | inl j => exact False.elim (hj j rfl)
    | inr j => rfl

/-- Extend a literal partial trace by a completely untouched register. -/
def TensorLayout.product {R Q : Register} (F : TensorLayout R.bits Q.bits) (T : Register) :
    TensorLayout (R.product T).bits (Q.product T).bits where
  Rest := F.Rest
  frame := {
    toFun p := (F.frame (p.1.1,p.2),p.1.2)
    invFun p := (((F.frame.symm p.1).1,p.2),(F.frame.symm p.1).2)
    left_inv p := by rcases p with ⟨⟨x,t⟩,r⟩; simp
    right_inv p := by rcases p with ⟨x,t⟩; simp }
  wires := {
    wire := ⟨fun i=>match i with
      | .inl i=>.inl (F.wires.wire i)
      | .inr i=>.inr i,by
        intro i j he
        cases i with
        | inl i => cases j with
          | inl j => exact congrArg Sum.inl (F.wires.wire.injective (Sum.inl.inj he))
          | inr j => cases he
        | inr i => cases j with
          | inl j => cases he
          | inr j => exact congrArg (Sum.inr : T.Wire → Q.Wire ⊕ T.Wire) (Sum.inr.inj he)⟩
    read := by
      intro x r i
      cases i with
      | inl i => exact F.wires.read x.1 r i
      | inr i => rfl
    outside := by
      intro x y r j hj
      cases j with
      | inl j =>
        apply F.wires.outside x.1 y.1 r j
        intro i hi
        exact hj (.inl i) (congrArg Sum.inl hi)
      | inr j => exact False.elim (hj (.inr j) rfl) }

end OptimalQLS.Reduction.GenericSolver.FreshCopies
