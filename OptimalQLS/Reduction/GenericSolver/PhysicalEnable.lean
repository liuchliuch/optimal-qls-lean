import OptimalQLS.Reduction.GenericSolver.PhysicalPlainQueries

/-! Ordinary source instructions are tensored with identity on one shared
enable qubit. This is a literal wire embedding, not an added work gate. -/
noncomputable section
open scoped Classical
namespace OptimalQLS.Reduction.GenericSolver.Physical
open Matrix TransducerCompiler BinaryClock PolynomialTransform DirtyAncilla LowerBounds
open Refinement.CostedExecution Refinement.PhysicalMeasurement Preparation.CompilerAttachment
set_option synthInstance.maxSize 32768
set_option maxHeartbeats 800000
set_option maxRecDepth 8192
variable {P W : Type} [Fintype P] [DecidableEq P]
  {chart : P ≃ (W → Bool)} {a n : ℕ}

def sourceEnableEmbedding : WireEmbedding chart (enableCoordinates chart) (Equiv.prodComm P Bool) where
  wire := Function.Embedding.inr
  read := by intros; rfl
  outside := by
    intro x y r j hj
    cases j with
    | inl j => rfl
    | inr j => exact False.elim (hj j rfl)

def liftGate (g : TransducerCompiler.Physical.LocalGate chart) :
    TransducerCompiler.Physical.LocalGate (enableCoordinates chart) where
  arity := g.arity
  bound := g.bound
  Rest := g.Rest × Bool
  frame := tensorFrame g.frame (Equiv.prodComm P Bool)
  wires := g.wires.comp sourceEnableEmbedding
  unitary := g.unitary

theorem liftGate_eval (g : TransducerCompiler.Physical.LocalGate chart) :
    (liftGate g).eval=GateSynthesis.placeHom (Equiv.prodComm P Bool) g.eval := by
  exact (placeHom_comp g.frame (Equiv.prodComm P Bool) g.unitary).symm

def enableFullFrame : (P × PhaseScratch) × Bool ≃ (Bool × P) × PhaseScratch where
  toFun x := ((x.2,x.1.1),x.1.2)
  invFun x := ((x.1.2,x.2),x.1.1)
  left_inv _ := rfl
  right_inv _ := rfl

def fullEnableEmbedding : WireEmbedding (coordinates chart)
    (coordinates (enableCoordinates chart)) (enableFullFrame (P := P)) where
  wire := ⟨fun i=>match i with
    | .inl i => .inl (.inr i)
    | .inr i => .inr i,by intro i j he; cases i <;> cases j <;> simp_all⟩
  read := by intro x r i; cases i <;> rfl
  outside := by
    intro x y r j hj
    rcases j with (j|j)|j
    · rfl
    · exact False.elim (hj (.inl j) rfl)
    · exact False.elim (hj (.inr j) rfl)

def liftMatrixFrame (F : MatrixFrame chart a n) : MatrixFrame (enableCoordinates chart) a n where
  Rest := F.Rest × Bool
  frame := tensorFrame F.frame (Equiv.prodComm P Bool)
  wires := by
    have he : matrixWiring a n (tensorFrame F.frame (Equiv.prodComm P Bool))=
        tensorFrame (matrixWiring a n F.frame) (enableFullFrame (P := P)) := by
      apply Equiv.ext
      intro x
      rfl
    rw [he]
    exact F.wires.comp fullEnableEmbedding

def liftVectorFrame (F : VectorFrame chart n) : VectorFrame (enableCoordinates chart) n where
  Rest := F.Rest × Bool
  frame := tensorFrame F.frame (Equiv.prodComm P Bool)
  wires := by
    have he : vectorWiring n (tensorFrame F.frame (Equiv.prodComm P Bool))=
        tensorFrame (vectorWiring n F.frame) (enableFullFrame (P := P)) := by
      apply Equiv.ext
      intro x
      rfl
    rw [he]
    exact F.wires.comp fullEnableEmbedding

theorem liftMatrixFrame_apply (F : MatrixFrame chart a n)
    (U : Matrix.unitaryGroup (Bits a × (Bits n ⊕ Bits n)) ℂ) :
    (liftMatrixFrame F).port.apply U=GateSynthesis.placeHom (Equiv.prodComm P Bool) (F.port.apply U) := by
  rw [MatrixFrame.port_apply,MatrixFrame.port_apply,placeHom_comp]
  rfl

theorem liftVectorFrame_apply (F : VectorFrame chart n)
    (U : Matrix.unitaryGroup (Bits n ⊕ Bits n) ℂ) :
    (liftVectorFrame F).port.apply U=GateSynthesis.placeHom (Equiv.prodComm P Bool) (F.port.apply U) := by
  rw [VectorFrame.port_apply,VectorFrame.port_apply,placeHom_comp]
  rfl

def liftInstruction : SourceInstruction chart a n → SourceInstruction (enableCoordinates chart) a n
  | .gate g => .gate (liftGate g)
  | .matrix F adj => .matrix (liftMatrixFrame F) adj
  | .vector F adj => .vector (liftVectorFrame F) adj

theorem liftInstruction_counts (i : SourceInstruction chart a n) :
    (liftInstruction i).work=i.work ∧
    (liftInstruction i).matrixCalls=i.matrixCalls ∧
    (liftInstruction i).vectorCalls=i.vectorCalls := by cases i <;> exact ⟨rfl,rfl,rfl⟩

theorem liftInstruction_eval (i : SourceInstruction chart a n)
    (UA : Matrix.unitaryGroup (Bits a × (Bits n ⊕ Bits n)) ℂ)
    (Ub : Matrix.unitaryGroup (Bits n ⊕ Bits n) ℂ) :
    (((liftInstruction i).sourceQuery.toQuery TransducerCompiler.Physical.LocalGate.eval).eval UA Ub)=
      GateSynthesis.placeHom (Equiv.prodComm P Bool)
        ((i.sourceQuery.toQuery TransducerCompiler.Physical.LocalGate.eval).eval UA Ub) := by
  cases i with
  | gate g => exact liftGate_eval g
  | matrix F adj => exact liftMatrixFrame_apply F _
  | vector F adj => exact liftVectorFrame_apply F _

theorem liftInstruction_intertwines (i : SourceInstruction chart a n)
    (UA : Matrix.unitaryGroup (Bits a × (Bits n ⊕ Bits n)) ℂ)
    (Ub : Matrix.unitaryGroup (Bits n ⊕ Bits n) ℂ) (b : Bool) :
    (((liftInstruction i).sourceQuery.toQuery TransducerCompiler.Physical.LocalGate.eval).eval UA Ub).val *
      basisInsertion (fun x : P => (b,x)) =
      basisInsertion (fun x : P => (b,x)) *
        ((i.sourceQuery.toQuery TransducerCompiler.Physical.LocalGate.eval).eval UA Ub).val := by
  rw [liftInstruction_eval]
  simpa only [scratchPort_apply] using scratchPort_intertwines (Equiv.prodComm P Bool) b
    ((i.sourceQuery.toQuery TransducerCompiler.Physical.LocalGate.eval).eval UA Ub)

def oneBit : Bits 1 ≃ Bool where
  toFun x := x 0
  invFun b := fun _=>b
  left_inv x := by funext i; fin_cases i; rfl
  right_inv _ := rfl

def oneFlip : Equiv.Perm (Bits 1) where
  toFun x := fun i=> !(x i)
  invFun x := fun i=> !(x i)
  left_inv x := by funext i; simp
  right_inv x := by funext i; simp

def enableX (chart : P ≃ (W → Bool)) : TransducerCompiler.Physical.LocalGate (enableCoordinates chart) where
  arity := 1
  bound := by decide
  Rest := P
  frame := Equiv.prodCongr oneBit (Equiv.refl _)
  wires := {
    wire := ⟨fun _ => .inl (),fun _ _ _ => Subsingleton.elim _ _⟩
    read := by intro x r i; fin_cases i; rfl
    outside := by
      intro x y r j hj
      cases j with
      | inl j => cases j; exact False.elim (hj 0 rfl)
      | inr j => rfl }
  unitary := permutation oneFlip

theorem enableX_initializes (chart : P ≃ (W → Bool)) :
    (enableX chart).eval.val*basisInsertion (fun x : P => (false,x))=basisInsertion enabled := by
  ext ⟨b,p⟩ q
  simp only [Matrix.mul_apply,basisInsertion,Fintype.sum_prod_type,Prod.mk.injEq]
  simp only [enabled,Prod.mk.injEq,mul_ite,mul_one,mul_zero,ite_and,Finset.sum_ite_irrel,
    Finset.sum_const_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  change (GateSynthesis.placeHom (Equiv.prodCongr oneBit (Equiv.refl P)) (permutation oneFlip)).val
    ((Equiv.prodCongr oneBit (Equiv.refl P)) (oneBit.symm b,p))
    ((Equiv.prodCongr oneBit (Equiv.refl P)) (oneBit.symm false,q)) = _
  rw [placeHom_entry]
  cases b <;> simp [permutation,PEquiv.toMatrix,oneFlip,oneBit,enabled]
  intro _ he
  have hf := congrFun he (0 : Fin 1)
  cases hf

end OptimalQLS.Reduction.GenericSolver.Physical
