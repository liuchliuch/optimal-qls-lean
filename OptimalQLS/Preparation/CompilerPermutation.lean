import OptimalQLS.Preparation.CompilerBridge
import OptimalQLS.TransducerCompiler.EncodedSpace
import OptimalQLS.Preparation.WorkGates.Complete

/-! # Constant-gate implementation of the compiler/preparation label permutation -/
noncomputable section
namespace OptimalQLS.Preparation
open Matrix TransducerCompiler BinaryClock
open PolynomialTransform DirtyAncilla

/-- Actual compiler bit order: spare data bit, low label bit, high label bit. -/
def compilerBitEquiv : Bool × Label ≃ (Fin 3 → Bool) where
  toFun p := ![p.1,(labelBitsEquiv p.2).2,(labelBitsEquiv p.2).1]
  invFun b := (b 0,labelBitsEquiv.symm (b 2,b 1))
  left_inv := by intro ⟨b,l⟩; cases b <;> cases l <;> rfl
  right_inv := by
    intro b
    cases h₁ : b 1 <;> cases h₂ : b 2 <;> ext i <;> fin_cases i <;>
      simp [labelBitsEquiv,labelCode,h₁,h₂]

/-- Six concrete reversible gates; the permutation is not charged as a wire reorder. -/
def compilerPermutation : Program (Fin 3) :=
  [.cx 2 1 (by decide),
   .ccx 0 2 1 (by decide) (by decide),
   .cx 1 2 (by decide),
   .ccx 1 2 0 (by decide) (by decide),
   .ccx 0 2 1 (by decide) (by decide),
   .cx 0 2 (by decide)]

theorem compilerPermutation_run (b : Bool) (l : Label) :
    run compilerPermutation (compilerBitEquiv (b,l))=
      WorkGates.labelEquiv (compilerLabel (b,l)) := by
  cases b <;> cases l <;> ext i <;> fin_cases i <;> rfl

/-- The literal real one- and two-qubit lowering returns its synthesis ancilla
clean and implements the precise nontrivial eight-entry label permutation. -/
theorem compilerPermutation_lowered (b : Bool) (l : Label) :
    (GateSynthesis.eval (GateSynthesis.lowerProgram compilerPermutation)).val*ᵥ
      Pi.single (false,compilerBitEquiv (b,l)) 1 =
      Pi.single (false,WorkGates.labelEquiv (compilerLabel (b,l))) 1 := by
  rw [GateSynthesis.lowerProgram_basis,compilerPermutation_run]

theorem compilerPermutation_gate_bound :
    (GateSynthesis.lowerProgram compilerPermutation).length≤90 := by
  exact (GateSynthesis.lowerProgram_length compilerPermutation).trans_eq (by rfl)

theorem compilerPermutation_real (i j : GateSynthesis.Space (Fin 3)) :
    ((GateSynthesis.eval (GateSynthesis.lowerProgram compilerPermutation)).val i j).im=0 :=
  GateSynthesis.lowerProgram_real compilerPermutation i j

/-- Both conjugating permutations together use at most180 real elementary gates. -/
theorem compilerPermutation_conjugation_bound :
    (GateSynthesis.lowerProgram compilerPermutation).length+
      (GateSynthesis.lowerProgram compilerPermutation.reverse).length≤180 := by
  have hp := compilerPermutation_gate_bound
  have hr := GateSynthesis.lowerProgram_length compilerPermutation.reverse
  simp only [List.length_reverse] at hr
  change (GateSynthesis.lowerProgram compilerPermutation.reverse).length≤90 at hr
  omega

end OptimalQLS.Preparation
