import OptimalQLS.Preparation.OriginalQueries
import OptimalQLS.PolynomialTransform.PhysicalRegister
import OptimalQLS.PolynomialTransform.NamedCircuit
import OptimalQLS.PolynomialTransform.CleanTransport

/-! # Shared physical preparation registers

The old compiler synthesis bit is retained, and exactly three new scratch bits
are supplied to every successive work/oracle/reflection macro.
-/
noncomputable section
set_option synthInstance.maxSize 4096
set_option linter.unusedSimpArgs false
open scoped Classical
namespace OptimalQLS.Preparation.CompilerAttachment
open Matrix TransducerCompiler BinaryClock PolynomialTransform

abbrev Logical (a n ℓ : ℕ) := SynthSpace (PreparationData (Bits a) (Bits n)) ℓ
abbrev Physical (a n ℓ : ℕ) := Logical a n ℓ × PhaseScratch


def clean (a n ℓ : ℕ) (x : Logical a n ℓ) : Physical a n ℓ := (x,(false,false,false))

theorem clean_injective (a n ℓ : ℕ) : Function.Injective (clean a n ℓ) := by
  intro x y h
  exact congrArg Prod.fst h

theorem clean_isometry (a n ℓ : ℕ) :
    (basisInsertion (clean a n ℓ))ᴴ*basisInsertion (clean a n ℓ)=1 :=
  basisInsertion_isometry _ (clean_injective a n ℓ)

/-- The literal original compiler auxiliary wires, with its data and new scratch spectators. -/
def auxFrame (a n ℓ : ℕ) :
    GateSynthesis.Space (LabelWire ℓ) × (PreparationData (Bits a) (Bits n) × PhaseScratch) ≃
      Physical a n ℓ where
  toFun p := (synthWiring (p.1,p.2.1),p.2.2)
  invFun p := ((synthWiring.symm p.1).1,(synthWiring.symm p.1).2,p.2)
  left_inv p := by rcases p with ⟨g,d,s⟩; simp
  right_inv p := by rcases p with ⟨x,s⟩; simp

/-- Rearranging spectator scratch through a specified logical register frame. -/
def scratchFrame {L P R : Type*} (e : L × R ≃ P) :
    (L × PhaseScratch) × R ≃ P × PhaseScratch where
  toFun p := (e (p.1.1,p.2),p.1.2)
  invFun p := (((e.symm p.1).1,p.2),(e.symm p.1).2)
  left_inv p := by rcases p with ⟨⟨x,s⟩,r⟩; simp
  right_inv p := by rcases p with ⟨x,s⟩; simp

/-- Old synthesis, the spare data bit, clock, and cache are always preserved as spectators. -/
abbrev CompilerRest (ℓ : ℕ) := Bool × (Bool × (Bits ℓ × Bits ℓ))

def labelDataFrame (a n ℓ : ℕ) :
    (((Bool × Bool) × (GraphEncoding.PhysicalSignal (Bits a) × (Fin 4 × Bits n))) ×
      CompilerRest ℓ) ≃ Logical a n ℓ where
  toFun p := (p.2.1,(((p.2.2.1,p.1.2),labelBitsEquiv.symm p.1.1),p.2.2.2))
  invFun p := (((labelBitsEquiv p.2.1.2),p.2.1.1.2),p.1,p.2.1.1.1,p.2.2)
  left_inv p := by rcases p with ⟨⟨m,w⟩,z,b,t,c⟩; simp
  right_inv p := by rcases p with ⟨z,⟨⟨b,w⟩,l⟩,t,c⟩; simp

/-- Actual Hilbert-space cardinality, including the three newly allocated scratch qubits. -/
theorem physical_card (a n ℓ : ℕ) :
    Fintype.card (Physical a n ℓ)=2^(n+a+2*ℓ+13) := by
  have hl : Fintype.card Label=4 := by decide
  simp [Physical,Logical,SynthSpace,CachedSpace,Base,PreparationData,
    GraphEncoding.PhysicalSignal,GraphEncoding.Signal,PhaseScratch,Bits,hl,
    Fintype.card_prod,Fintype.card_fun,pow_add,pow_mul]
  ring_nf
  rw [Nat.mul_comm ℓ 2,pow_mul]
  norm_num

end OptimalQLS.Preparation.CompilerAttachment
