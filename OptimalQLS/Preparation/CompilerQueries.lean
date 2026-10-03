import OptimalQLS.Preparation.Finite
import OptimalQLS.OracleSubstitution

/-! # Literal two-oracle query syntax for the synthesized finite compiler -/
noncomputable section
namespace OptimalQLS.Preparation
open Matrix TransducerCompiler BinaryClock
variable {N C W : Type*} [Fintype N] [DecidableEq N]
  [Fintype C] [DecidableEq C] [Fintype W] [DecidableEq W]

/-- A named finite control register is only an enumeration of QueryPort's
ordinary finite multiplicity; it does not change the oracle query model. -/
def namedPort (e : N × C ≃ W) (control : C → Bool) : QueryPort N W where
  multiplicity := Fintype.card C
  wiring := (Equiv.prodCongr (Equiv.refl N) (Fintype.equivFin C).symm).trans e
  control k := control ((Fintype.equivFin C).symm k)

theorem namedPort_eval (e : N × C ≃ W) (control : C → Bool)
    (U : Matrix.unitaryGroup N ℂ) :
    (namedPort e control).apply U=rewireUnitary e (controlledOn control U) := by
  apply Subtype.ext
  ext w w'
  obtain ⟨⟨i,c⟩,rfl⟩ := e.surjective w
  obtain ⟨⟨j,d⟩,rfl⟩ := e.surjective w'
  simp [namedPort,QueryPort.apply,rewireUnitary,controlledUnitary,controlledOn,
    Matrix.blockDiagonal_apply]

def compilerDataWiring (N : Type*) (ℓ : ℕ) :
    N × (Bool × Label × Bits ℓ × Bits ℓ) ≃ SynthSpace N ℓ where
  toFun p := (p.2.1,((p.1,p.2.2.1),p.2.2.2))
  invFun p := (p.2.1.1,(p.1,p.2.1.2,p.2.2))
  left_inv := by intro p; rfl
  right_inv := by intro p; rfl

def compilerDataPort (N : Type*) [Fintype N] [DecidableEq N] (ℓ : ℕ) (l : Label) :
    QueryPort N (SynthSpace N ℓ) := namedPort (compilerDataWiring N ℓ) (fun c => decide (c.2.1=l))

theorem compilerDataPort_eval {ℓ : ℕ} (l : Label) (U : Matrix.unitaryGroup N ℂ) :
    (compilerDataPort N ℓ l).apply U=padHom (dataQuery (a := Bits ℓ × Bits ℓ) l U) := by
  rw [compilerDataPort,namedPort_eval]
  change rewireUnitary _ _ = rewireUnitary (Equiv.prodComm (CachedSpace N ℓ) Bool)
    (controlledOn (fun _ : Bool => true) (dataQuery (a := Bits ℓ × Bits ℓ) l U))
  apply Subtype.ext
  ext ⟨a,⟨i,j⟩,x,y⟩ ⟨b,⟨k,m⟩,u,v⟩
  by_cases hab : a=b <;> by_cases hjm : j=m <;>
    by_cases hxu : x=u <;> by_cases hyv : y=v <;>
      simp_all [compilerDataWiring,padHom,GateSynthesis.placeHom,dataQuery,
        rewireUnitary,controlledOn,Matrix.blockDiagonal_apply,Matrix.one_apply]

/-- Replace only the compiler's semantic oracle instructions. Auxiliary/work
matrices retain their existing proven physical interpretations. -/
def compilerInstruction {ℓ : ℕ} (S : Matrix.unitaryGroup (Base N) ℂ) :
    SynthInstruction ℓ → QueryInstruction N N (SynthSpace N ℓ)
  | .query₁ => .matrixCall (compilerDataPort N ℓ .first) false
  | .query₂ => .vectorCall (compilerDataPort N ℓ .second) false
  | .work => .work (padHom (cachedWork S))
  | .elementary g => .work (lowerAuxHom g.eval)
  | .clock adj => .work (padHom (cacheLift (toBitUnitary
      (if adj then (clockLift (HadamardClock.finHadamard ℓ))⁻¹
        else clockLift (HadamardClock.finHadamard ℓ)))))

def compilerQueryCircuit {ℓ : ℕ} (S : Matrix.unitaryGroup (Base N) ℂ) (c : SynthCircuit ℓ) :
    QueryCircuit N N (SynthSpace N ℓ) := c.map (compilerInstruction S)

theorem compilerInstruction_eval {ℓ : ℕ} (S : Matrix.unitaryGroup (Base N) ℂ)
    (U₁ U₂ : Matrix.unitaryGroup N ℂ) (g : SynthInstruction ℓ) :
    (compilerInstruction S g).eval U₁ U₂=g.eval S U₁ U₂ := by
  cases g <;> simp [compilerInstruction,QueryInstruction.eval,SynthInstruction.eval,compilerDataPort_eval]

theorem compilerQueryCircuit_eval {ℓ : ℕ} (S : Matrix.unitaryGroup (Base N) ℂ)
    (U₁ U₂ : Matrix.unitaryGroup N ℂ) (c : SynthCircuit ℓ) :
    (compilerQueryCircuit S c).eval U₁ U₂=c.eval S U₁ U₂ := by
  induction c with
  | nil => rfl
  | cons g c ih =>
    simp only [compilerQueryCircuit,List.map_cons,QueryCircuit.eval,SynthCircuit.eval]
    rw [compilerInstruction_eval,← compilerQueryCircuit,ih]

theorem compilerQueryCircuit_counts {ℓ : ℕ} (S : Matrix.unitaryGroup (Base N) ℂ)
    (c : SynthCircuit ℓ) :
    (compilerQueryCircuit S c).matrixQueries=c.firstCalls ∧
    (compilerQueryCircuit S c).vectorQueries=c.secondCalls := by
  induction c with
  | nil => simp [compilerQueryCircuit,QueryCircuit.matrixQueries,QueryCircuit.vectorQueries,
      SynthCircuit.firstCalls,SynthCircuit.secondCalls]
  | cons g c ih =>
    cases g <;> simp_all [compilerQueryCircuit,compilerInstruction,QueryCircuit.matrixQueries,
      QueryCircuit.vectorQueries,SynthCircuit.firstCalls,SynthCircuit.secondCalls,
      SynthInstruction.firstCost,SynthInstruction.secondCost,Nat.add_comm]


/-- A source query on the public sector acts on the clean input without
preparing or charging any private catalyst. -/
theorem compilerDataPort_input {ℓ : ℕ} (b : Layout (2^ℓ))
    (U : Matrix.unitaryGroup N ℂ) (x : N → ℂ) :
    ((compilerDataPort N ℓ .pub).apply U).val*ᵥsynthInput b x =
      synthInput b (U.val*ᵥx) := by
  rw [compilerDataPort_eval,synthInput,padHom_clean]
  congr 1
  ext ⟨⟨i,l⟩,clock,cache⟩
  rw [dataQuery_apply]
  by_cases hc : cache=(fun _ => false) <;>
    by_cases hk : HadamardClock.bitsFinEquiv ℓ clock=b.zero <;>
      cases l <;> simp [cachedInput,cleanVector,inputToBits,spaceBitsEquiv,
        inputState,hc,hk,Matrix.mulVec,dotProduct]

end OptimalQLS.Preparation
