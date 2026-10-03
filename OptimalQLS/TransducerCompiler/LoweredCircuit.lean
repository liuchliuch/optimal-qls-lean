import OptimalQLS.TransducerCompiler.EfficientTheorems
import OptimalQLS.TransducerCompiler.GateSynthesis

/-! # Fully lowered compiler circuit with one reusable clean synthesis ancilla -/

noncomputable section
namespace OptimalQLS.TransducerCompiler
open Matrix BinaryClock

abbrev SynthSpace (n : Type*) (ℓ : ℕ) := Bool × CachedSpace n ℓ
variable {n : Type*} [Fintype n] [DecidableEq n] {ℓ : ℕ}

/-- Tensor a cached-space operation with the untouched synthesis ancilla. -/
def padHom : Matrix.unitaryGroup (CachedSpace n ℓ) ℂ →* Matrix.unitaryGroup (SynthSpace n ℓ) ℂ :=
  GateSynthesis.placeHom (Equiv.prodComm (CachedSpace n ℓ) Bool)

/-- Compiler gates act on named label/clock/cache wires and leave all data indices untouched. -/
def synthWiring : (GateSynthesis.Space (LabelWire ℓ) × n) ≃ SynthSpace n ℓ where
  toFun p := (p.1.1, ((p.2,(labelStateEquiv p.1.2).1),(labelStateEquiv p.1.2).2))
  invFun p := ((p.1,labelStateEquiv.symm (p.2.1.2,p.2.2)),p.2.1.1)
  left_inv p := by rcases p with ⟨⟨a,x⟩,i⟩; simp
  right_inv p := by rcases p with ⟨a,⟨i,l⟩,x,y⟩; simp

def lowerAuxHom : Matrix.unitaryGroup (GateSynthesis.Space (LabelWire ℓ)) ℂ →*
    Matrix.unitaryGroup (SynthSpace n ℓ) ℂ := GateSynthesis.placeHom synthWiring

/-- A clean, reusable synthesis ancilla. -/
def synthClean (v : CachedSpace n ℓ → ℂ) : SynthSpace n ℓ → ℂ
  | (false,x) => v x
  | (true,_) => 0

def synthCleanMap : (CachedSpace n ℓ → ℂ) →ₗ[ℂ] (SynthSpace n ℓ → ℂ) where
  toFun := synthClean
  map_add' v w := by ext ⟨a,x⟩; cases a <;> simp [synthClean]
  map_smul' c v := by ext ⟨a,x⟩; cases a <;> simp [synthClean]

theorem synthClean_single (x : CachedSpace n ℓ) (c : ℂ) :
    synthClean (Pi.single x c) = Pi.single (false,x) c := by
  ext ⟨a,y⟩
  cases a <;> simp [synthClean, Pi.single_apply]

theorem synthClean_eq_sum (v : CachedSpace n ℓ → ℂ) :
    synthClean v = ∑ x : CachedSpace n ℓ,
      v x • (Pi.single (false,x) (1 : ℂ) : SynthSpace n ℓ → ℂ) := by
  ext ⟨a,y⟩
  cases a <;> simp [synthClean, Pi.single_apply]

private theorem vector_eq_sum {a : Type*} [Fintype a] [DecidableEq a] (v : a → ℂ) :
    v = ∑ x : a, v x • (Pi.single x (1 : ℂ) : a → ℂ) := by
  ext x
  simp [Pi.single_apply]

theorem padHom_clean (U : Matrix.unitaryGroup (CachedSpace n ℓ) ℂ)
    (v : CachedSpace n ℓ → ℂ) :
    (padHom U).val *ᵥ synthClean v = synthClean (U.val *ᵥ v) := by
  change (rewireUnitary (Equiv.prodComm (CachedSpace n ℓ) Bool)
    (controlledOn (fun _ : Bool => true) U)).val *ᵥ synthClean v = _
  rw [rewire_apply]
  ext ⟨a,x⟩
  simp only [Function.comp_apply, Equiv.prodComm_apply]
  rw [controlledOn_apply]
  cases a <;> simp [synthClean, Function.comp_def, Matrix.mulVec, dotProduct]

/-- Every primitive-program macro acts coherently and returns the shared synthesis ancilla to zero. -/
theorem lowerAux_basis (p : Program (LabelWire ℓ)) (z : CachedSpace n ℓ) :
    (lowerAuxHom (GateSynthesis.eval (GateSynthesis.lowerProgram p))).val *ᵥ Pi.single (false,z) 1 =
      synthClean ((programOnSpace p).val *ᵥ Pi.single z 1) := by
  rcases z with ⟨⟨i,l⟩,x,a⟩
  rw [programOnSpace_basis p i (l,x,a), synthClean_single]
  have h := GateSynthesis.placeHom_basis (synthWiring (n := n) (ℓ := ℓ))
    (GateSynthesis.eval (GateSynthesis.lowerProgram p))
    (false,labelStateEquiv.symm (l,x,a))
    (false,run p (labelStateEquiv.symm (l,x,a))) i
    (GateSynthesis.lowerProgram_basis p _)
  simpa [lowerAuxHom, synthWiring] using h

theorem lowerAux_clean (p : Program (LabelWire ℓ)) (v : CachedSpace n ℓ → ℂ) :
    (lowerAuxHom (GateSynthesis.eval (GateSynthesis.lowerProgram p))).val *ᵥ synthClean v =
      synthClean ((programOnSpace p).val *ᵥ v) := by
  rw [synthClean_eq_sum, Matrix.mulVec_sum]
  conv_rhs => rw [vector_eq_sum v, Matrix.mulVec_sum]
  change _ = synthCleanMap (∑ x : CachedSpace n ℓ, (programOnSpace p).val *ᵥ
    (v x • (Pi.single x (1 : ℂ) : CachedSpace n ℓ → ℂ)))
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [Matrix.mulVec_smul, Matrix.mulVec_smul, map_smul]
  exact congrArg (v x • ·) (lowerAux_basis p x)

/-- Elementary auxiliary gates retain their explicit physical-wire placement.
Clock instructions contain the proved ℓ one-qubit Hadamard circuit. -/
inductive SynthInstruction (ℓ : ℕ) where
  | query₁ | query₂ | work
  | elementary (g : GateSynthesis.LowerGate (LabelWire ℓ))
  | clock (adjoint : Bool)

abbrev SynthCircuit (ℓ : ℕ) := List (SynthInstruction ℓ)

def SynthInstruction.eval (S : Matrix.unitaryGroup (Base n) ℂ)
    (U₁ U₂ : Matrix.unitaryGroup n ℂ) : SynthInstruction ℓ → Matrix.unitaryGroup (SynthSpace n ℓ) ℂ
  | .query₁ => padHom (dataQuery .first U₁)
  | .query₂ => padHom (dataQuery .second U₂)
  | .work => padHom (cachedWork S)
  | .elementary g => lowerAuxHom g.eval
  | .clock adj => padHom (cacheLift (toBitUnitary
      (if adj then (clockLift (HadamardClock.finHadamard ℓ))⁻¹
        else clockLift (HadamardClock.finHadamard ℓ))))

def SynthCircuit.eval (S : Matrix.unitaryGroup (Base n) ℂ)
    (U₁ U₂ : Matrix.unitaryGroup n ℂ) : SynthCircuit ℓ → Matrix.unitaryGroup (SynthSpace n ℓ) ℂ
  | [] => 1
  | g :: gs => SynthCircuit.eval S U₁ U₂ gs * g.eval S U₁ U₂

theorem SynthCircuit.eval_append (S : Matrix.unitaryGroup (Base n) ℂ)
    (U₁ U₂ : Matrix.unitaryGroup n ℂ) (c d : SynthCircuit ℓ) :
    (c ++ d).eval S U₁ U₂ = d.eval S U₁ U₂ * c.eval S U₁ U₂ := by
  induction c with
  | nil => simp [eval]
  | cons g gs ih => simp [eval, ih, mul_assoc]

def lowerInstruction : CachedInstruction ℓ → SynthCircuit ℓ
  | .query₁ => [.query₁]
  | .query₂ => [.query₂]
  | .work => [.work]
  | .classical p => (GateSynthesis.lowerProgram p).map .elementary

def lowerCached (c : CachedCircuit ℓ) : SynthCircuit ℓ := c.flatMap lowerInstruction

theorem eval_elementaryList (S : Matrix.unitaryGroup (Base n) ℂ)
    (U₁ U₂ : Matrix.unitaryGroup n ℂ) (p : List (GateSynthesis.LowerGate (LabelWire ℓ))) :
    SynthCircuit.eval S U₁ U₂ (p.map SynthInstruction.elementary) = lowerAuxHom (GateSynthesis.eval p) := by
  induction p with
  | nil => simp [SynthCircuit.eval, GateSynthesis.eval]
  | cons g gs ih => simp [SynthCircuit.eval, SynthInstruction.eval, GateSynthesis.eval, ih]

theorem lowerInstruction_clean (S : Matrix.unitaryGroup (Base n) ℂ)
    (U₁ U₂ : Matrix.unitaryGroup n ℂ) (g : CachedInstruction ℓ) (v : CachedSpace n ℓ → ℂ) :
    ((lowerInstruction g).eval S U₁ U₂).val *ᵥ synthClean v =
      synthClean ((g.eval S U₁ U₂).val *ᵥ v) := by
  cases g with
  | query₁ => simpa [lowerInstruction, SynthCircuit.eval, SynthInstruction.eval,
      CachedInstruction.eval] using padHom_clean (dataQuery .first U₁) v
  | query₂ => simpa [lowerInstruction, SynthCircuit.eval, SynthInstruction.eval,
      CachedInstruction.eval] using padHom_clean (dataQuery .second U₂) v
  | work => simpa [lowerInstruction, SynthCircuit.eval, SynthInstruction.eval,
      CachedInstruction.eval] using padHom_clean (cachedWork S) v
  | classical p => simpa [lowerInstruction, eval_elementaryList, CachedInstruction.eval] using lowerAux_clean p v

theorem lowerCached_clean (S : Matrix.unitaryGroup (Base n) ℂ)
    (U₁ U₂ : Matrix.unitaryGroup n ℂ) (c : CachedCircuit ℓ) (v : CachedSpace n ℓ → ℂ) :
    ((lowerCached c).eval S U₁ U₂).val *ᵥ synthClean v =
      synthClean ((c.eval S U₁ U₂).val *ᵥ v) := by
  induction c generalizing v with
  | nil => simp [lowerCached, SynthCircuit.eval, CachedCircuit.eval]
  | cons g gs ih =>
    rw [lowerCached, List.flatMap_cons, SynthCircuit.eval_append, Submonoid.coe_mul,
      ← Matrix.mulVec_mulVec, lowerInstruction_clean]
    rw [show gs.flatMap lowerInstruction = lowerCached gs from rfl, ih]
    simp only [CachedCircuit.eval, Submonoid.coe_mul, ← Matrix.mulVec_mulVec]

/-- Complete real elementary compiler, with its two explicit Hadamard layers. -/
def synthesize (c : CachedCircuit ℓ) : SynthCircuit ℓ := [.clock false] ++ lowerCached c ++ [.clock true]

theorem synthesize_clean (S : Matrix.unitaryGroup (Base n) ℂ)
    (U₁ U₂ : Matrix.unitaryGroup n ℂ) (c : CachedCircuit ℓ) (v : CachedSpace n ℓ → ℂ) :
    ((synthesize c).eval S U₁ U₂).val *ᵥ synthClean v =
      synthClean ((c.withClock S U₁ U₂).val *ᵥ v) := by
  simp only [synthesize, SynthCircuit.eval_append, SynthCircuit.eval, SynthInstruction.eval,
    Bool.false_eq_true, if_false, ite_true, one_mul, Submonoid.coe_mul, ← Matrix.mulVec_mulVec]
  rw [padHom_clean, lowerCached_clean, padHom_clean]
  simp only [CachedCircuit.withClock, Submonoid.coe_mul, ← Matrix.mulVec_mulVec]

end OptimalQLS.TransducerCompiler
