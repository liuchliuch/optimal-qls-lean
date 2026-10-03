import OptimalQLS.Preparation.Encoded
import OptimalQLS.TransducerCompiler.Reservoir

/-! # Exact eight-sector to four-sector preparation compiler wiring -/
noncomputable section
namespace OptimalQLS.Preparation
open Matrix TransducerCompiler
variable {F : Type*} [Fintype F] [DecidableEq F]

def compilerLabel : Bool × Label ≃ Fin 8 where
  toFun
    | (false,.pub) => 0
    | (false,.internal) => 1
    | (false,.first) => 2
    | (true,.first) => 3
    | (false,.second) => 4
    | (true,.pub) => 5
    | (true,.internal) => 6
    | (true,.second) => 7
  invFun j := ![(false,.pub),(false,.internal),(false,.first),(true,.first),
    (false,.second),(true,.pub),(true,.internal),(true,.second)] j
  left_inv := by intro ⟨b,l⟩; cases b <;> cases l <;> rfl
  right_inv := by intro j; fin_cases j <;> rfl

/-- The spare bit pads the unequal private spaces without changing any oracle. -/
def compilerWiring (F : Type*) : Base (Bool × F) ≃ Fin 8 × F where
  toFun p := (compilerLabel (p.1.1,p.2),p.1.2)
  invFun p := ((compilerLabel.symm p.1 |>.1,p.2),compilerLabel.symm p.1 |>.2)
  left_inv := by
    intro ⟨⟨b,i⟩,l⟩
    have h := compilerLabel.symm_apply_apply (b,l)
    change (( (compilerLabel.symm (compilerLabel (b,l))).1,i),
      (compilerLabel.symm (compilerLabel (b,l))).2)=((b,i),l)
    rw [h]
  right_inv := by
    intro ⟨j,i⟩
    change (compilerLabel (compilerLabel.symm j),i)=(j,i)
    rw [compilerLabel.apply_symm_apply]

def doubleVector (x y : F → ℂ) : Bool × F → ℂ := fun p => if p.1 then y p.2 else x p.2

theorem bundle8_compilerWiring (ξ q ω₁ ω₂ z : F → ℂ) :
    bundle8 ξ q ω₁ ω₂ z ∘ compilerWiring F =
      bundle (doubleVector ξ 0) (doubleVector q 0) (doubleVector ω₁ ω₂) (doubleVector z 0) := by
  ext ⟨⟨b,i⟩,l⟩
  cases b <;> cases l <;> simp [compilerWiring,compilerLabel,bundle8,bundle,doubleVector]

/-- Both copies share one call to the same whole intermediate oracle. -/
def doubleOracle (V : Matrix.unitaryGroup F ℂ) : Matrix.unitaryGroup (Bool × F) ℂ :=
  signalLift (S := Bool) V

theorem doubleOracle_apply (V : Matrix.unitaryGroup F ℂ) (x y : F → ℂ) :
    (doubleOracle V).val*ᵥdoubleVector x y = doubleVector (V.val*ᵥx) (V.val*ᵥy) := by
  rw [doubleOracle,signalLift,rewire_apply]
  ext ⟨b,i⟩
  change ((controlledOn (fun _ : Bool => true) V).val*ᵥ_) (i,b)=_
  rw [controlledOn_apply]
  cases b <;> simp [doubleVector,Function.comp_def]

/-- Oracle-independent compiler work, obtained only by a real basis permutation. -/
def compilerWork (Q : Matrix F F ℂ) (hQ : star Q=Q) (hQQ : Q*Q=Q)
    {μ r : ℝ} (hμ : 0<μ) (hr : |r|<1) : Matrix.unitaryGroup (Base (Bool × F)) ℂ :=
  rewireUnitary (compilerWiring F).symm (preparationWork Q hQ hQQ hμ hr)

theorem compilerWork_apply (Q : Matrix F F ℂ) (hQ : star Q=Q) (hQQ : Q*Q=Q)
    {μ r : ℝ} (hμ : 0<μ) (hr : |r|<1) (v : Fin 8 × F → ℂ) :
    (compilerWork Q hQ hQQ hμ hr).val*ᵥ(v ∘ compilerWiring F) =
      ((preparationWork Q hQ hQQ hμ hr).val*ᵥv) ∘ compilerWiring F := by
  rw [compilerWork,rewire_apply]
  congr 2
  ext i
  simp [Function.comp_def]

/-- The actual five-component preparation relation becomes the compiler's
canonical relation, with the two distinct query components retained. -/
theorem compilerWork_restoration (Q V R : Matrix F F ℂ)
    (hQ : star Q=Q) (hQQ : Q*Q=Q) (hV : V*V=1)
    {μ α r : ℝ} (hμ : 0<μ) (hα : α≠0) (hr : |r|<1)
    (ξ ψ q p z : F → ℂ) (hq : Q*ᵥq=q) (hp : Q*ᵥp=p) (hz : Q*ᵥz=z)
    (hVp : Q*ᵥ(V*ᵥp)=0) (hVz : Q*ᵥ(V*ᵥz)=α⁻¹ • (q-p))
    (hfirst : (-r) • ξ + Real.sqrt (1-r^2) • (-(R*ᵥ((2:ℝ) • p-q))) = ψ)
    (hsecond : Real.sqrt (1-r^2) • ξ + r • (-(R*ᵥ((2:ℝ) • p-q))) = q) :
    (compilerWork Q hQ hQQ hμ hr).val*ᵥ
      bundle (doubleVector ξ 0) (doubleVector q 0)
        (doubleVector (V*ᵥkernelCatalystOne V μ α p z) (V*ᵥkernelCatalystTwo V μ α p z))
        (doubleVector (R*ᵥ((2:ℝ) • p-q)) 0) =
      bundle (doubleVector ψ 0) (doubleVector q 0)
        (doubleVector (kernelCatalystOne V μ α p z) (kernelCatalystTwo V μ α p z))
        (doubleVector ((2:ℝ) • p-q) 0) := by
  rw [← bundle8_compilerWiring,← bundle8_compilerWiring,compilerWork_apply]
  rw [preparationWork_apply Q V R hQ hQQ hV hμ hα hr ξ ψ q p z hq hp hz hVp hVz hfirst hsecond]


/-- Exact transport from the original oracle instruction list to the canonical
four-sector relation used by the fully synthesized compiler. -/
theorem compilerRelation_of_circuit (Q : Matrix F F ℂ) (hQ : star Q=Q) (hQQ : Q*Q=Q)
    {μ r : ℝ} (hμ : 0<μ) (hr : |r|<1) (V R : Matrix.unitaryGroup F ℂ)
    (ξ ψ q ω₁ ω₂ z : F → ℂ)
    (h : ((preparationCircuit Q hQ hQQ hμ hr).eval V R).val*ᵥbundle8 ξ q ω₁ ω₂ z =
      bundle8 ψ q ω₁ ω₂ z) :
    (compilerWork Q hQ hQQ hμ hr).val*ᵥ
      bundle (doubleVector ξ 0) (doubleVector q 0)
        ((doubleOracle V).val*ᵥdoubleVector ω₁ ω₂)
        ((doubleOracle R).val*ᵥdoubleVector z 0) =
      bundle (doubleVector ψ 0) (doubleVector q 0)
        (doubleVector ω₁ ω₂) (doubleVector z 0) := by
  rw [doubleOracle_apply,doubleOracle_apply,Matrix.mulVec_zero,
    ← bundle8_compilerWiring,← bundle8_compilerWiring,compilerWork_apply]
  simp only [preparationCircuit,QueryCircuit.eval,QueryInstruction.eval,
    Bool.false_eq_true,ite_false,one_mul,Submonoid.coe_mul,← Matrix.mulVec_mulVec] at h
  rw [historyPort_apply,reflectionPort_apply] at h
  rw [h]

end OptimalQLS.Preparation
