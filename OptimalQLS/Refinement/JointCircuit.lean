import OptimalQLS.Preparation.CompilerQueries
import OptimalQLS.SignalIsometry

/-! # Literal disjoint-ancilla refinement and joint acceptance -/
noncomputable section
namespace OptimalQLS.Refinement
open Matrix Preparation TransducerCompiler
set_option synthInstance.maxSize 4096
variable {P F C D : Type*} [Fintype P] [DecidableEq P] [Fintype F] [DecidableEq F]
  [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]

abbrev Space (P F C D : Type*) := C × (P × (F × (Fin 4 × D)))

def filterWiring : (F × (Fin 4 × D)) × (C × P) ≃ Space P F C D where
  toFun p := (p.2.1,(p.2.2,p.1))
  invFun p := (p.2.2,(p.1,p.2.1))
  left_inv := by intro p; rfl
  right_inv := by intro p; rfl

def correctionWiring : (C × D) × (P × (F × Fin 4)) ≃ Space P F C D where
  toFun p := (p.1.1,(p.2.1,(p.2.2.1,(p.2.2.2,p.1.2))))
  invFun p := ((p.1,p.2.2.2.2),(p.2.1,(p.2.2.1,p.2.2.2.1)))
  left_inv := by intro p; rfl
  right_inv := by intro p; rfl

def filterPort : QueryPort (F × (Fin 4 × D)) (Space P F C D) := namedPort filterWiring (fun _ => true)
def correctionPort : QueryPort (C × D) (Space P F C D) := namedPort correctionWiring (fun _ => true)

def jointInput (f₀ : F) (c₀ : C) (Ψ : P × (Fin 4 × D) → ℂ) : Space P F C D → ℂ :=
  fun p => if p.1=c₀ then if p.2.2.1=f₀ then Ψ (p.2.1,p.2.2.2) else 0 else 0

def accepted (p₀ : P) (f₀ : F) (c₀ : C) (Ψ : Space P F C D → ℂ) : D → ℂ :=
  fun i => Ψ (c₀,(p₀,(f₀,(2,i))))

def jointUnitary (UF : Matrix.unitaryGroup (F × (Fin 4 × D)) ℂ)
    (UC : Matrix.unitaryGroup (C × D) ℂ) : Matrix.unitaryGroup (Space P F C D) ℂ :=
  correctionPort.apply UC * filterPort.apply UF

theorem filterPort_apply (UF : Matrix.unitaryGroup (F × (Fin 4 × D)) ℂ)
    (v : Space P F C D → ℂ) (c : C) (p : P) (f : F) (x : Fin 4 × D) :
    ((filterPort.apply UF).val*ᵥv) (c,(p,(f,x))) =
      (UF.val*ᵥfun fx => v (c,(p,fx))) (f,x) := by
  rw [filterPort,namedPort_eval,rewire_apply]
  change ((controlledOn (fun _ : C × P => true) UF).val*ᵥ_) ((f,x),(c,p))=_
  rw [controlledOn_apply]
  rfl

theorem correctionPort_apply (UC : Matrix.unitaryGroup (C × D) ℂ)
    (v : Space P F C D → ℂ) (c : C) (p : P) (f : F) (g : Fin 4) (i : D) :
    ((correctionPort.apply UC).val*ᵥv) (c,(p,(f,(g,i)))) =
      (UC.val*ᵥfun cd => v (cd.1,(p,(f,(g,cd.2))))) (c,i) := by
  rw [correctionPort,namedPort_eval,rewire_apply]
  change ((controlledOn (fun _ : P × (F × Fin 4) => true) UC).val*ᵥ_) ((c,i),(p,(f,g)))=_
  rw [controlledOn_apply]
  rfl

/-- The joint accepting branch is the product of the actual block operators.
No intermediate preparation/filter measurement or conditioning is assumed. -/
theorem joint_acceptance (p₀ : P) (f₀ : F) (c₀ : C)
    (UF : Matrix.unitaryGroup (F × (Fin 4 × D)) ℂ)
    (UC : Matrix.unitaryGroup (C × D) ℂ) (Ψ : P × (Fin 4 × D) → ℂ) :
    accepted p₀ f₀ c₀ ((jointUnitary UF UC).val*ᵥjointInput f₀ c₀ Ψ) =
      signalBlock c₀ UC*ᵥ(fun i => (signalBlock f₀ UF*ᵥfun x => Ψ (p₀,x)) (2,i)) := by
  ext i
  change ((jointUnitary UF UC).val*ᵥjointInput f₀ c₀ Ψ) (c₀,(p₀,(f₀,(2,i))))=_
  rw [jointUnitary,Submonoid.coe_mul,← Matrix.mulVec_mulVec,correctionPort_apply]
  simp_rw [filterPort_apply]
  simp [Matrix.mulVec,dotProduct,Fintype.sum_prod_type,jointInput,signalBlock_entries]



/-- Adding the two disjoint clean signal registers preserves norm exactly. -/
theorem jointInput_norm (f₀ : F) (c₀ : C) (Ψ : P × (Fin 4 × D) → ℂ) :
    ‖WithLp.toLp 2 (jointInput f₀ c₀ Ψ)‖=‖WithLp.toLp 2 Ψ‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp [EuclideanSpace.norm_sq_eq,Fintype.sum_prod_type,jointInput,apply_ite]

end OptimalQLS.Refinement
