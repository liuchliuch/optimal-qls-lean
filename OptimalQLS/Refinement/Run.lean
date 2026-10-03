import OptimalQLS.Refinement.Theorem56
import OptimalQLS.Preparation.Parameters

/-! # One literal preparation/filter/correction run -/
noncomputable section
namespace OptimalQLS.Refinement
open Matrix Preparation Alignment TransducerCompiler BinaryClock PolynomialTransform
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 1000000
variable {S D F C A B : Type*} [Fintype S] [DecidableEq S] [Fintype D] [DecidableEq D]
  [Fintype F] [DecidableEq F] [Fintype C] [DecidableEq C]
  [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

abbrev CoarseAux (S : Type*) (ℓ : ℕ) := Bool × (Bool × (S × (Label × (Bits ℓ × Bits ℓ))))

def coarseZero (s₀ : S) (ℓ : ℕ) : CoarseAux S ℓ :=
  (false,(false,(s₀,(.pub,((fun _=>false),(fun _=>false))))))

/-- Only product register regrouping; the nontrivial work-label permutation is
handled separately by CompilerPermutation and is not used here. -/
def coarseWiring (S D : Type*) (ℓ : ℕ) :
    CoarseAux S ℓ × (Fin 4 × D) ≃ SynthSpace (Bool × (S × (Fin 4 × D))) ℓ where
  toFun p := (p.1.1,(((p.1.2.1,(p.1.2.2.1,p.2)),p.1.2.2.2.1),p.1.2.2.2.2))
  invFun p := ((p.1,(p.2.1.1.1,(p.2.1.1.2.1,(p.2.1.2,p.2.2)))),p.2.1.1.2.2)
  left_inv := by intro p; rfl
  right_inv := by intro p; rfl

theorem coarse_slice {ℓ : ℕ} (s₀ : S)
    (Ψ : SynthSpace (Bool × (S × (Fin 4 × D))) ℓ → ℂ) :
    (fun x => (Ψ ∘ coarseWiring S D ℓ) (coarseZero s₀ ℓ,x))=zeroAuxiliaryOutput s₀ Ψ := rfl

theorem coarse_reindex_norm {ℓ : ℕ}
    (Ψ : SynthSpace (Bool × (S × (Fin 4 × D))) ℓ → ℂ) :
    ‖WithLp.toLp 2 (Ψ ∘ coarseWiring S D ℓ)‖=‖WithLp.toLp 2 Ψ‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [EuclideanSpace.norm_sq_eq,Function.comp_apply]
  exact (coarseWiring S D ℓ).sum_comp (fun i => ‖Ψ i‖^2)

def preparationRunWiring (P F C D : Type*) :
    (P × (Fin 4 × D)) × (C × F) ≃ Space P F C D where
  toFun p := (p.2.1,(p.1.1,(p.2.2,p.1.2)))
  invFun p := ((p.2.1,p.2.2.2),(p.1,p.2.2.1))
  left_inv := by intro p; rfl
  right_inv := by intro p; rfl

def preparationRunPort (P F C D : Type*) [Fintype P] [DecidableEq P]
    [Fintype F] [DecidableEq F] [Fintype C] [DecidableEq C]
    [Fintype D] [DecidableEq D] : QueryPort (P × (Fin 4 × D)) (Space P F C D) :=
  namedPort (preparationRunWiring P F C D) (fun _=>true)

theorem preparationRunPort_input {P : Type*} [Fintype P] [DecidableEq P]
    (U : Matrix.unitaryGroup (P × (Fin 4 × D)) ℂ) (f₀ : F) (c₀ : C)
    (Ψ : P × (Fin 4 × D) → ℂ) :
    ((preparationRunPort P F C D).apply U).val*ᵥjointInput f₀ c₀ Ψ =
      jointInput f₀ c₀ (U.val*ᵥΨ) := by
  rw [preparationRunPort,namedPort_eval,rewire_apply]
  ext ⟨c,p,f,x⟩
  change ((controlledOn (fun _ : C × F=>true) U).val*ᵥ_) ((p,x),(c,f))=_
  rw [controlledOn_apply]
  by_cases hc : c=c₀ <;> by_cases hf : f=f₀ <;>
    simp [jointInput,hc,hf,preparationRunWiring,Function.comp_def,Matrix.mulVec,dotProduct]

/-- All three procedures call the same original oracles. The new signal
registers remain disjoint from preparation until the one final joint test. -/
def fullRunProgram {ℓ : ℕ}
    (cp : QueryCircuit A B (SynthSpace (Bool × (S × (Fin 4 × D))) ℓ))
    (cf : QueryCircuit A B (F × (Fin 4 × D))) (cc : QueryCircuit A B (C × D)) :
    QueryCircuit A B (Space (CoarseAux S ℓ) F C D) :=
  (cp.lift (relabelPort (coarseWiring S D ℓ).symm)).lift
    (preparationRunPort (CoarseAux S ℓ) F C D) ++ refinementProgram cf cc

theorem fullRunProgram_counts {ℓ : ℕ}
    (cp : QueryCircuit A B (SynthSpace (Bool × (S × (Fin 4 × D))) ℓ))
    (cf : QueryCircuit A B (F × (Fin 4 × D))) (cc : QueryCircuit A B (C × D)) :
    (fullRunProgram cp cf cc).matrixQueries=cp.matrixQueries+cf.matrixQueries+cc.matrixQueries ∧
    (fullRunProgram cp cf cc).vectorQueries=cp.vectorQueries+cf.vectorQueries+cc.vectorQueries := by
  simp [fullRunProgram,QueryCircuit.matrixQueries_append,QueryCircuit.vectorQueries_append,
    (QueryCircuit.lift_counts _ _).1,(QueryCircuit.lift_counts _ _).2,
    (refinementProgram_counts _ _).1,(refinementProgram_counts _ _).2,Nat.add_assoc]

/-- Exact complete-run state, with preparation's full rejected components
retained coherently until the final acceptance projection. -/
theorem fullRunProgram_state {ℓ : ℕ}
    (cp : QueryCircuit A B (SynthSpace (Bool × (S × (Fin 4 × D))) ℓ))
    (cf : QueryCircuit A B (F × (Fin 4 × D))) (cc : QueryCircuit A B (C × D))
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ)
    (f₀ : F) (c₀ : C) (ξ : SynthSpace (Bool × (S × (Fin 4 × D))) ℓ → ℂ) :
    ((fullRunProgram cp cf cc).eval UA Ub).val*ᵥjointInput f₀ c₀ (ξ ∘ coarseWiring S D ℓ) =
      ((refinementProgram (P := CoarseAux S ℓ) cf cc).eval UA Ub).val*ᵥ
        jointInput f₀ c₀ (((cp.eval UA Ub).val*ᵥξ) ∘ coarseWiring S D ℓ) := by
  rw [fullRunProgram,QueryCircuit.eval_append,Submonoid.coe_mul,← Matrix.mulVec_mulVec,
    QueryCircuit.lift_eval,preparationRunPort_input,QueryCircuit.lift_eval,relabelPort_apply,rewire_apply]
  have hξ : (ξ ∘ coarseWiring S D ℓ) ∘ (coarseWiring S D ℓ).symm=ξ := by ext i; simp
  rw [hξ]
  rfl

end OptimalQLS.Refinement
