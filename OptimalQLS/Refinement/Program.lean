import OptimalQLS.Refinement.JointCircuit
import OptimalQLS.Refinement.Analytic

noncomputable section
namespace OptimalQLS.Refinement
open Matrix
set_option synthInstance.maxSize 4096
variable {A B P F C D : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype P] [DecidableEq P] [Fintype F] [DecidableEq F]
  [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]

/-- Filter and correction run coherently on their two disjoint clean signal
registers and share the original two input oracles. -/
def refinementProgram (cf : QueryCircuit A B (F × (Fin 4 × D)))
    (cc : QueryCircuit A B (C × D)) : QueryCircuit A B (Space P F C D) :=
  cf.lift filterPort ++ cc.lift correctionPort

theorem refinementProgram_eval (cf : QueryCircuit A B (F × (Fin 4 × D)))
    (cc : QueryCircuit A B (C × D)) (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) :
    (refinementProgram (P := P) cf cc).eval UA Ub=jointUnitary (cf.eval UA Ub) (cc.eval UA Ub) := by
  rw [refinementProgram,QueryCircuit.eval_append,QueryCircuit.lift_eval,QueryCircuit.lift_eval]
  rfl

theorem refinementProgram_counts (cf : QueryCircuit A B (F × (Fin 4 × D)))
    (cc : QueryCircuit A B (C × D)) :
    (refinementProgram (P := P) cf cc).matrixQueries=cf.matrixQueries+cc.matrixQueries ∧
    (refinementProgram (P := P) cf cc).vectorQueries=cf.vectorQueries+cc.vectorQueries := by
  simp [refinementProgram,QueryCircuit.matrixQueries_append,QueryCircuit.vectorQueries_append,
    (QueryCircuit.lift_counts _ _).1,(QueryCircuit.lift_counts _ _).2]

/-- Literal instruction execution, followed by one joint acceptance event. -/
theorem refinementProgram_acceptance (cf : QueryCircuit A B (F × (Fin 4 × D)))
    (cc : QueryCircuit A B (C × D)) (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ)
    (p₀ : P) (f₀ : F) (c₀ : C) (Ψ : P × (Fin 4 × D) → ℂ) :
    accepted p₀ f₀ c₀ (((refinementProgram cf cc).eval UA Ub).val*ᵥjointInput f₀ c₀ Ψ) =
      signalBlock c₀ (cc.eval UA Ub)*ᵥ
        (fun i => (signalBlock f₀ (cf.eval UA Ub)*ᵥfun x => Ψ (p₀,x)) (2,i)) := by
  rw [refinementProgram_eval]
  exact joint_acceptance p₀ f₀ c₀ _ _ Ψ

theorem accepted_norm_le (p₀ : P) (f₀ : F) (c₀ : C) (v : Space P F C D → ℂ) :
    ‖WithLp.toLp 2 (accepted p₀ f₀ c₀ v)‖≤‖WithLp.toLp 2 v‖ :=
  Preparation.coordinate_slice_norm_le
    ⟨(fun i => (c₀,(p₀,(f₀,(2,i))))),fun _ _ h => congrArg (fun p => p.2.2.2.2) h⟩ (WithLp.toLp 2 v)

/-- The norm squared of the actual joint accepted vector is a valid Born
probability, with no separate normalization certificate for a block operator. -/
theorem refinementProgram_acceptance_probability_le_one
    (cf : QueryCircuit A B (F × (Fin 4 × D))) (cc : QueryCircuit A B (C × D))
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ)
    (p₀ : P) (f₀ : F) (c₀ : C) (Ψ : P × (Fin 4 × D) → ℂ) (hΨ : ‖WithLp.toLp 2 Ψ‖=1) :
    ‖WithLp.toLp 2 (accepted p₀ f₀ c₀
      (((refinementProgram cf cc).eval UA Ub).val*ᵥjointInput f₀ c₀ Ψ))‖^2≤1 := by
  have h := accepted_norm_le p₀ f₀ c₀
    (((refinementProgram cf cc).eval UA Ub).val*ᵥjointInput f₀ c₀ Ψ)
  have hn := TransducerCompiler.unitary_norm ((refinementProgram (P := P) cf cc).eval UA Ub)
    (WithLp.toLp 2 (jointInput f₀ c₀ Ψ))
  rw [jointInput_norm,hΨ] at hn
  have hp : ‖WithLp.toLp 2 (accepted p₀ f₀ c₀
      (((refinementProgram cf cc).eval UA Ub).val*ᵥjointInput f₀ c₀ Ψ))‖≤1 := h.trans_eq hn
  have hnon := norm_nonneg (WithLp.toLp 2 (accepted p₀ f₀ c₀
      (((refinementProgram cf cc).eval UA Ub).val*ᵥjointInput f₀ c₀ Ψ)))
  nlinarith

end OptimalQLS.Refinement
