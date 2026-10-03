import OptimalQLS.Refinement.Repetition.Program
import OptimalQLS.TransducerCompiler.Basic

/-! Basis reindexing from arbitrary literal circuit registers to the Fin-indexed
finite-program semantics, without changing the oracle calls or accepted state. -/
noncomputable section
namespace OptimalQLS.Refinement.Repetition
open Matrix LowerBounds
set_option maxHeartbeats 200000
variable {A B W X D : Type*} [Fintype W] [DecidableEq W] [Fintype X] [DecidableEq X]

/-- Pure basis relabeling, not an oracle invocation. -/
def reindexPort (E : W ≃ X) (p : QueryPort A W) : QueryPort A X :=
  ⟨p.multiplicity, p.wiring.trans E, p.control⟩

def reindexInstruction (E : W ≃ X) : QueryInstruction A B W → QueryInstruction A B X
  | .work U => .work (rewireUnitary E U)
  | .matrixCall p adj => .matrixCall (reindexPort E p) adj
  | .vectorCall p adj => .vectorCall (reindexPort E p) adj

def reindexCircuit (E : W ≃ X) (c : QueryCircuit A B W) : QueryCircuit A B X :=
  c.map (reindexInstruction E)

theorem reindexCircuit_matrixQueries (E : W ≃ X) (c : QueryCircuit A B W) :
    (reindexCircuit E c).matrixQueries = c.matrixQueries := by
  induction c with
  | nil => rfl
  | cons gate c ih => cases gate <;> simp [reindexCircuit, reindexInstruction, QueryCircuit.matrixQueries, reindexCircuit] at ih ⊢ <;> exact ih

theorem reindexCircuit_vectorQueries (E : W ≃ X) (c : QueryCircuit A B W) :
    (reindexCircuit E c).vectorQueries = c.vectorQueries := by
  induction c with
  | nil => rfl
  | cons gate c ih => cases gate <;> simp [reindexCircuit, reindexInstruction, QueryCircuit.vectorQueries, reindexCircuit] at ih ⊢ <;> exact ih

variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

theorem reindexPort_apply (E : W ≃ X) (p : QueryPort A W) (U : Matrix.unitaryGroup A ℂ) :
    (reindexPort E p).apply U = rewireUnitary E (p.apply U) := by
  apply Subtype.ext
  rfl

theorem reindexCircuit_eval (E : W ≃ X) (c : QueryCircuit A B W)
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) :
    (reindexCircuit E c).eval UA Ub = rewireUnitary E (c.eval UA Ub) := by
  induction c with
  | nil => exact (rewireUnitary_one E).symm
  | cons gate c ih =>
    cases gate <;>
      simp only [reindexCircuit, List.map_cons, QueryCircuit.eval, reindexInstruction,
        QueryInstruction.eval, reindexPort_apply, ← rewireUnitary_mul] at ih ⊢ <;>
      rw [ih, ← rewireUnitary_mul]

def reindexEmbedding {d w : ℕ} (E : W ≃ Fin w) (F : D ≃ Fin d) (j : D ↪ W) :
    Fin d ↪ Fin w where
  toFun i := E (j (F.symm i))
  inj' := E.injective.comp (j.injective.comp F.symm.injective)

theorem reindex_successVector {d w : ℕ} (E : W ≃ Fin w) (F : D ≃ Fin d)
    (j : D ↪ W) (c : QueryCircuit A B W) (zero : W)
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) (i : D) :
    successVector (reindexCircuit E c) (reindexEmbedding E F j) (E zero) UA Ub (F i) =
      ((c.eval UA Ub).val *ᵥ (fun x => if x = zero then 1 else 0)) (j i) := by
  unfold successVector runState
  rw [reindexCircuit_eval, TransducerCompiler.rewire_apply]
  have hb : basis (E zero) ∘ E = (fun x => if x = zero then (1 : ℂ) else 0) := by
    funext x
    simp [basis, E.injective.eq_iff]
  rw [hb]
  simp [reindexEmbedding]

end OptimalQLS.Refinement.Repetition
