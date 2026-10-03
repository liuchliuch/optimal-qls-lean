import OptimalQLS.OracleCoordinateResources
import OptimalQLS.Refinement.CostedExecution.Provenance

/-! Source-register coordinates on the actual primitive instruction syntax. -/
noncomputable section
namespace OptimalQLS.Refinement.CostedExecution.Program
open Matrix PolynomialTransform
set_option maxHeartbeats 500000
set_option linter.unusedSectionVars false
variable {G A B A' B' Aux Data : Type*} {d w : ℕ}

def mapOracles (ea : A ≃ A') (eb : B ≃ B') :
    Program G A B Aux Data w → Program G A' B' Aux Data w
  | .named g p => .named g (mapOracles ea eb p)
  | .matrixCall p b next => .matrixCall (OracleCoordinates.port ea p) b (mapOracles ea eb next)
  | .vectorCall p b next => .vectorCall (OracleCoordinates.port eb p) b (mapOracles ea eb next)
  | .measure i next => .measure i (fun b=>mapOracles ea eb (next b))
  | .bitX i p => .bitX i (mapOracles ea eb p)
  | .discard b => .discard b

@[simp] theorem mapOracles_cost (ea : A ≃ A') (eb : B ≃ B') (p : Program G A B Aux Data w) :
    (p.mapOracles ea eb).cost=p.cost := by
  induction p <;> simp_all [mapOracles,cost]

@[simp] theorem mapOracles_matrixCalls (ea : A ≃ A') (eb : B ≃ B') (p : Program G A B Aux Data w) :
    (p.mapOracles ea eb).matrixCalls=p.matrixCalls := by
  induction p <;> simp_all [mapOracles,matrixCalls]

@[simp] theorem mapOracles_vectorCalls (ea : A ≃ A') (eb : B ≃ B') (p : Program G A B Aux Data w) :
    (p.mapOracles ea eb).vectorCalls=p.vectorCalls := by
  induction p <;> simp_all [mapOracles,vectorCalls]

variable [Fintype Aux] [DecidableEq Aux] [Fintype Data] [DecidableEq Data]

theorem mapOracles_lower (ea : A ≃ A') (eb : B ≃ B')
    (E : State Aux Data ≃ Fin w) (F : (Data → Bool) ≃ Fin d)
    (gate : G → Matrix.unitaryGroup (Fin w) ℂ) (p : Program G A B Aux Data w) :
    (p.mapOracles ea eb).lower E F gate=OracleCoordinates.program ea eb (p.lower E F gate) := by
  induction p <;> simp_all [mapOracles,lower,OracleCoordinates.program]
  rename_i i next ih
  funext b
  fin_cases b <;> simp_all [outcome]

theorem mapOracles_allowed (ea : A ≃ A') (eb : B ≃ B')
    (gok : G → Prop) (mok : QueryPort A' (Fin w) → Bool → Prop)
    (vok : QueryPort B' (Fin w) → Bool → Prop) (p : Program G A B Aux Data w)
    (hp : p.Allowed gok (fun q b=>mok (OracleCoordinates.port ea q) b)
      (fun q b=>vok (OracleCoordinates.port eb q) b)) :
    (p.mapOracles ea eb).Allowed gok mok vok := by
  induction p with
  | named g next ih => exact ⟨hp.1,ih hp.2⟩
  | matrixCall p b next ih => exact ⟨hp.1,ih hp.2⟩
  | vectorCall p b next ih => exact ⟨hp.1,ih hp.2⟩
  | measure i next ih => exact fun b=>ih b (hp b)
  | bitX i next ih => exact ih hp
  | discard b => trivial

end OptimalQLS.Refinement.CostedExecution.Program
