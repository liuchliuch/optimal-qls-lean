import OptimalQLS.Refinement.Repetition.Complete
import OptimalQLS.PolynomialTransform.NamedCircuit

/-! # Literal coordinate changes of supplied whole oracle registers -/
noncomputable section
namespace OptimalQLS.OracleCoordinates
open Matrix LowerBounds PolynomialTransform
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 500000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
universe u v u' v'
variable {A : Type u} {B : Type v} {A' : Type u'} {B' : Type v'} {W G : Type*}
  [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype A'] [DecidableEq A'] [Fintype B'] [DecidableEq B']
  [Fintype W] [DecidableEq W]

/-- Source coordinates change; the physical multiplicity/control wires do not. -/
def port (e : A ≃ A') (p : QueryPort A W) : QueryPort A' W :=
  ⟨p.multiplicity,(Equiv.prodCongr e.symm (Equiv.refl _)).trans p.wiring,p.control⟩

theorem port_readout (e : A ≃ A') (p : QueryPort A W) (w : W) :
    (port e p).control (((port e p).wiring.symm w).2)=p.control ((p.wiring.symm w).2) := rfl

theorem port_apply (e : A ≃ A') (p : QueryPort A W) (U : Matrix.unitaryGroup A' ℂ) :
    (port e p).apply U=p.apply (rewireUnitary e.symm U) := by
  apply Subtype.ext
  ext i j
  simp only [port,QueryPort.apply,rewireUnitary,controlledUnitary,Matrix.submatrix_apply,
    Equiv.symm_trans_apply,Equiv.symm_apply_apply,Equiv.prodCongr_symm,Equiv.symm_symm,
    Equiv.prodCongr_apply,Equiv.refl_apply,Equiv.trans_apply,Matrix.blockDiagonal_apply]
  split_ifs <;> simp_all [Matrix.one_apply,e.injective.eq_iff]

theorem rewire_inv (e : A ≃ A') (U : Matrix.unitaryGroup A ℂ) :
    rewireUnitary e U⁻¹=(rewireUnitary e U)⁻¹ := by
  apply Subtype.ext
  simp [rewireUnitary,Matrix.star_eq_conjTranspose,Matrix.conjTranspose_submatrix]

theorem port_apply_adjoint (e : A ≃ A') (p : QueryPort A W)
    (U : Matrix.unitaryGroup A' ℂ) (adj : Bool) :
    (port e p).apply (if adj then U⁻¹ else U)=
      p.apply (if adj then (rewireUnitary e.symm U)⁻¹ else rewireUnitary e.symm U) := by
  cases adj <;> simp [port_apply,rewire_inv]

def instruction (ea : A ≃ A') (eb : B ≃ B') : QueryInstruction A B W → QueryInstruction A' B' W
  | .work U => .work U
  | .matrixCall p b => .matrixCall (port ea p) b
  | .vectorCall p b => .vectorCall (port eb p) b

def circuit (ea : A ≃ A') (eb : B ≃ B') (c : QueryCircuit A B W) : QueryCircuit A' B' W :=
  c.map (instruction ea eb)

theorem circuit_eval (ea : A ≃ A') (eb : B ≃ B') (c : QueryCircuit A B W)
    (UA : Matrix.unitaryGroup A' ℂ) (Ub : Matrix.unitaryGroup B' ℂ) :
    (circuit ea eb c).eval UA Ub=c.eval (rewireUnitary ea.symm UA) (rewireUnitary eb.symm Ub) := by
  induction c with
  | nil => rfl
  | cons g c ih =>
    simp only [circuit] at ih
    cases g <;> simp only [circuit,List.map_cons,instruction,QueryCircuit.eval,
      QueryInstruction.eval,port_apply_adjoint] <;> rw [ih]

theorem circuit_counts (ea : A ≃ A') (eb : B ≃ B') (c : QueryCircuit A B W) :
    (circuit ea eb c).matrixQueries=c.matrixQueries ∧
    (circuit ea eb c).vectorQueries=c.vectorQueries := by
  induction c with
  | nil => exact ⟨rfl,rfl⟩
  | cons g c ih => cases g <;> simp_all [circuit,instruction,QueryCircuit.matrixQueries,QueryCircuit.vectorQueries]

def namedInstruction (ea : A ≃ A') (eb : B ≃ B') :
    NamedInstruction G A B W → NamedInstruction G A' B' W
  | .gate g => .gate g
  | .matrixCall p b => .matrixCall (port ea p) b
  | .vectorCall p b => .vectorCall (port eb p) b

def namedCircuit (ea : A ≃ A') (eb : B ≃ B') (c : NamedCircuit G A B W) : NamedCircuit G A' B' W :=
  c.map (namedInstruction ea eb)

theorem namedCircuit_toQuery (ea : A ≃ A') (eb : B ≃ B') (g : G → Matrix.unitaryGroup W ℂ)
    (c : NamedCircuit G A B W) :
    (namedCircuit ea eb c).toQuery g=circuit ea eb (c.toQuery g) := by
  induction c with
  | nil => rfl
  | cons x c ih => cases x <;> simp_all [namedCircuit,namedInstruction,circuit,instruction,
      NamedCircuit.toQuery,NamedInstruction.toQuery]

theorem namedCircuit_workGates (ea : A ≃ A') (eb : B ≃ B') (c : NamedCircuit G A B W) :
    (namedCircuit ea eb c).workGates=c.workGates := by
  induction c with
  | nil => rfl
  | cons x c ih => cases x <;> simp_all [namedCircuit,namedInstruction,NamedCircuit.workGates]

def program (ea : A ≃ A') (eb : B ≃ B') {d : ℕ} :
    {w : ℕ} → FiniteOracleProgram A B d w → FiniteOracleProgram A' B' d w
  | _,.output s a => .output s a
  | _,.matrixQuery p a c => .matrixQuery (port ea p) a (program ea eb c)
  | _,.vectorQuery p a c => .vectorQuery (port eb p) a (program ea eb c)
  | _,.instrument r dims K hn cs => .instrument r dims K hn (fun i=>program ea eb (cs i))

theorem program_density (ea : A ≃ A') (eb : B ≃ B') {d w : ℕ}
    (c : FiniteOracleProgram A B d w) (UA : Matrix.unitaryGroup A' ℂ)
    (Ub : Matrix.unitaryGroup B' ℂ) (select : Bool → Bool) (v : Fin w → ℂ) :
    (program ea eb c).executeDensity UA Ub select v=
      c.executeDensity (rewireUnitary ea.symm UA) (rewireUnitary eb.symm Ub) select v := by
  induction c with
  | output s a => rfl
  | matrixQuery p adj c ih => simp only [program,FiniteOracleProgram.executeDensity,port_apply_adjoint]; exact ih _
  | vectorQuery p adj c ih => simp only [program,FiniteOracleProgram.executeDensity,port_apply_adjoint]; exact ih _
  | instrument r dims K hn cs ih =>
    simp only [program,FiniteOracleProgram.executeDensity]
    exact Finset.sum_congr rfl (fun i _=>ih i _)

theorem program_successProbability (ea : A ≃ A') (eb : B ≃ B') {d w : ℕ}
    (c : FiniteOracleProgram A B d w) (UA : Matrix.unitaryGroup A' ℂ)
    (Ub : Matrix.unitaryGroup B' ℂ) (v : Fin w → ℂ) :
    (program ea eb c).successProbability UA Ub v=
      c.successProbability (rewireUnitary ea.symm UA) (rewireUnitary eb.symm Ub) v := by
  simp only [FiniteOracleProgram.successProbability,program_density]

theorem program_conditionalOutput (ea : A ≃ A') (eb : B ≃ B') {d w : ℕ}
    (c : FiniteOracleProgram A B d w) (UA : Matrix.unitaryGroup A' ℂ)
    (Ub : Matrix.unitaryGroup B' ℂ) (v : Fin w → ℂ) :
    (program ea eb c).conditionalOutput UA Ub v=
      c.conditionalOutput (rewireUnitary ea.symm UA) (rewireUnitary eb.symm Ub) v := by
  simp only [FiniteOracleProgram.conditionalOutput,program_density,program_successProbability]


theorem program_matrixDepth (ea : A ≃ A') (eb : B ≃ B') {d w : ℕ}
    (c : FiniteOracleProgram A B d w) :
    Refinement.Repetition.matrixDepth (program ea eb c)=Refinement.Repetition.matrixDepth c := by
  induction c with
  | output s a => rfl
  | matrixQuery p a c ih => simpa [program,Refinement.Repetition.matrixDepth] using congrArg Nat.succ ih
  | vectorQuery p a c ih => exact ih
  | instrument r dims K hn cs ih => simp only [program,Refinement.Repetition.matrixDepth,ih]

theorem program_vectorDepth (ea : A ≃ A') (eb : B ≃ B') {d w : ℕ}
    (c : FiniteOracleProgram A B d w) : (program ea eb c).vectorDepth=c.vectorDepth := by
  induction c with
  | output s a => rfl
  | matrixQuery p a c ih => exact ih
  | vectorQuery p a c ih => simpa [program,FiniteOracleProgram.vectorDepth] using congrArg Nat.succ ih
  | instrument r dims K hn cs ih => simp only [program,FiniteOracleProgram.vectorDepth,ih]

theorem program_registerBound (ea : A ≃ A') (eb : B ≃ B') {d w : ℕ}
    (c : FiniteOracleProgram A B d w) (m : ℕ) :
    Refinement.Repetition.RegisterBound m (program ea eb c) ↔ Refinement.Repetition.RegisterBound m c := by
  induction c with
  | output s a => rfl
  | matrixQuery p a c ih => simp only [program,Refinement.Repetition.RegisterBound,ih]
  | vectorQuery p a c ih => simp only [program,Refinement.Repetition.RegisterBound,ih]
  | instrument r dims K hn cs ih => simp only [program,Refinement.Repetition.RegisterBound,ih]

end OptimalQLS.OracleCoordinates
