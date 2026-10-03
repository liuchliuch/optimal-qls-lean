import OptimalQLS.LowerBounds.VariableBorn

/-!
# One concrete finitely branching two-oracle instruction semantics

The workspace dimension may change at each measurement outcome. Every
instrument carries literal rectangular Kraus matrices and their completeness
identity. Query nodes use actual controlled/adjoint query ports. A terminal
node returns its vector in the fixed output register and records success or
failure. Terminal paths are extracted by recursion from this same syntax.
-/
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
namespace OptimalQLS.LowerBounds
open Matrix
universe u v

inductive FiniteOracleProgram (A : Type u) (B : Type v) (d : ℕ) : ℕ → Type (max u v) where
  | output (success : Bool) (aborted : Bool) : FiniteOracleProgram A B d d
  | matrixQuery {w : ℕ} (port : OptimalQLS.QueryPort A (Fin w)) (adjoint : Bool)
      (next : FiniteOracleProgram A B d w) : FiniteOracleProgram A B d w
  | vectorQuery {w : ℕ} (port : OptimalQLS.QueryPort B (Fin w)) (adjoint : Bool)
      (next : FiniteOracleProgram A B d w) : FiniteOracleProgram A B d w
  | instrument {w : ℕ} (r : ℕ) (nextDimension : Fin r → ℕ)
      (K : ∀ i, Matrix (Fin (nextDimension i)) (Fin w) ℂ)
      (normalized : ∑ i, (K i).conjTranspose * K i = 1)
      (next : ∀ i, FiniteOracleProgram A B d (nextDimension i)) : FiniteOracleProgram A B d w

variable {A : Type u} {B : Type v} {d w : ℕ}

def FiniteOracleProgram.Terminal : {w : ℕ} → FiniteOracleProgram A B d w → Type
  | _, .output _ _ => Unit
  | _, .matrixQuery _ _ next => next.Terminal
  | _, .vectorQuery _ _ next => next.Terminal
  | _, .instrument r _ _ _ next => (i : Fin r) × (next i).Terminal

instance FiniteOracleProgram.terminalFintype (tree : FiniteOracleProgram A B d w) : Fintype tree.Terminal := by
  induction tree with
  | output flag aborted => exact inferInstanceAs (Fintype Unit)
  | matrixQuery port adj next ih => exact ih
  | vectorQuery port adj next ih => exact ih
  | instrument r dims K hn next ih =>
    letI : ∀ i : Fin r, Fintype (next i).Terminal := ih
    exact inferInstanceAs (Fintype ((i : Fin r) × (next i).Terminal))

def FiniteOracleProgram.terminalPath : {w : ℕ} → (tree : FiniteOracleProgram A B d w) →
    VariableQueryPath A B w → tree.Terminal → VariableQueryPath A B d
  | _, .output _ _, path => fun _ => path
  | _, .matrixQuery port adj next, path => next.terminalPath (.matrixQuery port adj path)
  | _, .vectorQuery port adj next, path => next.terminalPath (.vectorQuery port adj path)
  | _, .instrument _ _ K _ next, path => fun k => (next k.1).terminalPath (.work (K k.1) path) k.2

def FiniteOracleProgram.terminalSuccess : {w : ℕ} → (tree : FiniteOracleProgram A B d w) → tree.Terminal → Bool
  | _, .output flag _ => fun _ => flag
  | _, .matrixQuery _ _ next => next.terminalSuccess
  | _, .vectorQuery _ _ next => next.terminalSuccess
  | _, .instrument _ _ _ _ next => fun k => (next k.1).terminalSuccess k.2

/-- A separate tag records synthetic stopping/fuel aborts. Ordinary programs
return `aborted = false`; truncation marks exactly the discarded branches. -/
def FiniteOracleProgram.terminalAbortFlag : {w : ℕ} → (tree : FiniteOracleProgram A B d w) → tree.Terminal → Bool
  | _, .output _ aborted => fun _ => aborted
  | _, .matrixQuery _ _ next => next.terminalAbortFlag
  | _, .vectorQuery _ _ next => next.terminalAbortFlag
  | _, .instrument _ _ _ _ next => fun k => (next k.1).terminalAbortFlag k.2

variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

def FiniteOracleProgram.executeDensity (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ)
    (select : Bool → Bool) : {w : ℕ} → FiniteOracleProgram A B d w → (Fin w → ℂ) → Matrix (Fin d) (Fin d) ℂ
  | _, .output flag _, psi => if select flag then pureDensity psi else 0
  | w, .matrixQuery port adj next, psi => next.executeDensity UA Ub select
      ((port.apply (if adj then UA⁻¹ else UA) : Matrix (Fin w) (Fin w) ℂ) *ᵥ psi)
  | w, .vectorQuery port adj next, psi => next.executeDensity UA Ub select
      ((port.apply (if adj then Ub⁻¹ else Ub) : Matrix (Fin w) (Fin w) ℂ) *ᵥ psi)
  | _, .instrument _ _ K _ next, psi => ∑ i, (next i).executeDensity UA Ub select (K i *ᵥ psi)

def FiniteOracleProgram.executeMass (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) :
    {w : ℕ} → FiniteOracleProgram A B d w → (Fin w → ℂ) → ℝ
  | _, .output _ _, psi => bornMass psi
  | w, .matrixQuery port adj next, psi => next.executeMass UA Ub
      ((port.apply (if adj then UA⁻¹ else UA) : Matrix (Fin w) (Fin w) ℂ) *ᵥ psi)
  | w, .vectorQuery port adj next, psi => next.executeMass UA Ub
      ((port.apply (if adj then Ub⁻¹ else Ub) : Matrix (Fin w) (Fin w) ℂ) *ᵥ psi)
  | _, .instrument _ _ K _ next, psi => ∑ i, (next i).executeMass UA Ub (K i *ᵥ psi)

/-- The extracted paths give exactly the same successful/failing density
matrix as recursive execution, including each actual measurement branch. -/
theorem FiniteOracleProgram.terminalDensity_eq_execute (tree : FiniteOracleProgram A B d w)
    (path : VariableQueryPath A B w) (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ)
    (select : Bool → Bool) :
    (∑ k : tree.Terminal, if select (tree.terminalSuccess k) then
      pureDensity ((tree.terminalPath path k).state UA Ub) else 0) =
      tree.executeDensity UA Ub select (path.state UA Ub) := by
  induction tree with
  | output flag aborted => simp [Terminal, terminalPath, terminalSuccess, executeDensity]
  | matrixQuery port adj next ih => exact ih (.matrixQuery port adj path)
  | vectorQuery port adj next ih => exact ih (.vectorQuery port adj path)
  | instrument r dims K hn next ih =>
    change (∑ k : (i : Fin r) × (next i).Terminal,
      if select ((next k.1).terminalSuccess k.2) then pureDensity
        (((next k.1).terminalPath (.work (K k.1) path) k.2).state UA Ub) else 0) = _
    rw [Fintype.sum_sigma]
    exact Finset.sum_congr rfl (fun i _ => ih i (.work (K i) path))

/-- Kraus normalization proves total terminal Born mass, rather than taking
probabilistic branch normalization as an independent certificate. -/
theorem FiniteOracleProgram.executeMass_eq (tree : FiniteOracleProgram A B d w)
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) (psi : Fin w → ℂ) :
    tree.executeMass UA Ub psi = bornMass psi := by
  induction tree with
  | output flag aborted => rfl
  | matrixQuery port adj next ih => exact (ih _).trans (unitary_bornMass _ psi)
  | vectorQuery port adj next ih => exact (ih _).trans (unitary_bornMass _ psi)
  | instrument r dims K hn next ih =>
    simp only [executeMass, ih]
    exact varying_instrument_bornMass dims K hn psi

theorem FiniteOracleProgram.terminalBorn_eq_execute (tree : FiniteOracleProgram A B d w)
    (path : VariableQueryPath A B w) (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) :
    (∑ k : tree.Terminal, (tree.terminalPath path k).bornWeight UA Ub) =
      tree.executeMass UA Ub (path.state UA Ub) := by
  induction tree with
  | output flag aborted => simp [Terminal, terminalPath, executeMass, VariableQueryPath.bornWeight, bornMass]
  | matrixQuery port adj next ih => exact ih (.matrixQuery port adj path)
  | vectorQuery port adj next ih => exact ih (.vectorQuery port adj path)
  | instrument r dims K hn next ih =>
    change (∑ k : (i : Fin r) × (next i).Terminal,
      ((next k.1).terminalPath (.work (K k.1) path) k.2).bornWeight UA Ub) = _
    rw [Fintype.sum_sigma]
    exact Finset.sum_congr rfl (fun i _ => ih i (.work (K i) path))

theorem FiniteOracleProgram.terminalBorn_sum (tree : FiniteOracleProgram A B d w)
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) (psi : Fin w → ℂ) :
    (∑ k : tree.Terminal, (tree.terminalPath (.initial psi) k).bornWeight UA Ub) = bornMass psi := by
  rw [tree.terminalBorn_eq_execute, tree.executeMass_eq]
  rfl

end OptimalQLS.LowerBounds
