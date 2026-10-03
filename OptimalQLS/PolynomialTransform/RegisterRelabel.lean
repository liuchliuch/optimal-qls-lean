import OptimalQLS.PolynomialTransform.ElementaryEncoding
import OptimalQLS.TransducerCompiler.HadamardClock

/-! # Explicit binary-coordinate interfaces for the input signal register -/
noncomputable section
namespace OptimalQLS.PolynomialTransform
open Matrix Polynomial DirtyAncilla
variable {A S B ι D : Type*} [Fintype A] [DecidableEq A] [Fintype S] [DecidableEq S]
  [Fintype B] [DecidableEq B] [Fintype ι] [DecidableEq ι] [Fintype D] [DecidableEq D]

def ElementaryInstruction.relabelMatrix (e : S ≃ A) : ElementaryInstruction A B ι D → ElementaryInstruction S B ι D
  | .gate g => .gate g
  | .matrixCall p b => .matrixCall (p.comp (relabelPort e)) b
  | .vectorCall p b => .vectorCall p b

def ElementaryCircuit.relabelMatrix (e : S ≃ A) (c : ElementaryCircuit A B ι D) :
    ElementaryCircuit S B ι D := c.map (ElementaryInstruction.relabelMatrix e)

theorem ElementaryCircuit.relabelMatrix_counts (e : S ≃ A) (c : ElementaryCircuit A B ι D) :
    (c.relabelMatrix e).toQuery.matrixQueries=c.toQuery.matrixQueries ∧
    (c.relabelMatrix e).toQuery.vectorQueries=c.toQuery.vectorQueries ∧
    (c.relabelMatrix e).workGates=c.workGates := by
  induction c with
  | nil => exact ⟨rfl,rfl,rfl⟩
  | cons g c ih =>
    cases g <;> simp_all [relabelMatrix,ElementaryInstruction.relabelMatrix,ElementaryCircuit.toQuery,
      ElementaryInstruction.toQuery,QueryCircuit.matrixQueries,QueryCircuit.vectorQueries,ElementaryCircuit.workGates]

theorem ElementaryCircuit.relabelMatrix_eval (e : S ≃ A) (c : ElementaryCircuit A B ι D)
    (U : Matrix.unitaryGroup S ℂ) (Ub : Matrix.unitaryGroup B ℂ) :
    (c.relabelMatrix e).toQuery.eval U Ub=c.toQuery.eval ((relabelPort e).apply U) Ub := by
  induction c with
  | nil => rfl
  | cons g c ih =>
    dsimp only [relabelMatrix,ElementaryCircuit.toQuery] at ih
    cases g with
    | gate g =>
      change _ * _ = _ * _
      rw [ih]
      rfl
    | matrixCall p b =>
      change _ * (p.comp (relabelPort e)).apply (if b then U⁻¹ else U)=
        _ * p.apply (if b then ((relabelPort e).apply U)⁻¹ else (relabelPort e).apply U)
      rw [ih,QueryPort.comp_apply]
      cases b <;> simp [QueryPort.apply_inv]
    | vectorCall p b =>
      change _ * _ = _ * _
      rw [ih]
      rfl

theorem signalBlock_relabel (e : S ≃ A) (s₀ : S) (U : Matrix.unitaryGroup (S × D) ℂ) :
    signalBlock (e s₀) (rewireUnitary (Equiv.prodCongr e (Equiv.refl D)) U).val=signalBlock s₀ U.val := by
  ext i j
  rw [signalBlock_entries,signalBlock_entries]
  simp [rewireUnitary]

/-- The full elementary endpoint in any explicitly supplied binary signal coordinates. -/
theorem lemma24_elementary_encoding_relabel [Nonempty D] (a : ℕ) (e : S ≃ (Fin a → Bool))
    (s₀ : S) (he : e s₀=(fun _ => false)) (p : ℝ[X])
    (hp : Function.Even p.eval) (hbound : ∀ x : ℝ, |x| ≤ 1 → |p.eval x| ≤ 1) :
    ∃ out : ElementaryCircuit (S × D) B (QSVTWire a) D,
      out.toQuery.matrixQueries ≤ 4*p.natDegree ∧ out.toQuery.vectorQueries=0 ∧
      out.workGates ≤ 6248*(p.natDegree+1)*(a+1) ∧
      ∀ (U : Matrix.unitaryGroup (S × D) ℂ) (Ub : Matrix.unitaryGroup B ℂ)
        (A₀ : Matrix D D ℂ), A₀.IsHermitian → IsBlockEncoding s₀ 1 0 U A₀ →
        IsBlockEncoding (physicalZero a) 1 0 (out.toQuery.eval U Ub)
          (Polynomial.aeval A₀ (liftReal p)) := by
  obtain ⟨c,hq,hv,hg,henc⟩ := lemma24_elementary_encoding (D := D) (B := B) a p hp hbound
  let e' := Equiv.prodCongr e (Equiv.refl D)
  refine ⟨c.relabelMatrix e',?_,?_,?_,?_⟩
  · simpa only [ElementaryCircuit.relabelMatrix_counts] using hq
  · simpa only [ElementaryCircuit.relabelMatrix_counts] using hv
  · simpa only [ElementaryCircuit.relabelMatrix_counts] using hg
  · intro U Ub A₀ hA hU
    rw [ElementaryCircuit.relabelMatrix_eval,relabelPort_apply]
    apply henc _ Ub A₀ hA
    have hb := signalBlock_relabel e s₀ U
    rw [he] at hb
    simpa only [IsBlockEncoding,hb,e'] using hU

/-- Standard Fin(2^a) coordinates with the literal all-zero input label. -/
theorem bitsFin_zero (a : ℕ) :
    (TransducerCompiler.HadamardClock.bitsFinEquiv a).symm ⟨0,by positivity⟩=(fun _ => false) := by
  apply (TransducerCompiler.HadamardClock.bitsFinEquiv a).injective
  simp

/-- A fixed prefix of named physical qubits, in their existing order. -/
def BitPrefix : ℕ → ℕ → Type
  | 0,a => Fin a → Bool
  | n+1,a => Bool × BitPrefix n a

def bitPrefixZero : (n a : ℕ) → BitPrefix n a
  | 0,_ => fun _ => false
  | n+1,a => (false,bitPrefixZero n a)

def bitPrefixEquiv : (n a : ℕ) → BitPrefix n a ≃ (Fin (a+n) → Bool)
  | 0,a => Equiv.refl _
  | n+1,a => (Equiv.prodCongr (Equiv.refl Bool) (bitPrefixEquiv n a)).trans
      (Fin.consEquiv (fun _ : Fin (a+n+1) => Bool))

theorem bitPrefixEquiv_zero (n a : ℕ) :
    bitPrefixEquiv n a (bitPrefixZero n a)=(fun _ => false) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change Fin.cons false (bitPrefixEquiv n a (bitPrefixZero n a))=(fun _ => false)
    rw [ih]
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl

end OptimalQLS.PolynomialTransform
