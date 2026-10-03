import OptimalQLS.PolynomialTransform.Encoding
import OptimalQLS.PolynomialTransform.QSVTCircuit

/-! # Uniform, exact polynomial block encodings with proved separate query counts -/
noncomputable section
namespace OptimalQLS.PolynomialTransform
open Matrix Polynomial
open scoped Matrix.Norms.L2Operator
variable {W V S D B : Type*} [Fintype W] [DecidableEq W] [Fintype V] [DecidableEq V]
  [Fintype S] [DecidableEq S] [Fintype D] [DecidableEq D] [Fintype B] [DecidableEq B]

/-- Whole-workspace relabeling, represented by an actual query port. -/
def relabelPort (e : W ≃ V) : QueryPort W V where
  multiplicity := 1
  wiring := (wholeOraclePort W).wiring.trans e
  control := fun _ => true

@[simp] theorem relabelPort_apply (e : W ≃ V) (U : Matrix.unitaryGroup W ℂ) :
    (relabelPort e).apply U=rewireUnitary e U := by
  apply Subtype.ext
  ext i j
  simp [relabelPort,wholeOraclePort,QueryPort.apply,rewireUnitary,controlledUnitary,Matrix.blockDiagonal]

/-- The complete query list in the paper's signal/data register convention. -/
def boundedTransformCircuit (s₀ : S) (z₀ : Circle) (zs : List Circle) :
    QueryCircuit (S × D) B (((Bool × Bool) × S) × D) :=
  (evenQSVTCircuit (B := B) (signalInjection s₀) (signalInjection_isometry s₀) z₀ zs).lift (relabelPort (twoLabelSignalEquiv S D))

theorem boundedTransformCircuit_eval (s₀ : S) (z₀ : Circle) (zs : List Circle)
    (U : Matrix.unitaryGroup (S × D) ℂ) (Ub : Matrix.unitaryGroup B ℂ) :
    (boundedTransformCircuit s₀ z₀ zs).eval U Ub=boundedTransformUnitary s₀ U z₀ zs := by
  rw [boundedTransformCircuit,QueryCircuit.lift_eval,evenQSVTCircuit_eval,relabelPort_apply]
  rfl

theorem boundedTransformCircuit_counts (s₀ : S) (z₀ : Circle) (zs : List Circle) :
    (boundedTransformCircuit (D := D) (B := B) s₀ z₀ zs).matrixQueries=4*zs.length ∧
    (boundedTransformCircuit (D := D) (B := B) s₀ z₀ zs).vectorQueries=0 := by
  simpa only [boundedTransformCircuit,(QueryCircuit.lift_counts _ _).1,
    (QueryCircuit.lift_counts _ _).2] using
    evenQSVTCircuit_counts (B := B) (signalInjection (D := D) s₀) (signalInjection_isometry s₀) z₀ zs

/-- Lemma 2.4: exact normalization-one encoding and the actual O(d+1)
query program, uniformly chosen from the polynomial and signal register.
Elementary-gate synthesis is developed separately from this query theorem. -/
theorem lemma24_exact_query_encoding [Nonempty D] (s₀ : S) (p : ℝ[X])
    (hp : Function.Even p.eval) (hbound : ∀ x : ℝ, |x| ≤ 1 → |p.eval x| ≤ 1) :
    ∃ c : QueryCircuit (S × D) B (((Bool × Bool) × S) × D),
      c.matrixQueries ≤ 4*p.natDegree ∧ c.vectorQueries=0 ∧
      ∀ (U : Matrix.unitaryGroup (S × D) ℂ) (Ub : Matrix.unitaryGroup B ℂ) (A : Matrix D D ℂ),
        A.IsHermitian → IsBlockEncoding s₀ 1 0 U A →
        IsBlockEncoding ((false,false),s₀) 1 0 (c.eval U Ub) (Polynomial.aeval A (liftReal p)) := by
  obtain ⟨z₀,zs,hlen,henc⟩ := bounded_even_exact_encoding (D := D) s₀ p hp hbound
  refine ⟨boundedTransformCircuit s₀ z₀ zs,?_,(boundedTransformCircuit_counts s₀ z₀ zs).2,?_⟩
  · rw [(boundedTransformCircuit_counts s₀ z₀ zs).1]
    omega
  · intro U Ub A hA hb
    rw [boundedTransformCircuit_eval]
    exact henc U A hA hb

/-- Zero vector queries is verified at the whole-unitary level. -/
theorem boundedTransformCircuit_vector_independence (s₀ : S) (z₀ : Circle) (zs : List Circle)
    (U : Matrix.unitaryGroup (S × D) ℂ) (Ub Vb : Matrix.unitaryGroup B ℂ) :
    (boundedTransformCircuit s₀ z₀ zs).eval U Ub=(boundedTransformCircuit s₀ z₀ zs).eval U Vb :=
  QueryCircuit.eval_independent_vector_oracle _ (boundedTransformCircuit_counts s₀ z₀ zs).2 U Ub Vb

/-- The signal labels have exactly the size of a+2 qubits when the original
signal has 2^a basis states. -/
theorem transformed_signal_cardinality (a : ℕ) :
    Fintype.card ((Bool × Bool) × Fin (2^a))=2^(a+2) := by
  simp [Fintype.card_prod,pow_add]
  ring

end OptimalQLS.PolynomialTransform
