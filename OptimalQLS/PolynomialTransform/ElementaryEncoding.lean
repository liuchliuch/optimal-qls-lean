import OptimalQLS.PolynomialTransform.WorkClassification

/-! # Lemma 2.4 with an actual elementary circuit and aggregate gate bounds -/
noncomputable section
namespace OptimalQLS.PolynomialTransform
open Matrix Polynomial DirtyAncilla
open scoped Matrix.Norms.L2Operator
variable {D B : Type*} [Fintype D] [DecidableEq D] [Fintype B] [DecidableEq B]

/-- Uniform elementary implementation of the phase list on a+5 signal qubits. -/
theorem boundedTransform_elementary_synthesis (a : ℕ) (z₀ : Circle) (zs : List Circle) :
    ∃ out : ElementaryCircuit ((Fin a → Bool) × D) B (QSVTWire a) D,
      out.toQuery.matrixQueries=4*zs.length ∧ out.toQuery.vectorQueries=0 ∧
      out.workGates ≤ 6248*(zs.length+1)*(a+1) ∧
      ∀ (UA : Matrix.unitaryGroup ((Fin a → Bool) × D) ℂ) (Ub : Matrix.unitaryGroup B ℂ),
        (out.toQuery.eval UA Ub).val*basisInsertion (physicalClean a)=
          basisInsertion (physicalClean a)*
            (boundedTransformUnitary (fun _ : Fin a => false) UA z₀ zs).val := by
  let c := boundedTransformCircuit (D := D) (B := B) (fun _ : Fin a => false) z₀ zs
  have hport : ∀ U : Matrix.unitaryGroup (LogicalSignal a × D) ℂ,
      ((scratchPort (physicalEquiv a D)).apply U).val*basisInsertion (physicalClean a)=
        basisInsertion (physicalClean a)*U.val := by
    intro U
    exact scratchPort_intertwines (physicalEquiv a D) (false,false,false) U
  obtain ⟨out,hm,hv,hg,he⟩ := refine_query_circuit c (basisInsertion (physicalClean a))
    (scratchPort (physicalEquiv a D)) hport (781*(a+1)) (bounded_work_synthesis a z₀ zs)
  refine ⟨out,?_,?_,?_,?_⟩
  · exact hm.trans (boundedTransformCircuit_counts _ z₀ zs).1
  · exact hv.trans (boundedTransformCircuit_counts _ z₀ zs).2
  · have hw := bounded_work_count (D := D) (B := B) a z₀ zs
    change workInstructions c=8*zs.length+4 at hw
    rw [hw] at hg
    nlinarith
  · intro UA Ub
    simpa only [c,boundedTransformCircuit_eval] using he UA Ub

/-- Compression in a clean computational embedding is the same actual matrix block. -/
theorem signalBlock_of_clean_intertwines {S T : Type*} [Fintype S] [DecidableEq S]
    [Fintype T] [DecidableEq T] (f : S → T) (hf : Function.Injective f) (s₀ : S)
    (U : Matrix (T × D) (T × D) ℂ) (V : Matrix (S × D) (S × D) ℂ)
    (h : U*basisInsertion (fun x : S × D => (f x.1,x.2))=
      basisInsertion (fun x : S × D => (f x.1,x.2))*V) :
    signalBlock (f s₀) U=signalBlock s₀ V := by
  ext i j
  rw [signalBlock_entries,signalBlock_entries]
  have he := congrFun (congrFun h (f s₀,i)) (s₀,j)
  simpa [Matrix.mul_apply,basisInsertion,Fintype.sum_prod_type,Prod.mk.injEq,
    hf.eq_iff,ite_and,eq_comm] using he

def physicalZero (a : ℕ) : PhysicalSignal a := (false,fun _ => false)

theorem physicalClean_zero (a : ℕ) :
    physicalCleanSignal a ((false,false),fun _ : Fin a => false)=physicalZero a := by
  apply Prod.ext
  · rfl
  · funext i; cases i <;> simp [physicalCleanSignal,physicalSignalEquiv,physicalZero]

/-- Full Lemma 2.4: every bounded even real polynomial has a uniform literal
circuit with ≤4d matrix calls, no vector calls, ≤6248(d+1)(a+1) elementary
one- and two-qubit work gates, exact normalization-one encoding, and a+5 signal qubits. -/
theorem lemma24_elementary_encoding [Nonempty D] (a : ℕ) (p : ℝ[X])
    (hp : Function.Even p.eval) (hbound : ∀ x : ℝ, |x| ≤ 1 → |p.eval x| ≤ 1) :
    ∃ out : ElementaryCircuit ((Fin a → Bool) × D) B (QSVTWire a) D,
      out.toQuery.matrixQueries ≤ 4*p.natDegree ∧ out.toQuery.vectorQueries=0 ∧
      out.workGates ≤ 6248*(p.natDegree+1)*(a+1) ∧
      ∀ (UA : Matrix.unitaryGroup ((Fin a → Bool) × D) ℂ) (Ub : Matrix.unitaryGroup B ℂ)
        (A : Matrix D D ℂ), A.IsHermitian → IsBlockEncoding (fun _ : Fin a => false) 1 0 UA A →
        IsBlockEncoding (physicalZero a) 1 0 (out.toQuery.eval UA Ub)
          (Polynomial.aeval A (liftReal p)) := by
  obtain ⟨z₀,zs,hlen,henc⟩ := bounded_even_exact_encoding (D := D)
    (fun _ : Fin a => false) p hp hbound
  obtain ⟨out,hm,hv,hg,he⟩ := boundedTransform_elementary_synthesis (D := D) (B := B) a z₀ zs
  refine ⟨out,by omega,hv,hg.trans ?_,?_⟩
  · exact Nat.mul_le_mul_right (a+1) (Nat.mul_le_mul_left 6248 (by omega))
  · intro UA Ub A hA hUA
    have hb := henc UA A hA hUA
    have hc := signalBlock_of_clean_intertwines (physicalCleanSignal a)
      (physicalCleanSignal_injective a) ((false,false),fun _ : Fin a => false)
      (out.toQuery.eval UA Ub).val (boundedTransformUnitary (fun _ : Fin a => false) UA z₀ zs).val
      (he UA Ub)
    rw [physicalClean_zero] at hc
    simpa only [IsBlockEncoding,hc] using hb

end OptimalQLS.PolynomialTransform
