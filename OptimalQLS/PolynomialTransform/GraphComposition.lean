import OptimalQLS.PolynomialTransform.GraphAttachedGates

/-! # Joint graph-call and QSVT-work replacement with shared scratch -/
noncomputable section
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 800000
namespace OptimalQLS.PolynomialTransform
open Matrix Polynomial DirtyAncilla
variable {D B : Type*} [Fintype D] [DecidableEq D] [Fintype B] [DecidableEq B]

/-- The actual Hermitian graph oracle in its literal binary signal coordinates. -/
def binaryGraphOracle (a : ℕ) (κ : ℝ) (hκ : 0 < κ)
    (U : Matrix.unitaryGroup ((Fin a → Bool) × D) ℂ) :
    Matrix.unitaryGroup ((Fin (a+4) → Bool) × (Fin 4 × D)) ℂ :=
  rewireUnitary (Equiv.prodCongr (graphSignalBits a) (Equiv.refl (Fin 4 × D)))
    (GraphEncoding.physicalEncoding κ hκ U)

theorem binaryGraphOracle_inv (a : ℕ) (κ : ℝ) (hκ : 0 < κ)
    (U : Matrix.unitaryGroup ((Fin a → Bool) × D) ℂ) :
    (binaryGraphOracle a κ hκ U)⁻¹=binaryGraphOracle a κ hκ U := by
  apply Subtype.ext
  exact (GraphEncoding.physicalEncoding_hermitian κ hκ U).submatrix _

/-- Instantiate this compiler with the graph worker's actual masked-call lists.
Every macro is evaluated on the shared clean subspace, at its actual boundary. -/
theorem graphTransform_from_masked_calls (a : ℕ) (κ : ℝ) (hκ : 0 < κ)
    (z₀ : Circle) (zs : List Circle) (K : ℕ)
    (calls : Bool × Bool → ElementaryCircuit ((Fin a → Bool) × D) B GraphLocalWire ((Fin a → Bool) × D))
    (hq : ∀ mask, (calls mask).toQuery.matrixQueries=2 ∧ (calls mask).toQuery.vectorQueries=0)
    (hg : ∀ mask, (calls mask).workGates ≤ K)
    (hcall : ∀ mask (U : Matrix.unitaryGroup ((Fin a → Bool) × D) ℂ) (Ub : Matrix.unitaryGroup B ℂ),
      ((calls mask).toQuery.eval U Ub).val*basisInsertion graphLocalClean=
        basisInsertion graphLocalClean*
          ((GraphEncoding.maskedGraphPort (GraphEncoding.PhysicalSignal (Fin a → Bool) × (Fin 4 × D)) mask).apply
            (GraphEncoding.physicalEncoding κ hκ U)).val) :
    ∃ out : GraphAttachedCircuit a D B,
      (out.toQuery (GraphAttachedGate.eval a)).matrixQueries=8*zs.length ∧
      (out.toQuery (GraphAttachedGate.eval a)).vectorQueries=0 ∧
      out.workGates ≤ (6248*(a+5)+4*K)*(zs.length+1) ∧
      ∀ (U : Matrix.unitaryGroup ((Fin a → Bool) × D) ℂ) (Ub : Matrix.unitaryGroup B ℂ),
        ((out.toQuery (GraphAttachedGate.eval a)).eval U Ub).val*basisInsertion (physicalClean (a+4))=
          basisInsertion (physicalClean (a+4))*
            (boundedTransformUnitary (fun _ : Fin (a+4) => false) (binaryGraphOracle a κ hκ U) z₀ zs).val := by
  let c := boundedTransformCircuit (D := Fin 4 × D) (B := B) (fun _ : Fin (a+4) => false) z₀ zs
  have hwork : ∀ U, QueryInstruction.work U ∈ c → ∃ code : GraphAttachedCircuit a D B,
      (code.toQuery (GraphAttachedGate.eval a)).matrixQueries=0 ∧
      (code.toQuery (GraphAttachedGate.eval a)).vectorQueries=0 ∧ code.workGates ≤ 781*(a+5) ∧
      ∀ UA Ub, ((code.toQuery (GraphAttachedGate.eval a)).eval UA Ub).val*basisInsertion (physicalClean (a+4))=
        basisInsertion (physicalClean (a+4))*U.val := by
    intro U hU
    obtain ⟨code,hlen,he⟩ := bounded_work_synthesis (a+4) z₀ zs U hU
    refine ⟨attachedQSPMacro a code,?_,?_,?_,?_⟩
    · rw [attachedQSPMacro_toQuery]; exact (elementaryMacro_queries _).1
    · rw [attachedQSPMacro_toQuery]; exact (elementaryMacro_queries _).2
    · rw [attachedQSPMacro_workGates]; simpa [Nat.add_assoc] using hlen
    · intro UA Ub
      rw [attachedQSPMacro_toQuery,elementaryMacro_eval]
      exact he
  have hquery : ∀ p adj, QueryInstruction.matrixCall p adj ∈ c → ∃ code : GraphAttachedCircuit a D B,
      (code.toQuery (GraphAttachedGate.eval a)).matrixQueries=2 ∧
      (code.toQuery (GraphAttachedGate.eval a)).vectorQueries=0 ∧ code.workGates ≤ K ∧
      ∀ UA Ub, ((code.toQuery (GraphAttachedGate.eval a)).eval UA Ub).val*basisInsertion (physicalClean (a+4))=
        basisInsertion (physicalClean (a+4))*(p.apply
          (if adj then (binaryGraphOracle a κ hκ UA)⁻¹ else binaryGraphOracle a κ hκ UA)).val := by
    intro p adj hp
    obtain ⟨branch,hbranch⟩ := bounded_query_controls _ z₀ zs p adj hp
    refine ⟨attachGraphCircuit a (calls (branch,adj)),?_,?_,?_,?_⟩
    · exact (attachGraphCircuit_counts _ _).1.trans (hq _).1
    · exact (attachGraphCircuit_counts _ _).2.1.trans (hq _).2
    · rw [attachGraphCircuit_workGates]; exact hg _
    · intro UA Ub
      rw [attachGraphCircuit_eval,binaryGraphOracle_inv,ite_self,hbranch]
      rw [binaryGraphOracle,nested_mask_relabel]
      exact graphAttached_intertwines a _ _ (hcall (branch,adj) UA Ub)
  obtain ⟨out,hm,hv,hworkBound,he⟩ := refine_matrix_and_work (GraphAttachedGate.eval a) c
    (boundedTransformCircuit_counts _ z₀ zs).2 (basisInsertion (physicalClean (a+4)))
    (binaryGraphOracle a κ hκ) (781*(a+5)) K 2 hwork hquery
  refine ⟨out,?_,hv,?_,?_⟩
  · rw [(boundedTransformCircuit_counts _ z₀ zs).1] at hm
    omega
  · have hw := bounded_work_count (D := Fin 4 × D) (B := B) (a+4) z₀ zs
    change workInstructions c=8*zs.length+4 at hw
    have hmc := (boundedTransformCircuit_counts (D := Fin 4 × D) (B := B) (fun _ : Fin (a+4) => false) z₀ zs).1
    change c.matrixQueries=4*zs.length at hmc
    rw [hw,hmc] at hworkBound
    nlinarith
  · intro U Ub
    simpa only [c,boundedTransformCircuit_eval] using he U Ub

end OptimalQLS.PolynomialTransform
