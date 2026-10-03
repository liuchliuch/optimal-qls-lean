import OptimalQLS.PolynomialTransform.ElementaryControls
import OptimalQLS.PolynomialTransform.RegisterRelabel

/-! # Binary relabeling preserves every retained QSVT mask control -/
noncomputable section
namespace OptimalQLS.PolynomialTransform
open Matrix Polynomial DirtyAncilla
variable {S A B ι D : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B] [Fintype ι] [DecidableEq ι] [Fintype D] [DecidableEq D]

theorem ElementaryCircuit.relabelMatrix_ports (e : S ≃ A) (c : ElementaryCircuit A B ι D)
    (p : QueryPort S (ElementarySpace ι D)) (adj : Bool)
    (h : ElementaryInstruction.matrixCall p adj ∈ c.relabelMatrix e) :
    ∃ q, ElementaryInstruction.matrixCall q adj ∈ c ∧ p=q.comp (relabelPort e) := by
  obtain ⟨g,hg,he⟩ := List.mem_map.mp h
  cases g with
  | gate g => simp [ElementaryInstruction.relabelMatrix] at he
  | matrixCall q b =>
    simp only [ElementaryInstruction.relabelMatrix,ElementaryInstruction.matrixCall.injEq] at he
    obtain ⟨rfl,rfl⟩ := he
    exact ⟨q,hg,rfl⟩
  | vectorCall q b => simp [ElementaryInstruction.relabelMatrix] at he

theorem lemma24_elementary_relabel_with_controls [Nonempty D] (a : ℕ) (e : S ≃ (Fin a → Bool))
    (s₀ : S) (he : e s₀=(fun _ => false)) (p : ℝ[X])
    (hp : Function.Even p.eval) (hbound : ∀ x : ℝ, |x| ≤ 1 → |p.eval x| ≤ 1) :
    ∃ out : ElementaryCircuit (S × D) B (QSVTWire a) D,
      out.toQuery.matrixQueries ≤ 4*p.natDegree ∧ out.toQuery.vectorQueries=0 ∧
      out.workGates ≤ 6248*(p.natDegree+1)*(a+1) ∧
      (∀ port adj, ElementaryInstruction.matrixCall port adj ∈ out →
        ∃ branch : Bool, ∀ U, port.apply U=physicalMaskedOracle a branch adj
          (rewireUnitary (Equiv.prodCongr e (Equiv.refl D)) U)) ∧
      ∀ (U : Matrix.unitaryGroup (S × D) ℂ) (Ub : Matrix.unitaryGroup B ℂ)
        (A₀ : Matrix D D ℂ), A₀.IsHermitian → IsBlockEncoding s₀ 1 0 U A₀ →
        IsBlockEncoding (physicalZero a) 1 0 (out.toQuery.eval U Ub)
          (Polynomial.aeval A₀ (liftReal p)) := by
  obtain ⟨c,hq,hv,hg,hports,henc⟩ := lemma24_elementary_encoding_with_controls (D := D) (B := B) a p hp hbound
  let e' := Equiv.prodCongr e (Equiv.refl D)
  refine ⟨c.relabelMatrix e',?_,?_,?_,?_,?_⟩
  · simpa only [ElementaryCircuit.relabelMatrix_counts] using hq
  · simpa only [ElementaryCircuit.relabelMatrix_counts] using hv
  · simpa only [ElementaryCircuit.relabelMatrix_counts] using hg
  · intro port adj h
    obtain ⟨q,hq,rfl⟩ := ElementaryCircuit.relabelMatrix_ports e' c port adj h
    obtain ⟨branch,hbranch⟩ := hports q adj hq
    refine ⟨branch,?_⟩
    intro U
    rw [QueryPort.comp_apply,hbranch,relabelPort_apply]
  · intro U Ub A₀ hA hU
    rw [ElementaryCircuit.relabelMatrix_eval,relabelPort_apply]
    apply henc _ Ub A₀ hA
    have hb := signalBlock_relabel e s₀ U
    rw [he] at hb
    simpa only [IsBlockEncoding,hb,e'] using hU

end OptimalQLS.PolynomialTransform
