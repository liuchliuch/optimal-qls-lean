import OptimalQLS.GraphEncoding.ExactToffoli
import OptimalQLS.TransducerCompiler.GateSynthesis

/-! # Global real elementary synthesis of the graph's reversible work gates -/
noncomputable section
set_option synthInstance.maxSize 1024
namespace OptimalQLS.GraphEncoding.GateSynthesis
open Matrix TransducerCompiler BinaryClock
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Exact-global Toffoli expansion, using the sixteenth CNOT proved above. -/
def lowerGate : BinaryClock.Gate ι → List (TransducerCompiler.GateSynthesis.LowerGate ι)
  | .x t => [.x t]
  | .cx c t h => [.cx c t h]
  | .ccx c d t hct hdt => if hcd : c = d then [.cx c t hct] else
      ExactToffoli.circuit.map (TransducerCompiler.GateSynthesis.LowerGate.template c d t hcd hct hdt)

theorem lowerGate_length (g : BinaryClock.Gate ι) : (lowerGate g).length ≤ 16 := by
  cases g with
  | x t => simp [lowerGate]
  | cx c t h => simp [lowerGate]
  | ccx c d t hct hdt =>
    by_cases hcd : c = d <;> simp [lowerGate, hcd]

/-- Unlike the clean template, all borrowed-bit states are restored. -/
theorem template_basis_all (c d t : ι) (hcd : c ≠ d) (hct : c ≠ t) (hdt : d ≠ t)
    (z : Bool) (x : TransducerCompiler.GateSynthesis.Data ι) :
    (TransducerCompiler.GateSynthesis.templateHom c d t hcd hct hdt ExactToffoli.exactUnitary).val *ᵥ Pi.single (z,x) 1 =
      Pi.single (z,(BinaryClock.Gate.ccx c d t hct hdt).act x) 1 := by
  let e := TransducerCompiler.GateSynthesis.templateWiring c d t hcd hct hdt
  let s := TransducerCompiler.GateSynthesis.splitTriple c d t hcd hct hdt x
  have h := TransducerCompiler.GateSynthesis.placeHom_basis e ExactToffoli.exactUnitary (z,s.1)
    (z,RealToffoli.toffoliSector s.1) s.2
    (ExactToffoli.exactUnitary_basis z s.1.1 s.1.2.1 s.1.2.2)
  have hi : e ((z,s.1),s.2) = (z,x) := by
    change (z, (TransducerCompiler.GateSynthesis.splitTriple c d t hcd hct hdt).symm
      (TransducerCompiler.GateSynthesis.splitTriple c d t hcd hct hdt x)) = _
    rw [Equiv.symm_apply_apply]
  have ho : e ((z,RealToffoli.toffoliSector s.1),s.2) =
      (z,(BinaryClock.Gate.ccx c d t hct hdt).act x) := by
    change (z, (TransducerCompiler.GateSynthesis.splitTriple c d t hcd hct hdt).symm
      (RealToffoli.toffoliSector s.1,s.2)) = _
    apply congrArg (fun y => (z,y))
    apply (TransducerCompiler.GateSynthesis.splitTriple c d t hcd hct hdt).injective
    change (TransducerCompiler.GateSynthesis.splitTriple c d t hcd hct hdt)
      ((TransducerCompiler.GateSynthesis.splitTriple c d t hcd hct hdt).symm _) = _
    rw [Equiv.apply_symm_apply, TransducerCompiler.GateSynthesis.splitTriple_ccx]
  simpa only [hi,ho] using h

theorem dataHom_basis (U : Matrix.unitaryGroup (TransducerCompiler.GateSynthesis.Data ι) ℂ) (z : Bool) (x y : TransducerCompiler.GateSynthesis.Data ι)
    (h : U.val *ᵥ Pi.single x 1 = Pi.single y 1) :
    (TransducerCompiler.GateSynthesis.dataHom U).val *ᵥ Pi.single (z,x) 1 = Pi.single (z,y) 1 :=
  TransducerCompiler.GateSynthesis.placeHom_basis (Equiv.prodComm (TransducerCompiler.GateSynthesis.Data ι) Bool) U x y z h

theorem lowerGate_basis_all (g : BinaryClock.Gate ι) (z : Bool) (x : TransducerCompiler.GateSynthesis.Data ι) :
    (TransducerCompiler.GateSynthesis.eval (lowerGate g)).val *ᵥ Pi.single (z,x) 1 = Pi.single (z,g.act x) 1 := by
  cases g with
  | x t =>
    simp only [lowerGate, TransducerCompiler.GateSynthesis.eval, one_mul, TransducerCompiler.GateSynthesis.LowerGate.eval]
    apply dataHom_basis
    simpa only [run_cons, run_nil] using programUnitary_basis [BinaryClock.Gate.x t] x
  | cx c t hct =>
    simp only [lowerGate, TransducerCompiler.GateSynthesis.eval, one_mul, TransducerCompiler.GateSynthesis.LowerGate.eval]
    apply dataHom_basis
    simpa only [run_cons, run_nil] using programUnitary_basis [BinaryClock.Gate.cx c t hct] x
  | ccx c d t hct hdt =>
    by_cases hcd : c = d
    · subst d
      simp only [lowerGate, ↓reduceDIte, TransducerCompiler.GateSynthesis.eval, one_mul, TransducerCompiler.GateSynthesis.LowerGate.eval]
      have h := dataHom_basis (programUnitary [BinaryClock.Gate.cx c t hct]) z x _
        (programUnitary_basis [BinaryClock.Gate.cx c t hct] x)
      simpa only [run_cons, run_nil, BinaryClock.Gate.act, Bool.and_self] using h
    · rw [lowerGate, dif_neg hcd, TransducerCompiler.GateSynthesis.eval_template]
      exact template_basis_all c d t hcd hct hdt z x

def lowerProgram (p : Program ι) : List (TransducerCompiler.GateSynthesis.LowerGate ι) := p.flatMap lowerGate

theorem lowerProgram_basis_all (p : Program ι) (z : Bool) (x : TransducerCompiler.GateSynthesis.Data ι) :
    (TransducerCompiler.GateSynthesis.eval (lowerProgram p)).val *ᵥ Pi.single (z,x) 1 = Pi.single (z,run p x) 1 := by
  induction p generalizing x with
  | nil => simp only [lowerProgram, List.flatMap_nil, TransducerCompiler.GateSynthesis.eval, OneMemClass.coe_one, Matrix.one_mulVec, run_nil]
  | cons g gs ih =>
    rw [lowerProgram, List.flatMap_cons, TransducerCompiler.GateSynthesis.eval_append, Submonoid.coe_mul,
      ← Matrix.mulVec_mulVec, lowerGate_basis_all]
    exact ih (g.act x)

/-- Exact equality on the whole workspace, not merely a clean input subspace. -/
theorem lowerProgram_eq (p : Program ι) :
    TransducerCompiler.GateSynthesis.eval (lowerProgram p) = TransducerCompiler.GateSynthesis.dataHom (programUnitary p) := by
  apply Subtype.ext
  ext ⟨z,x⟩ ⟨r,y⟩
  have h := lowerProgram_basis_all p r y
  have h' := dataHom_basis (programUnitary p) r y (run p y) (programUnitary_basis p y)
  have hh := congrFun (h.trans h'.symm) (z,x)
  simpa only [Matrix.mulVec_single_one] using hh

theorem lowerProgram_length (p : Program ι) : (lowerProgram p).length ≤ 16*p.length := by
  induction p with
  | nil => simp [lowerProgram]
  | cons g gs ih =>
    simp only [lowerProgram, List.flatMap_cons, List.length_append, List.length_cons] at *
    have hg := lowerGate_length g
    omega

theorem lowerProgram_real (p : Program ι) (i j : TransducerCompiler.GateSynthesis.Space ι) :
    ((TransducerCompiler.GateSynthesis.eval (lowerProgram p)).val i j).im = 0 := TransducerCompiler.GateSynthesis.eval_real _ _ _

theorem lowerProgram_arity (p : Program ι) (g : TransducerCompiler.GateSynthesis.LowerGate ι) (hg : g ∈ lowerProgram p) :
    g.arity ≤ 2 := TransducerCompiler.GateSynthesis.LowerGate.arity_le_two g

end OptimalQLS.GraphEncoding.GateSynthesis
