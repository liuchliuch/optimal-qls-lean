import OptimalQLS.PolynomialTransform.GraphKernel

/-! # Literal shared-wire regrouping for controlled graph and QSVT code -/
noncomputable section
namespace OptimalQLS.PolynomialTransform
open Matrix

/-- Same constant-size named-wire type used by the graph control compiler:
two masks, graph-borrowed plus five graph wires, flag, dirty borrowed bit. -/
abbrev GraphLocalWire := (Fin 2 ⊕ Option (Fin 5)) ⊕ Fin 2
abbrev GraphLocalState := Bool × (GraphLocalWire → Bool)

def graphLocalWiring (S D : Type*) :
    GraphLocalState × (S × D) ≃
      (((Bool × Bool) × (GraphEncoding.PhysicalSignal S × (Fin 4 × D))) × PhaseScratch) where
  toFun p :=
    (((p.1.2 (.inl (.inl 0)),p.1.2 (.inl (.inl 1))),
      ((p.1.2 (.inl (.inr none)),p.1.2 (.inl (.inr (some 0))),
        p.1.2 (.inl (.inr (some 1))),p.1.2 (.inl (.inr (some 4))),p.2.1),
       GraphEncoding.graphBits (p.1.2 (.inl (.inr (some 2))),p.1.2 (.inl (.inr (some 3)))),p.2.2)),
      p.1.1,p.1.2 (.inr 0),p.1.2 (.inr 1))
  invFun p :=
    ((p.2.1,fun i => match i with
      | .inl (.inl j) => if j=0 then p.1.1.1 else p.1.1.2
      | .inl (.inr none) => p.1.2.1.1
      | .inl (.inr (some j)) => ![p.1.2.1.2.1,p.1.2.1.2.2.1,
          (GraphEncoding.graphBits.symm p.1.2.2.1).1,(GraphEncoding.graphBits.symm p.1.2.2.1).2,
          p.1.2.1.2.2.2.1] j
      | .inr j => if j=0 then p.2.2.1 else p.2.2.2),
      (p.1.2.1.2.2.2.2,p.1.2.2.2))
  left_inv p := by
    rcases p with ⟨⟨syn,b⟩,s,d⟩
    apply Prod.ext
    · apply Prod.ext
      · rfl
      · funext i
        rcases i with ((i|(_|i))|i)
        · fin_cases i <;> simp
        · rfl
        · fin_cases i <;> simp
        · fin_cases i <;> simp
    · rfl
  right_inv p := by
    rcases p with ⟨⟨⟨m,n⟩,⟨bor,sel,edge,ora,s⟩,g,d⟩,syn,flag,dirty⟩
    simp

/-- Clean local scratch corresponds to exactly the common three-bit clean sector. -/
def graphLocalClean {S D : Type*}
    (x : (Bool × Bool) × (GraphEncoding.PhysicalSignal S × (Fin 4 × D))) :
    GraphLocalState × (S × D) := (graphLocalWiring S D).symm (x,(false,false,false))

theorem graphLocalClean_zero {S D : Type*}
    (x : (Bool × Bool) × (GraphEncoding.PhysicalSignal S × (Fin 4 × D))) :
    (graphLocalClean x).1.1=false ∧
      (graphLocalClean x).1.2 (.inr 0)=false ∧ (graphLocalClean x).1.2 (.inr 1)=false := by
  simp [graphLocalClean,graphLocalWiring]

end OptimalQLS.PolynomialTransform
