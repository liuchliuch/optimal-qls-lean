import OptimalQLS.Preparation.CompilerAttachment.SourceGates
import OptimalQLS.Preparation.CompilerAttachment.GraphGates

/-! # Full original-source reflection attachment to the actual compiler oracle -/
noncomputable section
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 700000
set_option linter.unusedSimpArgs false
open scoped Classical
namespace OptimalQLS.Preparation.CompilerAttachment
open Matrix TransducerCompiler BinaryClock PolynomialTransform DirtyAncilla

theorem port_apply_mul {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (p : QueryPort X Y) (U V : Matrix.unitaryGroup X ℂ) :
    p.apply (U*V)=p.apply U*p.apply V := p.unitaryHom.map_mul _ _

theorem signalLift_mul {X S : Type*} [Fintype X] [DecidableEq X] [Fintype S] [DecidableEq S]
    (U V : Matrix.unitaryGroup X ℂ) : signalLift (S := S) (U*V)=signalLift U*signalLift V := by
  simpa only [signalLiftPort_apply] using port_apply_mul (signalLiftPort S X) U V

theorem signalLift_inv {X S : Type*} [Fintype X] [DecidableEq X] [Fintype S] [DecidableEq S]
    (U : Matrix.unitaryGroup X ℂ) : signalLift (S := S) U⁻¹=(signalLift U)⁻¹ := by
  simpa only [signalLiftPort_apply] using QueryPort.apply_inv (signalLiftPort S X) U

def compilerSourceOracle (a n ℓ : ℕ) (l : Label)
    (Ub : Matrix.unitaryGroup (Bits n) ℂ) : Matrix.unitaryGroup (Logical a n ℓ) ℂ :=
  (compilerDataPort (PreparationData (Bits a) (Bits n)) ℓ l).apply
    (doubleOracle (signalLift (S := GraphEncoding.PhysicalSignal (Bits a))
      (signalLift (S := Fin 4) Ub)))

theorem sourceDataFrame_oracle (a n ℓ : ℕ) (l : Label)
    (Ub : Matrix.unitaryGroup (Bits n) ℂ) :
    GateSynthesis.placeHom (sourceDataFrame a n ℓ)
      ((GraphEncoding.maskedGraphPort (Bits n) (labelBitsEquiv l)).apply Ub)=
      compilerSourceOracle a n ℓ l Ub := by
  unfold compilerSourceOracle
  rw [← labelDataFrame_oracle]
  apply Subtype.ext
  ext x y
  obtain ⟨⟨⟨m,d⟩,s,g,r⟩,rfl⟩ := (sourceDataFrame a n ℓ).surjective x
  obtain ⟨⟨⟨m',d'⟩,s',g',r'⟩,rfl⟩ := (sourceDataFrame a n ℓ).surjective y
  rw [placeHom_entry,GraphEncoding.maskedGraphPort_apply_entries]
  simp only [sourceDataFrame,GraphEncoding.placeHom_entries,Equiv.symm_apply_apply]
  rw [GraphEncoding.maskedGraphPort_apply_entries]
  simp only [signalLift,rewireUnitary,controlledOn,
    Matrix.blockDiagonal_apply,Matrix.submatrix_apply,Equiv.prodComm_symm,
    Equiv.prodComm_apply,Prod.swap]
  by_cases hr : r=r' <;> by_cases hs : s=s' <;> by_cases hg : g=g' <;>
    by_cases hm : m=m' <;> by_cases hl : m=labelBitsEquiv l <;>
    simp_all [Matrix.one_apply,Matrix.blockDiagonal_apply,Prod.mk.injEq]

theorem reflectionSourceFrame_oracle (a n ℓ : ℕ) :
    GateSynthesis.placeHom (reflectionSourceFrame a n ℓ) (reflectionPhaseUnitary n)=
      (compilerDataPort (PreparationData (Bits a) (Bits n)) ℓ .second).apply
        (doubleOracle (signalLift (S := GraphEncoding.PhysicalSignal (Bits a))
          (basisStateReflection (1,fun _ : Fin n=>false)))) := by
  rw [← labelDataFrame_oracle]
  apply Subtype.ext
  ext x y
  obtain ⟨⟨⟨m,d⟩,s,r⟩,rfl⟩ := (reflectionSourceFrame a n ℓ).surjective x
  obtain ⟨⟨⟨m',d'⟩,s',r'⟩,rfl⟩ := (reflectionSourceFrame a n ℓ).surjective y
  rw [placeHom_entry]
  simp only [reflectionPhaseUnitary]
  rw [GraphEncoding.maskedGraphPort_apply_entries]
  simp only [reflectionSourceFrame,GraphEncoding.placeHom_entries,Equiv.symm_apply_apply]
  rw [GraphEncoding.maskedGraphPort_apply_entries]
  simp only [signalLift,rewireUnitary,controlledOn,Matrix.blockDiagonal_apply,Matrix.submatrix_apply,
    Equiv.prodComm_symm,Equiv.prodComm_apply,Prod.swap]
  by_cases hr : r=r' <;> by_cases hs : s=s' <;> by_cases hm : m=m' <;>
    by_cases hl : m=(true,true) <;>
    simp_all [labelBitsEquiv,labelCode,Matrix.one_apply,Matrix.blockDiagonal_apply,Prod.mk.injEq]

def compilerReflectionCall (a n ℓ : ℕ) : SourceCircuit a n ℓ :=
  sourceCall a n ℓ .second true ++ reflectionMacro a n ℓ ++ sourceCall a n ℓ .second false

theorem compilerReflectionCall_counts (a n ℓ : ℕ) :
    ((compilerReflectionCall a n ℓ).toQuery (sourceGateEval a n ℓ)).matrixQueries=0 ∧
      ((compilerReflectionCall a n ℓ).toQuery (sourceGateEval a n ℓ)).vectorQueries=2 ∧
      (compilerReflectionCall a n ℓ).workGates≤11222*(n+1) := by
  have h₁ := sourceCall_counts a n ℓ .second true
  have h₂ := reflectionMacro_counts a n ℓ
  have h₃ := sourceCall_counts a n ℓ .second false
  simp only [compilerReflectionCall,NamedCircuit.toQuery_append,
    QueryCircuit.matrixQueries_append,QueryCircuit.vectorQueries_append,
    NamedCircuit.workGates_append,h₁.1,h₁.2.1,h₂.1,h₂.2.1,h₃.1,h₃.2.1]
  constructor
  · trivial
  constructor
  · trivial
  · omega

theorem compilerReflectionCall_intertwines (a n ℓ : ℕ)
    (UA : Matrix.unitaryGroup (Bits a × Bits n) ℂ) (Ub : Matrix.unitaryGroup (Bits n) ℂ) :
    (((compilerReflectionCall a n ℓ).toQuery (sourceGateEval a n ℓ)).eval UA Ub).val *
        basisInsertion (clean a n ℓ)=
      basisInsertion (clean a n ℓ)*
        ((compilerDataPort (PreparationData (Bits a) (Bits n)) ℓ .second).apply
          (doubleOracle (signalLift (S := GraphEncoding.PhysicalSignal (Bits a))
            (preparedReflection (signalLift (S := Fin 4) Ub) (1,fun _=>false))))).val := by
  have h₁ := sourceCall_intertwines a n ℓ .second true UA Ub
  have h₂ := reflectionMacro_intertwines a n ℓ UA Ub
  have h₃ := sourceCall_intertwines a n ℓ .second false UA Ub
  rw [sourceDataFrame_oracle] at h₁ h₃
  rw [reflectionSourceFrame_oracle] at h₂
  simp only [compilerReflectionCall,NamedCircuit.toQuery_append,QueryCircuit.eval_append,Submonoid.coe_mul]
  have hh := intertwines_mul _ _ _ _ _ (intertwines_mul _ _ _ _ _ h₁ h₂) h₃
  convert hh using 1
  unfold compilerSourceOracle
  simp only [Bool.false_eq_true,ite_false,ite_true,← Submonoid.coe_mul]
  congr 1
  simp only [doubleOracle,preparedReflection,signalLift_mul,signalLift_inv,
    port_apply_mul,mul_assoc]

theorem initialSource_intertwines (a n ℓ : ℕ)
    (UA : Matrix.unitaryGroup (Bits a × Bits n) ℂ) (Ub : Matrix.unitaryGroup (Bits n) ℂ) :
    (((sourceCall a n ℓ .pub false).toQuery (sourceGateEval a n ℓ)).eval UA Ub).val *
        basisInsertion (clean a n ℓ)=
      basisInsertion (clean a n ℓ)*
        ((preparationSourcePort (Bits a) (Bits n) ℓ).apply Ub).val := by
  have h := sourceCall_intertwines a n ℓ .pub false UA Ub
  rw [sourceDataFrame_oracle] at h
  rw [preparationSourcePort_eval]
  exact h

end OptimalQLS.Preparation.CompilerAttachment
