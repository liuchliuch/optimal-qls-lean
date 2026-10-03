import OptimalQLS.Preparation.CompilerAttachment.SourceSemantics

/-! # Real elementary leaves and literal single-flag provenance for source calls -/
noncomputable section
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 700000
open scoped Classical
namespace OptimalQLS.Preparation.CompilerAttachment
open Matrix TransducerCompiler BinaryClock PolynomialTransform DirtyAncilla

def SourceGate.Real {n : ℕ} : SourceGate n → Prop
  | .oracle g => GraphEncoding.RealPhaseGate g
  | .phase g => GraphEncoding.RealPhaseGate g

theorem sourceCall_real (a n ℓ : ℕ) (l : Label) (adj : Bool) :
    ∀ g, NamedInstruction.gate g ∈ sourceCall a n ℓ l adj → g.Real := by
  intro g hg
  obtain ⟨i,hi,hEq⟩ := List.mem_map.mp hg
  obtain ⟨j,hj,hji⟩ := List.mem_map.mp hi
  cases j with
  | gate q =>
    cases hji
    cases hEq
    exact (GraphEncoding.maskedOracleCircuit_safe (A := Bits n) (B := Bits a × Bits n)
      2 id Function.injective_id ![(labelBitsEquiv l).1,(labelBitsEquiv l).2] adj).1 q hj
  | matrixCall p b => cases hji; cases hEq
  | vectorCall p b => cases hji; cases hEq

theorem reflectionMacro_real (a n ℓ : ℕ) :
    ∀ g, NamedInstruction.gate g ∈ reflectionMacro a n ℓ → g.Real := by
  intro g hg
  obtain ⟨p,hp,hEq⟩ := List.mem_map.mp hg
  cases hEq
  exact reflectionPhaseCode_real n p hp

theorem compilerReflectionCall_real (a n ℓ : ℕ) :
    ∀ g, NamedInstruction.gate g ∈ compilerReflectionCall a n ℓ → g.Real := by
  intro g hg
  rcases List.mem_append.mp hg with hg|hg
  · rcases List.mem_append.mp hg with hg|hg
    · exact sourceCall_real a n ℓ .second true g hg
    · exact reflectionMacro_real a n ℓ g hg
  · exact sourceCall_real a n ℓ .second false g hg

theorem compilerReflectionCall_single_flag (a n ℓ : ℕ)
    (p : QueryPort (Bits n) (Physical a n ℓ)) (b : Bool)
    (hp : NamedInstruction.vectorCall p b ∈ compilerReflectionCall a n ℓ) :
    p=sourceSingleFlagPort a n ℓ := by
  rcases List.mem_append.mp hp with hp|hp
  · rcases List.mem_append.mp hp with hp|hp
    · exact (sourceCall_single_flag a n ℓ .second true p b hp).1
    · obtain ⟨g,hg,hEq⟩ := List.mem_map.mp hp
      cases hEq
  · exact (sourceCall_single_flag a n ℓ .second false p b hp).1

theorem sourceGate_real (a n ℓ : ℕ) (g : SourceGate n) (hg : g.Real) :
    ∀ i j, ((sourceGateEval a n ℓ g).val i j).im=0 := by
  cases g with
  | oracle g =>
    exact GateSynthesis.placeHom_real _ _ (GateSynthesis.placeHom_real _ _ hg)
  | phase g => exact GateSynthesis.placeHom_real _ _ hg

end OptimalQLS.Preparation.CompilerAttachment
