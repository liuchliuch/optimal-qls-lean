import OptimalQLS.KernelReflectionPhysical.Circuit
import OptimalQLS.KernelReflectionPhysical.QueryPlacement
import OptimalQLS.PhysicalPadding.Basis

/-! # Proposition 4.4: exact canonical catalysts and the actual physical program -/
noncomputable section
namespace OptimalQLS.KernelReflectionPhysical
open Matrix TransducerCompiler BinaryClock PolynomialTransform DirtyAncilla
open Preparation Preparation.WorkGates Refinement.CostedExecution
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
set_option synthInstance.maxSize 32768

variable {D B : Type} [Fintype D] [DecidableEq D] [Fintype B] [DecidableEq B]

def canonicalP (a : ℕ) (H : Matrix D D ℂ) (ξ : D→ℂ) : Bits a × D → ℂ :=
  signalInjection (fun _ : Fin a=>false) *ᵥ (matrixKernelProjection H *ᵥ ξ)

theorem canonical_public_reflection (a : ℕ) (H : Matrix D D ℂ) (ξ : D→ℂ) :
    (2:ℝ) • canonicalP a H ξ - signalInjection (fun _ : Fin a=>false) *ᵥ ξ =
      signalInjection (fun _ : Fin a=>false) *ᵥ
        (((2:ℝ) • matrixKernelProjection H - 1) *ᵥ ξ) := by
  simp [canonicalP,Matrix.sub_mulVec,Matrix.smul_mulVec,Matrix.mulVec_sub,Matrix.mulVec_smul]

def canonicalZ (a : ℕ) (H : Matrix D D ℂ) (hH : star H=H) (ξ : D→ℂ) : Bits a × D → ℂ :=
  signalInjection (fun _ : Fin a=>false) *ᵥ (matrixPseudoInverse H hH *ᵥ ξ)

def catalystOne {a : ℕ} (U : Matrix.unitaryGroup (Bits a × D) ℂ)
    (H : Matrix D D ℂ) (hH : star H=H) (α τ : ℝ) (ξ : D→ℂ) : Bits a × D → ℂ :=
  kernelCatalystOne U (α*τ) α (canonicalP a H ξ) (canonicalZ a H hH ξ)

def catalystTwo {a : ℕ} (U : Matrix.unitaryGroup (Bits a × D) ℂ)
    (H : Matrix D D ℂ) (hH : star H=H) (α τ : ℝ) (ξ : D→ℂ) : Bits a × D → ℂ :=
  kernelCatalystTwo U (α*τ) α (canonicalP a H ξ) (canonicalZ a H hH ξ)

def catalystWeight (H : Matrix D D ℂ) (hH : star H=H) (α τ : ℝ)
    (ξ : EuclideanSpace ℂ D) : ℝ :=
  α*τ*‖Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) (matrixKernelProjection H) ξ‖^2 +
    α/τ*‖Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) (matrixPseudoInverse H hH) ξ‖^2

/-- Literal physical inclusion of a complete private signal/data sector. -/
def sectorEmbedding (a : ℕ) (c : Bool) (j : Fin 8) : (Bits a × D) ↪ Physical a D where
  toFun x := sourceInsertion false ((j,x),c)
  inj' := by
    intro x y h
    have he := sourceInsertion_injective false h
    exact congrArg (fun z : Source a D => z.1.2) he

def physicalCatalyst (a : ℕ) (c : Bool) (j : Fin 8) (ω : Bits a × D → ℂ) :
    EuclideanSpace ℂ (Physical a D) :=
  WithLp.toLp 2 (basisInsertion (sectorEmbedding a c j) *ᵥ ω)

theorem physicalCatalyst_norm (a : ℕ) (c : Bool) (j : Fin 8) (ω : Bits a × D → ℂ) :
    ‖physicalCatalyst a c j ω‖ = ‖WithLp.toLp 2 ω‖ :=
  (PhysicalPadding.coordinateIsometry (sectorEmbedding a c j)).norm_map (WithLp.toLp 2 ω)

private theorem insertion_comp {L M P : Type*} [Fintype M] [DecidableEq M]
    [DecidableEq P] (f : L→M) (g : M→P) :
    basisInsertion g * basisInsertion f = basisInsertion (fun x=>g (f x)) := by
  ext p l
  simp [basisInsertion,Matrix.mul_apply]

theorem sourceState_decomposition {a : ℕ} (c : Bool) (ξ ω₁ ω₂ : Bits a × D→ℂ) :
    sourceState c ξ ω₁ ω₂ =
      basisInsertion (fun x : Bits a × D => ((1,x),c)) *ᵥ ξ +
      basisInsertion (fun x : Bits a × D => ((2,x),c)) *ᵥ ω₁ +
      basisInsertion (fun x : Bits a × D => ((3,x),c)) *ᵥ ω₂ := by
  funext ⟨⟨j,s,d⟩,b⟩
  fin_cases j <;> by_cases h : b=c <;>
    simp [sourceState,sourceLift,bundle8,basisInsertion,Matrix.mulVec,dotProduct,
      Fintype.sum_prod_type,Prod.mk.injEq,h,ite_and]

/-- The physical private components whose norms are costed are exactly the
components of the implemented catalytic input and output. -/
theorem physicalState_decomposition {a : ℕ} (c : Bool) (ξ ω₁ ω₂ : Bits a × D→ℂ) :
    basisInsertion (sourceInsertion false) *ᵥ sourceState c ξ ω₁ ω₂ =
      WithLp.ofLp (physicalCatalyst a c 1 ξ) +
      WithLp.ofLp (physicalCatalyst a c 2 ω₁) +
      WithLp.ofLp (physicalCatalyst a c 3 ω₂) := by
  rw [sourceState_decomposition]
  simp only [Matrix.mulVec_add,Matrix.mulVec_mulVec,insertion_comp]
  rfl

/-- Exact restoration by the emitted single-flag query and real elementary work list. -/
theorem physical_restoration {a : ℕ} (U : Matrix.unitaryGroup (Bits a × D) ℂ)
    (hU : star U.val=U.val) (H : Matrix D D ℂ) (hH : star H=H)
    {α τ : ℝ} (hα : 0<α) (hτ : 0<τ)
    (hblock : H=α • signalBlock (fun _ : Fin a=>false) U)
    (Ub : Matrix.unitaryGroup B ℂ) (ξ : D→ℂ) (c : Bool) :
    (((transducerProgram a (mul_pos hα hτ)).toQuery (gateEval a)).eval U Ub).val *ᵥ
      (basisInsertion (sourceInsertion false) *ᵥ
        sourceState c (signalInjection (fun _ : Fin a=>false) *ᵥ ξ)
          (catalystOne U H hH α τ ξ) (catalystTwo U H hH α τ ξ)) =
      basisInsertion (sourceInsertion false) *ᵥ
        sourceState c ((2:ℝ) • canonicalP a H ξ - signalInjection (fun _ : Fin a=>false) *ᵥ ξ)
          (catalystOne U H hH α τ ξ) (catalystTwo U H hH α τ ξ) := by
  rw [Matrix.mulVec_mulVec,transducerProgram_intertwines,← Matrix.mulVec_mulVec]
  exact congrArg (fun v => basisInsertion (sourceInsertion false) *ᵥ v)
    (sourceTransducer_restoration U hU H hH hα hτ hblock ξ c)

/-- Both source catalyst norms, their physical embeddings, and the exact paper cost. -/
theorem canonical_catalyst_cost {a : ℕ} (U : Matrix.unitaryGroup (Bits a × D) ℂ)
    (hU : star U.val=U.val) (H : Matrix D D ℂ) (hH : star H=H)
    {α τ : ℝ} (hα : 0<α) (hτ : 0<τ)
    (hblock : H=α • signalBlock (fun _ : Fin a=>false) U)
    (ξ : EuclideanSpace ℂ D) (c : Bool) :
    ‖WithLp.toLp 2 (catalystOne U H hH α τ (WithLp.ofLp ξ))‖^2 = catalystWeight H hH α τ ξ ∧
      ‖WithLp.toLp 2 (catalystTwo U H hH α τ (WithLp.ofLp ξ))‖^2 = catalystWeight H hH α τ ξ ∧
      ‖physicalCatalyst a c 2 (catalystOne U H hH α τ (WithLp.ofLp ξ))‖^2 +
        ‖physicalCatalyst a c 3 (catalystTwo U H hH α τ (WithLp.ofLp ξ))‖^2 =
        2*α*(τ*‖Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) (matrixKernelProjection H) ξ‖^2 +
          ‖Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) (matrixPseudoInverse H hH) ξ‖^2/τ) := by
  obtain ⟨h1,h2⟩ := kernelReflection_catalyst_norms (fun _ : Fin a=>false) U hU H hH hα hτ hblock ξ
  change ‖WithLp.toLp 2 (catalystOne U H hH α τ (WithLp.ofLp ξ))‖^2 = catalystWeight H hH α τ ξ at h1
  change ‖WithLp.toLp 2 (catalystTwo U H hH α τ (WithLp.ofLp ξ))‖^2 = catalystWeight H hH α τ ξ at h2
  refine ⟨h1,h2,?_⟩
  rw [physicalCatalyst_norm,physicalCatalyst_norm,h1,h2]
  unfold catalystWeight
  ring

/-- Every gate of the actual complete program is real and an honest tensor-local gate. -/
theorem transducerProgram_safe {J : Type} (a : ℕ) {μ : ℝ} (hμ : 0<μ)
    (d : D→J→Bool) (g : Gate a)
    (hg : NamedInstruction.gate g ∈ transducerProgram (D := D) (B := B) a hμ) :
    (∀ i j, ((gateEval (D := D) a g).val i j).im=0) ∧ IsTwoLocal (physicalBits d) (gateEval a g) := by
  rcases List.mem_append.mp hg with hg|hg
  · obtain ⟨i,hi,hEq⟩ := List.mem_map.mp hg
    cases i with
    | gate p =>
      cases hEq
      exact ⟨queryGate_real a p (queryProgram_real a p hi),queryGate_local a d p⟩
    | matrixCall q b => cases hEq
    | vectorCall q b => cases hEq
  · obtain ⟨p,hp,hEq⟩ := List.mem_map.mp hg
    cases hEq
    exact ⟨workGate_real a p (workProgram_real a hμ false p hp),workGate_local a d p⟩

/-- Controlled work retains semantic locality after adjoining all data spectators. -/
theorem controlledWork_safe {J : Type} (a : ℕ) {μ : ℝ} (hμ : 0<μ)
    (external : Bool) (d : D→J→Bool) (g : PhaseGate (Wire (LogicalWire a)))
    (hg : g ∈ workProgram a hμ external) :
    (∀ i j, ((elementaryPlacement (D := D) g.eval).val i j).im=0) ∧
      IsTwoLocal (physicalBits d) (elementaryPlacement g.eval) :=
  ⟨workGate_real a g (workProgram_real a hμ external g hg),workGate_local a d g⟩

/-- Arbitrary τ and α, full physical execution, exact canonical catalyst cost,
controlled-work implementation, elementary resources and literal oracle arguments.
The known work/circuit lists are chosen without seeing any oracle entries. -/
theorem proposition44 (a n : ℕ) (U : Matrix.unitaryGroup (Bits a × Bits n) ℂ)
    (hU : star U.val=U.val) (H : Matrix (Bits n) (Bits n) ℂ) (hH : star H=H)
    {α τ : ℝ} (hα : 0<α) (hτ : 0<τ)
    (hblock : H=α • signalBlock (fun _ : Fin a=>false) U)
    (Ub : Matrix.unitaryGroup B ℂ) :
    (∀ (ξ : Bits n→ℂ) (c : Bool),
      (((transducerProgram a (mul_pos hα hτ)).toQuery (gateEval a)).eval U Ub).val *ᵥ
        (basisInsertion (sourceInsertion false) *ᵥ
          sourceState c (signalInjection (fun _ : Fin a=>false) *ᵥ ξ)
            (catalystOne U H hH α τ ξ) (catalystTwo U H hH α τ ξ)) =
        basisInsertion (sourceInsertion false) *ᵥ
          sourceState c ((2:ℝ) • canonicalP a H ξ - signalInjection (fun _ : Fin a=>false) *ᵥ ξ)
            (catalystOne U H hH α τ ξ) (catalystTwo U H hH α τ ξ)) ∧
    (∀ (ξ : EuclideanSpace ℂ (Bits n)) (c : Bool),
      ‖physicalCatalyst a c 2 (catalystOne U H hH α τ (WithLp.ofLp ξ))‖^2 +
        ‖physicalCatalyst a c 3 (catalystTwo U H hH α τ (WithLp.ofLp ξ))‖^2 =
        2*α*(τ*‖Matrix.toEuclideanCLM (n := Bits n) (𝕜 := ℂ) (matrixKernelProjection H) ξ‖^2 +
          ‖Matrix.toEuclideanCLM (n := Bits n) (𝕜 := ℂ) (matrixPseudoInverse H hH) ξ‖^2/τ)) ∧
    ((transducerProgram (D := Bits n) (B := B) a (mul_pos hα hτ)).toQuery (gateEval a)).matrixQueries=1 ∧
    ((transducerProgram (D := Bits n) (B := B) a (mul_pos hα hτ)).toQuery (gateEval a)).vectorQueries=0 ∧
    (transducerProgram (D := Bits n) (B := B) a (mul_pos hα hτ)).workGates ≤ 18620*(a+1) ∧
    (∀ external dirty,
      (physicalWork (D := Bits n) (a := a) (mul_pos hα hτ) external).val *
          basisInsertion (sourceInsertion dirty) =
        basisInsertion (sourceInsertion dirty) * (sourceWork (mul_pos hα hτ) external).val) ∧
    (∀ external, (workProgram a (mul_pos hα hτ) external).length ≤ 16220*(a+1)) ∧
    (∀ g, NamedInstruction.gate g ∈ transducerProgram (D := Bits n) (B := B) a (mul_pos hα hτ) →
      (∀ i j, ((gateEval (D := Bits n) a g).val i j).im=0) ∧
        IsTwoLocal (physicalBits (a := a) (fun d : Bits n=>d)) (gateEval a g)) ∧
    (∀ external g, g ∈ workProgram a (mul_pos hα hτ) external →
      (∀ i j, ((elementaryPlacement (D := Bits n) g.eval).val i j).im=0) ∧
        IsTwoLocal (physicalBits (a := a) (fun d : Bits n=>d)) (elementaryPlacement g.eval)) ∧
    (∀ p adj, NamedInstruction.matrixCall p adj ∈
      transducerProgram (D := Bits n) (B := B) a (mul_pos hα hτ) →
        p=singleFlagPort a ∧ adj=false) ∧
    Nonempty (LiteralQueryPlacement (matrixArguments a n)
      (physicalBits (a := a) (fun d : Bits n=>d)) (singleFlagPort a)) ∧
    Fintype.card (Wire (LogicalWire a)) + 1 = a+7 := by
  have hc := transducerProgram_counts (D := Bits n) (B := B) a (mul_pos hα hτ)
  exact ⟨fun ξ c=>physical_restoration U hU H hH hα hτ hblock Ub ξ c,
    fun ξ c=>(canonical_catalyst_cost U hU H hH hα hτ hblock ξ c).2.2,
    hc.1,hc.2.1,hc.2.2,fun external dirty=>workProgram_intertwines _ external dirty,
    fun external=>workProgram_length a _ external,
    fun g hg=>transducerProgram_safe a _ (fun d : Bits n=>d) g hg,
    fun external g hg=>controlledWork_safe a _ external (fun d : Bits n=>d) g hg,
    fun p adj hp=>transducerProgram_single_flag a _ p adj hp,
    ⟨originalOraclePlacement a n⟩,scratch_card a⟩

end OptimalQLS.KernelReflectionPhysical
