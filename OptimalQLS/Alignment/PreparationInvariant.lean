import OptimalQLS.Alignment.DoubledSectors
import OptimalQLS.Alignment.CompilerInvariant
import OptimalQLS.Alignment.ProjectionAlignment

/-! Exact alignment for the actual finite preparation circuit. -/
noncomputable section
namespace OptimalQLS.Alignment
open Matrix Preparation TransducerCompiler
variable {F : Type*} [Fintype F] [DecidableEq F]

theorem eightInvariant_to_base (N M : Submodule ℝ (F → ℂ))
    {v : Fin 8 × F → ℂ} (hv : eightInvariant N M v) :
    baseInvariant (preparationSectors N M) (v ∘ compilerWiring F) := by
  obtain ⟨ξ,q,ω₁,ω₂,z,rfl,hξ,hq,hω₁,hω₂,hz⟩ := hv
  rw [bundle8_compilerWiring]
  intro l
  cases l <;> simp only [preparationSectors,bundle,doubleVector_mem_doubleSpace]
  · exact ⟨hξ,Submodule.zero_mem _⟩
  · exact ⟨hq,Submodule.zero_mem _⟩
  · exact ⟨hω₁,hω₂⟩
  · exact ⟨hz,Submodule.zero_mem _⟩

theorem baseInvariant_to_eight (N M : Submodule ℝ (F → ℂ))
    {v : Base (Bool × F) → ℂ} (hv : baseInvariant (preparationSectors N M) v) :
    eightInvariant N M (v ∘ (compilerWiring F).symm) := by
  have hp := hv .pub
  have hi := hv .internal
  have hf := hv .first
  have hs := hv .second
  have hp0 : (fun i => v ((true,i),.pub))=0 := hp.2
  have hi0 : (fun i => v ((true,i),.internal))=0 := hi.2
  have hs0 : (fun i => v ((true,i),.second))=0 := hs.2
  refine ⟨(fun i => v ((false,i),.pub)),(fun i => v ((false,i),.internal)),
    (fun i => v ((false,i),.first)),(fun i => v ((true,i),.first)),
    (fun i => v ((false,i),.second)),?_,hp.1,hi.1,hf.1,hf.2,hs.1⟩
  ext ⟨j,i⟩
  fin_cases j <;> simp [Function.comp_def,compilerWiring,compilerLabel,bundle8]
  · exact congrFun hp0 i
  · exact congrFun hi0 i
  · exact congrFun hs0 i

theorem compilerWork_preserves (N M : Submodule ℝ (F → ℂ)) (hNM : N≤M)
    (Q : Matrix F F ℂ) (hQ : star Q=Q) (hQQ : Q*Q=Q)
    (hQN : ∀ x∈N,Q*ᵥx=x) (hQM : ∀ x∈M,Q*ᵥx∈N)
    {μ r : ℝ} (hμ : 0<μ) (hr : |r|<1)
    {v : Base (Bool × F) → ℂ} (hv : baseInvariant (preparationSectors N M) v) :
    baseInvariant (preparationSectors N M) ((compilerWork Q hQ hQQ hμ hr).val*ᵥv) := by
  have hin := baseInvariant_to_eight N M hv
  have hout := eightInvariant_to_base N M
    (preparationWork_preserves N M hNM Q hQ hQQ hQN hQM hμ hr hin)
  rw [← compilerWork_apply] at hout
  simpa only [Function.comp_assoc,Equiv.symm_comp_self,Function.comp_id] using hout

variable {S D : Type*} [Fintype S] [DecidableEq S] [Fintype D] [DecidableEq D]

/-- The exact three invariance premises of the compiler follow from the
encoding and rank-one-reflection matrices. -/
theorem encodedCompilerWork_preserves (s₀ : S) (H : Matrix D D ℂ) (e : D → ℂ)
    (V : Matrix.unitaryGroup (S × D) ℂ) {α μ r : ℝ} (hα : α≠0)
    (hblock : H=α • signalBlock s₀ V) (hμ : 0<μ) (hr : |r|<1)
    {v : Base (Bool × (S × D)) → ℂ}
    (hv : baseInvariant (preparationSectors (signalKrylov s₀ H e)
      (oracleSpan (signalKrylov s₀ H e) V.val)) v) :
    baseInvariant (preparationSectors (signalKrylov s₀ H e)
      (oracleSpan (signalKrylov s₀ H e) V.val))
      ((compilerWork (signalProjector s₀) (signalProjector_star s₀)
        (signalProjector_idempotent s₀) hμ hr).val*ᵥv) := by
  exact compilerWork_preserves _ _ (le_oracleSpan _ _) _ _ _
    (fun x hx => projector_fixes_signalKrylov s₀ H e hx)
    (fun x hx => compression_oracleSpan _ _ _
      (fun x hx => projector_fixes_signalKrylov s₀ H e hx)
      (fun x hx => compression_mem_signalKrylov s₀ H e V hα hblock hx) hx) hμ hr hv

theorem encodedFirst_preserves (s₀ : S) (H : Matrix D D ℂ) (e : D → ℂ)
    (V : Matrix.unitaryGroup (S × D) ℂ) (hV : star V.val=V.val)
    {x : Bool × (S × D) → ℂ}
    (hx : x ∈ preparationSectors (signalKrylov s₀ H e)
      (oracleSpan (signalKrylov s₀ H e) V.val) .first) :
    (doubleOracle V).val*ᵥx ∈ preparationSectors (signalKrylov s₀ H e)
      (oracleSpan (signalKrylov s₀ H e) V.val) .first := by
  have hVV : V.val*V.val=1 := by simpa only [hV] using V.property.1
  exact doubleOracle_preserves _ _ V
    (fun x hx => oracleSpan_preserves _ _ hVV hx)
    (fun x hx => oracleSpan_preserves _ _ hVV hx) hx

theorem encodedSecond_preserves (s₀ : S) (H : Matrix D D ℂ) (hH : star H=H)
    (e : EuclideanSpace ℂ D) (he : ‖e‖=1) (Ub : Matrix.unitaryGroup D ℂ)
    (i₀ : D) (hcol : ∀ i,Ub i i₀=e i) (M : Submodule ℝ (S × D → ℂ))
    {x : Bool × (S × D) → ℂ}
    (hx : x ∈ preparationSectors (signalKrylov s₀ H (WithLp.ofLp e)) M .second) :
    (doubleOracle (signalLift (S := S) (preparedReflection Ub i₀))).val*ᵥx ∈
      preparationSectors (signalKrylov s₀ H (WithLp.ofLp e)) M .second := by
  apply doubleOracle_preserves _ _ _
    (fun x hx => signalReflection_preserves_signalKrylov s₀ H hH e he Ub i₀ hcol hx)
    ?_ hx
  intro x hx
  have hx0 : x=0 := hx
  simp [hx0]

theorem encodedInput_mem (s₀ : S) (H : Matrix D D ℂ) (e : D → ℂ)
    (M : Submodule ℝ (S × D → ℂ)) :
    doubleVector (signalInjection s₀*ᵥe) 0 ∈ preparationSectors (signalKrylov s₀ H e) M .pub := by
  change doubleVector (signalInjection s₀*ᵥe) 0 ∈ doubleSpace (signalKrylov s₀ H e) ⊥
  rw [doubleVector_mem_doubleSpace]
  exact ⟨injection_mem_signalKrylov s₀ H e (input_mem_dataKrylov H e),Submodule.zero_mem _⟩

theorem signalKrylov_slice (s₀ : S) (H : Matrix D D ℂ) (e : D → ℂ)
    {v : S × D → ℂ} (hv : v ∈ signalKrylov s₀ H e) :
    (fun i => v (s₀,i)) ∈ dataKrylov H e := by
  obtain ⟨x,hx,rfl⟩ := hv
  simpa only [realMatrixMap_apply,signalInjection_mulVec,ite_true] using hx

end OptimalQLS.Alignment
