import OptimalQLS.PhysicalRobustness.GeneralProgram.Correctness
import OptimalQLS.Reduction.DirectCostedResources

/-! The same primitive measurement/reset tree, with all three actual resources. -/
noncomputable section
set_option synthInstance.maxSize 16384
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
open scoped Classical Matrix.Norms.L2Operator
namespace OptimalQLS.PhysicalRobustness.GeneralProgram
open Matrix LowerBounds PhysicalPadding Reduction TransducerCompiler BinaryClock PolynomialTransform
open Refinement Refinement.PhysicalExecution Refinement.Repetition
variable {D : Type*} [Fintype D] [DecidableEq D] {a n : ℕ} {α κ δ ŝ ε : ℝ}

def physicalSyntax (I : Implementation a n κ ŝ ε) :=
  DirectCosted.physicalSyntax (circuit I) 600000

def physicalExecution (I : Implementation a n κ ŝ ε) :=
  DirectCosted.lower (circuit I) (Preparation.CompilerAttachment.preparationExponent_pos I.budget) 600000

/-- Complete density semantics, including every failure outcome and input state. -/
theorem physicalExecution_refines (I : Implementation a n κ ŝ ε)
    (UA : Matrix.unitaryGroup (Bits a × Bits n) ℂ) (Ub : Matrix.unitaryGroup (Bits n) ℂ)
    (select : Bool → Bool) (v : Fin (Fintype.card (PhysicalAdapter.Space a n (preparationExponent (2*κ)))) → ℂ) :
    (physicalExecution I).executeDensity UA Ub select v=(execution I).executeDensity UA Ub select v :=
  DirectCosted.refines (circuit I) _ 600000 UA Ub select v

theorem physicalExecution_correct (I : Implementation a n κ ŝ ε)
    (f : D ↪ Bits n) (A : Matrix D D ℂ) (hu : IsUnit A) (hn : ‖A‖≤α)
    (UA : Matrix.unitaryGroup (Bits a × Bits n) ℂ)
    (henc : IsBlockEncoding (fun _ : Fin a=>false) α δ UA (zeroExtend f A))
    (Ub : Matrix.unitaryGroup (Bits n) ℂ) (b : EuclideanSpace ℂ D) (hb : ‖b‖=1)
    (hcol : ∀ i,Ub i (fun _ : Fin n=>false)=coordinateIsometry f b i)
    (hi : α*‖Ring.inverse A‖≤κ) (hs : κ*δ/α≤1/4)
    (hlo : solutionScale α A b/2≤ŝ) (hhi : ŝ≤2*solutionScale α A b)
    (hε : 0<ε) (hε1 : ε<1/2) :
    (2 : ℝ)/3<(physicalExecution I).successProbability UA Ub
      (basis (AdaptedExecution.initialIndex a n (preparationExponent (2*κ)))) ∧
    ∃ x : EuclideanSpace ℂ (Fin (2^n)), ‖x‖=1 ∧
      ‖x-solution f A b‖≤ε+2*κ*δ/α ∧
      (physicalExecution I).conditionalOutput UA Ub
        (basis (AdaptedExecution.initialIndex a n (preparationExponent (2*κ))))=
        pureDensity (WithLp.ofLp x) := by
  have hc := accepted_correct I f A hu hn UA henc Ub b hb hcol hi hs hlo hhi hε hε1
  have hr := execution_success I UA Ub hc.2.2.2
  have hps := DirectCosted.success_eq (circuit I)
    (Preparation.CompilerAttachment.preparationExponent_pos I.budget) 600000 UA Ub
    (basis (AdaptedExecution.initialIndex a n (preparationExponent (2*κ))))
  have hpo := DirectCosted.output_eq (circuit I)
    (Preparation.CompilerAttachment.preparationExponent_pos I.budget) 600000 UA Ub
    (basis (AdaptedExecution.initialIndex a n (preparationExponent (2*κ))))
  exact ⟨hr.1.trans_eq hps.symm,NormedSpace.normalize (accepted I UA Ub),hc.2.1,hc.2.2.1,hpo.trans hr.2⟩

theorem physicalExecution_query_depths (I : Implementation a n κ ŝ ε) :
    matrixDepth (physicalExecution I)=1200000*I.runCircuit.matrixQueries ∧
    (physicalExecution I).vectorDepth=600000*I.runCircuit.vectorQueries := by
  have hh := DirectCosted.query_depths (circuit I)
    (Preparation.CompilerAttachment.preparationExponent_pos I.budget) 600000
  change matrixDepth (physicalExecution I)=600000*(runCircuit I).matrixQueries ∧
    (physicalExecution I).vectorDepth=600000*(runCircuit I).vectorQueries at hh
  rw [(circuit_counts I).1,(circuit_counts I).2.1] at hh
  refine ⟨hh.1.trans (by omega),hh.2⟩

theorem physicalExecution_matrix_bound (I : Implementation a n κ ŝ ε)
    (hε : 0<ε) (hε1 : ε<1/2) :
    (matrixDepth (physicalExecution I) : ℝ)<534000000000000000*κ*Real.log (1/ε) := by
  have hq := I.matrix_bound_log hε hε1
  rw [(physicalExecution_query_depths I).1]
  push_cast
  nlinarith only [hq]

theorem physicalExecution_width_bound (I : Implementation a n κ ŝ ε) :
    RegisterBound (2^(n+3*a+2*preparationExponent (2*κ)+31)) (physicalExecution I) ∧
    n+3*a+2*preparationExponent (2*κ)+31≤n+3*a+2*Nat.log2 ⌈2*κ⌉₊+87 := by
  refine ⟨DirectCosted.register_bound _ _ _,?_⟩
  have hw := I.qubit_bound.2
  omega

theorem physicalSyntax_cost_bound (I : Implementation a n κ ŝ ε) :
    (physicalSyntax I).cost≤600000*(circuit I).workGates+
      1800002*(n+3*a+2*preparationExponent (2*κ)+31) := by
  have hh := DirectCosted.physicalSyntax_cost (circuit I) 600000
  change (DirectCosted.physicalSyntax (circuit I) 600000).cost≤_
  omega

/-- No theorem treats an arithmetic budget as evidence for a primitive tree:
the bounded quantity is the cost read from that tree's syntax. -/
theorem physicalSyntax_work_bound (I : Implementation a n κ ŝ ε)
    {s t : ℝ} (h : BudgetParameters (2*κ) t (9*ŝ/8))
    (hs : 0<s) (hsk : s≤κ) (hst : 2*s/3≤t)
    (hε : 0<ε) (hε1 : ε<1/2) :
    ((physicalSyntax I).cost : ℝ)<3000000000000000000000*κ*(a+1)*Real.log (1/ε)+
      3000000000000000000*(κ/s)*(n+1) := by
  have hc : ((physicalSyntax I).cost : ℝ)≤600000*((circuit I).workGates : ℝ)+
      1800002*((n+3*a+2*preparationExponent (2*κ)+31 : ℕ) : ℝ) := by
    exact_mod_cast physicalSyntax_cost_bound I
  have hg : ((circuit I).workGates : ℝ)≤(I.circuit.workGates : ℝ)+4801*I.runCircuit.matrixQueries := by
    exact_mod_cast (circuit_counts I).2.2
  have hq := I.matrix_bound_log hε hε1
  have hw := (I.original_scale_bounds h hs hst).2
  have hwidth := width_linear a (n+1) h
  have hwidth' : ((n+3*a+2*preparationExponent (2*κ)+31 : ℕ) : ℝ)≤
      (n : ℝ)+4+94*κ*(a+1) := by
    push_cast at hwidth ⊢
    linarith only [hwidth]
  have hl := log_accuracy_lower hε hε1
  have he := PhysicalRobustness.PhysicalProgram.log_noisy_accuracy hε hε1
  have hk : 0<κ := by linarith [I.kappa_ge_two]
  have ha : (0 : ℝ)≤a := Nat.cast_nonneg a
  have hnn : (0 : ℝ)≤n := Nat.cast_nonneg n
  have hx : 0≤κ*((a : ℝ)+1) := by positivity
  have hxl := mul_le_mul_of_nonneg_left hl hx
  have hel := mul_le_mul_of_nonneg_left he (show 0≤150000027051856*κ*((a : ℝ)+1) by positivity)
  have hqa := mul_le_mul_of_nonneg_left ha (show 0≤κ*Real.log (1/ε) by positivity)
  have hratio : 1≤κ/s := (le_div_iff₀ hs).mpr (by simpa using hsk)
  have hsn := mul_le_mul_of_nonneg_right hratio (show 0≤(n : ℝ)+1 by positivity)
  have hsp : 0≤κ/s := by positivity
  have hgw := mul_le_mul_of_nonneg_left hg (by norm_num : (0 : ℝ)≤600000)
  have hw' := mul_lt_mul_of_pos_left hw (by norm_num : (0 : ℝ)<600000)
  have hq' := mul_lt_mul_of_pos_left hq (by norm_num : (0 : ℝ)<2880600000)
  have hwidth'' := mul_le_mul_of_nonneg_left hwidth' (by norm_num : (0 : ℝ)≤1800002)
  push_cast at hw'
  nlinarith only [hc,hgw,hw',hq',hwidth'',hel,hxl,hqa,hsn,hsp,hnn,hx]

/-- Both input-dependent resource terms use the original exact solution scale,
never the noisy physical inverse or a hidden scale used to select the program. -/
theorem physicalExecution_input_resources (I : Implementation a n κ ŝ ε)
    (f : D ↪ Bits n) (A : Matrix D D ℂ) (hu : IsUnit A) (hn : ‖A‖≤α)
    (UA : Matrix.unitaryGroup (Bits a × Bits n) ℂ)
    (henc : IsBlockEncoding (fun _ : Fin a=>false) α δ UA (zeroExtend f A))
    (Ub : Matrix.unitaryGroup (Bits n) ℂ) (b : EuclideanSpace ℂ D) (hb : ‖b‖=1)
    (hcol : ∀ i,Ub i (fun _ : Fin n=>false)=coordinateIsometry f b i)
    (hi : α*‖Ring.inverse A‖≤κ) (hs : κ*δ/α≤1/4)
    (hlo : solutionScale α A b/2≤ŝ) (hhi : ŝ≤2*solutionScale α A b)
    (hε : 0<ε) (hε1 : ε<1/2) :
    ((physicalExecution I).vectorDepth : ℝ)<216000001800000*(κ/solutionScale α A b) ∧
    ((physicalSyntax I).cost : ℝ)<3000000000000000000000*κ*(a+1)*Real.log (1/ε)+
      3000000000000000000*(κ/solutionScale α A b)*(n+1) := by
  obtain ⟨hH,hHu,hHn,hHi,hδ,hpert,hsmall,hbn,_,hsl,hsh⟩ :=
    normalize_input f A hu hn UA henc Ub b hb hcol hi hs hlo hhi
  have hg := noisy_graph_promises (dilationActive f) (normalizedMatrix α A) hH hHu hHn
    (noisyMatrix UA) (noisyMatrix_hermitian UA) (norm_le_of_exact_block (noisyMatrix_encoding UA))
    (WithLp.toLp 2 (source (WithLp.ofLp b))) hbn I.kappa_ge_two hδ hHi hpert hsmall hsl hsh
  dsimp only at hg
  obtain ⟨h,_,_,_,_,_,hst⟩ := hg
  rw [normalized_scale henc.1 A hu b] at hst
  have hbounds := scale_bounds_of_norm henc.1 A hu hn hi b hb
  have hspos : 0<solutionScale α A b := by linarith only [hbounds.1]
  constructor
  · have hv := (I.original_scale_bounds h hspos hst).1
    change (I.runCircuit.vectorQueries : ℝ)<_ at hv
    rw [(physicalExecution_query_depths I).2]
    push_cast
    nlinarith only [hv]
  · exact physicalSyntax_work_bound I h hspos hbounds.2 hst hε hε1

end OptimalQLS.PhysicalRobustness.GeneralProgram
