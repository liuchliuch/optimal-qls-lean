import OptimalQLS.Reduction.GenericSolver.FreshCopiesComplete
import OptimalQLS.Reduction.GenericSolver.PhysicalTarget

/-! Proposition 2.3 in the physical two-oracle model. The normalized input,
actual supplied-oracle implementation, three fresh runs, terminal-wise output
accuracy and resource costs are joined for one constructed program. -/
noncomputable section
open scoped Classical Matrix.Norms.L2Operator
namespace OptimalQLS.Reduction.GenericSolver
open Matrix LowerBounds Refinement.Repetition PhysicalPadding TransducerCompiler BinaryClock PolynomialTransform
open Refinement.CostedExecution Physical FreshCopies
set_option synthInstance.maxSize 32768
set_option maxHeartbeats 1000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false
variable {D P W : Type} [Fintype D] [DecidableEq D]
  [Fintype P] [DecidableEq P] [Fintype W] [DecidableEq W]
variable {chart : P ≃ (W → Bool)} {a n : ℕ}

/-- All normalized promises concern the logical invertible operator; its signal
block on the complete physical data register is its zero extension. -/
structure NormalizedInputConditions (f : D ↪ Bits n) (α κ estimate ε : ℝ)
    (A : Matrix D D ℂ) (b : EuclideanSpace ℂ D)
    (UA : Matrix.unitaryGroup (Bits a × Bits n) ℂ) (Ub : Matrix.unitaryGroup (Bits n) ℂ) : Prop where
  hermitian : (normalizedMatrix α A).IsHermitian
  invertible : IsUnit (normalizedMatrix α A)
  encoding : IsBlockEncoding (fun _ : Fin a=>false) 1 0 (dilationEncoding UA)
    (zeroExtend (sumIndex f) (normalizedMatrix α A))
  preparation : ∀ i,Reduction.preparation Ub i (.inl (fun _ : Fin n=>false))=
    coordinateIsometry (sumIndex f) (WithLp.toLp 2 (source (WithLp.ofLp b))) i
  source_unit : ‖coordinateIsometry (sumIndex f) (WithLp.toLp 2 (source (WithLp.ofLp b)))‖=1
  norm_bound : ‖normalizedMatrix α A‖≤1
  inverse_bound : ‖(normalizedMatrix α A)⁻¹‖≤κ
  kappa_ge_two : 2≤κ
  estimate_lower : 3*‖WithLp.toLp 2 ((normalizedMatrix α A)⁻¹ *ᵥ source (WithLp.ofLp b))‖/8≤estimate
  estimate_upper : estimate≤5*‖WithLp.toLp 2 ((normalizedMatrix α A)⁻¹ *ᵥ source (WithLp.ofLp b))‖/2
  accuracy_positive : 0<ε/2
  accuracy_lt_half : ε/2<1/2

theorem normalized_input_conditions (f : D ↪ Bits n) {α κ estimate ε : ℝ}
    (A : Matrix D D ℂ) (hA : IsUnit A) (b : EuclideanSpace ℂ D) (hb : ‖b‖=1)
    (UA : Matrix.unitaryGroup (Bits a × Bits n) ℂ)
    (henc : IsBlockEncoding (fun _ : Fin a=>false) α 0 UA (zeroExtend f A))
    (Ub : Matrix.unitaryGroup (Bits n) ℂ)
    (hcol : ∀ i,Ub i (fun _ : Fin n=>false)=coordinateIsometry f b i)
    (hκ : 2≤κ) (hinv : α*‖A⁻¹‖≤κ)
    (hlo : 3*(α*‖WithLp.toLp 2 (A⁻¹ *ᵥ WithLp.ofLp b)‖)/8≤estimate)
    (hhi : estimate≤5*(α*‖WithLp.toLp 2 (A⁻¹ *ᵥ WithLp.ofLp b)‖)/2)
    (hε0 : 0<ε) (hε1 : ε<1/2) :
    NormalizedInputConditions f α κ estimate ε A b UA Ub := by
  have hi:=input_promises f A hA b hb UA henc Ub hcol
  have hn:=input_bounds f A hA UA henc hinv
  have hs:=(input_relaxed_estimate f henc.1 A hA b hlo hhi).1
  exact ⟨hi.1,hi.2.1,hi.2.2.1,hi.2.2.2.1,hi.2.2.2.2.1,hn.1,hn.2,hκ,hs.1,hs.2,
    by linarith,by linarith⟩

/-- Exact numbered reduction. The supplied solver may use ordinary or controlled
queries, branch on measurements, and produce different close pure states on
successful branches. Its entire successful conditional density need not be pure.
The returned `Process` itself contains literal local gates, single-control oracle
placements, measurements and partial traces, so costs are attached to execution. -/
theorem proposition23 (F : OutputLayout chart n) (c : AnyProgram chart a n) (zero : P)
    (hzero : chart zero=fun _=>false)
    (f : D ↪ Bits n) {α κ estimate ε : ℝ}
    (A : Matrix D D ℂ) (hA : IsUnit A) (b : EuclideanSpace ℂ D) (hb : ‖b‖=1)
    (UA : Matrix.unitaryGroup (Bits a × Bits n) ℂ)
    (henc : IsBlockEncoding (fun _ : Fin a=>false) α 0 UA (zeroExtend f A))
    (Ub : Matrix.unitaryGroup (Bits n) ℂ)
    (hcol : ∀ i,Ub i (fun _ : Fin n=>false)=coordinateIsometry f b i)
    (hκ : 2≤κ) (hinv : α*‖A⁻¹‖≤κ)
    (hlo : 3*(α*‖WithLp.toLp 2 (A⁻¹ *ᵥ WithLp.ofLp b)‖)/8≤estimate)
    (hhi : estimate≤5*(α*‖WithLp.toLp 2 (A⁻¹ *ᵥ WithLp.ofLp b)‖)/2)
    (hε0 : 0<ε) (hε1 : ε<1/2) :
    let result:=reducedProcess F c
    NormalizedInputConditions f α κ estimate ε A b UA Ub ∧
    (poolRegister (adaptedRegister chart) n 3).bits
      (poolPoint (adaptedRegister chart) n (adaptedZero zero) (fun _=>false) 3)=(fun _=>false) ∧
    result.work≤3*c.work+14406*c.matrixCalls+3*c.vectorCalls ∧
    result.measurements≤3*(c.measurements+1) ∧
    matrixDepth result.lower≤6*c.matrixCalls ∧ result.lower.vectorDepth≤3*c.vectorCalls ∧
    RegisterBound (2^(4*Fintype.card W+16)) result.lower ∧
    ((∀ t : (c.lower F).Terminal,(c.lower F).terminalSuccess t=true→
      0<bornMass (((c.lower F).terminalPath (.initial (basis ((Fintype.equivFin P) zero))) t).state
        (dilationEncoding UA) (Reduction.preparation Ub))→
      CloseDilationSolution f α A b ε
        (((c.lower F).terminalPath (.initial (basis ((Fintype.equivFin P) zero))) t).state
          (dilationEncoding UA) (Reduction.preparation Ub))) →
      2/3≤(c.lower F).successProbability (dilationEncoding UA) (Reduction.preparation Ub)
        (basis ((Fintype.equivFin P) zero))→
      (2:ℝ)/3<result.lower.successProbability UA Ub (reducedInput (chart := chart) zero) ∧
      (∀ t : result.lower.Terminal,result.lower.terminalSuccess t=true→
        CloseState (finiteSolutionTarget f A b) ε
          ((result.lower.terminalPath (.initial (reducedInput (chart := chart) zero)) t).state UA Ub))) := by
  dsimp only
  have hi:=normalized_input_conditions f A hA b hb UA henc Ub hcol hκ hinv hlo hhi hε0 hε1
  have hr:=reducedProcess_resources F c
  refine ⟨hi,reducedInput_zero zero hzero,hr.1,hr.2.1,hr.2.2.1,hr.2.2.2.1,hr.2.2.2.2,?_⟩
  intro hc hp
  apply reducedProcess_reachable F c zero UA Ub (finiteSolutionTarget f A b)
    (finiteSolutionTarget_unit f A hA b hb) hε0 hε1 _ hp
  intro t ht hm
  exact (closeDilationSolution_iff f henc.1 A hA b ε _).mp (hc t ht hm)

/-- The target displayed in the endpoint is exactly the active embedding of the
normalized original inverse solution. No physical padded inverse occurs. -/
theorem proposition23_target (f : D ↪ Bits n) (A : Matrix D D ℂ) (b : EuclideanSpace ℂ D) :
    finiteSolutionTarget f A b=WithLp.toLp 2
      (indexedVector (dataRegister n) (WithLp.ofLp
        (coordinateIsometry f (NormedSpace.normalize (WithLp.toLp 2 (A⁻¹ *ᵥ WithLp.ofLp b)))))) := rfl

end OptimalQLS.Reduction.GenericSolver
