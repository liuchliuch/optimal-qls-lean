import OptimalQLS.InputReflection
import OptimalQLS.GraphEncoding.SmallGates
import OptimalQLS.Preparation.CompilerAttachment.SourceSafety

/-! Proposition 4.5: exact swap transducer, literal two-query reflection,
real elementary phase test, and coherent cleanup in the physical caller. -/
noncomputable section
namespace OptimalQLS.PaperStatements
open Matrix TransducerCompiler BinaryClock PolynomialTransform
open Preparation Preparation.CompilerAttachment GraphEncoding
set_option synthInstance.maxSize 8192

/-- The same prepared reflection appears in both the catalytic identity and
its emitted controlled implementation. Only its prepared column is used. -/
theorem proposition45 (a n ℓ : ℕ) :
    let c := compilerReflectionCall a n ℓ
    (c.toQuery (sourceGateEval a n ℓ)).matrixQueries = 0 ∧
    (c.toQuery (sourceGateEval a n ℓ)).vectorQueries = 2 ∧
    c.workGates ≤ 11222*(n+1) ∧
    (∀ g, NamedInstruction.gate g ∈ c → g.arity ≤ 2 ∧
      ∀ i j, ((sourceGateEval a n ℓ g).val i j).im = 0) ∧
    (∀ p adj, NamedInstruction.vectorCall p adj ∈ c → p = sourceSingleFlagPort a n ℓ) ∧
    (GateSynthesis.placeHom (sumBitWiring (Fin 4 × Bits n))
      (complexifyRealUnitary RealToffoli.xReal) =
        (swapPublicPrivate : Matrix.unitaryGroup ((Fin 4 × Bits n) ⊕ (Fin 4 × Bits n)) ℂ)) ∧
    (GateSynthesis.placeHom (controlledBitWiring Unit (Fin 4 × Bits n))
      (complexifyRealUnitary (controlledBitReal RealToffoli.xReal)) =
      sumUnitary (tensorUnitary (1 : Matrix.unitaryGroup Unit ℂ)
        (swapPublicPrivate : Matrix.unitaryGroup ((Fin 4 × Bits n) ⊕ (Fin 4 × Bits n)) ℂ)) 1) ∧
    ∀ (UA : Matrix.unitaryGroup (Bits a × Bits n) ℂ) (Ub : Matrix.unitaryGroup (Bits n) ℂ),
      let U := signalLift (S := Fin 4) Ub
      let e₀ := ((1 : Fin 4), fun _ : Fin n => false)
      let R := preparedReflection U e₀
      R.val = (2 : ℂ) • (Matrix.of (fun i j => U i e₀ * star (U j e₀))) - 1 ∧
      (∀ ξ : Fin 4 × Bits n → ℂ,
        (inputReflectionTransducer U e₀).val *ᵥ Sum.elim ξ ξ =
          Sum.elim (R.val *ᵥ ξ) ξ ∧ energy ξ = ‖WithLp.toLp 2 ξ‖^2) ∧
      ((c.toQuery (sourceGateEval a n ℓ)).eval UA Ub).val * basisInsertion (clean a n ℓ) =
        basisInsertion (clean a n ℓ) *
          ((compilerDataPort (PreparationData (Bits a) (Bits n)) ℓ .second).apply
            (doubleOracle (signalLift (S := GraphEncoding.PhysicalSignal (Bits a)) R))).val := by
  dsimp only
  obtain ⟨hm, hv, hg⟩ := compilerReflectionCall_counts a n ℓ
  refine ⟨hm, hv, hg, ?_, compilerReflectionCall_single_flag a n ℓ,
    swap_one_qubit, ?_, ?_⟩
  · intro g hg
    exact ⟨SourceGate.arity_le_two g,
      sourceGate_real a n ℓ g (compilerReflectionCall_real a n ℓ g hg)⟩
  · simpa only [swap_one_qubit] using
      (controlled_one_is_two (C := Unit) (W := Fin 4 × Bits n) RealToffoli.xReal)
  · intro UA Ub
    exact ⟨preparedReflection_matrix _ _,
      fun ξ => ⟨inputReflectionTransducer_identity _ _ ξ, energy_eq_norm_sq ξ⟩,
      compilerReflectionCall_intertwines a n ℓ UA Ub⟩

end OptimalQLS.PaperStatements
