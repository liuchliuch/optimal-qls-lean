import OptimalQLS.Reduction.Circuits
import OptimalQLS.Reduction.Normalized

/-! # Physical reduction circuits for the normalized supplied oracles

These are whole-oracle clean-subspace identities. The only coordinate changes
are the displayed regroupings of the external-control, dilation, original
signal, and original data registers. No arbitrary Boolean query controls are
silently compiled or charged as elementary work gates.
-/
noncomputable section
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
namespace OptimalQLS.Reduction
open Matrix PolynomialTransform LowerBounds
variable {S D B : Type*} [Fintype S] [DecidableEq S]
  [Fintype D] [DecidableEq D] [Fintype B] [DecidableEq B]

/-- The vector-query implementation realizes precisely the supplied
preparation oracle used in the normalized-input theorem. -/
theorem vectorDilation_eq_preparation (Ub : Matrix.unitaryGroup D ℂ) :
    vectorDilation Ub = preparation Ub := by
  apply Subtype.ext
  rfl

theorem preparationCircuit_intertwines (adj : Bool)
    (UA : Matrix.unitaryGroup (S × D) ℂ) (Ub : Matrix.unitaryGroup D ℂ) :
    ((vectorDilationCircuit adj).toQuery.eval UA Ub).val*basisInsertion dilationSumClean =
      basisInsertion dilationSumClean *
        ((bitControlPort (D ⊕ D)).apply
          (if adj then (preparation Ub)⁻¹ else preparation Ub)).val := by
  simpa only [vectorDilation_eq_preparation] using
    vectorDilationCircuit_sum_intertwines adj UA Ub

theorem rewireUnitary_inv_eq {Q R : Type*} [Fintype Q] [DecidableEq Q]
    [Fintype R] [DecidableEq R] (e : Q ≃ R) (U : Matrix.unitaryGroup Q ℂ) :
    rewireUnitary e U⁻¹ = (rewireUnitary e U)⁻¹ := by
  apply Subtype.ext
  simp [rewireUnitary,Matrix.star_eq_conjTranspose,Matrix.conjTranspose_submatrix]

/-- Transport a literal external-control bit without changing which bit
controls the query. The target is only relabeled by the displayed equivalence. -/
theorem bitControlPort_rewire {Q R : Type*} [Fintype Q] [DecidableEq Q]
    [Fintype R] [DecidableEq R] (e : Q ≃ R) (U : Matrix.unitaryGroup Q ℂ) :
    rewireUnitary (Equiv.prodCongr (Equiv.refl Bool) e) ((bitControlPort Q).apply U) =
      (bitControlPort R).apply (rewireUnitary e U) := by
  apply Subtype.ext
  ext ⟨c,i⟩ ⟨d,j⟩
  simp [rewireUnitary,bitControlPort_entries]

/-- The external control remains first. The original signal register moves
outside the sum label, so the resulting oracle target is S × (D ⊕ D). -/
def dilationSignalLogicalWiring (S D : Type*) :
    Bool × ((S × D) ⊕ (S × D)) ≃ Bool × (S × (D ⊕ D)) :=
  Equiv.prodCongr (Equiv.refl Bool) (distributeSignal S D)

def dilationSignalClean (x : Bool × (S × (D ⊕ D))) : DilationSpace (S × D) :=
  dilationSumClean ((dilationSignalLogicalWiring S D).symm x)

theorem dilationSignalClean_left (c : Bool) (s : S) (i : D) :
    dilationSignalClean (c,(s,Sum.inl i)) = dilationClean ((c,false),(s,i)) := rfl

theorem dilationSignalClean_right (c : Bool) (s : S) (i : D) :
    dilationSignalClean (c,(s,Sum.inr i)) = dilationClean ((c,true),(s,i)) := rfl

theorem dilationSignalClean_injective :
    Function.Injective (dilationSignalClean (S := S) (D := D)) :=
  dilationSumClean_injective.comp (dilationSignalLogicalWiring S D).symm.injective

theorem dilationSignalClean_isometry :
    (basisInsertion (dilationSignalClean (S := S) (D := D)))ᴴ *
      basisInsertion (dilationSignalClean (S := S) (D := D)) = 1 :=
  basisInsertion_isometry _ dilationSignalClean_injective

/-- Literal controlled/adjoint simulation of the exact oracle appearing in
normalized_encoding. Every original signal/data column is included. -/
theorem dilationEncodingCircuit_intertwines (adj : Bool)
    (UA : Matrix.unitaryGroup (S × D) ℂ) (Ub : Matrix.unitaryGroup B ℂ) :
    ((dilationOracleCircuit adj).toQuery.eval UA Ub).val *
        basisInsertion (dilationSignalClean (S := S) (D := D)) =
      basisInsertion (dilationSignalClean (S := S) (D := D)) *
        ((bitControlPort (S × (D ⊕ D))).apply
          (if adj then (dilationEncoding UA)⁻¹ else dilationEncoding UA)).val := by
  have h := clean_intertwines_transport (Equiv.refl (DilationSpace (S × D)))
    (dilationSignalLogicalWiring S D) dilationSumClean
    ((dilationOracleCircuit adj).toQuery.eval UA Ub)
    ((bitControlPort ((S × D) ⊕ (S × D))).apply
      (if adj then (hermitianUnitaryDilation UA)⁻¹ else hermitianUnitaryDilation UA))
    (dilationOracleCircuit_sum_intertwines adj UA Ub)
  have he : rewireUnitary (dilationSignalLogicalWiring S D)
      ((bitControlPort ((S × D) ⊕ (S × D))).apply
        (if adj then (hermitianUnitaryDilation UA)⁻¹ else hermitianUnitaryDilation UA)) =
      (bitControlPort (S × (D ⊕ D))).apply
        (if adj then (dilationEncoding UA)⁻¹ else dilationEncoding UA) := by
    rw [dilationSignalLogicalWiring,bitControlPort_rewire]
    cases adj <;> simp [dilationEncoding,rewireUnitary_inv_eq]
  rw [he] at h
  exact h

theorem dilationEncodingCircuit_uncontrolled_intertwines (adj : Bool)
    (UA : Matrix.unitaryGroup (S × D) ℂ) (Ub : Matrix.unitaryGroup B ℂ) :
    ((dilationOracleCircuit adj).toQuery.eval UA Ub).val *
        basisInsertion (fun x => dilationSignalClean (true,x)) =
      basisInsertion (fun x => dilationSignalClean (true,x)) *
        (if adj then (dilationEncoding UA)⁻¹ else dilationEncoding UA).val :=
  active_control_intertwines _ _ _ (dilationEncodingCircuit_intertwines adj UA Ub)

/- The following audit commands inspect the dependency closure, not merely
the absence of proof placeholders in this source file. -/

end OptimalQLS.Reduction
