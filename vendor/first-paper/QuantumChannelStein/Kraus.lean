import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Tactic

/-!
# Finite Kraus representations

Concrete finite-dimensional matrix foundations for arXiv:2609.27196, §2.1.
This file defines concrete Kraus representations. The equivalence with every
finite-dimensional CPTP matrix map is proved in `ChannelRepresentation.lean`.
-/
noncomputable section
namespace QuantumChannelStein

open scoped BigOperators ComplexOrder Kronecker
open Matrix

abbrev Operator (n : ℕ) := Matrix (Fin n) (Fin n) ℂ

/-- A density matrix has positive semidefinite matrix and complex trace one. -/
structure State (n : ℕ) where
  matrix : Operator n
  positive : matrix.PosSemidef
  trace_one : matrix.trace = 1

/-- An effect is a positive matrix bounded above by the identity in Löwner order. -/
structure Effect (n : ℕ) where
  matrix : Operator n
  positive : matrix.PosSemidef
  complement_positive : (1 - matrix).PosSemidef

/-- A finite Kraus family with the trace-preserving normalization. -/
structure KrausChannel (n m : ℕ) where
  rank : ℕ
  kraus : Fin rank → Matrix (Fin m) (Fin n) ℂ
  normalized : ∑ i, (kraus i)ᴴ * kraus i = 1

namespace KrausChannel

variable {n m : ℕ}

/-- Schrödinger-picture action of a concrete Kraus family. -/
def apply (Φ : KrausChannel n m) (X : Operator n) : Operator m :=
  ∑ i, Φ.kraus i * X * (Φ.kraus i)ᴴ

@[simp] theorem apply_zero (Φ : KrausChannel n m) : Φ.apply 0 = 0 := by
  simp [apply]

@[simp] theorem apply_add (Φ : KrausChannel n m) (X Y : Operator n) :
    Φ.apply (X + Y) = Φ.apply X + Φ.apply Y := by
  simp [apply, Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib]

@[simp] theorem apply_smul (Φ : KrausChannel n m) (c : ℂ) (X : Operator n) :
    Φ.apply (c • X) = c • Φ.apply X := by
  simp [apply, Matrix.mul_smul, Matrix.smul_mul, Finset.smul_sum]

/-- The underlying complex-linear map. -/
def toLinearMap (Φ : KrausChannel n m) : Operator n →ₗ[ℂ] Operator m where
  toFun := Φ.apply
  map_add' := Φ.apply_add
  map_smul' := Φ.apply_smul

/-- Kraus normalization implies trace preservation. -/
theorem trace_apply (Φ : KrausChannel n m) (X : Operator n) :
    (Φ.apply X).trace = X.trace := by
  unfold apply
  rw [Matrix.trace_sum]
  conv_lhs => arg 2; ext i; rw [Matrix.trace_mul_cycle]
  rw [← Matrix.trace_sum, ← Matrix.sum_mul, Φ.normalized, Matrix.one_mul]

/-- Positivity follows from congruence of positive semidefinite matrices. -/
theorem apply_positive (Φ : KrausChannel n m) {X : Operator n} (hX : X.PosSemidef) :
    (Φ.apply X).PosSemidef := by
  unfold apply
  apply Finset.sum_induction
  · intro A B hA hB
    exact hA.add hB
  · exact Matrix.PosSemidef.zero
  · intro i _
    exact hX.mul_mul_conjTranspose_same (Φ.kraus i)

/-- A channel represented by a normalized Kraus family sends states to states. -/
def onState (Φ : KrausChannel n m) (ρ : State n) : State m where
  matrix := Φ.apply ρ.matrix
  positive := Φ.apply_positive ρ.positive
  trace_one := (Φ.trace_apply ρ.matrix).trans ρ.trace_one


/-- Identity extension on a reference system, represented by `I ⊗ Kᵢ`. -/
def amplify (Φ : KrausChannel n m) (r : ℕ)
    (X : Matrix (Fin r × Fin n) (Fin r × Fin n) ℂ) :
    Matrix (Fin r × Fin m) (Fin r × Fin m) ℂ :=
  ∑ i, ((1 : Operator r) ⊗ₖ Φ.kraus i) * X *
    ((1 : Operator r) ⊗ₖ Φ.kraus i)ᴴ

/-- Positivity persists for every finite reference dimension. -/
theorem amplify_positive (Φ : KrausChannel n m) (r : ℕ)
    {X : Matrix (Fin r × Fin n) (Fin r × Fin n) ℂ} (hX : X.PosSemidef) :
    (Φ.amplify r X).PosSemidef := by
  unfold amplify
  apply Finset.sum_induction
  · intro A B hA hB
    exact hA.add hB
  · exact Matrix.PosSemidef.zero
  · intro i _
    exact hX.mul_mul_conjTranspose_same _

/-- The extension really applies the original map to each reference block. -/
theorem amplify_block (Φ : KrausChannel n m) (r : ℕ)
    (X : Matrix (Fin r × Fin n) (Fin r × Fin n) ℂ)
    (a b : Fin r) (u v : Fin m) :
    Φ.amplify r X (a, u) (b, v) =
      Φ.apply (fun i j => X (a, i) (b, j)) u v := by
  simp [amplify, apply, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fintype.sum_prod_type, Matrix.one_apply, apply_ite]


/-- The reference-extended Kraus family retains its normalization. -/
theorem amplify_normalized (Φ : KrausChannel n m) (r : ℕ) :
    (∑ i, ((1 : Operator r) ⊗ₖ Φ.kraus i)ᴴ *
      ((1 : Operator r) ⊗ₖ Φ.kraus i)) = 1 := by
  simp_rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    ← Matrix.mul_kronecker_mul, Matrix.one_mul]
  have h : (∑ i, (1 : Operator r) ⊗ₖ ((Φ.kraus i)ᴴ * Φ.kraus i)) =
      (1 : Operator r) ⊗ₖ (∑ i, (Φ.kraus i)ᴴ * Φ.kraus i) := by
    ext ⟨a, u⟩ ⟨b, v⟩
    simp [Matrix.sum_apply, Finset.mul_sum]
  rw [h, Φ.normalized, Matrix.one_kronecker_one]

/-- The arbitrary finite-reference extension is trace preserving. -/
theorem trace_amplify (Φ : KrausChannel n m) (r : ℕ)
    (X : Matrix (Fin r × Fin n) (Fin r × Fin n) ℂ) :
    (Φ.amplify r X).trace = X.trace := by
  unfold amplify
  rw [Matrix.trace_sum]
  conv_lhs => arg 2; ext i; rw [Matrix.trace_mul_cycle]
  rw [← Matrix.trace_sum, ← Matrix.sum_mul, Φ.amplify_normalized, Matrix.one_mul]

end KrausChannel
end QuantumChannelStein
