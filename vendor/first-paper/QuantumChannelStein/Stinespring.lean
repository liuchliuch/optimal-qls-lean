import QuantumChannelStein.Kraus

/-!
# Concrete Stinespring matrix of a normalized Kraus family

The output factor precedes the environment factor, as in the paper. The
matrix identity `Vᴴ V = 1` is the algebraic isometry condition. This module
makes no claim about operator norm estimates or uniqueness of dilations.
-/
noncomputable section
namespace QuantumChannelStein
open scoped BigOperators ComplexOrder
open Matrix
namespace KrausChannel
variable {n m : ℕ}

/-- Output-environment matrix of the Kraus Stinespring construction. -/
def stinespring (Φ : KrausChannel n m) :
    Matrix (Fin m × Fin Φ.rank) (Fin n) ℂ :=
  fun x j => Φ.kraus x.2 x.1 j

/-- Kraus normalization is precisely the isometry matrix identity. -/
theorem stinespring_isometry (Φ : KrausChannel n m) :
    Φ.stinespringᴴ * Φ.stinespring = 1 := by
  ext i j
  have h := congrFun (congrFun Φ.normalized i) j
  simp only [stinespring, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fintype.sum_prod_type] at h ⊢
  rw [Finset.sum_comm]
  exact h

/-- Discard the finite environment by partial trace. -/
def traceEnvironment {e : ℕ}
    (X : Matrix (Fin m × Fin e) (Fin m × Fin e) ℂ) : Operator m :=
  fun a b => ∑ i, X (a, i) (b, i)

/-- Discarding the environment of the Stinespring output recovers the channel. -/
theorem traceEnvironment_stinespring (Φ : KrausChannel n m) (X : Operator n) :
    traceEnvironment (Φ.stinespring * X * Φ.stinespringᴴ) = Φ.apply X := by
  ext a b
  simp [traceEnvironment, stinespring, apply, Matrix.sum_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply]

end KrausChannel
end QuantumChannelStein
