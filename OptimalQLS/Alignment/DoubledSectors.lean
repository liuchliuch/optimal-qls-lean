import OptimalQLS.Alignment.EncodedInvariant
import OptimalQLS.Preparation.CompilerBridge

noncomputable section
namespace OptimalQLS.Alignment
open Matrix Preparation TransducerCompiler
variable {F : Type*} [Fintype F] [DecidableEq F]

/-- Slice of the spare data bit, as an actual real-linear map. -/
def bitSlice (b : Bool) : (Bool × F → ℂ) →ₗ[ℝ] (F → ℂ) where
  toFun v := fun i => v (b,i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Independent real subspaces on the two copies of the common data register. -/
def doubleSpace (N M : Submodule ℝ (F → ℂ)) : Submodule ℝ (Bool × F → ℂ) :=
  N.comap (bitSlice false) ⊓ M.comap (bitSlice true)

@[simp] theorem mem_doubleSpace (N M : Submodule ℝ (F → ℂ)) (v : Bool × F → ℂ) :
    v ∈ doubleSpace N M ↔ (fun i => v (false,i)) ∈ N ∧ (fun i => v (true,i)) ∈ M := Iff.rfl

@[simp] theorem doubleVector_mem_doubleSpace (N M : Submodule ℝ (F → ℂ)) (x y : F → ℂ) :
    doubleVector x y ∈ doubleSpace N M ↔ x ∈ N ∧ y ∈ M := Iff.rfl

theorem eq_doubleVector (v : Bool × F → ℂ) :
    v = doubleVector (fun i => v (false,i)) (fun i => v (true,i)) := by
  funext ⟨b,i⟩; cases b <;> rfl

/-- The four compiler sectors encode exactly the five active preparation labels. -/
def preparationSectors (N M : Submodule ℝ (F → ℂ)) : Label → Submodule ℝ (Bool × F → ℂ)
  | .first => doubleSpace M M
  | _ => doubleSpace N ⊥

theorem doubleOracle_preserves (N M : Submodule ℝ (F → ℂ)) (U : Matrix.unitaryGroup F ℂ)
    (hN : ∀ x ∈ N, U.val*ᵥx∈N) (hM : ∀ x ∈ M, U.val*ᵥx∈M)
    {v : Bool × F → ℂ} (hv : v∈doubleSpace N M) :
    (doubleOracle U).val*ᵥv∈doubleSpace N M := by
  rw [eq_doubleVector v,doubleOracle_apply,doubleVector_mem_doubleSpace]
  exact ⟨hN _ hv.1,hM _ hv.2⟩

end OptimalQLS.Alignment
