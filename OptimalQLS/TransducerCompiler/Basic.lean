import OptimalQLS.OracleCircuit
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Tactic

noncomputable section
namespace OptimalQLS.TransducerCompiler
open Matrix
open scoped Matrix.Norms.L2Operator
set_option maxHeartbeats 400000


variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A literal computational-basis permutation, with no data-dependent entries. -/
def permutation (e : Equiv.Perm n) : Matrix.unitaryGroup n ℂ :=
  ⟨e.permMatrix ℂ, by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_permMatrix, ← Matrix.permMatrix_mul]
    simp⟩

@[simp] theorem permutation_apply (e : Equiv.Perm n) (v : n → ℂ) :
    (permutation e : Matrix n n ℂ) *ᵥ v = v ∘ e :=
  Matrix.permMatrix_mulVec e

/-- All computational-basis routing matrices are real. -/
theorem permutation_real (e : Equiv.Perm n) (i j : n) :
    ((permutation e : Matrix n n ℂ) i j).im = 0 := by
  by_cases h : e i = j <;> simp [permutation, PEquiv.toMatrix, h]

/-- Controlled matrix multiplication acts separately in each clock sector. -/
theorem blockDiagonal_mulVec {c : Type*} [Fintype c] [DecidableEq c]
    (M : c → Matrix n n ℂ) (v : n × c → ℂ) (i : n) (k : c) :
    (Matrix.blockDiagonal M *ᵥ v) (i,k) = (M k *ᵥ fun j => v (j,k)) i := by
  simp [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.blockDiagonal_apply]

@[simp] theorem controlled_apply (K : ℕ) (b : Fin K → Bool)
    (U : Matrix.unitaryGroup n ℂ) (v : n × Fin K → ℂ) (i : n) (k : Fin K) :
    ((controlledUnitary K b U : Matrix (n × Fin K) (n × Fin K) ℂ) *ᵥ v) (i,k) =
      if b k then ((U : Matrix n n ℂ) *ᵥ fun j => v (j,k)) i else v (i,k) := by
  change (Matrix.blockDiagonal _ *ᵥ v) (i,k) = _
  rw [blockDiagonal_mulVec]
  cases b k <;> simp

/-- Controls indexed by an arbitrary finite register. -/
def controlledOn {c : Type*} [Fintype c] [DecidableEq c]
    (control : c → Bool) (U : Matrix.unitaryGroup n ℂ) :
    Matrix.unitaryGroup (n × c) ℂ :=
  ⟨Matrix.blockDiagonal (fun j => if control j then (U : Matrix n n ℂ) else 1), by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
      Matrix.blockDiagonal_conjTranspose, ← Matrix.blockDiagonal_mul]
    have h : (fun j : c =>
        (if control j then (U : Matrix n n ℂ) else 1) *
          (if control j then (U : Matrix n n ℂ) else 1)ᴴ) = 1 := by
      funext j
      have hu : (U : Matrix n n ℂ) * (U : Matrix n n ℂ)ᴴ = 1 := U.property.2
      cases control j <;> simp [hu]
    rw [h, Matrix.blockDiagonal_one]⟩

@[simp] theorem controlledOn_apply {c : Type*} [Fintype c] [DecidableEq c]
    (b : c → Bool) (U : Matrix.unitaryGroup n ℂ) (v : n × c → ℂ) (i : n) (k : c) :
    ((controlledOn b U : Matrix (n × c) (n × c) ℂ) *ᵥ v) (i,k) =
      if b k then ((U : Matrix n n ℂ) *ᵥ fun j => v (j,k)) i else v (i,k) := by
  change (Matrix.blockDiagonal _ *ᵥ v) (i,k) = _
  rw [blockDiagonal_mulVec]
  cases b k <;> simp

theorem rewire_apply {m : Type*} [Fintype m] [DecidableEq m]
    (e : n ≃ m) (U : Matrix.unitaryGroup n ℂ) (v : m → ℂ) :
    (rewireUnitary e U : Matrix m m ℂ) *ᵥ v =
      ((U : Matrix n n ℂ) *ᵥ (v ∘ e)) ∘ e.symm :=
  Matrix.submatrix_mulVec_equiv _ _ _ _

/-- Matrix unitaries preserve the Hilbert-space (not coordinate supremum) norm. -/
theorem unitary_norm (U : Matrix.unitaryGroup n ℂ) (v : EuclideanSpace ℂ n) :
    ‖Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) (U : Matrix n n ℂ) v‖ = ‖v‖ := by
  apply ContinuousLinearMap.norm_map_of_mem_unitary
  exact Unitary.map_mem (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)) U.property

/-- The two perturbations in the catalytic argument. This is used only after
an exact compiler invariant has been proved from the gate sequence. -/
theorem catalytic_error (U : Matrix.unitaryGroup n ℂ)
    (x y v : EuclideanSpace ℂ n)
    (h : Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) (U : Matrix n n ℂ) (x + v) = y + v) :
    ‖Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) (U : Matrix n n ℂ) x - y‖ ≤ 2 * ‖v‖ := by
  have heq : Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) (U : Matrix n n ℂ) x - y =
      v - Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) (U : Matrix n n ℂ) v := by
    rw [map_add] at h
    apply sub_eq_sub_iff_add_eq_add.mpr
    simpa [add_comm] using h
  rw [heq]
  calc
    _ ≤ ‖v‖ + ‖Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) (U : Matrix n n ℂ) v‖ := norm_sub_le _ _
    _ = 2 * ‖v‖ := by rw [unitary_norm]; ring

/-- Route a selected clock slot separately in every label/data sector.
In applications the selector depends only on the finite label, not the data. -/
def routing {K : ℕ} (zero : Fin K) (f : n → Fin K) : Equiv.Perm (n × Fin K) where
  toFun x := (x.1, Equiv.swap zero (f x.1) x.2)
  invFun x := (x.1, Equiv.swap zero (f x.1) x.2)
  left_inv x := by simp
  right_inv x := by simp

@[simp] theorem routing_apply {K : ℕ} (zero : Fin K) (f : n → Fin K) (x : n × Fin K) :
    routing zero f x = (x.1, Equiv.swap zero (f x.1) x.2) := rfl

/-- A work call whose public and private sectors have distinct clock addresses. -/
def routedWork {K : ℕ} (zero : Fin K) (f : n → Fin K)
    (U : Matrix.unitaryGroup n ℂ) : Matrix.unitaryGroup (n × Fin K) ℂ :=
  permutation (routing zero f) * controlledUnitary K (fun k => decide (k = zero)) U *
    permutation (routing zero f)

theorem routedWork_apply {K : ℕ} (zero : Fin K) (f : n → Fin K)
    (U : Matrix.unitaryGroup n ℂ) (v : n × Fin K → ℂ) (i : n) (k : Fin K) :
    ((routedWork zero f U : Matrix (n × Fin K) (n × Fin K) ℂ) *ᵥ v) (i,k) =
      if k = f i then ((U : Matrix n n ℂ) *ᵥ fun j => v (j,f j)) i else v (i,k) := by
  simp only [routedWork, Submonoid.coe_mul, ← Matrix.mulVec_mulVec,
    permutation_apply, Function.comp_apply, routing_apply]
  rw [controlled_apply]
  have hz : Equiv.swap zero (f i) k = zero ↔ k = f i := by
    rw [Equiv.swap_apply_eq_iff, Equiv.swap_apply_left]
  simp only [decide_eq_true_eq, hz]
  split_ifs with hk
  · congr 2
    funext j
    simp [hk]
  · simp

end OptimalQLS.TransducerCompiler
