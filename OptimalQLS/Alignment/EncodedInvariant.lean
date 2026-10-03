import OptimalQLS.Alignment.WorkInvariant
import OptimalQLS.Preparation.IdealGeometry
import OptimalQLS.Preparation.SignalLift

/-! The real subspaces are obtained from the actual Hermitian block encoding
and actual prepared-vector reflection; no invariance certificate is assumed. -/
noncomputable section
namespace OptimalQLS.Alignment
open Matrix Preparation
variable {S D : Type*} [Fintype S] [DecidableEq S] [Fintype D] [DecidableEq D]

/-- The real Krylov subspace in matrix-coordinate notation. -/
def dataKrylov (H : Matrix D D ℂ) (e : D → ℂ) : Submodule ℝ (D → ℂ) :=
  (hermitianKrylov (Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) H) (WithLp.toLp 2 e)).comap
    (WithLp.linearEquiv 2 ℝ (D → ℂ)).symm.toLinearMap

@[simp] theorem mem_dataKrylov (H : Matrix D D ℂ) (e x : D → ℂ) :
    x ∈ dataKrylov H e ↔ WithLp.toLp 2 x ∈
      hermitianKrylov (Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) H) (WithLp.toLp 2 e) := Iff.rfl

theorem input_mem_dataKrylov (H : Matrix D D ℂ) (e : D → ℂ) : e ∈ dataKrylov H e :=
  self_mem_realKrylov _ _

theorem mulVec_mem_dataKrylov (H : Matrix D D ℂ) (e : D → ℂ)
    {x : D → ℂ} (hx : x ∈ dataKrylov H e) : H*ᵥx ∈ dataKrylov H e :=
  map_mem_realKrylov _ _ hx

/-- Public signal-zero Krylov subspace. -/
def signalKrylov (s₀ : S) (H : Matrix D D ℂ) (e : D → ℂ) : Submodule ℝ (S × D → ℂ) :=
  (dataKrylov H e).map (realMatrixMap (signalInjection s₀))

theorem injection_mem_signalKrylov (s₀ : S) (H : Matrix D D ℂ) (e : D → ℂ)
    {x : D → ℂ} (hx : x ∈ dataKrylov H e) : signalInjection s₀*ᵥx ∈ signalKrylov s₀ H e :=
  Submodule.mem_map.mpr ⟨x,hx,rfl⟩

theorem projector_fixes_signalKrylov (s₀ : S) (H : Matrix D D ℂ) (e : D → ℂ)
    {x : S × D → ℂ} (hx : x ∈ signalKrylov s₀ H e) : signalProjector s₀*ᵥx=x := by
  obtain ⟨x,hx,rfl⟩ := hx
  exact signalProjector_injection s₀ x

/-- This compression is derived from the literal signal block. -/
theorem compression_mem_signalKrylov (s₀ : S) (H : Matrix D D ℂ) (e : D → ℂ)
    (V : Matrix.unitaryGroup (S × D) ℂ) {α : ℝ} (hα : α≠0)
    (hblock : H=α • signalBlock s₀ V) {x : S × D → ℂ}
    (hx : x ∈ signalKrylov s₀ H e) : signalProjector s₀*ᵥ(V.val*ᵥx) ∈ signalKrylov s₀ H e := by
  obtain ⟨x,hx,rfl⟩ := hx
  rw [realMatrixMap_apply,signalProjector_oracle_injection s₀ V H hα hblock]
  exact (signalKrylov s₀ H e).smul_mem _
    (injection_mem_signalKrylov s₀ H e (mulVec_mem_dataKrylov H e hx))

theorem encodedWork_preserves (s₀ : S) (H : Matrix D D ℂ) (e : D → ℂ)
    (V : Matrix.unitaryGroup (S × D) ℂ) {α μ r : ℝ} (hα : α≠0)
    (hblock : H=α • signalBlock s₀ V) (hμ : 0<μ) (hr : |r|<1)
    {v : Fin 8 × (S × D) → ℂ}
    (hv : eightInvariant (signalKrylov s₀ H e) (oracleSpan (signalKrylov s₀ H e) V.val) v) :
    eightInvariant (signalKrylov s₀ H e) (oracleSpan (signalKrylov s₀ H e) V.val)
      ((preparationWork (signalProjector s₀) (signalProjector_star s₀)
        (signalProjector_idempotent s₀) hμ hr).val*ᵥv) := by
  apply preparationWork_preserves _ _ (le_oracleSpan _ _) _ _ _
    (fun x hx => projector_fixes_signalKrylov s₀ H e hx) ?_ hμ hr hv
  intro x hx
  exact compression_oracleSpan _ _ _ (fun x hx => projector_fixes_signalKrylov s₀ H e hx)
    (fun x hx => compression_mem_signalKrylov s₀ H e V hα hblock hx) hx

/-- Hermiticity makes the coefficients in the actual rank-one reflection real. -/
theorem preparedReflection_preserves_dataKrylov (H : Matrix D D ℂ) (hH : star H=H)
    (e : EuclideanSpace ℂ D) (he : ‖e‖=1) (Ub : Matrix.unitaryGroup D ℂ)
    (i₀ : D) (hcol : ∀ i, Ub i i₀=e i) {x : D → ℂ}
    (hx : x ∈ dataKrylov H (WithLp.ofLp e)) :
    (preparedReflection Ub i₀).val*ᵥx ∈ dataKrylov H (WithLp.ofLp e) := by
  have hHerm : IsSelfAdjoint (Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) H) := by
    change star (Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) H) = _
    rw [← map_star,hH]
  have hR := congrArg (fun T : EuclideanSpace ℂ D →L[ℂ] EuclideanSpace ℂ D => T (WithLp.toLp 2 x))
    (preparedReflection_to_operator Ub i₀ e he hcol)
  dsimp only at hR
  rw [mem_dataKrylov]
  change Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) (preparedReflection Ub i₀).val
      (WithLp.toLp 2 x) ∈ _
  rw [hR,vectorReflectionUnitary_apply]
  have hi := inputReflection_mem_hermitianKrylov
    (Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) H) hHerm e hx
  simpa [inputReflection,smul_smul,mul_assoc] using hi

theorem signalReflection_preserves_signalKrylov (s₀ : S)
    (H : Matrix D D ℂ) (hH : star H=H) (e : EuclideanSpace ℂ D) (he : ‖e‖=1)
    (Ub : Matrix.unitaryGroup D ℂ) (i₀ : D) (hcol : ∀ i, Ub i i₀=e i)
    {x : S × D → ℂ} (hx : x ∈ signalKrylov s₀ H (WithLp.ofLp e)) :
    (signalLift (S := S) (preparedReflection Ub i₀)).val*ᵥx ∈
      signalKrylov s₀ H (WithLp.ofLp e) := by
  obtain ⟨x,hx,rfl⟩ := hx
  rw [realMatrixMap_apply,signalLift_injection]
  exact injection_mem_signalKrylov s₀ H _
    (preparedReflection_preserves_dataKrylov H hH e he Ub i₀ hcol hx)

end OptimalQLS.Alignment
