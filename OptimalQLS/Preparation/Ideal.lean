import OptimalQLS.Preparation.SignalLift
import OptimalQLS.MatrixPseudoInverse

noncomputable section
namespace OptimalQLS.Preparation
open Matrix
variable {D : Type*} [Fintype D] [DecidableEq D]

theorem matrixKernelProjection_star (H : Matrix D D ℂ) :
    star (matrixKernelProjection H)=matrixKernelProjection H := by
  let φ := Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ)
  apply φ.injective
  change φ (star (matrixKernelProjection H)) = φ (matrixKernelProjection H)
  rw [map_star]
  change star (φ (φ.symm (LinearMap.ker (φ H).toLinearMap).starProjection)) =
    φ (φ.symm (LinearMap.ker (φ H).toLinearMap).starProjection)
  rw [φ.apply_symm_apply]
  exact ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
    (LinearMap.ker (φ H).toLinearMap).starProjection_isSymmetric

theorem matrixKernelProjection_square (H : Matrix D D ℂ) :
    matrixKernelProjection H * matrixKernelProjection H = matrixKernelProjection H := by
  let φ := Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ)
  apply φ.injective
  rw [map_mul]
  change φ (φ.symm (LinearMap.ker (φ H).toLinearMap).starProjection) *
    φ (φ.symm (LinearMap.ker (φ H).toLinearMap).starProjection) =
    φ (φ.symm (LinearMap.ker (φ H).toLinearMap).starProjection)
  rw [φ.apply_symm_apply]
  exact (LinearMap.ker (φ H).toLinearMap).isIdempotentElem_starProjection

/-- The exact kernel reflection on the public data space. -/
def kernelReflectionMatrix (H : Matrix D D ℂ) : Matrix.unitaryGroup D ℂ :=
  ⟨(2 : ℝ) • matrixKernelProjection H - 1, by
    have hs : star ((2 : ℝ) • matrixKernelProjection H - 1) =
        (2 : ℝ) • matrixKernelProjection H - 1 := by
      simp [star_smul,matrixKernelProjection_star]
    have hh : ((2 : ℝ) • matrixKernelProjection H - 1)*
        ((2 : ℝ) • matrixKernelProjection H - 1)=1 := by
      simp only [sub_mul,mul_sub,smul_mul_assoc,mul_smul_comm,matrixKernelProjection_square,
        mul_one,one_mul]
      module
    constructor <;> rw [hs] <;> exact hh⟩

def idealUnitary (H : Matrix D D ℂ) (R : Matrix.unitaryGroup D ℂ) : Matrix.unitaryGroup D ℂ :=
  -(R * kernelReflectionMatrix H)

theorem idealUnitary_apply (H : Matrix D D ℂ) (R : Matrix.unitaryGroup D ℂ) (q : D → ℂ) :
    (idealUnitary H R : Matrix D D ℂ)*ᵥq =
      -((R : Matrix D D ℂ)*ᵥ((2:ℝ) • (matrixKernelProjection H*ᵥq)-q)) := by
  change (-((R : Matrix D D ℂ)*((2:ℝ) • matrixKernelProjection H-1)))*ᵥq = _
  rw [Matrix.neg_mulVec,← Matrix.mulVec_mulVec,Matrix.sub_mulVec,Matrix.smul_mulVec,
    Matrix.one_mulVec]

/-- Both scalar rows are extracted from the already-verified block-matrix
fractional transducer, for its actual inverse-defined catalyst. -/
theorem fractional_rows (U : Matrix.unitaryGroup D ℂ) {r : ℝ} (hr : |r|<1) (ξ : D → ℂ) :
    (-r) • ξ + Real.sqrt (1-r^2) • ((U : Matrix D D ℂ)*ᵥfractionalCatalyst U r ξ) =
      fractionalAction U r*ᵥξ ∧
    Real.sqrt (1-r^2) • ξ + r • ((U : Matrix D D ℂ)*ᵥfractionalCatalyst U r ξ) =
      fractionalCatalyst U r ξ := by
  have h := fractional_transduction U hr ξ
  rw [fractionalMix,Matrix.fromBlocks_mulVec] at h
  constructor
  · have hh := congrArg (fun v : (D ⊕ D) → ℂ => fun i => v (.inl i)) h
    simpa [Matrix.smul_mulVec,Matrix.neg_mulVec,Matrix.one_mulVec] using hh
  · have hh := congrArg (fun v : (D ⊕ D) → ℂ => fun i => v (.inr i)) h
    simpa [Matrix.smul_mulVec,Matrix.neg_mulVec,Matrix.one_mulVec] using hh

end OptimalQLS.Preparation
