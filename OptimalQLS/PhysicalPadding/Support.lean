import OptimalQLS.PhysicalPadding.Preparation
import OptimalQLS.PhysicalPadding.Dimensions

/-! Coordinate-level support statements for the actual accepted preparation. -/
noncomputable section
namespace OptimalQLS.PhysicalPadding
open Matrix GraphEncoding Preparation Alignment
variable {D P : Type*} [Fintype D] [DecidableEq D] [Fintype P] [DecidableEq P]

theorem coordinateIsometry_inactive (f : D ↪ P) (x : EuclideanSpace ℂ D)
    (p : P) (hp : p ∉ Set.range f) : coordinateIsometry f x p = 0 :=
  insertion_mulVec_inactive f _ p hp

theorem graphIsometry_inactive (f : D ↪ P) (x : EuclideanSpace ℂ (Fin 4 × D))
    (g : Fin 4) (p : P) (hp : p ∉ Set.range f) : graphIsometry f x (g,p) = 0 := by
  apply coordinateIsometry_inactive
  rintro ⟨⟨h,i⟩,hi⟩
  exact hp ⟨i, congrArg Prod.snd hi⟩

/-- Every coordinate outside the active data register vanishes in a graph Krylov vector. -/
theorem graphKrylov_inactive (f : D ↪ P) (A : Matrix D D ℂ) (κ : ℝ) (b : EuclideanSpace ℂ D)
    (y : EuclideanSpace ℂ (Fin 4 × P))
    (hy : y ∈ hermitianKrylov (Matrix.toEuclideanCLM (n := Fin 4 × P) (𝕜 := ℂ)
      (graphMatrix (zeroExtend f A) κ)) (graphInput (coordinateIsometry f b)))
    (g : Fin 4) (p : P) (hp : p ∉ Set.range f) : y (g,p) = 0 := by
  obtain ⟨x,hx⟩ := graphKrylov_active f A κ b hy
  rw [← hx]
  exact graphIsometry_inactive f x g p hp

/-- The equivalent matrix-coordinate invariant used by Alignment.FiniteAlignment. -/
theorem graph_dataKrylov_inactive (f : D ↪ P) (A : Matrix D D ℂ) (κ : ℝ)
    (b : EuclideanSpace ℂ D) (y : Fin 4 × P → ℂ)
    (hy : y ∈ dataKrylov (graphMatrix (zeroExtend f A) κ)
      (WithLp.ofLp (graphInput (coordinateIsometry f b))))
    (g : Fin 4) (p : P) (hp : p ∉ Set.range f) : y (g,p) = 0 :=
  graphKrylov_inactive f A κ b (WithLp.toLp 2 y) hy g p hp

theorem physicalSource_inactive {d : ℕ} (b : DataSpace d) (p : Fin (physicalDimension d))
    (hp : d ≤ p.val) : activeIsometry d b p = 0 := by
  apply coordinateIsometry_inactive
  rintro ⟨i,hi⟩
  have hh := congrArg Fin.val hi
  have hil := i.isLt
  change i.val = p.val at hh
  omega

end OptimalQLS.PhysicalPadding
