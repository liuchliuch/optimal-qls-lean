import Verification.Statements
import OptimalQLS

/-! Proofs of the independently stated Comparator obligations. -/
namespace Verification.Certificate

theorem upper : Specification.Upper.Exact := by
  intro p d _ hk he he1
  obtain ⟨I, hs, hi, hq, hr, hw, hc⟩ :=
    OptimalQLS.Reduction.PhysicalUpper.theorem57 p d hk he he1
  exact ⟨I, ⟨hs, hi, hq, hr, hw⟩, hc⟩

theorem upper_relaxed : Specification.Upper.Relaxed := by
  intro p d _ hk he he1
  obtain ⟨I, hs, hi, hq, hr, hw, hc⟩ :=
    OptimalQLS.Reduction.PhysicalUpper.theorem57_relaxed p d hk he he1
  exact ⟨I, ⟨hs, hi, hq, hr, hw⟩, hc⟩

theorem lower : Specification.Lower.{u} := by
  intro kappa estimate eps hk he hek heps hsmall
  exact OptimalQLS.LowerBounds.Physical.theorem61.{u} hk he hek heps hsmall

theorem robust : Specification.Robust.Statement := by
  intro p d _ hk he he1
  exact OptimalQLS.PhysicalRobustness.GeneralProgram.theorem72 p d hk he he1

end Verification.Certificate
