import OptimalQLS.PhysicalRobustness.Input
import OptimalQLS.PhysicalRobustness.PhysicalEndpoint
import OptimalQLS.PhysicalRobustness.Preparation
import OptimalQLS.PhysicalRobustness.CoherentRefinement
import OptimalQLS.PhysicalRobustness.Parity

/-! Complete noisy physical-input core: actual support-aware target, original
finite preparation, literal single-flag refinement circuits, and exact right
support after Hermitian dilation. Final retry/reset and general-input oracle
adapters are assembled by the main theorem integration. -/
