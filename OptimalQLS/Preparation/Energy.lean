import OptimalQLS.Preparation.CompilerBridge
import OptimalQLS.TransducerCompiler.Energy

noncomputable section
namespace OptimalQLS.Preparation
open Matrix TransducerCompiler
variable {F S D : Type*} [Fintype F] [DecidableEq F]
  [Fintype S] [DecidableEq S] [Fintype D] [DecidableEq D]

theorem doubleVector_energy (x y : F → ℂ) :
    energy (doubleVector x y)=energy x+energy y := by
  simp [energy,doubleVector,Fintype.sum_prod_type,Fintype.sum_bool,add_comm]

@[simp] theorem zero_energy : energy (0 : F → ℂ)=0 := by simp [energy]

theorem signal_energy (s₀ : S) (x : D → ℂ) :
    energy (signalInjection s₀*ᵥx)=energy x := by
  rw [energy_eq_norm_sq,energy_eq_norm_sq]
  have h := (signalIsometry (D := D) s₀).norm_map (WithLp.toLp 2 x)
  exact congrArg (fun t : ℝ => t^2) h

theorem unitary_energy (U : Matrix.unitaryGroup F ℂ) (x : F → ℂ) :
    energy (U.val*ᵥx)=energy x := by
  rw [energy_eq_norm_sq,energy_eq_norm_sq]
  exact congrArg (fun t : ℝ => t^2) (unitary_norm U (WithLp.toLp 2 x))

/-- Reflection preserves the complete catalyst norm, including both kernel
and nonkernel components. -/
theorem kernel_reflection_energy (H : Matrix D D ℂ) (x : D → ℂ) :
    energy ((2:ℝ) • (matrixKernelProjection H*ᵥx)-x)=energy x := by
  have h : (kernelReflectionMatrix H).val*ᵥx=(2:ℝ) • (matrixKernelProjection H*ᵥx)-x := by
    change (((2:ℂ) • matrixKernelProjection H-1)*ᵥx)=_
    simp only [Matrix.sub_mulVec,Matrix.smul_mulVec,Matrix.one_mulVec]
    rfl
  rw [← h]
  exact unitary_energy _ _

end OptimalQLS.Preparation
