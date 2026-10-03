import OptimalQLS.Preparation.WorkGates.Foundations

noncomputable section
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace OptimalQLS.Preparation.WorkGates
open Matrix

def kernelLabelMatrix (a b : ℝ) (q : Bool) : Matrix (Fin 8) (Fin 8) ℂ :=
  !![1,0,0,0,0,0,0,0;
     0,(if q then (a:ℂ) else 1),0,(if q then (b:ℂ) else 0),0,0,0,0;
     0,(if q then (b:ℂ) else 0),0,(if q then (-a:ℂ) else -1),0,0,0,0;
     0,0,(if q then -1 else 1),0,0,0,0,0;
     0,0,0,0,1,0,0,0;
     0,0,0,0,0,1,0,0;
     0,0,0,0,0,0,1,0;
     0,0,0,0,0,0,0,1]

theorem kernelLabelMatrix_entries (a b : ℝ) (q : Bool) (i j : Fin 8) :
    kernelLabelMatrix a b q i j =
      if i=1 then (if j=1 then (if q then (a:ℂ) else 1)
        else if j=3 then (if q then (b:ℂ) else 0) else 0)
      else if i=2 then (if j=1 then (if q then (b:ℂ) else 0)
        else if j=3 then (if q then (-a:ℂ) else -1) else 0)
      else if i=3 then (if j=2 then (if q then -1 else 1) else 0)
      else if i=j then 1 else 0 := by
  fin_cases i <;> fin_cases j <;> rfl

private def kernelPrefix (a b : ℝ) (q : Bool) : Matrix (Fin 8) (Fin 8) ℂ :=
  !![1,0,0,0,0,0,0,0;
     0,(if q then (a:ℂ) else 1),0,(if q then (b:ℂ) else 0),0,0,0,0;
     0,0,(if q then -1 else 1),0,0,0,0,0;
     0,(if q then (-b:ℂ) else 0),0,(if q then (a:ℂ) else 1),0,0,0,0;
     0,0,0,0,1,0,0,0;
     0,0,0,0,0,1,0,0;
     0,0,0,0,0,0,1,0;
     0,0,0,0,0,0,0,1]

private def kernelSuffix : Matrix (Fin 8) (Fin 8) ℂ :=
  !![1,0,0,0,0,0,0,0;
     0,1,0,0,0,0,0,0;
     0,0,0,-1,0,0,0,0;
     0,0,1,0,0,0,0,0;
     0,0,0,0,1,0,0,0;
     0,0,0,0,0,1,0,0;
     0,0,0,0,0,0,1,0;
     0,0,0,0,0,0,0,1]

private def kernelMixLabel (a b : ℝ) (q : Bool) : Matrix (Fin 8) (Fin 8) ℂ :=
  !![1,0,0,0,0,0,0,0;
     0,(if q then (a:ℂ) else 1),0,(if q then (b:ℂ) else 0),0,0,0,0;
     0,0,1,0,0,0,0,0;
     0,(if q then (b:ℂ) else 0),0,(if q then (-a:ℂ) else 1),0,0,0,0;
     0,0,0,0,1,0,0,0;
     0,0,0,0,0,1,0,0;
     0,0,0,0,0,0,1,0;
     0,0,0,0,0,0,0,1]

private def kernelSignLabel (q : Bool) : Matrix (Fin 8) (Fin 8) ℂ :=
  !![1,0,0,0,0,0,0,0;
     0,1,0,0,0,0,0,0;
     0,0,(if q then -1 else 1),0,0,0,0,0;
     0,0,0,(if q then -1 else 1),0,0,0,0;
     0,0,0,0,1,0,0,0;
     0,0,0,0,0,1,0,0;
     0,0,0,0,0,0,1,0;
     0,0,0,0,0,0,0,1]


private theorem kernel_gate0_eq {μ r : ℝ} (hμ : 0<μ) (hr : |r|<1) (q : Bool) :
    labelOperation hμ hr q 0 = kernelMixLabel (kernelMixA μ) (kernelMixB μ) q := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [labelOperation, labelTargetMatrix, labelControl, labelTarget, labelGate,
      labelBits, Fin.forall_fin_succ, kernelGate, TransducerCompiler.complexifyRealUnitary,
      reflectionReal, GraphEncoding.zReal, kernelMixLabel]


private theorem kernel_gate1_eq {μ r : ℝ} (hμ : 0<μ) (hr : |r|<1) (q : Bool) :
    labelOperation hμ hr q 1 = kernelSignLabel q := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [labelOperation, labelTargetMatrix, labelControl, labelTarget, labelGate,
      labelBits, Fin.forall_fin_succ, kernelGate, TransducerCompiler.complexifyRealUnitary,
      reflectionReal, GraphEncoding.zReal, kernelSignLabel]


private theorem kernel_first_two {μ r : ℝ} (hμ : 0<μ) (hr : |r|<1) (q : Bool) :
    labelOperation hμ hr q 1 * labelOperation hμ hr q 0 =
      kernelPrefix (kernelMixA μ) (kernelMixB μ) q := by
  rw [kernel_gate1_eq, kernel_gate0_eq]
  cases q <;> simp [kernelSignLabel, kernelMixLabel, kernelPrefix]

private def gate2Matrix : Matrix (Fin 8) (Fin 8) ℂ :=
  !![1,0,0,0,0,0,0,0;
     0,1,0,0,0,0,0,0;
     0,0,0,1,0,0,0,0;
     0,0,1,0,0,0,0,0;
     0,0,0,0,1,0,0,0;
     0,0,0,0,0,1,0,0;
     0,0,0,0,0,0,1,0;
     0,0,0,0,0,0,0,1]

private def gate3Matrix : Matrix (Fin 8) (Fin 8) ℂ :=
  !![1,0,0,0,0,0,0,0;
     0,1,0,0,0,0,0,0;
     0,0,-1,0,0,0,0,0;
     0,0,0,1,0,0,0,0;
     0,0,0,0,1,0,0,0;
     0,0,0,0,0,1,0,0;
     0,0,0,0,0,0,1,0;
     0,0,0,0,0,0,0,1]

private theorem gate2_eq {μ r : ℝ} (hμ : 0<μ) (hr : |r|<1) (q : Bool) :
    labelOperation hμ hr q 2 = gate2Matrix := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [labelOperation, labelTargetMatrix, labelControl, labelTarget, labelGate,
      labelBits, Fin.forall_fin_succ, TransducerCompiler.complexifyRealUnitary,
      TransducerCompiler.RealToffoli.xReal, TransducerCompiler.RealToffoli.xEntry,
      GraphEncoding.zReal, gate2Matrix]

private theorem gate3_eq {μ r : ℝ} (hμ : 0<μ) (hr : |r|<1) (q : Bool) :
    labelOperation hμ hr q 3 = gate3Matrix := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [labelOperation, labelTargetMatrix, labelControl, labelTarget, labelGate,
      labelBits, Fin.forall_fin_succ, TransducerCompiler.complexifyRealUnitary,
      TransducerCompiler.RealToffoli.xReal, TransducerCompiler.RealToffoli.xEntry,
      GraphEncoding.zReal, gate3Matrix]


private theorem kernel_last_two {μ r : ℝ} (hμ : 0<μ) (hr : |r|<1) (q : Bool) :
    labelOperation hμ hr q 3 * labelOperation hμ hr q 2 = kernelSuffix := by
  rw [gate3_eq, gate2_eq]
  simp [gate2Matrix, gate3Matrix, kernelSuffix]


theorem kernel_four_factorization {μ r : ℝ} (hμ : 0<μ) (hr : |r|<1) (q : Bool) :
    labelOperation hμ hr q 3 * labelOperation hμ hr q 2 *
      labelOperation hμ hr q 1 * labelOperation hμ hr q 0 =
      kernelLabelMatrix (kernelMixA μ) (kernelMixB μ) q := by
  rw [kernel_last_two, Matrix.mul_assoc, kernel_first_two]
  cases q <;> simp [kernelSuffix, kernelPrefix, kernelLabelMatrix]


end OptimalQLS.Preparation.WorkGates
