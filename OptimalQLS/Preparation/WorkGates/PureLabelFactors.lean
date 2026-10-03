import OptimalQLS.Preparation.WorkGates.Foundations

noncomputable section
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace OptimalQLS.Preparation.WorkGates
open Matrix
private def swapPrefix : Matrix (Fin 8) (Fin 8) ℂ :=
  !![0,0,0,0,1,0,0,0;
     1,0,0,0,0,0,0,0;
     0,0,1,0,0,0,0,0;
     0,0,0,1,0,0,0,0;
     0,1,0,0,0,0,0,0;
     0,0,0,0,0,1,0,0;
     0,0,0,0,0,0,1,0;
     0,0,0,0,0,0,0,1]

def swapLabelMatrix : Matrix (Fin 8) (Fin 8) ℂ :=
  !![1,0,0,0,0,0,0,0;
     0,0,0,0,1,0,0,0;
     0,0,1,0,0,0,0,0;
     0,0,0,1,0,0,0,0;
     0,1,0,0,0,0,0,0;
     0,0,0,0,0,1,0,0;
     0,0,0,0,0,0,1,0;
     0,0,0,0,0,0,0,1]

private def gate4Matrix : Matrix (Fin 8) (Fin 8) ℂ :=
  !![0,1,0,0,0,0,0,0;
     1,0,0,0,0,0,0,0;
     0,0,1,0,0,0,0,0;
     0,0,0,1,0,0,0,0;
     0,0,0,0,1,0,0,0;
     0,0,0,0,0,1,0,0;
     0,0,0,0,0,0,1,0;
     0,0,0,0,0,0,0,1]

private def gate5Matrix : Matrix (Fin 8) (Fin 8) ℂ :=
  !![0,0,0,0,1,0,0,0;
     0,1,0,0,0,0,0,0;
     0,0,1,0,0,0,0,0;
     0,0,0,1,0,0,0,0;
     1,0,0,0,0,0,0,0;
     0,0,0,0,0,1,0,0;
     0,0,0,0,0,0,1,0;
     0,0,0,0,0,0,0,1]

private theorem gate4_eq {μ r : ℝ} (hμ : 0<μ) (hr : |r|<1) (q : Bool) :
    labelOperation hμ hr q 4 = gate4Matrix := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [labelOperation, labelTargetMatrix, labelControl, labelTarget, labelGate,
      labelBits, Fin.forall_fin_succ, TransducerCompiler.complexifyRealUnitary,
      TransducerCompiler.RealToffoli.xReal, TransducerCompiler.RealToffoli.xEntry,
      GraphEncoding.zReal, gate4Matrix]

private theorem gate5_eq {μ r : ℝ} (hμ : 0<μ) (hr : |r|<1) (q : Bool) :
    labelOperation hμ hr q 5 = gate5Matrix := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [labelOperation, labelTargetMatrix, labelControl, labelTarget, labelGate,
      labelBits, Fin.forall_fin_succ, TransducerCompiler.complexifyRealUnitary,
      TransducerCompiler.RealToffoli.xReal, TransducerCompiler.RealToffoli.xEntry,
      GraphEncoding.zReal, gate5Matrix]

private theorem gate6_eq {μ r : ℝ} (hμ : 0<μ) (hr : |r|<1) (q : Bool) :
    labelOperation hμ hr q 6 = gate4Matrix := by
  exact gate4_eq hμ hr q


private theorem swap_first_two {μ r : ℝ} (hμ : 0<μ) (hr : |r|<1) (q : Bool) :
    labelOperation hμ hr q 5 * labelOperation hμ hr q 4 = swapPrefix := by
  rw [gate5_eq, gate4_eq]
  simp [gate4Matrix, gate5Matrix, swapPrefix]


theorem swap_three_factorization {μ r : ℝ} (hμ : 0<μ) (hr : |r|<1) (q : Bool) :
    labelOperation hμ hr q 6 * labelOperation hμ hr q 5 *
      labelOperation hμ hr q 4 = swapLabelMatrix := by
  rw [Matrix.mul_assoc, swap_first_two]
  rw [gate6_eq]
  simp [gate4Matrix, swapPrefix, swapLabelMatrix]

variable {F : Type*} [Fintype F] [DecidableEq F]


theorem swap14_fiber : (swap14 (F := F)).val =
    fiberMatrix (fun _ : F => swapLabelMatrix) := by
  ext ⟨i,x⟩ ⟨j,y⟩
  fin_cases i <;> fin_cases j <;>
    simp [swap14, TransducerCompiler.permutation, PEquiv.toMatrix,
      Equiv.swap_apply_def, fiberMatrix, swapLabelMatrix]


theorem sign1_fiber {μ r : ℝ} (hμ : 0<μ) (hr : |r|<1) (q : F → Bool) :
    (sign1 (F := F)).val = fiberMatrix (fun x => labelOperation hμ hr (q x) 7) := by
  ext ⟨i,x⟩ ⟨j,y⟩
  fin_cases i <;> fin_cases j <;>
    simp [sign1, Matrix.diagonal_apply, fiberMatrix, labelOperation,
      labelTargetMatrix, labelControl, labelTarget, labelGate, labelBits,
      Fin.forall_fin_succ, TransducerCompiler.complexifyRealUnitary,
      GraphEncoding.zReal]


theorem mix8_fiber {μ r : ℝ} (hμ : 0<μ) (hr : |r|<1) (q : F → Bool) :
    (mix8 (F := F) hr).val = fiberMatrix (fun x => labelOperation hμ hr (q x) 8) := by
  ext ⟨i,x⟩ ⟨j,y⟩
  fin_cases i <;> fin_cases j <;>
    simp [mix8, labelSumUnitary, mixFirstTwo, rewireUnitary, directSumUnitary,
      labelSumEquiv, finSumFinEquiv, Fin.addCases, twoLabelEquiv, fractionalMix,
      Matrix.one_apply, Matrix.smul_apply, Complex.real_smul,
      fiberMatrix, labelOperation, labelTargetMatrix, labelControl, labelTarget,
      labelGate, labelBits, Fin.forall_fin_succ,
      TransducerCompiler.complexifyRealUnitary, GraphEncoding.mixReal,
      GraphEncoding.mixRealEntry] <;>
    split_ifs <;> simp_all


end OptimalQLS.Preparation.WorkGates
