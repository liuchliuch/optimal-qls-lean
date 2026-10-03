import OptimalQLS.Preparation.LabelOperations
import OptimalQLS.GraphEncoding.SmallGates

noncomputable section
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace OptimalQLS.Preparation.WorkGates
open Matrix

/-- Low-first binary coordinates of the eight preparation labels. -/
def labelBits (j : Fin 8) : Fin 3 → Bool :=
  (![![false,false,false], ![true,false,false], ![false,true,false],
    ![true,true,false], ![false,false,true], ![true,false,true],
    ![false,true,true], ![true,true,true]] j)

def labelNumber (b : Fin 3 → Bool) : Fin 8 :=
  ⟨(b 0).toNat + 2 * (b 1).toNat + 4 * (b 2).toNat, by
    have h0 := Bool.toNat_le (b 0)
    have h1 := Bool.toNat_le (b 1)
    have h2 := Bool.toNat_le (b 2)
    omega⟩

def labelEquiv : Fin 8 ≃ (Fin 3 → Bool) where
  toFun := labelBits
  invFun := labelNumber
  left_inv j := by fin_cases j <;> rfl
  right_inv b := by
    have h : b = ![b 0,b 1,b 2] := by ext k; fin_cases k <;> rfl
    rw [h]
    cases b 0 <;> cases b 1 <;> cases b 2 <;> rfl

@[simp] theorem labelBits_labelNumber (b : Fin 3 → Bool) :
    labelBits (labelNumber b) = b := labelEquiv.apply_symm_apply b

@[simp] theorem labelNumber_labelBits (j : Fin 8) :
    labelNumber (labelBits j) = j := labelEquiv.symm_apply_apply j

/-- One target bit, with a Boolean control on its spectator bits. -/
def labelTargetMatrix (control : Fin 8 → Bool) (t : Fin 3)
    (U : Matrix Bool Bool ℂ) : Matrix (Fin 8) (Fin 8) ℂ := fun i j =>
  if (∀ k : Fin 3, k ≠ t → labelBits i k = labelBits j k) then
    if control j then U (labelBits i t) (labelBits j t)
    else if i = j then 1 else 0
  else 0

theorem labelTargetMatrix_false (t : Fin 3) (U : Matrix Bool Bool ℂ) :
    labelTargetMatrix (fun _ => false) t U = 1 := by
  ext i j
  by_cases h : i=j
  · subst j
    simp [labelTargetMatrix]
  · simp [labelTargetMatrix, Matrix.one_apply, h]

/-- A real normalized reflection, including the kernel's signed rotation. -/
def reflectionReal (a b : ℝ) (hab : a*a+b*b=1) : Matrix.unitaryGroup Bool ℝ := by
  refine ⟨fun i j => if i then (if j then -a else b) else (if j then b else a), ?_⟩
  rw [Matrix.mem_unitaryGroup_iff]
  ext i j
  cases i <;> cases j <;>
    simp [Matrix.mul_apply, Matrix.star_eq_conjTranspose] <;> nlinarith

def kernelGate (μ : ℝ) (hμ : 0 < μ) : Matrix.unitaryGroup Bool ℂ :=
  TransducerCompiler.complexifyRealUnitary
    (reflectionReal (kernelMixA μ) (kernelMixB μ) (kernelMix_normalized hμ))

/-- Gates are numbered in execution order. -/
def labelControl (k : Fin 9) (q : Bool) (j : Fin 8) : Bool :=
  let b := labelBits j
  (![(!b 2 && b 0 && q), (!b 2 && q), (!b 2 && b 1),
    (!b 2 && !b 0), (!b 2 && !b 1), (!b 1 && !b 0),
    (!b 2 && !b 1), (!b 2 && !b 1), (!b 2 && !b 1)] k)

def labelTarget : Fin 9 → Fin 3 := ![1,1,0,1,0,2,0,0,0]

def labelGate {μ r : ℝ} (hμ : 0<μ) (hr : |r|<1) : Fin 9 → Matrix.unitaryGroup Bool ℂ :=
  ![kernelGate μ hμ,
    TransducerCompiler.complexifyRealUnitary GraphEncoding.zReal,
    TransducerCompiler.complexifyRealUnitary TransducerCompiler.RealToffoli.xReal,
    TransducerCompiler.complexifyRealUnitary GraphEncoding.zReal,
    TransducerCompiler.complexifyRealUnitary TransducerCompiler.RealToffoli.xReal,
    TransducerCompiler.complexifyRealUnitary TransducerCompiler.RealToffoli.xReal,
    TransducerCompiler.complexifyRealUnitary TransducerCompiler.RealToffoli.xReal,
    TransducerCompiler.complexifyRealUnitary GraphEncoding.zReal,
    TransducerCompiler.complexifyRealUnitary (GraphEncoding.mixReal r hr)]

theorem labelGate_real {μ r : ℝ} (hμ : 0<μ) (hr : |r|<1)
    (k : Fin 9) (i j : Bool) : ((labelGate hμ hr k).val i j).im = 0 := by
  fin_cases k <;> simp [labelGate, kernelGate, TransducerCompiler.complexifyRealUnitary]

def labelOperation {μ r : ℝ} (hμ : 0<μ) (hr : |r|<1) (q : Bool) (k : Fin 9) :
    Matrix (Fin 8) (Fin 8) ℂ :=
  labelTargetMatrix (labelControl k q) (labelTarget k) (labelGate hμ hr k).val

/-- Label matrices lifted with arbitrary unchanged workspace spectators. -/
def fiberMatrix {F : Type*} [DecidableEq F] (M : F → Matrix (Fin 8) (Fin 8) ℂ) :
    Matrix (Fin 8 × F) (Fin 8 × F) ℂ :=
  fun i j => if i.2=j.2 then M i.2 i.1 j.1 else 0

theorem fiberMatrix_mul {F : Type*} [Fintype F] [DecidableEq F]
    (M N : F → Matrix (Fin 8) (Fin 8) ℂ) :
    fiberMatrix M * fiberMatrix N = fiberMatrix (fun x => M x * N x) := by
  ext ⟨i,x⟩ ⟨j,y⟩
  classical
  by_cases h : x=y
  · subst y
    simp [fiberMatrix, Matrix.mul_apply, Fintype.sum_prod_type]
  · simp [fiberMatrix, Matrix.mul_apply, Fintype.sum_prod_type, h]


theorem labelNumber_update_eq (i j : Fin 8) (t : Fin 3) (y : Bool) :
    i = labelNumber (Function.update (labelBits j) t y) ↔
      (∀ k : Fin 3, k ≠ t → labelBits i k = labelBits j k) ∧ labelBits i t = y := by
  constructor
  · intro h
    have he : labelBits i = Function.update (labelBits j) t y := by
      rw [h, labelBits_labelNumber]
    constructor
    · intro k hk
      simp [he, Function.update_of_ne hk]
    · simp [he]
  · rintro ⟨ho,ht⟩
    apply labelEquiv.injective
    change labelBits i = labelBits (labelNumber _)
    rw [labelBits_labelNumber]
    funext k
    by_cases hk : k=t
    · subst k
      simpa using ht
    · simpa [Function.update_of_ne hk] using ho k hk

/-- Column form used when lowering a logical target to a physical gate macro. -/
theorem labelTargetMatrix_column (c : Fin 8 → Bool) (t : Fin 3)
    (U : Matrix Bool Bool ℂ) (i j : Fin 8) :
    labelTargetMatrix c t U i j =
      ∑ y : Bool, (if c j then U y (labelBits j t)
        else if y=labelBits j t then 1 else 0) *
        (Pi.single (labelNumber (Function.update (labelBits j) t y)) 1 : Fin 8 → ℂ) i := by
  classical
  by_cases h : ∀ k : Fin 3, k ≠ t → labelBits i k = labelBits j k
  · have hd : i=j ↔ labelBits i t=labelBits j t := by
      have he := labelNumber_update_eq i j t (labelBits j t)
      simp only [Function.update_eq_self, labelNumber_labelBits] at he
      exact he.trans (and_iff_right h)
    cases hi : labelBits i t <;> cases hj : labelBits j t <;> cases hc : c j <;>
      simp [labelTargetMatrix, h, Fintype.sum_bool, Pi.single_apply,
        labelNumber_update_eq, hd, hi, hj, hc]
  · simp [labelTargetMatrix, h, Fintype.sum_bool, Pi.single_apply, labelNumber_update_eq]

theorem labelControl_update (k : Fin 9) (q : Bool) (j : Fin 8) (y : Bool) :
    labelControl k q (labelNumber (Function.update (labelBits j) (labelTarget k) y)) =
      labelControl k q j := by
  fin_cases k <;> simp [labelControl, labelTarget]


theorem labelTargetMatrix_basis (c : Fin 8 → Bool) (t : Fin 3)
    (U : Matrix Bool Bool ℂ) (j : Fin 8) :
    labelTargetMatrix c t U *ᵥ Pi.single j 1 =
      ∑ y : Bool, (if c j then U y (labelBits j t)
        else if y=labelBits j t then 1 else 0) •
        (Pi.single (labelEquiv.symm (Function.update (labelBits j) t y)) 1 : Fin 8 → ℂ) := by
  rw [Matrix.mulVec_single_one]
  ext i
  simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using
    labelTargetMatrix_column c t U i j


def kernelBlocks8 {F : Type*} [Fintype F] [DecidableEq F]
    (Q : Matrix F F ℂ) (a b : ℝ) : Matrix (Fin 8) (Fin 8) (Matrix F F ℂ) :=
  !![1,0,0,0,0,0,0,0;
     0,a • Q + (1-Q),0,b • Q,0,0,0,0;
     0,b • Q,0,(-a) • Q - (1-Q),0,0,0,0;
     0,0,1-(2:ℝ) • Q,0,0,0,0,0;
     0,0,0,0,1,0,0,0;
     0,0,0,0,0,1,0,0;
     0,0,0,0,0,0,1,0;
     0,0,0,0,0,0,0,1]

theorem kernelBlocks8_entries {F : Type*} [Fintype F] [DecidableEq F]
    (Q : Matrix F F ℂ) (a b : ℝ) (i j : Fin 8) :
    kernelBlocks8 Q a b i j =
      if i=1 then (if j=1 then a • Q + (1-Q) else if j=3 then b • Q else 0)
      else if i=2 then (if j=1 then b • Q else if j=3 then (-a) • Q - (1-Q) else 0)
      else if i=3 then (if j=2 then 1-(2:ℝ) • Q else 0)
      else if i=j then 1 else 0 := by
  fin_cases i <;> fin_cases j <;> rfl

theorem kernelWork8_blocks {F : Type*} [Fintype F] [DecidableEq F]
    (Q : Matrix F F ℂ) (hQ : star Q=Q) (hQQ : Q*Q=Q) {μ : ℝ} (hμ : 0<μ) :
    (kernelWork8 Q hQ hQQ hμ).val =
      Matrix.compRingEquiv (Fin 8) F ℂ (kernelBlocks8 Q (kernelMixA μ) (kernelMixB μ)) := by
  ext ⟨i,x⟩ ⟨j,y⟩
  have hid {n : ℕ} (k : Fin n) :
      (1 : Matrix (Fin n × F) (Fin n × F) ℂ) (k,x) (k,y) =
        (1 : Matrix F F ℂ) x y := by
    simp [Matrix.one_apply]
  fin_cases i <;> fin_cases j <;> try rfl
  · exact hid (0 : Fin 1)
  · exact hid (0 : Fin 4)
  · exact hid (1 : Fin 4)
  · exact hid (2 : Fin 4)
  · exact hid (3 : Fin 4)

end OptimalQLS.Preparation.WorkGates
