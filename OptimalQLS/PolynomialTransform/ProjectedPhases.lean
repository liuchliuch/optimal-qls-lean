import OptimalQLS.PolynomialTransform.QuadraticCircuit

/-! # Explicit phase unitaries about an isometric signal subspace -/
noncomputable section
namespace OptimalQLS.PolynomialTransform
open Matrix
open scoped ComplexConjugate

variable {W D : Type*} [Fintype W] [DecidableEq W] [Fintype D] [DecidableEq D]

/-- The actual orthogonal signal projector. -/
def insertionProjector (E : Matrix W D ℂ) : Matrix W W ℂ := E * Eᴴ

@[simp] theorem insertionProjector_star (E : Matrix W D ℂ) :
    (insertionProjector E)ᴴ = insertionProjector E := by simp [insertionProjector]

theorem insertionProjector_sq (E : Matrix W D ℂ) (hE : Eᴴ*E=1) :
    insertionProjector E * insertionProjector E = insertionProjector E := by
  unfold insertionProjector
  calc
    E*Eᴴ*(E*Eᴴ) = E*(Eᴴ*E)*Eᴴ := by simp only [Matrix.mul_assoc]
    _ = E*Eᴴ := by rw [hE, Matrix.mul_one]

theorem insertionProjector_mul_insertion (E : Matrix W D ℂ) (hE : Eᴴ*E=1) :
    insertionProjector E * E = E := by
  rw [insertionProjector, Matrix.mul_assoc, hE, Matrix.mul_one]

/-- Two independent unit-circle phases on the signal and its complement. -/
def insertionPhases (E : Matrix W D ℂ) (hE : Eᴴ*E=1) (z w : Circle) :
    Matrix.unitaryGroup W ℂ := by
  let P := insertionProjector E
  let R := 1-P
  have hPP : P*P=P := insertionProjector_sq E hE
  have hRR : R*R=R := by dsimp only [R]; noncomm_ring [hPP]
  have hPR : P*R=0 := by dsimp only [R]; rw [mul_sub,mul_one,hPP,sub_self]
  have hRP : R*P=0 := by dsimp only [R]; rw [sub_mul,one_mul,hPP,sub_self]
  have hPs : Pᴴ=P := insertionProjector_star E
  have hRs : Rᴴ=R := by simp [R,hPs]
  refine ⟨(z : ℂ) • P+(w : ℂ) • R,?_⟩
  rw [Matrix.mem_unitaryGroup_iff,Matrix.star_eq_conjTranspose]
  have hstar : ((z : ℂ) • P+(w : ℂ) • R)ᴴ = star (z : ℂ) • P+star (w : ℂ) • R := by
    simp [hPs,hRs]
  rw [hstar]
  calc
    ((z : ℂ) • P+(w : ℂ) • R)*(star (z : ℂ) • P+star (w : ℂ) • R) =
        ((z : ℂ)*star (z : ℂ)) • P+((w : ℂ)*star (w : ℂ)) • R := by
      simp only [Matrix.add_mul,Matrix.mul_add,Matrix.smul_mul,Matrix.mul_smul,
        hPP,hPR,hRP,hRR,smul_zero,add_zero,zero_add,smul_smul]
      congr 1 <;> congr 1 <;> ring
    _ = P+R := by simp [RCLike.star_def,Complex.mul_conj]
    _ = 1 := by dsimp only [R]; abel

/-- Actual action of the phase unitary on all initialized signal columns. -/
theorem insertionPhases_mul_E (E : Matrix W D ℂ) (hE : Eᴴ*E=1) (z w : Circle) :
    (insertionPhases E hE z w : Matrix W W ℂ)*E = (z : ℂ) • E := by
  change ((z : ℂ) • insertionProjector E+(w : ℂ) • (1-insertionProjector E))*E = _
  simp only [Matrix.add_mul,Matrix.smul_mul,Matrix.sub_mul,Matrix.one_mul,
    insertionProjector_mul_insertion E hE,sub_self,smul_zero,add_zero]

/-- Actual action on any columns orthogonal to the initialized signal. -/
theorem insertionPhases_mul_orthogonal (E F : Matrix W D ℂ) (hE : Eᴴ*E=1)
    (hF : Eᴴ*F=0) (z w : Circle) :
    (insertionPhases E hE z w : Matrix W W ℂ)*F = (w : ℂ) • F := by
  have hPF : insertionProjector E*F=0 := by rw [insertionProjector,Matrix.mul_assoc,hF,Matrix.mul_zero]
  change ((z : ℂ) • insertionProjector E+(w : ℂ) • (1-insertionProjector E))*F = _
  simp only [Matrix.add_mul,Matrix.smul_mul,Matrix.sub_mul,Matrix.one_mul,
    hPF,sub_zero,smul_zero,zero_add]

/-- The literal unit-circle value i. -/
def circleI : Circle := ⟨Complex.I, by simp [Submonoid.unitSphere,Metric.mem_sphere,dist_zero_right]⟩

/-- Signal-basis phase D=Π+i(I-Π), turning a reflection into W(x). -/
def signalBasisPhase (E : Matrix W D ℂ) (hE : Eᴴ*E=1) : Matrix.unitaryGroup W ℂ :=
  insertionPhases E hE 1 circleI

/-- Reciprocal signal phase diag(z,z^-1) on the two-dimensional invariant pair. -/
def reciprocalSignalPhase (E : Matrix W D ℂ) (hE : Eᴴ*E=1) (z : Circle) :
    Matrix.unitaryGroup W ℂ := insertionPhases E hE z z⁻¹

/-- A genuine Hermitian unitary oracle yields the concrete signal rotation. -/
def hermitianSignal (E : Matrix W D ℂ) (hE : Eᴴ*E=1) (U : Matrix.unitaryGroup W ℂ) :
    Matrix.unitaryGroup W ℂ := signalBasisPhase E hE * U * signalBasisPhase E hE

end OptimalQLS.PolynomialTransform
