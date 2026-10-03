import OptimalQLS.PolynomialTransform.CleanEmbedding

/-! # Transport of clean-subspace implementations through explicit wire regroupings -/
noncomputable section
namespace OptimalQLS.PolynomialTransform
open Matrix
variable {L P L' P' : Type*} [Fintype L] [DecidableEq L] [Fintype P] [DecidableEq P]
  [Fintype L'] [DecidableEq L'] [Fintype P'] [DecidableEq P']

theorem basisInsertion_transport (eP : P ≃ P') (eL : L ≃ L') (f : L → P) :
    basisInsertion (fun x => eP (f (eL.symm x)))=(basisInsertion f).submatrix eP.symm eL.symm := by
  ext i j
  simp [basisInsertion,Matrix.submatrix,Equiv.symm_apply_eq]

/-- Pure wire regrouping preserves the full coherent clean-subspace action. -/
theorem clean_intertwines_transport (eP : P ≃ P') (eL : L ≃ L') (f : L → P)
    (U : Matrix.unitaryGroup P ℂ) (V : Matrix.unitaryGroup L ℂ)
    (h : U.val*basisInsertion f=basisInsertion f*V.val) :
    (rewireUnitary eP U).val*basisInsertion (fun x => eP (f (eL.symm x)))=
      basisInsertion (fun x => eP (f (eL.symm x)))*(rewireUnitary eL V).val := by
  rw [basisInsertion_transport]
  change U.val.submatrix eP.symm eP.symm*(basisInsertion f).submatrix eP.symm eL.symm=
    (basisInsertion f).submatrix eP.symm eL.symm*V.val.submatrix eL.symm eL.symm
  rw [Matrix.submatrix_mul_equiv,Matrix.submatrix_mul_equiv,h]

end OptimalQLS.PolynomialTransform
