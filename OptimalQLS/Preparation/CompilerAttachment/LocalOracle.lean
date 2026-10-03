import OptimalQLS.PolynomialTransform.SingleFlagEncoding
import OptimalQLS.Preparation.CompilerAttachment.LocalAttach

/-! # Full-column local oracle adapters for both original oracle roles -/
noncomputable section
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace OptimalQLS.Preparation.CompilerAttachment
open Matrix TransducerCompiler PolynomialTransform DirtyAncilla
variable {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

def localOracleCode (mask : Bool × Bool) (adj : Bool) :
    ElementaryCircuit A B OracleLocalWire A :=
  GraphEncoding.maskedOracleCircuit 2 id Function.injective_id ![mask.1,mask.2] adj

theorem localOracleCode_counts (mask : Bool × Bool) (adj : Bool) :
    (localOracleCode (A := A) (B := B) mask adj).toQuery.matrixQueries=1 ∧
      (localOracleCode (A := A) (B := B) mask adj).toQuery.vectorQueries=0 ∧
      (localOracleCode (A := A) (B := B) mask adj).workGates ≤ 2400 :=
  GraphEncoding.maskedOracleCircuit_counts 2 id Function.injective_id ![mask.1,mask.2] adj

theorem localOracle_basisInsertion_col {X Y : Type*} [DecidableEq Y]
    (f : X → Y) (x : X) : (basisInsertion f).col x = (Pi.single (f x) 1 : Y → ℂ) := by
  ext y
  simp [basisInsertion,Matrix.col_apply,Pi.single_apply]

theorem localOracleCode_intertwines (mask : Bool × Bool) (adj : Bool)
    (U : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) :
    ((localOracleCode mask adj).toQuery.eval U Ub).val*basisInsertion oracleLocalClean =
      basisInsertion oracleLocalClean *
        ((GraphEncoding.maskedGraphPort A mask).apply (if adj then U⁻¹ else U)).val := by
  apply basisInsertion_intertwines
  intro j
  rcases j with ⟨m,i⟩
  have he (V : Matrix.unitaryGroup A ℂ) :
      V.val *ᵥ Pi.single i 1 = ∑ k, V.val k i • (Pi.single k 1 : A → ℂ) := by
    ext k
    simp [Matrix.mulVec_single_one,Pi.single_apply]
  rw [GraphEncoding.maskedGraphPort_basis_expansion mask m _ _ _ _ (he _)]
  have hclean (i : A) : oracleLocalClean (m,i) =
      ((false,fun k : SmallWire 2 => match k with
        | .inl k => if k=0 then m.1 else m.2 | .inr _ => false),i) := by
    simp [oracleLocalClean,oracleLocalWiring]
    funext k
    cases k <;> rfl
  rw [hclean i]
  change ((GraphEncoding.maskedOracleCircuit (A := A) (B := B)
    2 id Function.injective_id ![mask.1,mask.2] adj).toQuery.eval U Ub).val *ᵥ
      Pi.single ((false,fun k : SmallWire 2 => match k with
        | .inl k => if k=0 then m.1 else m.2 | .inr _ => false),i) 1 = _
  rw [GraphEncoding.maskedOracleCircuit_basis _ _ _ _ _ _ (by rfl)]
  by_cases hm : m=mask
  · subst m
    simp [Fin.forall_fin_succ,Matrix.mulVec_sum,Matrix.mulVec_smul,basisInsertion_basis,
      localOracle_basisInsertion_col,hclean]
  · have hn : ¬(m.1=mask.1 ∧ m.2=mask.2) := fun h => hm (Prod.ext h.1 h.2)
    simp [Fin.forall_fin_succ,hm,hn,basisInsertion_basis,localOracle_basisInsertion_col,hclean]


end OptimalQLS.Preparation.CompilerAttachment
