import OptimalQLS.TransducerCompiler.Physical.QueryFrames

/-! Actual compute-flag/oracle/uncompute words for the two compiler labels. -/
noncomputable section
set_option synthInstance.maxSize 16384
set_option maxHeartbeats 700000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
open scoped Classical
namespace OptimalQLS.TransducerCompiler.Physical
open Matrix BinaryClock PolynomialTransform DirtyAncilla
open Preparation.CompilerAttachment

def localCode (m : ℕ) (l : Label) (second : Bool) :
    ElementaryCircuit (Bits m) (Bits m) OracleLocalWire (Bits m) :=
  if second then swapElementary (localOracleCode (labelBitsEquiv l) false)
  else localOracleCode (labelBitsEquiv l) false

theorem localCode_counts (m : ℕ) (l : Label) (second : Bool) :
    (localCode m l second).toQuery.matrixQueries=(if second then 0 else 1) ∧
    (localCode m l second).toQuery.vectorQueries=(if second then 1 else 0) ∧
    (localCode m l second).workGates≤2400 := by
  have hc := localOracleCode_counts (A := Bits m) (B := Bits m) (labelBitsEquiv l) false
  cases second with
  | false => exact hc
  | true =>
    simp only [localCode,ite_true,swapElementary_toQuery,swapElementary_workGates]
    have hs := QueryCircuit.swapOracles_counts
      (localOracleCode (A := Bits m) (B := Bits m) (labelBitsEquiv l) false).toQuery
    exact ⟨hs.1.trans hc.2.1,hs.2.trans hc.1,hc.2.2⟩

theorem localCode_intertwines (m : ℕ) (l : Label) (second : Bool)
    (U₁ U₂ : Matrix.unitaryGroup (Bits m) ℂ) :
    ((localCode m l second).toQuery.eval U₁ U₂).val*basisInsertion oracleLocalClean=
      basisInsertion oracleLocalClean*
        ((GraphEncoding.maskedGraphPort (Bits m) (labelBitsEquiv l)).apply
          (if second then U₂ else U₁)).val := by
  cases second with
  | false => exact localOracleCode_intertwines (labelBitsEquiv l) false U₁ U₂
  | true =>
    simp only [localCode,ite_true,swapElementary_toQuery,QueryCircuit.swapOracles_eval]
    exact localOracleCode_intertwines (labelBitsEquiv l) false U₂ U₁

def queryGateEval (m ℓ : ℕ) (g : PhaseGate OracleLocalWire) : Matrix.unitaryGroup (Space m ℓ) ℂ :=
  GateSynthesis.placeHom (queryFrame m ℓ) (elementaryPlacement g.eval)

def queryCode (m ℓ : ℕ) (l : Label) (second : Bool) :
    NamedCircuit (PhaseGate OracleLocalWire) (Bits m) (Bits m) (Space m ℓ) :=
  attachList (queryFrame m ℓ) id (localCode m l second)

theorem queryCode_counts (m ℓ : ℕ) (l : Label) (second : Bool) :
    ((queryCode m ℓ l second).toQuery (queryGateEval m ℓ)).matrixQueries=(if second then 0 else 1) ∧
    ((queryCode m ℓ l second).toQuery (queryGateEval m ℓ)).vectorQueries=(if second then 1 else 0) ∧
    (queryCode m ℓ l second).workGates≤2400 := by
  rw [queryCode,attachList_toQuery (queryFrame m ℓ) id (queryGateEval m ℓ) (fun _=>rfl),
    attachList_workGates]
  have hl := QueryCircuit.lift_counts (scratchPort (queryFrame m ℓ)) (localCode m l second).toQuery
  have hc := localCode_counts m l second
  exact ⟨hl.1.trans hc.1,hl.2.trans hc.2.1,hc.2.2⟩

theorem queryCode_intertwines (m ℓ : ℕ) (l : Label) (second : Bool)
    (U₁ U₂ : Matrix.unitaryGroup (Bits m) ℂ) :
    (((queryCode m ℓ l second).toQuery (queryGateEval m ℓ)).eval U₁ U₂).val*
        basisInsertion (clean m ℓ)=basisInsertion (clean m ℓ)*
      (padHom (dataQuery (a := Bits ℓ × Bits ℓ) l (if second then U₂ else U₁))).val := by
  rw [queryCode,attachList_eval (queryFrame m ℓ) id (queryGateEval m ℓ) (fun _=>rfl)]
  have ht := tensor_intertwines (D := QueryRest ℓ) oracleLocalClean _ _
    (localCode_intertwines m l second U₁ U₂)
  have hh := clean_intertwines_transport (queryFrame m ℓ) (labelFrame m ℓ)
    (fun x=> (oracleLocalClean x.1,x.2)) _ _ ht
  have hc : (fun x=>queryFrame m ℓ
      (oracleLocalClean ((labelFrame m ℓ).symm x).1,((labelFrame m ℓ).symm x).2))=clean m ℓ := by
    funext x
    rw [queryFrame_clean,Equiv.apply_symm_apply]
  rw [hc] at hh
  change (GateSynthesis.placeHom (queryFrame m ℓ) ((localCode m l second).toQuery.eval U₁ U₂)).val*
      basisInsertion (clean m ℓ)=basisInsertion (clean m ℓ)*
      (GateSynthesis.placeHom (labelFrame m ℓ)
        ((GraphEncoding.maskedGraphPort (Bits m) (labelBitsEquiv l)).apply (if second then U₂ else U₁))).val at hh
  rw [label_query_eq] at hh
  exact hh

end OptimalQLS.TransducerCompiler.Physical
