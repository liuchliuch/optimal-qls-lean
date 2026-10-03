import OptimalQLS.Refinement.Repetition.Measurement
import OptimalQLS.TransducerCompiler.Basic

/-! Explicit single-bit projective measurements for the fixed-auxiliary
acceptance pattern. Measurement/reset operations are counted separately from
unitary gates; the accepted data register is never measured. -/
noncomputable section
open scoped BigOperators
namespace OptimalQLS.Refinement.Repetition.Physical
open Matrix
set_option maxHeartbeats 200000
variable {I : Type*} [Fintype I] [DecidableEq I]
abbrev Bits (I : Type*) := I → Bool

def bitProjector (k : I) (b : Bool) : Matrix (Bits I) (Bits I) ℂ :=
  diagonal (fun s => if s k = b then 1 else 0)

def patternMeasurement (wires : List I) (pattern : Bits I) : Matrix (Bits I) (Bits I) ℂ :=
  (wires.map (fun k => bitProjector k (pattern k))).prod

theorem patternMeasurement_diagonal (wires : List I) (pattern : Bits I) :
    patternMeasurement wires pattern =
      diagonal (fun s => if ∀ k ∈ wires, s k = pattern k then 1 else 0) := by
  induction wires with
  | nil => simp [patternMeasurement]
  | cons k wires ih =>
    change bitProjector k (pattern k) * patternMeasurement wires pattern = _
    rw [ih, bitProjector, diagonal_mul_diagonal]
    congr 1
    ext s
    simp only [List.mem_cons, forall_eq_or_imp]
    split_ifs <;> simp_all

theorem bitProjector_complete (k : I) :
    (bitProjector k false).conjTranspose * bitProjector k false +
      (bitProjector k true).conjTranspose * bitProjector k true = 1 := by
  ext s t
  by_cases h : s = t
  · subst t
    cases hs : s k <;>
      simp [bitProjector, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.diagonal, hs]
  · simp [bitProjector, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.diagonal, h, Ne.symm h]

theorem fullMeasurement (pattern : Bits I) :
    patternMeasurement Finset.univ.toList pattern =
      diagonal (fun s => if s = pattern then 1 else 0) := by
  rw [patternMeasurement_diagonal]
  congr 1
  ext s
  simp [funext_iff]

/-- Exact number of single-qubit measurements. -/
theorem patternMeasurement_length (wires : List I) (pattern : Bits I) :
    (wires.map (fun k => bitProjector k (pattern k))).length = wires.length := by simp

/-- A conditional X on a classically measured bit maps it to the requested
basis value. The other coordinates are unchanged. -/
def resetBit (target : Bits I) (k : I) (s : Bits I) : Bits I :=
  Function.update s k (target k)

def resetWord (target : Bits I) (wires : List I) (s : Bits I) : Bits I :=
  wires.foldr (resetBit target) s

theorem resetWord_apply (target s : Bits I) (wires : List I) (k : I) :
    resetWord target wires s k = if k ∈ wires then target k else s k := by
  induction wires with
  | nil => simp [resetWord]
  | cons j wires ih =>
    change Function.update (resetWord target wires s) j (target j) k = _
    by_cases h : k = j
    · subst j; simp
    · simp only [Function.update_apply, h, if_false, List.mem_cons]
      rw [ih]
      simp [h]

theorem resetWord_full (target s : Bits I) :
    resetWord target Finset.univ.toList s = target := by
  ext k
  simp [resetWord_apply]

def bitFlip (k : I) (s : Bits I) : Bits I := Function.update s k (!(s k))

theorem resetBit_is_identity_or_X (target s : Bits I) (k : I) :
    resetBit target k s = if s k = target k then s else bitFlip k s := by
  by_cases h : s k = target k
  · rw [if_pos h]
    unfold resetBit
    rw [← h]
    simp
  · have hb : (!(s k)) = target k := by
      cases hs : s k <;> cases ht : target k <;> simp_all
    simp [resetBit, bitFlip, h, hb]

def bitFlipEquiv (k : I) : Equiv.Perm (Bits I) where
  toFun := bitFlip k
  invFun := bitFlip k
  left_inv s := by ext j; by_cases h : j = k <;> simp [bitFlip, Function.update_apply, h]
  right_inv s := by ext j; by_cases h : j = k <;> simp [bitFlip, Function.update_apply, h]

def ket (s : Bits I) : Bits I → ℂ := fun j => if j = s then 1 else 0

def feedbackGate (target s : Bits I) (k : I) : Matrix.unitaryGroup (Bits I) ℂ :=
  if s k = target k then 1 else TransducerCompiler.permutation (bitFlipEquiv k)

theorem feedbackGate_basis (target s : Bits I) (k : I) :
    (feedbackGate target s k).val *ᵥ ket s = ket (resetBit target k s) := by
  rw [resetBit_is_identity_or_X]
  by_cases h : s k = target k
  · simp [feedbackGate, h]
  · simp only [feedbackGate, h, ite_false, TransducerCompiler.permutation_apply]
    ext j
    have he : bitFlip k j = s ↔ j = bitFlip k s :=
      (bitFlipEquiv k).apply_eq_iff_eq_symm_apply
    simp [ket, Function.comp_apply, bitFlipEquiv, he]

def feedbackMatrix (target : Bits I) : List I → Bits I → Matrix (Bits I) (Bits I) ℂ
  | [], _ => 1
  | k :: wires, s => (feedbackGate target (resetWord target wires s) k).val *
      feedbackMatrix target wires s

theorem feedbackMatrix_basis (target s : Bits I) (wires : List I) :
    feedbackMatrix target wires s *ᵥ ket s = ket (resetWord target wires s) := by
  induction wires with
  | nil => simp [feedbackMatrix, resetWord]
  | cons k wires ih =>
    rw [feedbackMatrix, ← Matrix.mulVec_mulVec, ih, feedbackGate_basis]
    rfl

theorem fullMeasurement_branch (observed : Bits I) (v : Bits I → ℂ) :
    patternMeasurement Finset.univ.toList observed *ᵥ v = v observed • ket observed := by
  rw [fullMeasurement]
  ext j
  by_cases h : j = observed
  · subst j; simp [Matrix.mulVec_diagonal, ket]
  · simp [Matrix.mulVec_diagonal, ket, h]

/-- The literal product of single-bit measurements followed by at most one
classically selected single-bit X per wire has exactly the reset Kraus action. -/
theorem physical_reset_branch (target observed : Bits I) (v : Bits I → ℂ) :
    (feedbackMatrix target Finset.univ.toList observed *
      patternMeasurement Finset.univ.toList observed) *ᵥ v =
      v observed • ket target := by
  rw [← Matrix.mulVec_mulVec, fullMeasurement_branch, Matrix.mulVec_smul,
    feedbackMatrix_basis, resetWord_full]

/-- The reset implementation has one measured bit and at most one classically
controlled X per physical wire, and introduces no quantum wires. -/
theorem full_reset_operation_bounds :
    (Finset.univ.toList : List I).length = Fintype.card I ∧
      (Finset.univ.toList : List I).length ≤ Fintype.card I := by
  simp

/-- Fixed auxiliary bits and unrestricted data bits: this is the literal
accepting subspace used by the joint QLSA circuit. -/
def fixedAuxEmbedding {Aux Data : Type*} (a : Aux) : Data ↪ Aux × Data :=
  ⟨fun d => (a, d), fun _ _ h => congrArg Prod.snd h⟩

theorem fixedAux_range {Aux Data : Type*} (a : Aux) (s : Aux × Data) :
    (∃ d, fixedAuxEmbedding a d = s) ↔ s.1 = a := by
  constructor
  · rintro ⟨d, rfl⟩; rfl
  · intro h; exact ⟨s.2, by cases s; simp_all [fixedAuxEmbedding]⟩


section AuxiliaryPattern
variable {Aux Data : Type*} [Fintype Aux] [DecidableEq Aux]
  [Fintype Data] [DecidableEq Data]

def auxEmbedding (a : Bits Aux) : Bits Data ↪ Bits (Aux ⊕ Data) where
  toFun d := Sum.elim a d
  inj' := by intro d e h; funext j; exact congrFun h (.inr j)

theorem auxEmbedding_range (a : Bits Aux) (s : Bits (Aux ⊕ Data)) :
    (∃ d, auxEmbedding a d = s) ↔ ∀ i, s (.inl i) = a i := by
  constructor
  · rintro ⟨d, rfl⟩; intro i; rfl
  · intro h
    refine ⟨fun j => s (.inr j), ?_⟩
    funext k
    cases k with
    | inl i => exact (h i).symm
    | inr j => rfl

def auxWires : List (Aux ⊕ Data) := (Finset.univ.toList : List Aux).map Sum.inl

def auxMeasurement (a : Bits Aux) : Matrix (Bits (Aux ⊕ Data)) (Bits (Aux ⊕ Data)) ℂ :=
  patternMeasurement auxWires (Sum.elim a (fun _ => false))

theorem auxMeasurement_exact (a : Bits Aux) :
    auxMeasurement (Data := Data) a =
      diagonal (fun s => if ∃ d, auxEmbedding a d = s then 1 else 0) := by
  rw [auxMeasurement, patternMeasurement_diagonal]
  congr 1
  funext s
  simp only [auxEmbedding_range]
  simp [auxWires]


/-- Conditioning on the accepted auxiliary word does not measure or dephase
any data bit. -/
def auxAccept (a : Bits Aux) : Matrix (Bits Data) (Bits (Aux ⊕ Data)) ℂ :=
  fun d s => if auxEmbedding a d = s then 1 else 0

theorem auxAccept_mulVec (a : Bits Aux) (v : Bits (Aux ⊕ Data) → ℂ) :
    auxAccept a *ᵥ v = fun d => v (auxEmbedding a d) := by
  ext d
  simp [auxAccept, Matrix.mulVec, dotProduct]

theorem physical_accept_branch (a : Bits Aux) (v : Bits (Aux ⊕ Data) → ℂ) :
    (auxAccept a * auxMeasurement a) *ᵥ v = fun d => v (auxEmbedding a d) := by
  rw [← Matrix.mulVec_mulVec, auxAccept_mulVec, auxMeasurement_exact]
  ext d
  simp [Matrix.mulVec_diagonal]

/-- For a rejected auxiliary outcome, full basis measurement and classical
X feedback reset the same register. The condition records the actual measured
auxiliary word, rather than an independence or channel-correctness premise. -/
theorem physical_reset_after_aux (target observed : Bits (Aux ⊕ Data))
    (a : Bits Aux) (v : Bits (Aux ⊕ Data) → ℂ) :
    (feedbackMatrix target Finset.univ.toList observed *
      patternMeasurement Finset.univ.toList observed) *ᵥ (auxMeasurement a *ᵥ v) =
      (if ∀ i, observed (.inl i) = a i then v observed else 0) • ket target := by
  rw [physical_reset_branch, auxMeasurement_exact]
  congr 1
  simp [Matrix.mulVec_diagonal, auxEmbedding_range]

theorem auxMeasurement_count : (auxWires (Aux := Aux) (Data := Data)).length = Fintype.card Aux := by
  simp [auxWires]

/-- This is the actual per-run measurement/reset work list: measure auxiliary
bits; on rejection measure every bit, then perform at most one conditional X
per bit. All three lists use existing wires only. -/
def physicalOperationList : List (Aux ⊕ Data) :=
  auxWires ++ Finset.univ.toList ++ Finset.univ.toList

theorem physicalOperationList_length :
    (physicalOperationList (Aux := Aux) (Data := Data)).length =
      Fintype.card Aux + 2 * (Fintype.card Aux + Fintype.card Data) := by
  simp [physicalOperationList, auxWires, Fintype.card_sum]
  omega


/-- A worst-case list for all attempted runs, including the terminal failure
conversion. This deliberately overcounts the earlier-success branches. -/
def repeatedOperationList (attempts : ℕ) : List (Aux ⊕ Data) :=
  (List.replicate attempts (physicalOperationList (Aux := Aux) (Data := Data))).flatten ++
    Finset.univ.toList ++ Finset.univ.toList

theorem repeatedOperationList_length (attempts : ℕ) :
    (repeatedOperationList (Aux := Aux) (Data := Data) attempts).length =
      attempts * (Fintype.card Aux + 2 * (Fintype.card Aux + Fintype.card Data)) +
        2 * (Fintype.card Aux + Fintype.card Data) := by
  simp [repeatedOperationList, List.length_flatten, physicalOperationList_length,
    Fintype.card_sum]
  omega

end AuxiliaryPattern

end OptimalQLS.Refinement.Repetition.Physical
