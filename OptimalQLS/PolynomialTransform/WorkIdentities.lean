import OptimalQLS.PolynomialTransform.PhysicalLabels

/-! # Identifying every QSVT work matrix with its physical local implementation -/
noncomputable section
namespace OptimalQLS.PolynomialTransform
open Matrix DirtyAncilla OptimalQLS.TransducerCompiler
variable {S D : Type*} [Fintype S] [DecidableEq S] [Fintype D] [DecidableEq D]

theorem insertionProjector_signal (s₀ : S) :
    insertionProjector (signalInjection (D := D) s₀)=
      Matrix.diagonal (fun x : S × D => if x.1=s₀ then (1 : ℂ) else 0) := by
  ext ⟨s,i⟩ ⟨t,j⟩
  simp [insertionProjector,signalInjection,Matrix.mul_apply,Matrix.conjTranspose_apply,
    Matrix.diagonal,ite_and]
  by_cases hs : s=s₀ <;> by_cases ht : t=s₀ <;> by_cases hij : i=j <;> simp_all [eq_comm]

theorem insertionPhases_signal (s₀ : S) (z w : Circle) :
    insertionPhases (signalInjection (D := D) s₀) (signalInjection_isometry s₀) z w=
      diagonalPhase (fun x : S × D => if x.1=s₀ then z else w) := by
  apply Subtype.ext
  change (z : ℂ) • insertionProjector (signalInjection s₀)+(w : ℂ) •
    (1-insertionProjector (signalInjection s₀))=_
  rw [insertionProjector_signal]
  ext i j
  by_cases hij : i=j
  · subst j; by_cases hi : i.1=s₀ <;> simp [diagonalPhase,hi]
  · simp [diagonalPhase,Matrix.diagonal,Matrix.one_apply,hij]

theorem insertionPhases_duplicate (E : Matrix (S × D) D ℂ) (hE : Eᴴ*E=1) (z w : Circle) :
    insertionPhases (duplicateInsertion E) (duplicateInsertion_isometry E hE) z w=
      sumUnitary (insertionPhases E hE z w) (insertionPhases E hE z w) := by
  apply Subtype.ext
  change (z : ℂ) • insertionProjector (duplicateInsertion E)+(w : ℂ) •
    (1-insertionProjector (duplicateInsertion E))=_
  simp only [insertionProjector,duplicateInsertion,Matrix.fromBlocks_conjTranspose,
    Matrix.fromBlocks_multiply,Matrix.mul_zero,Matrix.zero_mul,zero_add,add_zero]
  ext i j
  cases i <;> cases j <;>
    simp [sumUnitary,insertionPhases,insertionProjector,Matrix.one_apply]

/-- The direct-sum controlled phases are exactly the literal zero-signal phases. -/
theorem relabel_controlled_phase (a : ℕ) (branch : Bool) (z w : Circle) :
    rewireUnitary (twoLabelSignalEquiv (Fin a → Bool) D)
      (if branch then
        sumUnitary 1 (insertionPhases (duplicateInsertion (signalInjection (D := D) (fun _ : Fin a => false)))
          (duplicateInsertion_isometry _ (signalInjection_isometry _)) z w)
      else
        sumUnitary (insertionPhases (duplicateInsertion (signalInjection (D := D) (fun _ : Fin a => false)))
          (duplicateInsertion_isometry _ (signalInjection_isometry _)) z w) 1)=
      logicalPhase (D := D) a branch z w := by
  have hd := insertionPhases_duplicate (signalInjection (D := D) (fun _ : Fin a => false))
    (signalInjection_isometry _) z w
  rw [hd,insertionPhases_signal]
  apply Subtype.ext
  ext ⟨⟨⟨b,c⟩,x⟩,i⟩ ⟨⟨⟨d,e⟩,y⟩,j⟩
  cases branch <;> cases b <;> cases c <;> cases d <;> cases e <;>
    simp [rewireUnitary,twoLabelSignalEquiv,sumUnitary,logicalPhase,logicalPhaseFunction,
      diagonalPhase,Matrix.one_apply,Matrix.diagonal_apply,Prod.mk.injEq]

/-- The two-qubit label matrix can be inspected directly without any spectator permutation. -/
theorem logicalLabels_entry (a : ℕ) (U : Matrix.unitaryGroup (Bool × Bool) ℂ)
    (b c : Bool × Bool) (x y : Fin a → Bool) (i j : D) :
    (logicalLabels (D := D) a U).val ((b,x),i) ((c,y),j)=
      if (x,i)=(y,j) then U.val b c else 0 := rfl

def labelSumEquiv : ((Unit ⊕ Unit) ⊕ (Unit ⊕ Unit)) ≃ Bool × Bool where
  toFun x := match x with
    | .inl (.inl _) => (false,false)
    | .inl (.inr _) => (false,true)
    | .inr (.inl _) => (true,false)
    | .inr (.inr _) => (true,true)
  invFun x := match x.1,x.2 with
    | false,false => .inl (.inl ())
    | false,true => .inl (.inr ())
    | true,false => .inr (.inl ())
    | true,true => .inr (.inr ())
  left_inv x := by rcases x with (⟨⟩|⟨⟩)|(⟨⟩|⟨⟩) <;> rfl
  right_inv x := by rcases x with ⟨b,c⟩; cases b <;> cases c <;> rfl

def labelHadamard : Matrix.unitaryGroup (Bool × Bool) ℂ :=
  rewireUnitary labelSumEquiv (sumHadamard (Unit ⊕ Unit))

def labelSwap (branch : Bool) : Matrix.unitaryGroup (Bool × Bool) ℂ :=
  rewireUnitary labelSumEquiv (if branch then sumUnitary 1 (swapPublicPrivate (S := Unit))
    else sumUnitary (swapPublicPrivate (S := Unit)) 1)

theorem relabel_hadamard (a : ℕ) :
    rewireUnitary (twoLabelSignalEquiv (Fin a → Bool) D)
      (sumHadamard (((Fin a → Bool) × D) ⊕ ((Fin a → Bool) × D)))=
      logicalLabels (D := D) a labelHadamard := by
  apply Subtype.ext
  ext ⟨⟨⟨b,c⟩,x⟩,i⟩ ⟨⟨⟨d,e⟩,y⟩,j⟩
  rw [logicalLabels_entry]
  change (sumHadamard _).val _ _ = _
  simp only [sumHadamard_matrix,labelHadamard,rewireUnitary]
  cases b <;> cases c <;> cases d <;> cases e <;>
    by_cases hx : x=y <;> by_cases hi : i=j <;>
      simp [twoLabelSignalEquiv,labelSumEquiv,Matrix.one_apply,Prod.mk.injEq,hx,hi]

theorem relabel_swap (a : ℕ) (branch : Bool) :
    rewireUnitary (twoLabelSignalEquiv (Fin a → Bool) D)
      (if branch then sumUnitary 1 (swapPublicPrivate (S := (Fin a → Bool) × D))
        else sumUnitary (swapPublicPrivate (S := (Fin a → Bool) × D)) 1)=
      logicalLabels (D := D) a (labelSwap branch) := by
  apply Subtype.ext
  ext ⟨⟨⟨b,c⟩,x⟩,i⟩ ⟨⟨⟨d,e⟩,y⟩,j⟩
  rw [logicalLabels_entry]
  cases branch <;> cases b <;> cases c <;> cases d <;> cases e <;>
    simp [rewireUnitary,twoLabelSignalEquiv,labelSwap,labelSumEquiv,swapPublicPrivate,
      sumUnitary,Matrix.one_apply,Prod.mk.injEq]

end OptimalQLS.PolynomialTransform
