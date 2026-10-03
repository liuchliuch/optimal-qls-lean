import OptimalQLS.TransducerCompiler.EncodedSpace

noncomputable section
namespace OptimalQLS.TransducerCompiler
open Matrix BinaryClock

variable {n : Type*} [Fintype n] [DecidableEq n] {ℓ : ℕ}

/-- A physical reversible label/clock/cache program as an actual unitary matrix. -/
def programOnAux (p : Program (LabelWire ℓ)) : Matrix.unitaryGroup (Label × (Bits ℓ × Bits ℓ)) ℂ :=
  rewireUnitary labelStateEquiv (programUnitary p)

/-- Data is a multiplicity register and is untouched by every compiler primitive. -/
def auxDataWiring : ((Label × (Bits ℓ × Bits ℓ)) × n) ≃ CachedSpace n ℓ where
  toFun p := ((p.2,p.1.1),p.1.2)
  invFun p := ((p.1.2,p.2),p.1.1)
  left_inv _ := rfl
  right_inv _ := rfl

def programOnSpace (p : Program (LabelWire ℓ)) : Matrix.unitaryGroup (CachedSpace n ℓ) ℂ :=
  rewireUnitary auxDataWiring (controlledOn (fun _ : n => true) (programOnAux p))

private theorem rewire_basis {a b : Type*} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b] (e : a ≃ b) (U : Matrix.unitaryGroup a ℂ) (i j : a)
    (h : U.val *ᵥ Pi.single i 1 = Pi.single j 1) :
    (rewireUnitary e U).val *ᵥ Pi.single (e i) 1 = Pi.single (e j) 1 := by
  rw [rewire_apply]
  have he : Pi.single (e i) (1 : ℂ) ∘ e = Pi.single i 1 := by
    ext k
    simp [Function.comp_def, Pi.single_apply, e.injective.eq_iff]
  rw [he,h]
  ext k
  simp [Function.comp_def, Pi.single_apply, Equiv.symm_apply_eq]

private theorem allControlled_basis {a b : Type*} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b] (U : Matrix.unitaryGroup a ℂ) (i j : a) (k : b)
    (h : U.val *ᵥ Pi.single i 1 = Pi.single j 1) :
    (controlledOn (fun _ : b => true) U).val *ᵥ Pi.single (i,k) 1 = Pi.single (j,k) 1 := by
  ext ⟨x,y⟩
  rw [controlledOn_apply]
  simp only [Bool.true_eq, ite_true]
  by_cases hy : y = k
  · subst y
    have hv : (fun z => (Pi.single (i,k) (1 : ℂ) : a × b → ℂ) (z,k)) = Pi.single i 1 := by
      ext z; simp [Pi.single_apply]
    rw [hv,h]
    simp [Pi.single_apply]
  · simp [Pi.single_apply, hy, Matrix.mulVec, dotProduct]

theorem programOnAux_basis (p : Program (LabelWire ℓ)) (z : Label × (Bits ℓ × Bits ℓ)) :
    (programOnAux p).val *ᵥ Pi.single z 1 =
      Pi.single (labelStateEquiv (run p (labelStateEquiv.symm z))) 1 := by
  simpa only [programOnAux, Equiv.apply_symm_apply] using
    rewire_basis labelStateEquiv (programUnitary p) (labelStateEquiv.symm z)
      (run p (labelStateEquiv.symm z)) (programUnitary_basis p _)

theorem programOnSpace_basis (p : Program (LabelWire ℓ)) (i : n)
    (z : Label × (Bits ℓ × Bits ℓ)) :
    (programOnSpace p).val *ᵥ Pi.single ((i,z.1),z.2) 1 =
      Pi.single ((i,(labelStateEquiv (run p (labelStateEquiv.symm z))).1),
        (labelStateEquiv (run p (labelStateEquiv.symm z))).2) 1 := by
  exact rewire_basis auxDataWiring (controlledOn (fun _ : n => true) (programOnAux p))
    (z,i) (labelStateEquiv (run p (labelStateEquiv.symm z)),i)
    (allControlled_basis _ _ _ i (programOnAux_basis p z))

/-- Linear encoded-subspace inclusion. -/
def encodeMap : (BitSpace n ℓ → ℂ) →ₗ[ℂ] (CachedSpace n ℓ → ℂ) where
  toFun := encodeVector
  map_add' v w := by ext ⟨b,x,a⟩; simp [encodeVector]; split_ifs <;> simp
  map_smul' c v := by ext ⟨b,x,a⟩; simp [encodeVector]

theorem encodeVector_single (z : BitSpace n ℓ) (c : ℂ) :
    encodeVector (Pi.single z c) = Pi.single (z.1,z.2,cache z.2) c := by
  rcases z with ⟨b,x⟩
  ext ⟨b',x',a⟩
  simp [encodeVector, Pi.single_apply, Prod.mk.injEq]
  split_ifs <;> simp_all

private theorem vector_eq_sum {a : Type*} [Fintype a] [DecidableEq a] (v : a → ℂ) :
    v = ∑ z : a, v z • (Pi.single z (1 : ℂ) : a → ℂ) := by
  ext i
  simp [Pi.single_apply]

/-- Basis semantics imply exact coherent semantics on every encoded vector. -/
theorem encoded_intertwine (M : Matrix (CachedSpace n ℓ) (CachedSpace n ℓ) ℂ)
    (N : Matrix (BitSpace n ℓ) (BitSpace n ℓ) ℂ)
    (h : ∀ z : BitSpace n ℓ, M *ᵥ Pi.single (z.1,z.2,cache z.2) 1 =
      encodeVector (N *ᵥ Pi.single z 1)) (v : BitSpace n ℓ → ℂ) :
    M *ᵥ encodeVector v = encodeVector (N *ᵥ v) := by
  rw [encodeVector_eq_sum, Matrix.mulVec_sum]
  conv_rhs => rw [vector_eq_sum v, Matrix.mulVec_sum]
  change _ = encodeMap (∑ z : BitSpace n ℓ, N *ᵥ (v z • (Pi.single z (1 : ℂ) : BitSpace n ℓ → ℂ)))
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro z _
  rw [Matrix.mulVec_smul, Matrix.mulVec_smul, map_smul]
  exact congrArg (v z • ·) (h z)

/-- Explicit wiring of a clean label/clock/cache basis state. -/
theorem labelStateEquiv_clean (l : Label) (x : Bits ℓ) :
    labelStateEquiv (extend (labelCode l) (BinaryClock.clean x)) =
      (l, x, fun _ => false) := by
  cases l <;> simp [labelStateEquiv, labelBitsEquiv, extend, labelCode, BinaryClock.clean] <;> rfl

theorem labelStateEquiv_symm_encode (l : Label) (x : Bits ℓ) :
    labelStateEquiv.symm (l, x, cache x) = extend (labelCode l) (encode x) := by
  apply labelStateEquiv.injective
  rw [Equiv.apply_symm_apply, labelStateEquiv_encode]

theorem labelStateEquiv_symm_clean (l : Label) (x : Bits ℓ) :
    labelStateEquiv.symm (l, x, fun _ => false) = extend (labelCode l) (BinaryClock.clean x) := by
  apply labelStateEquiv.injective
  rw [Equiv.apply_symm_apply, labelStateEquiv_clean]

/-- The literal primitive program initializing all comparator ancillas. -/
def cachePrepareProgram (ℓ : ℕ) : Program (LabelWire ℓ) :=
  (computePrefix ℓ le_rfl).map liftGate

/-- The exact reverse computation, touching no data or label bit. -/
def cacheUnprepareProgram (ℓ : ℕ) : Program (LabelWire ℓ) :=
  (computePrefix ℓ le_rfl).reverse.map liftGate

theorem cachePrepare_basis (i : n) (l : Label) (x : Bits ℓ) :
    (programOnSpace (cachePrepareProgram ℓ)).val *ᵥ
        Pi.single ((i,l), x, fun _ : Fin ℓ => false) 1 =
      Pi.single ((i,l), x, cache x) 1 := by
  have h := programOnSpace_basis (cachePrepareProgram ℓ) i (l, x, fun _ => false)
  simpa only [cachePrepareProgram, labelStateEquiv_symm_clean, liftProgram_run,
    compute_clean, labelStateEquiv_encode] using h

theorem cacheUnprepare_basis (i : n) (l : Label) (x : Bits ℓ) :
    (programOnSpace (cacheUnprepareProgram ℓ)).val *ᵥ Pi.single ((i,l), x, cache x) 1 =
      Pi.single ((i,l), x, fun _ : Fin ℓ => false) 1 := by
  have h := programOnSpace_basis (cacheUnprepareProgram ℓ) i (l, x, cache x)
  simpa only [cacheUnprepareProgram, labelStateEquiv_symm_encode, liftProgram_run,
    uncompute_clean, labelStateEquiv_clean] using h

/-- The actual comparator circuit prepares the encoded graph coherently on arbitrary vectors. -/
theorem cachePrepare_cleanVector (v : BitSpace n ℓ → ℂ) :
    (programOnSpace (cachePrepareProgram ℓ)).val *ᵥ cleanVector v = encodeVector v := by
  rw [cleanVector_eq_sum, encodeVector_eq_sum, Matrix.mulVec_sum]
  apply Finset.sum_congr rfl
  rintro ⟨⟨i,l⟩,x⟩ _
  rw [Matrix.mulVec_smul, cachePrepare_basis]

/-- Every comparator ancilla is returned exactly to zero on the entire encoded subspace. -/
theorem cacheUnprepare_encodeVector (v : BitSpace n ℓ → ℂ) :
    (programOnSpace (cacheUnprepareProgram ℓ)).val *ᵥ encodeVector v = cleanVector v := by
  rw [encodeVector_eq_sum, cleanVector_eq_sum, Matrix.mulVec_sum]
  apply Finset.sum_congr rfl
  rintro ⟨⟨i,l⟩,x⟩ _
  rw [Matrix.mulVec_smul, cacheUnprepare_basis]

/-- The exact per-label XOR address difference on the ideal clock register. -/
def bitUpdateEquiv (ℓ d₁ d₂ t : ℕ) : Equiv.Perm (BitSpace n ℓ) where
  toFun p := (p.1, fun i => Bool.xor (p.2 i) (truncMask ℓ (trackWidth ℓ d₁ d₂ p.1.2) t i))
  invFun p := (p.1, fun i => Bool.xor (p.2 i) (truncMask ℓ (trackWidth ℓ d₁ d₂ p.1.2) t i))
  left_inv p := by rcases p with ⟨b,x⟩; simp
  right_inv p := by rcases p with ⟨b,x⟩; simp

def bitUpdate (ℓ d₁ d₂ t : ℕ) : Matrix.unitaryGroup (BitSpace n ℓ) ℂ :=
  permutation (bitUpdateEquiv ℓ d₁ d₂ t)

theorem bitUpdate_basis (ℓ d₁ d₂ t : ℕ) (z : BitSpace n ℓ) :
    (bitUpdate ℓ d₁ d₂ t).val *ᵥ Pi.single z 1 =
      Pi.single (bitUpdateEquiv ℓ d₁ d₂ t z) 1 := by
  rw [bitUpdate, permutation_apply]
  funext p
  have he : bitUpdateEquiv ℓ d₁ d₂ t p = z ↔ p = bitUpdateEquiv ℓ d₁ d₂ t z :=
    (bitUpdateEquiv ℓ d₁ d₂ t).apply_eq_iff_eq_symm_apply
  simp only [Function.comp_apply, Pi.single_apply, he]

/-- Primitive-gate execution realizes the ideal XOR update coherently, preserving the cache. -/
theorem reservoirUpdate_encodeVector (ℓ d₁ d₂ t : ℕ) (v : BitSpace n ℓ → ℂ) :
    (programOnSpace (reservoirUpdate ℓ d₁ d₂ t)).val *ᵥ encodeVector v =
      encodeVector ((bitUpdate ℓ d₁ d₂ t).val *ᵥ v) := by
  apply encoded_intertwine
  rintro ⟨⟨i,l⟩,x⟩
  rw [bitUpdate_basis, encodeVector_single]
  have h := programOnSpace_basis (reservoirUpdate ℓ d₁ d₂ t) i (l, x, cache x)
  simpa only [labelStateEquiv_symm_encode, reservoirUpdate_supported,
    labelStateEquiv_encode, bitUpdateEquiv] using h

theorem cachePrepareProgram_length (ℓ : ℕ) : (cachePrepareProgram ℓ).length ≤ 3 * ℓ := by
  simpa [cachePrepareProgram] using computePrefix_length ℓ le_rfl

theorem cacheUnprepareProgram_length (ℓ : ℕ) : (cacheUnprepareProgram ℓ).length ≤ 3 * ℓ := by
  simpa [cacheUnprepareProgram] using computePrefix_length ℓ le_rfl

end OptimalQLS.TransducerCompiler
