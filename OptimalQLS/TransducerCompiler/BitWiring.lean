import OptimalQLS.TransducerCompiler.EncodedSpace
import OptimalQLS.TransducerCompiler.XorCompiler
import OptimalQLS.TransducerCompiler.QuantumProgram

noncomputable section
namespace OptimalQLS.TransducerCompiler
open Matrix BinaryClock

variable {n : Type*} [Fintype n] [DecidableEq n] {ℓ : ℕ}

def spaceBitsEquiv : BitSpace n ℓ ≃ Space n (2^ℓ) :=
  Equiv.prodCongr (Equiv.refl (Base n)) (HadamardClock.bitsFinEquiv ℓ)

def toBitUnitary (U : Matrix.unitaryGroup (Space n (2^ℓ)) ℂ) :
    Matrix.unitaryGroup (BitSpace n ℓ) ℂ := rewireUnitary spaceBitsEquiv.symm U

theorem toBit_mul (U V : Matrix.unitaryGroup (Space n (2^ℓ)) ℂ) :
    toBitUnitary (U * V) = toBitUnitary U * toBitUnitary V := by
  apply Subtype.ext
  simp only [toBitUnitary, rewireUnitary, Submonoid.coe_mul, Matrix.submatrix_mul_equiv]

theorem toBit_one : toBitUnitary (n := n) (ℓ := ℓ) 1 = 1 := by
  apply Subtype.ext
  simp [toBitUnitary, rewireUnitary]

private theorem bits_zero_iff (b : Layout (2^ℓ)) (x : Bits ℓ) :
    HadamardClock.bitsFinEquiv ℓ x = b.zero ↔ x = fun _ => false := by
  have hz : b.zero = HadamardClock.bitsFinEquiv ℓ (fun _ => false) := by
    rw [HadamardClock.bitsFinEquiv_zero]
    rfl
  rw [hz, Equiv.apply_eq_iff_eq]

/-- Bit wiring identifies the source's zero-clock work with bitWork exactly. -/
theorem toBit_work (b : Layout (2^ℓ)) (S : Matrix.unitaryGroup (Base n) ℂ) :
    toBitUnitary (controlledUnitary (2^ℓ) (fun k => decide (k = b.zero)) S) = bitWork S := by
  apply Subtype.ext
  apply Matrix.ext_of_mulVec_single
  intro z
  ext ⟨i,x⟩
  rw [toBitUnitary, rewire_apply]
  simp only [Function.comp_apply, spaceBitsEquiv, Equiv.prodCongr_apply, Equiv.refl_apply,
    Equiv.symm_symm]
  rw [controlled_apply, bitWork, controlledOn_apply]
  simp [spaceBitsEquiv, Function.comp_def, bits_zero_iff]
  rw [(HadamardClock.bitsFinEquiv ℓ).symm_apply_apply x]

/-- The source's input-oracle call is the identical data query in bit coordinates. -/
theorem toBit_query (l : Label) (U : Matrix.unitaryGroup n ℂ) :
    toBitUnitary (query (K := 2^ℓ) l U) = dataQuery (a := Bits ℓ) l U := by
  apply Subtype.ext
  apply Matrix.ext_of_mulVec_single
  intro z
  ext ⟨⟨i,j⟩,x⟩
  rw [toBitUnitary, rewire_apply]
  simp only [Function.comp_apply, spaceBitsEquiv, Equiv.prodCongr_apply, Equiv.refl_apply,
    Equiv.symm_symm]
  rw [query_apply, dataQuery_apply]
  simp [spaceBitsEquiv, Function.comp_def]
  rw [(HadamardClock.bitsFinEquiv ℓ).symm_apply_apply x]

/-- Binary wiring respects XOR on every actual clock bit. -/
theorem bitsFin_xor (mask : Fin (2^ℓ)) (x : Bits ℓ) (i : Fin ℓ) :
    (HadamardClock.bitsFinEquiv ℓ).symm
      (xorClock mask (HadamardClock.bitsFinEquiv ℓ x)) i =
      Bool.xor (x i) ((HadamardClock.bitsFinEquiv ℓ).symm mask i) := by
  have hx := congrFun ((HadamardClock.bitsFinEquiv ℓ).symm_apply_apply x) i
  rw [HadamardClock.bitsFinEquiv_symm_apply] at hx
  simp [HadamardClock.bitsFinEquiv_symm_apply, xorClock, Nat.testBit_xor, hx]

/-- XOR frame in the physical bit-clock convention. -/
def bitFrameEquiv (b : Layout (2^ℓ)) (t : ℕ) : Equiv.Perm (BitSpace n ℓ) where
  toFun z := (z.1,fun i => Bool.xor (z.2 i)
    ((HadamardClock.bitsFinEquiv ℓ).symm (labelAddress b t z.1.2) i))
  invFun z := (z.1,fun i => Bool.xor (z.2 i)
    ((HadamardClock.bitsFinEquiv ℓ).symm (labelAddress b t z.1.2) i))
  left_inv z := by simp [Bool.xor_assoc]
  right_inv z := by simp [Bool.xor_assoc]

def bitFrame (b : Layout (2^ℓ)) (t : ℕ) : Matrix.unitaryGroup (BitSpace n ℓ) ℂ :=
  permutation (bitFrameEquiv b t)

/-- Exact whole-matrix identification of XOR frames, independent of all states. -/
theorem toBit_frame (b : Layout (2^ℓ)) (t : ℕ) :
    toBitUnitary (xorFrame (n := n) b t) = bitFrame b t := by
  apply Subtype.ext
  apply Matrix.ext_of_mulVec_single
  intro z
  ext ⟨i,x⟩
  rw [toBitUnitary, rewire_apply]
  simp only [xorFrame, address_eq_labelAddress, permutation_apply, Function.comp_apply,
    routingVia_apply, spaceBitsEquiv, Equiv.prodCongr_apply, Equiv.refl_apply,
    Equiv.symm_symm, bitFrame]
  apply congrArg (Pi.single z (1 : ℂ))
  change (i, (HadamardClock.bitsFinEquiv ℓ).symm
    (xorClock (labelAddress b t i.2) (HadamardClock.bitsFinEquiv ℓ x))) =
    (i,fun j => Bool.xor (x j) ((HadamardClock.bitsFinEquiv ℓ).symm (labelAddress b t i.2) j))
  apply Prod.ext
  · rfl
  · funext j
    exact bitsFin_xor _ x j

/-- Frame addresses agree bit-for-bit with the three truncated binary counters. -/
theorem labelAddress_bits (b : Layout (2^ℓ)) (d₁ d₂ : ℕ)
    (h₁ : b.D₁ = 2^d₁) (h₂ : b.D₂ = 2^d₂) (t : ℕ) (l : Label) (i : Fin ℓ) :
    (HadamardClock.bitsFinEquiv ℓ).symm (labelAddress b t l) i =
      natBits ℓ (t % 2^(trackWidth ℓ d₁ d₂ l)) i := by
  rw [HadamardClock.bitsFinEquiv_symm_apply]
  cases l with
  | pub => rfl
  | internal =>
    simp [labelAddress, Layout.zero, natBits, trackWidth]
    rw [Nat.mod_one]
    simp
  | first =>
    change Nat.testBit (t % 2^ℓ % b.D₁) i.val = Nat.testBit (t % 2^d₁) i.val
    rw [Nat.mod_mod_of_dvd t b.divides₁, h₁]
  | second =>
    change Nat.testBit (t % 2^ℓ % b.D₂) i.val = Nat.testBit (t % 2^d₂) i.val
    rw [Nat.mod_mod_of_dvd t b.divides₂, h₂]

/-- The actual low-bit primitive program realizes exactly the optimized frame change. -/
theorem toBit_update (b : Layout (2^ℓ)) (d₁ d₂ : ℕ)
    (h₁ : b.D₁ = 2^d₁) (h₂ : b.D₂ = 2^d₂) (t : ℕ) :
    toBitUnitary (xorFrame (n := n) b (t+1) * xorFrame b t) = bitUpdate ℓ d₁ d₂ t := by
  rw [toBit_mul, toBit_frame, toBit_frame]
  apply Subtype.ext
  apply Matrix.ext_of_mulVec_single
  intro z
  ext ⟨i,x⟩
  simp only [Submonoid.coe_mul, ← Matrix.mulVec_mulVec, bitFrame, bitUpdate,
    permutation_apply, Function.comp_apply]
  apply congrArg (Pi.single z (1 : ℂ))
  apply Prod.ext
  · rfl
  · funext j
    change Bool.xor (Bool.xor (x j)
      ((HadamardClock.bitsFinEquiv ℓ).symm (labelAddress b (t+1) i.2) j))
      ((HadamardClock.bitsFinEquiv ℓ).symm (labelAddress b t i.2) j) =
      Bool.xor (x j) (truncMask ℓ (trackWidth ℓ d₁ d₂ i.2) t j)
    rw [labelAddress_bits b d₁ d₂ h₁ h₂, labelAddress_bits b d₁ d₂ h₁ h₂,
      truncMask_eq_addresses]
    simp [Bool.xor_assoc, Bool.xor_comm]
    exact Bool.xor_left_comm _ _ _

end OptimalQLS.TransducerCompiler
