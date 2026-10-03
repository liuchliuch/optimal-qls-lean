import OptimalQLS.TransducerCompiler.RealToffoli
import OptimalQLS.TransducerCompiler.BinaryClock.Quantum

/-! # Wire-local real gate synthesis with one reusable clean ancilla

A Toffoli is expanded into the proved fifteen-gate real template. The placement
selects three distinct existing wires and one shared ancilla; all remaining
wires are unchanged. Equal-control Toffolis reduce to one CNOT. This is a
structural gate expansion, not a cost certificate for an arbitrary matrix.
-/

noncomputable section
namespace OptimalQLS.TransducerCompiler.GateSynthesis
open Matrix BinaryClock

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

abbrev Data (ι : Type*) := ι → Bool
abbrev Space (ι : Type*) := Bool × Data ι
abbrev Rest (c d t : ι) := {i : ι // i ≠ c ∧ i ≠ d ∧ i ≠ t}

/-- Select exactly three physical wires, retaining every other wire as a spectator. -/
def splitTriple (c d t : ι) (hcd : c ≠ d) (hct : c ≠ t) (hdt : d ≠ t) :
    Data ι ≃ RealToffoli.Sector × (Rest c d t → Bool) where
  toFun x := ((x c, x d, x t), fun i => x i.val)
  invFun p i := if hc : i = c then p.1.1 else
    if hd : i = d then p.1.2.1 else if ht : i = t then p.1.2.2 else p.2 ⟨i,hc,hd,ht⟩
  left_inv x := by
    funext i
    by_cases hc : i = c <;> by_cases hd : i = d <;> by_cases ht : i = t <;>
      simp [hc, hd, ht, Ne.symm hcd, Ne.symm hct, Ne.symm hdt]
  right_inv p := by
    rcases p with ⟨⟨a,b,y⟩,r⟩
    apply Prod.ext
    · simp [hcd, hct, hdt, Ne.symm hcd, Ne.symm hct, Ne.symm hdt]
    · funext i
      simp [i.property.1, i.property.2.1, i.property.2.2]

/-- The four-qubit template is placed by literal wire selection, never an arbitrary basis change. -/
def templateWiring (c d t : ι) (hcd : c ≠ d) (hct : c ≠ t) (hdt : d ≠ t) :
    (RealToffoli.State × (Rest c d t → Bool)) ≃ Space ι where
  toFun p := (p.1.1, (splitTriple c d t hcd hct hdt).symm (p.1.2,p.2))
  invFun p := ((p.1, (splitTriple c d t hcd hct hdt p.2).1),
    (splitTriple c d t hcd hct hdt p.2).2)
  left_inv p := by rcases p with ⟨⟨z,s⟩,r⟩; simp
  right_inv p := by rcases p with ⟨z,x⟩; simp

private def allLiftHom {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] :
    Matrix.unitaryGroup a ℂ →* Matrix.unitaryGroup (a × b) ℂ where
  toFun U := controlledOn (fun _ : b => true) U
  map_one' := by
    apply Subtype.ext
    change Matrix.blockDiagonal (1 : b → Matrix a a ℂ) = 1
    exact Matrix.blockDiagonal_one
  map_mul' U V := by
    apply Subtype.ext
    change Matrix.blockDiagonal (fun _ : b => U.val * V.val) =
      Matrix.blockDiagonal (fun _ : b => U.val) * Matrix.blockDiagonal (fun _ : b => V.val)
    rw [Matrix.blockDiagonal_mul]

private def rewireHom {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (e : a ≃ b) : Matrix.unitaryGroup a ℂ →* Matrix.unitaryGroup b ℂ where
  toFun := rewireUnitary e
  map_one' := rewireUnitary_one e
  map_mul' := rewireUnitary_mul e

/-- Physical tensor placement is a genuine homomorphism of the actual unitary matrices. -/
def placeHom {a b w : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype w] [DecidableEq w] (e : a × b ≃ w) :
    Matrix.unitaryGroup a ℂ →* Matrix.unitaryGroup w ℂ :=
  (rewireHom e).comp allLiftHom

private theorem rewire_basis {a b : Type*} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b] (e : a ≃ b) (U : Matrix.unitaryGroup a ℂ) (i j : a)
    (h : U.val *ᵥ Pi.single i 1 = Pi.single j 1) :
    (rewireUnitary e U).val *ᵥ Pi.single (e i) 1 = Pi.single (e j) 1 := by
  rw [rewire_apply]
  have he : (Pi.single (e i) (1 : ℂ) : b → ℂ) ∘ e = Pi.single i 1 := by
    ext k; simp [Pi.single_apply, e.injective.eq_iff]
  rw [he,h]
  ext k
  simp [Pi.single_apply, Equiv.symm_apply_eq]

private theorem allControlled_basis {a b : Type*} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b] (U : Matrix.unitaryGroup a ℂ) (i j : a) (k : b)
    (h : U.val *ᵥ Pi.single i 1 = Pi.single j 1) :
    (controlledOn (fun _ : b => true) U).val *ᵥ Pi.single (i,k) 1 = Pi.single (j,k) 1 := by
  ext ⟨x,y⟩
  rw [controlledOn_apply]
  simp only [ite_true]
  by_cases hy : y = k
  · subst y
    have hv : (fun z => (Pi.single (i,k) (1 : ℂ) : a × b → ℂ) (z,k)) = Pi.single i 1 := by
      ext z; simp [Pi.single_apply]
    rw [hv,h]
    simp [Pi.single_apply]
  · simp [hy, Matrix.mulVec, dotProduct]

theorem placeHom_basis {a b w : Type*} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b] [Fintype w] [DecidableEq w]
    (e : a × b ≃ w) (U : Matrix.unitaryGroup a ℂ) (i j : a) (k : b)
    (h : U.val *ᵥ Pi.single i 1 = Pi.single j 1) :
    (placeHom e U).val *ᵥ Pi.single (e (i,k)) 1 = Pi.single (e (j,k)) 1 :=
  rewire_basis e _ _ _ (allControlled_basis U i j k h)

def dataHom : Matrix.unitaryGroup (Data ι) ℂ →* Matrix.unitaryGroup (Space ι) ℂ :=
  placeHom (Equiv.prodComm (Data ι) Bool)

def templateHom (c d t : ι) (hcd : c ≠ d) (hct : c ≠ t) (hdt : d ≠ t) :
    Matrix.unitaryGroup RealToffoli.State ℂ →* Matrix.unitaryGroup (Space ι) ℂ :=
  placeHom (templateWiring c d t hcd hct hdt)

/-- Primitive lower instructions. Template gates retain their verified one- or two-wire kind.
Their only placement freedom is the explicitly selected physical wires. -/
inductive LowerGate (ι : Type*) where
  | x (target : ι)
  | cx (control target : ι) (distinct : control ≠ target)
  | template (c d t : ι) (hcd : c ≠ d) (hct : c ≠ t) (hdt : d ≠ t) (g : RealToffoli.Gate)

def LowerGate.eval : LowerGate ι → Matrix.unitaryGroup (Space ι) ℂ
  | .x t => dataHom (programUnitary [BinaryClock.Gate.x t])
  | .cx c t h => dataHom (programUnitary [BinaryClock.Gate.cx c t h])
  | .template c d t hcd hct hdt g => templateHom c d t hcd hct hdt g.eval

def LowerGate.arity : LowerGate ι → ℕ
  | .x _ => 1
  | .cx _ _ _ => 2
  | .template _ _ _ _ _ _ g => g.arity

theorem LowerGate.arity_le_two (g : LowerGate ι) : g.arity ≤ 2 := by
  cases g with
  | x t => simp [arity]
  | cx c t h => simp [arity]
  | template c d t hcd hct hdt g => exact RealToffoli.Gate.arity_le_two g

def eval : List (LowerGate ι) → Matrix.unitaryGroup (Space ι) ℂ
  | [] => 1
  | g :: gs => eval gs * g.eval

theorem eval_append (c d : List (LowerGate ι)) : eval (c ++ d) = eval d * eval c := by
  induction c with
  | nil => simp [eval]
  | cons g gs ih => simp [eval, ih, mul_assoc]

theorem eval_template (c d t : ι) (hcd : c ≠ d) (hct : c ≠ t) (hdt : d ≠ t)
    (p : List RealToffoli.Gate) :
    eval (p.map (LowerGate.template c d t hcd hct hdt)) =
      templateHom c d t hcd hct hdt (RealToffoli.eval p) := by
  induction p with
  | nil => simp [eval, RealToffoli.eval]
  | cons g gs ih => simp [eval, RealToffoli.eval, LowerGate.eval, ih, map_mul]

/-- Expansion of one primitive, with the repeated-control case implemented as a CNOT. -/
def lowerGate : BinaryClock.Gate ι → List (LowerGate ι)
  | .x t => [.x t]
  | .cx c t h => [.cx c t h]
  | .ccx c d t hct hdt => if hcd : c = d then [.cx c t hct] else
      RealToffoli.circuit.map (LowerGate.template c d t hcd hct hdt)

theorem macro_length (g : BinaryClock.Gate ι) : (lowerGate g).length ≤ 15 := by
  cases g with
  | x t => simp [lowerGate]
  | cx c t h => simp [lowerGate]
  | ccx c d t hct hdt =>
    by_cases hcd : c = d
    · simp [lowerGate, hcd]
    · simpa only [lowerGate, dif_neg hcd, List.length_map, RealToffoli.circuit_length]
        using (le_rfl : (15 : ℕ) ≤ 15)

theorem splitTriple_ccx (c d t : ι) (hcd : c ≠ d) (hct : c ≠ t) (hdt : d ≠ t) (x : Data ι) :
    splitTriple c d t hcd hct hdt ((BinaryClock.Gate.ccx c d t hct hdt).act x) =
      (RealToffoli.toffoliSector (splitTriple c d t hcd hct hdt x).1,
        (splitTriple c d t hcd hct hdt x).2) := by
  apply Prod.ext
  · simp [splitTriple, BinaryClock.Gate.act, Function.update_apply, hct, hdt,
      RealToffoli.toffoliSector]
  · funext i
    simp [splitTriple, BinaryClock.Gate.act, Function.update_apply, i.property.2.2]

/-- The placed fifteen-gate template implements the chosen Toffoli and returns the shared ancilla. -/
theorem template_basis (c d t : ι) (hcd : c ≠ d) (hct : c ≠ t) (hdt : d ≠ t) (x : Data ι) :
    (templateHom c d t hcd hct hdt RealToffoli.unitary).val *ᵥ Pi.single (false,x) 1 =
      Pi.single (false,(BinaryClock.Gate.ccx c d t hct hdt).act x) 1 := by
  let e := templateWiring c d t hcd hct hdt
  let s := splitTriple c d t hcd hct hdt x
  have h := placeHom_basis e RealToffoli.unitary (false,s.1)
    (false,RealToffoli.toffoliSector s.1) s.2
    (RealToffoli.clean_toffoli_basis s.1.1 s.1.2.1 s.1.2.2)
  have hi : e ((false,s.1),s.2) = (false,x) := by
    change (false, (splitTriple c d t hcd hct hdt).symm
      (splitTriple c d t hcd hct hdt x)) = _
    rw [Equiv.symm_apply_apply]
  have ho : e ((false,RealToffoli.toffoliSector s.1),s.2) =
      (false,(BinaryClock.Gate.ccx c d t hct hdt).act x) := by
    change (false, (splitTriple c d t hcd hct hdt).symm
      (RealToffoli.toffoliSector s.1,s.2)) = _
    apply congrArg (fun y => (false,y))
    apply (splitTriple c d t hcd hct hdt).injective
    change (splitTriple c d t hcd hct hdt)
      ((splitTriple c d t hcd hct hdt).symm _) = _
    rw [Equiv.apply_symm_apply, splitTriple_ccx]
  simpa only [hi,ho] using h

private theorem dataHom_basis (U : Matrix.unitaryGroup (Data ι) ℂ) (x y : Data ι)
    (h : U.val *ᵥ Pi.single x 1 = Pi.single y 1) :
    (dataHom U).val *ᵥ Pi.single (false,x) 1 = Pi.single (false,y) 1 :=
  placeHom_basis (Equiv.prodComm (Data ι) Bool) U x y false h

theorem lower_x_basis (t : ι) (x : Data ι) :
    (LowerGate.eval (.x t)).val *ᵥ Pi.single (false,x) 1 =
      Pi.single (false,(BinaryClock.Gate.x t).act x) 1 := by
  apply dataHom_basis
  simpa only [run_cons, run_nil] using programUnitary_basis [BinaryClock.Gate.x t] x

theorem lower_cx_basis (c t : ι) (hct : c ≠ t) (x : Data ι) :
    (LowerGate.eval (.cx c t hct)).val *ᵥ Pi.single (false,x) 1 =
      Pi.single (false,(BinaryClock.Gate.cx c t hct).act x) 1 := by
  apply dataHom_basis
  simpa only [run_cons, run_nil] using programUnitary_basis [BinaryClock.Gate.cx c t hct] x

/-- Every gate expansion has the exact primitive action and restores the shared clean ancilla. -/
theorem lowerGate_basis (g : BinaryClock.Gate ι) (x : Data ι) :
    (eval (lowerGate g)).val *ᵥ Pi.single (false,x) 1 = Pi.single (false,g.act x) 1 := by
  cases g with
  | x t => simpa [lowerGate, eval] using lower_x_basis t x
  | cx c t hct => simpa [lowerGate, eval] using lower_cx_basis c t hct x
  | ccx c d t hct hdt =>
    by_cases hcd : c = d
    · subst d
      simpa [lowerGate, eval, BinaryClock.Gate.act] using lower_cx_basis c t hct x
    · rw [lowerGate, dif_neg hcd, eval_template]
      exact template_basis c d t hcd hct hdt x

/-- Lower every primitive to a literal list of real one- and two-qubit gates. -/
def lowerProgram (p : Program ι) : List (LowerGate ι) := p.flatMap lowerGate

/-- The shared ancilla is reused safely through an arbitrary-length gate program. -/
theorem lowerProgram_basis (p : Program ι) (x : Data ι) :
    (eval (lowerProgram p)).val *ᵥ Pi.single (false,x) 1 = Pi.single (false,run p x) 1 := by
  induction p generalizing x with
  | nil => simp only [lowerProgram, List.flatMap_nil, eval, OneMemClass.coe_one, Matrix.one_mulVec, run_nil]
  | cons g gs ih =>
    rw [lowerProgram, List.flatMap_cons, eval_append, Submonoid.coe_mul,
      ← Matrix.mulVec_mulVec, lowerGate_basis]
    exact ih (g.act x)

/-- At most fifteen actual elementary gates replace each original reversible primitive. -/
theorem lowerProgram_length (p : Program ι) : (lowerProgram p).length ≤ 15 * p.length := by
  induction p with
  | nil => simp [lowerProgram]
  | cons g gs ih =>
    simp only [lowerProgram, List.flatMap_cons, List.length_append, List.length_cons] at *
    have hg := macro_length g
    omega

/-- Arbitrary data amplitudes with one clean ancilla. -/
def cleanVector (v : Data ι → ℂ) : Space ι → ℂ
  | (false,x) => v x
  | (true,_) => 0

def cleanMap : (Data ι → ℂ) →ₗ[ℂ] (Space ι → ℂ) where
  toFun := cleanVector
  map_add' v w := by ext ⟨z,x⟩; cases z <;> simp [cleanVector]
  map_smul' c v := by ext ⟨z,x⟩; cases z <;> simp [cleanVector]

theorem cleanVector_single (x : Data ι) (c : ℂ) :
    cleanVector (Pi.single x c) = Pi.single (false,x) c := by
  ext ⟨z,y⟩
  cases z <;> simp [cleanVector, Pi.single_apply]

private theorem vector_eq_sum (v : Data ι → ℂ) :
    v = ∑ x : Data ι, v x • (Pi.single x (1 : ℂ) : Data ι → ℂ) := by
  ext x
  simp [Pi.single_apply]

theorem cleanVector_eq_sum (v : Data ι → ℂ) :
    cleanVector v = ∑ x : Data ι, v x • (Pi.single (false,x) (1 : ℂ) : Space ι → ℂ) := by
  ext ⟨z,x⟩
  cases z <;> simp [cleanVector, Pi.single_apply]

/-- Exact coherent synthesis on arbitrary superpositions, including reusable-ancilla cleanup. -/
theorem lowerProgram_cleanVector (p : Program ι) (v : Data ι → ℂ) :
    (eval (lowerProgram p)).val *ᵥ cleanVector v =
      cleanVector ((programUnitary p).val *ᵥ v) := by
  rw [cleanVector_eq_sum, Matrix.mulVec_sum]
  conv_rhs => rw [vector_eq_sum v, Matrix.mulVec_sum]
  change _ = cleanMap (∑ x : Data ι, (programUnitary p).val *ᵥ
    (v x • (Pi.single x (1 : ℂ) : Data ι → ℂ)))
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [Matrix.mulVec_smul, Matrix.mulVec_smul, map_smul,
    lowerProgram_basis, programUnitary_basis]
  change _ = v x • cleanVector (Pi.single (run p x) 1)
  rw [cleanVector_single]

theorem placeHom_real {a b w : Type*} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b] [Fintype w] [DecidableEq w]
    (e : a × b ≃ w) (U : Matrix.unitaryGroup a ℂ)
    (hU : ∀ i j, (U.val i j).im = 0) (i j : w) : ((placeHom e U).val i j).im = 0 := by
  change (Matrix.blockDiagonal (fun _ : b => U.val) (e.symm i) (e.symm j)).im = 0
  rw [Matrix.blockDiagonal_apply]
  split_ifs
  · exact hU _ _
  · rfl

theorem LowerGate.eval_real (g : LowerGate ι) (i j : Space ι) : (g.eval.val i j).im = 0 := by
  cases g with
  | x t => exact placeHom_real _ _ (programUnitary_real [BinaryClock.Gate.x t]) i j
  | cx c t h => exact placeHom_real _ _ (programUnitary_real [BinaryClock.Gate.cx c t h]) i j
  | template c d t hcd hct hdt g =>
    exact placeHom_real _ _ (RealToffoli.Gate.eval_real g) i j

theorem eval_real (p : List (LowerGate ι)) (i j : Space ι) : ((eval p).val i j).im = 0 := by
  induction p generalizing i j with
  | nil =>
    simp only [eval, OneMemClass.coe_one, Matrix.one_apply]
    split_ifs <;> rfl
  | cons g gs ih => simp [eval, Matrix.mul_apply, Complex.mul_im, ih, LowerGate.eval_real]

/-- The concrete lowered program has real matrix entries. -/
theorem lowerProgram_real (p : Program ι) (i j : Space ι) :
    ((eval (lowerProgram p)).val i j).im = 0 := eval_real _ i j

end OptimalQLS.TransducerCompiler.GateSynthesis
