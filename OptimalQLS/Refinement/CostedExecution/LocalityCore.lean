import OptimalQLS.Refinement.PhysicalMeasurement

/-! # Semantic tensor locality, with literal physical-wire witnesses

A placement is admitted only when its active coordinates read distinct physical
bits and changing those coordinates preserves every other physical bit. Thus an
arbitrary Hilbert-space equivalence cannot make a nonlocal gate local. -/
noncomputable section
namespace OptimalQLS.Refinement.CostedExecution
open Matrix TransducerCompiler PolynomialTransform DirtyAncilla
open scoped Classical
set_option synthInstance.maxSize 16384
set_option maxHeartbeats 600000
set_option linter.unusedSimpArgs false

structure WireEmbedding {S W Q P R : Type}
    (q : Q → S → Bool) (c : P → W → Bool) (e : Q × R ≃ P) where
  wire : S ↪ W
  read : ∀ x r i, c (e (x,r)) (wire i) = q x i
  outside : ∀ x y r j, (∀ i, wire i ≠ j) → c (e (x,r)) j = c (e (y,r)) j

/-- An actual tensor product with an at-most-two-qubit unitary. The displayed
coordinate map certifies selected wires and every unselected spectator. -/
inductive IsTwoLocal {P W : Type} [Fintype P] [DecidableEq P]
    (c : P → W → Bool) : Matrix.unitaryGroup P ℂ → Prop where
  | tensor {S Q R : Type} [Fintype S] [DecidableEq S]
      [Fintype Q] [DecidableEq Q] [Fintype R] [DecidableEq R]
      (hS : Fintype.card S ≤ 2) (q : Q ≃ (S → Bool)) (e : Q × R ≃ P)
      (hw : WireEmbedding q c e) (U : Matrix.unitaryGroup Q ℂ) :
      IsTwoLocal c (GateSynthesis.placeHom e U)

/-- Composition of actual tensor placements; no circuit gate is inserted. -/
def tensorFrame {A B C P Q : Type} (e : A × B ≃ Q) (f : Q × C ≃ P) :
    A × (B × C) ≃ P :=
  (Equiv.prodAssoc A B C).symm.trans ((Equiv.prodCongr e (Equiv.refl C)).trans f)

theorem placeHom_comp {A B C P Q : Type}
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype C] [DecidableEq C] [Fintype P] [DecidableEq P]
    [Fintype Q] [DecidableEq Q] (e : A × B ≃ Q) (f : Q × C ≃ P)
    (U : Matrix.unitaryGroup A ℂ) :
    GateSynthesis.placeHom f (GateSynthesis.placeHom e U) =
      GateSynthesis.placeHom (tensorFrame e f) U := by
  apply Subtype.ext
  ext x y
  obtain ⟨⟨x,r⟩,rfl⟩ := f.surjective x
  obtain ⟨⟨y,s⟩,rfl⟩ := f.surjective y
  obtain ⟨⟨x,t⟩,rfl⟩ := e.surjective x
  obtain ⟨⟨y,u⟩,rfl⟩ := e.surjective y
  rw [placeHom_entry,placeHom_entry]
  change (if r=s then if t=u then U.val x y else 0 else 0) =
    (GateSynthesis.placeHom (tensorFrame e f) U).val
      ((tensorFrame e f) (x,(t,r))) ((tensorFrame e f) (y,(u,s)))
  rw [placeHom_entry]
  by_cases hr : r=s <;> by_cases ht : t=u <;> simp [hr,ht]

def WireEmbedding.comp {S T W A B C P Q : Type}
    {a : A → S → Bool} {b : Q → T → Bool} {c : P → W → Bool}
    {e : A × B ≃ Q} {f : Q × C ≃ P}
    (he : WireEmbedding a b e) (hf : WireEmbedding b c f) :
    WireEmbedding a c (tensorFrame e f) where
  wire := he.wire.trans hf.wire
  read := by
    intro x r i
    exact (hf.read (e (x,r.1)) r.2 (he.wire i)).trans (he.read x r.1 i)
  outside := by
    intro x y r j hj
    by_cases h : ∃ i, hf.wire i = j
    · obtain ⟨i,rfl⟩ := h
      rw [show tensorFrame e f (x,r) = f (e (x,r.1),r.2) from rfl,
        show tensorFrame e f (y,r) = f (e (y,r.1),r.2) from rfl,
        hf.read,hf.read]
      apply he.outside x y r.1 i
      intro k hk
      exact hj k (congrArg hf.wire hk)
    · exact hf.outside (e (x,r.1)) (e (y,r.1)) r.2 j (by simpa using h)

theorem IsTwoLocal.place {S W Q P R : Type}
    [Fintype Q] [DecidableEq Q] [Fintype P] [DecidableEq P]
    [Fintype R] [DecidableEq R] {q : Q → S → Bool} {c : P → W → Bool}
    (e : Q × R ≃ P) (hw : WireEmbedding q c e) (U : Matrix.unitaryGroup Q ℂ)
    (hU : IsTwoLocal q U) : IsTwoLocal c (GateSynthesis.placeHom e U) := by
  cases hU with
  | tensor hS q' e' he V =>
    rw [placeHom_comp]
    exact .tensor hS q' (tensorFrame e' e) (he.comp hw) V

/-- Boolean coordinates of the existing synthesis qubit and all named wires. -/
def phaseBits {ι : Type} (x : GateSynthesis.Space ι) : Unit ⊕ ι → Bool :=
  Sum.elim (fun _ => x.1) x.2

def boolCoordinates : Bool ≃ (Unit → Bool) where
  toFun b := fun _ => b
  invFun b := b ()
  left_inv _ := rfl
  right_inv b := by funext i; cases i; rfl

def pairCoordinates : (Bool × Bool) ≃ (Fin 2 → Bool) where
  toFun b := ![b.1,b.2]
  invFun b := (b 0,b 1)
  left_inv _ := rfl
  right_inv b := by funext i; fin_cases i <;> rfl


def phaseCoordinates (ι : Type) : GateSynthesis.Space ι ≃ (Unit ⊕ ι → Bool) :=
  PhysicalMeasurement.productBits boolCoordinates (Equiv.refl _)

/-- Reading literal source bits proves that their destination wires are distinct. -/
def WireEmbedding.ofWireMap {S W Q P R : Type} [DecidableEq S] [Nonempty R]
    (q : Q ≃ (S → Bool)) (c : P → W → Bool) (e : Q × R ≃ P)
    (f : S → W) (hr : ∀ x r i, c (e (x,r)) (f i) = q x i)
    (ho : ∀ x y r j, (∀ i, f i ≠ j) → c (e (x,r)) j = c (e (y,r)) j) :
    WireEmbedding q c e where
  wire := ⟨f,by
    intro i j hij
    by_contra hne
    let x := q.symm (fun k=>decide (k=j))
    have he := (hr x (Classical.choice inferInstance) i).symm.trans
      ((congrArg (c (e (x,Classical.choice inferInstance)))) hij |>.trans
        (hr x (Classical.choice inferInstance) j))
    simp [x,hne] at he⟩
  read := hr
  outside := ho

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def singleWiring_embedding (t : ι) :
    WireEmbedding boolCoordinates phaseBits (singleWiring t) where
  wire := ⟨fun _ => .inr t,fun i j _ => Subsingleton.elim i j⟩
  read := by intro x r i; cases i; simp [singleWiring,phaseBits,boolCoordinates]
  outside := by
    intro x y r j hj
    cases j with
    | inl j => rfl
    | inr j =>
      have ht : j ≠ t := by intro h; exact hj () (by simp [h])
      simp [singleWiring,phaseBits,ht]

def pairWiring_embedding (c t : ι) (hct : c ≠ t) :
    WireEmbedding pairCoordinates phaseBits (pairWiring c t hct) where
  wire := ⟨fun i => .inr (if i=0 then c else t),by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all⟩
  read := by
    intro x r i
    fin_cases i <;> simp [pairWiring,phaseBits,pairCoordinates,hct,Ne.symm hct]
  outside := by
    intro x y r j hj
    cases j with
    | inl j => rfl
    | inr j =>
      have hc : j ≠ c := by intro h; exact hj 0 (by simp [h])
      have ht : j ≠ t := by intro h; exact hj 1 (by simp [h])
      simp [pairWiring,phaseBits,hc,ht]

theorem phase_single_local (t : ι) (U : Matrix.unitaryGroup Bool ℂ) :
    IsTwoLocal phaseBits ((PhaseGate.single t U).eval) :=
  .tensor (by simp) boolCoordinates (singleWiring t) (singleWiring_embedding t) U

theorem phase_pair_local (c t : ι) (hct : c ≠ t)
    (U : Matrix.unitaryGroup (Bool × Bool) ℂ) :
    IsTwoLocal phaseBits ((PhaseGate.pair c t hct U).eval) :=
  .tensor (by simp) pairCoordinates (pairWiring c t hct) (pairWiring_embedding c t hct) U

end OptimalQLS.Refinement.CostedExecution
