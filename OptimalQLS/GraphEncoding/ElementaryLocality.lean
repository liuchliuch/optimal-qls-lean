import OptimalQLS.GraphEncoding.Proposition43

/-! # A syntactic elementary-gate witness for every counted graph work instruction -/
noncomputable section
set_option synthInstance.maxSize 2048
set_option maxHeartbeats 800000
namespace OptimalQLS.GraphEncoding
open Matrix PolynomialTransform TransducerCompiler
variable {S D B : Type*} [Fintype S] [DecidableEq S]
  [Fintype D] [DecidableEq D] [Fintype B] [DecidableEq B]

/-- Every constructor is a literal real gate on named wires. There is no
constructor for arbitrary work matrices or arbitrary basis equivalences. -/
inductive GraphWorkGate where
  | selectBit (G : Matrix.unitaryGroup Bool ℝ)
  | controlledHadamard
  | controlledX
  | edge (g : TransducerCompiler.GateSynthesis.LowerGate (Fin 4))

def GraphWorkGate.arity : GraphWorkGate → ℕ
  | .selectBit _ => 1
  | .controlledHadamard => 2
  | .controlledX => 2
  | .edge g => g.arity

theorem GraphWorkGate.arity_le_two (g : GraphWorkGate) : g.arity ≤ 2 := by
  cases g with
  | selectBit _ => simp [arity]
  | controlledHadamard => simp [arity]
  | controlledX => simp [arity]
  | edge g => exact TransducerCompiler.GateSynthesis.LowerGate.arity_le_two g

def GraphWorkGate.eval (S D : Type*) [Fintype S] [DecidableEq S]
    [Fintype D] [DecidableEq D] : GraphWorkGate →
    Matrix.unitaryGroup (Bool × (BranchSpace S D ⊕ BranchSpace S D)) ℂ
  | .selectBit G => borrow (TransducerCompiler.GateSynthesis.placeHom
      (sumBitWiring (BranchSpace S D)) (complexifyRealUnitary G))
  | .controlledHadamard => borrow (TransducerCompiler.GateSynthesis.placeHom
      (controlledBitWiring Label (S × D)) (complexifyRealUnitary
        (controlledBitReal (mixReal (-halfAmplitude) halfAmplitude_bound))))
  | .controlledX => borrow (TransducerCompiler.GateSynthesis.placeHom
      (controlledBitWiring Label (S × D)) (complexifyRealUnitary
        (controlledBitReal RealToffoli.xReal)))
  | .edge g => TransducerCompiler.GateSynthesis.placeHom
      (labelLowerWiring ((S × D) ⊕ (S × D))) g.eval

theorem borrow_real {W : Type*} [Fintype W] [DecidableEq W]
    (U : Matrix.unitaryGroup W ℂ) (h : ∀ i j, (U.val i j).im=0)
    (i j : Bool × W) : ((borrow U).val i j).im=0 := by
  simp [borrow, tensorUnitary, HadamardClock.tensorUnitary, Complex.mul_im, h,
    Matrix.one_apply]
  split_ifs <;> simp_all

theorem GraphWorkGate.real (g : GraphWorkGate)
    (i j : Bool × (BranchSpace S D ⊕ BranchSpace S D)) : ((g.eval S D).val i j).im=0 := by
  cases g with
  | selectBit G =>
    apply borrow_real
    exact TransducerCompiler.GateSynthesis.placeHom_real _ _ (fun _ _ => rfl)
  | controlledHadamard =>
    apply borrow_real
    exact TransducerCompiler.GateSynthesis.placeHom_real _ _ (fun _ _ => rfl)
  | controlledX =>
    apply borrow_real
    exact TransducerCompiler.GateSynthesis.placeHom_real _ _ (fun _ _ => rfl)
  | edge g =>
    exact TransducerCompiler.GateSynthesis.placeHom_real _ _
      (TransducerCompiler.GateSynthesis.LowerGate.eval_real g) _ _

theorem weightedMix_inv {W : Type*} [Fintype W] [DecidableEq W] (κ : ℝ) (hκ : 0 < κ) :
    (weightedMix W κ hκ)⁻¹ = weightedMix W κ hκ := by
  apply Subtype.ext
  exact weightedMix_hermitian κ hκ

theorem controlledSignal_work (U : Matrix.unitaryGroup (Bool × (BranchSpace S D ⊕ BranchSpace S D)) ℂ)
    (h : QueryInstruction.work U ∈ controlledSignalCircuit S D B) :
    ∃ g : GraphWorkGate, g.eval S D = U := by
  simp only [controlledSignalCircuit, signalCircuit, hermitianizationCircuit,
    QueryCircuit.lift, List.map_append, List.map_cons, List.map_nil,
    QueryInstruction.lift, List.append_assoc, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false, QueryInstruction.work.injEq,
    QueryInstruction.noConfusion, tensorPort_apply, leftOraclePort_apply,
    sumHadamard_inv] at h
  rcases h with h | h | h | h | h
  · refine ⟨.controlledHadamard, ?_⟩
    simpa only [GraphWorkGate.eval, controlled_one_is_two, hadamard_one_qubit, borrow] using h.symm
  · refine ⟨.controlledX, ?_⟩
    simpa only [GraphWorkGate.eval, controlled_one_is_two, swap_one_qubit, borrow] using h.symm
  · cases h
  · cases h
  · refine ⟨.controlledHadamard, ?_⟩
    simpa only [GraphWorkGate.eval, controlled_one_is_two, hadamard_one_qubit, borrow] using h.symm

theorem labelLower_work (p : BinaryClock.Program (Fin 4))
    (U : Matrix.unitaryGroup (Bool × (BranchSpace S D ⊕ BranchSpace S D)) ℂ)
    (h : QueryInstruction.work U ∈ labelLowerCircuit ((S × D) ⊕ (S × D)) (S × D) B p) :
    ∃ g : GraphWorkGate, g.eval S D = U := by
  obtain ⟨g,hg,hEq⟩ := List.mem_map.mp h
  refine ⟨.edge g, ?_⟩
  exact QueryInstruction.work.inj hEq

/-- Exhaustive accounting: every one of the76 counted work instructions comes
from a genuine one- and two-qubit real-gate constructor on named physical wires. -/
theorem realizedSelect_work_elementary (κ : ℝ) (hκ : 0 < κ)
    (U : Matrix.unitaryGroup (Bool × (BranchSpace S D ⊕ BranchSpace S D)) ℂ)
    (h : QueryInstruction.work U ∈ realizedSelectCircuit S D B κ hκ) :
    ∃ g : GraphWorkGate, g.eval S D = U ∧ g.arity ≤ 2 := by
  have he : ∃ g : GraphWorkGate, g.eval S D = U := by
    simp only [realizedSelectCircuit, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false, QueryInstruction.work.injEq] at h
    simp only [or_assoc] at h
    rcases h with h | h | h | h | h | h
    · refine ⟨.selectBit (mixReal (-mixAmplitude κ) (mixAmplitude_properties hκ).2), ?_⟩
      exact (congrArg borrow (mixing_one_qubit (W := BranchSpace S D) κ hκ)).trans
        (by simpa only [weightedMix_inv] using h.symm)
    · exact controlledSignal_work U h
    · exact labelLower_work label01Program U h
    · refine ⟨.selectBit zReal, ?_⟩
      simpa only [GraphWorkGate.eval, phase_one_qubit] using h.symm
    · exact labelLower_work label02Program U h
    · refine ⟨.selectBit (mixReal (-mixAmplitude κ) (mixAmplitude_properties hκ).2), ?_⟩
      exact (congrArg borrow (mixing_one_qubit (W := BranchSpace S D) κ hκ)).trans h.symm
  obtain ⟨g,hg⟩ := he
  exact ⟨g,hg,g.arity_le_two⟩

/-- The final physical register routing changes no gate, only its tuple order. -/
theorem elementaryGraph_work_elementary (κ : ℝ) (hκ : 0 < κ)
    (U : Matrix.unitaryGroup (PhysicalSignal S × (Fin 4 × D)) ℂ)
    (h : QueryInstruction.work U ∈ elementaryGraphCircuit S D B κ hκ) :
    ∃ g : GraphWorkGate,
      rewireUnitary (realizedPhysicalWiring S D) (g.eval S D) = U ∧ g.arity ≤ 2 := by
  obtain ⟨q,hq,hEq⟩ := List.mem_map.mp h
  cases q with
  | matrixCall p b => cases hEq
  | vectorCall p b => cases hEq
  | work V =>
    have hv : rewireUnitary (realizedPhysicalWiring S D) V = U := by
      simpa only [QueryInstruction.lift, rewirePort_apply] using QueryInstruction.work.inj hEq
    obtain ⟨g,hg,ha⟩ := realizedSelect_work_elementary κ hκ V hq
    exact ⟨g, hg ▸ hv, ha⟩


/-- Proposition4.3 strengthened by a syntactic elementary-gate witness for
absolutely every counted work instruction. -/
theorem proposition4_3_elementary [Nonempty D] (κ : ℝ) (hκ : 2 ≤ κ) (s : S) :
    ∃ c : QueryCircuit (S × D) B (PhysicalSignal S × (Fin 4 × D)),
      c.matrixQueries=2 ∧ c.vectorQueries=0 ∧ workInstructions c=76 ∧
      (∀ U, QueryInstruction.work U ∈ c → ∃ g : GraphWorkGate,
        rewireUnitary (realizedPhysicalWiring S D) (g.eval S D) = U ∧ g.arity ≤ 2) ∧
      (∀ a : ℕ, Fintype.card S=2^a → Fintype.card (PhysicalSignal S)=2^(a+4)) ∧
      ∀ (U : Matrix.unitaryGroup (S × D) ℂ) (Ub : Matrix.unitaryGroup B ℂ)
        (A : Matrix D D ℂ), A.IsHermitian → IsBlockEncoding s 1 0 U A →
        (c.eval U Ub).val.IsHermitian ∧
        IsBlockEncoding (physicalSignalZero s) (1+κ⁻¹) 0 (c.eval U Ub) (graphMatrix A κ) := by
  have hp : 0 < κ := by linarith
  refine ⟨elementaryGraphCircuit S D B κ hp, (elementaryGraphCircuit_counts κ hp).1,
    (elementaryGraphCircuit_counts κ hp).2.1, (elementaryGraphCircuit_counts κ hp).2.2,
    elementaryGraph_work_elementary κ hp, physical_signal_qubits, ?_⟩
  intro U Ub A hA henc
  rw [elementaryGraphCircuit_eval]
  exact ⟨physicalEncoding_hermitian κ hp U, physicalEncoding_exact κ hp s U A hA henc⟩

/-- Global Hermiticity permits the identical76-gate word for an adjoint call,
without assuming anything about the original input oracle's adjoint. -/
theorem elementaryGraphCircuit_inverse (κ : ℝ) (hκ : 0 < κ)
    (U : Matrix.unitaryGroup (S × D) ℂ) (Ub : Matrix.unitaryGroup B ℂ) :
    ((elementaryGraphCircuit S D B κ hκ).eval U Ub)⁻¹ =
      (elementaryGraphCircuit S D B κ hκ).eval U Ub := by
  rw [elementaryGraphCircuit_eval]
  apply Subtype.ext
  exact physicalEncoding_hermitian κ hκ U

end OptimalQLS.GraphEncoding
