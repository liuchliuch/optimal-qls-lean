import OptimalQLS.LowerBounds.ReachableBranches
import Mathlib.Data.Fintype.BigOperators

/-!
# Finite adaptive quantum query trees

Measurements are concrete input-independent matrices. Their outcome selects
a subtree, and vectors remain unnormalized throughout. On a valid quantum
instrument these squared norms are joint branch probabilities, so there is
no postselection renormalization hidden in this semantics. The polynomial
bound holds for all such matrix trees, even without their usual Kraus
completeness equations; hence it does not assume any hard analytic fact.
-/
noncomputable section
open scoped BigOperators
namespace OptimalQLS.LowerBounds

inductive AdaptiveQueryTree (m w : ℕ) where
  | output (weight : ℝ)
  | gate (U : Matrix (QueryBasis m w) (QueryBasis m w) ℂ) (next : AdaptiveQueryTree m w)
  | query (next : AdaptiveQueryTree m w)
  | instrument (r : ℕ) (K : Fin r → Matrix (QueryBasis m w) (QueryBasis m w) ℂ)
      (next : Fin r → AdaptiveQueryTree m w)

def AdaptiveQueryTree.Terminal {m w : ℕ} : AdaptiveQueryTree m w → Type
  | .output _ => Unit
  | .gate _ next => next.Terminal
  | .query next => next.Terminal
  | .instrument r _ next => (i : Fin r) × (next i).Terminal

instance AdaptiveQueryTree.terminalFintype {m w : ℕ} (tree : AdaptiveQueryTree m w) :
    Fintype tree.Terminal := by
  induction tree with
  | output weight => exact inferInstanceAs (Fintype Unit)
  | gate U next ih => exact ih
  | query next ih => exact ih
  | instrument r K next ih =>
    letI : ∀ i : Fin r, Fintype (next i).Terminal := ih
    exact inferInstanceAs (Fintype ((i : Fin r) × (next i).Terminal))

/-- The actual query/matrix path to a terminal measurement outcome. -/
def AdaptiveQueryTree.terminalPath {m w : ℕ} (tree : AdaptiveQueryTree m w)
    (initialPath : QueryPath m w) : tree.Terminal → QueryPath m w :=
  match tree with
  | .output _ => fun _ => initialPath
  | .gate U next => next.terminalPath (.gate U initialPath)
  | .query next => next.terminalPath (.query initialPath)
  | .instrument _ K next => fun k => (next k.1).terminalPath (.gate (K k.1) initialPath) k.2

def AdaptiveQueryTree.terminalWeight {m w : ℕ} (tree : AdaptiveQueryTree m w) :
    tree.Terminal → ℝ :=
  match tree with
  | .output weight => fun _ => weight
  | .gate _ next => next.terminalWeight
  | .query next => next.terminalWeight
  | .instrument _ _ next => fun k => (next k.1).terminalWeight k.2

/-- Recursive operational bias. `+1`, `-1`, and `0` terminal weights express
output 0, output 1, and a fair random bit, respectively. -/
def AdaptiveQueryTree.execute {m w : ℕ} (tree : AdaptiveQueryTree m w)
    (z : BitString m) (ψ : QueryBasis m w → ℂ) : ℝ :=
  match tree with
  | .output weight => weight * ∑ b, Complex.normSq (ψ b)
  | .gate U next => next.execute z (fun b => ∑ c, U b c * ψ c)
  | .query next => next.execute z (applyBitOracle z ψ)
  | .instrument _ K next =>
      ∑ k, (next k).execute z (fun b => ∑ c, K k b c * ψ c)

/-- Enumerating terminal branches agrees exactly with the recursive matrix
and measurement semantics. -/
theorem AdaptiveQueryTree.branchBias_eq_execute {m w : ℕ}
    (tree : AdaptiveQueryTree m w) (initialPath : QueryPath m w) (z : BitString m) :
    branchBias (tree.terminalPath initialPath) tree.terminalWeight z =
      tree.execute z (initialPath.state z) := by
  induction tree generalizing initialPath with
  | output weight => simp [branchBias, terminalPath, terminalWeight, execute, QueryPath.bornWeight, Terminal]
  | gate U next ih => exact ih (.gate U initialPath)
  | query next ih => exact ih (.query initialPath)
  | instrument r K next ih =>
    change (∑ k : (i : Fin r) × (next i).Terminal,
      (next k.1).terminalWeight k.2 *
        ((next k.1).terminalPath (.gate (K k.1) initialPath) k.2).bornWeight z) = _
    rw [Fintype.sum_sigma]
    exact Finset.sum_congr rfl (fun i _ => ih i (.gate (K i) initialPath))

/-- The paper's unbounded-error parity conclusion for finite adaptive
measurement trees, counting only positive-probability runs. -/
theorem AdaptiveQueryTree.exists_reachable_parity_hard_run {m w : ℕ} (hm : 0 < m)
    (tree : AdaptiveQueryTree m w) (ψ : QueryBasis m w → ℂ)
    (hsuccess : ∀ z : BitString m, 0 < paritySign z * tree.execute z ψ) :
    ∃ (z : BitString m) (k : tree.Terminal),
      0 < (tree.terminalPath (.initial ψ) k).bornWeight z ∧
      m ≤ 2 * (tree.terminalPath (.initial ψ) k).queries := by
  apply OptimalQLS.LowerBounds.exists_reachable_parity_hard_run hm
    (tree.terminalPath (.initial ψ)) tree.terminalWeight
  intro z
  rw [tree.branchBias_eq_execute]
  exact hsuccess z

end OptimalQLS.LowerBounds
