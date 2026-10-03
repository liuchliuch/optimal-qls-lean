# Scope and paper correspondence review

The target is Gao, Ji and Liu, *Simultaneously Query-Optimal Quantum Linear-System
Algorithm*, [arXiv:2609.33686v1](https://arxiv.org/abs/2609.33686v1), submitted
27 September 2026. The 2 October 2026 review compared the original TeX statements
with their Lean endpoints and the definitions governing inputs, output states,
oracle access, and costs. The downloaded source archive matched the recorded
SHA-256 byte for byte. [paper-map.md](paper-map.md) records all 36 numbered items.

## Inputs and outputs

- **Theorem 5.7:** invertible complex matrices of any positive dimension, a unit
  right-hand side, an exact block encoding, the original factor-two solution-norm
  estimate (and its stated relaxed variant), and `0 < epsilon < 1/2`. One physical
  implementation is selected before the matrix, vector, and full oracle unitaries.
  Its heralded output has success probability greater than `2/3` and Euclidean
  error at most `epsilon`. Separate matrix/vector queries, local gates, and
  logarithmic space are bounded for this same implementation.
- **Theorem 6.1:** `kappa >= 8`, `0 < epsilon <= exp(-16)`, and every estimate
  between `1` and `kappa`. A single real Hermitian instance forces both
  `kappa * log(1/epsilon) / 192` matrix queries and `kappa / (75 * estimate)`
  vector queries. Correctness ranges over all promised Hermitian inputs, with
  heralded success at least `2/3` and conditional trace-distance error. Programs
  may branch, loop, and change finite workspace. Query bounds apply to every
  positive-Born finite prefix, so nontermination is not silently excluded.
- **Theorem 7.2:** the original matrix norm bound `norm A <= alpha` remains a
  separate premise, alongside the original estimate and fixed approximate
  encoding. If `kappa * delta / alpha <= 1/4`, the error is at most
  `epsilon + 2 * kappa * delta / alpha`, with the claimed separate resource
  orders. The implementation is chosen before `delta` as well as all hidden inputs.

`IsBlockEncoding` uses the induced Euclidean operator norm and literal signal
compression. Arbitrary logical dimensions use zero padding into the actual
power-of-two data register. All complete supplied unitaries remain quantified;
the development does not replace them with a preferred completion. Inverses of
the logical matrix and pseudoinverses of singular padded operators are distinct.

Upper-bound executions use actual at-most-two-wire gates, single-bit
measurements, partial traces, and classical branches. Oracle placement includes
the complete argument register, its literal control bit, and unchanged spectator
wires. Adjoint and controlled calls count as queries. The syntax that supplies
the cost also supplies the operational semantics.

## Proof choices and boundaries

The inverse-square approximation in Lemma 2.5 uses a proved bounded binomial
surrogate and Chebyshev compression, instead of importing the cited theorem as
an axiom. It satisfies the same evenness, interval, global bound, approximation,
and asymptotic degree requirements. QSP completion, phase factorization and
local gate synthesis are proved in the repository.

The final exact solver tests the dilation head together with the other
acceptance bits and repeats a fixed number of times. This differs from the
paper's staged repetition but proves the same existential result and resource
orders. Proposition 2.3's general three-run transformation is proved separately
for arbitrary supplied finite solver syntax and branch-dependent successful
states. Large explicit constants in Lean witness asymptotic bounds; they are
not intended as practical implementation estimates.

For non-power-of-two dimensions, the approximate full physical compression can
couple active and unused coordinates. The robust solver uses a support-aware
truncated-inverse argument for this case. This is stronger physical bookkeeping
than simply inverting the padded matrix, which is singular.

In Appendix A, synthesis scratch is returned exactly to zero. The live compiler
clock is part of the approximate transduction state; it is not claimed to return
exactly to zero. The controlled work circuit in Lemma 2.8 and Appendix A.1 is a
legitimate supplied premise. Its realization for the actual QLS preparation is
proved separately. The `Implementation` records contain correctness fields,
but the main theorems **construct** these records; they do not assume them.

The development establishes mathematical existence and correctness in the
exact-rotation query model. It is not an executable quantum-circuit generator.
Classical phase computation and finite universal gate-set approximation are
outside the paper's counted gate model.

## Findings and release changes

No mismatch was found in the reviewed numbered endpoints after checking the
model definitions and the padding/implementation bridges listed in the map.
This is a source-correspondence review, not a mathematical equivalence theorem
between an English manuscript and Lean.

The release preparation fixed a genuine standard-build failure: the vendored
library configuration omitted the dependency modules of `TraceNormBounds`.
It also corrected the old correspondence map's `bundle` reference from `Basic`
to `Reservoir`, replaced machine-specific build scripts, and removed obsolete
completion claims tied to another environment. The proof entry point was reduced
from 82 direct imports to 17 without changing its transitive project dependency
set. Per-file axiom-print commands were replaced by a module-based global audit.
No mathematical theorem statement or proof body was changed by these repairs.

## Mathematical sources

These sources motivate parts of the development; they are not additional
trusted axioms or build dependencies:

- [Belovs, Jeffery and Yolcu, arXiv:2311.15873v3](https://arxiv.org/abs/2311.15873v3):
  transducers and finite implementation.
- [Gilyén, Su, Low and Wiebe, arXiv:1806.01838v1](https://arxiv.org/abs/1806.01838v1):
  polynomial transformations and approximation.
- [Lin and Tong, arXiv:1910.14596v4](https://arxiv.org/abs/1910.14596v4):
  Chebyshev eigenstate filtering.

The main paper source can be retrieved with `python3 scripts/fetch-paper.py`;
it is saved under the ignored `.lake/paper/` directory and checked against
[paper-source.json](paper-source.json).
