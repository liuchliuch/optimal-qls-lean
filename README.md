# Simultaneously Query-Optimal Quantum Linear-System Algorithm

Lean 4 formalization of [Gao, Ji and Liu, arXiv:2609.33686v1](https://arxiv.org/abs/2609.33686v1).

The main results give a quantum linear-system algorithm with simultaneous
`O(kappa log(1/epsilon))` matrix queries and `O(kappa/s)` state-preparation
queries, a matching lower bound on one common instance, and stability under
fixed approximate block encodings. Here `s = alpha * norm(A⁻¹ b)` and a
constant-factor estimate of `s` is supplied to the algorithm.

## Build and verify

Install [elan](https://github.com/leanprover/elan), Git, and Python 3.9 or later.
The Lean version and all Lake dependencies are pinned.

```sh
lake exe cache get
./scripts/verify.sh
```

`lake build` builds the proof library and the main-theorem certificates, and
checks the transitive axioms of every project declaration. The verification
script additionally checks source hygiene, the complete import closure, the
paper map, and vendored source checksums. Generated files stay in `.lake/`.

- Lean: **4.29.0-rc6**
- mathlib: **f156f7abd91ac67adb22bf999e5a71ba22e22e41**
- Allowed axioms: `propext`, `Classical.choice`, `Quot.sound`

## Reading the formalization

Start with the independently written [main-theorem statements](Verification/Statements.lean)
and their short [proof connections](Verification/Solution.lean).

| Paper result | Implementation endpoint |
| --- | --- |
| Theorem 5.7: exact and relaxed upper bounds | [Reduction/Theorem57.lean](OptimalQLS/Reduction/Theorem57.lean) |
| Theorem 6.1: same-instance lower bound | [LowerBounds/Physical/Theorem61.lean](OptimalQLS/LowerBounds/Physical/Theorem61.lean) |
| Theorem 7.2: approximate block encodings | [PhysicalRobustness/GeneralProgram/Promise.lean](OptimalQLS/PhysicalRobustness/GeneralProgram/Promise.lean) |

The [paper map](docs/paper-map.md) covers all 36 numbered items, including the
29 substantive proof statements. Read the [scope and correspondence review](docs/scope.md)
for input/output conventions, physical padding, and alternative proof choices.

`OptimalQLS.lean` is the public import. The proof library contains the matrix
geometry, transducer compiler, polynomial transformations, physical executions,
resource accounting, and lower-bound arguments. `vendor/first-paper/` contains
eleven trace-analysis modules used by the lower bounds.

## Comparator

The repository includes a separate trusted challenge for the three main
theorems and the relaxed clause of Theorem 5.7. It uses
[Lean Comparator](https://github.com/leanprover/comparator) to compare theorem
statements, restrict axioms, and replay the exported proofs in the kernel.

For these trusted local sources, including on macOS:

```sh
./scripts/run-comparator.sh --development
```

This mode performs the mathematical checks **without process sandboxing**.
See [verification details](docs/verification.md) for the Linux sandbox mode,
trust boundary, pinned tool revisions, and recorded verification results.
The four `sorry` placeholders exist only in `Verification/Challenge.lean`;
that module is excluded from the proof library, solution, and axiom audit.

## Citation and license

Use [CITATION.cff](CITATION.cff) to cite the paper. The project is released under
[Apache-2.0](LICENSE); third-party attribution is preserved in [NOTICE](NOTICE)
and the vendored sources.
