# Verification and trust

## Reproduce the checks

```sh
lake exe cache get
./scripts/verify.sh
./scripts/run-comparator.sh --development
```

The first command downloads the cache for the pinned mathlib revision. The
second checks the source inventory, builds the full library and certificate,
reruns the axiom audit even if Lake already cached it, and verifies that its
module coverage equals the full solution import closure. The third downloads
and builds the pinned Comparator tool and runs its statement comparison,
axiom restriction, and Lean kernel replay. Python 3.9+, Bash, Git, and elan are
required. No machine-specific workspace paths are part of the build.

To rebuild only this project's Lean artifacts from scratch, remove
`.lake/build` before running the verification script; pinned dependency caches
may be retained. The GitHub workflow starts without a restored project cache
and runs the same checks on Linux. The workflow itself is not evidence that a
remote GitHub run has occurred.

## Statement/proof separation

- [Statements.lean](../Verification/Statements.lean) explicitly spells out the
  main result predicates, quantifier order, physical input promises, output
  error, success probability, and resource bounds.
- [Challenge.lean](../Verification/Challenge.lean) states four obligations with
  intentional proof placeholders: exact upper bound, relaxed upper bound,
  same-instance lower bound, and robust upper bound.
- [Solution.lean](../Verification/Solution.lean) proves those same obligations
  using the implementation theorems. It never imports the challenge.
- [comparator.json](../Verification/comparator.json) fixes these four theorem
  names and permits only the three standard axioms.

The specification imports the project's mathematical/operational model and
supporting lemmas. Its transitive import closure excludes the three final
endpoint modules; the source check enforces this separation. This is not a
second independent implementation of the quantum model. The imported definitions
remain part of the trusted specification and must be reviewed with it.

Comparator compares the statements and the definitions on which they depend,
checks the proof axiom dependencies, and replays the exported solution in the
Lean kernel. It cannot establish that the specification expresses the intended
informal mathematics. That correspondence is documented separately in the
[paper map](paper-map.md) and [scope review](scope.md).

Only the three main theorems and the relaxed clause are Comparator obligations.
The other numbered results are included in the library build, source
correspondence review, and global axiom audit; this repository does not claim
that all 29 have separate Comparator challenges.

## Global proof audit

[Audit.lean](../Verification/Audit.lean) selects declarations by their defining
module, including private, generated, and differently named declarations. It
checks membership in Lean's checked kernel environment and traverses both types
and proof values with Lean's `CollectAxioms.collect`. Any nonstandard axiom fails
the build. Importing the challenge into the audited environment also fails.

The permitted set is `propext`, `Classical.choice`, and `Quot.sound`. There are
no proof placeholders in `OptimalQLS`, the vendored modules, or the solution.
The four challenge placeholders are specification markers and are never used
as proof dependencies.

The elaboration option `backward.isDefEq.respectTransparency=false` preserves
compatibility with the pinned Lean release. It changes elaboration behavior,
not the kernel's logical rules. The source check rejects unchecked proof
mechanisms and checks the unchanged hashes of the vendored modules. Source
scanning complements, but does not replace, the kernel and axiom checks.

## Comparator versions and sandboxing

The compatible toolchain is pinned to:

| Tool | Commit |
| --- | --- |
| Comparator | `e6831abb2f76b7ce6f2fb28e6410a0df878e6e4b` |
| lean4export | `048394e1afeeb52b0fa27bcf3f1ade2ff0f0ab6d` |
| Lean4Checker | `b7398199245524275543dec6113229c9bb4902e5` |

The latter two revisions come from Comparator's checked-in Lake manifest. This
pins the version compatible with Lean 4.29.0-rc6 rather than using current master,
which targets a different Lean version.

On macOS, `--development` explicitly substitutes a local process runner for
Landrun. It performs comparison and kernel replay **without sandboxing**. Use it
only on trusted source trees. The included CI job uses the same mode on its
checkout and is labeled accordingly.

For a sandboxed run on Linux, install
[Landrun](https://github.com/Zouuup/landrun) and use:

```sh
./scripts/run-comparator.sh
```

This uses a user systemd unit with the address-family restriction described in
[current upstream guidance](https://github.com/leanprover/comparator). It requires
an operational Landrun sandbox and user systemd session. The sandboxed mode has
not been exercised by the macOS verification recorded here. No claim is made
about safely executing hostile source code or about independent external-kernel
verification; Nanoda is disabled.

## Recorded run

The 2 October 2026 run used official Lean 4.29.0-rc6 on macOS arm64 and clean,
revision-checked pinned dependency sources with their compiled caches. All 631
project/vendor proof modules were compiled from source in this workspace. The
standard Lake build, the specification and proof connections, and the global
audit passed. The audit covered 13,941 declarations in 633 imported project
modules and found only the three permitted axioms.

Comparator accepted all four obligations and reported that the Lean kernel
accepted the solution. Development mode was used. Small positive and negative
controls also check that a matching proof passes while a changed statement and
an extra axiom are rejected.

[verification.json](verification.json) records the checked source digest and
outcomes. `scripts/check_source.py` prints the digest and saves the per-file
SHA-256 inventory locally. The digest hashes `path`, NUL, file SHA-256,
and newline records, sorted lexicographically by the complete relative POSIX path,
for all release files except `docs/verification.json` itself; generated caches
are excluded. Regenerate the checks after editing Lean sources, specifications,
configuration, or verification scripts; a saved record is not a substitute for
running them. Detailed local logs and generated inventories belong in
`.lake/verification/`, not in the published source tree.

The 4 October 2026 release recheck standardized the digest ordering and updated
the packaging exclusions. Every Lean source file, dependency lock, toolchain,
build configuration, and Comparator configuration/runner was compared byte for
byte with the previously verified distribution and is unchanged. The source
checks and extracted-archive checks were rerun; the Lean build and Comparator
results above remain the 2 October run, not a new kernel run on 4 October.
