# Separate word-RAM proof backend

This project uses Lean 4.33.1, formal-math commit
`e1a4e6508154ea59f030480661590a9fe3018011` (package subdirectory
`3sum-apsp`), and mathlib commit
`0df444a360eaa60ab8c11dca51a86af692955474`.
The main project's Lean 4.31 configuration is unchanged.

`ThinMatrixProofs` reads the six existing source modules needed by the
canonical adapter from `../lean` and recompiles them into this project's own
`.lake` directory. Other research modules remain in the main Lean 4.31
project until explicitly integrated. Never add the main project's
4.31 build directory to `LEAN_PATH`.

`MachineAdapter.lean` reuses the actual upstream min-plus-to-APSP controller,
layout wrapper, verified Light-to-RAM compiler and rational-exponent bridge.
Its hypotheses require a genuine `Light.Solves mpTask ...` execution proof,
polynomial resource needs and the complete execution-time bound. It does not
prove that the improved min-plus implementation meets those hypotheses.

The upstream Apache-2.0 dependency is fetched by Lake rather than vendored.
Its copyright, license and NOTICE remain in the dependency checkout.

With elan available, build from this directory:

```sh
cd machine
MATHLIB_CACHE_DIR="$PWD/.lake/mathlib-cache" lake update
lake build ThinMatrixMachine
python3 scripts/verify.py
```

`lean-toolchain` selects the exact version. An isolated installation can set
`ELAN_HOME` to a separate directory before running these commands; the audit
uses a task-local installation and leaves the main project's toolchain intact.
Dependency downloads require network access. Commit the generated
`lake-manifest.json` so that all transitive revisions are fixed.

`MATHLIB_CACHE_DIR` is the cache tool's documented local download-cache
setting (mathlib `Cache/README.md`); the example keeps those downloads inside
this project's ignored `.lake` directory. Lake may
fetch the precompiled mathlib cache during its update hook.

`MachineBackend.lean` starts with actual finite Light code for a stored
coefficient read and pointwise add/sub/multiply. Its `Meets` proofs charge
five steps for a read and `21*n+6` for a pointwise pass, and specify memory
framing. A closed `Solves`/`PolyNeed` contract for the read is included;
caller argument evaluation and call overhead are additional charges.

`DenseMarkPass.lean` proves the actual Boolean pair-mark scatter pass, with
exact final marks, framing, and `30*I+6` steps (`36*I` for positive `I`).
`DenseScorePass.lean` proves an active-row sum in `22*I+10` steps (`32*I` for
positive `I`), with frozen input memory and accumulator bound `I*h`. Both
require explicit address, disjointness where needed, and word bounds.
`DenseArgminPass.lean` proves a minimum scan of cached scalar scores in
`29*P+14` steps (`43*P` for a nonempty candidate mask), including an explicit
word bound on the initial sentinel `maxScore+1`. It returns a remaining
candidate even when every score is zero. `DenseAffirmativePass.lean` proves
the strict certification flags in `34*I+6` steps; `DenseSurvivorPass.lean`
proves the subsequent survivor flags in `51*I+6` steps. Both charge the
current-pool threshold and explicit word bounds for both products.
`DenseMinimumUpdatePass.lean` proves an in-place cached-row minimum update
in `26*I+6` steps, including safe reads before each destination overwrite.
These are controller primitives; they do not provide the complete controller.

The initial backend, dense passes and adapter were checked with Lean 4.33.1: 28 scoped
declarations compiled with warnings treated as errors, with only `propext`,
`Classical.choice` and `Quot.sound` in their printed axiom dependencies.
The standard-library Python verifier checks the runtime, every transitive
dependency's pinned commit, and that dependency source checkouts have no
tracked changes or nonignored untracked files. It checks dependency sources
both before and after building imported dependencies and repeating the
compiler/axiom checks. A before/after SHA-256 snapshot covers this project's
Lean sources, the six shared proof sources, and its toolchain, Lake files and
verifier. A run fails if those sources or configuration change. The compiler
transcript records the source hash and check totals; dependency downloads and
build products remain excluded.
For a directly extracted runtime, pass `--lake-bin /path/to/bin/lake`; the
verifier puts that directory first on `PATH` for compiler helper processes.

`python3 scripts/verify.py --core` additionally checks recompilation of the
existing APSP correctness and cost-certificate sources, and the adapter that
combines the canonical ledger with a genuine execution-cost domination proof.
This optional target remains separate from the initial backend. Minimal
compatibility repairs preserve the statements of `APSPReduction`,
`APSPAlgorithm` and `AsymptoticCosts`; all three files have also been checked
with warnings treated as errors under both Lean 4.31 and Lean 4.33.1.
The project toolchains and their compiled artifacts remain separate.
The expanded check passed: 60 scoped declaration checks covering 58 unique
names, including all three compatibility files and the canonical ledger
adapter, with the same standard axiom allowlist. This proves the stated
composition lemmas; the improved Light min-plus solver and its execution-cost
domination hypothesis still have to be supplied.

The adapter alone does not close the improved APSP theorem. The new backend
must still implement and prove the shared-cache equality oracle, fast cyclic
coefficient arithmetic, composite-selection controller, and bit-scaled
min-plus caller with actual array layouts and execution costs.

