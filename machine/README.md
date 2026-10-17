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

`DenseScoreTablePass.lean` now composes the row scorer into an actual
row-major candidate-score table. It charges nested calls, argument
evaluation, output stores and the outer loop: `P*(22*I+33)+6` steps.
Its `Selection` routine computes that table and calls the argmin scan,
returning a remaining candidate minimizing the original active
multiplicity sum in `22*P*I+62*P+37` steps, including all-zero scores.
Both have closed `Solves`, `PolyNeed` and `SolvedIn` contracts for fixed
finite programs, explicit word/layout bounds, append stability and memory
framing. Caller-provided score buffers are charged as part of the instance;
neither routine allocates additional scratch cells.

`DenseCertificationFinish.lean` composes affirmative flags, pair-mark
scatter and survivor flags into one fixed finite Light program. Its
closed `Meets` contract proves all three outputs and framing outside
their buffers in `115*I+47` steps. That includes 29 argument/call steps
beyond the three kernel allowances. The supplied pool scalar is used in
both comparisons; the enclosing controller must still compute and pass
the current pool cardinality. Ordered layout, product word bounds and
call depth remain explicit preconditions.

`ScoreSelectionMachine.lean` compiles the closed score-selection routine
to one fixed RAM instruction list using the pinned verified compiler.
`ThinMatrix.ScoreSelectionMachine.compiled_execution` proves that actual
RAM execution returns a remaining minimizing candidate, stores every score,
and preserves memory outside the score vector and fixed compiler workspace.
Its hypotheses describe the eight-cell metadata header, input arrays,
word representation and admissible word size; it has no solver or execution
premise. The complete source wrapper takes at most `62*n+59` steps, where
`n=P*I+2*P+I`; `compiled_time_bound` gives the corresponding RAM bound
with the fixed compiler constant. This is a compiled controller component,
not a compiled improved min-plus or APSP implementation.

`DensePoolPass.lean` scans the current Boolean candidate mask in
`19*P+10` steps and preserves all memory. Its closed task contract returns
the exact filtered cardinality, including an empty pool; deletion lemmas
show that clearing a selected member removes exactly one candidate.

`DensePoolMinimumPass.lean` computes each incidence's minimum over **all
remaining candidates** from the row-major cache, visiting every candidate
for every incidence. The fixed program costs `I*(35*P+33)+6` steps and
writes only the minima vector. Its closed public task requires a nonempty
pool. An internal empty scan returns the explicitly charged `height+1`
sentinel; it is not identified with the canonical empty-pool convention.

`DenseSelectionRound.lean` composes aggregate-score selection, a selected-row
minimum update and exact flag deletion in `22*P*I+62*P+26*I+87` steps.
Its closed task returns an argmin for the original active mask and original
remaining pool, stores every original score and preserves memory outside
the scores, minima and remaining arrays. Its minima are
`min(initial, chosenRow)`. This literal component does not by itself compute
the canonical per-incidence minimum over the whole pool, or implement the
canonical replacement of the base row by the chosen row.

`CertificationFinishTask.lean` closes the three-pass certification task,
with a physical remaining mask determining its exact mathematical current
cardinality, polynomial needs and append stability. The separately compiled
`CertificationFinishMachine.lean` proves actual RAM execution of that task
from a twelve-cell header containing the exact pool scalar; its source
wrapper costs `115*n+77`, where `n=6*I+Q+P`.

`CountedCertificationFinish.lean` removes that scalar from the calling
convention: it actually scans the remaining mask and passes the returned
count to affirmative testing, pair marking and survivor filtering. The
complete fixed program costs `19*P+115*I+76` steps, including the scan and
both argument lists and calls. It has closed `Solves`, `PolyNeed` and
`SolvedIn` contracts and preserves the mask. The cached modular counts,
incidence ownership and input word/layout promises remain explicit.

`CountedCertificationMachine.lean` compiles this counted routine to one
fixed RAM program. Its thirteen-cell header contains the remaining-mask
length and address, with no supplied cardinality. The execution theorem
proves the same exact outputs and memory framing after the actual count
and certification. The full source wrapper costs
`19*P+115*I+108 <= 115*n+108`, including header reads, calls and the
compiler's main entry. As with the other compiled component, word
representation, input layout and admissible word size are explicit promises;
no execution or solver premise is assumed.

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
The expanded check passed: 142 scoped declaration checks covering 140 unique
names, including compiled score selection and dynamically counted certification, the three
compatibility files and the canonical ledger adapter, with the same
standard axiom allowlist. The checked source/configuration hash and full
compiler output are in [`verification-output.txt`](verification-output.txt).
The improved Light min-plus solver and its complete execution-cost
domination hypothesis still have to be supplied. In particular these routines
have not yet been assembled into a full canonical composite-selection loop
with an implemented equality oracle and bit-scaled min-plus caller.

The next lowering target is the existing main project's
`BinaryLowEncoder.Instruction` and its `runInstructions`/`rowBlock` loops:
connect that explicit instruction language to actual Light code with array
layout, transient word bounds, framing and cost domination. The main
project's higher-order `Counted`/`Result` values carry ghost counters rather
than a target-code syntax; those counters alone do not instantiate a
compiler. The active binary cyclic multiplier uses `BinaryArrayFFT`, so
lowering only the earlier Toom engine would leave that implementation gap.

The adapter alone does not close the improved APSP theorem. The new backend
must still implement and prove the shared-cache equality oracle, fast cyclic
coefficient arithmetic, composite-selection controller, and bit-scaled
min-plus caller with actual array layouts and execution costs.

