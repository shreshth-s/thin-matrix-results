# Scope of the Lean checks

This directory formalizes selected algebraic identities and the numerical
feasibility of the aligned `2.99294792` witness. It does **not** formalize the
complete APSP algorithm or establish its running time independently of the
mathematical arguments in the proof note.

## Reproduce

Install [Lean through elan](https://lean-lang.org/install/). The repository pins
Lean `4.31.0` in `lean-toolchain` and mathlib commit
`9a9483a92959bc92bd6a60176dd1fe597298c1f8` in `lakefile.toml` and
`lake-manifest.json`. From the repository root:

```sh
lake exe cache get
python3 scripts/verify_lean.py
```

The first command downloads the pinned dependencies and mathlib's compiled
cache. Those dependencies are much larger than this results repository.
The verifier builds local imports, checks the three Lean source files with
warnings treated as errors, and prints the axiom dependencies of the listed
declarations. Only Lean's standard `propext`, `Classical.choice`, and
`Quot.sound` are permitted by the runner. No proof uses `sorry`, a custom
axiom, or `native_decide`.

The two core-only files can also be checked without mathlib:

```sh
lean -DwarningAsError=true lean/LocalIdentities.lean
lean -DwarningAsError=true lean/AlignedCertificate.lean
```

The standard-library Python suite remains a separate command:

```sh
python3 scripts/verify.py
```

## Statements covered

- `LocalIdentities.lean` proves six universally quantified commutative-ring
  identities, including the aligned five-term identity (A1), the pencil
  identity (A7), their local rearrangements, and the private specialization
  `H(0) = P_N`. These do not assume that four is invertible.
- `AlignedCertificate.lean` proves the exact rational witness identities and
  recomputes all 47 strict inequalities from the witness constants and three
  compact rational boxes for `T`, `G`, and `q1`. It proves that the affine
  expressions equal the unexpanded phase costs. The interval-to-cost theorem
  in this core-only file is conditional on the three enclosures.
- `RealCertificate.lean` proves the required enclosures for the actual real
  logarithm and entropy expressions using mathlib's proved atanh-series
  bounds and exact arithmetic. It connects these analytic bounds to the
  rational certificate, removing the enclosure assumptions for the 47
  numerical checks. This is a numerical feasibility theorem, not a theorem
  about the existence or running time of an APSP algorithm.
- `generate_aligned_intervals.py` checks consistency with the canonical Python
  witness and its rational intervals. It is a maintenance aid; the Lean
  analytic proof does not assume its output.

## Statements not covered

The Walsh/source embedding, good-set construction, tensor-power contractions,
encoder and cache implementations, intermediate-array bounds, exact division
of complete output numerators, coefficient bit complexity, modular selection,
graph reductions, asymptotic cost accounting, and the final APSP theorem
remain mathematical proof obligations outside this formalization. The other
results and historical numerical witnesses are not formalized here. External
algorithmic theorems cited by the note are also not formalized by this project.

Successful Lean checks therefore do not certify the complete results table,
establish literature priority, or prove a sub-`2.99` APSP bound.
