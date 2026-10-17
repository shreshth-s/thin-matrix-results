# Lean formalization status

The target is deterministic integer APSP in `O(n^2.99294792)`, for
polynomially bounded integer weights and graphs without negative cycles.
The end-to-end theorem is
[`ThinMatrix.BinaryAlignedAPSPTheorem.correctness_and_work`](BinaryAlignedAPSPTheorem.lean).
It proves exact APSP correctness and the complete constructed program's
`O(n^2.99294792)` charged-work bound in the binary-arithmetic and bounded
indexed-array/control model described below. The embedding, complete LOW/HIGH
identity, cache geometry, binary cyclic arithmetic, deterministic certification
and adaptive APSP caller are joined in this theorem. A resource-counter theorem
and a compiled machine execution theorem have different statements.

The final hypotheses concern the original graph only: an integer edge bound
`W(n) <= n^degree` for a fixed degree and no negative cycles. Correctness means
minimum weight over every finite directed walk, with infinity for unreachable
pairs. Successful parameter selection, coefficient/address widths, multiplier
costs, and the oracle's correctness and charged work are proved internally.
There is no assumed fast oracle or desired final cost inequality.

## Reproduce

Install [Lean through elan](https://lean-lang.org/install/). The main project
pins Lean `4.31.0` and mathlib commit
`9a9483a92959bc92bd6a60176dd1fe597298c1f8`.

```sh
lake exe cache get
python3 scripts/verify_lean.py
```

The verifier compiles every top-level `lean/*.lean` module in local dependency
order, treats warnings as errors, and checks every listed `#print axioms`
report. Only `propext`, `Classical.choice`, and `Quot.sound` are allowed.
It checks every dependency revision and rejects modified or nonignored
untracked dependency sources. It fails if the source changes during the run
and prints a SHA-256 identifying the checked sources, configuration and
numerical interval-generator inputs. The successful transcript is
[`verification-output.txt`](verification-output.txt). Build products and
dependency downloads are excluded from the repository.

The recorded frozen-source run compiled 135 modules and checked 1,928 axiom
reports, all containing only the standard axioms above. The transcript records
the source/configuration hash; `sources.json` records the same digest.

The independent numerical and finite-instance suite uses only Python's
standard library:

```sh
python3 scripts/verify.py
```

Passing finite tests does not prove the asymptotic theorem. The Lean results
are the checked theorem statements, including their explicit hypotheses.

## Main components

| Components | Scope |
| --- | --- |
| `LocalIdentities`, `TensorContraction` | Aligned local identity, arbitrary entangled contractions, shared-channel LOW expansion, residual weights and exact LOW/HIGH partition. |
| `GoodSets`, `GoodSetConstruction`, `GoodMapRuntime` | Good-map density and an actual deterministic vector/bit-score construction. The implemented exhaustive kernel tests have their own charged bound; they do not claim Gaussian-elimination costs. |
| `WalshEmbedding`, `RawWordBijection`, `GoodMapEmbedding`, `CompleteThinProduct` | Constructed raw sources contract to `4^L` times the original product. Matching runs, opposite-index Walsh transforms, normal weights and the transpose-Delta locator are preserved. |
| `CacheBounds`, `CacheCardinality`, `CappedEnumeration`, `EntropyBounds` | Exact retained states, directly generated capped prefixes, every intermediate suffix-array volume, and rounded entropy bounds. |
| `SharedEncoder`, `SparseLocalForms`, `SourceFormation`, `CacheDenseLowering`, `CachedLowQuery` | Stored source/encoder arrays, literal sparse integer rows, shared materialization, direct channel enumeration, selected cyclic dots, weights and equal-run query correctness. LOW is prepared once per input band. |
| `HighBoxDP`, `HighBoxEntropy`, `StoredHighDP`, `ArrayKeys`, `HighBaseEncoder`, `HighQueryKeys` | Capped ordered HIGH recurrence, stored complete cyclic vectors, explicit trie keys, pruned mask generation and direct four-way query keys. Stored HIGH coefficient reads do not scan all cyclic slots. |
| `RowIndexing`, `SourceCoordinates`, `ThinMatrixBackend` | Original flat matrix inputs, padded shared bands, cached maps/dimensions/locators, and complete prepared queries equal to original cyclic matrix products. Reference helpers are distinguished from stored production paths. |
| `CyclicRing`, `PolynomialCyclicFold`, `BackendNumeratorBounds` | Exact integer cyclic semantics and division of the complete LOW-plus-HIGH numerator. Individual terms need not be divisible; arbitrary-ring decoding when four is noninvertible is not asserted. |
| `IntegerArithmetic`, `FixedPointComplex`, `RootsApproximation`, `RationalWorkBounds`, `FFTBitCost`, `BinaryArrayFFT`, `BinaryMultiplierAdapter` | Exact binary arithmetic, bounded-precision roots/FFT with proved error and exact recovery, and a guarded full-vector cyclic multiplier with a proved `q·polylog(qA)` bit/control allowance. The fast branch is proved reachable for the actual bounded HIGH operands. |
| `ToomCook`, `ToomBitCost`, `ToomExecutionBound`, `ToomCyclicBit`, `BitArraySimulation`, `BitArrayCost` | Separate exact Toom multiplication developments, including recursive binary-array execution. Their public statements distinguish pre-padded kernels and cyclic/native boundary wrappers. |
| `PipelineBitBounds`, `AdaptiveQueryBitBounds`, `AdaptiveBitBounds`, `CacheSchemaBitBounds`, `GlobalAddressBitBounds`, `BackendScalarBits` | Source/cache/HIGH/LOW intermediate widths, adaptive graph-query bounds, factorial temporaries, complete numerator division, global allocation addresses and actual local binary primitive prices. Local primitive bounds alone do not prove whole-program simulation. |
| `FoldedCounts`, `CompactBlocks`, `FoldedBackendExecution` | Literal physical factor three, compact original-label blocks, padded 0/1 cyclic sources, one shared preparation per block and retained window-query results equal to modular incidence counts. |
| `PrimePool`, `CompositeCertification`, `ArrayCompositeAlgorithm`, `CountedArrayComposite`, `DenseControllerExecution`, `FactorValidation` | Proved prime-pool density, exact certification, actual array/scalar controller loops, retained producer results from one call, and explicit factor validation/prefix-suffix products. |
| `MinPlusReduction`, `APSPReduction`, `APSPAlgorithm`, `StoredMinPlusAPSP`, `CountedEndToEndAPSP`, `AlignedAPSP` | Bit scaling, sentinel/tie conventions, repeated squaring and APSP correctness. `AlignedAPSP.run_correct` uses the concrete aligned producer and binary cyclic multiplier; it assumes no separate correct fast-oracle hypothesis. |
| `AlignedCertificate`, `RealCertificate`, `ArithmeticSlack`, `PhaseGeometry`, `ComputableParameters`, `ComputedPhaseGeometry`, `ReductionCosts`, `BackendCostRefinement`, `ComputedReductionCosts`, `UniformAPSPBound` | All 47 checks for real entropy expressions, integer parameter rounding, actual candidate geometry, complete phase ledgers and strict slack. Intermediate interfaces expose their premises; the final binary theorem discharges its execution-cost premises. |
| `BinaryBackendExecution`, `BinaryBackendCosts`, `BinaryTriangleExecution`, `BinaryTriangleCosts` | The same retained binary source, shared LOW cache, HIGH table, requested coefficients and complete numerator division; bounded folded formation and actual certification histories; complete phase costs with no final width, multiplier or oracle-cost premise. |
| `ParameterExecution`, `ParameterMetadata`, `BinaryAPSPCaller`, `BinaryAPSPHostTotalCosts`, `BinaryAlignedAPSP`, `BinaryAlignedAPSPCosts`, `BinaryAlignedAPSPTheorem` | Charged parameter selection and retained metadata, adaptive binary min-plus/APSP calls, host arithmetic and output writes, and the final closed correctness and charged-work theorem. |

The additional `Binary*` integration modules construct persistent bit-cell
sources, encoders, queries, tables and callers. Their individual refinement
statements are part of this library; the final status is governed by the
end-to-end statement, not by the number of modules or successful checks.

## Execution model

The main operational developments use explicit bit operations and indexed
array/control actions. Their counters describe that model, not elapsed time
of Lean's native compiler or persistent-array implementation. Intermediate
coefficient arithmetic uses stored binary cells and charged primitives;
denotational integer views are used in correctness proofs.

The final theorem bounds the actual returned counter of the same retained
execution, including setup, input formation, intermediate arrays, source-band
sharing, complete cyclic-vector preprocessing, queries, controller work,
host arithmetic and output writes. Fixed pricing constants may depend on the
fixed polynomial input promise. Their analytic choice is a proof parameter;
the program's answers do not depend on that price.

The control charges and bounded-address interpretation are explicit resource
annotations. The main project does not prove a semantics-preserving compilation
of the whole program to word-RAM instructions. Consequently the theorem should
be described as correctness and charged work in this model, rather than a
machine-certified runtime or a performance claim for Lean's evaluator.

## Separate word-RAM adapter

The [`machine/`](../machine/) project independently pins Lean `4.33.1`, the
source paper's [formal-math word-RAM development](https://github.com/anthropics/formal-math/tree/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp), and its own mathlib revision.
It contains actual Light controller primitives and compiler/host composition
lemmas. The improved `Light.Solves` min-plus implementation, polynomial needs
and full time domination are still premises of its adapter. The main verifier
does not check that project; follow its own README and verifier.

Other results in the results table and historical witnesses are outside this
APSP formalization. These checks establish neither priority nor peer review,
a practical speedup, or an unrestricted sub-`2.99` APSP bound.
