# Thin-matrix exponent improvements: results

Working derivations and exact-rational certificates for improvements to the exponents displayed in Alman and Vassilevska Williams, *Truly Subquadratic 3SUM and Truly Subcubic APSP via Triangles in Sparse Lopsided Graphs* ([arXiv:2610.06783v1](https://arxiv.org/abs/2610.06783v1)), and to the five-term follow-up of Majdoddin ([arXiv:2610.17420v1](https://arxiv.org/abs/2610.17420v1)). This repository holds the proof note, exact-rational certificates, finite brute-force checkers, an APSP Lean development, and explanatory pages. The exploratory history lives in the separate research repository.

The current research-note bound for deterministic integer APSP, min-plus product,
and all-edges Exact Triangle is **`O(n^2.9926862626)`**. The source algorithm uses
small-bias middle translations, exact-half rare-symbol caps, grouped residual
completion shared across middle blocks, and jointly capped box encodings.
The change from the earlier `2.9926863` witness is a small numerical refinement;
the original geometry/query bottleneck remains. The two new certificates each
check 61 strict inequalities, and the published finite checks include complete
signed cyclic products. No unrestricted bound below `2.99` is proved here.
The Lean development now proves exact APSP correctness and the complete
`O(n^2.9926862626)` charged-work bound for the constructed program in its
binary-arithmetic and bounded indexed-array/control model, with eventual
address-price sufficiency within its reserved retained layout. The endpoint is
[`ThinMatrix.HalfSourceAPSPTheorem.correctness_work_and_addresses`](lean/HalfSourceAPSPTheorem.lean).
The older `2.99294792` theorem is preserved separately. Counting, 3SUM, clique
and other separately parameterized results keep their existing witnesses.

## Current bounds

All inputs are polynomially bounded integers unless stated; APSP assumes no negative cycles. The 3SUM and exact #3SUM rows below use sets. Deterministic bounds are also Las Vegas bounds. A dash means no separate source comparison is quoted here, not that the source leaves the problem untreated.

| Problem | Source paper | Majdoddin | Here | Guarantee |
| --- | --- | --- | --- | --- |
| Wanted entries of an `N x D` by `D x N` product, `N >= D^18`, at most `N^2/sqrt(D)` entries | `O(N^2/D^0.063)`, query `O(D^0.437)` | `0.092`, `0.403` | `O(N^2/D^0.0991)`, query `O(D^0.4009)` | Deterministic |
| Integer 3SUM | `O(n^1.9992)` | `n^(1.9945+o(1))` | `O(n^1.9931055)` | Deterministic |
| Exact #3SUM | truly subquadratic; no exponent displayed | — | `O(n^1.9931055)` | Deterministic exact counts |
| All-Integers 3SUM | — | — | `O(n^1.9931055)` | Deterministic |
| Integer Exact Triangle (all-edges) | `O(n^2.9983)` | `n^(2.9945+o(1))` | `O(n^2.9926862626)` | Deterministic |
| Integer min-plus product and APSP | `O(n^2.9995)` | `n^(2.9945+o(1))` | `O(n^2.9926862626)` | Deterministic |
| Exact #Exact Triangle and min-plus witness counts | truly subcubic | — | `O(n^2.99294792)` | Deterministic |
| 3XOR, exact #3XOR, per-target counts, `d = O(log n)` | truly subquadratic | `O(n^1.99451)` | `O(n^1.9931055)` | Deterministic |
| Real 3SUM (comparisons, additions, subtractions) | `O(n^1.998)` | not restated | `O(n^1.993805)` | Las Vegas |
| Real APSP, min-plus product, Exact Triangle | `O(n^2.998)` | not restated | `O(n^2.993805)` | Las Vegas |
| Directed APSP with weights of magnitude `polylog n` (incl. unweighted) | some `eps > 0` below Zwick's `n^2.5275` | — | `O(n^2.525754)`; `O(n^2.5251975)` with the table row `omega(1,0.6,1) <= 2.092351` | Deterministic |
| Zero/Min/Max-Weight `k`-Clique, integer weights | `O(n^(k - 0.0017 floor(k/3)))` | `0.0055 floor(k/3)` | `O(n^(k - 0.00705208 floor(k/2.046046346)))`, e.g. `4.98589584` at `k = 5` | Deterministic |
| Weighted `k`-Clique, real weights | — | — | `O(n^(k - 0.006195 floor(k/2.040915)))` | Las Vegas |
| Integer min-plus convolution | truly subquadratic | — | `O(n^1.993927)` | Deterministic and Las Vegas |
| MonoConvolution | `O(n^1.4999)` | — | `O(n^1.498271)` | Deterministic |
| Min-sum subset convolution, arbitrary `beta`-bit tables | Stoian (arXiv:2610.10282): `O*(2.9987^n)` | — | `O(2.995627^n poly(n, beta))` | Las Vegas |
| Min-sum subset convolution, entries of magnitude `n^O(1)` | Stoian: `O*(2.9997^n)` deterministic | — | `O*(2.995124^n)` | Deterministic |
| Hinted OMv conjectures | refuted for hint thinness `tau < 1/18` | `tau < 0.172` | explicit exponents `n^(2-0.07195 tau)`, `n^(1+0.42805 tau)`; refuted for `tau <= 0.145` | Deterministic |

Row-by-row comparisons with every number the source paper and Majdoddin display, including results not touched here, are in [docs/SOURCE_COMPARISON.md](docs/SOURCE_COMPARISON.md). A guided tour of the proof is in [docs/PROOF_OVERVIEW.md](docs/PROOF_OVERVIEW.md).

## What is in the proof

The note [outputs/exponent-improvement.tex](outputs/exponent-improvement.tex) ([PDF mathematical snapshot](exponent-improvement.pdf)) derives every bound above. Current Lean verification status is recorded in [lean/README.md](lean/README.md); the linked PDF remains the mathematical snapshot. Its main ingredients, in order of appearance:

- a sharper binomial-tail analysis and a pruned encoder for the source's box data structure;
- residue folding, which shares band encodings across residues, and amplified independent modular filters;
- direct bucket-pair reductions for 3SUM and certified comparison counts for real inputs;
- conditional modular moments and per-pair certificates for deterministic selection;
- the five-term tensor of Majdoddin with fixed-profile slots, two separately charged encoders, prefix queries, a cyclic or group-algebra coefficient ring, polynomial caches, and a Walsh re-embedded local identity;
- deterministic small-bias and exact-half source caps, shared rectangular completion, and a separate jointly capped box encoder;
- composite incidence certification, read on square and lopsided instances;
- rectangular five-term tiles for convolution and subset convolution, and the explicit directed APSP transfer.

## Verification

Python 3.10 or newer, standard library only:

```sh
python3 scripts/verify.py
```

This reruns fifteen exact-rational certificate scripts (rational interval arithmetic with explicit logarithm bounds), compares their output with the recorded `outputs/*certificate-results.txt`, and runs every finite checker in `outputs/check_*.py`, which test encodings, identities, reductions, and counting constructions on small instances against brute-force oracles. It also runs eight structured-source checks and compares their saved outputs byte for byte; the required import dependencies are included under `work/`. The proof was compiled with tectonic.

Assertions must be enabled: do not use Python's `-O`/`-OO` options or `PYTHONOPTIMIZE`. The runner rejects optimized execution and ignores Python environment flags in its child processes.

For the additional Lean checks, see [lean/README.md](lean/README.md). With the pinned Lean toolchain and mathlib dependencies installed, run:

```sh
python3 scripts/verify_lean.py
```

<!-- exact-half-final-status-v1 -->
The main end-to-end statement is
[`ThinMatrix.HalfSourceAPSPTheorem.correctness_work_and_addresses`](lean/HalfSourceAPSPTheorem.lean).
It proves exact APSP correctness, `O(n^2.9926862626)` charged work for the
complete constructed program, and eventual address-price sufficiency within
its reserved retained layout. Its hypotheses concern the original graph: polynomially bounded
integer edge weights and no negative cycles. Source/setup costs, shared
batching and independent fit, rounded parameters, all phase and repeated-call
costs, and the adaptive APSP caller are connected without a supplied fast
oracle or desired runtime bound.

The final frozen verification passed **612 modules and 5,290
axiom reports**, using only `propext`, `Classical.choice` and `Quot.sound`.
Source/configuration SHA-256: `9d5e9865f2e599654af2082098a609a237ed2208d99adbb14648695b9527b04b`.
See the [complete transcript](lean/verification-output.txt),
[execution model and reproduction instructions](lean/README.md), and
[closed dependency chain](lean/EXACT_HALF_ROADMAP.md#closed-dependency-chain).

The [finite Lean verification record](lean/runtime-verification/README.md)
accounts for all 71 current fixtures: 68 unchanged passes and three targeted
rechecks. Original failures and their corrections remain in the evidence.

The historical
[`BinaryAlignedAPSPTheorem.correctness_and_work`](lean/BinaryAlignedAPSPTheorem.lean)
remains a separate closed `2.99294792` theorem. Earlier extension checkpoints
are retained as historical records, with their then-pending obligations
clearly marked.

## Caveats

- The exponents are asymptotic. The deterministic composite certification uses fixed stage counts whose constants only settle for astronomically large `n`; no practical speedup is claimed.
- The Python certificates verify numerical inequalities and finite instances. The Lean theorem proves correctness and charged work in its specified model, not Lean evaluator performance or a complete compiled word-RAM execution. The separate [word-RAM development](machine/README.md) includes compiled controller components and actual pool/minimum scans; its complete APSP adapter remains conditional on an improved `Light.Solves` implementation and its time bound. The completed `2.9926862626` APSP theorem is within the stated charged-work formalization; other result rows are not proved by this endpoint. Neither the theorem nor its address-layout result is a compiler/allocator correctness proof or a native-runtime performance guarantee. The TeX is current; the linked PDF is the mathematical snapshot described above.
- The `2.99294792` chain and everything after it build on Majdoddin's five-term tensor. The source paper states that its authors found better exponents than they displayed; the comparisons here are with displayed numbers and make no priority claim.
- External numerical inputs are recorded in `sources.json` and in the bibliography of the note.
