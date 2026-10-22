# Comparison with the numbers displayed in the source paper

Source: Alman and Vassilevska Williams, arXiv:2610.06783v1. Every row below pairs a number the source displays with this repository's current certified bound under the same guarantee and input type. Bounds are from `outputs/exponent-improvement.tex`; the source numbers are quoted from the paper text (theorem numbers in parentheses). The source paper states that its authors found slightly better exponents and omitted them, so this is a comparison with displayed numbers, not a priority claim. The asymptotic algorithms are not peer reviewed or fully formalized. The local evidence consists of the exact rational interval certificates and finite checks run by `python3 scripts/verify.py`, plus the separately scoped [Lean checks](../lean/README.md).

## Source headline numbers that are improved here

| Problem | Source | Here | Guarantee, inputs |
| --- | --- | --- | --- |
| Wanted entries of an `N x D` by `D x N` product, `N >= D^18`, `|W| <= N^2/sqrt(D)` (Thm 1, Cor 26) | `O(N^2/D^0.063)` | `O(N^2/D^0.0991)` (five-term data structure; ten-term analysis `0.07195`) | Deterministic, integer entries |
| Thin-product data structure, single-entry query (Thm 3) | `O(D^0.437)` | `O(D^0.4009)` (five-term; ten-term `0.42805`) | Deterministic |
| Thin regime at query density `|W| <= N^2/sqrt(D)` | positive saving only for `D <= N^0.1204` | positive saving up to `D <= N^0.129` (`O(N^2/D^0.0001)`) | Deterministic |
| Integer 3SUM (Thm 2, Thm 22) | `O(n^1.9992)` | `O(n^1.9931055)` | Deterministic; fixed-bucket count refinement and aligned cyclic histograms |
| Integer Exact Triangle, decision, search, and all-edges (Thm 2, Thm 19) | `O(n^2.9983)`, precisely `O(n^(3-0.00175) log n)` | `O(n^2.9926862626)` | Deterministic; exact-half sources and shared completion using Majdoddin's framework and the SODA 2024 CW theorem |
| Integer min-plus product and APSP, no negative cycles (Thm 2, Thm 22) | `O(n^2.9995)` | `O(n^2.9926862626)` | Deterministic; same additional dependency |
| Zero-, Min-, Max-Weight `k`-Clique, integer weights (Cor 39) | `O(n^(k - 0.0017 floor(k/3)))` | `O(n^(k - 0.00705208 floor(k/2.046046346)))` via the lopsided five-term construction (`4.98589584` for `k = 5`); chunking alone gives `floor(k/3)` | Deterministic, every fixed `k >= 3` |
| Real 3SUM (Thm 2, Thm 35) | `O(n^1.998)` | `O(n^1.993805)` (ten-term: `1.996001`) | Las Vegas expected, real RAM with comparisons, additions, subtractions |
| Real APSP, min-plus product, Exact Triangle (Thm 2, Thm 35) | `O(n^2.998)` | `O(n^2.993805)` (ten-term: `2.996001`) | Las Vegas expected |
| MonoConvolution (Section 1) | `O(n^1.4999)` | `O(n^1.498271)` deterministic (All-Integers 3SUM at the full saving; the half-saving transfer gives `1.4991368`) | Integer sequences |
| Hinted OMv, `v`-hinted and `Mv`-hinted forms (Thm 4, Cor 40) | phases `n^(2-0.063 tau)`, `n^(1+0.437 tau)` for `tau < 1/18`; general limit `tau < 0.1204` | phases `n^(2-0.07195 tau)`, `n^(1+0.42805 tau)` for `tau <= 1/18`; refuted up to `tau <= 0.145` | Deterministic |
| Hinted uMv (Cor 40) | explicit exponents for `tau_1 < tau_2/18`; general limit `tau_1 < 0.1204 tau_2` | same improved exponents for `tau_1 <= tau_2/18`; refuted for `tau_1 <= min(0.1726 tau_2, (1 + tau_2)/13.8)` | Deterministic |
| Negative Triangle, Min-Weight Triangle, Metricity, min-plus verification, Diameter, Radius, Median, Wiener index, directed Minimum Weight Cycle | `O(n^2.9995)` through APSP | `O(n^2.9926862626)` deterministic, hence also Las Vegas; real weights `O(n^2.993805)` Las Vegas | Integer weights unless stated |

The earlier `2.99294792` construction uses the good-set and composite-certification framework of [Majdoddin, arXiv:2610.17420v1](https://arxiv.org/abs/2610.17420v1), which reports `n^(2.9945+o(1))`. We separately prove a modified five-term identity and Walsh embedding, then cache its polynomial baseline and channel forms jointly across both physical halves. The residual exponent is `Q=2H(theta)/ln4` and the encoder exponent is `E=T+Q`; original tile geometry still uses `T`. Recover each integer cyclic-ring output by exact coefficientwise division of its complete numerator by `4^L`. Every cyclic coefficient is charged in preprocessing and residual contractions; stored-box queries read one precomputed coefficient. The 47-inequality certificate checks all candidate costs and both direct/cyclic phase endpoints. The historical partial-cache `2.993401`, cyclic-fiber `2.993441`, and fixed-profile `2.993676` proofs retain their valid 58-, 48-, and 29-inequality certificates. No unrestricted bound below `2.99` is claimed.

The earlier `2.9926863` construction adds deterministic small-bias translations, a rare-support crop, grouped subset-selector completion across middle blocks, and a separate jointly capped high-box encoder. Its rectangular algorithm is a derived level-one specialization of Proposition 5.1 and Theorem 3.2 of [Vassilevska Williams, Xu, Xu, and Zhou](https://arxiv.org/abs/2307.07970v2), with a fixed positive allowance. The canonical 61-inequality certificate includes original geometry, source roots, all phase costs, and independent batch fits. Counting and other separately parameterized transfers retain their earlier witnesses.

The exact-half source refinement strengthens the cap to `floor(m/2)` using a deterministic shrinking-bias list. Its separate 61-inequality witness gives `2.9926862626`. The change from the preceding displayed exponent is small and largely numerical; it preserves the same external dependencies and geometry/query bottleneck.

The earlier `2.9958892` deterministic APSP construction combines per-pair modular moments, direct-sum batching, prefix-contracted queries, and cyclic lazy encoding with the rectangular bounds in [Vassilevska Williams, Xu, Xu, and Zhou, SODA 2024](https://arxiv.org/abs/2307.07970v2). It improves the previous `2.996261` witness. The new square-instance parameters do not replace the separately certified clique splits.

## Separate conditional statement, not counted as a bound

Assuming Corollary 1.2 and Lemma 6.1 of [Uznański, arXiv:2610.10494v2](https://arxiv.org/abs/2610.10494v2), the ten-term construction would give deterministic `O(n^2.9958323)` for integer all-edges Exact Triangle, min-plus product, and APSP. That preprint is unrefereed and self-described as Codex-generated, and its stated bound `omega(1,k,1) <= 1 + k + 1/(4k)` evaluated at `k = 1` would give `omega <= 2.25`, far below the `omega < 2.371339` bound in the pinned [arXiv:2404.16349v2](https://arxiv.org/abs/2404.16349v2). This comparison uses the pinned version, rather than a rounded value or a newer numerical refinement. The conditional figure is recorded for completeness only; it is superseded in any case by `2.9926862626`.

## Bounds stated here for which the source displays no number

| Problem | Here | Guarantee | What the source says |
| --- | --- | --- | --- |
| Integer all-edges Exact Triangle, min-plus product, APSP | `O(n^2.9926862626)` inherited from the deterministic theorem; the direct randomized batched construction gives `O(n^2.995535)`, unbatched `O(n^2.995943)` | Las Vegas expected | Footnote 10 remarks that APSP could keep the full Exact Triangle saving; no number |
| Integer 3SUM | `O(n^1.9931055)` inherited from the deterministic theorem; the direct randomized bucket-pair construction gives `O(n^1.996001)` | Las Vegas expected | Footnote 10 remarks that the direct offline-set-disjointness route keeps the full saving; no number |
| Weighted `k`-Clique, integer weights | `O(n^(k - 0.004057 floor(k/2.02914)))` and 4-Clique `O(n^3.995486)`, both superseded by the deterministic lopsided five-term bound | Las Vegas expected | Only the deterministic Cor 39 |
| Weighted `k`-Clique, real weights | `O(n^(k - 0.006195 floor(k/2.040915)))` (ten-term: `0.003999 floor(k/2.028423)`) | Las Vegas expected | Integer weights only |
| Integer min-plus convolution | `O(n^1.993927)` deterministic and Las Vegas (square five-term tiles) | both | "Truly subquadratic", no exponent |
| #3SUM | `O(n^1.9931055)` | Deterministic exact counts; sets of polynomially bounded integers | "Truly subquadratic", no exponent |
| #Exact Triangle, min-plus witness counting | `O(n^2.99294792)` | Deterministic exact counts via signed-window refinement | "Truly subcubic", no exponent |
| Min-sum subset convolution, `beta`-bit tables | `O(2.995627^n poly(n, beta))` (ten-term: `2.997190`) | Las Vegas expected | Not in this source; Stoian (arXiv:2610.10282v1) displays `O*(2.9987^n)` Las Vegas and `O*(2.9997^n)` deterministic |

## Comparison with Majdoddin, arXiv:2610.17420v1 (October 12, 2026)

Majdoddin's paper uses Schönhage's five-term partial-product tensor, develops the squared embedding that the current deterministic chain builds on, and proves lossless integer reductions of its own. Its displayed numbers and the current bounds here:

| Problem | Majdoddin | Here | Notes |
| --- | --- | --- | --- |
| Thin product, `N >= D^18`, `|W| <= N^2/sqrt(D)` | `O(N^2/D^0.092)`, query `O(D^0.403)` | `O(N^2/D^0.0991)`, query `O(D^0.4009)` | both deterministic; here via the fixed-profile five-term lemma |
| Thin product, `N >= D^14` | `O(N^2/D^0.077)`, query `O(D^0.421)` | `O(N^2/D^0.0853)`, query `O(D^0.4147)` | deterministic |
| Thin regime limit | matrix theorem for every `eps < 0.172` | explicit points only up to `D <= N^0.145` (ten-term analysis) | Majdoddin's universal statement is wider; not reproduced here |
| Integer 3SUM, deterministic | `n^(1.9945+o(1))` | `O(n^1.9931055)` | |
| Integer Exact Triangle, min-plus, APSP, deterministic | `n^(2.9945+o(1))` | `O(n^2.9926862626)` | |
| 3XOR, deterministic | `O(n^1.99451)` | `O(n^1.9931055)`, with exact counts | here ahead |
| 3SUM over abelian groups, coordinatewise dichotomy | treated | not treated here | |
| Real 3SUM | not restated; substituting his matrix theorem into the source's real-input argument keeps a quarter of the saving; keeping the whole saving for reals is left open | `O(n^1.993805)` Las Vegas, full unfolded saving via certified comparison counts | the cited source reduction is Las Vegas; deterministic matrix preprocessing does not derandomize it |
| Real APSP, min-plus, Exact Triangle | as above | `O(n^2.993805)` Las Vegas | |
| Zero/Min/Max-Weight k-Clique, integer | saving `floor(k/3)` times his Exact Triangle saving, i.e. about `0.0055 floor(k/3)` | `0.00705208 floor(k/2.046046346)` via the lopsided five-term construction | here ahead |
| Hinted OMv | refuted for every `tau < 0.172` (Section 10) | explicit exponents for `tau <= 0.145` | here behind on the regime |
| Verification | Python scripts and a Lean 4 formalization (Section 22) | exact rational certificates, finite checks, and an APSP correctness/charged-work theorem in an explicit binary/indexed-array model; compiled word-RAM adapter remains conditional | see [Lean scope](../lean/README.md) |

## Source results not touched here

- Directed unweighted APSP (Thm 34): the source proves `O(n^(2 + mu - eps''))` for an unspecified constant. The record now makes it explicit: deterministic `O(n^2.525754)` from the source's displayed `mu < 0.5275` and `omega < 2.372` alone, and `O(n^2.5251975)` with the table row `omega(1,0.6,1) <= 2.092351` of Alman–Duan–Vassilevska Williams–Xu–Xu–Zhou, against Zwick's `O(n^2.5275)`.
- 3XOR (Remark 23) is now treated: deterministic `O(n^1.9931055)` with exact counts. Knapsack and approximate Subset Sum, Tree Edit Distance, Replacement Paths, Second Shortest Simple Path, Betweenness Centrality, and the other equivalence-class members the source lists without explicit exponents: not restated here, although the known reductions would transfer the bounds above.
- The universal trade-off theorems (Thms 24 and 25, "for every `eps < 0.1204` and every `kappa > 0`") and Table 2 of parameter trade-offs: not extended or recomputed; only the explicit points above are certified.
- The source reports Lean certification of Theorems 19 and 22 and the Zero-Weight case of Corollary 39. The separate [machine project](../machine/README.md) rebuilds the pinned upstream components needed by its adapters; this does not independently recheck every source theorem. The closed Lean APSP theorem retains the `2.99294792` exponent. New exact-half source components are formalized, but the complete `2.9926862626` theorem and execution-cost proof remain unfinished. The main project's improved APSP theorem concerns correctness and charged work in its specified model. Whole-program word-RAM compilation remains conditional.

## Guarantee and input conventions

Deterministic, Las Vegas expected, and Monte Carlo one-sided bounds are never compared across guarantee types. Integer bounds assume polynomially bounded integers; real bounds use only comparisons, additions, and subtractions on reals. APSP assumes no negative cycles.
