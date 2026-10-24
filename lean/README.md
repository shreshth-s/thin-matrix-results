# Lean formalization status

The current closed theorem proves deterministic integer APSP in `O(n^2.99294792)`, for
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

## Exact-half extension in progress

The requested end-to-end target is `O(n^2.9926862626)`. That theorem is
**not yet proved in Lean**. The existing closed APSP theorem above retains
`2.99294792`; its parameters and cost proofs have not been relabeled.

The dependency audit and finite ordered completion path are recorded in
[EXACT_HALF_ROADMAP.md](EXACT_HALF_ROADMAP.md). The closed theorem imports none
of the exact-half extension modules; the roadmap distinguishes connected
subprograms from the missing links to original graph inputs.

The latest finite endpoint is
[`GraphFoldedCountCorrect.finite_modCount`](GraphFoldedCountCorrect.lean):
the actual new LOW/HIGH program, exhaustive band/block schedule and binary
coefficient collection return the original graph-incidence modular counts.
A finite fallback plan is constructed internally (`L=m,t=0`), so no valid-plan
or answer premise is supplied at that endpoint. It is not the optimized
rounded plan. Global binary setup/address pricing, efficient graph batching,
the combined rectangular resource theorem and caller complexity remain unproved. See the final
checkpoint below for exact cost and runtime limits. The latest setup repair
retains translation numerator arithmetic and binary character-sum updates in
that same executed program; it does not close the remaining speed proof. The earlier
rectangular milestones include exact rational extraction from the CW16 polynomial
degeneration, with a computable dense integer bilinear evaluator and explicit
integer-arithmetic and retained-value bit bounds. The extension also
proves the six CW block identities and constructs finite independent copies by
coordinate filtering and collision cleanup, tied to that exact decomposition.
Exact finite hash-fiber counts and a quantitative bound for the actual
symmetric cleanup are now proved. Type-class regularity, exact multinomial
counts and a concrete prime choice now give a retained-copy bound equal to
the smallest marginal class size times the supplied progression-free bucket
density, divided by 24. A concrete exhaustive modular bucket construction now
satisfies the Behrend density bound, yielding an unconditional finite
cleanup bound with explicit length-dependent loss. The actual rational target
marginal entropy bounds now absorb this loss and prove the exponential
independent-copy rate, including exact integral scales and floor boundaries.
The level-one equal-copy rank conversion and retained recursive evaluation
are now proved, including binary primitives, intermediate widths, exact
denominator recovery and matrix coordinates at tensor-power dimensions; see
[the current checkpoint](#retained-recursive-execution-checkpoint).
Arbitrary-size padding and integer size bounds are now proved; see the
[padded matrix checkpoint](#padded-matrix-execution-checkpoint). Binary depth
selection, tensor address codecs, a uniform scalar bound for the actual CW
program, and a shared rectangular completion adapter are now proved; see the
[shared completion checkpoint](#shared-rectangular-completion-checkpoint).
Integrating all address costs, the optimized graph schedule and the final
APSP bound remains unfinished.

The following new source components are formalized:

- `LightSourceIdentities` and `ShiftedSourceEmbedding` prove the shifted
  identity and preservation of the complete raw Walsh contraction over a
  commutative ring, with the original source arrays and degree filters.
- `HalfSourcePotential`, `HalfSourceGreedy`, and `HalfSourceList` construct
  the rational greedy translation list and prove its strict small-bias bound
  for every positive `m`. The list has `64*m^3` entries, uses base
  `1+1/(4*m)`, and has bias strictly below `1/(2*m)`. The bitwise selector
  compares two closed conditional scores and resolves ties toward false.
  It does not search all completed translations or assume a small-bias oracle.
- `HalfSourceCoverage` and `HalfSourceSelector` prove exact
  `floor(m/2)` affine coverage, including both parities of `m`, and selection
  of the first valid **list index**. Repeated translation values are retained.
- `TranslatedSourcePartition`, `MaskedLightSources`,
  `CroppedSourceContraction`, and `TranslatedCroppedEmbedding` prove the
  original-coordinate mask partition, preservation of normal-source zeros
  by the opposite Walsh transform, safe cropping of both opposite sources,
  and the complete scaled contraction after summing all translation pairs.
  The latter theorem uses the repository's constructed good maps and
  transpose locators, with explicit normal-coordinate weight and selector
  validity hypotheses. It does not assert equality of individual cropped
  residuals or HIGH boxes with their uncropped counterparts.

The following integration milestones are now proved:

- `ExactHalfGoodMap` enumerates each good restriction, proves that its actual
  inverse is represented by binary rows, proves row-map surjectivity, and
  identifies inverse-subset cardinality with the original normal P2 weight.
- `HalfSourceScan` and `HalfSourceMaskWork` implement a retained first-valid
  list-index scan and explicit dot/weight evaluators. On stored inputs the
  indexed Boolean/register charge is at most
  `J * (m*(6*m+5) + 4*m + 5) + 2`, including candidate-index generation.
  This is not a binary cost for building good maps, inverse rows, or the list.
- `HalfSourceIntegerScores` uses `A=4*m+1`, `B=4*m`, `K=64*m^3+1` and a single
  denominator `2*(A*B)^K`. It proves exact score and strict-comparison
  refinement, plus the polynomial score bit bound `m+2+A*(2*K)+1` for at
  most `2^m` characters. Summation does not multiply denominators.
- `HalfSourceIntegerGreedy` precomputes the two power arrays and maintains
  character sums and prefix signs through the integer recurrence. Its entire
  output list equals the rational greedy list, including order and repeats.
  Selected bit vectors and character sums are stored in arrays with a
  computable binary enumeration. Prefix signs retain computed decisions.
  This native integer refinement alone does not price bit operations or
  array/control work; the binary refinement below proves the cost of its
  numerator arithmetic.
- `HalfSourceBinaryScores` computes power tables and conditional numerators
  using stored binary cells and charged multiplication, addition and comparison
  circuits. `HalfSourceBinarySelection` enumerates the actual nonzero
  characters, retains selected bits, and proves that its whole output list
  equals the rational list, including order and repeats. Its returned
  **numerator-arithmetic** counter is bounded by an explicit `2^m` times
  polynomial expression. The counter excludes character-sum updates,
  enumeration, row/sign scans, indexing, storage, and loop control; it is not
  yet the complete construction cost.
- `ExactHalfCroppedEmbedding.complete_embedding` composes those results with
  the actual good maps, translations generated by binary score arithmetic,
  and the retained scan result, at cap `m/2`. It has no arbitrary weight function, selector,
  inverse-weight identity, or small-bias premise. The `m=0` case uses one
  empty translation; positive `m` retains every one of the `4096*m^6` pairs.
- `CappedSubsetList` directly enumerates each capped rare support once, with
  exact length `s = sum_{j<=r} choose(ell,j)`. `CroppedGroupedSuffix` proves
  the ordinary suffix transform `(y1+w,y1,y2-w,y2)` equals its signed,
  capped subset-selector sum for arbitrary entangled sources. It also proves
  the raw-volume and mixed-prefix-layer allocation inequalities. These are
  finite identities; retained-cell capped shared prefix execution is now proved below.
- `StoredGroupedCompletion` retains all `2^ell` signed source groups and
  each group's independent selector matrix. Its executable elementary
  completion reconstructs the cropped suffix transform at every requested
  coefficient. Data storage is exactly `2^ell*s*(B*q*F)`, selector storage
  is `M*s`, and output storage is `M*(B*q*F)`, including all batches, cyclic
  slots and formal coefficients. On already stored masks and source groups,
  `GroupedMaskCompletion` and `StoredGroupedCompletion.all_work` bound the
  returned scalar/read/write/control counter by
  `M*(s*(8*C+16)+3*C+20)+20*2^ell+4`, where `C=B*q*F`.
  This is the elementary completion algorithm, with unit scalar additions;
  its bound does not supply fast rectangular multiplication or binary prices.
  Its standalone preparation definitions are unpriced; the counted replacement
  below supplies an actual preparation path.
- `CappedBitPreparation` generates every capped Boolean support once by a
  pruned recursion. Its counter includes root creation, every copied vector,
  intermediate list, map/append traversal and recursion control, and is at most
  `(ell+1)*(8*ell+32)*s`. `GroupedCoordinates` computes signed ternary addresses
  and subset selectors by retained linear scans, with no runtime powers,
  finite-set enumeration or inverse-equivalence lookup.
- `GroupedPreparation` generates both the capped keys and all `2^ell` pair
  keys, retains every signed source group, and forms independent selector
  matrices from Boolean request arrays. `PreparedGroupedProgram` composes this
  preparation with elementary completion. Its `correctness_and_work` theorem
  takes only the actual raw coefficient arrays and requests: no prepared-matrix,
  successful-construction or preparation-cost premise remains. It reconstructs
  every coefficient, preserves duplicate and empty requests, and bounds the
  returned total counter by `totalBudget`. Loop lengths come from retained
  arrays, so binomial cardinality formulas are not evaluated to recover shapes.
  The counter includes preparation, all intermediate-array traversals, source
  reads, scalar negations/additions, selector tests and complete output writes.
  It is a scalar/Boolean/bounded-register bound, not a binary-cost or fast
  rectangular theorem. The raw source arrays and request keys are its inputs;
  forming those arrays from the cropped root/window encoders remains open.


- `BinaryGroupedCoordinates`, `BinaryGroupedPreparation`,
  `BinaryGroupedCompletion`, and `BinaryPreparedGroupedProgram` refine the
  elementary grouped program to retained binary cells. Ternary addresses use
  charged binary multiplication/addition and a charged final decode. Selected
  original integer inputs are serialized once per retained copy, then signed
  and accumulated through binary circuits; semantic intermediate integers are
  never re-encoded. `correctness_and_costs` proves every cropped output
  coefficient and two separate counters from the original coefficient bound
  `A`. With `s=sum_{j<=r} choose(ell,j)` and `C=B*q*F`, binary work is at most
  `2^ell*s*(addressBudget(ell)+C*inputUnit(A)) +
  M*s*C*backendScalarUnit(ell+size(A))`. All partial-sum widths are derived.
  `totalControl` separately bounds support/pair generation, masks, indexed
  reads, intermediate-array traversals and output writes. This is not a full
  binary price for that control counter or a compiled-machine theorem. It
  remains elementary completion, not the required fast rectangular algorithm.

- `BinaryCroppedHighInput` executes the opposite rare-letter crop using a
  binary count and comparison, serializes the cap once, and materializes every
  accepted or zeroed root vector. `ShiftedHighForms` supplies the actual shifted
  binary coefficient ROM: ordinary normal rows exclude `p1`, while the private
  row is `-x1-x2+p1`; its five-term identity is checked.
- `BinaryCroppedHighEncoder` runs the shared, jointly capped encoder on that
  root, in both physical orientations. It proves every stored base coefficient
  from the original raw cells, derives coefficient bounds, and retains all
  intermediate arrays. Their total coefficient cells are at most
  `q*(2*L+1)*baseCount(L,m,t)`. Its charged-work theorem includes crop tests,
  root materialization, all shared contractions and table storage; no
  preprocessed-base or preparation-cost premise remains.
- `BinaryCroppedHighBoxes.correctness_and_work` composes two such encoders
  with full cyclic binary FFT base products and the retained five-child box
  recurrence. It proves every coefficient of every jointly capped HIGH box.
  The magnitude parameter `8^(2*L)*A+1` is actually constructed through binary
  doubling, addition and charged decoding; all arithmetic widths follow from
  the original raw-source bound `A`. The returned counter uses the repository's
  binary-arithmetic and bounded indexed-array/control model. It is not a full
  binary implementation of all indexing or a compiled-machine bound. The
  theorem starts with raw source arrays, not the original graph; Walsh/mask
  formation and integration with the new LOW/window path remain separate.

- `CyclicLightWindow` proves the exact cyclic averaging identity and the
  existence of a window of weight at most `floor(r*ell/k)`. Its disjoint source
  partition commutes with arbitrary finite linear contractions, so window
  components are summed on each input before residual products.
- `WindowSelection` implements a retained first-valid window scan and direct
  base-three decoding. It proves first-index selection, global crop rejection,
  and explicit traversal/register costs. It uses no runtime inverse-equivalence
  lookup or per-coordinate exponentiation. These are bounded-register/control
  costs; modular addresses, counters and division have not been refined to
  binary machine instructions.
- `BinaryWindowPartition` starts from actual row-major ternary coefficient
  arrays. It stores one owner per raw word, shared by all coefficient columns,
  then materializes every window component, including every zero. The selected
  half has the larger channel count, with normal-half ties; its rare budget is
  computed as `cap-max(normalChannels,oppositeChannels)`. The public
  `correctness_and_costs` theorem proves reconstruction of the cropped source,
  each component's window support, preserved magnitudes and separate binary-copy
  and control bounds. Component storage is exactly `k*3^(2*k)*C`, for full
  `C=B*q*F` columns. Binary copies cost at most
  `k*3^(2*k)*C*backendScalarUnit(size(A))`; all owner scans, decoded vectors,
  component traversals and writes have a separate polynomial register/control
  factor. `executeZero` retains one copied component when `k=0`.
  `ordinary_reconstruction` connects these arrays to the shifted ordinary
  tensor transform. The finite distinguished-root support proof below now
  shows that its global crop is lossless for residual sources. Retained binary root arrays, their window adapter, the opposite forward map
  and the window-to-suffix permutation are now connected below. The shared
  prefix encoder remains open. This is not a complete residual oracle.

- `DistinguishedResidualRoot` supplies the shifted private row
  `H(z)=-x1-x2+(1+z)*p1`, singleton opposite factors `2s,w`, and a recursive
  normal contraction equal to its complete tensor sum. The scalar evaluator
  makes at most `3^m` source calls and satisfies
  `2*ringOps <= 5*(3^m-1)`. These are scalar lookup/operation counts, not binary
  costs. The binary refinement below supplies retained words, coefficient
  arrays, opposite scaling, copies and explicit indexing/control charges.
- `DistinguishedResidualSupport` defines the distinguished root on actual
  physical source coordinates, with a layout derived from each distinguished
  set. Its semantic layout uses finite noncomputable enumeration; the retained
  mask layout below supplies a separate computable construction. It proves
  equality to the full normal/opposite tensor contraction and to the sparse
  scalar evaluator. A nonzero root satisfies
  `|C_n|+remainingNormalRare <= cap` and
  `|C_o|+remainingOppositeRare <= cap`. The physical channel sets are subsets
  of the distinguished sets and their sizes equal the counted mask bits.
  These support proofs need no integral-domain or nonzero-factor assumption.
- `ExactHalfResidualWindow` instantiates the normal cap with the actual first
  scan masks and constructed maps for both original Walsh sources. Thus the
  normal crop used in the support proof is redundant on the sources from the
  exact-half embedding. The resulting selected-half cap proves the window
  crop lossless, with normal-half ties, zero roots and empty channel masks.
  Window reconstruction commutes with arbitrary entangled linear queries;
  `coefficient_window_reconstruction` retains every formal degree and every
  cyclic residue. These are semantic/window identities; the binary root-array
  refinement is below. A completed LOW query and the new APSP exponent remain
  unproved.

- `ResidualLayout` builds both retained physical-position lists and all routes
  from an input Boolean mask. Binary increment circuits construct route indices,
  and charged decoding produces the stored indices. Assembly from these routes
  equals the proved layout equivalence. Filtering, position lists, every route
  and bounded-alphabet word copy have explicit indexed-control counts.
- `BinaryResidualPolynomial` and `BinaryResidualLeaf` build full binary
  coefficient blocks from the actual raw Walsh-source trie. They test both
  rare caps with binary cells, write every constant-polynomial coefficient,
  and implement `-a-b+c+z*c` with binary copies, negation and addition. The
  polynomial row is correct at every retained degree and cyclic residue.
- `BinaryResidualContraction` and `BinaryResidualRootProgram` construct a
  complete residual row using those actual readers and layouts, with each
  recursive child computed once. They retain the word/channel copies, encode
  the cap once per row, and perform every opposite doubling on every cell.
  Input magnitude `A` gives magnitude at most `2^mO*4^mN*A` and binary width
  at most `mO+2*mN+A.size`. The closed row arithmetic/control bounds require
  only the original source bound, not a supplied lookup or oracle cost.
- `BinaryResidualArray.execute`, for a fixed pair of channel vectors, constructs
  all `3^(kN+kO)` remaining-word rows and retains exactly `3^(kN+kO)*F*C` coefficient cells, including zeros.
  Shape allocation, ternary decoding, word splitting, each layout construction,
  all row arithmetic and coefficient writes are counted. `execute_coeff`
  identifies every retained formal degree and every column with the complete cropped
  shifted residual contraction; `execute_bits`, `execute_control` and
  `execute_width` prove explicit bounds. Layouts are conservatively rebuilt
  and charged per row. `C` retains every batch/cyclic/request incidence, including
  repeated requests; no coefficient or request quotient is taken. The bit
  bound is `3^(kN+kO)` times the concrete row bound, whose recursive term is
  `3^mN` times an explicit polynomial in dimensions and input width. This is
  a binary coefficient-arithmetic result with separate bounded indexed-control
  counts, not complete binary control pricing or an asymptotic APSP bound.
  This generic theorem covers degrees below supplied `F`; the complete-root
  entry point below now computes sufficient degree space itself.
  Enumeration of all root/channel families, raw Walsh/mask production, and
  the root-to-window/prefix adapters remain open.

- `ResidualPolynomialDegree` proves the existing shifted contraction has
  degree at most `m+D` for degree-`D` leaves, without a domain assumption.
  For the actual constant raw-source leaves its full degree is at most `mN`.
  `BinaryResidualDegreeSpace` computes `mN+1` by binary mask counting,
  addition and decoding, with explicit construction prices.
- `CompleteResidualArray.execute` feeds that computed size into the retained
  root-array program. `execute_polynomial` proves full polynomial equality,
  not merely agreement below a supplied truncation bound. `ResidualRootBridge`
  identifies the same polynomial with the existing physical root when the two
  distinguished sets have equal size, transporting the opposite layout explicitly.
  `execute_support` applies the existing rare-support theorem to the actual
  complete binary output. It stores exactly `3^(kN+kO)*(mN+1)*C` cells and
  includes degree selection in its binary/control bounds. This closes the
  root's sufficient-degree and semantic-support boundary for one channel pair;
  it does not enumerate all families or execute the root/window adapter.

- `ExactHalfWeightTable` constructs inverse weights by scanning retained supported
  subsets and their actual Gamma images. Binary counting computes each candidate's
  weight once; uniqueness follows from the existing good-restriction equivalence.
  No noncomputable inverse is executed. The stored weight table equals the weight
  in `ExactHalfCroppedEmbedding` for every good set and frequency.
- `ExactHalfSourcePlan` constructs the actual translation list, retains its vectors,
  and fills a first-valid index table from those weights. It proves exact equality
  to `scanPick`, including off-good inputs and `m=0`. Runtime enumeration uses the
  numeric count `1` or `64*m^3`; obtaining sizes does not reconstruct translations.
  Its counters explicitly cover inverse-weight bit arithmetic and construction
  after list generation, not complete list state/control or binary addressing.
- `ExactHalfBandSources` caches each original band input once, applies its own
  first-index mask on each side, and forms both binary Walsh sources for all runs
  and translation-index pairs. Every coefficient equals the source used in the
  exact-half embedding. The source-work bound includes both input caches and all
  copies, pairs, runs and cyclic coefficients; it depends on the input magnitude.
- `ExactHalfGraphSources.execute` starts from the callback's stored binary integer
  tables and its existing retained physical-parameter interface. It executes
  folded source formation, band copies, good-map/selector construction and the
  complete pair/run source array. Folded values refine the existing original-input
  specification. The derived band coefficient cap is one, with no coefficient
  premise, and source formation and band-copy work are bounded accordingly.
  This closes the first graph-to-source value boundary for a physical block and
  band pair. It does not enumerate all physical blocks/bands, produce counts,
  integrate LOW/HIGH, or derive the requested asymptotic cost.

- `ResidualFamilyKeys` reads actual retained good codes through an explicit
  quotient/remainder decoder, proves unique coverage of good sets, and directly
  generates joint channel keys with total weight strictly below `t`. Its exact
  cardinality is the required binomial sum, including an empty family at `t=0`.
  Key enumeration and decoding have explicit indexed-control costs.
- `RetainedResidualFamily` builds all complete roots for each generated good-set
  pair and channel key, including zeros. It proves whole-polynomial identities,
  derived coefficient widths, full degree/cyclic storage counts and aggregate
  binary arithmetic/control bounds on these actual arrays.
- `ExactHalfSourceBounds` derives root input magnitude `2^(L+m)` and the normal
  cap from the actual stored graph-source arrays, using their input-derived band
  cap of one. The caller supplies no raw magnitude premise.
- `GraphResidualFamilies.fromInputs` connects original binary callback inputs
  through the preceding source program and all generated root families, preparing
  keys once and retaining both inputs, every translation occurrence and every run.
  Root-phase counters and exact total root/cell counts are proved. Source/setup
  costs, full binary control lowering, outer scheduling and
  the final asymptotic bound remain separate obligations; window execution is
  connected by the following modules.

- `ResidualWindowSource` performs charged binary copies of every retained
  degree/residue cell into degree-major window rows; its indexed allowance also
  covers flattening prefix copies without relying on in-place array append.
- `ResidualWindowSupport` transfers whole-root rare support to those exact
  copied coefficients, proving the selected remaining cap without a supplied
  support premise.
- `RetainedRootWindows` computes both channel weights with binary circuits and
  charged decoding, runs the retained first-window partition, and proves exact
  reconstruction of every column and arbitrary linear contractions. The zero
  residual case retains one copied component without a window search.
- `GraphRootWindows.fromInputs` connects those windows to actual graph inputs
  through the existing retained roots, preserving both inputs and every indexed
  family occurrence. It derives the window input magnitude internally, proves
  aggregate bit/control bounds and counts every retained flat-source/window
  coefficient. The existing physical parameter contract and one-block/band-pair
  scope remain. Binary channel/coefficient work and indexed control are distinct.

- `TernaryWindowAddress` forms ternary row addresses by the existing binary
  scan and charged unsigned decoding. `OppositeWindowLayer` implements the
  forward integer map `(s,v,w) -> (s+v,s-v,-w)` using stored binary operands,
  with every input/output copy charged. It proves the exact local ordinary-form
  identity and preserves every predicate depending only on rare positions.
- `RetainedOppositeTransform` executes each opposite physical axis once,
  retains every intermediate coefficient layer, proves magnitude at most
  `2^k*A`, and sums actual binary arithmetic/address work. Window reconstruction
  commutes with this sequential transform. Its trace contains exactly
  `k*3^(2*k)*C` new coefficient cells; the result references its final layer.
- `WindowSuffixPermutation` proves the concrete cyclic coordinate bijection
  and exact rare-weight transport. `RetainedWindowPermutation` builds both
  retained position tables and copies every coefficient through binary ternary
  addresses. It clamps the window length, includes `k=0`, and preserves the
  selected suffix cap after the actual partition and opposite transform.
- `GraphWindowTransforms.fromInputs` and
  `GraphWindowPermutations.fromInputs` connect both stages to actual retained
  graph-source/root/window arrays for one block and band pair. Both-input
  reconstruction and suffix support are proved for every degree/residue column.
  All translation-list occurrences, runs, good-set pairs, joint channel keys
  and windows remain distinct. Magnitude and phase budgets are derived inside
  the graph entry points, without supplied generated arrays or cost bounds.
  Binary coefficient/address work and indexed control remain separate; these
  are not full binary-control execution theorems. The new prefix program is described below.

The remaining obligations are substantial: finish complete translation-list
state/control pricing and binary lowering of inverse-weight-table/selector
construction, including addresses and storage; execute the outer block/band
schedule with shared setup and sum its work; aggregate the completed root/window queries and build compatible batches; integrate these graph-derived sources with the jointly capped
HIGH and grouped LOW paths; prove strict independent batch fit, rounded entropy
and all aggregate phase costs; supply the rectangular arithmetic algorithm and
its binary costs; and instantiate the adaptive APSP caller. No supplied fast
oracle, desired final cost, or sufficient-degree assumption discharges these.

The rectangular dependency is a genuine missing proof, rather than an
uninstantiated numerical hypothesis. The TeX invokes [arXiv:2307.07970v2,
Proposition 5.1 and Theorem 3.2](https://arxiv.org/html/2307.07970v2) for aspect
`(861/500,1,15)` and exponent `16.7220002`. Those results concern tensor
extraction/degeneration and the asymptotic sum inequality. Closing this gap
requires a tensor/rank formalization, its extraction bound, and an exact finite
bilinear algorithm with coefficient growth and binary costs. The library's
`TensorContraction.tensor_rank_one_expansion` is a finite expansion identity;
it does not prove that rectangular algorithm. A rational entropy inequality
cannot substitute for these statements. No axiom or assumed fast oracle has
been introduced for this dependency.

These are finite source identities and implementation refinements. The only
closed APSP theorem still proves `2.99294792` in its stated charged-work model.

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
dependency downloads are excluded from the repository. The stored compiler
transcript normalizes trailing whitespace; diagnostics and axiom reports are retained.

The recorded frozen-source run compiled 416 modules and checked 4,337 axiom
reports, all containing only the standard axioms above. The transcript records
the source/configuration hash; `sources.json` records the same digest.

The independent numerical and finite-instance suite requires Python 3.10 or
newer and uses only its standard library:

```sh
python3 scripts/verify.py
```

A focused binary runtime check covers every numerator and conditional term
for `m=1`, strict choices including ties, a four-entry list prefix, the returned
arithmetic counters, and the raw `m=0` list:

```sh
lake env lean -DwarningAsError=true scripts/check_half_source_binary.lean
```

The grouped runtime check exercises `ell=0..4`, every cap through `ell+1`,
every pair-bit group and activity set, duplicate/empty requests, signed input
coefficients, all `B*q*F` output slots and the returned elementary counters:

```sh
lake env lean -DwarningAsError=true scripts/check_grouped_completion.lean
```

The complete preparation fixture also checks the directly generated keys and
groups, all output coefficients against a separate raw-tensor evaluation,
duplicate/empty request arrays, the zero-column boundary and the total
preparation/completion counters:

```sh
lake env lean -DwarningAsError=true scripts/check_grouped_preparation.lean
```


The binary fixture checks the same raw-tensor outputs through `ell=4`, both
counters, address construction, original magnitudes and partial-sum widths.
It includes signed/zero inputs, bit-length boundaries through 65536, all full
coefficient slots, duplicate/empty requests and zero-column cases:

```sh
lake env lean -DwarningAsError=true scripts/check_binary_grouped.lean
```

The cropped HIGH fixture checks both orientations through `L=2`, every tested
joint cap and every cyclic slot against an independent raw tensor sum, and
checks retained array volumes and returned work. Through `L=1`, it executes
the binary box recurrence using elementary full cyclic base products and compares
with independent cyclic sums. It covers empty coefficient vectors, zero sources
and setup bit boundaries. The production FFT composition is kernel-checked; its
expensive unreduced root computation is not evaluated in this runtime fixture:

```sh
lake env lean -DwarningAsError=true scripts/check_cropped_high.lean
```

The cyclic-window fixture checks first-index selection through `k=7`, direct
ternary decoding through eight positions, and actual binary partitions through
`k=3` against independent raw-coordinate calculations. It checks all full
coefficient columns, zero writes, storage/counter bounds, channel-side ties,
zero-position and zero-column cases, and bit boundaries. Independent ordinary
contractions include repeated requests; they check the partition identity and
are not an implementation of the still-missing prefix encoder:

```sh
lake env lean -DwarningAsError=true scripts/check_cyclic_window.lean
```

The distinguished-root fixture compares the sparse scalar evaluator with an
independent dense normal/opposite tensor sum for asymmetric physical layouts,
all tested channels and remaining ternary words, cap rejection, zero dimensions,
all 12 retained scalar coefficient columns and duplicated request incidences.
It does not evaluate the noncomputable layout or a binary polynomial root program:

```sh
lake env lean -DwarningAsError=true scripts/check_distinguished_root.lean
```


The binary residual fixture checks every mask through `L=6`, actual retained
layout routes and both binary searches, coefficient rows at bit boundaries
through 65536, and full root arrays through `L=2`. An independent dense tensor
reference uses binomial coefficients for products of `(1+z)` and enumerates
all normal/opposite letters. It checks asymmetric channel counts, crops, all
four formal degrees, all nine residue/request columns with duplicate requests,
zero dimensions, input-derived widths, and both counters. It invokes no FFT:

```sh
lake env lean -DwarningAsError=true scripts/check_binary_residual.lean
```

The complete-root fixture checks binary degree-space selection for every mask
through `L=7`, whole stored polynomials against independent dense coefficients
through `L=2`, zero tails beyond the chosen degree, and nonzero highest-degree
examples through `L=3`. It also checks full storage, costs, duplicate columns,
zero dimensions and integer bit boundaries:

```sh
lake env lean -DwarningAsError=true scripts/check_complete_residual.lean
```

The exact-half source fixture checks inverse weights against independent subset
and parity enumeration through `L=3`, the full translation list and first-valid
masks, zero dimensions, signed Walsh coefficients and binary magnitude boundaries.
Its first fourteen phases passed. The final actual graph-input case, including
all 4,096 translation pairs, did not finish within a 30-minute runtime budget
and was stopped; this fixture is **not recorded as fully passing**. All universal
graph/source coefficient and multiplicity results passed the complete kernel
verifier. See `exact-half-source-runtime-check.txt` for the exact coverage.

```sh
lake env lean -DwarningAsError=true --run scripts/check_exact_half_sources.lean
```

The bounded root-family fixture exercises decoder inputs through `L=7`, strict
joint channels through `m=5`, every family coefficient through `L=2` against an
independent dense/binomial reference, all zero cases and duplicate columns,
bit boundaries and the complete two-input container at `m=0`:

```sh
lake env lean -DwarningAsError=true --run scripts/check_residual_families.lean
```

It does not execute the previously incomplete full graph-source or first-pair
runtime cases, or the production FFT. Graph-input composition is kernel checked.
Root arithmetic and indexed-control bounds are separate from a complete binary
control implementation and the requested asymptotic APSP theorem.

The bounded root-window fixture adds independent dense coefficient and modular
first-owner comparisons, including all degree/residue copies, binary channel
weights, ties, both selected sides, zero residual dimension, duplicate columns,
empty families/columns, a coefficient bit boundary, and nontrivial remaining
windows through a selected mask pair at `L=4,m=2`:

```sh
lake env lean -DwarningAsError=true --run scripts/check_root_windows.lean
```

It passed under a 180-second process-group deadline. It does not execute the
full graph entry point or production FFT. See `root-window-runtime-check.txt`
and `root-window-statement-audit.txt` for exact runtime and theorem scope.

The independent finite suite also checks support counts and exactly `2^j`
copies per raw word of rare weight `j`, plus all tested mixed-prefix volumes,
for `ell=0..6`. The general exact-copy-count formula is currently a finite
test, whereas the general storage and raw-volume inequalities are Lean results.

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
It contains actual Light pool counting, per-incidence pool minima, selection
and certification routines, compiled controller components, and compiler/host
composition lemmas. The improved `Light.Solves` min-plus implementation, polynomial needs
and full time domination are still premises of its adapter. The main verifier
does not check that project; follow its own README and verifier.

Other results in the results table and historical witnesses are outside this
APSP formalization. These checks establish neither priority nor peer review,
a practical speedup, or an unrestricted sub-`2.99` APSP bound.

The bounded window-transform fixture uses an independent dense product of the
explicit 3 by 3 matrix and an independent coordinate-position formula. It
checks `k=0,1,2`, both selected sides, ties, zero/full/clamped windows, suffix
caps, all retained layers, duplicate request columns, empty coefficients and
the 65536 bit boundary. Actual roots at `L=3,m=2` are checked against the
independent physical tensor coefficient reference. Both-input family traversal
is executed at `m=0`; the full graph entry point remains kernel-checked only.
The suite passed under a 180-second deadline in 7.5 seconds. No expensive graph
or FFT runtime attempt was rerun. See `window-transform-runtime-check.txt` and
`window-transform-statement-audit.txt`.

The new retained-cell capped prefix connection is implemented in
`PrefixCellTree`, `BinaryPrefixContraction`, `RetainedPrefixEncoder`,
`RetainedCappedGroups`, `CappedPrefixProgram`, `WindowPrefixProgram`,
`OppositeTensorBridge`, `GraphPrefixProgram` and `GraphPrefixTensor`.

`GraphPrefixProgram.fromInputs` retains and calls the actual
`GraphWindowPermutations.fromInputs` program once. For every existing family
occurrence and window, it computes `r=(m/2-max(cn,co))*ell/k` with
`k=L-m` and `ell=min(requested,k)`. It groups only the capped suffix supports
before expanding the prefix. It consumes retained binary cells directly,
uses binary sign/address and copy circuits, and retains every shared prefix
intermediate. It never serializes an intermediate semantic integer view.
All formal-degree/cyclic columns and repeated translation occurrences persist.
At zero residual dimension the empty prefix and suffix have one group and
one coefficient row. Zero coefficient columns are also supported.

For `P=2*k-ell`, `H=sum_{j<=r} binomial(ell,j)` and `C=(m+1)*cyclic`,
initial groups contain exactly `2^ell*H*3^P*C` cells. The prefix trace,
including its referenced initial groups, has at most
`(P+1)*4^P*2^ell*H*C` cells. The enclosing record shares those initial groups
and retains previous graph/root/window/transform/permutation arrays as well.
`GraphPrefixProgram.fromInputs_bits` and `fromInputs_control` sum actual
channel-dependent phase budgets; they derive the coefficient bound from the
original graph-source construction. Bit costs cover the implemented coefficient,
sign, copy and ternary-address circuits. Key enumeration, tree traversal,
allocation, radius computation and array control have separate indexed-register
allowances, including a quadratic traversal charge for generated word closures.
These are neither a complete binary-control lowering nor an
asymptotic final phase bound.

`fromInputs_left_query` and `fromInputs_right_query` identify a query of the
retained encoded cells with the full tensor over every ternary word; the
actual graph-window support discharges the crop. The two `GraphPrefixTensor`
original-query theorems carry this identity through the actual coordinate
permutation and opposite transform to the original retained window, for every
formal-degree/cyclic column. `originalForms_value` exposes the unchanged normal
forms and the explicit transpose of the opposite matrix. Together with the
prior lossless window theorem, these specify the coefficient data needed for
LOW completion. `CappedPrefixProgram.query` is a mathematical specification. The new
`GraphPrefixCompletion` path below now executes these sums for actual folded
requests on one selected oriented root/window. Full-root aggregation remains.

The bounded independent fixture is `scripts/check_prefix_encoding.lean`:

```sh
lake env lean -DwarningAsError=true --run scripts/check_prefix_encoding.lean
```

It compares every group/prefix label/suffix query in its selected small
instances with a direct dense four-by-three tensor sum, and checks actual
root/window/opposite/permutation/prefix construction against the independent
physical-root reference. It includes zero dimensions, empty coefficients,
duplicate columns and the 65536 bit boundary. Full graph entry points are
kernel checked; this fixture executes the enclosing both-input container only
at `m=0`. No incomplete expensive graph or FFT runtime attempt was rerun.
See `prefix-encoding-runtime-check.txt`, `prefix-encoding-statement-audit.txt`
and `EXACT_HALF_ROADMAP.md` for the verification evidence and exact gaps.


## Executed prefix completion from graph requests

`GraphPrefixCompletion.fromInputs` retains `GraphPrefixProgram.fromInputs`
once, generates every folded request from the original binary target table,
and decodes its physical ordinary labels using the retained shape and Delta
columns. It retains the band/row/column and cyclic coefficient tags; no request
is discarded or deduplicated. For a selected oriented root/window it constructs
residual position arrays from the actual retained masks, materializes residual
labels, applies the opposite-form conversion, and reads the retained forward
window permutation. Right-oriented roots use the right physical coordinates
for their normal positions and left physical coordinates for opposite positions.
The pending outer root scheduler must select the corresponding swapped mask pair.

`PrefixCompletionMatrices` copies every retained prefix leaf into a concrete
support-by-coefficient matrix, in a four-way prefix tree, once per pair key.
`PrefixRequestKey` decomposes each transported request and scans the actual
retained pair keys. `PrefixCompletionProgram` builds its Boolean selector row
and performs elementary binary additions over the selected matrix. It retains
all output columns, duplicate request occurrences, selector rows and labels.
For prefix length `P`, suffix length `ell`, support count `H`, and `C` complete
formal-degree/cyclic columns, the additional matrix bank has `4^P*2^ell*H*C`
coefficient cells. `M` requests retain `M*H` selector entries and `M*C` outputs.
Existing source/group/prefix traces remain retained and shared by reference.

`GraphPrefixCompletion.fromInputs_tensor` proves, for every original folded
request and every retained column, that this executed binary output equals
the full tensor on the original graph-derived window. No source-support,
prepared-matrix, query-correctness or desired-cost premise is supplied.
`WindowCompletionRequests.ordinary_forms` identifies both local forms with
the original normal/opposite Walsh forms. The empty-request, empty-column and
zero-residual cases are supported.

`fromInputs_newBits` includes binary target/geometry formation, matrix copies
and completion additions, deriving all coefficient widths from the graph
source. Its target-table width is the sum of all input-cell bit widths, a
conservative finite bound. Final caller pricing must sharpen this using the
existing per-cell `BinaryFoldedTargets.requests_cost` bound; the sum-width
estimate alone does not prove the desired phase exponent. `execute_control` includes physical request decoding, residual positions
and labels, orientation/permutation, pair scans, selector construction, matrix
tree copies/traversal and full output work as indexed-register/control charges.
The `newBitSteps`/`newControl` fields explicitly exclude previously retained
source/root/window/prefix preparation, whose counters stay in the graph field.
They are finite subprogram bounds, not a binary-control lowering, native Lean
execution bound, fast rectangular cost or complete APSP phase bound.

The scope is one physical block/band pair and one selected oriented
root/channel/window, completed for every request. Requests for other bands or
root masks are retained with tags; filtering and full-root/channel/window
aggregation have not been implemented here. Batch fit, fast rectangular
completion, LOW/HIGH count assembly, outer scheduling, entropy/phase bounds
and adaptive caller integration remain open. The closed theorem still proves
`2.99294792`; the requested `2.9926862626` is not proved.

The independent bounded fixture is `scripts/check_prefix_completion.lean`:

```sh
lake env lean -DwarningAsError=true --run scripts/check_prefix_completion.lean
```

All 16 groups plus completion passed in 7.6 seconds under a 180-second deadline.
It checks all labels for `P,ell=0,1,2`, caps through `ell+1`, duplicated requests
and columns, empty requests/columns, the 65536 boundary, zero residual/window
length, both window orientations, actual folded requests at `n=0,2,5`, and an
actual `L=3,m=2` retained physical root against independent coefficient sums.
Full `GraphPrefixCompletion.fromInputs` is kernel checked, not runtime executed.
No previously incomplete full graph or production FFT runtime case was rerun.
See `prefix-completion-runtime-check.txt`, `prefix-completion-statement-audit.txt`,
`prefix-completion-finite-verification.txt` and `EXACT_HALF_ROADMAP.md`.


## Executed full-root window sum and request selection

Five further modules connect the actual selected-window executions to one
complete oriented residual root/channel for every original folded request:

- `WindowCompletionRows` retains the executed window's matrices, keys,
  selectors and all output columns, then copies those cells into common rows.
- `RetainedWindowCompletion` executes every retained window with the shared
  request vector, retains each copied output, and sums actual binary cells.
  Materialized row references and selectors are charged as indexed control.
- `GraphRootCompletion.fromInputs_contraction` connects that execution to the
  original graph-derived residual root, independently for every formal degree
  and cyclic residue. Target construction and residual projection happen once
  per selected root. Its proof uses the retained lossless window reconstruction
  underlying `RetainedRootWindows.produce_contraction`; no returned query value
  or output-support premise is assumed.
- `RootRequestSelection.fromInputs_value` executes band and good-mask matching,
  copies accepted output rows, and writes zero rows for other requests.
  `fromInputs_selected_masks` identifies the selected actual retained masks
  with the request's decoded physical row/column masks, in either orientation.
  `unique_ranks` proves uniqueness for a request's band and orientation.
- `GraphTargetWidth.prepare_formation_bits` sharpens request-formation pricing
  to the maximum original cell bit width. This is an analysis parameter: the
  circuit does not require an uncharged maximum-width preprocessing scan.

Let `k=L-m`, `s=RetainedRootWindows.slots k` (one slot at zero),
`M=windowQuerySize n`, and `C=(m+1)*q`. From original graph input bounds,
`aggregate_magnitude` and `fromInputs_width` prove each completed window has
magnitude at most `2^(3*k+L+4*m)`, and the final sum has bit width at most
`3*k+L+4*m+s.size`. The same `s`-term bound prices intermediate additions.
The new collector retains `s*M*C` copied window cells and `M*C` summed cells;
original window outputs, matrix banks and traces remain retained as well.
Selection adds another `M*C` output cells, including zeros. Equal requests
stay separate occurrences. No formal degree or cyclic residue is discarded.
Selection occurs after completion, so it does not reduce the earlier work on
unmatched requests. The finite bounds charge all `M` requests for each window;
a final fast schedule must route requests before completion or explicitly
account for that extra work in its batch-fit proof.

`GraphRootCompletion.fromInputs_newBits` includes target/geometry formation,
all per-window matrix/output copies, completion additions and full-window
accumulation, with original-input widths derived internally. Selection's
additional copy bound is `RootRequestSelection.fromInputs_bits`.
The separate control theorems include target decoding, label/layout construction,
window/reference collection, selectors, sums, matching and zero-output writes.
These are indexed-register/control bounds, not binary address lowering or
native Lean evaluation costs. Earlier source/root/window/prefix preparation
remains retained in the graph and has its own counters; it is not silently
included in the new-phase counters.

This is still one physical block/band pair and one oriented root/channel.
It does not multiply the two completed root polynomials, aggregate joint
channels/runs/translation incidences, produce a LOW modular count, join HIGH,
or establish a fast completion/phase bound. Compatible batches and strict fit,
outer sharing/scheduling, complete list/control/address pricing, rounded
entropy/phase bounds, rectangular extraction and adaptive caller integration
remain. The closed APSP theorem is unchanged at `2.99294792`; the requested
`2.9926862626` remains unproved.

Run the bounded independent fixture with:

```sh
lake env lean -DwarningAsError=true --run scripts/check_root_completion.lean
```

All 13 groups plus completion passed in 15.064 seconds under a 180-second
deadline: zero dimensions/window length, all 256 request forms across two
windows for four lengths, both orientations, signed 65536 cells, empty
coefficients/requests/window families, duplicate requests/columns, an actual
`L=3,m=1` residual root with every degree/cyclic coefficient checked against
independent physical sums, and actual folded requests with all tested band/mask
selections and the maximum-cell width bound. Full graph entry points are kernel
checked only. No previously incomplete full graph or production FFT attempt
was rerun. See `root-completion-runtime-check.txt`,
`root-completion-statement-audit.txt`, `root-completion-finite-verification.txt`
and `EXACT_HALF_ROADMAP.md`.


## Paired root products and retained family sums

Nine further modules connect the existing executed root rows to complete
paired products, weighted degree reduction and retained family accumulation:

- `ResidualChannelTranspose` scans the actual retained strict-channel list,
  finds the swapped halves, and proves the resulting index map is an
  involution. The scan is charged, including comparison and half construction;
  repeated translation-list values are not deduplicated.
- `CompletedRootProducts` copies flat rows into formal-degree blocks and
  executes `BinaryLowQuery.polynomialDot` for every output degree and every
  cyclic residue. `execute_polynomial` identifies the entire output polynomial
  with the product, including zero-degree tails and empty input blocks.
- `PairedRootRows` retains both reshaping copies and complete products for
  every request position. `GraphRootProducts.fromInputs_product` connects
  these products to the two actual graph-derived source-root polynomials,
  swapping both good masks and channel halves on the right. Band/mask rejection
  yields a zero product after the already charged completion work.
- `GraphRootProductCosts` derives coefficient bounds and arithmetic/copy
  budgets from original inputs. It includes both target formations, every
  window completion, selection copies and full products. It assumes no answer,
  magnitude or desired cost. The earlier shared graph preparation has its own
  counters and is excluded from the new-phase counter explicitly.
- `WeightedRootProducts` executes the actual signed binomial weight circuit,
  precomputes weights once per product-row array, materializes every shifted
  weighted degree/residue term and accumulates all degrees. The shift by the
  joint channel cardinality occurs exactly once. `GraphWeightedRootProducts`
  counts the actual channel halves and connects this reduction to graph inputs.
- `RootProductCollection` retains child executions, builds actual row-reference
  and selector arrays and accumulates every cyclic column per request.
  `GraphRootFamilyProducts` executes this collector over the strict-channel
  list, all runs, and both translation-list indices for one fixed good-mask
  pair and physical block/band pair. `fromInputs_value` proves equality to the
  corresponding weighted source-polynomial sum. All occurrences remain;
  neither equal translation values nor repeated requests are merged.

With `F=m+1`, `N=2*F-1`, `q=cyclic`, and
`A=slots(L-m)*2^(3*(L-m)+L+4*m)`, each retained product coefficient has magnitude
at most `P=(N+1)*q*A^2`. Its weighted cyclic output has magnitude at most
`t*2^(2*m)*P`. The final fixed-mask family sum is bounded by
`J(m)^2*(2*m+1)*channelCount(m,t)` times that quantity. These bounds price all
intermediate arithmetic. The paired array alone adds `M*(2*F+N)*q` cells,
including both copied inputs and every product coefficient; all completion
traces, weighted terms and family partial sums remain retained as well.

The kernel-checked graph results have no supplied root, answer or cost premise.
They still use the existing physical plan, and they keep earlier preparation
costs separate. Indexed scans, comparisons, array-reference construction and
control annotations are not binary address costs or Lean evaluation costs.
The family executor reuses graph preparation, but repeats target formation
and executes unmatched requests for every leaf; those costs are charged.
No efficient routing or fast completion bound is asserted.

The exact source-polynomial family sum is not yet identified with the complete
LOW residual. The next algebraic connection must reindex the actual channel
keys and masks into `TensorContraction.weighted_low_uses_small_channel_sets`
using the shifted pencil `H(z)=-x1-x2+(1+z)*p1`, transport the actual residual
forms and opposite halves, and join the resulting LOW expression with the
cropped HIGH contribution. The old aligned pencil uses a different baseline
and cannot be substituted unchanged. Matching/aggregation across mask pairs,
shared request setup and batching, strict batch fit, outer scheduling,
`4^L` normalization, complete binary control/translation construction, rounded
phase bounds, rectangular extraction and the adaptive caller remain.
The requested `2.9926862626` theorem is still unproved; the old closed theorem
remains unchanged at `2.99294792`.

The bounded independent fixture is:

```sh
lake env lean -DwarningAsError=true --run scripts/check_root_products.lean
```

All 13 groups plus completion passed in 44.838 seconds under a 180-second
deadline. Independent dense convolution checks all formal/cyclic outputs;
independent signed binomial formulas check weights, shifts and zero tails.
The suite also checks signed 65536 cells, zero dimensions, empty rows/families,
strict-channel transposes for `m=0,1,2`, duplicate requests and finite budgets.
An actual `L=3,m=2` paired residual/window/transform/prefix/completion execution
with swapped masks/channel halves is compared to independent physical tensor
sums for all 16 forms, duplicate and unmatched requests, all five product
degrees and all three cyclic residues. A supplemental audit confirms this
physical case includes nonzero products. Full graph/family entry points are
kernel checked only. No incomplete expensive graph or production FFT case
was rerun. Evidence: `root-products-runtime-check.txt`,
`root-products-statement-audit.txt`, `root-products-finite-verification.txt`
and the frozen full-verifier log.


## Shifted LOW identity for the executed fixed-mask family

Six further modules connect the existing executed weighted family sum to the
shifted LOW functional of the actual cropped raw sources:

- `RetainedChannelPowerset.sum_support` identifies the actual strict retained
  key list with the filtered powerset, proving coverage, uniqueness and the
  equality between support size and the two counted channel halves. This is
  an erased proof reindexing, not an additional powerset enumeration.
- `StoredRootPolynomial.produced_row` identifies the complete polynomial of
  each retained row with its physically assembled root. Equal-dimension casts
  transport the actual layouts without choosing or recomputing new layouts.
- `RetainedShiftedFactor.query_factor` expresses the full stored-row tensor
  contraction as the shifted cache factor of the physically cropped raw input,
  summing every distinguished normal/opposite word and every residual word.
  `rawValue_cropped` connects its coefficients to the actual raw store.
- `ShiftedLowChannelFormula.local_pencil` proves the local physical pencil
  `privateNormal*privateOpposite + z*innerCoefficient`, including the shifted
  `(1+z)*p1` baseline. The right cache crosses the two channel halves.
  `weighted_channels` proves the exact joint-size shift and binomial weights
  over the retained strict list, including empty lists and zero dimension.
- `GraphShiftedRootFactors` applies these facts to actual graph-produced roots.
  It proves the two oriented cache identities and the ordinary-form identity
  with actual physical projected labels. The normal residual alphabet excludes
  `p1`, so its ordinary forms equal the shifted ordinary forms.
- `GraphShiftedLow.fromInputs_value` proves that the already executed collector
  equals the sum of these shifted LOW functionals over every retained run and
  translation-list index, at every cyclic residue. It assumes neither returned
  query answers nor supplied roots, coefficient bounds or costs.

This is a value identity for the existing program, not a new evaluator. All
actual construction, copies, elementary completion, full polynomial/cyclic
products, weights and accumulation retain the derived budgets in
`GraphRootFamilyProducts.execute_bits`, `execute_control` and `execute_bound`.
Earlier shared preparation remains charged by its existing separate ledger.
There is no new runtime polynomial conversion or unpriced preprocessing.
All unmatched requests still execute, and their work is charged. Indexed
control remains distinct from binary coefficient arithmetic and from complete
binary address/control execution costs.

The endpoint is **one mask pair and one physical block/band pair**, with all
runs, translation indices and request occurrences retained. It is not the
full LOW count. Mask routing/aggregation, physical locator and run recombination,
LOW/HIGH assembly and `4^L` normalization, efficient compatible batches/strict
fit, shared setup and outer scheduling, full binary control/translation costs,
rounded phase bounds and adaptive caller integration remain. The uniform exact
rectangular algorithm at aspect `(861/500,1,15)` and exponent `16.7220002`,
including CW extraction/asymptotic-sum machinery and controlled binary costs,
is still absent. The requested `2.9926862626` theorem remains unproved; the
unchanged closed theorem states `299294792/100000000`.

Verification evidence for this checkpoint is in
`shifted-low-statement-audit.txt`, `shifted-low-runtime-check.txt`,
`shifted-low-finite-verification.txt` and `verification-output.txt`.
The bounded runtime reference expands physical letters and the local pencil
using independent integer coefficient lists and cyclic convolution. Five test
groups plus completion passed in 8.007 seconds; the full two-position case has
nonzero independent residue values `[-6272, 21952, -15680]`. An initial
reference-only attempt used partial reads at zero polynomial tails and hit its
180-second deadline; it was terminated and is not counted as passing. The
corrected reference uses explicit zero defaults. It does
not read returned query values to form expected answers. Full graph/family
entry points are kernel checked only; prior incomplete expensive graph and
FFT attempts were not repeated.

Frozen source/configuration SHA-256: `b70a80234bcd5dd03f97f5a4c8ff716d7fe0323898433f9ca90a3884b9ce4bcc`.


## Executed mask, physical locator and shared-degree recombination

Seven further modules connect the fixed-mask LOW program to exhaustive mask
aggregation and the original masked Walsh degree filter:

- `LowRequestLocator` identifies the actual folded physical request, its
  outside geometry and the canonical retained masks obtained from its row and
  column ranks. `sum_masks` proves that exactly one mask pair contributes for
  the matching band pair; all other band pairs give zero. The actual retained
  masks are proved to equal the good sets of the decoded physical rows.
- `GraphLowMaskAssembly.execute` executes every retained good-mask pair using
  the existing family program, retains the children and row-reference tables,
  and accumulates every cyclic coefficient of every request. The program does
  not skip unmatched masks or repeated requests. `fromInputs_value` identifies
  this actual accumulator with the uniquely selected physical-query LOW
  functional, assuming no returned answer or preconstructed source.
- `RetainedDegreeRuns.sum_runs` proves that the actual run array enumerates
  each integer in `[-m,m]` exactly once, including `m=0`.
- `GraphLowRunSources.fromInputs_raw` identifies actual stored coefficients
  with `rawLeftSource`/`rawRightSource` of the retained folded bands, using the
  constructed exact-half translations and first-valid masks. Its normal-cap
  theorem shows the double crop equals the intended opposite-only crop for
  these source formulas. Physical ordinary forms and mask layouts are retained.
- `GraphLowRecombination.fromInputs_value` connects the all-mask executor to
  the integer-run source formula. `ShiftedLowRunFilter` then collapses the
  shared run mathematically: only words with equal signed degrees in `[-m,m]`
  pair, and each such pair occurs once. `GraphLowDegreeFilter.fromInputs_value`
  proves that explicit degree-matched functional for the actual executor.
  Translation-list indices and request occurrences remain separate, even when
  their values coincide. No runtime loop is removed by this proof identity.

Writing `G=card(goodSlots L m)` and `A` for the already derived fixed-mask
family magnitude, the row and final accumulators are bounded by `G*A` and
`G*(G*A)`. `GraphLowMaskAssembly.row_bits` and `execute_bits` sum the actual
child budgets and charge all new binary additions at these widths. Their
control bounds include retained child construction, references, selectors and
all output rows. Earlier shared graph preparation retains its separate
existing costs. The executor still repeats target setup and performs every
unmatched completion; no efficient routing or target phase bound is asserted.
Indexed-register control and binary coefficient/copy arithmetic remain
separate from full binary address/control execution pricing.

The preceding checkpoint covers all good-mask pairs and all runs/translations for one physical
block/band pair, with a concrete physical request and explicit degree filter.
It is still an unnormalized LOW functional, not a complete modular count.
The subsequent physical LOW/HIGH checkpoint below reindexes its assembled source coordinates into the
full physical source-word sum, using vanishing shifted normal `p1` forms on
ordinary positions. Actual cropped HIGH queries now consume the same
retained stores/physical keys; joining them with LOW remains pending. Only the combined
numerator can be proved equal to `4^L` times the matrix product and normalized;
there is no divisibility claim for isolated LOW. Band/block scheduling,
coefficient extraction, efficient batches/strict fit, full binary control,
rounded phase costs, the rectangular implementation and adaptive caller remain.
The old closed exponent stays `2.99294792`; `2.9926862626` remains unproved.

The bounded fixture has two distinct scopes: actual masked Walsh stores for
selected translation pairs, and an exhaustive small mask/run/root/window/
completion collector on synthetic signed inputs with explicit degree filters
and actual physical locators. Seven groups plus completion passed in 35.986
seconds. An independent nonzero degree-matched reference gives
`[-6272, 21952, -15680]`. The graph-wide specialization is kernel checked only.

Evidence: `low-recombination-statement-audit.txt`,
`low-recombination-runtime-check.txt`, `low-recombination-finite-verification.txt`
and `verification-output.txt`. Full graph entry points are kernel checked;
no previous expensive full-graph/first-pair/production-FFT attempt was repeated.
Frozen source/configuration SHA-256: `d1fca8d872a5579f0e045182af3ca75f18bda5eb1658f1ffe87d6011bc1f20bb`.


## Physical LOW reindexing and executed HIGH assembly

Eight further modules connect actual retained sources to both physical-word
interfaces for one block/band pair:

- `PhysicalWordReindex` gives inverse maps between the retained selected and
  residual source coordinates and physical words with no outside normal
  `p1`. `PhysicalOrdinaryForms` proves that omitted words vanish under the
  actual projected shifted ordinary forms. `GraphPhysicalLow.fromInputs_value`
  identifies the executed all-mask LOW accumulator with a full physical-word
  pencil, using the retained masks, outside labels and original band formulas.
- `CroppedHighQueries` executes the shifted jointly capped HIGH encoders and
  full cyclic boxes, then materializes every physical key, reads its table
  cell and accumulates the actual query. Every cyclic residue is computed.
  Requests for other bands are executed before the result is copied or zeroed.
- `GraphHighRun` feeds the actual raw stores retained by
  `GraphPrefixProgram.fromInputs` to that program. Its raw coefficient bounds
  follow from the original graph-source construction, with no supplied answer,
  source bound or fast oracle. `GraphHighFamily` prepares physical requests
  once and retains/accumulates every translation-list occurrence and common
  degree run. It shares the existing graph preparation; those earlier costs
  remain separate and are not silently removed.
- `CountedCyclicCollection` retains children and references and sums every
  request's complete cyclic row. `GraphHighFamily.fromInputs_work` charges
  request formation at the actual target width, every HIGH child, references,
  copies and binary accumulation at proved growing widths. Its `operations`
  bound combines binary coefficient arithmetic with indexed-register control.
  It is not a binary-address machine theorem or the target phase bound.
- `ShiftedPhysicalHigh` proves that the literal binary HIGH coefficient ROM,
  in both orientations, is the shifted physical five-form system. The actual
  heterogeneous encoder grid is reindexed bijectively to all physical source
  words, including zero dimensions. `fromInputs_value` identifies the executed
  HIGH family with the physical-word leaf convolution and actual stored HIGH
  query for every request and cyclic residue.

The preceding checkpoint closed physical-word reindexing and actual HIGH query assembly, but did
not yet prove that the two executed outputs sum to the scaled matrix product.
The subsequent join/normalization checkpoint below now proves that identity.
The remaining finite join must match the LOW selected-position pencil to the
ordered physical support used by HIGH, transport integer forms into the cyclic
ring, and apply the shifted five-term identity with common runs and masks.
Only then can `ExactHalfCroppedEmbedding.complete_embedding` establish the
combined `4^L` numerator and justify executable normalization. Isolated LOW or
HIGH is not asserted divisible by `4^L`.

The bounded fixture passed seven groups plus completion in 5.990 seconds.
It exhausts physical words/labels/orientations for actual masks through
`L=2,m=1`, and compares actual cropped encoders, binary HIGH recurrence, key
queries and selectors through `L=1` against independent literal tensor sums
and an ordinary-label threshold predicate. It covers repeated/rejected
requests, every cyclic residue, zero dimensions, zero raw values and empty
signed collections. The box bases use an elementary full cyclic product in
this fixture; production FFT and the full graph specialization are kernel
checked only. No prior expensive incomplete runtime attempt was repeated.

Efficient compatible batches/strict fit, outer scheduling, complete binary
construction/control costs, rounded entropy/phase inequalities, the uniform
rectangular implementation and adaptive caller remain unresolved. The old
closed theorem still proves `2.99294792`; `2.9926862626` remains unproved.
Evidence: `physical-low-high-statement-audit.txt`,
`physical-low-high-runtime-check.txt`, `physical-low-high-finite-verification.txt`
and `verification-output.txt`.
Frozen source/configuration SHA-256: `eb366ccc35697f6e75c444968ddb9c7d63b2665c0ef6fa0939e3d9ccbb0fc9fb`.


## Executed LOW/HIGH join and exact binary normalization

Ten further modules close the finite physical contraction and normalization
boundary for one retained graph block and band pair. They use the actual
`GraphPrefixProgram.fromInputs` output and both actual executors; no answer,
normalization premise or fast rectangular oracle is supplied.

- `PhysicalSupportProducts`, `PhysicalShiftedForms` and
  `PhysicalLowHighGeometry` identify selected and complementary positions,
  the literal shifted binary ROM, the LOW polynomial pencil, and HIGH's
  ordered physical support. The identities hold over commutative rings.
- `GraphPhysicalQueries` transports the retained raw sources and matched
  query masks to the common geometry. `CroppedHighCyclic` transports the
  entire stored HIGH box sums into the cyclic ring, with convolution for
  multiplication and coefficientwise addition.
- `GraphLowHighJoin.joined_fromInputs` proves that the actually executed LOW
  and HIGH families sum to the same physical contraction. Every translation
  list occurrence, shared integer degree run, request and cyclic coefficient
  is preserved. Rejected band requests still execute and remain charged.
- `CroppedPhysicalContraction` identifies that contraction with the cropped
  shifted Walsh source contraction. `GraphLowHighScale.fromInputs_scale`
  applies the actual exact-half embedding, retained band matrices, decoded
  masks and transpose locators to prove the combined numerator equals
  `4^L` times the retained band product (or zero for an unmatched band pair).
- `BinaryLowHighNormalize` constructs `4^L` by repeated multiplication of
  stored binary cells, retains each complete LOW+HIGH numerator and quotient,
  and divides using the binary floor routine. It proves divisor width
  `2*L+1`, arithmetic bounds at the actual operand widths, and separate
  indexed-control bounds. No intermediate integer-to-bits conversion occurs.
- `GraphNormalizedBand.execute` retains both child executions, row-reference
  arrays, divisor, numerators and quotients. `fromInputs_value` proves every
  normalized cyclic coefficient equals the actual retained band product,
  with no divisibility hypothesis. `fromInputs_divisible` derives divisibility
  only for the complete numerator. `fromInputs_bits`, `execute_control` and
  `fromInputs_highWork` price the new execution from proved graph-source
  magnitudes. HIGH's existing mixed binary/indexed charge remains explicitly
  separate from LOW/normalization arithmetic and indexed-control counters.
  Shared graph preparation retains its earlier separate costs.

The bounded executable fixture passed six groups plus completion in 3.652
seconds. It checks signed exact quotients and retained numerators for
`L=0..12`, a 257-bit divisor (`L=128`), empty request/coefficient arrays,
nondivisible signed floor cases, and independent literal LOW/HIGH threshold
identities for every local letter and threshold at `k=0..2`. Actual exact-half
band-source construction, cropped encoders, binary HIGH recurrence, physical
queries and new normalization are checked at `m=0,L=0..1`, with signed cyclic
products and duplicate/rejected requests. These last cases have no strict LOW
channels; their reference is direct stored-matrix cyclic multiplication.
Their cyclic bases are elementary. General graph specialization, nonzero-m
combined execution and production FFT are kernel checked, not claimed as
completed full runtime tests. Prior expensive incomplete attempts were not
repeated.

The next finite connection is to identify the copied band product with the
requested entry of the original folded matrices, gather the requested cyclic
coefficient, and execute the complete band/block schedule with uniqueness,
multiplicity and accumulation costs. Efficient routing/batches and strict fit,
shared setup, complete binary construction/control costs, rounded phase costs,
the formal fast rectangular algorithm and adaptive caller complexity remain
unproved. The closed theorem is unchanged at `2.99294792`; the requested
`2.9926862626` theorem is still unfinished.

Evidence: `low-high-join-statement-audit.txt`, `low-high-join-runtime-check.txt`,
`low-high-join-finite-verification.txt` and `verification-output.txt`.
Frozen source/configuration SHA-256: `b111c275d763463786ffb13d803493959d92ed240cfe13e289a71ebe3b04713b`.


## Original folded requests and exhaustive retained scheduling

This section records the earlier scheduling snapshot; the setup-charge
omission described here is partially repaired in the following checkpoint.

Eight further modules connect the normalized bands to the original graph
quantities. `GraphFoldedCountCorrect.finite_modCount` has only positive block
width, physical factorization, original binary input tables and an original
incidence index as inputs. Its actual new program returns the exact original
modular count; it assumes neither answers nor a valid parameter plan.

- `FoldedBandTransport` transports actual stored binary band copies, decoded
  local row addresses and zero padding to the original folded matrix product.
  It identifies the selected cyclic residue with the original folded request.
- `FoldedRequestBounds` proves each requested count is nonnegative and at
  most the block width, and that exactly one enumerated band pair matches
  every request occurrence. Equal-valued requests remain separate indices.
- `NormalizedCoefficientCollection` retains the actual graph preparation and
  normalized execution, then copies each requested residue from its retained
  output. It bounds binary copy work using the derived count width and keeps
  indexed control separate. It does not rerun a query to collect its answer.
- `RetainedBandIndices` enumerates bands from the actual stored width, with
  an indexed-register allowance. No binary division cost is asserted.
- `GraphBandSchedule` executes and retains every band pair, including
  unmatched pairs, and sums the copied coefficients using actual binary
  accumulators. `execute_value` proves the complete sum is the original
  folded count. Accumulation bounds sum every child charge and price every
  addition and row/reference array at conservative proved widths.
- `GraphBlockSchedule` retains every graph block, materializes coefficient
  reference arrays and copies answers into the original incidence ordering.
  Its nonnegative/count-width and extraction bounds are proved from the
  executed outputs. All repeated preparations and unmatched work remain in
  the child traces and recorded ledger; no sharing or efficient routing is
  claimed.
- `FiniteFoldedPlan` constructs a finite fallback using `L=m`, `t=0`, and
  the existing padded middle exponent. Every plan validity proof is derived.
  Its native parameter calculations have no binary cost theorem here, and
  these are not the optimized parameters for the requested exponent.
- `GraphFoldedCountCorrect` proves original semantic coefficients and modular
  counts after full incidence reindexing, then specializes to the constructed
  plan. The old backend appears only in an existing semantic identity used
  in the proof; it is not executed by the new program.

Cost scope is deliberately limited: the new copies, accumulations, retained
reference arrays and schedule control are priced, and all earlier recorded
child charges are propagated. `ExactHalfSourcePlan.prepare` still excludes
translation-list generation from its retained-control counter. Earlier
shape/source native control, binary address costs, optimized parameter
construction and other incomplete setup prices are not silently filled in.
`GraphBlockSchedule.recorded_work_le` bounds an explicitly partial mixed
ledger, not total binary running time or the desired exponent. Full cyclic
outputs are computed before requested-residue extraction; no coefficient work
or request multiplicity is discarded.

The bounded fixture passes seven groups plus completion in 3.254 seconds:
signed normalized coefficient copies and widths, empty requests, singleton
cyclic spaces, exhaustive binary accumulation retaining unmatched children,
stored band indices and partial final bands, independent incidence ordering,
and copied bands versus direct original signed cyclic products. It executes
the complete new finite program only at `n=0,h=0..3`, where there are no graph
children. Positive-size complete graph execution, general LOW/HIGH scheduling
and production FFT are kernel-checked scope, not completed full runtime tests.
Prior expensive incomplete attempts were not repeated.

The finite graph-to-original-count correctness boundary is now closed.
Remaining work is optimized parameter/callback construction and sharing,
complete binary setup/address/control pricing, efficient routing and strict
batch fit, rounded entropy/phase costs, the uniform exact rectangular
algorithm, and adaptive caller complexity. The closed APSP theorem remains
`2.99294792`; the requested `2.9926862626` theorem is unfinished.
Evidence: `folded-band-schedule-statement-audit.txt`,
`folded-band-schedule-runtime-check.txt`,
`folded-band-schedule-finite-verification.txt` and `verification-output.txt`.
Frozen source/configuration SHA-256: `b8c0bff07126e22887292bddc87ba9e2a0476f2ed592da16fe5002519277bd67`.


## Retained translation arithmetic and binary state costs

`ExactHalfSourcePlan.prepare` now runs `HalfSourceRetainedTranslations.produce`
once and retains its keys, binary power tables and final binary/cached-sum
state in the actual selector plan. The generator's output is proved equal to
the original exact-half list, with the same order and repetitions. The
existing source and scheduler correctness proofs continue to refer to this
actual preparation. No answer or fast multiplication oracle is introduced.

`HalfSourceStoredKeys` explicitly constructs the binary character keys and
nonzero flags, including dimension zero. `HalfSourceBinaryState` updates each
stored signed sum with an actual binary addition and explicitly decodes its
small index value. It proves cache agreement, magnitude at most the number
of steps, binary addition/decoding bounds, and indexed row/array control.
`HalfSourceRetainedTranslations.build_refines` preserves the previous greedy
list and character sums. Its power tables and all score arithmetic are
retained; `produce_keeps_arithmetic` proves the earlier arithmetic counter
cannot disappear. `prepare_keeps_generation` and `prepare_keeps_arithmetic`
connect this fact to the plan consumed by the existing graph scheduler.
The resulting arithmetic bound is `2^m` times a polynomial in `m`.

This is a repair to the executed preparation, not total binary setup pricing.
Selection row/sign closures, zero tests, cube enumeration, score table-index
arithmetic and power-table loop control still need explicit retained programs
and prices. Indexed control is not a binary address bound. Setup still repeats
for every band pair, requests are not efficiently routed, and the finite
fallback parameters remain unoptimized. The full APSP target remains unproved.
The old `prepare_inverse_bits` bound priced only the inverse component; that
component is now named `inverse_bits`, and `prepare_bits` includes generation.
All prior frozen source snapshots preserve the earlier statements verbatim.

The new bounded fixture covers independent character enumeration, signed
binary state updates and caches, eight actual greedy/select/update steps at
`m=1` with independently supplied exact power tables, and actual preparation
at `m=0,L=0..3`. It does not rerun production power-table generation at positive
`m`, a full positive-size graph or the production FFT. Those general statements
are kernel-checked. See `shared-selector-costs-runtime-check.txt`,
`shared-selector-costs-statement-audit.txt`,
`shared-selector-costs-finite-verification.txt` and `verification-output.txt`.
The frozen full rebuild passed 277 modules and 3,307 axiom reports, using
only `propext`, `Classical.choice` and `Quot.sound`. The numerical suite and
exact statement audit passed; the bounded cost fixture completed in 5.873
seconds, and the earlier bounded scheduler regression passed. The old closed
theorem and its complete 129-module import closure are unchanged.
Frozen source/configuration SHA-256: `0b81c9d97ea21665b01740e95d993308ab0f227991baadcbbad727f150b4a5c3`.


## CW polynomial certificate and tensor-power interface

`CWPolynomialCertificate.cw16` constructs an explicit certificate over Q:
18 separated polynomial terms, coefficients below degree 3 zero, degree-3
coefficient exactly the independently defined big CW16 tensor, and degree
at most 10. The more general `certificate q` works over every commutative
ring, including `q=0`, without division. Its three variable spaces use
separate copies of the same axis labels; the formal variable is an additional
polynomial parameter.

`FiniteTrilinear` gives finite coefficient tensors, separated terms, their
bilinear evaluation identity, coordinate pullback, products, term reindexing
and ring-homomorphism transport. `PolynomialDegeneration` proves that counts
multiply and orders/degrees add under tensor products; coordinate restriction
preserves the certificate. `cw16Power n` consequently constructs `18^n`
terms of leading order `3*n` and degree at most `10*n` for the exact tensor
power, with `18^n` coordinates on each axis. The zeroth power is the scalar
one tensor. These are reusable inputs for extraction and interpolation.

`termsAt q t` is executable scalar data. Its ring-map and specialization
proofs identify its values with evaluation of the polynomial certificate.
Mathlib polynomials here are a noncomputable semantic representation; no
claim is made that Lean executes that polynomial representation. The scalar
fixture executes exact rational terms for `q=0,1,2,3,16` at four integer
nodes and independently checks all 24,224 coordinate triples. A separate
integer-polynomial Python implementation checks all 6,056 coefficient triples
for those dimensions, including every one of CW16's 5,832 entries. It uses
neither floating point nor an external algebra package.

This proves an explicit polynomial degeneration. It does not assert exact
rank 18 for CW16 over Q, define/prove an abstract border-rank theorem, or
prove the rectangular exponent. The polynomial family's term count is an
upper-bound witness. The next checkpoint below supplies exact interpolation,
a dense bilinear program, integer-arithmetic counts and retained-value bit
bounds. Independent-copy extraction, the rectangular asymptotic sum argument,
uniform finite-base recursion and complete binary costs remain to be formalized. See the finite extraction plan
in `EXACT_HALF_ROADMAP.md`. Existing finite graph correctness and cost repairs
are unchanged; no fast oracle is introduced into the graph program.

Evidence: `cw-polynomial-statement-audit.txt`,
`cw-polynomial-runtime-check.txt`, `cw-polynomial-finite-verification.txt`
and `verification-output.txt`. The full frozen rebuild passed 281 modules
and 3,340 axiom reports, using only `propext`, `Classical.choice` and
`Quot.sound`. The numerical/finite suite and exact statement audit passed. The old closed theorem and its 129-module import closure remain
unchanged; the requested APSP exponent remains unproved.
Frozen source/configuration SHA-256: `81758711a5bc3539647986a448b354c483a7a842308fe73b53c2e97f9c6853d4`.


## Exact interpolation and executable CW extraction checkpoint

`CWExactDecomposition.terms_total` proves an explicit exact rational separated
sum for every tensor power of CW16. It has `(10*n+1)*18^n` terms, including
one term at `n=0`; it does not assert exact rank 18 for CW16. The term data
uses integer node evaluations and computably constructed interpolation weights.
`RationalInterpolation.coefficient` derives coefficient extraction from
mathlib's `Lagrange.eq_interpolate`, rather than assuming an extraction oracle.

For degree `d`, nodes are the integers `0,...,d`. The retained row for node i
contains the coefficients of `prod(j != i, X-j)` and the nonzero signed integer
`delta_i = prod(j != i, i-j)`. `IntegerInterpolationWeights.prepare` constructs
one shared denominator `D = prod_i delta_i` and weight numerators
`W_i = coeff_k(prod(j != i, X-j)) * prod(j != i, delta_j)`.
The proofs identify `W_i/D` with the Lagrange weight and prove `D != 0`.
No denominator is repeatedly multiplied while summing exponentially many terms.
`IntegerCoefficientExtraction.extract_exact` proves that the actual integer
dot product equals `D` times the requested polynomial coefficient.

`CWInterpolationProgram.execute_correct` connects these weights to the actual
integer CW coefficient evaluator, enumerated keys, retained input linear-form
products, all output accumulations, and exact integer division. Its result list
contains every coordinate of the bilinear map for the nth CW16 tensor power,
in the enumerated order. Neither node evaluations nor returned answers are
supplied as hypotheses. `family_bounds` supplies order `3*n`, degree at most
`10*n`, and the target leading coefficient, including `n=0`.

The new cost theorem is explicitly an integer-register arithmetic theorem.
Put `d=10*n`, `L=18^n`, `S=(d+1)*L`. Coefficient generation costs at most `25*n`
arithmetic operations per coefficient. The setup bound is
`P(d)=(d+1)^2*(2*(d+1)+2)+(d+1)*(d+2)+(d+1)`. `execute_work` proves

```
operations <= P(d) + S*(2*L*(25*n+2)+1) + L*(S*(25*n+3)+1).
```

It charges preparation arithmetic, both input linear forms, each retained
product, every output coefficient and accumulation, and one exact-division
primitive for every output. This dense execution is not a fast rectangular
multiplier. It does not equate an integer division with unit binary cost.
The setup's separate indexed control bound is proved, but key construction,
all native list/array copies, addressing, basis tests, branches and counter
bookkeeping have not been compiled to a complete binary execution model.
The arithmetic counter must not be reported as that missing complete cost.

The denominator and weight numerator envelope for magnitude bits is
`(2*d+2)*(d+1)*(d+2)+1`. For input magnitudes at most `2^B`, put
`C=20+(1+16*d)*(1+d^3)+d*(1+d)+(1+16*d^2)` and
`E=(2*d+2)*(d+1)*(d+2)`. The retained input linear forms have at most
`18*n+C*n+B+1` magnitude bits, retained products at most
`2*(18*n+C*n+B)+1`, and output numerators at most
`d+1+54*n+E+3*C*n+2*B+1`. These are proved polynomial envelopes on the stated
retained values, not a trace theorem pricing every temporary and address.

Independent exact Gaussian elimination checked 592 Vandermonde moments and
5,913 CW extraction coordinates (all 5,832 n=1 coordinates and 81 selected
n=2 coordinates). The Lean fixture recovered every coefficient at degrees
0,1,2,3,10,20; executed n=0; and executed three n=1 input pairs, each retaining
198 products and returning all 18 correct outputs with 76,457 charged arithmetic
operations. The bounded fixture passed in 3.381 seconds. There is no large-power
runtime claim; no previous incomplete graph/FFT attempt was repeated.

Next on the rectangular path: identify the six CW blocks as matrix-multiplication
tensors, formalize compatible type classes and independent-copy extraction,
prove the rectangular asymptotic sum argument, and compile a uniform recursive
exact algorithm with binary costs. Efficient graph batching, remaining setup/
control charges, rounded phase bounds and adaptive APSP caller integration also
remain. The old closed exponent is 2.99294792; 2.9926862626 remains unproved.

Evidence: `cw-interpolation-statement-audit.txt`,
`cw-interpolation-runtime-check.txt`, `cw-interpolation-finite-verification.txt`
and `verification-output.txt`. The full frozen rebuild passed 293 modules and 3,448 axiom reports,
using only `propext`, `Classical.choice` and `Quot.sound`. The numerical/finite
suite and exact statement audit passed.
All 281 previous Lean source files and all 26 earlier frozen snapshots are
preserved. Frozen source/configuration SHA-256: `2d59d6de9b8b142f60109e524f3d3ae1dc53c17cd44072a5fcb95128394518e1`.

Verification recovery note: the original verifier tool session was interrupted
during its final module, after 292 completed modules and 3,442 axiom reports.
The completed reports were revalidated against the unchanged frozen sources;
the final module was recompiled with `warningAsError=true` and exit code 0.
Pinned dependencies, Lean version, roots, all 3,448 reports and the source hash
were checked again. `verification-output.txt` explicitly records this recovery.
The interrupted raw log and resumed tail remain in the frozen staging directory.

## CW block and finite independent-copy extraction checkpoint

`CWSixBlocks.identity` proves all six coordinate restrictions of the actual
CW tensor are matrix-multiplication tensors: <1,1,q>, <q,1,1>, <1,q,1>,
and three scalar blocks. The coordinate maps are injective, and all other
color triples vanish. `CWBlockWords.word_identity` and its cyclic variant
prove the corresponding products, including the zero tensor power.
`CWTypeCounts.joint_counts_unique` proves that the three marginal histograms
uniquely determine all six joint counts at level one.

The extraction now uses constructed finite sets, rather than an assumed
isolated family. `CWIsolatedCandidates` enumerates words of the reference
marginal type whose three coordinate words survive the supplied coordinate
restrictions. `FiniteCollisionCleanup` removes every candidate incident to
an X, Y or Z collision in that original set. The proof establishes closure
of compatible mixed coordinates inside the candidate set, and then proves
that no mixed retained triple survives. `CWIndependentCopies` supplies
injective maps from the three disjoint unions of matrix coordinates into
the actual CW16 tensor-power coordinates. Its `restricted_tensor` theorem
identifies the restricted tensor with the direct sum; `exact_decomposition`
restricts `CWExactDecomposition.terms` to that same direct sum, with exactly
`(10*n+1)*18^n` terms. This is a finite separated rational decomposition,
not an asserted optimized rectangular algorithm or exact rank 18.

`CWCanonicalType` constructs the target reference words from six repeated
blocks. Its period is 75,249,000,000,000, and its counts in the order
011,101,110,002,020,200 are
6,888,000,000,000; 4,000,000,000,000; 60,000,000,000,000;
131,843,770,853; 4,180,500,000,000; 48,656,229,147.
The proofs identify their exact rational probabilities, positivity, length
and dimensions. A retained copy at scale s has dimensions
<16^(4,000,000,000,000*s), 16^(60,000,000,000,000*s),
16^(6,888,000,000,000*s)>; cyclic permutation gives aspect (861/500,1,15).
There is no claim that this enormous reference word has been executed.

`CWHashSeparation` proves the actual weighted-hash relation and equal-bucket
consequence of `ThreeAPFree`. `CWHashedCandidates` connects those hashes to
the actual coordinate filters and cleanup. `CWExtractionExample` proves
that weights (0,1,2), offsets (5,1) and buckets {0,1,3} over ZMod 7 retain
exactly two independent <16,16,16> copies in CW16 cubed. This is a concrete
nonempty example, not the required exponential extraction estimate.

The current bound is only `candidate.card <= kept.card + collisions.card`.
The cleanup is a conservative symmetric one-pass construction; it is not
the asymmetric procedure of the published proof. These are cardinality
statements, not operation counters. Enumeration of 6^n words and scanning
all candidate pairs is not charged as an efficient extraction compiler.
The earlier interpolation arithmetic/width theorems remain unchanged;
complete binary addressing, copies and control are still unproved.

Independent Python tests check 5,931 block coordinates, 1,555 word/marginal
cases, every one of 512 mixed coordinates of a two-copy q=2 example,
the actual mod-7 selection, empty/zero cases and exact target counts.
The Lean runtime fixture executes the actual hash/cleanup and word maps;
the generic rational direct-sum identity is separately kernel-checked.
The full frozen rebuild passed 304 modules and 3,527 axiom reports,
using only `propext`, `Classical.choice` and `Quot.sound`. The numerical/finite
suite and exact statement audit passed. The Lean runtime fixture passed in
3.068 seconds. All 293 earlier Lean modules and 27 prior frozen snapshots
remain unchanged. No previous incomplete graph/FFT runtime or denied process
inventory was repeated. The requested APSP exponent remains unproved.

Frozen source/configuration SHA-256: `3afb7ecc13475d053566ba9e431a478e4d9054b2c5f9cf497d58ec7fdfb79499`.

Verification recovery: the tool session was interrupted after 259 completed
modules and 3,264 axiom reports. The completed prefix was revalidated against
the frozen sources; all remaining 45 modules were compiled with warnings as
errors and exit code 0. Pinned dependencies, exact roots, Lean version, all
3,527 axiom reports and the unchanged source hash were checked again. The
installed verification transcript records the recovery; the original log and
resumed tail remain in the staging directory. A deep staging-cache symlink
chain was shortened to the identical dependency directory before resuming;
no previous snapshot or dependency source was changed.

## Finite hash-counting and quantitative cleanup checkpoint

`CWPrimeHashCounts` proves the finite counting contract underlying VXXZ24
Claim 5.5 for every prime M>2. The random space is the explicit product of
two offsets and n coordinate weights over ZMod M, of cardinality M^(n+2).
ZMod M is used only for hashing coordinate labels; the restricted tensor
and its exact separated decomposition remain over the rationals.
For any actual CW block word and specified bucket c, the fiber has exactly
M^n elements. For two distinct words sharing an X, Y or Z coordinate word,
the common-bucket fiber has exactly M^(n-1) elements. The n=0 single-word
case is included; no distinct pair exists at n=0.

These counts have no independence hypothesis. `CWHashFibers.restrictedEquiv`
solves both offsets in terms of arbitrary weights and preserves an arbitrary
predicate on those weights. `CWWeightedFibers` solves a nonzero coefficient
for one weight, or recurses past equal coefficients, proving the exact
fiber size. The prime specialization proves that the three color values
remain distinct and that 2 is nonzero. `CWWordCollisions` proves that any
two coordinate words determine the original word, so a distinct pair
sharing one coordinate has a genuinely nonzero constraint in another.

`CWFilteredHashCounts` applies these counts to the actual coordinate filters
from `CWHashedCandidates`, with an explicit progression-free bucket set B.
For the full reference marginal class E, let T=|E| and let P be the actual
number of ordered distinct pairs in E sharing any coordinate word.
`CWQuantitativeCleanup` proves, by finite double counting, that the sums
over all hash samples of candidate and collision counts are respectively
T*|B|*M^n and P*|B|*M^(n-1). It then applies the existing symmetric cleanup
inequality to the actual retained sets. For n>0,
`CWFiniteSurvival.exists_survivors_rational` proves the existence of a hash
sample retaining at least

    T*|B|/M^2 - P*|B|/M^3

copies. An undivided natural-number inequality also covers n=0. Empty bucket
sets are allowed and give the expected zero bound. The retained set is
exactly `CWHashedCandidates.kept`, so the preceding injective-coordinate,
no-cross-term and exact direct-sum decomposition theorems apply to it.
No isolated family or returned count is supplied as an assumption.

This is a finite cardinality and existence theorem. The bound can be
nonpositive; no exponential lower bound follows without controlling P and
constructing a sufficiently large B. It does not implement or price an
efficient hash search, a random sampler or a rectangular multiplier.
Type-class regularity, multinomial estimates, modular progression-free
construction, entropy extraction, rectangular asymptotic sum, uniform binary
recursion and the final APSP speed integration remain unproved.

Independent Python enumeration checks 20,418 samples, 2,145 single-bucket
fibers, 60,648 shared-pair fibers and 83 cleanup classes for primes 3,5,7
and bounded n<=3. The Lean fixture executes the actual hashes at n=0,1
and selected n=2 words, plus the actual filters and cleanup. In its n=2,
M=5 case, T=2, P=2, |B|=2, total candidates=100, total collisions=20 and
maximum retained copies=1. Zero-dimensional and empty-bucket cases also
pass. No large target reference word or earlier incomplete graph/FFT
runtime attempt is executed.
The full frozen rebuild passed 313 modules and 3,567 axiom reports,
using only `propext`, `Classical.choice` and `Quot.sound`. The full finite
suite, bounded executable fixture and exact statement audit passed.
All 304 earlier Lean modules and 28 prior frozen snapshots are unchanged.
The old closed theorem remains 2.99294792; 2.9926862626 is unproved.

Frozen source/configuration SHA-256: `7380a16ffdd885fa5b35f1a2a2496e8432f1f15e31aeb5324a78de7d414f3699`.

## Type regularity, multinomial counts and finite density bound

This checkpoint connects the actual reference type class and hash cleanup
to exact multinomial data. It does not prove the rectangular exponent or
the requested 2.9926862626 APSP theorem.

`CWCoordinatePermutations.funEquiv` identifies the repository's nested
`PowerIndex` words with functions on `Fin n`. Equal histograms produce a
coordinate permutation by matching the finite fibers of the two functions.
Simultaneously permuting a CW word preserves all three marginal histograms
and commutes with each coordinate map. `CWTypeRegularity` uses this actual
permutation to give bijections between coordinate fibers of
`CWFilteredHashCounts.fullClass`. No uniform-fiber premise is supplied.
The reference word proves that all three fiber degrees are at least one.

`CWTypeCollisionCount.collision_identity` proves the exact ordered-pair
identity

    P = T * (D_X + D_Y + D_Z - 3).

Distinct words cannot share two coordinate keys, so the three kinds of
ordered collisions are disjoint. For each coordinate, deleting the word
itself leaves D_i-1 neighbors. Positivity justifies the natural-number
subtractions. The identity and regularity include n=0: the reference class
is a singleton, all degrees are one, and there are no distinct collisions.

`FiniteHistogramCounts` derives the cardinality of a type class from the
actual permutation fibers and mathlib's `DomMulAct.stabilizer_card`.
`CWTypeCardinalities` identifies the full CW class with its joint histogram
and proves that each coordinate image is the complete marginal type class.
Thus T is the six-symbol multinomial, |X|, |Y| and |Z| are the corresponding
three-symbol multinomials, and T=|X|*D_X=|Y|*D_Y=|Z|*D_Z. The positive
marginal counts make the formulas D_i=T/|i| exact natural-number divisions.
These are actual class cardinalities, not supplied parameters.

Let D=D_X+D_Y+D_Z. `CWTypePrimeChoice.selected` is the least prime in
2D<M<=4D, defined using Nat.find; mathlib's Bertrand theorem proves the
search terminates and M>2. The bounded fixture executes this selector.
This establishes a concrete mathematical prime choice, without an
execution-cost bound for the search, factorials, permutations or hashes.

For n>0 and any explicit `ThreeAPFree` B in ZMod M, the actual cleanup now
has a sample retaining at least T*|B|/(2*M^2). More strongly,
`CWTypePrimeChoice.selected_density_survival` proves

    retained copies >= min(|X|,|Y|,|Z|) * |B| / (24*M).

The proof uses min(|X|,|Y|,|Z|)*D<=3T and M<=4D. This is the finite bridge
to the desired entropy-scale rate: it isolates the remaining bucket-density
and marginal-multinomial estimates. It does not assume or construct a large
progression-free set, and the bound may be zero for B empty. The retained
set is the same `CWHashedCandidates.kept` used by the prior coordinate
injection, no-cross-term and exact rational direct-sum restriction proofs.
The hash labels are modular; the tensor decomposition remains rational.

Independent Python enumeration checks all 462 type classes through n=5:
9,331 words, 11,952 coordinate fibers and 394,200 ordered distinct pairs.
It checks complete marginal images, regularity, multinomials, collisions,
the least admissible prime and both rational bound simplifications for every
possible bucket cardinality. The Lean fixture executes the actual classes,
fibers, collisions, formulas and prime selector for all 84 classes through
n=3, including zero dimension. These are finite checks, not benchmarks.
No previous incomplete graph/FFT runtime attempt is repeated.
The full frozen rebuild passed 322 modules and 3,628 axiom reports,
using only `propext`, `Classical.choice` and `Quot.sound`. The full finite
suite, bounded executable fixture and exact statement audit passed.
All 313 earlier Lean modules and 29 prior frozen snapshots are unchanged.
The old closed theorem remains 2.99294792; 2.9926862626 is unproved.

Frozen source/configuration SHA-256: `ea7f05b91af35162e9d69110a71316bd75b72efd775394f15e24d6b3b43a5316`.

## Constructed modular buckets and unconditional finite survival

`FiniteAPSearch` gives an executable deterministic reference construction.
It enumerates all subsets of `range N`, tests the finite three-term
progression predicate, and retains a largest admissible set, with a fixed
last-on-tie rule. Its correctness proof shows that the actual returned set
has cardinality `rothNumberNat N`. Mathlib's `Behrend.roth_lower_bound` then
bounds that actual set by `N*exp(-4*sqrt(log N))`, including small N.
No progression-free set or density is assumed. This is an exhaustive search,
not an efficient Behrend generator: `subsets_length` proves that it enumerates
exactly 2^N candidates. No generation or binary execution-cost bound is claimed.

`ModularAPEmbedding` proves the exact integer-to-ZMod bridge. If a set is
inside `range N` and 2N<=M, both sides of any equation a+c=b+b are below M.
Equality after reduction modulo M therefore implies integer equality.
The map is injective on the interval, so it preserves cardinality and
ThreeAPFree. Primality is not needed for this bridge.

`ModularBehrendBuckets.buckets M` is the image of the actual integer selector
at N=floor(M/2). It is progression-free for every M and has exact cardinality
`rothNumberNat (M/2)`. The small cases are proved explicitly: M=0 and M=1
give the empty set; M=2 gives {0}. For every M>2, the following real bound
is proved without any large-modulus premise:

    |buckets M| / M >= (1/3) * exp(-4*sqrt(log M)).

The proof uses floor(M/2)>=M/3 and monotonicity of log, sqrt and exp, together
with mathlib's all-N Behrend inequality. The repository's selected prime
already satisfies M>2, so no additional prime-size assumption is introduced.

`CWBehrendSurvival.exists_survivors` instantiates the earlier actual-cleanup
bound with these constructed buckets. For every positive tensor-power length
n and actual reference word, let S be the minimum of its three marginal
multinomial cardinalities and M its actual selected prime. Some actual hash
sample retains at least

    (S/72) * exp(-4*sqrt(log M))

copies. No B, density, regularity or returned-answer premise appears.
The retained set is exactly the preceding `CWHashedCandidates.kept`, so the
existing independent-coordinate, no-cross-term and rational direct-sum
restriction results continue to apply. `selected_le_power` proves
M<=12*6^n; `exists_survivors_explicit_loss` consequently gives the bound

    (S/72) * exp(-4*sqrt(log 12 + n*log 6)).

This is an exact finite inequality with an explicit length-dependent loss.
It does not yet prove a multinomial entropy rate, the rectangular asymptotic
sum inequality, or a fast multiplication algorithm. The zero-length cases
are covered by the set/cardinality proofs and bounded actual cleanup tests;
the real-valued survival theorems above explicitly require n>0.

Independent integer/rational enumeration checks 8,191 candidate subsets for
N=0..12, the optimal integer cardinalities using a separate descending-size
search, 26 moduli M=0..25, and 12,168 no-wrap triples. Both the independent
Python fixture and the Lean runtime fixture execute cleanup with the actual
selected primes and constructed buckets at n=0,1,2, totaling 15,033 hash
samples. The n=2 case uses M=11, |B|=4 and has candidate/collision totals
968/88, with maximum retained cardinality 1. No floating-point experiment
is used to certify the analytic Behrend bound; that proof is kernel-checked.
No previous incomplete graph/FFT runtime attempt is repeated.
The full frozen rebuild passed 326 modules and 3,652 axiom reports,
using only `propext`, `Classical.choice` and `Quot.sound`. The full finite
suite, bounded executable fixture and exact statement audit passed.
All 322 earlier Lean modules and 30 prior frozen snapshots are unchanged.
The old closed theorem remains 2.99294792; 2.9926862626 is unproved.

Frozen source/configuration SHA-256: `38d5d4593ca50df6431c273a33bf782cfe8c34d7e1f54c4cca5a84243e13bf44`.

## Actual target marginal entropy and exponential extraction rate

`TernaryEntropy` proves endpoint-inclusive finite bounds for the actual
ternary multinomial coefficient: if n=a+b+c, its value lies between
exp(n*H)/(n+1)^2 and exp(n*H). H is expressed by a binary entropy chain;
for positive coordinates it is proved equal to the usual Shannon expression
-sum(p_i*log p_i), using natural logarithms. The finite coefficient bounds
include zero coordinates and n=0. They use the existing proved binomial
entropy bounds and mathlib's exact multinomial factorization.

`CWTargetMarginals` derives all three marginal histograms from the actual
`CWCanonicalType.reference s`, not an assumed histogram or growth premise.
The exact period is P=75249000000000 and n=s*P. In color order 0,1,2 the
unscaled counts are:

- X: (11200343770853,64000000000000,48656229147).
- Y: (4180500000000,66888000000000,4180500000000).
- Z: (64229156229147,10888000000000,131843770853).

Every coordinate is positive and each triple sums to P. Scaling is integral
and exact. For H_i=-sum_a (c_ia/P)*log(c_ia/P), the actual marginal count
is between exp(n*H_i)/(n+1)^2 and exp(n*H_i), including scale zero, where
the cardinalities are 1. Let h=min(H_X,H_Y,H_Z); h>0 is proved.

`ExtractionLoss` proves that every epsilon>0 eventually absorbs the complete
loss

    L(n)=2*log(n+1)+log(72)+4*sqrt(log(12)+n*log(6)) <= epsilon*n.

The logarithmic part uses mathlib's proved log=o(id) theorem. The square-root
part has an elementary eventual bound with an explicit threshold. The real
inequalities are kernel proofs, not floating-point tests.

`CWEntropySurvival.finite_survival` combines the actual marginal bound with
`CWBehrendSurvival` to retain at least exp(n*h-L(n)) copies at every positive
scale. `exponential_survival` proves: for every epsilon>0, at every
sufficiently large integer scale s, some actual hash sample retains at least
exp(n*(h-epsilon)) copies, using the already constructed prime and bucket set.
No marginal-growth, progression-free-set or density premise is supplied.

`CWEntropyFloors` proves that s=floor(N/P) discards fewer than P positions,
including all small boundary cases, and eventually retains at least
exp(N*(h-epsilon)) copies for every epsilon>0. This is an extraction from
length n=s*P<=N with the bound expressed against N; it does not assert a new
padding implementation into tensor length N. The exact-scale theorem is
already sufficient for selecting arbitrarily large integral bases.

`CWTargetExtractionRate.exponential_extraction` joins the rate to the actual
coordinate-filtered independent-copy type, the exact rational direct-sum
decomposition, and its (10*n+1)*18^n rank-one terms. Each retained copy has
rows 16^(s*4000000000000), inner dimension 16^(s*60000000000000), and columns
16^(s*6888000000000). The existing injective coordinate embeddings and
no-cross-term theorem apply to these same constructed coordinate sets.
`exists_positive_base` proves existence of a positive integral base for any
fixed strict entropy slack. Neither statement proves rectangular asymptotic
sum or a single-matrix runtime exponent.

The independent Python fixture and Lean runtime fixture each check 343
ternary coefficient cases via exact integer entropy-weight inequalities,
18 scaled target marginal histograms, 12 floor boundaries, and 1555 bounded
CW words. The Lean fixture also executes the actual zero-scale reference
and its three marginal cardinalities. Positive-scale target words are not
materialized: their enormous period is handled symbolically by the kernel
proofs. No previous incomplete graph/FFT runtime attempt is repeated.
The full frozen rebuild passed 332 modules and 3,684 axiom reports,
using only `propext`, `Classical.choice` and `Quot.sound`. The full finite
suite, bounded executable fixture and exact statement audit passed.
All 326 earlier Lean modules and 31 prior frozen snapshots are unchanged.
The old closed theorem remains 2.99294792; 2.9926862626 is unproved.

## Remaining rectangular path after target entropy

The actual target marginal growth and exponential independent-copy rate are
now proved. The next mathematical contract is rectangular asymptotic sum:
convert the proved exact decompositions of many independent rectangular
matrix tensors into a bound for a single rectangular multiplication family,
with the correct aspect/orientation and strict exponent slack. The local
contract now supplies copy count, exact dimensions, no cross terms, and
(10*n+1)*18^n terms; a numerical comparison alone cannot perform that
conversion. The required target remains w=16.7220002 at aspect
(861/500,1,15), with any coordinate permutation justified explicitly.

1. Formalize rectangular asymptotic sum on these actual rational bilinear
   decompositions, including its finite tensor-power/aggregation construction.
   Prove the required strict entropy/logarithm comparison and select a finite
   base that meets the desired rectangular arithmetic exponent. The current
   entropy slack theorem does not certify that numerical comparison or w.
2. Build the resulting uniform recursive binary multiplication algorithm,
   with coefficient and denominator growth, exact recovery, dimension padding,
   addresses, copies and control. The previously proved arithmetic evaluator
   for a finite decomposition is not this recursive algorithm.
3. Integrate efficient graph batches, optimized rounded phase bounds,
   remaining setup/control costs and the adaptive APSP caller. The unchanged
   closed theorem remains 2.99294792; 2.9926862626 remains unproved.

Fixed-base preprocessing can legally be an input-independent constant when
all target parameters and strict slack are fixed first, a single suitable
finite base and its rational data are fixed, and that same base is used for
all input matrix sizes. Its finite search, prime selection, bucket generation
and coefficient preparation can then contribute a constant depending on the
fixed base. This observation does not establish any missing recursion or
coefficient-growth theorem. The current existential base selection also is
not an implemented algorithm uniform in an epsilon supplied as input; a
computable certified selector and its complexity would require additional
work. In particular, the existing bucket generator still enumerates exactly
2^floor(M/2) subsets. It is not a fast generator when M or the tensor length
varies with the matrix input. No such changing-size generation cost has been
silently absorbed into a constant here.

Frozen source/configuration SHA-256: `b031d74d6cb353cc4500d521a2953e6e2c4153400ce7617570810e9923d18e0b`.

## Proof-gap audit: informal mathematics versus the requested theorem

An argument in the manuscript can be mathematically sound without already
being a closed Lean theorem about the particular executed program. These
are three distinct tasks; progress in one does not automatically settle the
others.

1. Translation of explicit local arguments. Exact rational type scaling,
   finite histogram identities, the entropy chain, logarithmic loss absorption,
   and the small/floor cases have now been translated and checked in the
   entropy checkpoint. Further explicit reindexings, rounded parameter
   inequalities and conversion of the stored rational logarithm certificates
   into Lean bounds belong here. They require substantial proof work, but
   do not by themselves demand a new matrix-multiplication result.

2. Published ingredients absent from the local library. In
   [arXiv:2307.07970v2, Theorem 3.2](https://arxiv.org/html/2307.07970v2#S3.SS5),
   positive integers t,q and nonnegative a,b,c satisfy
   `t*q^(omega(a,b,c)) <= asymptoticRank(directSum_t <q^a,q^b,q^c>)`.
   Here the dimensions must denote actual integral matrix dimensions.
   Proposition 5.1 gives
   `2^((A1*E1+A2*E2+A3*E3)*n-o(n))` independent interface copies,
   for normalized nonnegative region weights and valid type/split
   distributions. Its first rate is
   `E1=min(H(X)-P_alpha,H(Y)-P_alpha,H(barBeta_Z)-lambda_Z)`;
   the other two are coordinate permutations. Our level-one specialization
   uses q=16, A=(1,0,0), the six rational types and point-mass splits;
   unique compatible types and these splits remove both penalties.
   The entropy bases must be converted consistently. The paper's exponent
   is in the arithmetic-circuit model, not a binary machine-cost statement.

   Our current finite extraction proof independently supplies the required
   level-one copies, so formalizing all levels and hole-repair machinery of
   Proposition 5.1 is unnecessary. The missing asymptotic-sum bridge still
   has real content. For our positive integral scales the base is
   Q=16^(s*4000000000000)>1 and the dimensions are Q, Q^15, Q^(861/500),
   with the last integrality supplied by the exact exponent identity.
   The actual rational decomposition has (10*n+1)*18^n terms. One must
   justify tensor/rank conventions, coordinate permutation, the asymptotic
   limit and strict finite-base selection before deriving the advertised
   rectangular bound. None of those implications follows just by counting
   the terms of a direct sum.

3. Program and cost arguments still unverified locally. The manuscript's
   instruction to choose a finite rational base and recurse is a plausible
   proof outline, not yet a specified recursive implementation with a proved
   recurrence, padding strategy and width invariant. Fixed rational
   coefficients and fixed fan-in can support O(log input-size) additional
   bits across logarithmic depth, but the actual numerator/denominator
   representation, accumulation, exact recovery and all addressing/copy
   costs must implement that argument. Naive denominator multiplication
   does not inherit a shared-denominator cost bound automatically. The
   optimized graph batching, rounded phase bounds, remaining setup/control
   pricing and adaptive caller integration also remain incomplete. These
   are not established by the published arithmetic exponent, and should not
   be called mere bookkeeping or assumed correct because finite output
   correctness has passed.

The shortest useful conditional APSP target would have one explicit external
contract: a uniform deterministic exact rectangular multiplier for aspect
(861/500,1,15), with exponent 16.7220002 and a stated binary cost bound
`C*s^w*(B+log(s+2))^k`, including padding and all reads/writes, for the
integer/rational coefficient domains actually passed by the reduction.
The conditional theorem would prove the optimized exact-half reduction and
adaptive APSP bound from that contract. It must be an ordinary theorem
parameter, not an axiom. This conditional reduction is not yet proved here:
its own batching and complete cost integration still need work. Assuming
the final program's desired cost as an extra premise would hide the novel
obligation and is not a useful substitute.

For the requested closed result, that multiplier contract ultimately needs
an actual proof. However, it is avoidable scope expansion to formalize the
whole higher-level VXXZ framework when the level-one specialization suffices,
or to demand a fast variable-size bucket generator if a single fixed base
is selected first and reused for every input size. A conditional reduction
would cleanly isolate the novel work sooner. A complete CPU/ISA execution
model is also stronger than the repository's current charged binary and
indexed-control theorem; no such scope expansion is necessary unless that
stronger claim is explicitly wanted.

A fixed finite base can place its finite preparation cost in a constant
independent of the matrix input size. This requires fixing the base and its
rational data before that size varies. It does not make the current
2^floor(M/2) bucket search fast when M varies, does not give an algorithm
uniform in an input epsilon, and does not prove the missing recursion.


## Equal-copy recursion and rectangular rank checkpoint

The latest endpoint is `CWRectangularRanks.exists_fixed_base`. It closes the
level-one rank conversion that was missing after target entropy extraction.
There is one positive integral CW base and an explicit family of exact
rational decompositions of rectangular matrix powers at aspect
`(861/500,1,15)`. Its term count is at most

    t * Q^(16.7220001*k),

where Q is the fixed inner-dimension base and t is its fixed number of
independent copies. The coordinate permutation is proved, not inferred from
a numerical aspect ratio. `aspect` proves the exact integer identities
`rows^500=inner^861` and `columns=inner^15` at every power, including zero.
This leaves `1e-7` below the manuscript's `16.7220002` endpoint.

The construction is finite and explicit:

- `FiniteDirectSum` routes r requests into exactly `ceil(r/t)` groups of t
  slots by quotient and remainder. The routing is injective and padded slots
  do not contribute. Its coefficient theorem includes zero and incomplete
  groups.
- `FiniteBilinearSubstitution` proves that simultaneous lower products can
  replace the scalar products of the upper decomposition. `EqualCopyRecursion`
  then supplies the coefficients of t simultaneous tensor powers recursively,
  using exactly `t*ceil(r/t)^k` terms. Restricting to one actual copy gives a
  single tensor power. No division of a rank is assumed.
- `FiniteDependentCopies` and `CWHomogeneousCopies` connect this construction
  to the actual extracted CW coordinate sets and rational interpolation terms.
  Finite equivalences choose labels for one fixed base; no input-dependent
  multiplication oracle is introduced.
- `CWEntropyCertificate` proves the strict comparison for all three actual
  marginal entropies, using rational atanh partial sums and proved analytic
  tails. `CWFiniteBase` combines it with the previously proved extraction
  rate and absorbs interpolation, extraction loss, and the last partial
  batch into a single sufficiently large integral base.
- `FiniteMatrixPowers` identifies the resulting tensor powers with actual
  matrix tensors and justifies their cyclic orientation.
- `EqualCopyCoefficientGrowth` proves coefficient magnitude at most `(r*H)^k`
  and a common denominator `d^k`. `FiniteRationalCoefficients` constructs d
  and H from the fixed rational base itself, with no supplied height or
  denominator premise. `CWRectangularRanks.coefficient_invariants` transfers
  both facts to the same final rectangular coefficients.

The independent Python and executable Lean fixtures each check 168 routing
cases, four recursion depths, 2,232 coefficient bounds/denominators and
24 simultaneous dot-product outputs with signed rational coefficients.
The fixture's five-term/two-copy base forces an incomplete final batch.
The full-sized CW witness is handled symbolically, not materialized in a
runtime fixture. Run the bounded executable fixture with:

```sh
lake env lean --run scripts/check_equal_copy_recursion.lean
```

### Remaining execution obligations

The new endpoint is an exact rational **rank construction**. Evaluating each
expanded dense coefficient form separately would not attain its rank
exponent. The following work is still needed for the requested closed APSP
statement:

1. Implement the retained recursive evaluator that shares the upper linear
   forms, groups the resulting products and recombines stored child outputs.
   Prove its arithmetic and control recurrence from those executed loops.
   A scalar multiplication count alone does not price those operations.
2. Clear the fixed base denominators once and lower that evaluator to binary
   cells. The new `d^k` invariant prevents unconstrained denominator growth,
   but actual retained-input, partial-sum and output widths, exact recovery,
   padding, copies and addresses still need their own execution proofs.
3. Replace elementary completion in compatible graph batches with this
   proved evaluator; retain shared setup, the strict independent batch fit,
   all phase endpoints and the optimized rounded plan. Finish the adaptive
   callback and complete APSP work bound.

The old `BinaryAlignedAPSPTheorem.correctness_and_work` remains unchanged at
`2.99294792`. No theorem in its import closure uses these extension modules.
The requested end-to-end `2.9926862626` theorem is **not yet proved**. The
mathematical manuscript and its numerical certificate have not been relabeled
as a completed Lean execution theorem.

Frozen verification for this checkpoint: 343 modules, 3,726 axiom reports; only the standard Lean axioms. Full numerical/finite suite and the bounded Lean recursion fixture passed. Source/configuration SHA-256: `90abb7bb63b1b39806411c302dcf50cee30f65083b0e852955829321dd93421b`.


## Retained recursive execution checkpoint

The rank construction now feeds an actual retained program. The new endpoint
`CWRetainedArithmetic.exists_arithmetic_program` selects the same positive
fixed CW base, stores its three coefficient arrays once, and proves that its
recursive simultaneous tensor-power products use at most

    C * (k + 1) * Q^(16.7220001 * k)

ring operations plus indexed-control annotations. Here Q and C are fixed
before the input size varies. The exponent includes the input and output
axis volumes, whose largest exponent is 16.722. It does not assume that a
rank bound prices evaluation of dense expanded forms.

`RecursiveTable` gives explicit product layouts and stored vectors.
`RecursiveBilinearStep`, `RetainedEqualCopy` and `RetainedEqualCopyCosts`
construct and price the actual loops. At each level the program stores each
upper linear form once per suffix coordinate, pads the last request batch,
executes each child once, and recombines its stored outputs. The exact
arithmetic recurrence is

    A(0) = t
    A(k+1) = ceil(r/t) * A(k) + 2*r*t*(i^(k+1)+j^(k+1)+o^(k+1)).

A separate exact control recurrence charges dot-product input lists, table
construction/projection, padding and output writes. The bound uses
`M=max(1,ceil(r/t),i,j,o)` and proves `A(k)+control(k) <= C*(k+1)*M^k`.
The actual CW extraction supplies `M <= Q^16.7220001`; no lower bound on
matrix tensor rank is assumed to dominate the axis sizes.

The binary path is implemented separately using the existing stored signed
bit cells. `BinaryRecursiveDot` prices every multiplication and accumulation,
including partial sums. `BinaryRetainedEqualCopy.run_correct` proves the
recursive program's value, and `BinaryRetainedBounds.run_linear_bits` derives
its bit budget from the original input magnitude B and fixed base data:

    W <= (4*k+1)*size(F) + 2*size(B) + 2.

The fixed F bounds the local coefficient height and all local fan-ins.
`BinaryRecursiveCost` constructs these constants from the stored base;
intermediate magnitude or desired-cost premises are not required. Its
`execute_bits` theorem includes coefficient encoding, denominator powering,
recursive binary arithmetic and division of every complete output.

`ClearedRecursiveBase` clears all three rational coefficient arrays with a
single positive fixed denominator d. It proves that the complete depth-k
integer numerator equals `d^(3*k)` times the requested product. The exponent
3 accounts for all three forms; it is not the denominator of just one path.
`BinaryRecursiveRecovery` constructs that power with binary multiplication
and performs binary floor division only after the full numerator has been
assembled. Exact recovery, signed values and zero outputs are proved.
Fixed-base rational-data construction is outside the priced variable-size
recursion; a public implementation must retain that base rather than rebuild
it inside graph batches.

`MatrixPowerReindex` proves both inverses of the word/pair coordinate map.
`BinaryMatrixPowers.execute_correct` adapts ordinary matrix arrays to and from
this program and proves every output is the direct row/column inner product.
`cw_correct` uses the actual extracted CW coefficient base, without a
rectangular multiplication oracle. The adapter retains every input and output
slot and has a separate exact indexed-control count.

The Lean runtime fixture checks 202 outputs against dense tensor contractions,
with independently computed exact-rational and integer-numerator paths. It
also checks the actual ring/control recurrences and complete binary bit budget.
It covers depth zero through three, signed rational bases, incomplete batches,
empty rank, zero targets and values across the 16-bit boundary. A further 172
ordinary matrix output entries exercise both coordinate adapters. The independent
Python fixture checks the same 202 tensor outputs and exact recovery, without
using the Lean implementation or expanded recursive coefficient forms.

```sh
lake env lean --run scripts/check_retained_recursion.lean
python3 outputs/check_retained_recursion.py
```

### What still prevents the requested APSP theorem

1. The multiplier currently accepts tensor-power dimensions. Construct and
   prove the arbitrary-size next-power padding/truncation adapter, including
   its size bounds. Price the recursive layout/index arithmetic and combine
   setup, copies, scalar bit costs and indexed control into the uniform
   rectangular interface used by the graph algorithm. The current counters
   do not themselves lower recursive address calculations to binary circuits.
2. Replace elementary graph completion with compatible shared rectangular
   batches, lift repeated setup out of the outer schedules, and prove the
   strict independent batch fit for the optimized rounded parameters. The
   constructed `FiniteFoldedPlan.produce` still uses `L=m,t=0`; it is a finite
   correctness fallback, not the optimized asymptotic schedule.
3. Prove every optimized phase's aggregate cost, retain all translations,
   requests and restart/candidate costs, then connect the backend to the
   adaptive APSP caller and its complete work theorem.

These are substantive remaining proofs. In particular, this checkpoint does
not update `BinaryAlignedAPSPTheorem.correctness_and_work`: the closed APSP
exponent remains **2.99294792**, and the requested **2.9926862626** theorem is
still unfinished. The mathematical TeX/PDF and numerical witnesses are unchanged.

Frozen verification for this checkpoint: 356 modules, 3,806 axiom reports; only standard Lean axioms. The full Python suite and the actual Lean runtime fixture passed. Source/configuration SHA-256: `0f62323de659fbe349e6e14b14e048fb36512d8e7b951f997ad7a09b12d69e69`.


## Padded matrix execution checkpoint

`PaddedMatrix` now takes ordinary matrix arrays at arbitrary finite dimensions,
selects a depth with integer ceiling logarithms, pads one copy into the retained
simultaneous product, and crops the original output coordinates. Its
`atSize_correct` theorem proves every output is the original matrix product,
including empty dimensions. No caller-supplied valid padding plan is needed.
The fixed bilinear base still supplies its already-proved tensor identity.

Padding retains the original signed cells and inserts zeros. It preserves the
original magnitude bound, so `execute_bits` transfers the complete binary
arithmetic budget from `BinaryRecursiveCost`. Separate exact control identities
charge both padded input arrays and every cropped output; these do not price
native logarithm computation or recursive address arithmetic.

`PaddedMatrixScale` connects that adapter to the actual extracted CW base.
For a fixed positive base scale s, write Q for its inner axis `rows s`. The
selected depth is `k=clog(Q,D)+1`. The integer hypotheses

    (n-1)^500 <= D^861,       p <= D^15

suffice to fit an n-by-D times D-by-p product into the base powers; the extra
level covers upward rounding of the first axis. The adapter proves the
original product and its binary arithmetic budget for this same actual base.
For positive D it also proves

    Q^k <= Q^2 * D,          k <= size(D)+1.

Thus selecting the next base power costs only a fixed factor in the inner
size. These are finite integer size bounds, not the complete uniform binary
resource theorem. The first-axis hypothesis still has to be established for
the graph algorithm's actual rounded batch shapes.

The actual Lean runtime fixture checks 80 original matrix entries for empty
axes, partial power dimensions, signed values and the 16-bit boundary. Every
result is compared with an independent direct inner product, and the complete
binary arithmetic budget is checked. It uses small explicit bilinear bases;
the positive-scale CW base remains symbolically proved rather than materialized.

```sh
lake env lean --run scripts/check_padded_recursion.lean
```

The remaining work is complete binary pricing of size selection and addresses,
a combined uniform rectangular resource interface, optimized shared graph
batches and strict fit, rounded aggregate phase costs, and adaptive APSP
integration. The full `2.9926862626` theorem remains unproved. The existing
closed theorem remains `2.99294792` and imports none of these extensions.

The concrete next integration point is `BinaryPreparedGroupedProgram.runGroup`
and its family scheduler. They still call the elementary
`BinaryGroupedCompletion.runMatrix`. The fast replacement must construct the
selector/data chunks for the padded CW multiplier, preserve original request
indices and duplicates, retain every `B*q*F` column, and charge the resulting
outputs. Its actual dimensions must establish the independent strict batch
fit before the rectangular bound enters the phase ledger.

Frozen verification for this checkpoint: 358 modules, 3,824 axiom reports; only standard Lean axioms. The padded Lean runtime fixture passed on 80 original entries. The numerical/finite Python suite is unchanged from its preceding successful run. Source/configuration SHA-256: `9148e2d054b2c9a5dc21b66077e068aaf037e4c36e1c51c3a2e0acf10f3b0f4a`.

## Shared rectangular completion checkpoint

Seven new modules connect the retained CW program to concrete selector/data
chunks. They do not yet connect that program to the optimized graph schedule.

- `BinaryMatrixSetup` reuses the actual binary padding loop. For positive
  middle size D and fixed base q >= 2, it selects k with
  `D < q^k <= q*D` and `k <= size(D)+1`. Selection costs at most
  `1400*(size(D)+3)*(size(q)+size(D)+6)^2`. The integer aspect conditions
  `(n-1)^den <= D^num` and `p <= D^z` prove all padded dimensions fit.
- `BinaryMatrixAddress` implements binary product-index construction and
  quotient/remainder splitting, and proves agreement with the stored layout.
  `BinaryPowerAddress` constructs strides and both directions of every
  tensor-power address. Their bound is
  `8192*(k+1)^2*((k+1)*size(q)+2)^2`, including recomputed strides.
  These codecs have not yet replaced every native indexed operation.
- `BinaryRecursiveUniform` derives uniform scalar-bit and indexed-control
  bounds from the actual recursion. `CWBinaryScalarBound` combines the
  scalar bound with the actual fixed positive CW base and charged size
  selection. Its `exists_uniform_scalar_program` proves, for all admissible
  original matrix inputs of magnitude at most H,
  `C*(size(D)+size(H)+6)^3*D^16.7220001` scalar bit operations.
  C is fixed independently of the variable input sizes. This retains the
  positive allowance before the manuscript's `16.7220002`; it is not the
  complete scalar-plus-address resource theorem.
- `RectangularBatch` copies each row chunk and column chunk once, outside
  their Cartesian product, executes the actual padded recursive program,
  and restores every original output position. Short chunks and empty outer
  axes are included. Its exact control identity charges chunk creation,
  product storage and every output write separately from scalar bits.
- `SharedGroupedCompletion` constructs the selector/data matrices and proves
  all requested sums, retaining duplicates and every coefficient column.
  Its grouped adapter agrees pointwise with
  `BinaryPreparedGroupedProgram.runGroup`. Intermediate data bounds are
  derived from the original source magnitude.

The finite chunk-count theorem states

    ceil(N/A) * ceil(P/C) * A * C <= 2*(N+A)*P

under the independent condition `C <= P`. A large number of request rows
does not establish this long-side condition. In the graph application P
must come from genuinely compatible middle-block/coefficient columns.

The runtime checks cover 318 complete forward/inverse tensor addresses,
90 product/split addresses, and 30 depth selections, including powers of two
and the 16-bit boundary. The shared-completion fixture checks 196 matrix
outputs against independent dense selector sums and 90 prepared-group
outputs against independent raw-tensor contractions. It covers signed data,
duplicate and empty requests, empty columns, partial chunks and the returned
scalar budgets. The fixture uses a small rational bilinear base; the actual
positive-scale CW base is proved symbolically, not materialized for testing.

```sh
lake env lean --run scripts/check_matrix_addresses.lean
lake env lean --run scripts/check_shared_rectangular.lean
```

### Remaining integration boundary

The production graph does not call `BinaryPreparedGroupedProgram.runGroup`.
Its path is `GraphPrefixCompletion` -> `WindowCompletionProgram` ->
`PrefixCompletionProgram`, whose elementary row contractions read the
`PrefixCompletionMatrices` bank. Thus agreement with the earlier grouped
routine is a useful local adapter theorem, not evidence that the production
callback has been replaced. The next connection must batch equal prefix,
pair-bit, shape and locator keys, concatenate compatible middle blocks,
route original request indices, and scatter all formal/cyclic columns.
The current pair lookup is also a fully charged linear scan; an efficient
routing replacement must be constructed and proved.

The full target still requires:

1. Global setup and address/control accounting for the same executed
   program, including all retained storage and indexed accesses.
2. The optimized rounded plan and production shared batching, with shared
   setup across the outer schedule and the independent strict
   `Bq >= D^(kappa*zeta+xi)` fit. `FiniteFoldedPlan.produce` still uses
   the finite correctness fallback `L=m,t=0`.
3. Rounded entropy and all phase, candidate, restart and output costs,
   followed by instantiation of the adaptive APSP caller.

The closed theorem remains `BinaryAlignedAPSPTheorem.correctness_and_work`
at **2.99294792**. None of these extension modules is in its import closure.
The requested **2.9926862626** theorem is still unproved. The canonical
mathematical manuscript, its numerical witnesses and the published main
branches have not been changed by this local checkpoint.

Frozen verification for this checkpoint: 365 modules, 3,875 axiom reports, only standard Lean axioms. Both new Lean runtime fixtures and the full numerical/finite Python suites in the results and research repositories passed. Source/configuration SHA-256: `62c3838b62e284166edaca506c5cd5eea57b08ec8af8dd5b9dd97fba201a4611`.

## Routed shared-batch and parameter checkpoint

The frozen verification passed **416 modules and 4,337 axiom reports**, using
only `propext`, `Classical.choice` and `Quot.sound`. Source/configuration
SHA-256: `3cb6f842ac3e6a8e16586eb1e4337258821d272bad05a61d1c3998021dd4238b`.

This checkpoint connects compatible middle-block columns to retained prefix
matrix banks and window completion. Stable routing preserves original
occurrence indices, including duplicates, and proves that each request
belongs to exactly one own band/mask group. Both orientations have matching
occurrence lists after transposition. Matrix banks are prepared for reuse
across opposite bands. Binary chunk, table and recursive address programs
have explicit value and cost theorems. Adaptive prefix lengths are chosen
before window partitioning.

The actual rounded candidate plan, original grid geometry and independent
long-side batch fit are proved. The exact-half witness satisfies all 61
strict numerical checks, and the rounded seven-term analytic cost ledger has
the requested exponent. These statements do not assert that the unfinished
optimized graph program already satisfies that ledger.

Remaining work is to assemble the address-priced rectangular execution with
the retained sources, route and pair completed roots, reuse HIGH encodings,
prove every aggregate executed backend cost, and instantiate the adaptive
APSP caller. The closed theorem remains **2.99294792**; the requested
**2.9926862626** theorem is unfinished. Its 129-module import closure contains
none of the 281 extension modules. No canonical mathematical result or
numerical witness changed at this checkpoint.
