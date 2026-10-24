# Exact-half APSP dependency roadmap

<!-- exact-half-final-status-v1 -->
## Current proof status

The exact-half dependency chain is closed by
[`ThinMatrix.HalfSourceAPSPTheorem.correctness_work_and_addresses`](HalfSourceAPSPTheorem.lean).
For polynomially bounded integer weights and graphs without negative cycles,
it proves exact APSP output, complete charged work
**`O(n^(14963431313/5000000000)) = O(n^2.9926862626)`**, and eventual
address-price sufficiency within its reserved retained layout. Its hypotheses
concern the original graph; no backend-cost or fit assumption remains.

The frozen final verification passed **612 modules and 5,290
axiom reports**, using only `propext`, `Classical.choice` and `Quot.sound`.
Source/configuration SHA-256: `9d5e9865f2e599654af2082098a609a237ed2208d99adbb14648695b9527b04b`.
See [verification-output.txt](verification-output.txt) and the
[current scope and reproduction instructions](README.md#current-proof-status).

## Closed dependency chain

| Former obligation | Closed endpoint or connection |
| --- | --- |
| Constructed exact-half sources and complete source/setup costs | Exact-half translations and masks, retained per-input-band sources, cap-dependent source bounds, and [`HalfSourceSetupPhaseRate.exists_setup_rate`](HalfSourceSetupPhaseRate.lean). |
| Rectangular mathematical and binary execution dependencies | A proved fixed valid CW scheme, exact retained recursive arithmetic, padded matrix/tile setup, addresses and full shared-completion cost. [`GraphOwnBandCompleteRate.exists_complete_rate`](GraphOwnBandCompleteRate.lean) supplies the actual per-type rate. |
| Shared production batching and independent fit | Stable own-band routing gathers all opposite bands before completion, retains compatible middle-block/full-coefficient columns and original IDs, and uses the proved actual rounded independent fit in [`HalfSourceDispatchFit`](HalfSourceDispatchFit.lean). |
| Complete original graph counts | [`GraphHalfSourceExecution`](GraphHalfSourceExecution.lean) and [`GraphHalfSourceBackend`](GraphHalfSourceBackend.lean) connect actual LOW/HIGH execution, normalization, incidence tables and concrete factor dispatch. |
| Aggregate executed phase costs | [`HalfSourceBackendPhaseRate.exists_phase_prices`](HalfSourceBackendPhaseRate.lean) uses actual source/setup, LOW, HIGH, output, metadata and address bounds, with the rounded seven-term ledger and all 61 numerical checks. |
| Adaptive APSP correctness and complete work | [`HalfSourceAPSPTheorem.correctness_and_work`](HalfSourceAPSPTheorem.lean) fixes the concrete backend and discharges every phase/caller premise at the exact target exponent. |
| Whole retained layout and address price | [`HalfSourceRunAddress`](HalfSourceRunAddress.lean) connects actual host/callback counts and the reserved retained layout to eventual address-price sufficiency; [`correctness_work_and_addresses`](HalfSourceAPSPTheorem.lean) combines all three conclusions. |

There is no remaining proof obligation for this endpoint in its stated
binary-arithmetic and bounded indexed-array/control charged-work model.
A compiler/allocator correctness theorem, full word-RAM lowering and a native
Lean performance guarantee are different claims and are not established here.
The separate `machine/` adapter retains its own implementation/time premises.

The original
[`BinaryAlignedAPSPTheorem.correctness_and_work`](BinaryAlignedAPSPTheorem.lean)
is preserved at `2.99294792`. The historical exclusion of exact-half modules
from that older theorem's import closure is still a fact about that older
endpoint; it is not a gap in the new theorem's proof path.

## Historical dependency audits and checkpoints

The remainder preserves the audit trail, including its original baseline,
missing-obligation lists and checkpoint hashes. Each section is explicitly
historical. References there to the "current" old theorem, unproved target or
remaining work mean the state at that checkpoint, superseded by the closed
chain above. These records do not change the canonical mathematical witness.

### Historical initial audit baseline

> **Historical checkpoint.** This section records the state when it was
> written. Statements that the exact-half theorem was unfinished or that
> `2.99294792` was the current endpoint are superseded by the completed
> `2.9926862626` theorem described at the top of this document.

Audit baseline before this checkpoint: source/configuration SHA-256
`d1fca8d872a5579f0e045182af3ca75f18bda5eb1658f1ffe87d6011bc1f20bb`
(248 modules, 3,109 axiom reports). This roadmap distinguishes mathematical
identities, executable refinements, resource bounds, and the final caller.

The target is a concrete deterministic program on original optional integer
edge tables, with only an original polynomial edge bound and no negative
cycles as hypotheses, exact APSP output, and complete charged work
`O(n^(29926862626/10000000000))`. It must include parameter selection, source
formation, repeated calls, failures/restarts, arithmetic and output writes.
A theorem assuming an exact-half backend or its desired cost is insufficient.
The cost model must be stated as precisely as the existing binary-arithmetic
and bounded indexed-control model; native Lean evaluation is not that model.

The current `BinaryAlignedAPSPTheorem.correctness_and_work` proves
`299294792/100000000`. Its transitive local import closure contains 129
modules and **none of the 367 modules recorded as exact-half extensions**.
Thus no exact-half result is currently on the closed theorem's proof path.
The existing graph/controller correctness framework is reusable, but its
concrete callback and cost specialization still use the old backend. All
367 extension modules remain outside that closure. The full local import graph is recorded in
`exact-half-dependency-audit.json`; import closure is an overapproximation of
declaration dependencies, and exclusion is decisive for this audit.

The current result is in [Addressed execution and source-cost
checkpoint](#addressed-execution-and-source-cost-checkpoint). It adds actual
binary address pricing, shared batches, stable occurrence routing, selected
cyclic coefficient products and source-volume bounds.
Earlier checkpoint sections below retain their historical scope and pending obligations.

## Current proof boundaries

> **Historical checkpoint.** This section records the state when it was
> written. Statements that the exact-half theorem was unfinished or that
> `2.99294792` was the current endpoint are superseded by the completed
> `2.9926862626` theorem described at the top of this document.

| Dependency | Established connection | Remaining obligation |
| --- | --- | --- |
| Original graph to modular counts | `GraphFoldedCountCorrect.finite_modCount` executes the new sources, LOW/HIGH join, exact normalization, band/block schedule and coefficient collection. It constructs its own finite fallback plan. | Replace the fallback `L=m,t=0` and exhaustive elementary completion with the optimized rounded plan and compatible shared batches. Finite correctness alone gives no improved running time. |
| Exact-half sources and retained graph preparation | Constructed good maps, rational/binary translation list, first-valid list indices, original-coordinate masks, cropped sources and the complete embedding are proved. Retained translation numerator arithmetic and character-state costs have been added. | Lift shared setup out of repeated schedules and close all remaining construction, selector, address and control costs on that executed path. |
| Rectangular base mathematics | The CW degeneration, independent-copy extraction, quantitative density/entropy bounds, positive fixed base and equal-copy rank conversion are proved. | The fixed positive-scale base is proved symbolically; it has not been materialized in runtime fixtures. The asymptotic program must retain this fixed base outside variable-size graph schedules. |
| Retained rectangular execution | The actual CW base now gives `CWBinaryScalarBound.exists_uniform_scalar_program`, including binary depth selection, arbitrary matrix dimensions, retained scalar arithmetic and exact recovery. Binary product and tensor-power address codecs have proved values and costs. | Refine every actual indexed access to the codecs, derive global retained-storage/address bounds, and combine address/control work with the scalar theorem. |
| Shared graph batches and rounded costs | Production prefix matrix banks and window completion use compatible middle-block columns. Stable own-request routing preserves duplicates and transposed IDs. Adaptive prefix selection, rounded independent batch fit, parameter setup and all 61 phase inequalities are proved. | Finish complete addressed execution and actual aggregate source/query costs, then connect the optimized graph backend to the analytic seven-term ledger. |
| Full APSP caller | The older concrete backend and adaptive theorem are closed at `2.99294792`. | Instantiate the caller with the improved backend and derive its complete `2.9926862626` cost from original graph hypotheses. None of the extension modules is yet in the closed theorem's import closure. |

The current remaining obligations are listed at the end of the
[addressed execution and source-cost checkpoint](#addressed-execution-and-source-cost-checkpoint).

## Original completion sequence (historical)

> **Historical checkpoint.** This section records the state when it was
> written. Statements that the exact-half theorem was unfinished or that
> `2.99294792` was the current endpoint are superseded by the completed
> `2.9926862626` theorem described at the top of this document.

The sequence below records the initial integration audit. Later checkpoints
in this document discharge several of its obligations, including the finite
LOW/HIGH join and original-count connection. Use the current boundaries above
and the latest checkpoint for present status.

1. **Value boundary now connected for one physical block and band pair.**
   `ExactHalfGraphSources.execute` consumes the callback's binary integer tables
   and retained physical dimensions, executes folded formation and band copies,
   constructs the actual good maps and inverse weights, retains the translation
   list and first-valid selectors, caches each band input once, and materializes
   both source arrays for every pair/run. Correctness identifies the exact inputs
   in `ExactHalfCroppedEmbedding`; source and copy costs use a derived cap of one.
   Remaining in this stage: share setup and bands across the outer schedule,
   price complete list state/control, and lower the inverse/selector/indexed
   construction to binary addresses. A noncomputable inverse-row implementation
   is no longer required on this program path. The existing parameter interface
   is supplied; choosing the new parameters and their asymptotic bounds remains.
2. Close the root representation boundary: select sufficient formal-degree
   storage inside the program, prove equality to the entire semantic root,
   enumerate the required good-set/channel families (including zeros), and
   charge every root and retained array. Prior checkpoints discharge the
   sufficient-degree/full-polynomial connection, physical-root identity,
   rare-support transfer, actual family enumeration and aggregate root-phase
   counters from graph sources.
   Prior checkpoints close the window adapter and lossless execution. Complete two-input product degree space, single channel shifts, actual signed
   binomial weights and retained degree sums are now implemented. Their source
   polynomial identity is connected to the assembled, unnormalized shifted LOW
   functional. The global physical LOW/HIGH algebraic connection remains.
3. The roots are now connected to `BinaryWindowPartition`, with lossless
   reconstruction of every retained degree and cyclic coefficient, binary
   channel counting, copies and a separate zero-residual branch. The opposite forward map and
   window-to-suffix permutation are now connected to those actual arrays. The
   retained-cell capped shared prefix encoder, actual folded request transport
   and elementary completion are connected and priced for a selected oriented
   root/window. This checkpoint executes and sums every window, proving the
   full single-root contraction and accumulation widths/costs; matching band
   and actual good-mask selection is implemented without removing requests.
4. Actual request rows, form transport and copied completion matrices are now
   constructed for each window of a selected oriented root/channel. The full
   physical-root query and actual band/mask selection are now executed and
   proved coefficientwise. Both oriented roots are now multiplied in full,
   shifted/weighted, and summed over the actual channel/run/translation indices
   for every mask pair. Exhaustive mask accumulation now selects the actual
   physical masks, and the shared run sum becomes the explicit equal-degree
   source functional. Physical-word reindexing and actual HIGH assembly are now
   proved. Join their LOW/HIGH contractions, then prove efficient routing, compatible shared
   batches and strict batch fit on the actual caller's geometry. Elementary completion is a correctness fallback, not the target
   cost. In parallel, discharge the mathematical rectangular dependency below;
   use its actual algorithm for fast grouped completion and charge its binary
   work and full outputs.
5. Join LOW and the already implemented cropped HIGH path using exactly the
   translated sources, locators, degree runs and `4^L` normalization in the
   embedding theorem. Produce the exact modular counts required by
   `BinaryTriangleExecution.Backend` for every actual factor history.
6. Prove full construction/control/address costs and the rounded exact-half
   entropy bounds for these same programs. Sum all families, translations,
   batches, windows, residual products, output incidences, setup, and failures.
   Derive the new callback bound; do not reuse old exponents by renaming them.
7. Instantiate the adaptive caller with that backend and transport the new
   callback bound through its actual setup and repeated calls. Prove the
   original-graph correctness-and-work theorem with exponent `2.9926862626`.

The remaining parts of steps 1–3 have substantial executable/formal integration work, not merely
missing theorem aliases. Step 4 has an additional mathematical obstruction:
for a scale `D`, establish an exact characteristic-zero rectangular
multiplication algorithm for
`ceil(D^(861/500)) x D` by `D x ceil(D^15)` with operation bound
`O(D^16.7220002)` (including the fixed positive allowance), together with
coefficient-growth and implementation/binary-cost bounds adequate for the
integer/cyclic application. The local TeX invokes arXiv:2307.07970v2,
Proposition 5.1 and Theorem 3.2, to obtain this from a CW tensor with `q=16`.
No corresponding extraction/asymptotic-sum proof or finite algorithm has been
formalized locally. `tensor_rank_one_expansion` and 61 numerical checks do
not establish it. Completing the requested exponent is therefore blocked by
missing mathematical machinery as well as the executable connections above.
Closing only the latter cannot finish the theorem.

The cited paper was checked directly during this audit. Its Proposition 5.1
is a degeneration to many interface tensors; Theorem 3.2 is the rectangular
asymptotic sum inequality. Its exponent definitions use arithmetic circuits.
These statements explain why an entropy witness alone is insufficient and
why the binary implementation theorem is a separate obligation. This is
missing formalization of cited mathematical machinery, not a claim that the
published theorem is an open conjecture.
[Primary source](https://arxiv.org/html/2307.07970v2).

## Previous root-to-window connection

> **Historical checkpoint.** This section records the state when it was
> written. Statements that the exact-half theorem was unfinished or that
> `2.99294792` was the current endpoint are superseded by the completed
> `2.9926862626` theorem described at the top of this document.

`GraphRootWindows.fromInputs` calls the existing actual graph-source/root-family
program once, then traverses its retained roots. It does not recompute sources,
translations, keys or roots. Each translation-list occurrence, degree run,
good-set pair and strict joint channel key has a window result for each input.
The input remains one physical block and band pair under the existing physical
parameter contract. Outer scheduling, sharing and new parameter selection are
still pending.

`ResidualWindowSource` copies every binary cell in each retained formal-degree
block, then flattens in degree-major, cyclic-residue-minor order. Type casts
align the already proved equal dimensions and erase at runtime. The proof
identifies each output column `d*C+r` with exactly its original root coefficient.
All binary copies are charged. The indexed-control allowance for flattening
conservatively pays for copying every accumulated prefix at each array append;
it does not assume destructive append optimization. Its polynomial degree-factor
overhead does not supply an asymptotic phase bound by itself.

`ResidualWindowSupport` transfers the existing whole-polynomial root support
through these casts and copies. A nonzero stored coefficient implies both
remaining rare-symbol caps. Consequently the side with more distinguished
channels (normal on a tie) has remaining budget `m/2-max(cn,co)`; the selected
crop is proved redundant for produced roots, without a supplied support premise.

`RetainedRootWindows` computes both channel weights with the existing binary
bit-count circuit and charged unsigned decoding. It then runs the actual
retained first-window program. At `L-m=0` it instead retains one copied source
component with no owner array or window search. Reconstruction is exact for
every degree/residue column and remains exact after arbitrary entangled linear
queries. Nonzero-dimensional components obey the existing light-window support
bound. All zero roots are retained. The flat source, every window component and
both channel counts are retained; no selected-coefficient projection is used.

`GraphRootWindows` connects these results back to original binary callback
inputs. Both `fromInputs_left_reconstruct` and `fromInputs_right_reconstruct`
identify the sum of actual windows with the corresponding previously proved
complete physical-root array. The window bit bound derives its magnitude
`2^m*(4^m*2^(L+m))` from the actual graph sources. It assumes no generated roots,
support certificate, coefficient bound or desired cost. Source/setup, root
and window counters remain separate. Binary channel/coefficient work is proved;
window searches, address arithmetic, array allocation and control still use
indexed-register annotations, not a full binary-machine lowering.

Writing `k=L-m`, `S=1` for `k=0` and `S=k` otherwise, the newly retained flat
sources and windows contain exactly
`2*J^2*(2*m+1)*K^2*H*(1+S)*3^(2*k)*(m+1)*C` coefficient cells. The enclosing
record also retains the original root arrays, whose separate cell count was
proved in `GraphResidualFamilies`. Repeated translation and request-column
incidences remain distinct; neither the program nor this count deduplicates them.

The subsequent transform/permutation checkpoint and the current capped prefix
checkpoint preserve the physical mask/channel associations and retained columns.
Actual request-list production, form transport and completion-matrix construction
remain pending. No source-to-completion or LOW/HIGH count theorem is claimed.
Steps 4–7 and the rectangular extraction/arithmetic/binary theorem above remain.

The new bounded fixture compares full copied roots with an independent dense
coefficient reference, and window ownership with an independent modular-index
scan. It covers channel binary counts through `m=5`, complete families through
`L=2`, a selected good-mask pair at `L=3,m=2`, and a nontrivial two-position
residual window at `L=4,m=2`. It also checks ties, both sides, zero dimensions,
empty families/columns, repeated request columns and the 65536 bit boundary.
The complete two-input outer container is evaluated only at `m=0`. Original
graph composition remains kernel-checked; the incomplete full/first-pair graph
and production FFT runtime attempts were not rerun.

## Previous checkpoint: graph windows through opposite transform and permutation

> **Historical checkpoint.** This section records the state when it was
> written. Statements that the exact-half theorem was unfinished or that
> `2.99294792` was the current endpoint are superseded by the completed
> `2.9926862626` theorem described at the top of this document.

`GraphWindowTransforms.fromInputs` runs the prior graph/root/window construction
once and retains it. It then applies `(s,v,w) -> (s+v,s-v,-w)` on each of the
`k=L-m` opposite positions, once each, for both input families. Every stage is
retained. Binary ternary addresses use `TernaryWindowAddress`; coefficients
consume stored bits through copy/add/subtract/negate circuits. The result has
magnitude at most `2^k*A`. A local ordinary-form identity and exact sequential
coefficient identity are proved. Every rare-pattern predicate is preserved,
and summing transformed windows equals transforming the complete original root.
That prior checkpoint supplied the local identity; the prefix-encoding checkpoint
below adds the full per-window tensor-query bridge.

`GraphWindowPermutations.fromInputs` clamps the requested length to
`ell=min(requested,k)` before making windows. For each actual window it reads
the retained channel counts, selects normal on a tie, and builds forward and
inverse position tables. The other half comes first; the selected half is
rotated so that exactly its selected cyclic window occupies the last `ell`
positions. The executable copy reconstructs old row addresses from the retained
inverse table and copies all degree/cyclic columns. Both graph-family
reconstruction theorems sum the outputs after undoing their respective retained
permutations and recover the transformed original root. Both graph-family
support theorems prove suffix rare count at most
`(m/2-max(cn,co))*ell/k`, with no supplied support certificate. At `k=0` the
opposite trace has no new layer and the permutation copies the sole empty-word
row; its suffix rare count is zero.

Each opposite trace retains `k*3^(2*k)*(m+1)*C` new coefficient cells. Each
permutation retains a further `3^(2*k)*(m+1)*C` cells and `4*k` position entries.
The entire permutation family is counted by traversing its actual nested
retained arrays: `2*J^2*(2*m+1)*K^2*H*S*3^(2*k)*(m+1)*C`, where `S=1` at
`k=0` and `S=k` otherwise. The enclosing record retains earlier arrays too.
All translation and request-column occurrences persist. The phase bit bounds
derive the actual graph magnitudes internally. Construction/allocation/table
arithmetic/control are explicitly indexed-register allowances, separate from
proved bit costs of coefficient circuits, ternary address arithmetic and
unsigned decoding. No native Lean performance or full binary-control claim is
made. No asymptotic aggregation of these phases is yet proved.

The bounded runtime fixture passed 16 reported groups (including repeated
zero/singleton length variants) plus completion in 7.5 seconds. Its independent
dense 3 by 3 tensor matrix and coordinate formula cover `k=0,1,2`, both sides,
ties, clamped lengths, caps, intermediate retention, zero columns, duplicate
columns and the 65536 bit boundary. Actual retained roots are checked against
an independent dense physical-root reference at `L=3,m=2`; the enclosing
both-input container is evaluated at `m=0`. Full graph-entry composition is
kernel checked. The expensive prior graph/FFT attempts were not rerun.

## Previous checkpoint: retained capped groups and shared prefix encoding

> **Historical checkpoint.** This section records the state when it was
> written. Statements that the exact-half theorem was unfinished or that
> `2.99294792` was the current endpoint are superseded by the completed
> `2.9926862626` theorem described at the top of this document.

`GraphPrefixProgram.fromInputs` consumes the actual retained graph permutation
result once. It traverses every existing translation-list occurrence, degree
run, good-set pair, strict joint channel key, input side and window. For each
window it computes the radius from its retained channel weights and clamped
length, then invokes `WindowPrefixProgram.execute`.

`RetainedCappedGroups` first enumerates the capped support keys and pair keys.
It constructs only `2^ell*H` groups of retained ternary prefix trees, where
`H=sum_{j<=r} binomial(ell,j)`. Each coefficient is a signed copy of an actual
binary input cell addressed by the concatenated prefix/suffix word. It never
serializes an intermediate integer view. `RetainedPrefixEncoder` shares the
four local contractions at each prefix node, recursively retaining their
outputs. Its exact tensor theorem ranges over all original prefix words.
Every formal-degree/cyclic column remains in every constructed row.

Initial groups contain exactly `2^ell*H*3^P*C` cells, where `P=2*k-ell`.
The full prefix trace, including its initial group arrays, is bounded by
`(P+1)*4^P*2^ell*H*C` cells. The separate group field references the same
initial arrays. Earlier graph/root/window/opposite/permutation storage remains
retained by the enclosing program. These statements count actual nested
arrays; they do not replace a dense uncropped construction by a desired bound.

The bit bounds include binary coefficient arithmetic, negation/copies and
ternary address circuits, with intermediate magnitude bounded by `2^P*A`.
The graph entry point derives `A=2^k*(2^m*(4^m*2^(L+m)))` internally and sums
actual channel-dependent radii. Key construction, allocation, tree traversal,
radius arithmetic and loop control remain explicitly indexed-register costs.
The prefix contraction includes a quadratic allowance for generated word-closure
traversals; the aggregate prefix control budget is conservative and polynomial
in prefix length times the capped encoded volume.
No full binary lowering, native Lean runtime bound or aggregate asymptotic
phase cost is asserted. Prior phase budgets remain separate and retained.

`CappedPrefixProgram.query_cropped` proves the complete prefix/suffix tensor
identity. Both graph query theorems discharge the crop using actual window
support, without an input support premise. `GraphPrefixTensor` carries that
identity back through the retained permutation and the adjoint of every actual
opposite axis to the original window coefficients. `originalForms_value`
exposes the explicit original-basis forms. The zero-residual branch has an
empty prefix/suffix and retains its single row; no positive-dimension premise
is introduced. Repeated input-column and translation occurrences persist.

At that checkpoint, the query was still a mathematical specification of
stored cells. The connected request/completion checkpoint below now executes
these queries and their form transport. Summing all lossless windows and
forming complete physical-root/LOW counts remains; neither checkpoint proves
the final APSP theorem or the missing rectangular algorithm.

## Previous prefix-encoding integration contract

> **Historical checkpoint.** This section records the state when it was
> written. Statements that the exact-half theorem was unfinished or that
> `2.99294792` was the current endpoint are superseded by the completed
> `2.9926862626` theorem described at the top of this document.

1. Request/form transport and elementary completion now execute from the
   actual binary target table for a selected oriented root/window. Next select
   the matching band and root-mask pair from retained request tags (swapping
   normal/opposite mask roles on the right), share matrices across requests,
   and execute all required window/root/channel instances. Join the executed
   tensor identity with lossless window reconstruction, then perform complete
   formal-degree/cyclic products and filters for the full physical-root query.
   Charge those aggregates and preserve every request/translation incidence.
   The current result does not already perform this contraction.
2. Prove compatible shared batches and strict fit, and execute their complete
   coefficient outputs. The elementary grouped product is a correctness
   fallback; the missing fast rectangular algorithm and its controlled binary
   implementation remain the exact mathematical dependency stated above.
3. Join LOW with cropped HIGH, the common degree runs/filters/locators and
   embedding normalization, yielding actual backend counts. Execute and price
   outer blocks/bands, share setup, close translation state/control and binary
   address lowering, prove rounded entropy/phase bounds, and integrate the
   adaptive caller. Ordered steps 4–7 remain open.

The bounded fixture compares all selected capped groups, prefix labels and
suffix queries with an independent dense four-by-three tensor matrix. It also
feeds actual retained physical roots through windows, the opposite transform,
permutation and prefix encoding. Zero dimensions, empty coefficients, duplicate
columns and the 65536 bit boundary are covered. Original graph composition is
kernel checked; the enclosing both-input container is evaluated only at `m=0`.
No incomplete expensive graph-source or production FFT attempt is rerun.

The rectangular extraction/asymptotic-sum and controlled exact finite arithmetic
algorithm remain missing formalization of published mathematics. Completing
this source path cannot establish the requested exponent without that theorem.
The old closed result remains `2.99294792` and imports none of these extensions.

The frozen full rebuild passed 214 modules and 2,849 axiom reports, with only
`propext`, `Classical.choice` and `Quot.sound`. All 16 bounded runtime groups
plus completion passed in 46.1 seconds, as did the numerical/finite suite and
exact-statement audit. No expensive incomplete runtime case was rerun.

Frozen source/configuration SHA-256 for the prefix-encoding checkpoint:
`6c7eae91ba38b7f40a55a36a888c8d0049e3b85de25305429d41c4e8ff1a7491`.


## Connected request/completion checkpoint

> **Historical checkpoint.** This section records the state when it was
> written. Statements that the exact-half theorem was unfinished or that
> `2.99294792` was the current endpoint are superseded by the completed
> `2.9926862626` theorem described at the top of this document.

Seven modules now implement the next source boundary: `GraphCompletionRequests`
generates folded requests from the original target cells and retains physical
labels and band/row/column/coefficient tags; `WindowCompletionRequests` constructs
opposite-oriented and permuted ordinary request forms; `PrefixRequestKey`
constructs prefix, pair and active keys by a charged retained-key scan;
`PrefixCompletionMatrices` copies all prefix leaves into shared concrete
support/coefficient matrices; `PrefixCompletionProgram` performs elementary
binary selector completion; `WindowCompletionProgram` and
`GraphPrefixCompletion` connect these executions to the retained graph program.

The public `fromInputs_tensor` theorem identifies every output coefficient
with the original selected window's full tensor and derives the crop premise
internally. `fromInputs_newBits` bounds all new binary target formation, copies
and completion arithmetic from original inputs. Its target-table bound uses
the sum of cell bit widths; this is conservative and must be sharpened for
final caller pricing via the existing per-cell `BinaryFoldedTargets.requests_cost`
contract. It is not already the desired asymptotic target-formation bound.
`execute_control` separately
bounds indexed decoding, position construction, form transport, pair scans,
selectors, tree traversal and full outputs. Original preparation is retained
once and its earlier counters are explicitly excluded from these new-phase
fields. All dimensions, including zero, retain the intended multiplicities.

This discharges the actual-request and completion-matrix portion of steps 3–4.
It does not aggregate all windows/roots/channels, filter the retained requests
by matching band/mask tags, produce a complete LOW count, or supply strict
batch fit. Elementary completion has no claimed fast rectangular exponent.
The finite next path is the three items above, followed by ordered steps 5–7.
The missing CW extraction/asymptotic-sum theorem is a substantial formalization
dependency, not a conjecture that these numerical/source checks resolve.

The immediate reusable lemma is `RetainedRootWindows.produce_contraction`.
For fixed actual residual labels, let `K(w)` be the product of the normal and
opposite ordinary local forms identified by `ordinary_forms`. The next exact
identity is that summing the executed completion output over every retained
window slot equals `sum_w K(w)*rootCoefficient(w,d,r)` for each formal degree
`d` and cyclic residue `r`. The new `fromInputs_tensor` gives each summand;
the retained lossless contraction supplies the right side. This still needs
an actual shared window-output collector and binary sum with derived widths,
plus the graph/root and request-label equality transports. Root selection can
use `RowIndexing.rowUnrank_good_rank` on retained tile rows: left normal/other
ranks are row/column, and right normal/other ranks are column/row. None of this
requires assuming a fast rectangular algorithm, so useful integration remains
feasible before the independent rectangular formalization blocker.

The bounded fixture passed 16 groups plus completion in 7.6 seconds. It includes
actual folded requests at n=0,2,5, all selected labels/caps, duplicated requests,
empty requests/columns, zero residual/window dimensions, both orientations and
an actual L=3,m=2 physical root checked by independent dense coefficient sums.
The full graph entry point is kernel checked only. Expensive incomplete graph
and FFT runtime attempts were not rerun.

The frozen full rebuild passed 223 modules and 2,911 axiom reports, using only
`propext`, `Classical.choice` and `Quot.sound`. The numerical/finite suite,
all 16 bounded runtime groups plus completion, and the exact-statement audit
also passed. The old closed theorem and all prior Lean sources are unchanged.
Frozen source/configuration SHA-256: `90a252a00a23149720a530e36e222598e506e0d322f835735df0ee25ffa6c739`.


## Connected full-root completion checkpoint

> **Historical checkpoint.** This section records the state when it was
> written. Statements that the exact-half theorem was unfinished or that
> `2.99294792` was the current endpoint are superseded by the completed
> `2.9926862626` theorem described at the top of this document.

The current program boundary is now original graph inputs → retained sources,
roots, windows, transforms and prefix traces → actual folded requests → every
executed window completion → binary all-window sum → matching band/mask
selection. The five new modules are `WindowCompletionRows`,
`RetainedWindowCompletion`, `GraphTargetWidth`, `GraphRootCompletion` and
`RootRequestSelection`. Public graph theorems supply no desired output, crop,
magnitude or cost assumption. They retain the existing physical parameter plan.

The executed single-root contraction is proved for every degree `0..m` and
every cyclic residue. Accepted masks are the actual retained mask entries for
the decoded physical rows; the right orientation swaps normal/opposite ranks.
Each request has a unique matching mask pair for its band and orientation.
This does not deduplicate channels, translation-list incidences or repeated
requests. Unmatched requests retain explicit zero rows and all columns.
The current selector is applied after all-window completion: no reduction of
that already executed work is claimed. Efficient root/batch routing must
precede completion in the final schedule, or its extra work must be charged
and shown to fit the desired bound.

The per-window magnitude is at most `2^(3*(L-m)+L+4*m)`; all-window accumulation
adds `slots(L-m).size` to this linear bit-width bound. Copies, all intermediate
sum additions, row-reference/selector arrays, layout collection and final
selection are charged. Binary coefficient arithmetic and indexed control
remain distinct. The maximum original target-cell bit width now replaces the
previous conservative sum-of-cell-widths estimate on this connected path.
Old selected-window theorems are preserved intact, including their older bound.

The finite next path is:

1. Pair the two oriented executed roots for the same physical request and
   channel incidence. Connect their full formal polynomials to the shifted
   five-term source split. Implement complete formal-degree multiplication
   over the cyclic coefficient ring, with enough output degree space and all
   cyclic residues, followed by the specified channel shift/filter. In the
   right root the normal/opposite mask and channel halves must be swapped;
   establish that transport in the actual retained strict-channel enumeration.
   Reuse or adapt the existing `BinaryLowQuery.polynomialDot` and `lowTerm`
   circuits only after proving their stored-block/shifted-form contracts for
   these new outputs, including the `actualWeights` binomial coefficients.
2. Execute the strict joint-channel sum and all required run/translation-list
   incidences with the original multiplicities and signs. Reuse prepared graph
   and request stores across roots rather than invoking `fromInputs` repeatedly.
   Derive the exact LOW count and its aggregate construction/copy/arithmetic
   counters. This checkpoint's `execute` can reuse a graph, but target formation
   is currently once per selected root, not globally shared by a family scheduler.
3. Connect actual source stores to cropped HIGH, combine LOW/HIGH with the
   same locators, runs, caps and `4^L` normalization, and obtain the required
   modular-count backend for one block/band pair. Then implement outer sharing
   and scheduling, compatible batches/strict fit and all repeated-call work.
4. Complete binary address/control and translation state construction costs,
   prove rounded exact-half entropy/phase bounds for these actual programs,
   and integrate the adaptive APSP caller. The independent rectangular
   extraction/arithmetic theorem below must supply an actual fast completion
   implementation before the final phase exponent can be proved.

The exact independent mathematical formalization still missing is a uniform,
exact characteristic-zero rectangular algorithm for
`ceil(D^(861/500)) × D` by `D × ceil(D^15)` with arithmetic exponent
`16.7220002`, plus coefficient-growth/bit-cost control and the finite-size
rounding/extraction interface needed by actual batches. Published CW
extraction/degeneration and asymptotic-sum mathematics is not an open conjecture;
its required formal dependency is absent here. Neither the 61 conditional
numerical checks nor elementary completion establishes this algorithm.

All 13 bounded runtime groups plus completion passed in 15.064 seconds,
including an actual two-window physical root and independent direct tensor
checks. Full graph executions are kernel checked only. Incomplete expensive
graph/FFT cases were not rerun. The numerical/finite suite and exact-statement
audit passed. The frozen full rebuild passed 226 modules and 2,965 axiom reports, using only
`propext`, `Classical.choice` and `Quot.sound`. The exact final source hash
was unchanged throughout verification. All 221 prior Lean modules and the
old closed theorem are preserved unchanged.

Frozen source/configuration SHA-256: `3694e17747b24ff63237d222731d893201a706fe639ae23850be5712f0101342`.


## Previous paired-product and family checkpoint

> **Historical checkpoint.** This section records the state when it was
> written. Statements that the exact-half theorem was unfinished or that
> `2.99294792` was the current endpoint are superseded by the completed
> `2.9926862626` theorem described at the top of this document.

The nine modules in this checkpoint are `ResidualChannelTranspose`,
`CompletedRootProducts`, `PairedRootRows`, `WeightedRootProducts`,
`GraphRootProducts`, `GraphRootProductCosts`, `GraphWeightedRootProducts`,
`RootProductCollection` and `GraphRootFamilyProducts`. All consume the existing
retained graph/root/window/completion path. The precise new endpoint is the
weighted source-polynomial sum for one fixed good-mask pair and one physical
block/band pair:

`sum(u,v,run,c) sum(d<t, card(c)<=d) residualWeight(2*m,t,d) *
    coeff(Pleft(u,v,run,c) * Pright(u,v,run,swap(c)), d-card(c))`.

This is coefficientwise over every cyclic residue and every original folded
request, with a band/mask acceptance predicate. Right masks are also swapped.
The polynomials are defined from source-root tensor contractions independently
of returned completion answers. The actual program computes and retains both
root rows, all `2*m+1` product degrees, every cyclic coefficient, signed weights,
all shifted terms and every stage of channel/run/translation accumulation.
Canonical key coverage and the proved transpose involution preserve the joint
channel incidence. Translation-list and request multiplicities are retained.
Empty channel/request arrays and the zero residual/formal cases are supported.

`GraphRootFamilyProducts.execute_bits`, `execute_control` and `execute_bound`
derive finite bounds for this exact executed aggregate from original input
bounds. Their costs include every unmatched request, both target formations
per leaf, the retained-key transpose scan, complete elementary completion,
all copies/products/weighted terms and full cyclic sums. Earlier graph
preparation is shared once and retains its existing separate ledger. Weights
are shared within each leaf's request array, not globally across all leaves.
Native indexing and control remain separate from binary coefficient arithmetic.
No fast phase bound, efficient routing or free request preparation is claimed.

The current finite remaining path is:

1. **Shifted LOW identity.** Identify each actual source polynomial with the
   appropriate cache factor in `TensorContraction.weighted_low_uses_small_channel_sets`,
   over the physical joint distinguished set of size `2*m`. Transport the
   actual mask layouts, ordinary labels and opposite halves, and reindex the
   canonical strict channel list to the filtered powerset. Use
   `LightSourceIdentities.shifted_pencil`, whose baseline is
   `-x1-x2+(1+z)*p1`. The old aligned polynomial baseline is different. Prove
   that the executed fixed-mask family sum is the required cropped LOW term,
   with all run and translation incidences. These are finite algebraic and
   reindexing obligations; the rectangular theorem does not block this step.
2. **Count-producing backend.** Route matching masks before completion or
   explicitly aggregate them with full costs. Execute cropped HIGH on the same
   retained graph sources, combine with LOW using the same runs, locators,
   bands and `4^L` normalization, and prove exact modular counts. One fixed
   mask/block/band sum alone does not meet this contract.
3. **Efficient schedule and full execution costs.** Share target formation and
   weight preparation where needed; construct compatible batches and strict
   fit, preserving every cyclic/formal coefficient and request multiplicity.
   Implement outer scheduling and charge all repeated calls, construction,
   copies, list state/control and binary addresses. Prove rounded exact-half
   entropy/phase inequalities for these programs.
4. **Fast rectangular implementation and caller.** Formalize the uniform
   exact rectangular algorithm of aspect `(861/500,1,15)` and exponent
   `16.7220002`, with controlled coefficient/binary work and finite-size
   extraction/rounding. The required CW degeneration/extraction and asymptotic
   sum machinery remains absent. Integrate this actual implementation into
   batches and then the adaptive caller. Published mathematics supplies the
   source, but numerical witnesses or elementary products do not prove this
   algorithm. The final `2.9926862626` theorem is therefore still blocked by
   missing formal mathematical machinery as well as steps 1–3.

All 13 bounded runtime groups plus completion passed in 44.838 seconds;
full graph/family evaluation is kernel checked only. Previously incomplete
expensive graph/FFT attempts were not rerun. The statement audit confirms the
old theorem still states `299294792/100000000` and uses only standard axioms.
The frozen full rebuild passed 235 modules and 3,050 axiom reports, using only
`propext`, `Classical.choice` and `Quot.sound`. Sources remained unchanged
through verification. All 226 prior Lean modules and the old closed theorem
are preserved unchanged.

Frozen source/configuration SHA-256: `4baaf08e3f69487cf8e14172a4ade32bb8887fb09577e76f572ab5e773877560`.


## Previous shifted-LOW checkpoint and ordered remaining path

> **Historical checkpoint.** This section records the state when it was
> written. Statements that the exact-half theorem was unfinished or that
> `2.99294792` was the current endpoint are superseded by the completed
> `2.9926862626` theorem described at the top of this document.

`GraphShiftedLow.fromInputs_value` now connects the actual weighted family
executor to the shifted LOW functional of the physically cropped raw source
and actual projected ordinary forms. The theorem covers every cyclic residue,
all runs and both translation-list indices for a fixed good-mask pair and one
physical block/band pair. The actual strict key list is reindexed bijectively;
right roots use swapped masks and channel halves. No returned query answer,
preprocessed root, magnitude or cost hypothesis is introduced. No runtime work
is added: the same collector and its existing input-derived finite budgets
are used. These remain elementary completion costs and indexed control counts,
not the target phase exponent or a complete binary address cost theorem.

The finite ordered path is now:

1. **Count-producing backend.** Aggregate or route matching mask pairs, prove
   the correspondence of these selected-mask expressions with the physical
   locator sums, and recombine actual degree runs. Connect cropped HIGH to the
   same retained graph stores and requests, combine LOW/HIGH and translations,
   and execute/prove `4^L` normalization and exact modular output counts. The
   fixed-mask LOW functional is now proved; calling it the full LOW count would
   still omit these obligations.
2. **Efficient schedule and complete execution costs.** Share target/weight
   setup, construct compatible batches and strict fit, retain every cyclic and
   formal coefficient and every request occurrence, and implement outer
   scheduling. Charge all construction, copies, repeated calls, translation
   state and binary address/control operations. Prove rounded exact-half
   entropy and phase inequalities for those concrete programs.
3. **Rectangular implementation and caller.** Formalize the uniform exact
   characteristic-zero rectangular algorithm of aspect `(861/500,1,15)` with
   work `O(D^16.7220002)` and controlled coefficient/binary work, including
   finite-size extraction/rounding. Formal CW degeneration/extraction and the
   asymptotic sum machinery remain missing. Published mathematics is not an
   open conjecture, but a numerical witness is not this algorithm theorem.
   Insert the implementation into the batches and adaptive caller.

Useful finite integration remains feasible before the rectangular machinery
is available, especially step 1. The complete requested exponent cannot be
proved merely by connecting the current elementary algorithm: it still lacks
both the fast rectangular formalization and the remaining count/cost/caller
contracts. The old theorem and all 235 prior Lean modules are unchanged.

The frozen full rebuild passed 241 modules and 3,078 axiom reports, using only
`propext`, `Classical.choice` and `Quot.sound`. Sources stayed frozen throughout.
All five bounded runtime groups plus completion passed in 8.007 seconds; the
independent nonzero reference gives residues [-6272, 21952, -15680] for the
full two-position case. The statement audit preserves the old exponent, and
the applicable finite/numerical suite passed. All 235 prior Lean modules and
all nineteen earlier frozen snapshots are preserved.
Frozen source/configuration SHA-256: `b70a80234bcd5dd03f97f5a4c8ff716d7fe0323898433f9ca90a3884b9ce4bcc`.


## Previous all-mask and shared-degree checkpoint

> **Historical checkpoint.** This section records the state when it was
> written. Statements that the exact-half theorem was unfinished or that
> `2.99294792` was the current endpoint are superseded by the completed
> `2.9926862626` theorem described at the top of this document.

The actual program now executes and retains **every good-mask pair** for one
physical block/band pair. `GraphLowMaskAssembly.fromInputs_value` proves that
its binary cyclic accumulator selects exactly the good-mask ranks of the
actual physical folded request, or zero for a different band pair. The
canonical masks and physical outside labels are identified with the decoded
row/column geometry. No source, output, magnitude or desired cost is supplied.
All unmatched children, repeated setup, references and accumulations remain
executed and charged. The new finite magnitude bound is `G^2` times the prior
fixed-mask family bound; graph preparation remains shared with separate costs.

`GraphLowRunSources` replaces every retained run coefficient with the original
masked Walsh formula of the actual input-derived band. The normal crop is
proved redundant for that source. `GraphLowRecombination` reindexes the run
array to every integer in `[-m,m]` once. `GraphLowDegreeFilter.fromInputs_value`
then proves the equal-signed-degree expression for the actual all-mask output:
left degree is opposite-W minus normal-p2; right degree has the reversed sign.
Only equal degrees in the original interval pair, exactly once. The proof
preserves all translation-list and request incidences and every cyclic
coefficient. It does not optimize away the executed run loops.

The finite ordered completion path is now:

1. **Global physical LOW/HIGH composition.** Reindex the assembled source
   coordinates into full physical words on the selected good masks. Ordinary
   shifted normal forms vanish on `p1`, which justifies the omitted outside
   `p1` cases. Identify the resulting global LOW query with the physical
   support/key interface used by cropped HIGH. Execute actual HIGH key lookup
   and accumulation on the same retained sources, caps, runs, translations,
   locators and requests. This is still finite integration, not blocked by
   rectangular extraction.
2. **Exact count and normalization.** Join the shifted five-term LOW/HIGH
   identity to `ExactHalfCroppedEmbedding.complete_embedding` and the actual
   input-band source formulas. Prove that the *combined* numerator equals
   `4^L` times the intended product, prove divisibility, execute normalization
   and extract the requested cyclic coefficient. Isolated LOW need not be
   divisible by `4^L`. Complete the band/block output schedule.
3. **Efficient execution costs.** Replace or price exhaustive unmatched work,
   share setup, construct compatible batches and strict fit with all degrees,
   cyclic columns and occurrences retained, and implement outer scheduling.
   Charge complete translation state and binary addresses/control; prove
   rounded exact-half entropy/phase inequalities for the actual programs.
4. **Rectangular algorithm and caller.** Supply the missing formal uniform
   exact characteristic-zero multiplication algorithm for aspect
   `(861/500,1,15)` with `O(D^16.7220002)` arithmetic and controlled binary work,
   including CW degeneration/extraction, asymptotic-sum machinery and finite
   rounding. Integrate it into batches and the adaptive caller. This missing
   formalization is a genuine blocker to the requested exponent, not an open
   mathematical conjecture or a numerical-inequality obligation.

The new statement is an assembled, unnormalized LOW functional for one
block/band pair, not a complete LOW/HIGH count or the requested APSP theorem.
All 241 prior Lean modules and the old theorem remain unchanged. Finite steps
1–2 remain feasible; the new milestone does not close them implicitly.
The frozen full rebuild passed 248 modules and 3,109 axiom reports, using only
`propext`, `Classical.choice` and `Quot.sound`. Sources stayed frozen throughout.
All seven bounded runtime groups plus completion passed in 35.986 seconds; the
independent nonzero reference gives residues [-6272, 21952, -15680] for the
full two-position case. The statement audit preserves the old exponent, and
the applicable finite/numerical suite passed. All 241 prior Lean modules and
all twenty earlier frozen snapshots are preserved.
Frozen source/configuration SHA-256: `d1fca8d872a5579f0e045182af3ca75f18bda5eb1658f1ffe87d6011bc1f20bb`.


## Previous physical-word and executed HIGH checkpoint

> **Historical checkpoint.** This section records the state when it was
> written. Statements that the exact-half theorem was unfinished or that
> `2.99294792` was the current endpoint are superseded by the completed
> `2.9926862626` theorem described at the top of this document.

`GraphPhysicalLow.fromInputs_value` now reindexes the executed all-mask LOW
output into physical source words, using inverse retained layouts and the
vanishing outside normal `p1` forms. `GraphHighFamily.execute` prepares actual
physical requests once and executes every translation/run HIGH child on the
same retained raw stores. All query keys, lookups, full cyclic rows, rejected
band requests, references and accumulations are retained and charged.
`ShiftedPhysicalHigh.fromInputs_value` identifies this actual HIGH output with
its physical-word five-form leaf convolution and stored query. Literal binary
normal/private and opposite ROM entries are proved to match those forms.

No full-count claim follows from these two separate identities alone. The
ordered remaining path is:

1. **Join the two physical contractions.** Identify
   `GraphPhysicalLow.kernel` and its outside products with the selected support
   of `CroppedHighQueries.geometry`, including the ordering of both physical
   halves. Transport integer forms and raw coefficients into the cyclic ring.
   Apply the shifted five-term LOW/HIGH identity to the actual two executors,
   with the same translation occurrences, run indices, bands and requests.
   Reuse `GraphLowRunSources.fromInputs_raw` and `RetainedDegreeRuns.sum_runs`;
   do not assume that the individual LOW or HIGH value is a matrix product.
2. **Normalize and schedule the exact count.** Use the actual decoded masks,
   outside locators and `ExactHalfCroppedEmbedding.complete_embedding` to prove
   the combined numerator is `4^L` times the intended band product. Derive
   divisibility, execute normalization, extract the requested coefficient and
   complete the band/block schedule. This is still finite integration and is
   feasible without the rectangular theorem.
3. **Efficient costs for the actual program.** Replace exhaustive unmatched
   completion by proved routing/batches and strict fit, share setup, retain all
   degrees/cyclic columns/occurrences, and charge outer scheduling, translation
   state and full binary addresses/control. Prove rounded exact-half entropy
   and phase bounds. Current finite mixed counters do not establish this bound.
4. **Formal fast rectangle and caller.** Prove a uniform exact characteristic-
   zero rectangular multiplication algorithm at aspect `(861/500,1,15)` with
   `O(D^16.7220002)` arithmetic work and controlled coefficient/binary work,
   including finite extraction and rounding from CW degeneration/extraction
   and asymptotic-sum machinery. Integrate it into the batches and adaptive
   caller. The published mathematics is not an open conjecture; the required
   algorithm formalization is absent. Numerical inequalities cannot supply it.

The old closed theorem's import closure stays 129 modules and contains none
of the 121 extension modules. All 248 previous Lean sources remain byte-for-byte
unchanged. The new endpoint remains one block/band pair's unnormalized LOW and
HIGH functionals, not a complete APSP count or a target exponent theorem.
The frozen full rebuild passed 256 modules and 3,170 axiom reports, using only
`propext`, `Classical.choice` and `Quot.sound`. Sources stayed frozen throughout.
All seven bounded runtime groups plus completion passed in 5.990 seconds; the
statement audit preserves the old exponent, and the finite/numerical suite
passed. All 248 prior Lean modules and twenty-one earlier frozen snapshots
are preserved. Production FFT/full graph execution remains kernel checked only.
Frozen source/configuration SHA-256: `eb366ccc35697f6e75c444968ddb9c7d63b2665c0ef6fa0939e3d9ccbb0fc9fb`.


## Previous joined and normalized retained-band checkpoint

> **Historical checkpoint.** This section records the state when it was
> written. Statements that the exact-half theorem was unfinished or that
> `2.99294792` was the current endpoint are superseded by the completed
> `2.9926862626` theorem described at the top of this document.

The physical join and the scaling/normalization part of the preceding steps
1 and 2 are discharged. `GraphLowHighJoin.joined_fromInputs` joins both actual
executors, `GraphLowHighScale.fromInputs_scale` proves their complete numerator
is `4^L` times the retained band product, and
`GraphNormalizedBand.fromInputs_value` proves actual binary division returns
each exact cyclic coefficient. Divisibility is derived, never assumed.
The retained children, reference arrays, shared binary divisor, complete
numerators and quotients are explicit. Bounds price divisor construction,
addition and division from proved graph-input magnitudes; the earlier HIGH
mixed charge and indexed control remain distinct from binary arithmetic.
Shared graph preparation is still separately charged by prior modules.

The finite ordered path is now:

1. **Original folded requests and scheduling.** For each original folded
   request, use the existing actual band-copy and row-ranking refinements to
   identify `GraphLowHighScale.entry` with its zero-padded original matrix
   entry. Materialize and copy the requested cyclic coefficient from each
   retained normalized output; prove the matching band pair occurs exactly
   once. Execute and charge all band pairs and graph blocks, including
   unmatched work until a better route is proved. Reuse folded-count identities
   to establish the complete count. No supplied count values are permitted.
2. **Efficient actual costs.** Prove compatible routing/batches, strict fit,
   shared setup, all degrees/cyclic columns/occurrences, translation state and
   binary address/control prices. Establish rounded exact-half entropy/phase
   bounds. Current exhaustive elementary completions and generous widths do
   not imply the target asymptotic bound.
3. **Formal fast rectangle and adaptive caller.** Formalize the uniform exact
   characteristic-zero algorithm for aspect `(861/500,1,15)` with arithmetic
   `O(D^16.7220002)`, finite extraction/rounding and coefficient/binary costs
   from CW degeneration/extraction and asymptotic-sum machinery. Then insert
   the proved algorithm into the compatible batches and connect the adaptive
   caller. The published mathematics is not open; this formal machinery is
   absent. A numerical certificate cannot replace it.

The first step is a feasible finite integration task; it is not blocked by
missing rectangular machinery. The final exponent genuinely requires that
substantial absent algorithm formalization as well as steps 1 and 2.
The closed theorem's local import closure remains 129 modules, containing
none of the 131 extension modules. All 256 prior Lean modules are unchanged.
The frozen full rebuild passed 266 modules and 3,231 axiom reports, using only
`propext`, `Classical.choice` and `Quot.sound`. The numerical/finite suite passed
under Python 3.12; the first Python 3.9 attempt failed on an existing union-type
annotation and was superseded without source changes. The exact statement
audit preserves the old exponent. All 256 previous Lean modules, unrelated
user work and twenty-two earlier frozen snapshots are preserved.
The new runtime fixture passed six groups plus completion in 3.652 seconds;
its actual source/query cases use `m=0,L=0..1` and an elementary cyclic base.
Nonzero-m combined graph execution and production FFT remain kernel-checked
scope, without a completed full runtime fixture. Prior incomplete attempts
were not repeated. All previous evidence and snapshots are preserved.
Frozen source/configuration SHA-256: `b111c275d763463786ffb13d803493959d92ed240cfe13e289a71ebe3b04713b`.


The immediate scheduling proof can reuse
`BinaryBackendExecution.makeLeftBandStored_view` / `makeRightBandStored_view`,
`ThinMatrixBackend.makeLeftBandStored_refines` / `makeRightBandStored_refines`,
`makeLeftBand_value` / `makeRightBand_value`, `storedLocate_refines`,
`RowIndexing.rowUnrank_value`, `genuine_tile_product`, and `padMiddle_product`.
`GraphCompletionRequests.prepare_get` and `locate_tags` identify the actual
folded request and selected coefficient. The needed new contract is that the
**new** `GraphNormalizedBand.execute` outputs, after collection over their
actual matching band pair, equal the original folded matrix-product request.
The old `ThinMatrixBackend.queryGlobal_correct` illustrates the band transport
but executes a different backend; citing it alone does not establish this
contract. Then `FoldedBackendExecution.semanticCoefficient_count` and the
physical/grouped incidence identities can identify the collected block counts.


## Previous original-count scheduling checkpoint

> **Historical checkpoint.** This section records the state when it was
> written. Statements that the exact-half theorem was unfinished or that
> `2.99294792` was the current endpoint are superseded by the completed
> `2.9926862626` theorem described at the top of this document.

`GraphFoldedCountCorrect.modCount` closes the original folded-request,
requested-coefficient and band/block scheduling correctness boundary for any
existing valid plan. `finite_modCount` supplies its own proved finite fallback
plan. Both refer to the actual new retained LOW/HIGH program. All band pairs,
blocks, requests and cyclic coefficients execute; repeated preparations and
unmatched children remain retained. The count is nonnegative and at most the
block width. No returned count or oracle premise is used.

This discharges the correctness portion of the preceding step 1. New binary
copy/addition costs and schedule/reference-array indexed control are proved.
The complete cost portion is **not** discharged: the propagated preparation
ledger already omits translation-list generation and binary control prices.
The exhaustive scheduler repeats that setup for each band pair, and the
fallback plan uses `L=m,t=0`; no optimized asymptotic cost follows.

The remaining ordered path is:

1. **Construct the production callback and optimized plan.** Supply the
   chosen physical factors/block widths and rounded exact-half parameters
   from the actual adaptive caller; prove the plan's fit, turn the retained
   nonnegative cells into its count-table interface, and retain all parameter
   construction. The finite fallback proves existence/correctness, not the
   needed production choice. Refactor actual shared requests, good maps,
   translations and folded sources before claiming shared setup costs.
2. **Efficient execution and complete prices.** Route requests into compatible
   retained capped batches with strict dimensions and preserve occurrences,
   formal degrees and full cyclic outputs. Prove all construction and binary
   address/control work, including translation-list generation and retained
   state/control. Price the actual optimized schedule and establish rounded
   entropy/phase inequalities. Current elementary multiplication, exhaustive
   band scheduling and conservative widths do not have the target bound.
3. **Uniform exact rectangle and final caller complexity.** Formalize the
   characteristic-zero matrix algorithm of aspect `(861/500,1,15)` with
   arithmetic `O(D^16.7220002)`, finite extraction/rounding and coefficient/
   binary costs, from CW degeneration/extraction and asymptotic-sum machinery.
   Insert that actual algorithm into the compatible batches, then prove the
   adaptive APSP caller's complete bound. The published mathematics exists;
   its required formal algorithm is absent. Numerical inequalities are not
   this theorem.

Steps 1 and substantial parts of 2 are feasible formal integration tasks.
The full requested exponent also requires the substantial missing formal
rectangle machinery in step 3; it cannot be closed by further count identities
or conditional ledgers. The old theorem and all 266 previous Lean modules are
unchanged. Its 129-module local import closure contains none of the 139
extension modules. The frozen full rebuild passed 274 modules and 3,270 axiom reports,
using only `propext`, `Classical.choice` and `Quot.sound`. The numerical/finite
suite and exact statement audit passed. All 266 prior Lean modules, unrelated
user files and twenty-three previous frozen snapshots are preserved. The seven-group bounded fixture passed in 3.254 seconds;
complete program runtime coverage is limited to empty graphs. General
positive-size graph execution and production FFT are kernel checked only.
All earlier snapshots/evidence and unrelated user work are preserved.
Frozen source/configuration SHA-256: `b8c0bff07126e22887292bddc87ba9e2a0476f2ed592da16fe5002519277bd67`.

The next concrete caller boundary is `BinaryTriangleExecution.positiveTable`
and its `HistoryPayload`, whose positive branch is currently typed to
`BinaryFoldedFactory.Payload` and executes the old producer. A new callback
must retain `GraphBlockSchedule`'s actual payload and use the new count and
nonnegativity proofs when constructing `BinaryControllerExecution.Table`.
Reusing the old `positiveTable_modCount` alone would still certify the old
program. `BinaryTriangleSetupCosts.preparePlan` provides charged native
geometry loops for the old parameter choice; the new rounded parameter
program must refine the selected exact-half dimensions, not merely reuse that
old choice or the finite fallback. `ExactHalfCroppedEmbedding.shifts` already
uses the shared-denominator binary numerator implementation, but
`ExactHalfSourcePlan.prepare` discards its arithmetic charge and does not price
its state/control. Reconnecting that retained charge and proving the missing
control/state work is a concrete prerequisite to a complete setup bound.


## Setup-charge repair and speed-proof contracts

> **Historical checkpoint.** This section records the state when it was
> written. Statements that the exact-half theorem was unfinished or that
> `2.99294792` was the current endpoint are superseded by the completed
> `2.9926862626` theorem described at the top of this document.

Finite modular-count correctness remains the endpoint. The executed
`ExactHalfSourcePlan.prepare` now retains the generated payload and the sum
of generation and inverse-weight arithmetic. Generation uses materialized
keys and signed binary character sums, with explicitly decoded score indices.
Its list refines the prior list exactly. `produce_bits` bounds the actual
numerator/addition/decoding counter by `2^m poly(m)`; `produce_control` bounds
key construction and state-loop indexed operations. Neither theorem prices
all control of the score kernel. The scheduler's existing
`preparationRecorded -> band.operations -> child.operations -> recordedWork`
path retains these repaired counters. A stored power table is generated once
per preparation, not once globally across the exhaustive schedule.

Audit of the complete current scheduler, from its retained definitions:

| Boundary | Retained charge / remaining contract |
| --- | --- |
| Translation generation | Numerator power/product/sum/comparison arithmetic, binary signed-sum updates/decoding, key formation and state array loops retained. Still missing selection cube/zero scans, retained row/sign transitions, native score-index construction, power-table control and binary lowering of bounded addresses. |
| `ExactHalfSourcePlan.prepare` | Now adds the actual generator counter and keeps its payload. Inverse candidates, weight tables, first-valid selectors and shift copies remain charged. Native indexed control remains distinct from binary execution. |
| `ExactHalfGraphSources.execute` | Constructs shape, selectors and folded sources afresh for each band pair. Shape operations, selectors, folded arithmetic, band copies and source-family charges reach `preparationRecorded`. Shared setup and formation/metadata control must be constructed and priced, not credited speculatively. |
| `GraphPrefixProgram` | Root keys/families, windows, transforms, permutations and prefix encoders all reach `preparationRecorded`. Existing conservative bounds and indexed controls do not prove optimized phase costs or binary addresses. |
| `GraphNormalizedBand` / `GraphBandSchedule.band` | LOW, HIGH request formation/execution, full cyclic output normalization, reference arrays and requested-coefficient copies are retained. HIGH is still a mixed ledger; no globally complete binary control theorem follows. |
| `GraphBandSchedule.execute` | Executes every band pair; nested accumulators sum every child charge including unmatched requests. `accumulationBudget` still contains actual child charges. It is not a derived phase bound. |
| `GraphBlockSchedule` | Retains all block charges, index/reference arrays and incidence copies. `recorded_work_le` remains a partial mixed bound; its sum does not repair omitted child work. |
| `FiniteFoldedPlan` / adaptive caller | Fallback parameter construction is unpriced and unoptimized. The old caller still has its old payload/plan. A new retained callback and charged rounded plan must be constructed. |

The ordered remaining speed-proof work is finite in outline, although some
steps require substantial new mathematics in the library:

1. Replace score enumeration/zero tests and row/sign closures with retained
   loops; price their operations, power-table construction and bounded
   integer/index arithmetic. Lower the resulting complete setup to the
   selected binary/address model. The current repair discharges the binary
   character-sum update and charge-retention parts of this step.
2. Lift shared shape/selectors/folded sources and requests out of actual
   band-pair loops; prove the new schedule's values and costs. Construct
   occurrence-preserving compatible batches, strict rectangular fit and
   every intermediate formal/cyclic output. Then prove the optimized rounded
   parameter/entropy/phase bounds, replacing conservative finite widths only
   where the proof justifies it. This is local algorithm integration, not a
   consequence of numerical certification.
3. Prove and compile the exact rectangular algorithm described below. Its
   result must replace elementary completion in the actual compatible
   batches, with coefficient/copy/address costs retained.
4. Construct the new adaptive callback and plan, use the original-count
   correctness theorem for its table interface, and prove the complete
   adaptive APSP cost. Preserve the old closed theorem until this closes.

### Exact rectangular bottleneck: formalization, not impossibility

> **Historical checkpoint.** This section records the state when it was
> written. Statements that the exact-half theorem was unfinished or that
> `2.99294792` was the current endpoint are superseded by the completed
> `2.9926862626` theorem described at the top of this document.

The required contract is an actual uniform exact program, with no oracle or
runtime-bound premise: for all integers `D>=1` and integer matrices of shapes
`ceil(D^(861/500)) x D` and `D x ceil(D^15)`, return their exact product,
including every output entry. Establish arithmetic cost `O(D^16.7220002)`
with fixed constants and appropriate finite-size padding. To use it here,
also prove input-dependent intermediate numerator/denominator widths,
exact denominator clearing/recovery, copies and binary arithmetic costs.
For a fixed finite rational base, the desired width statement is
`O(B+log D)` for inputs of at most `B` bits; the resulting polynomial bit
factor must be absorbed using explicitly reserved exponent slack. The
output alone has about `D^16.722` entries. An infimum inequality or a supplied
rank/cost certificate is not yet this uniform exact program theorem.

Published route (the paper contribution summarized here): the big CW tensor
has asymptotic rank at most `q+2`. Proposition 5.1 extracts independent
interface tensors from its powers; at level one these become products of
matrix-multiplication tensors. Theorem 3.2 converts such a direct sum into a
rectangular exponent bound. Section 3.3 uses polynomial degenerations, and
Section 3.11 supplies progression-free hashing sets. These are arithmetic
rank/exponent statements, not this repository's binary executor theorem.
Source: [Vassilevska Williams, Xu, Xu and Zhou, arXiv:2307.07970v2](https://arxiv.org/html/2307.07970v2).

The local specialization is `outputs/exponent-improvement.tex`, lemma
`light-cw` near line 3587: CW parameter 16, a fixed rational six-type witness,
level one, and a strict margin before `16.7220002`. Its rational logarithm
checks certify scalar inequalities. They do not construct the extracted
coordinate sets, establish tensor identities, or prove rank-to-algorithm
and coefficient-growth claims. The positivity, integral type counts, zero
penalties and cyclic dimension permutation must accompany the extraction
proof. The finite base must be chosen with strict slack; no finite algorithm
attaining the exponent infimum is required or claimed.

Local inventory at the pinned mathlib revision:

- The project has binary integer circuits, exact cyclic convolution,
  elementary rectangular/grouped completion, retained arrays and charged
  copying/accumulation. `TensorContraction.tensor_rank_one_expansion` is a
  finite contraction identity, not CW rank or the asymptotic sum theorem.
- Mathlib supplies tensor products/associators and multilinear maps,
  matrices and polynomial algebra; `Lagrange.eq_interpolate` supplies exact
  polynomial interpolation. Multinomial coefficients and Stirling estimates
  are available. `Behrend.roth_lower_bound` already supplies a quantitative
  large progression-free set theorem over integers; adapting it to the
  required cyclic hash/extraction contract is still work.
- The current checkpoint below adds a CW coefficient definition, a checked
  polynomial certificate, tensor-power composition and coordinate pullback.
  Abstract border/asymptotic tensor rank, independent-copy extraction,
  the rectangular asymptotic sum inequality and a uniform rank-to-binary
  compiler remain absent. These are missing formal results, not merely
  missing syntax for applying an existing theorem.

The first rectangle step now has a finite CW16 polynomial certificate with
18 separated terms. It remains to prove how its evaluated
linear forms and coefficient extraction produce an exact bilinear program,
including dimensions, rational coefficients and work. A convenient concrete
representation is finite coefficient arrays with polynomial entries; a
finished certificate and compiler correctness theorem matter more than a
new abstract tensor definition. Follow with the level-one rational type-class
and progression-free extraction proof, rectangular asymptotic sum theorem,
then finite-base recursion and padding. Fixing a finite base makes its
constants independent of input size; that observation must be formalized
with recursive coefficient and exact-recovery bounds. It does not authorize
assuming the final algorithm or counting its construction as free per input.

For uniformity, an existential choice of separate circuits at each size is
insufficient. One proved finite rational base plus a computable recursive
padding/tiling program is enough in principle. Its initial finite search can
be a fixed input-independent cost only after termination and decidability of
the certificate checker are proved, or a concrete checked base is supplied.
For coefficient growth, generic circuit depth is insufficient: use the
bilinear structure to bound the two input linear-form paths and output
recombination separately. Rational coefficients must remain rational through
all degenerations and interpolation; an arbitrary-field rank infimum alone
does not supply the required denominator bounds. These are precise proof
obligations, not evidence that the published exponent is false.

A concrete next certificate can be stated without asymptotic-rank notation.
Let `q=16`, `X=sum_i x_i`, `Y=sum_i y_i`, `Z=sum_i z_i` for `i=1..q`,
and define the polynomial in `lambda`

```
P = lambda * sum_i (x0 + lambda*xi)(y0 + lambda*yi)(z0 + lambda*zi)
    - (x0 + lambda^2*X)(y0 + lambda^2*Y)(z0 + lambda^2*Z)
    + (1-q*lambda)(x0 + lambda^3*x17)(y0 + lambda^3*y17)(z0 + lambda^3*z17).
```

The current checkpoint proves this proposed certificate, independently
checks the coefficient conventions, and proves tensor-power composition.
Degrees 0, 1 and 2 vanish; degree 3 is exactly CW16; degree is at most 10.
At that checkpoint, exact interpolation with `(10*N+1)*18^N` terms and
its construction/bit costs were not yet proved. The later exact interpolation
checkpoint below now proves the finite decomposition, integer-arithmetic
counts and retained-value bit bounds; complete binary costs remain open. The existing polynomial
certificate does not assert exact rank 18 for CW16 over Q.

Nothing found shows a Lean expressiveness obstruction or a mathematical
impossibility. The main obstacle is a substantial absent formalization,
including constructive uniformity and bit-growth bridges; local execution
integration is additional work. This audit is not a proof of the paper's
specialization. No completion estimate follows from the module count.

The frozen full rebuild passed 277 modules and 3,307 axiom reports, using
only `propext`, `Classical.choice` and `Quot.sound`. Numerical/finite checks,
the exact statement audit, the four-group cost fixture (5.873 seconds) and
the prior bounded scheduler regression passed. The old closed
APSP theorem still proves `2.99294792`, and the target `2.9926862626` remains
unproved. All twenty-four earlier frozen snapshots are preserved.
Frozen source/configuration SHA-256: `0b81c9d97ea21665b01740e95d993308ab0f227991baadcbbad727f150b4a5c3`.


## CW certificate checkpoint and its initial extraction path

> **Historical checkpoint.** This section records the state when it was
> written. Statements that the exact-half theorem was unfinished or that
> `2.99294792` was the current endpoint are superseded by the completed
> `2.9926862626` theorem described at the top of this document.

The candidate is valid. `CWPolynomialIdentity.expansion` proves its full
symbolic expansion for arbitrary q over a commutative ring, including the
error coefficients in degrees 4, 6, 7, 9 and 10. `CWPolynomialCertificate`
defines the CW coefficient tensor separately, proves equality with the
leading coefficient, and builds `cw16` and `cw16Power n`. Scalar term data
is computable and specializes correctly; the semantic polynomial certificate
uses mathlib's noncomputable polynomial operations. No choice of a fast
rectangular algorithm or desired bound appears as a premise.

The reusable interface has an explicit finite term index, coefficientwise
coordinate pullback and tensor products, and a proved bilinear interpretation
of separated terms. For every n, `cw16Power n` witnesses `18^n` terms,
leading order `3*n`, degree at most `10*n`, and `18^n` coordinates on each
axis. It covers n=0 and permits later coordinate restrictions without changing
the term budget. This is polynomial degeneration data, not an abstract rank
or border-rank theorem, an interpolation compiler, or the required exponent.

At the certificate checkpoint, the finite dependencies were as follows.
The exact interpolation checkpoint below updates step 1 and its remaining
binary-cost scope.

1. Build explicit rational interpolation at `10*N+1` distinct rational nodes,
   apply coefficient extraction at `3*N`, and retain the weighted evaluated
   separated terms. Prove exact target equality, term-count overhead,
   construction operations and rational numerator/denominator bounds.
   `Lagrange.eq_interpolate`, `termsAt` specialization and the bilinear
   interpretation are available. The polynomial certificate alone does not
   price this operation.
2. Define the matrix-multiplication coefficient tensor and identify the six
   CW coordinate blocks. Under the standard convention X=(row,inner),
   Y=(inner,column), Z=(column,row), types 011, 101, 110 have shapes
   respectively <1,1,16>, <16,1,1>, <1,16,1>; corner types 002, 020, 200
   are scalar. Then index words by integral rational type counts and prove
   their constituent tensor-product identities. These block identifications
   are the next algebraic lemmas, not yet installed theorems.
3. For the exact six-type distribution in local lemma `light-cw`, prove
   independent-copy extraction via coordinate zeroing/reindexing, preserving
   the marginal type classes and eliminating mixed-block terms. The needed
   asymptotic contract is: for every positive epsilon and arbitrarily large
   admissible N, extract at least exp(N*(min(H(X),H(Y),H(Z))-epsilon))
   independent copies of <16^(p*N),16^(15*p*N),16^((861/500)*p*N)>.
   Admissibility includes integrality of all six type counts. Prove the
   unique compatible distribution and progression-free hashing bound;
   numerical marginal inequalities do not establish this tensor identity.
4. Formalize the rectangular asymptotic sum argument with cyclic permutation,
   combine it with the certificate/interpolation and rational logarithm
   enclosures, and choose one finite rational base using the strict allowance
   before 16.7220002. An exponent infimum is not an executable uniform bound.
5. Construct the recursive exact program, padding and output copying; bound
   both input linear-form paths and output recombination to control rational
   coefficients and exact denominator recovery. Connect this program to the
   already identified graph batches, rounded phase bounds and adaptive caller.

Steps 1-2 are finite algebra/compiler work using the new interface. Steps
3-4 are the main missing extraction and asymptotic-sum formalization from
[arXiv:2307.07970v2](https://arxiv.org/html/2307.07970v2), not an unresolved
claim about the published mathematics. Step 5 and the separate scheduling/
control roadmap are additional uniformity and binary-cost obligations. No
completion estimate is justified by the number of checked modules.

The independent exact polynomial checker passed 6,056 triples; the scalar
Lean fixture passed 24,224 rational entries in 5.726 seconds. The full frozen rebuild
passed 281 modules and 3,340 axiom reports, using only `propext`,
`Classical.choice` and `Quot.sound`. The numerical/finite suite and exact
statement audit also passed.
No previous graph/FFT runtime attempt or denied process inventory was repeated.
All 25 earlier frozen source snapshots and all 277 earlier Lean modules are
preserved. The old closed APSP theorem still proves 2.99294792; 2.9926862626
is unproved.
Frozen source/configuration SHA-256: `81758711a5bc3539647986a448b354c483a7a842308fe73b53c2e97f9c6853d4`.


## Exact interpolation checkpoint: the first finite extraction step

> **Historical checkpoint.** This section records the state when it was
> written. Statements that the exact-half theorem was unfinished or that
> `2.99294792` was the current endpoint are superseded by the completed
> `2.9926862626` theorem described at the top of this document.

The preceding roadmap's first algebraic extraction obligation now has a
constructive exact result: `CWExactDecomposition.terms_total` gives
`(10*n+1)*18^n` separated rational terms for CW16 to the nth tensor power,
including n=0. It uses mathlib interpolation and the existing polynomial
certificate, not an assumed rank or extraction oracle. The actual integer
program executes the corresponding bilinear map with one shared nonzero
signed denominator and exact final divisions. Inputs and outputs are not
assumed precomputed. See the README checkpoint for the explicit operations
and coefficient/denominator bounds.

This discharges finite rational coefficient extraction and provides a dense
reference execution with charged integer arithmetic. It does not discharge
complete binary control/address costs or give the desired fast rectangular
algorithm. In particular the dense linear forms in this reference execution
have exponential dimension; its honest work bound is not the rectangular
phase bound. Preparation has a separate indexed-control bound, but copies,
key enumeration, addressing, basis tests, branch/counter work and binary
arithmetic refinement of the whole evaluator remain a compiler obligation.
Retained-value polynomial bit bounds are available to that future refinement.

The finite ordered path is now:

1. Identify the six CW blocks as matrix-multiplication tensors, with the three
   non-scalar shapes <1,1,16>, <16,1,1>, <1,16,1>, and prove word/type tensor
   products. This is the next concrete algebraic prerequisite.
2. Prove independent-copy extraction for the specified rational type counts:
   coordinate zeroing/reindexing, compatible marginal classes, no mixed terms,
   and the progression-free hashing cardinality estimate. The required
   exponential copy lower bound and integrality conditions above are unchanged.
3. Formalize the rectangular asymptotic sum argument, cyclic permutations and
   strict numerical specialization, then select a finite rational base for
   exponent allowance 16.7220002. This is missing formalization of published
   mathematics, not evidence that the result is mathematically impossible.
4. Compile that base recursively, pad/reindex inputs and copy outputs, and
   bound rational coefficients, exact recovery, every binary arithmetic path
   and control/address operation. The current reference evaluator and shared
   denominator bounds are reusable foundations, not that finished compiler.
5. Connect the constructed rectangular program to efficient graph batches,
   optimized rounded phases, remaining setup/control charges and the adaptive
   APSP caller. The existing finite fallback count theorem is unchanged.

The exact fixture checks 592 Vandermonde moments, all 5,832 n=1 CW coordinates
and 81 selected n=2 coordinates. Native Lean tests cover interpolation degrees
0,1,2,3,10,20 and actual n=0 and n=1 bilinear executions (3.381 seconds).
The full frozen rebuild passed 293 modules and 3,448 axiom reports,
using only `propext`, `Classical.choice` and `Quot.sound`. The numerical/finite
suite and exact statement audit passed. All 281 prior Lean modules and 26 prior
snapshots remain unchanged. The old closed theorem still proves 2.99294792;
the requested 2.9926862626 theorem remains unproved.
Frozen source/configuration SHA-256: `2d59d6de9b8b142f60109e524f3d3ae1dc53c17cd44072a5fcb95128394518e1`.

Verification recovery note: the original verifier tool session was interrupted
during its final module, after 292 completed modules and 3,442 axiom reports.
The completed reports were revalidated against the unchanged frozen sources;
the final module was recompiled with `warningAsError=true` and exit code 0.
Pinned dependencies, Lean version, roots, all 3,448 reports and the source hash
were checked again. `verification-output.txt` explicitly records this recovery.
The interrupted raw log and resumed tail remain in the frozen staging directory.

## CW block and finite independent-copy extraction checkpoint

> **Historical checkpoint.** This section records the state when it was
> written. Statements that the exact-half theorem was unfinished or that
> `2.99294792` was the current endpoint are superseded by the completed
> `2.9926862626` theorem described at the top of this document.

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

## Next quantitative extraction contracts

> **Historical checkpoint.** This section records the state when it was
> written. Statements that the exact-half theorem was unfinished or that
> `2.99294792` was the current endpoint are superseded by the completed
> `2.9926862626` theorem described at the top of this document.

The block, type and finite restriction steps of the preceding plan are now
proved as described in the README checkpoint. The finite extraction is
connected to the exact CW decomposition and target aspect. It does **not**
yet prove how many target-shaped copies survive at large tensor powers.

The immediate missing combinatorial statement is the finite counting form
of [VXXZ24 Claim 5.5](https://arxiv.org/html/2307.07970v2#S5.SS2): for prime
M>2, over all M^(n+2) choices of the offsets b,w0 and n coordinate weights,
a fixed compatible triple reaches a specified common bucket in exactly
M^n choices. Two distinct triples sharing one coordinate block reach that
same bucket in exactly M^(n-1) choices (n>=1). These require explicit
bijections solving two or three independent linear constraints; the
hash relation alone does not prove them. Distinct color words differ by
1 or 2 at some coordinate, so M>2 supplies an invertible coefficient.
The published argument also needs type-class regularity and a large
progression-free bucket set. The source's Claims 5.6–5.7 perform the
subsequent survival estimate; our symmetric cleanup needs its own bound.

A sufficient finite next contract for this cleanup is as follows. Let E
be the full reference marginal class, T=|E|, and P its number of ordered
pairs sharing any coordinate block. For a progression-free B modulo M,
prove there is a hash choice whose actual kept set has size at least
T*|B|/M^2 - P*|B|/M^3, interpreted over the rationals. This follows by
summing the two exact counting statements and the already proved cleanup
inequality. It is currently **unproved**, not a new hypothesis smuggled into
a completed speed theorem. Derive regular degrees D_X,D_Y,D_Z and
P=T*(D_X+D_Y+D_Z-3) for the actual type class, then select M at least twice
their sum to obtain the needed finite survival estimate. No two distinct
compatible words share two whole coordinate words, which must also be
proved for that collision count.

The remaining finite ordered path is:

1. Prove the hash counting bijections and type-class degree/cardinality
   formulas; obtain the survival bound for the actual symmetric cleanup.
2. Construct suitable modular progression-free sets and choose prime sizes;
   derive the entropy-scale copy lower bound from exact multinomial counts.
   Mathlib has `ThreeAPFree` and Behrend results over natural numbers, but
   the modular embedding, quantitative parameters and this extraction
   application are not present locally. Available exact starting points are
   `Behrend.roth_lower_bound_explicit` (N>=4096) and
   `Nat.exists_prime_lt_and_le_two_mul`. Embedding a natural progression-free
   set from a short interval into ZMod M must prove that sums do not wrap;
   the required three-term modular property does not follow from casting alone.
3. Prove the rectangular asymptotic sum inequality and combine the copy
   lower bound with the exact `(10*n+1)*18^n` decomposition. Formalize the
   strict logarithm/entropy specialization and choose a finite rational
   base within exponent 16.7220002. Neither decomposition size alone nor
   the two-copy example implies that exponent.
4. Compile the chosen base into a uniform recursive rectangular multiplier,
   including padding, coordinate enumeration/reindexing, copies, coefficient
   growth, exact recovery, binary arithmetic and every address/control cost.
5. Integrate that multiplier with efficient graph batches, optimized rounded
   phases, the remaining setup/control charges and the adaptive APSP caller.
   The existing finite graph modular-count endpoint uses its honest fallback
   plan and does not establish the requested fast bound.

These are missing formalizations and program refinements, not a claim that
the published mathematics is impossible to formalize or mathematically
open. The old closed APSP theorem remains 2.99294792. The requested complete
2.9926862626 theorem remains unproved.

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

> **Historical checkpoint.** This section records the state when it was
> written. Statements that the exact-half theorem was unfinished or that
> `2.99294792` was the current endpoint are superseded by the completed
> `2.9926862626` theorem described at the top of this document.

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

## Next type-class and asymptotic contracts

> **Historical checkpoint.** This section records the state when it was
> written. Statements that the exact-half theorem was unfinished or that
> `2.99294792` was the current endpoint are superseded by the completed
> `2.9926862626` theorem described at the top of this document.

The earlier roadmap's finite hash-counting and finite survivor inequality
are now proved. Its exponential-rate requirement is unchanged. The first
remaining exact combinatorial theorem is regularity of the constructed
reference type class, not an independence assertion about hashes.

For E=`CWFilteredHashCounts.fullClass n reference`, construct its three
images X,Y,Z under wx,wy,wz. Prove that for every x in X the actual fiber
`{u in E | wx u=x}` has the same size D_X=T/|X|, and likewise for Y and Z.
The reference word supplies nonemptiness. A concrete proof path is to
transport words by simultaneous coordinate permutations: each color image
is a complete marginal type class, and its permutation action transports
fibers bijectively. Mathlib already provides `DomMulAct.stabilizer_card`
and `MulAction.card_orbit_mul_card_stabilizer_eq_card_group` for the counting
step; an adapter from nested CW words to functions on Fin n and the
identification of the actual marginal classes with permutation orbits still
need proofs. The existing `CWWordCollisions` results ensure that
no distinct pair shares two coordinate words. Derive the exact collision
identity P=T*(D_X+D_Y+D_Z-3), with natural-number subtraction handled
using D_X,D_Y,D_Z>=1. These statements are not yet formalized.

Next count E and the marginal images by exact multinomial formulas, choose
a prime M comparable to D_X+D_Y+D_Z, and construct a large ThreeAPFree set
inside ZMod M. Mathlib's Behrend and Bertrand lemmas are available, but the
no-wrap modular embedding and the required quantitative parameter choices
remain missing. Combine these facts with the new finite survivor inequality
to obtain the exponential copy rate min{H(X),H(Y),H(Z)}. The huge canonical
reference period and target aspect from the previous checkpoint are
already proved; they are not a substitute for this rate theorem.

Then prove the rectangular asymptotic sum argument, strict entropy/logarithm
specialization and finite rational base selection within 16.7220002.
Compile the chosen base into a uniform recursive binary multiplier with
coefficient growth, exact recovery and all address/copy/control costs.
Finally connect efficient graph batches, optimized rounded phases,
remaining setup/control work and the adaptive APSP caller. The old closed
theorem remains 2.99294792; the requested 2.9926862626 theorem is unproved.

Source correspondence: the exact fixed-bucket counts formalize the finite
uniform-space content of [Claim 5.5](https://arxiv.org/html/2307.07970v2#S5.SS2).
The survivor inequality proved here is for the repository's conservative
symmetric cleanup. It does not assert that the paper's asymmetric cleanup
or its complete Proposition 5.1 has been formalized.

Frozen source/configuration SHA-256: `7380a16ffdd885fa5b35f1a2a2496e8432f1f15e31aeb5324a78de7d414f3699`.

## Type regularity, multinomial counts and finite density bound

> **Historical checkpoint.** This section records the state when it was
> written. Statements that the exact-half theorem was unfinished or that
> `2.99294792` was the current endpoint are superseded by the completed
> `2.9926862626` theorem described at the top of this document.

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

## Remaining quantitative extraction path after regularity

> **Historical checkpoint.** This section records the state when it was
> written. Statements that the exact-half theorem was unfinished or that
> `2.99294792` was the current endpoint are superseded by the completed
> `2.9926862626` theorem described at the top of this document.

The preceding checklist's regularity, exact collision count, multinomial
cardinalities and finite prime selection are now proved. The new density
bound is still finite; an exponential copy rate has not been established.
The next dependencies, in order, are:

1. Construct an explicit progression-free subset of ZMod M with density
   at least exp(-C*sqrt(log M)) for all sufficiently large M, for a fixed C.
   Transport mathlib's natural-number Behrend set into a short interval
   before reducing modulo M, proving that a modular three-term progression
   cannot wrap. Small M and all parameter inequalities need separate bounds.
2. Prove the quantitative multinomial/entropy bounds for the three actual
   marginal classes of repeated canonical CW reference words. Combine them
   with the finite density theorem to obtain the exponential copy rate
   min{H(X),H(Y),H(Z)}, with an explicit subexponential loss. The enormous
   canonical period and aspect identities do not themselves give this rate.
3. Prove the rectangular asymptotic sum argument for the exact rational
   restricted decomposition, the strict logarithm/entropy specialization,
   and a finite base selection meeting w=16.7220002 at aspect
   (861/500,1,15). This published mathematical argument still needs its Lean
   formalization; no assumed rectangular oracle has been introduced.
4. Construct the uniform recursive binary multiplier and bound coefficient
   growth, exact recovery, generation, addressing, copies and control. The
   current finite existence proofs and unpriced Nat.find selector are not
   that executable complexity theorem.
5. Connect efficient graph batches, optimized rounded phases, remaining
   setup/control bounds and the adaptive APSP caller. Preserve the old
   2.99294792 theorem until the complete replacement is genuinely proved.

All earlier sources and frozen snapshots remain preserved. No new axiom,
sorry, commit or push is introduced by this checkpoint.

Frozen source/configuration SHA-256: `ea7f05b91af35162e9d69110a71316bd75b72efd775394f15e24d6b3b43a5316`.

Local APIs for the next step are already present in mathlib:
`rothNumberNat_spec N` gives a subset of `Finset.range N` attaining the
natural-number Roth number, and `Behrend.roth_lower_bound` proves
`N * exp(-4*sqrt(log N)) <= rothNumberNat N` for every N, including the small
cases. Both are in `Combinatorics/Additive/AP/Three` (`Defs.lean` and
`Behrend.lean`). A concrete next proof can take N=floor(M/2), prove that
natural-number sums below 2N do not wrap modulo M, and transport cardinality
and ThreeAPFree into ZMod M. For M>=3, N>=M/3 and log N<=log M suggest the
finite target density `(1/3)*exp(-4*sqrt(log M))`. This modular transport
and real inequality have not yet been formalized here. A Roth-number
maximizer existence theorem must not be reported as a fast bucket generator;
constructing or pricing the chosen finite witness is a separate obligation.

## Constructed modular buckets and unconditional finite survival

> **Historical checkpoint.** This section records the state when it was
> written. Statements that the exact-half theorem was unfinished or that
> `2.99294792` was the current endpoint are superseded by the completed
> `2.9926862626` theorem described at the top of this document.

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

## Remaining extraction path after modular Behrend

> **Historical checkpoint.** This section records the state when it was
> written. Statements that the exact-half theorem was unfinished or that
> `2.99294792` was the current endpoint are superseded by the completed
> `2.9926862626` theorem described at the top of this document.

The explicit modular set, no-wrap/cardinality transport, all-selected-prime
density bound and its connection to actual cleanup are now proved. A fast
bucket generator and priced hash selection are not proved. The current
reference construction deliberately enumerates 2^floor(M/2) candidates.

1. Establish quantitative multinomial entropy estimates for the actual
   three marginal classes of repeated canonical reference words, including
   rounding and zero/small-length conventions. Combine them with the proved
   loss exp(-4*sqrt(log 12+n*log 6))/72 to obtain the exponential copy rate
   min{H(X),H(Y),H(Z)}. The finite formulas and canonical aspect alone do not
   establish this rate.
2. Prove the rectangular asymptotic sum theorem for the actual exact rational
   direct-sum decomposition. Specialize the strict entropy/logarithm bounds
   and select a finite base meeting w=16.7220002 at aspect (861/500,1,15).
3. Construct and price the uniform recursive binary multiplication program,
   including coefficient/denominator growth, exact recovery, finite-witness
   generation, addresses, copies and control. Finite existence and exhaustive
   search correctness must not be relabeled as the required speed theorem.
4. Connect efficient graph batching, optimized rounded phases, remaining
   setup/control bounds and adaptive APSP caller complexity. The existing
   closed 2.99294792 theorem remains intact; 2.9926862626 is unproved.

The analytic source used in this checkpoint is the pinned mathlib theorem
`Behrend.roth_lower_bound` in
`Mathlib/Combinatorics/Additive/AP/Three/Behrend.lean`, together with
`rothNumberNat_spec` and `ThreeAPFree.le_rothNumberNat` in that directory's
`Defs.lean`. The new Lean modules prove the missing modular transport and
actual-selector instantiation rather than adding a published result as an axiom.

Frozen source/configuration SHA-256: `38d5d4593ca50df6431c273a33bf782cfe8c34d7e1f54c4cca5a84243e13bf44`.

The next entropy step can reuse local results rather than add Stirling as an
assumption. `EntropyBounds.choose_entropy_lower_of_le` and
`choose_entropy_upper_of_le` already handle finite binomial endpoints.
Mathlib's `Nat.multinomial_insert` splits a multinomial into a binomial times
a smaller multinomial. Applying it twice to the three marginal counts gives
two binomial factors; the two lower-bound denominators are at most (n+1)^2.
The missing algebraic bridge is the entropy chain identity converting their
two binary entropies to the three-symbol entropy, with zero counts handled
explicitly. For repeated canonical references, the existing
`CWCanonicalType.reference_counts` and `reference_length` supply exact scaled
counts and total length. A subsequent limit estimate must absorb both
2*log(n+1)+log(72) and 4*sqrt(log 12+n*log 6) into epsilon*n. None of these new
multinomial entropy or rate statements is claimed by this checkpoint.

## Actual target marginal entropy and exponential extraction rate

> **Historical checkpoint.** This section records the state when it was
> written. Statements that the exact-half theorem was unfinished or that
> `2.99294792` was the current endpoint are superseded by the completed
> `2.9926862626` theorem described at the top of this document.

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

> **Historical checkpoint.** This section records the state when it was
> written. Statements that the exact-half theorem was unfinished or that
> `2.99294792` was the current endpoint are superseded by the completed
> `2.9926862626` theorem described at the top of this document.

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

> **Historical checkpoint.** This section records the state when it was
> written. Statements that the exact-half theorem was unfinished or that
> `2.99294792` was the current endpoint are superseded by the completed
> `2.9926862626` theorem described at the top of this document.

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

> **Historical checkpoint.** This section records the state when it was
> written. Statements that the exact-half theorem was unfinished or that
> `2.99294792` was the current endpoint are superseded by the completed
> `2.9926862626` theorem described at the top of this document.

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

> **Historical checkpoint.** This section records the state when it was
> written. Statements that the exact-half theorem was unfinished or that
> `2.99294792` was the current endpoint are superseded by the completed
> `2.9926862626` theorem described at the top of this document.

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

> **Historical checkpoint.** This section records the state when it was
> written. Statements that the exact-half theorem was unfinished or that
> `2.99294792` was the current endpoint are superseded by the completed
> `2.9926862626` theorem described at the top of this document.

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

> **Historical checkpoint.** This section records the state when it was
> written. Statements that the exact-half theorem was unfinished or that
> `2.99294792` was the current endpoint are superseded by the completed
> `2.9926862626` theorem described at the top of this document.

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

> **Historical checkpoint.** This section records the state when it was
> written. Statements that the exact-half theorem was unfinished or that
> `2.99294792` was the current endpoint are superseded by the completed
> `2.9926862626` theorem described at the top of this document.

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

> **Historical checkpoint.** This section records the state when it was
> written. Statements that the exact-half theorem was unfinished or that
> `2.99294792` was the current endpoint are superseded by the completed
> `2.9926862626` theorem described at the top of this document.

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

> **Historical checkpoint.** This section records the state when it was
> written. Statements that the exact-half theorem was unfinished or that
> `2.99294792` was the current endpoint are superseded by the completed
> `2.9926862626` theorem described at the top of this document.

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

> **Historical checkpoint.** This section records the state when it was
> written. Statements that the exact-half theorem was unfinished or that
> `2.99294792` was the current endpoint are superseded by the completed
> `2.9926862626` theorem described at the top of this document.

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

## Addressed execution and source-cost checkpoint

> **Historical checkpoint.** This section records the state when it was
> written. Statements that the exact-half theorem was unfinished or that
> `2.99294792` was the current endpoint are superseded by the completed
> `2.9926862626` theorem described at the top of this document.

The frozen verification passed **502 modules and 4,848 axiom reports**, using
only `propext`, `Classical.choice` and `Quot.sound`. Source/configuration
SHA-256: `f1a93c88a816e1d76fa9c953e3a074170ce9a1978f9eb0a6bab6c5dde34b2a57`.

This checkpoint connects binary matrix-address operations to retained shared
prefix and window completion. It prices padded storage, input gathering,
internal arrays, projected outputs, matrix tiles and recursion. Stable own-band
routing preserves original occurrence IDs and duplicates; selected cyclic
products read the requested coefficient while retaining full coefficient
vectors during preprocessing. HIGH preparation reuses source encodings.

Actual source, root, channel-type, own-band, completion and HIGH volumes have
proved bounds, alongside the rounded independent fit and 61 numerical phase
checks. The executable optimized LOW/HIGH backend and complete aggregate
runtime/caller proof are still being integrated. Newer scratch proofs are not
part of this frozen verification. The complete theorem remains **2.99294792**;
the requested **2.9926862626** theorem is unfinished. The closed theorem's
129-module import closure contains none of the 367 extension modules.

Both canonical/research and results Python verification suites were rerun and
passed, reproducing all stored certificate outputs. No mathematical witness
or canonical TeX source changed in this checkpoint.
