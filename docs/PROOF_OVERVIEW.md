# Proof overview

The authoritative argument and its scope are in [the LaTeX note](../outputs/exponent-improvement.tex). The strongest current integer APSP bound is deterministic `O(n^2.9926862626)`, a small refinement using exact-half structured sources and shared residual completion. The earlier Walsh-reindexed polynomial-cache bound `2.99294792` remains valid. The earlier partial-cache `2.993401` proof remains valid. The ten-term construction gives deterministic `O(n^2.9958892)` and Las Vegas expected `O(n^2.995535)`. This page explains these reductions and the related 3SUM, real-input, convolution, and subset-convolution results. No unrestricted bound below `2.99` has been proved here.

## Exact-half refinement: `2.9926862626`

Allow the translation list's bias to shrink with the tensor parameter: `epsilon=1/(2m)`, with `64m^3` entries. Exact conditional expectations construct the list in `2^m poly(m)` bit operations. Every invertible binary change of basis and every translation then has average Hamming weight below `m/2+1/4`; integrality guarantees a list entry of weight at most `floor(m/2)`. The original masks and complete-output crop give this cap in both source halves.

The grouped-source proof accepts this stronger cap and a shorter suffix exponent `zeta=.22`. A refined rational witness passes [61 inequalities](../outputs/verify_half_source_apsp.py) for `2.9926862626`, with runtime slack above `8.43e-11` and geometry slack above `2.19e-10`. The earlier witness remains valid. This is a small numerical refinement, much of which uses prior rounding slack; the strengthened source lemma does not remove the existing box/query bottleneck or the scoped `2.99268` exclusion. The exact-half lemma in [the proof](../outputs/exponent-improvement.tex) gives the argument for all parameters; [the published check suite](../scripts/verify_structured_sources.py) reproduces the finite evidence.

## Light structured sources: `2.9926863`

The shifted private factor exposes an ordinary basis with a rare symbol. Deterministic small-bias translations partition every original middle summand exactly once, and limit each normal source to `floor(.51m)` rare symbols. Equality of the original degree runs permits the same cap on the opposite half when both residual and box encoders use the cropped source. Complete outputs retain the original Walsh normalization.

After contracting distinguished positions first, a cyclic-window partition gives short suffixes with sparse rare supports. Each source is explicitly duplicated into its compatible pair-bit groups; requested suffixes become subset-selector rows. Shared matrix products across middle blocks complete these rows, with asymmetric row chunks chosen from a proved first-power specialization of the SODA 2024 CW theorem. The positive rectangular-algorithm allowance remains in every cost.

A separate high-box encoder retains the joint private-position cap, giving exponent `T-G`. Residual encoding, source roots, complete cyclic vectors, every short padded chunk, and the independent batch-width condition are charged. The [canonical certificate](../outputs/verify_light_source_apsp.py) checks 61 strict inequalities plus the exact bias-potential inequality, with runtime slack above `3.25e-8`. This is a change to the source algorithm, whereas the earlier `2.99294792` refinement only tightened a target within its existing cost family. The standard verification command reproduces the accompanying structured-source checks; finite checks supplement the asymptotic proof.

## Deterministic exact counts through signed windows

For arbitrary targets `T`, shift `A,B,T` together to nonnegative integers and reveal their bits from most to least significant. Maintain exact counts of original middle labels with signed gap `A+B−T` in `{-1,0,1}` for every pair and middle block. All prefixes start at zero. One refinement maps a gap to `2gap+alpha+beta−gamma`; a new gap in the window must have come from the old window.

Start each composite modulus at 3 so the three target residues are disjoint. The total modular count equals the known genuine window count plus a nonnegative false count. Greedily select all fixed `R` prime factors, minimizing the total modular count over active incidences. Divisor averaging makes the total false mass at most one quarter of the number of incidences. Equality with the known count certifies at least three quarters of them. Four products masked by the next two input bits then give exact parity subclasses at those incidences; the target bit enters only a scalar update. Restart on the remainder, and repeat at each input bit.

The constant targets and masks and logarithmic levels reuse the earlier aligned oracle and its strict 47-inequality certificate. Count tables cost `O(n^3/h)`, already charged. This proves deterministic exact all-edges #Exact Triangle and min-plus witness multiplicities in `O(n^2.99294792)`. It counts middle labels in one matrix product, not shortest paths. The older randomized counting argument remains valid with its original guarantee.

## Deterministic 3SUM and exact counts at 1.9931055

Choose the bucket prime and sub-buckets from the original full values once. Keep the compatible `(sub-bucket A, sub-bucket B, target)` incidences fixed through every bit level. Each contains at most `s²` original pairs, and there are `O~(n²/s)` incidences. Prefix coalescence changes histogram multiplicities, never original memberships. The signed-window argument therefore applies to these pairs even though their prefixes need not obey the old bucket congruence.

For a composite `m=dq`, keep factor 3 physically folded and use coefficient vectors over `Z[x]/(x^q−1)`. The histogram product has inner dimension `D=d` and outer dimension `N=O((n/s)sqrt(d))`. A requested folded entry and cyclic coefficient count the same original pairs modulo both coprime factors. Three offsets and four parity masks suffice. Histogram formation costs `O(n+qND)`; prime-selection sums count each incidence separately even when query answers coincide.

The witness uses `c=10.83107856`, `theta=.06504251269`, `b=.04436367207`, `s=n^b`, and `R=10^9` prime factors, freezing `S=884889170` physically. Thus `u=.0785138659123489638`, `v=.0102134782276510362`, and the candidate cost is `2b/R`. Final savings for boxes, residuals, stored reads, and source encoding all exceed `.0068945`, with more than `1.4238e−8` slack; the original tile margin exceeds `.03415`. Both phase endpoints are certified. This proves deterministic integer 3SUM and exact #3SUM at `1.9931055`, including the one-set distinct-element correction. Its source transfer gives MonoConvolution at `1.4991368`; since the incidence counts are exact per target, All-Integers 3SUM has the same exponent and the Lincoln–Polak–Vassilevska Williams reduction then gives MonoConvolution at `1.498271`. These reductions retain their original witnesses; the separate source construction above improves APSP.

## Earlier improvement: Walsh embedding and a joint polynomial cache

Change the local five-term identity so its private kernel is `P=(-x1-x2)(2s)` and its inner kernel is `I=2p1s+p2w`. This aligns one factor of the private and inner terms. The four ordinary paired forms still sum with `P` to `I`, so the stopping-box decomposition retains its form. The new opposite coordinates use `s+v` and `s-v`, however, so the original matrix embedding must be proved again.

Apply unnormalized Walsh transforms to the original matrices' opposite outer indices. Source entries also receive a factor of two for each normal `p2` position. The good-set maps and degree filters ensure that inner channels match and unwanted opposite `w` positions vanish. A transpose character map of the restricted `Delta` matrix locates each output. Walsh orthogonality then shows that the complete degree-summed output is exactly `4^L` times the original product entry. The original good-set capacity and full-grid tile condition `N>=K N0` remain unchanged, with exponent `T=c-1+cH(1/c)/ln4`.

Introduce a separate formal variable `z` and set `H(z)=-x1-x2+z p1`. Then

```
P+zI = H(z)(2s) + z p2w.
```

Cache `H,p2` on normal coordinates and `2s,w` on opposite coordinates, alongside the four ordinary forms. Retain at most `m` distinguished positions in each physical half and at most `t=ceil(2theta m)` channel positions across both halves jointly. For each residual query, the two input lookups use the same physical channel subset. There is one binary channel choice at each position; no extra per-channel alphabet factor is needed. The joint binomial tail yields residual exponent `Q=2H(theta)/ln4` for `0<theta<1/2` and encoder exponent `E=T+Q`. Every intermediate array is paid for by its disjoint all-ordinary completions, so this count covers the entire encoder.

A channel subset `C` contributes one shift `z^|C|`; the residual extracts coefficient `j-|C|` with the usual signed binomial weight. Polynomial degree is only `O(log n)`. Stored-box base cases use the constant coefficient `H(0)`, which restores the exact private kernel. They do not use the entire cached polynomial. The stored-box query exponent remains `q2=Q+2theta`, and tile geometry uses `T`, not `E`.

For composite incidence counts, work over `Z[x]/(x^q−1)` and keep `x` separate from `z`. Preprocessing stores and charges all cyclic coefficients; a requested residual coefficient costs `O~(q D^Q)`, while stored boxes cost `O~(D^q2)` through scalar coefficient reads. Walsh transforms, source weights, internal encodings, and normalization have polynomial magnitude and logarithmic coefficient bit length. Assemble every residual and box contribution and sum all source degree runs before dividing the complete numerator by `4^L`. This division is exact coefficientwise over the integer cyclic ring, regardless of the parity of `q`; no arbitrary-ring division or separate divisibility of individual terms is assumed.

The normalized oracle returns the same exact modular count as before, so the composite selection and incidence-halving proof applies unchanged. The witness uses `c=10.66550171`, `theta=.06529782140`, `b=.04604634600`, `R=1000000000`, and `S=768979045`. Its folded exponent is `u=.03540867517281957`, cyclic exponent `v=.01063767082718043`, and inner exponent `e=.08145502117281957`. The candidate charge is `eta=b/R=.000000000046046346`. After charging it, every runtime saving exceeds `.007052` with more than `8.12e−8` strict slack. Both endpoints of both modulus phases are checked. The stage count is a large fixed constant; the proof charges its fixed polylogarithmic factors. This parameter refinement improves the earlier `2.992949` witness without changing the oracle.

The [47-inequality certificate](../outputs/verify_five_term_aligned_apsp.py), [original-matrix embedding checks](../outputs/check_five_term_aligned_embedding.py), [compact cache checks](../outputs/check_five_term_aligned_cache.py), and [end-to-end scalar/cyclic checks](../outputs/check_five_term_aligned_integration.py) supplement this argument. They are finite and numerical evidence, not a proof of the complete asymptotic algorithm.

## Earlier improvement: cached inner projections and cyclic-fiber counts

Use the ordinary five-term squared embedding with no physical-prefix restriction. Each input cache adds the actual `p1,p2` projections anywhere in its normal half. Retain at most `ell=rho m+O(1)` direct projections, at most `m` private-plus-direct positions in that half, and at most `m` private positions in the opposite half. If `U=sum_(j<=m) binom(L,j)4^(L−j)`, the retained count is at most `U² sum_(a<=ell) binom(m,a)2^a`. Every retained encoder prefix has all its ordinary completions, which pay for its entire remaining array. The shared encoding exponent is therefore `E=T+[H(rho)+rho ln2]/ln4`, while the original tile exponent remains `T`.

For each input separately, outputs with fewer than `ell` nonprivate normal positions use cached projections directly. Other outputs are grouped by their first `ell` nonprivate normal positions and their labels; other normal positions before that group's last cached position are fixed private. The remaining truncated transform has three normal sources and two opposite sources. Its exact high-family source count is `sum_(a+b<t,a>=ell) binom(m,a)binom(m,b)2^ell 3^(a−ell)2^b`. The two input sides usually have different groups, so their transformed values are paired by the complete output word. This yields `q1=max(q_inner,q_old−rho ln(3/2)/ln4)`, where `q_inner=H(theta)/ln2+theta` and `q_old=[ln((1+3y)(1+2y))−2theta ln y]/ln4`. The stored-box exponent `q2` is unchanged.

Use the five-term squared embedding over the exact cyclic ring `Z[x]/(x^q−1)`. For a middle block of size `h`, fold a base modulus `d` into the matrix dimensions, giving `D0=hd` and `N0=O(n sqrt(d))`. Replace each nonzero indicator for an edge weight `w` by `x^(w mod q)`. At the usual folded position for outer weight `C`, the coefficient at `−C mod q` counts exactly the witnesses divisible by `dq`, since the two moduli are coprime.

Every encoded array and stored box contains all `q` coefficients. Preprocessing, storage, formation and residual contractions pay `O~(q)` per scalar operation; exact polynomial arithmetic and coefficient bit lengths are charged. A stored-box query is a scalar linear combination of values already computed, so it reads just the requested coefficient in constant time per box. The two query branches therefore cost `q D0^q1` and `D0^q2`; merging them first would lose the improvement. The cache's two residual branches are also certified separately. The original geometry `N0>=D0^T polylog(D0)` remains, despite the larger cache exponent `E`.

Build each composite from `R=100000` distinct primes. Freeze its first `S=88618` factors as the folded base `d`, then accumulate the remaining selected and candidate primes in the cyclic length `q`. Every call supplies the same exact incidence count as the original composite certificate, so minimization, certification, restart halving and final scans are preserved. Every candidate costs exponent `eta=b/R`; both endpoints of each affine direct and cyclic phase are certified, covering all intermediate calls.

The explicit witness is `c=10.767898969`, `theta=.060343925615`, `rho=.066059242397`, `y=.025749961`, and block exponent `b=.04337385`. It has `u=bS/R=.038437038393`, cyclic exponent `v=b−u=.004936811607`, and inner exponent `e=b+u=.081810888393`. After charging `eta=.0000004337385`, every required runtime saving exceeds `.006599` with more than `6.85e−7` strict slack. The [58-inequality certificate](../outputs/verify_five_term_cache_apsp.py), [finite partial-cache checks](../outputs/check_five_term_cache.py), and [cyclic-fiber reduction checks](../outputs/check_five_term_ring.py) supplement the proof of deterministic `O(n^2.993401)` integer all-edges Exact Triangle, min-plus product and APSP. No unrestricted bound below `2.99` is claimed.

The earlier uncached cyclic-fiber witness remains valid: `c=10.67333763`, `theta=.0590858825`, `y=.025178142`, `b=.04368276`, `S=92277`, `R=100000`, and no physical prefix. Its encoding exponent is `T`, its saving is `.006559`, and its [48-inequality certificate](../outputs/verify_five_term_ring_apsp.py) still establishes the earlier `2.993441` result. The new cache does not reinterpret that witness.

## Earlier five-term encoding and composite certification

[Majdoddin, arXiv:2610.17420v1](https://arxiv.org/abs/2610.17420v1), supplies a squared five-term embedding. It has two halves, each with `m` inner positions, and tile width `K N0`, where `K = binom(L,m)` and `N0 = 4^(L−m)`. This grid is not a collection of independent products.

Restrict each inner set to have exactly `ell` positions in a fixed physical prefix. This loses only a polynomial fraction of the slots and permits direct storage of the two inner-coordinate forms there. Each query then reads `4^ell` prefix combinations per input side, instead of `8^ell`. A truncated suffix transform uses three ordinary forms on one side and two on the other. Its predecessor closure ensures no full Cartesian array is silently allocated.

Charge two encoders separately: ordinary private-capped leaves supply box base cases, while a second table supplies the new prefix forms and suffix query sources. Every retained prefix has enough ordinary descendants to pay for its entire remaining input array. The original tile geometry and both query exponents are preserved.

For an incidence `(outer pair, middle block)`, exact modular counts equal true witnesses plus false positives. Build each modulus from a fixed number of distinct primes, choosing each prime to minimize the aggregate count. In the final round, an incidence is false when its minimum count is zero, and true when that minimum exceeds the precise divisor-averaging threshold. Every uncertified incidence carries enough false mass to bound the number remaining by half the previous set. Restart on those incidences and scan after logarithmically many halvings. This is Majdoddin's per-incidence construction, applied to our explicit preprocessing-plus-query costs.

The explicit witness is `c=10.74132662`, `theta=.056740653`, prefix fraction `r=.038571087`, inner exponent `e=.083812911`, and coefficient point `y=.025146880`, with block exponent `b=e/2`. Use `R=100000` prime factors per composite. Candidate enumeration costs exponent `b/R=.000000419064555`; after charging it, every runtime saving exceeds `.006324` with more than `7.1e−7` slack. Intermediate moduli are covered by monotonicity, without assuming a fixed query density. The [29-inequality certificate](../outputs/verify_five_term_apsp.py) and [independent fixed-profile query checks](../outputs/check_five_term_profile.py) supplement the full proof. This earlier construction improves `2.99372` to `2.993676` for deterministic integer all-edges Exact Triangle, min-plus, and APSP. Its proof and 29-inequality verifier remain valid alongside the stronger cyclic-fiber result.

## 1. Restrict the encoder

An output with `m` inner positions can use only leaves with at most `m` occurrences of `P₀`. Retain those leaves during encoding, rather than allocating the original full encoding array.

$$S=\sum_{j=0}^{m}\binom Lj9^{L-j}.$$

If `p_k` prefixes survive at depth `k`, each has at least `9^(L-k)` retained descendants, so `p_k 9^(L-k) ≤ S`. Its child arrays cost `O(7^(L-k))` to form. Therefore the entire encoding costs

$$O\!\left(\sum_k p_k7^{L-k}\right)\le O(S)\sum_{h\ge0}(7/9)^h=O(S).$$

For fixed `L/m > 10`, `S = O(M)`, where `M = binom(L,m)9^(L-m)` is the batch output count. Sharing across bands gives encoding cost `O(N√M)` up to logarithmic factors. A compact prefix trie avoids any hidden full-array allocation.

## 2. Use the exact counts

The box and query counts come from the source paper:

$$\beta_d=\binom L{m-d}9^{L-m+d},\qquad\alpha_d=\binom md9^d.$$

The geometric decrease after the cutoff lets the exact ratio `β_t/M` control preprocessing. Entropy estimates and `L = ceil(c m)`, `t = ceil(θm)`, `D = 4^m` give

$$\widetilde O(ND^E+N^2D^{-G})\text{ preprocessing},\qquad\widetilde O(D^q)\text{ per entry query}.$$

With `c = 21.0477`, `θ = .111971`, and `e = .05828`, the exponents are approximately:

| Quantity | Value |
| --- | ---: |
| `E` | 17.338290775304982 |
| `G` | 0.069613877076460 |
| `q` | 0.430386142770839 |
| `1 − e(E − 1/4)` | 0.004094413615226 |

The actual dimension condition is `N ≥ √M`, not the convenient `N ≥ D^18` corollary. The folded instances of step 3 have outer dimension `N = Θ(n √P) ≥ n D^{1/4}`, and `e(E − 1/4) < 1` verifies it. Round `D` to a power of four as specified in the note.

## 3. Fold residues, then amplify modular filters before scanning

For a triangle's original integer weight sum `s(a,b,c)`, partition the middle vertices into blocks of size `h ≍ √D/log²n`. Choose `O(log n)` independent, uniformly sampled primes in `[P,2P]`, where `P ≍ √D log²n`, with constants ensuring `2Ph ≤ D`.

For every prime `p` and block `B`, build one folded thin product instead of `p` residue-specific ones. With `p_1 = ceil(√p)` and `p_2 = ceil(p/p_1)`, rows are `(a, ρ_1)`, columns are `(b, ρ_2)`, the middle part is `B × Z_p`, and

$$X[(a,ρ_1),(c,σ)]=[σ ≡ w(a,c)+ρ_1],\qquad Y[(c,σ),(b,ρ_2)]=[σ ≡ -w(b,c)-p_1ρ_2].$$

Writing `w(a,b) mod p = ρ_1 + p_1 ρ_2` makes the entry at `((a,ρ_1),(b,ρ_2))` count the `c ∈ B` with `s(a,b,c) ≡ 0 (mod p)`. Per prime this produces:

- `Õ(n/√D)` instances with outer dimension `Õ(n D^{1/4})`, whose band encodings cost `Õ(n² D^{E−1/4})` in all, a factor `D^{1/4}` below the unfolded `Õ(n² D^E)`;
- unchanged box work `Õ(n³ D^{−G})`;
- `Õ(n³/√D)` entry queries, one per pair and block, with no extra prime-size factor.

A block with no actual zero passes a random prime with probability at most `O(h log n/P) = O(log⁻³n)`. Independent tests reduce survival to at most `n⁻⁴`. Different primes may have different false witnesses; this is a block-level probability calculation.

Every actual zero survives. Scan surviving blocks using original sums, stopping separately for each outer pair after its first zero. The algorithm is correct for every random choice. Expected failed-scan work is negligible; successful scans cost at most `O(n²h)`.

## 4. Account for every term, then batch independent products

Before absorbing any term, the expected all-edges runtime is

$$\widetilde O\left(n^2D^{E-1/4}+n^3D^{-G}+n^3D^{q-1/2}+n^2D^{3/4}+n^2\sqrt D\right).$$

At `D = Θ(n^.05828)`, the largest raw exponent is

$$\tau=2.995942904400685\ldots<2.995943.$$

This is the earlier unbatched bound, which remains useful for lopsided instances. The exact-rational verifier certifies strict slack. If all three edge classes are requested, cyclically permute the parts three times.

For each prime, the middle blocks supply independent products of a common shape. Assign them to the tensor's `K` slots, sharing each input-band encoding across all tiles in its pack. The encoding exponent becomes `A₀ = (c−1) log₄ 3`, with both `N ≥ N₀` and `B ≥ K` required; the latter counts available independent products. Prefix contraction also replaces the original query exponent by `q_pc = max(q₁,q₂)`, with both terms checked. At the certified batched witness, the largest raw exponent is `2.995534854890842… < 2.995535`. Neither improvement changes the modular tests or their correctness.

## 5. Preserve the exponent for APSP

For nonnegative integer matrices, recursively compute `C′ = floor(A/2) ⋆ floor(B/2)`. Then

$$ (A\star B)_{ij}\in\{2C'_{ij},2C'_{ij}+1,2C'_{ij}+2\}.$$

Two all-edges equality calls distinguish these possibilities; the lower value wins when both tests succeed. There is one recursive min-plus call per bit level. Negative entries are handled by shifts local to each matrix product, using `(A+u) ⋆ (B+v) = A ⋆ B + u+v`.

Repeated min-plus squaring computes APSP with no negative cycles. Polynomially large sentinels and a final threshold handle missing edges. Both reductions add only logarithmic factors, so retain the unrounded exponent until the end. The batched construction gives expected `O(n^2.995535)`; the earlier unbatched construction gives `O(n^2.995943)`. The same transfer preserves the deterministic guarantees established next.

## 6. Integer 3SUM without the Exact Triangle detour

Bucket `A` and `B` by residue modulo a prime `r ≈ n/s` chosen to minimize the bucket second moment, cut each bucket into sub-buckets of at most `s` elements, and sample `O(log n)` universe primes `p` in `[P, 2P]` with `s² ≤ P/polylog`. For each prime, rows are `(sub-bucket α of A, ρ₁)`, columns `(sub-bucket β of B, ρ₂)`, the middle is `Z_p`, and for `z ∈ C` with `z mod p = ρ₁ + p₁ρ₂` the entry at `((α,ρ₁),(β,ρ₂))` is positive iff some `x ∈ α`, `y ∈ β` have `x + y ≡ z (mod p)`. Only sub-bucket pairs compatible modulo `r` are queried, `Õ(n²/√D)` of them; a sub-query is scanned only if positive under every prime, and scans are exact. The outer dimension is `Õ(n)`, so the costs are `n D^E`, `n² D^{−G}`, `n² D^{q−1/2}`, the unfolded Las Vegas constraint set, giving `O(n^1.996001)` with `c = 21.2733`, `θ = .111731`, `e = .056846`. The source's footnote 10 anticipates this route through Kopelowitz, Pettie, and Porat. The earlier deterministic variant chooses one universe prime by exact convolution counts and gives `O(n^1.997903)`. The next step supersedes that bound.

## 7. Choose several 3SUM filters deterministically

For each compatible sub-query `u`, let `c_p(u)` be the number of actual pairs whose sum matches the target modulo `p`, counting multiplicities. After choosing `t` distinct primes, consider the exact objective

$$J_t=\sum_u\prod_{j=1}^t c_{p_j}(u).$$

CRT histograms of ordered tuples within each sub-bucket, followed by one exact cyclic convolution, compute this objective. Different primes may use different witnesses; the product of counts accounts for that explicitly.

Choose each next prime to minimize `J_t`. On a NO instance, every nonzero difference has a bounded number of prime divisors, so averaging guarantees a contraction by roughly `s²/P`, up to logarithms. If the minimum fails the exact integer contraction test, that failure proves a solution exists. If every stage contracts, the surviving sub-queries number at most `J_k`, giving scan cost `Õ(n²(s²/P)^k)`. The full proof charges the CRT histogram and convolution cost for every candidate prime.

The certified witness `k = 18`, `c = 22.4828`, `θ = .111021`, `e = .0538428`, `z = .00021113` gives deterministic `O(n^1.996200)` time. A separating family handles distinct elements in the one-set version before this decision procedure is used; decision self-reduction recovers a witness. For 3SUM the affirmative certificate is specific to decision. For Exact Triangle the same threshold is applied to each outer pair: a pair whose smallest candidate moment exceeds `rho_t` times its previous moment contains a zero, every uncertified pair has genuine mass at most `rho_t` times its previous moment, and the common prime minimizing the uncertified sum contracts it by `2 rho_t`. This gave the earlier deterministic `O(n^2.996261)` all-edges, min-plus, and APSP bound. Its lopsided parameters remain the ones used for the stated clique bounds.

### Strengthen deterministic APSP with cyclic lazy encoding and rectangular selection

The square-instance construction combines these per-pair certificates with batching and prefix queries. It further lowers encoding work by keeping only leaves with at most `(1−α)m` copies of `P₀`, under all cyclic coordinate orders, while storing the intermediate arrays at retained prefixes. For any missing leaf, a cyclic-window averaging argument places its excess `P₀` positions in a short suffix. Sparse contraction of that suffix retrieves the exact leaf. The proof charges every stored array, rotation, and retrieval; stored box values remain unchanged. The resulting encoding exponent is `A₀−G(c,α)`, and the query cost includes a third, explicitly bounded lazy-retrieval term.

At moment stage `t`, the tuple-indexed matrices have shape `n × (n h^(t−1))` by `(n h^(t−1)) × n`. Use rectangular multiplication directly instead of dividing them into square products. The selector charges every candidate prime and every cyclic-ring coordinate, including exact integer bit complexity. The main witness uses the rectangular bounds in [Vassilevska Williams, Xu, Xu, and Zhou, SODA 2024](https://arxiv.org/abs/2307.07970v2), with a fixed positive exponent allowance.

The explicit parameters are `k = 11`, `c = 21.8429984`, `θ = .1125375917`, `r = .0254666251`, `α = .0478165400`, `e = .0613141114`, and `z = .0003737179`. Box work, all three query terms, scans, encoding, selection, formation, and both layout conditions have strict certificates at saving `0.0041108`. This gives deterministic `O(n^2.9958892)` for integer all-edges Exact Triangle, min-plus product, and APSP. These are square-instance parameters; they do not automatically improve the clique formulas.

Separately, assuming the characteristic-zero rectangular bound and exact bilinear realization in [Uznański, arXiv:2610.10494v2](https://arxiv.org/abs/2610.10494v2), a 13-stage witness gives deterministic `O(n^2.9958323)`. This is an additional conditional result. The [45-inequality certificate](../outputs/verify_deterministic_apsp.py) distinguishes the two external dependencies; its checks do not prove either matrix-multiplication theorem. [Five finite lazy-encoding tests](../outputs/check_lazy_encoding.py) supplement the reconstruction proof. That preprint is unrefereed and self-described as Codex-generated; its stated rectangular bound at `k = 1` would give `omega <= 2.25`, so the conditional figure is not counted among the bounds derived here, and it is superseded by `2.9926862626` in any case.

## 8. Certify real comparison counts using rank prefixes

Sort occurrences separately by color, assigning distinct integer ranks. Break equal-value ties with columns before rows for `<`, and with rows before columns for `≤`. Real magnitudes are unrestricted: hashing is applied only to the resulting bounded ranks.

A row occurrence precedes a column occurrence exactly at their first differing rank bit. Build two counting products whose middle coordinates are `(color, bit level, prefix residue)`: one counts the `0/1` orientation, the other `1/0`. Replacing exact prefix equality by equality modulo a sampled prime can only increase each count. Entries count occurrences, so duplicates are retained.

Compute the total `T` of same-color occurrence pairs independently. With one color it is the product of list lengths; with at most one occurrence per color it is a color-incidence product, zero-padded to the same full thin dimension. Keep the minimum observed upper count separately for each orientation. Once their sum equals `T`, both are exact. Repeat with fresh primes until every requested pair certifies. Each pair has a constant success probability per round, giving logarithmically many rounds in expectation.

The two list structures in the source's Lemma 36 allow actual dimension `D = Θ(d² log⁵ n)`, rounded to a power of four. Using `d = floor(n^.028423)` and the unfolded parameter witness gives expected `O(n^1.996001)` real 3SUM and `O(n^2.996001)` real min-plus/APSP/Exact Triangle. Strict tiling and exponent slack absorb the extra logarithms. The earlier same-block enumeration is no longer used.

Replacing the ten-term data structure by the five-term fixed-profile lemma, with `c = 10.7769`, `theta = .0567`, `r = .03854`, `y = .02511`, `e = .08183`, keeps the same reduction and gives expected `O(n^1.993805)` real 3SUM and `O(n^2.993805)` real min-plus, APSP, and Exact Triangle; the 89-inequality certificate is `outputs/verify_five_term_realinput.py`, which also certifies the five-term thin-product bounds `O(N^2/D^0.0991)` with query `O(D^0.4009)` at `N >= D^18` and `O(N^2/D^0.0853)` with query `O(D^0.4147)` at `N >= D^14`.

## 9. Recover isolated witnesses and use rectangular convolution blocks

For each middle block, sample masks at dyadic rates. Query a modular witness-count product and a label-sum product. When the count is one, the label identifies a candidate, which is checked against the original weights. Amplified trials isolate a true witness with high probability; exact fallback scans preserve correctness on every random outcome. This removes the expected successful-scan term without assuming that every trial succeeds.

For min-plus convolution choose `s = ceil(n^β)` and `r = ceil(n/s)`, forming `s` products of dimensions `(r+1) × s` by `s × r`. Their diagonals produce every one of the `2n−1` outputs. Keep both boundary rows and use a sentinel above `3W` for input magnitudes bounded by `W`.

Retuning the thin-product parameters gives Las Vegas expected `O(n^1.996057)` with `β = .027755`. In the deterministic version, quasi-linear exact cyclic polynomial multiplication during prime selection replaces the old quadratic ring cost; with `β = .083712` the resulting bound is `O(n^1.998057)`. All input formation, extraction, tiling, prime selection, and recovery costs are included. With square five-term tiles in the same block reduction, witness `c = 11.0588596`, `θ = .0563850479`, prefix `.0383287249`, `y = .0249694743`, `e = .0814836742`, `β = .03914792`, both the Las Vegas (isolated recovery) and the deterministic (lopsided composite incidence certification, `Λ = 10^5`) versions reach `O(n^1.993927)`; the 44-inequality certificate is `outputs/verify_five_term_convolution.py`.

Reading the deterministic square-case algorithm on lopsided instances gives the uniform bound `2 + rho - 0.00705208` for the `n x n^rho x n` min-plus product (`rho >= b`); inside the source's Theorem 33 this makes directed APSP with polylogarithmic weights explicit at `O(n^2.525754)` (crossover with fast rectangular multiplication at `rho* = 0.5328`), and `O(n^2.5251975)` with one further table row. Over `F_2`, the fixed-bucket construction with a small-bias row family and `Z[F_2^t]` coefficients gives deterministic 3XOR and exact #3XOR in `O(n^1.9931055)`.

The same rectangular accounting gives, for every fixed `k ≥ 3`, weighted clique bounds with savings `0.004057 floor(k/2.02914)` for Las Vegas integer inputs, `0.003739 floor(k/3)` deterministically through per-pair conditional moments (`0.002125 floor(k/2.09687)` with one chosen prime), and `0.003999 floor(k/2.028423)` for Las Vegas real inputs. These are explicit feasible splits, not optimized split claims.

The five-term composite-incidence construction applies to the lopsided `(alpha, alpha, m)` split whenever one block fits in the middle part (`m >= b alpha`), with every saving scaling by `alpha`; with `alpha = floor(k/(2+b))` this gives `O(n^(k - 0.00705208 floor(k/2.046046346)))` for Zero-, Min-, and Max-Weight integer `k`-Clique (`4.98589584` for `k = 5`), superseding both displayed integer savings for every `k`; chunking the middle part into square instances gives the weaker `floor(k/3)` form; the real lopsided split with the five-term data structure gives `0.006195 floor(k/2.040915)`.

## 10. Transfer to subset convolution and distinguish counting guarantees

[Stoian's restriction-product reduction](https://arxiv.org/abs/2610.10282v1) expresses min-sum subset convolution through rectangular min-plus products. An asymmetric tiling bound, followed by weighted greedy covers on small coordinate blocks, gives a leading base below `2.997190`. Exact rounding and a strict gap absorb the cover's subexponential overhead. The resulting guarantee is Las Vegas expected `O(2.997190^n poly(n, beta))` for explicit tables with arbitrary `beta`-bit integer values, including infinity sentinels. Square five-term tiles (no clamped regime; the fit is on the two outer sides) with the fixed-profile witness of the `2.993676` corollary give expected `O(2.995627^n poly(n, beta))`, certified by the 34 inequalities of `outputs/verify_five_term_subset.py`. For finite entries of magnitude `n^O(1)`, the deterministic transfer of the square `2.99294792` bound proves `O*(2.995124^n)`. Extending that deterministic guarantee to arbitrary `beta`-bit weights would require composite certification with a divisor bound `Theta(beta)` instead of `Theta(log n)`; that extension is not proved here. The Las Vegas result retains its arbitrary-bit guarantee. This also supports the source's join-ordering transfer under its stated assumptions.

The earlier counting construction uses a different guarantee. Its integer #3SUM algorithm takes Monte Carlo worst-case `O(n^1.996001)` time: multiplicity-preserving residue products give upper counts, and independent trials make all counts exact with high probability. It never undercounts, but it does not use the real comparison oracle's complementary certificate. The historical #Exact Triangle and min-plus witness-count construction has the same Monte Carlo guarantee at `O(n^2.995943)`, including a capped min-plus computation and upper-count fallback. The separate signed-window construction above supersedes it for integer inputs with deterministic exact counts at `O(n^2.99294792)`.

## Review boundaries

The research note builds on the source papers' algebraic identities, embeddings and box lemmas. The separate [Lean development](../lean/README.md) proves the constructed embedding, complete LOW/HIGH caches, deterministic reductions, and exact APSP correctness with an `O(n^2.99294792)` charged-work bound in its stated binary/indexed-array model. Whole-program word-RAM compilation remains a separate conditional adapter. The new `2.9926862626` result and the other result rows are outside that APSP formalization; no practical speedup or literature priority is claimed.

The separate fixed-bucket signed-window construction supersedes this older integer #3SUM guarantee with deterministic exact `O(n^1.9931055)` counts. Its 48-check certificate also covers the inherited MonoConvolution exponent.
