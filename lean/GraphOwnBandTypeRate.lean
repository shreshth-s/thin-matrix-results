import GraphOwnBandOverhead

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 10000

namespace ThinMatrix.GraphOwnBandTypeRate
open BinaryCell BinaryGroupedCoordinates GraphAdaptiveRootBatch GraphOwnBandPriced
open SharedCompletionRate
open scoped BigOperators
variable {n h r S : ℕ} (f : CompactBlocks.PhysicalFactorization r)
  (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (base : Index f p)

abbrev F := 2^(WindowPrefixProgram.length (p.L-p.m) (E f p base))*
  4^(WindowPrefixProgram.prefixLength (p.L-p.m) (E f p base))
def H := 2^(WindowPrefixProgram.prefixLength (p.L-p.m) (E f p base))*
  GraphAdaptiveBatchSources.windowMagnitude f p

/-- These are only public dimension and word-length conditions, with no
running-time premise. The independent product fit is explicit. -/
structure Fits (scheme : RectangularBatch.Scheme) (targets : GraphOwnBandTargets.Prepared f p (S:=S)) (L : ℕ) : Prop where
  groups : 1 ≤ G f p (S:=S)
  batch : SharedCompletionTile.col (D f p base) ≤ Q f p
  dimension : 2*(p.L-p.m)+1 ≤ L
  groupWidth : (G f p (S:=S)).size+1 ≤ L
  span : ∀ g : Fin (G f p (S:=S)),
    (SharedFullyAddressedBatch.addressSpan
      (labels f p base targets.requests targets.masks (GraphOwnBandTargets.tree f p targets base.right) g).size
      (D f p base) (Q f p) (SharedCompletionTile.row (D f p base))
      (SharedCompletionTile.col (D f p base))).size+1 ≤ L
  qWidth : scheme.q.size+(D f p base).size+6 ≤ L
  valueWidth : (D f p base).size+(H f p base).size+6 ≤ L
  rootWidth : (W f p).size+(D f p base).size+(H f p base).size+1 ≤ L

theorem source_bound (hm : p.m ≤ p.L-p.m) (input : BinaryFoldedFormation.Inputs n)
    (a : Fin S) (stored : GraphAdaptiveBatchSources.Stored f p)
    (hc : GraphAdaptiveBatchSources.Correct f p hm input a.val a.val stored)
    (slot : Fin (W f p)) (b : Fin (CompactBlocks.blockCount n h))
    (pair : Fin (2^(WindowPrefixProgram.length (p.L-p.m) (E f p base)))) :
    PrefixCompletionMatrices.LeafBound
      ((((GraphAdaptiveRootBatch.sources f p hm input a.val a.val stored hc base).get slot).get b).traces.get pair)
      (H f p base) := by
  have hh := GraphAdaptiveBatchSources.source_leaf_bound f p hm input a.val a.val stored hc (base.atSlot slot) b pair
  rw [←GraphAdaptiveBatchSources.collect_get f p hm input a.val a.val stored hc (base.atSlot slot) b] at hh
  simpa only [GraphAdaptiveRootBatch.sources,Vector.get_ofFn,H,GraphAdaptiveBatchSources.S,GraphAdaptiveBatchSources.P,GraphAdaptiveBatchSources.R,GraphAdaptiveBatchSources.E,GraphRootCompletion.Index.atSlot,E] using hh

/-- One fixed proved CW base, the concrete shared tile selector and actual
own-band execution. Every completion/setup/route/scatter cost is bounded;
source-bank construction remains the explicit first term. -/
theorem exists_type_rate : ∃ scheme : RectangularBatch.Scheme,
    ∃ hnum : scheme.num=861, ∃ hden : scheme.den=500, ∃ hz : scheme.z=15,
    scheme.Valid ∧ ∃ K : ℝ, 0 < K ∧
    ∀ n h r S : ℕ, ∀ f : CompactBlocks.PhysicalFactorization r,
    ∀ p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f,
    ∀ hm : p.m ≤ p.L-p.m, ∀ input : BinaryFoldedFormation.Inputs n,
    ∀ base : Index f p, ∀ hD : 0 < D f p base,
    ∀ stored : GraphOwnBandPreparation.Stores f p (S:=S),
    ∀ hc : ∀ a : Fin S,GraphAdaptiveBatchSources.Correct f p hm input a.val a.val (stored.get a),
    ∀ targets : GraphOwnBandTargets.Prepared f p (S:=S),
    ∀ hb : ∀ i,(targets.requests.get i).bandL<S ∧ (targets.requests.get i).bandR<S,
    GraphOwnBandTargets.tree f p targets base.right=(GraphOwnBandRouter.run base.right targets.requests hb).value →
    ∀ price L : ℕ, Fits f p base scheme targets L →
    let out := GraphOwnBandTargets.execute f p input hm base scheme hnum hden hz hD stored hc targets
    let banks := GraphOwnBandPreparation.banks f p hm input base stored hc
    (out.bitSteps+price*out.control:ℝ) ≤ (banks.bitSteps+price*banks.control:ℝ)+
      K*(price+1)*W f p*(L:ℝ)^5*((M (n:=n):ℝ)*Q f p*(D f p base:ℝ)^beta+
        (G f p (S:=S):ℝ)*F f p base*Q f p*(D f p base:ℝ)^gamma) := by
  obtain ⟨scheme,hnum,hden,hz,hvalid,K,hK,hcost⟩ := AutoRootCompletionRate.exists_root_rate
  refine ⟨scheme,hnum,hden,hz,hvalid,K+1024,by positivity,?_⟩
  intro n h r S f p hm input base hD stored hc targets hb htree price L fits
  dsimp only
  let br := GraphOwnBandPreparation.banks f p hm input base stored hc
  let family := GraphOwnBandPreparation.get f p base br.value
  let tree := GraphOwnBandTargets.tree f p targets base.right
  let s := D f p base
  let H0 := H f p base
  let F0 := F f p base
  let V := (M (n:=n):ℝ)*Q f p*(s:ℝ)^beta+(G f p (S:=S):ℝ)*F0*Q f p*(s:ℝ)^gamma
  have hH : 1 ≤ H0 := by
    change 0 < H0
    dsimp [H0,H,GraphAdaptiveBatchSources.windowMagnitude,GraphAdaptiveBatchSources.rawMagnitude]
    positivity
  have hW : 1 ≤ W f p := by
    dsimp only [W]
    cases p.L-p.m <;> simp [RetainedRootWindows.slots]
  have hF : 1 ≤ F0 := by change 0 < F0;dsimp [F0,F];positivity
  have hQ : 1 ≤ Q f p := (SharedCompletionTile.dimensions s hD).2.1.trans_le fits.batch
  have hL : 1 ≤ L := by have hh := fits.dimension;omega
  have hpL : p.L ≤ L := by have hh := fits.dimension;have hmL := p.m_le_L;omega
  have each (g : Fin (G f p (S:=S))) :
      ((auto f p base scheme hnum hden hz hD targets.requests targets.masks tree family g).bitSteps+
        price*(auto f p base scheme hnum hden hz hD targets.requests targets.masks tree family g).control:ℝ) ≤
      K*(price+1)*W f p*(L:ℝ)^5*((count f p base tree g:ℝ)*Q f p*(s:ℝ)^beta+
        (F0:ℝ)*Q f p*(s:ℝ)^gamma) := by
    let a := own f p g
    let i := ix f p base g
    have he : family g=(GraphAdaptiveRootBatch.prepare f p hm input a.val a.val (stored.get a) (hc a) i).value :=
      GraphOwnBandPreparation.banks_get f p hm input base stored hc g
    unfold auto
    rw [he]
    have hh := hcost (p.L-p.m) (E f p i) (p.m/2)
      (GraphWindowCompatibility.counts i.channel).1 (GraphWindowCompatibility.counts i.channel).2
      ((p.m+1)*f.cyclic) (CompactBlocks.blockCount n h) (W f p) hD
      (GraphAdaptiveRootBatch.sources f p hm input a.val a.val (stored.get a) (hc a) i)
      (GraphAdaptiveRootBatch.prepare f p hm input a.val a.val (stored.get a) (hc a) i).value.banks
      (GraphAdaptiveRootBatch.prepare_bank f p hm input a.val a.val (stored.get a) (hc a) i)
      (fun slot b => (GraphAdaptiveRootBatch.sources_layout f p hm input a.val a.val (stored.get a) (hc a) i slot b).1)
      (fun slot b => (GraphAdaptiveRootBatch.sources_layout f p hm input a.val a.val (stored.get a) (hc a) i slot b).2)
      (GraphAdaptiveRootBatch.prepare f p hm input a.val a.val (stored.get a) (hc a) i).value.layouts
      (labels f p base targets.requests targets.masks tree g) H0 price L hH
      (source_bound f p i hm input a (stored.get a) (hc a)) hW fits.batch fits.dimension (fits.span g)
      fits.qWidth fits.valueWidth fits.rootWidth
    conv at hh => rhs;rw [labels_size]
    simpa only [F0,F,Q,GraphOwnBandCollection.C,s,D,i,ix,GraphOwnBandCollection.index,E,Nat.cast_mul] using hh
  have hsum := Finset.sum_le_sum (fun g (_ : g∈Finset.univ) => each g)
  have ht := count_total f p base targets.requests tree hb htree
  have htr : (∑ g : Fin (G f p (S:=S)),(count f p base tree g:ℝ))=M (n:=n) := by exact_mod_cast ht
  have hsum' :
      (∑ g : Fin (G f p (S:=S)),((auto f p base scheme hnum hden hz hD targets.requests targets.masks tree family g).bitSteps+
        price*(auto f p base scheme hnum hden hz hD targets.requests targets.masks tree family g).control:ℝ)) ≤
        K*(price+1)*W f p*(L:ℝ)^5*V := by
    apply hsum.trans_eq
    simp only [←Finset.mul_sum,Finset.sum_add_distrib,←Finset.sum_mul,Finset.sum_const,
      Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,htr,V]
    ring
  have hn := targets_price f p base scheme hnum hden hz hD hm input stored hc targets price fits.groups hb htree
  have hnR :
      ((GraphOwnBandTargets.execute f p input hm base scheme hnum hden hz hD stored hc targets).bitSteps+
        price*(GraphOwnBandTargets.execute f p input hm base scheme hnum hden hz hD stored hc targets).control:ℝ) ≤
      (br.bitSteps+price*br.control:ℝ)+
      (∑ g : Fin (G f p (S:=S)),((auto f p base scheme hnum hden hz hD targets.requests targets.masks tree family g).bitSteps+
        price*(auto f p base scheme hnum hden hz hD targets.requests targets.masks tree family g).control:ℝ))+
      (extra f p (S:=S) price:ℝ) := by exact_mod_cast hn
  have he := GraphOwnBandOverhead.rate (G f p (S:=S)) (M (n:=n)) (Q f p) (W f p) L p.L (p.L-p.m)
    price s F0 fits.groups hQ hW hL fits.groupWidth (Nat.sub_le _ _) hpL hD hF
  have he' : (extra f p (S:=S) price:ℝ)≤1024*(price+1)*W f p*(L:ℝ)^5*V := by
    simpa only [extra,V,Nat.cast_mul,Nat.cast_add,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_one] using he
  change _≤(br.bitSteps+price*br.control:ℝ)+(K+1024)*(price+1)*W f p*(L:ℝ)^5*V
  nlinarith only [hnR,hsum',he']

#print axioms source_bound
#print axioms exists_type_rate
end ThinMatrix.GraphOwnBandTypeRate
