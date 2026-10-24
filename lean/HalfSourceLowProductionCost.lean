import HalfSourceLowTypeVolume
import HalfSourceLowExtraVolume

/-! Price the concrete LOW production, including every retained source-bank
copy, chosen tile, routed completion, requested cyclic contraction and sum.
The premises are public dimension/word bounds, not running-time assumptions. -/
namespace ThinMatrix.HalfSourceLowProductionCost
open BinaryCell BinaryGroupedCoordinates ExactHalfSourcePlan ResidualFamilyKeys
open GraphAdaptiveRootBatch GraphOwnBandPriced GraphOwnBandTypeRate
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 12000
noncomputable section

 theorem exists_production_rate : ∃ scheme : RectangularBatch.Scheme,
    ∃ hnum : scheme.num=861, ∃ hden : scheme.den=500, ∃ hz : scheme.z=15,
    scheme.Valid ∧ ∃ K : ℝ, 0<K ∧
    ∀ n h r S : ℕ, ∀ f : CompactBlocks.PhysicalFactorization r,
    ∀ p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f,
    ∀ hm : p.m≤p.L-p.m, ∀ input : BinaryFoldedFormation.Inputs n,
    ∀ hb : ∀ i,((GraphSharedTargets.prepare f p input.target).physical.value.get i).bandL<S ∧
      ((GraphSharedTargets.prepare f p input.target).physical.value.get i).bandR<S,
    ∀ stored : GraphOwnBandPreparation.Stores f p (S:=S),
    ∀ hc : ∀ a : Fin S,GraphAdaptiveBatchSources.Correct f p hm input a.val a.val (stored.get a),
    ∀ keys : Vector (Channel p.m) (channelCount p.m p.t),
    keys.toList=(channels p.m p.t).value →
    ∀ ws : Vector Cell p.t, (∀ d,(view (ws.get d)).natAbs≤2^(2*p.m)) →
    ∀ price Lw : ℕ, 1≤CompactBlocks.blockCount n h →
    (∀ u v run c side,Fits f p (GraphOwnLowProduction.index f p u v run c side) scheme
      (GraphOwnBandTargets.prepare f p input hb).value Lw) →
    let out := GraphOwnLowProduction.execute f p hm input scheme hnum hden hz stored hc
      (GraphOwnBandTargets.prepare f p input hb).value keys ws
    (out.bitSteps+price*out.control:ℝ)≤
      2*K*(price+1)*(W f p:ℝ)*(Lw:ℝ)^5*(Q f p:ℝ)*
        (HalfSourceRootFamilyCosts.multiplicity p.m:ℝ)*
        HalfSourceLowTypeVolume.volume p.L p.m p.t S (M (n:=n))+
      (price+1)*(HalfSourceLowCollectionCosts.extra f p (2^(2*p.m))
        (HalfSourceLowProductCosts.rootMagnitude f p):ℝ) := by
  obtain ⟨scheme,hnum,hden,hz,hvalid,K,hK,hcost⟩ := GraphOwnBandCompleteRate.exists_complete_rate
  refine ⟨scheme,hnum,hden,hz,hvalid,K,hK,?_⟩
  intro n h r S f p hm input hb stored hc keys hkeys ws hws price Lw hB hfits
  dsimp only
  let targets := (GraphOwnBandTargets.prepare f p input hb).value
  let roots := GraphOwnLowProduction.roots f p hm input scheme hnum hden hz stored hc targets
  let profile (c : Fin (channelCount p.m p.t)) : ℝ :=
    K*(price+1)*(W f p:ℝ)*(Lw:ℝ)^5*(Q f p:ℝ)*
      ((M (n:=n):ℝ)*(HalfSourceLowTypeVolume.support p.L p.m p.t c:ℝ)^HalfSourceParameters.beta+
        (S:ℝ)*(GoodMapEmbedding.goodSlots p.L p.m).card^2*
          (HalfSourceLowTypeVolume.groups p.L p.m p.t c:ℝ)*
          (HalfSourceLowTypeVolume.support p.L p.m p.t c:ℝ)^(1+HalfSourceParameters.alpha))
  have each u v run c side :
      ((roots u v run c side).bitSteps+price*(roots u v run c side).control:ℝ)≤profile c := by
    have hh := hcost n h r S f p hm input (GraphOwnLowProduction.index f p u v run c side)
      (GraphOwnLowProduction.dimension_pos f p u v run c side) stored hc targets hb
      (GraphOwnBandTargets.tree_eq f p input hb side) price Lw (hfits u v run c side)
    change _≤_ at hh
    apply hh.trans_eq
    dsimp only [profile,G,GraphOwnBandCollection.G,GraphOwnBandRouter.count,
      F,D,GraphOwnLowProduction.index,HalfSourceLowTypeVolume.groups,HalfSourceLowTypeVolume.support]
    rw [show SharedCompletionRate.beta=HalfSourceParameters.beta by norm_num[SharedCompletionRate.beta,HalfSourceParameters.beta],
      show SharedCompletionRate.gamma=1+HalfSourceParameters.alpha by norm_num[SharedCompletionRate.gamma,HalfSourceParameters.alpha]]
    push_cast
    ring
  have hs := HalfSourceLowRootSum.sum_children f p keys hkeys roots price profile each
  have hr : ∀ u v run c side,SelectedRootRows.RowsBound
      (HalfSourceLowProductCosts.rootMagnitude f p) (roots u v run c side).value := by
    apply HalfSourceLowProductCosts.rows_bound_of_correct f p roots input
    exact GraphOwnLowProduction.root_correct f p hm input hb scheme hnum hden hz stored hc hvalid
  have hp := HalfSourceLowCollectionCosts.actual_price f p ws keys targets.requests roots
    (2^(2*p.m)) (HalfSourceLowProductCosts.rootMagnitude f p) price hB hws hr
  have hpR :
      ((GraphOwnLowProgram.execute f p ws keys targets.requests roots).bitSteps+
        price*(GraphOwnLowProgram.execute f p ws keys targets.requests roots).control:ℝ)≤
      (∑ s,(HalfSourceLowCollectionCosts.rootWork f p keys roots price s:ℝ))+
        (price+1)*(HalfSourceLowCollectionCosts.extra f p (2^(2*p.m))
          (HalfSourceLowProductCosts.rootMagnitude f p):ℝ) := by exact_mod_cast hp
  apply hpR.trans
  apply (add_le_add_left hs _).trans_eq
  unfold profile HalfSourceLowTypeVolume.volume
  simp_rw [←Finset.mul_sum]
  ring

#print axioms exists_production_rate
end
end ThinMatrix.HalfSourceLowProductionCost
