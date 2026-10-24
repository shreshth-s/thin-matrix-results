import GraphOwnBandTargets
import AutoRootCompletionRate

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

namespace ThinMatrix.GraphOwnBandPriced
open BinaryCell BinaryGroupedCoordinates GraphAdaptiveRootBatch
open scoped BigOperators
variable {n h r S : ℕ} (f : CompactBlocks.PhysicalFactorization r)
  (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f)
  (base : Index f p) (scheme : RectangularBatch.Scheme)
  (hnum : scheme.num=861) (hden : scheme.den=500) (hz : scheme.z=15)
  (hD : 0 < D f p base)
  (requests : GraphOwnBandCompletion.Requests f p)
  (masks : GraphOwnBandCompletion.Masks f p)
  (tree : GraphOwnBandCompletion.Tree f p (S:=S))

abbrev G := GraphOwnBandCollection.G f p (S:=S)
abbrev Q := GraphOwnBandCollection.C f p
abbrev M := FoldedBackendExecution.windowQuerySize n

def ix (g : Fin (G f p (S:=S))) := GraphOwnBandCollection.index f p base g

def own (g : Fin (G f p (S:=S))) := (GraphOwnBandRouter.decode (S:=S) (L:=p.L) (m:=p.m) g).1

def labels (g : Fin (G f p (S:=S))) :=
  (GraphOwnBandCompletion.projected f p (ix f p base g) requests masks tree (own f p g)).value.residuals.labels

def count (g : Fin (G f p (S:=S))) :=
  (GraphOwnBandRouter.ids tree (own f p g) (ix f p base g).normal (ix f p base g).opposite).value.length

 theorem labels_size (g : Fin (G f p (S:=S))) : (labels f p base requests masks tree g).size=count f p base tree g := by
  simp only [labels,count,GraphOwnBandCompletion.projected,GraphOwnBandRouter.project,GraphCompletionRequests.project_size]

 theorem count_total (hb : ∀ i,(requests.get i).bandL<S ∧ (requests.get i).bandR<S)
    (htree : tree=(GraphOwnBandRouter.run base.right requests hb).value) :
    (∑ g,count f p base tree g)=M (n:=n) := by
  subst tree
  exact GraphOwnBandRouter.group_total base.right requests hb

variable (banks : (g : Fin (G f p (S:=S))) → GraphAdaptiveRootBatch.Prepared f p (ix f p base g))

def auto (g : Fin (G f p (S:=S))) :=
  AutoFullyRetainedRootBatch.execute scheme hnum hden hz hD (banks g).banks (banks g).layouts
    (labels f p base requests masks tree g)

def extra (price : ℕ) : ℕ := price*(
    G f p (S:=S)*(16*((G f p (S:=S)).size+1)^2+64*((G f p (S:=S)).size+1)^3+48*p.L+60)+
    M (n:=n)*(32*(p.L-p.m)+112)+48*G f p (S:=S)+80*M (n:=n)+16*Q f p+68)

/-- The one shared tile setup is paid by the sum of auto-root envelopes.
The additional term contains only explicit projection/collection control. -/
theorem collection_price (price : ℕ)
    (hG : 1 ≤ G f p (S:=S))
    (hb : ∀ i,(requests.get i).bandL<S ∧ (requests.get i).bandR<S)
    (htree : tree=(GraphOwnBandRouter.run base.right requests hb).value) :
    let tile := AutoFullyRetainedRootBatch.prepare scheme hnum hden hz (D f p base) hD
    let out := GraphOwnBandCollection.execute f p base scheme hD tile.value requests masks tree banks
    tile.bitSteps+out.bitSteps+price*(out.control+32) ≤
      (∑ g,((auto f p base scheme hnum hden hz hD requests masks tree banks g).bitSteps+
        price*(auto f p base scheme hnum hden hz hD requests masks tree banks g).control))+
      extra f p (S:=S) price := by
  dsimp only
  let tile := AutoFullyRetainedRootBatch.prepare scheme hnum hden hz (D f p base) hD
  let child := GraphOwnBandCollection.child f p base scheme hD tile.value requests masks tree banks
  let out := GraphOwnBandCollection.execute f p base scheme hD tile.value requests masks tree banks
  let overhead := 16*((G f p (S:=S)).size+1)^2+64*((G f p (S:=S)).size+1)^3+48*p.L+60
  have each (g : Fin (G f p (S:=S))) :
      tile.bitSteps+(child g).bitSteps+price*(child g).control ≤
      (auto f p base scheme hnum hden hz hD requests masks tree banks g).bitSteps+
        price*(auto f p base scheme hnum hden hz hD requests masks tree banks g).control+
        price*(overhead+count f p base tree g*(32*(p.L-p.m)+112)) := by
    have hc := GraphOwnBandCompletion.complete_control f p (ix f p base g) scheme hD
      tile.value.hA tile.value.hZ tile.value.first tile.value.last requests masks tree (own f p g) (banks g)
    have hb' := GraphOwnBandCompletion.complete_bits f p (ix f p base g) scheme hD
      tile.value.hA tile.value.hZ tile.value.first tile.value.last requests masks tree (own f p g) (banks g)
    change (child g).control≤_ at hc
    change (child g).bitSteps=_ at hb'
    let root := GraphAdaptiveRootBatch.execute f p (ix f p base g) scheme hD
      tile.value.hA tile.value.hZ tile.value.first tile.value.last (banks g)
      (labels f p base requests masks tree g)
    change (child g).bitSteps=root.bitSteps at hb'
    change (child g).control ≤ root.control+16*((G f p (S:=S)).size+1)^2+
      64*((G f p (S:=S)).size+1)^3+48*p.L+count f p base tree g*(32*(p.L-p.m)+112)+60 at hc
    rw [hb']
    change tile.bitSteps+root.bitSteps+price*(child g).control ≤
      tile.bitSteps+root.bitSteps+price*(root.control+16)+
        price*(overhead+count f p base tree g*(32*(p.L-p.m)+112))
    have hp := Nat.mul_le_mul_left price hc
    dsimp only [overhead]
    nlinarith only [hp]
  have hs := Finset.sum_le_sum (fun g (_ : g∈Finset.univ) => each g)
  have ht := count_total f p base requests tree hb htree
  have hbits := GraphOwnBandCollection.bits f p base scheme hD tile.value requests masks tree banks
  have hctrl := GraphOwnBandCollection.control f p base scheme hD tile.value requests masks tree banks hb htree
  have htile : tile.bitSteps ≤ G f p (S:=S)*tile.bitSteps := by nlinarith
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    smul_eq_mul,←Finset.mul_sum,←Finset.sum_mul,ht] at hs
  change tile.bitSteps+out.bitSteps+price*(out.control+32)≤_
  change out.bitSteps=∑ g,(child g).bitSteps at hbits
  change out.control=(∑ g,(child g).control)+48*G f p (S:=S)+80*M (n:=n)+16*Q f p+36 at hctrl
  rw [hbits,hctrl]
  unfold extra
  dsimp only [overhead] at hs
  simp only [Finset.sum_add_distrib,←Finset.mul_sum]
  nlinarith only [hs,htile]

omit requests masks tree banks in
theorem targets_price (hm : p.m ≤ p.L-p.m) (input : BinaryFoldedFormation.Inputs n)
    (stored : GraphOwnBandPreparation.Stores f p (S:=S))
    (hc : ∀ a : Fin S,GraphAdaptiveBatchSources.Correct f p hm input a.val a.val (stored.get a))
    (targets : GraphOwnBandTargets.Prepared f p (S:=S)) (price : ℕ)
    (hG : 1 ≤ G f p (S:=S))
    (hb : ∀ i,(targets.requests.get i).bandL<S ∧ (targets.requests.get i).bandR<S)
    (htree : GraphOwnBandTargets.tree f p targets base.right=(GraphOwnBandRouter.run base.right targets.requests hb).value) :
    let br := GraphOwnBandPreparation.banks f p hm input base stored hc
    let family := GraphOwnBandPreparation.get f p base br.value
    let out := GraphOwnBandTargets.execute f p input hm base scheme hnum hden hz hD stored hc targets
    out.bitSteps+price*out.control ≤ br.bitSteps+price*br.control+
      (∑ g,((auto f p base scheme hnum hden hz hD targets.requests targets.masks
        (GraphOwnBandTargets.tree f p targets base.right) family g).bitSteps+
        price*(auto f p base scheme hnum hden hz hD targets.requests targets.masks
          (GraphOwnBandTargets.tree f p targets base.right) family g).control))+
      extra f p (S:=S) price := by
  dsimp only
  let br := GraphOwnBandPreparation.banks f p hm input base stored hc
  let family := GraphOwnBandPreparation.get f p base br.value
  let tile := AutoFullyRetainedRootBatch.prepare scheme hnum hden hz (D f p base) hD
  let out := GraphOwnBandCollection.execute f p base scheme hD tile.value targets.requests targets.masks
    (GraphOwnBandTargets.tree f p targets base.right) family
  have hh := collection_price f p base scheme hnum hden hz hD targets.requests targets.masks
    (GraphOwnBandTargets.tree f p targets base.right) family price hG hb htree
  change tile.bitSteps+out.bitSteps+price*(out.control+32)≤_ at hh
  change tile.bitSteps+br.bitSteps+out.bitSteps+price*(br.control+16+out.control+16)≤_
  change _≤br.bitSteps+price*br.control+_+_
  nlinarith only [hh]

#print axioms targets_price
#print axioms labels_size
#print axioms count_total
#print axioms collection_price
end ThinMatrix.GraphOwnBandPriced
