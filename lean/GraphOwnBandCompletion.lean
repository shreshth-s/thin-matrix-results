import GraphOwnBandRoutingTotals
import GraphAdaptiveRootCorrect
import GraphAdaptiveBankSharing
import OriginalRowCollection

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option maxRecDepth 10000

namespace ThinMatrix.GraphOwnBandCompletion
open BinaryCell BinaryGroupedCoordinates GraphAdaptiveRootBatch
open scoped BigOperators
variable {n h r S : ℕ} (f : CompactBlocks.PhysicalFactorization r)
  (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f)

abbrev M := FoldedBackendExecution.windowQuerySize n
abbrev Columns := CompactBlocks.blockCount n h*((p.m+1)*f.cyclic)
abbrev Requests := Vector (GraphCompletionRequests.Physical p.L p.m f.cyclic) (M (n:=n))
abbrev Masks := Vector (ResidualFamilyKeys.Mask p.L p.m) (GoodMapEmbedding.goodSlots p.L p.m).card
abbrev Tree := BooleanRequestRouter.Tree (Fin (M (n:=n))) (GraphOwnBandRouter.count S p.L p.m).size

variable (i : Index f p) {A Z : ℕ} (scheme : RectangularBatch.Scheme)
  (hD : 0 < D f p i) (hA : 0 < A) (hZ : 0 < Z)
  (hfirst : (A-1)^scheme.den≤(D f p i)^scheme.num) (hlast : Z≤(D f p i)^scheme.z)
  (requests : Requests f p) (masks : Masks f p) (tree : Tree f p (S:=S)) (a : Fin S)

def projected := GraphOwnBandRouter.project i.right requests tree a i.normal i.opposite
  (masks.get i.normal) (masks.get i.opposite)

/-- Complete one own-band/mask group using its retained matrix banks. Every
original occurrence and every block/formal-degree/cyclic column is retained. -/
def complete (bank : GraphAdaptiveRootBatch.Prepared f p i) :
    Run (OriginalRowCollection.Rows (M (n:=n)) (Columns f p)) :=
  let proj := projected f p i requests masks tree a
  let out := GraphAdaptiveRootBatch.execute f p i scheme hD hA hZ hfirst hlast bank proj.value.residuals.labels
  let values := Vector.ofFn (fun j : Fin proj.value.indices.length =>
    RootProductCollection.output out.value ⟨j.val,by rw [proj.value.size_eq];exact j.isLt⟩)
  ⟨⟨proj.value.indices,values⟩,proj.bitSteps+out.bitSteps,
    proj.control+out.control+32*proj.value.indices.length+8⟩

 theorem complete_indices (bank : GraphAdaptiveRootBatch.Prepared f p i) :
    (complete f p i scheme hD hA hZ hfirst hlast requests masks tree a bank).value.indices=
      (GraphOwnBandRouter.ids tree a i.normal i.opposite).value := rfl

 theorem complete_bits (bank : GraphAdaptiveRootBatch.Prepared f p i) :
    (complete f p i scheme hD hA hZ hfirst hlast requests masks tree a bank).bitSteps=
      (GraphAdaptiveRootBatch.execute f p i scheme hD hA hZ hfirst hlast bank
        (projected f p i requests masks tree a).value.residuals.labels).bitSteps := by
  simp only[complete,projected,GraphOwnBandRouter.project_bits,zero_add]

 theorem complete_control (bank : GraphAdaptiveRootBatch.Prepared f p i) :
    (complete f p i scheme hD hA hZ hfirst hlast requests masks tree a bank).control≤
      (GraphAdaptiveRootBatch.execute f p i scheme hD hA hZ hfirst hlast bank
        (projected f p i requests masks tree a).value.residuals.labels).control+
      16*((GraphOwnBandRouter.count S p.L p.m).size+1)^2+64*((GraphOwnBandRouter.count S p.L p.m).size+1)^3+
      48*p.L+(GraphOwnBandRouter.ids tree a i.normal i.opposite).value.length*(32*(p.L-p.m)+112)+60 := by
  have hh := GraphOwnBandRouter.project_control i.right requests tree a i.normal i.opposite
    (masks.get i.normal) (masks.get i.opposite)
  dsimp only[complete]
  change _≤_ at hh
  change (projected f p i requests masks tree a).control+_+32*(GraphOwnBandRouter.ids tree a i.normal i.opposite).value.length+8≤_
  change (projected f p i requests masks tree a).control≤_ at hh
  nlinarith only[hh]

variable (hm : p.m≤p.L-p.m) (input : BinaryFoldedFormation.Inputs n)
  (stored : GraphAdaptiveBatchSources.Stored f p)
  (hc : GraphAdaptiveBatchSources.Correct f p hm input a.val a.val stored)
  (hreq : requests=(GraphSharedTargets.prepare f p input.target).physical.value)
  (hmask : masks=(GraphSharedTargets.keys f p).value.masks)

include hreq hmask

 theorem projected_label (j : Fin (GraphOwnBandRouter.ids tree a i.normal i.opposite).value.length) :
    (projected f p i requests masks tree a).value.residuals.labels[j.val]'(by simp [projected,GraphOwnBandRouter.project])=
      (GraphSharedTargets.project f p input.target i).value.labels[
        ((GraphOwnBandRouter.ids tree a i.normal i.opposite).value[j.val]).val]'(by simp) := by
  have hh := GraphOwnBandRouter.project_get i.right requests tree a i.normal i.opposite
    (masks.get i.normal) (masks.get i.opposite) j
  simpa only[projected,hreq,hmask,GraphSharedTargets.project] using hh

/-- Diagonal preparation supplies the correct full root for this own band.
The opposite-band replacement is a separate sharing equality. -/
 theorem row_correct (hv : scheme.Valid) (bank : GraphAdaptiveRootBatch.Prepared f p i)
    (hbank : bank=(GraphAdaptiveRootBatch.prepare f p hm input a.val a.val stored hc i).value)
    (j : Fin (complete f p i scheme hD hA hZ hfirst hlast requests masks tree a bank).value.indices.length)
    (block : Fin (CompactBlocks.blockCount n h)) (c : Fin ((p.m+1)*f.cyclic)) :
    view ((((complete f p i scheme hD hA hZ hfirst hlast requests masks tree a bank).value.values.get j).get
      (PrefixBlockBatch.column block c)))=
      view (((GraphRootCompletion.fromInputs f p block input a.val a.val (E f p i) i).completed.value.sums.value.get
        ((complete f p i scheme hD hA hZ hfirst hlast requests masks tree a bank).value.indices[j.val])).output.get c) := by
  have hj : j.val<(GraphOwnBandRouter.ids tree a i.normal i.opposite).value.length := j.isLt
  let j' : Fin (projected f p i requests masks tree a).value.residuals.labels.size := ⟨j.val,by simp [projected,GraphOwnBandRouter.project];exact hj⟩
  have hl := projected_label (f:=f) (p:=p) (i:=i) (requests:=requests) (masks:=masks) (tree:=tree) (a:=a) (input:=input) (A:=A) (Z:=Z) (scheme:=scheme) (hreq:=hreq) (hmask:=hmask) ⟨j.val,hj⟩
  have hh := GraphAdaptiveRootCorrect.correct f p hm input a.val a.val stored hc i scheme hv hD hA hZ hfirst hlast
    (projected f p i requests masks tree a).value.residuals.labels j'
    ((GraphOwnBandRouter.ids tree a i.normal i.opposite).value[j.val]) hl block c
  rw [←hbank] at hh
  simpa only[complete,Vector.get_ofFn,projected,GraphOwnBandRouter.project,j'] using hh

#print axioms complete_indices
#print axioms complete_bits
#print axioms complete_control
#print axioms projected_label
#print axioms row_correct
end ThinMatrix.GraphOwnBandCompletion
