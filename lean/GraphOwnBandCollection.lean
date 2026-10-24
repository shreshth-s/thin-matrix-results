import GraphOwnBandCompletion
import AutoFullyRetainedRootBatch

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

namespace ThinMatrix.GraphOwnBandCollection
open BinaryCell BinaryGroupedCoordinates GraphAdaptiveRootBatch
open scoped BigOperators
variable {n h r S : ℕ} (f : CompactBlocks.PhysicalFactorization r)
  (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f)

abbrev G := GraphOwnBandRouter.count S p.L p.m
abbrev M := FoldedBackendExecution.windowQuerySize n
abbrev C := CompactBlocks.blockCount n h*((p.m+1)*f.cyclic)

def index (base : Index f p) (g : Fin (G f p (S:=S))) : Index f p :=
  {base with normal := (GraphOwnBandRouter.decode (S:=S) (L:=p.L) (m:=p.m) g).2.1,opposite := (GraphOwnBandRouter.decode (S:=S) (L:=p.L) (m:=p.m) g).2.2}

def requestIndex (base : Index f p) (request : GraphCompletionRequests.Physical p.L p.m f.cyclic) : Index f p :=
  {base with normal := (RootRequestSelection.ranks base.right request).1, opposite := (RootRequestSelection.ranks base.right request).2}

variable (base : Index f p) (scheme : RectangularBatch.Scheme) (hD : 0 < D f p base)
  (tile : AutoFullyRetainedRootBatch.Tile scheme (D f p base))
  (requests : GraphOwnBandCompletion.Requests f p) (masks : GraphOwnBandCompletion.Masks f p)
  (tree : GraphOwnBandCompletion.Tree f p (S:=S))
  (banks : (g : Fin (G f p (S:=S))) → GraphAdaptiveRootBatch.Prepared f p (index f p base g))

def child (g : Fin (G f p (S:=S))) : Run (OriginalRowCollection.Rows (M (n:=n)) (C f p)) :=
  GraphOwnBandCompletion.complete f p (index f p base g) scheme hD tile.hA tile.hZ tile.first tile.last
    requests masks tree (GraphOwnBandRouter.decode (S:=S) (L:=p.L) (m:=p.m) g).1 (banks g)

 theorem child_indices (g : Fin (G f p (S:=S))) :
    (child f p base scheme hD tile requests masks tree banks g).value.indices=
      (GraphOwnBandRouter.ids tree (GraphOwnBandRouter.decode (S:=S) (L:=p.L) (m:=p.m) g).1 (GraphOwnBandRouter.decode (S:=S) (L:=p.L) (m:=p.m) g).2.1
        (GraphOwnBandRouter.decode (S:=S) (L:=p.L) (m:=p.m) g).2.2).value := rfl

/-- One original-ID output array for the whole oriented root family. -/
def execute := OriginalRowCollection.execute (child f p base scheme hD tile requests masks tree banks)

 theorem bits : (execute f p base scheme hD tile requests masks tree banks).bitSteps=
      ∑ g,(child f p base scheme hD tile requests masks tree banks g).bitSteps := OriginalRowCollection.bits _

 theorem control (hb : ∀ i,(requests.get i).bandL<S ∧ (requests.get i).bandR<S)
    (htree : tree=(GraphOwnBandRouter.run base.right requests hb).value) :
    (execute f p base scheme hD tile requests masks tree banks).control=
      (∑ g,(child f p base scheme hD tile requests masks tree banks g).control)+
        48*G f p (S:=S)+80*M (n:=n)+16*C f p+36 := by
  apply OriginalRowCollection.control
  simp only [child_indices,htree]
  exact GraphOwnBandRouter.group_total base.right requests hb

 theorem coverage (hb : ∀ i,(requests.get i).bandL<S ∧ (requests.get i).bandR<S)
    (htree : tree=(GraphOwnBandRouter.run base.right requests hb).value) (i : Fin (M (n:=n))) :
    ∃ g,i∈(child f p base scheme hD tile requests masks tree banks g).value.indices := by
  let g := GraphOwnBandRouter.key base.right (requests.get i) (hb i).1 (hb i).2
  refine ⟨g,?_⟩
  rw [child_indices,htree,GraphOwnBandRouter.ids_mem]
  apply (GraphOwnBandRouter.key_eq_iff base.right (requests.get i) (hb i).1 (hb i).2 _ _ _).mp
  exact (GraphOwnBandRouter.encode_decode g).symm

noncomputable def expected (input : BinaryFoldedFormation.Inputs n) (request : Fin (M (n:=n)))
    (col : Fin (C f p)) : ℤ :=
  let bc := finProdFinEquiv.symm col
  let own := GraphOwnBandRouter.ownBand base.right (requests.get request)
  let ix := requestIndex f p base (requests.get request)
  view (((GraphRootCompletion.fromInputs f p bc.1 input own own (E f p base) ix).completed.value.sums.value.get request).output.get bc.2)

attribute [local irreducible] GraphAdaptiveRootBatch.prepare GraphPrefixProgram.fromInputs GraphAdaptiveBatchSources.Correct

variable (hm : p.m≤p.L-p.m) (input : BinaryFoldedFormation.Inputs n)
  (stored : Fin S → GraphAdaptiveBatchSources.Stored f p)
  (hc : ∀ a : Fin S, GraphAdaptiveBatchSources.Correct f p hm input a.val a.val (stored a))
  (hreq : requests=(GraphSharedTargets.prepare f p input.target).physical.value)
  (hmask : masks=(GraphSharedTargets.keys f p).value.masks)
  (hbank : ∀ g : Fin (G f p (S:=S)),banks g=(GraphAdaptiveRootBatch.prepare f p hm input
    (GraphOwnBandRouter.decode (S:=S) (L:=p.L) (m:=p.m) g).1.val (GraphOwnBandRouter.decode (S:=S) (L:=p.L) (m:=p.m) g).1.val
    (stored (GraphOwnBandRouter.decode (S:=S) (L:=p.L) (m:=p.m) g).1) (hc (GraphOwnBandRouter.decode (S:=S) (L:=p.L) (m:=p.m) g).1) (index f p base g)).value)

include hreq hmask hbank

theorem correct (hv : scheme.Valid)
    (hb : ∀ i,(requests.get i).bandL<S ∧ (requests.get i).bandR<S)
    (htree : tree=(GraphOwnBandRouter.run base.right requests hb).value)
    (request : Fin (M (n:=n))) (col : Fin (C f p)) :
    view (((execute f p base scheme hD tile requests masks tree banks).value.get request).get col)=
      expected f p base requests input request col := by
  apply OriginalRowCollection.correct _ (expected f p base requests input)
  · intro g j c
    let row := (child f p base scheme hD tile requests masks tree banks g).value.indices[j.val]
    have hj : row∈(GraphOwnBandRouter.ids tree (GraphOwnBandRouter.decode (S:=S) (L:=p.L) (m:=p.m) g).1
        (GraphOwnBandRouter.decode (S:=S) (L:=p.L) (m:=p.m) g).2.1 (GraphOwnBandRouter.decode (S:=S) (L:=p.L) (m:=p.m) g).2.2).value := List.getElem_mem _
    rw [htree,GraphOwnBandRouter.ids_mem] at hj
    have ha : GraphOwnBandRouter.ownBand base.right (requests.get row)=(GraphOwnBandRouter.decode (S:=S) (L:=p.L) (m:=p.m) g).1.val ∧
      (RootRequestSelection.ranks base.right (requests.get row)).1=(GraphOwnBandRouter.decode (S:=S) (L:=p.L) (m:=p.m) g).2.1 ∧
      (RootRequestSelection.ranks base.right (requests.get row)).2=(GraphOwnBandRouter.decode (S:=S) (L:=p.L) (m:=p.m) g).2.2 := by
      simpa only [GraphOwnBandRouter.accepts,decide_eq_true_eq] using hj
    have hi : index f p base g=requestIndex f p base (requests.get row) := by
      simp only[index,requestIndex,ha.2.1,ha.2.2]
    let bc : Fin (CompactBlocks.blockCount n h) × Fin ((p.m+1)*f.cyclic) := finProdFinEquiv.symm c
    have hh := GraphOwnBandCompletion.row_correct f p (index f p base g) scheme hD tile.hA tile.hZ tile.first tile.last
      requests masks tree (GraphOwnBandRouter.decode (S:=S) (L:=p.L) (m:=p.m) g).1 hm input (stored _) (hc _) hreq hmask hv (banks g) (hbank g) j bc.1 bc.2
    have he : PrefixBlockBatch.column bc.1 bc.2=c := finProdFinEquiv.apply_symm_apply c
    rw [he] at hh
    change view (((child f p base scheme hD tile requests masks tree banks g).value.values.get j).get c)=_ at hh
    unfold expected
    dsimp only
    rw [ha.1,←hi]
    exact hh
  · exact coverage f p base scheme hD tile requests masks tree banks hb htree

#print axioms child_indices
#print axioms bits
#print axioms control
#print axioms coverage
#print axioms correct
end ThinMatrix.GraphOwnBandCollection
