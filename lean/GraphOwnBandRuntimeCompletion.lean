import GraphOwnBandRuntime
import GraphOwnBandCollection

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
namespace ThinMatrix.GraphOwnBandRuntimeCompletion
open BinaryCell BinaryGroupedCoordinates GraphAdaptiveRootBatch
variable {n h r S : ℕ} (f : CompactBlocks.PhysicalFactorization r)
  (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f)
  (shape : GraphOwnBandRuntime.Shape p.L p.m)

variable (i : Index f p) {A Z : ℕ} (scheme : RectangularBatch.Scheme)
  (hD : 0 < D f p i) (hA : 0 < A) (hZ : 0 < Z)
  (hfirst : (A-1)^scheme.den≤(D f p i)^scheme.num) (hlast : Z≤(D f p i)^scheme.z)
  (requests : GraphOwnBandCompletion.Requests f p) (masks : GraphOwnBandCompletion.Masks f p)
  (tree : GraphOwnBandCompletion.Tree f p (S:=S)) (a : Fin S)

def complete (bank : GraphAdaptiveRootBatch.Prepared f p i) :
    Run (OriginalRowCollection.Rows (GraphOwnBandCompletion.M (n:=n)) (GraphOwnBandCompletion.Columns f p)) :=
  let proj := GraphOwnBandRuntime.project shape i.right requests tree a i.normal i.opposite
    (masks.get i.normal) (masks.get i.opposite)
  let out := GraphAdaptiveRootBatch.execute f p i scheme hD hA hZ hfirst hlast bank proj.value.residuals.labels
  let values := Vector.ofFn (fun j : Fin proj.value.indices.length =>
    RootProductCollection.output out.value ⟨j.val,by rw [proj.value.size_eq];exact j.isLt⟩)
  ⟨⟨proj.value.indices,values⟩,proj.bitSteps+out.bitSteps,
    proj.control+out.control+32*proj.value.indices.length+8⟩

 theorem complete_eq (bank : GraphAdaptiveRootBatch.Prepared f p i) :
    complete f p shape i scheme hD hA hZ hfirst hlast requests masks tree a bank=
      GraphOwnBandCompletion.complete f p i scheme hD hA hZ hfirst hlast requests masks tree a bank := by
  rcases shape with ⟨K,hK⟩
  subst K
  rfl

 def index (base : Index f p) (g : Fin (GraphOwnBandCollection.G f p (S:=S))) : Index f p :=
  {base with normal := (GraphOwnBandRuntime.decode shape g).2.1, opposite := (GraphOwnBandRuntime.decode shape g).2.2}

 theorem index_eq (base : Index f p) (g : Fin (GraphOwnBandCollection.G f p (S:=S))) :
    index f p shape base g=GraphOwnBandCollection.index f p base g := by
  simp only [index,GraphOwnBandRuntime.decode_eq,GraphOwnBandCollection.index]

 def child (base : Index f p) (scheme : RectangularBatch.Scheme) (hD : 0 < D f p base)
    (tile : AutoFullyRetainedRootBatch.Tile scheme (D f p base))
    (requests : GraphOwnBandCompletion.Requests f p) (masks : GraphOwnBandCompletion.Masks f p)
    (tree : GraphOwnBandCompletion.Tree f p (S:=S))
    (banks : (g : Fin (GraphOwnBandCollection.G f p (S:=S))) →
      GraphAdaptiveRootBatch.Prepared f p (GraphOwnBandCollection.index f p base g))
    (g : Fin (GraphOwnBandCollection.G f p (S:=S))) :
    Run (OriginalRowCollection.Rows (GraphOwnBandCompletion.M (n:=n)) (GraphOwnBandCompletion.Columns f p)) :=
  complete f p shape (index f p shape base g) scheme hD tile.hA tile.hZ tile.first tile.last
    requests masks tree (GraphOwnBandRuntime.decode shape g).1 ⟨(banks g).banks,(banks g).layouts⟩

 theorem child_eq (base : Index f p) (scheme : RectangularBatch.Scheme) (hD : 0 < D f p base)
    (tile : AutoFullyRetainedRootBatch.Tile scheme (D f p base))
    (requests : GraphOwnBandCompletion.Requests f p) (masks : GraphOwnBandCompletion.Masks f p)
    (tree : GraphOwnBandCompletion.Tree f p (S:=S))
    (banks : (g : Fin (GraphOwnBandCollection.G f p (S:=S))) →
      GraphAdaptiveRootBatch.Prepared f p (GraphOwnBandCollection.index f p base g))
    (g : Fin (GraphOwnBandCollection.G f p (S:=S))) :
    child f p shape base scheme hD tile requests masks tree banks g=
      GraphOwnBandCollection.child f p base scheme hD tile requests masks tree banks g := by
  rcases shape with ⟨K,hK⟩
  subst K
  rfl

/-- The outer collection receives its loop length from retained storage. -/
def collect {M C : ℕ} (child : Fin (GraphOwnBandRouter.count S p.L p.m) → Run (OriginalRowCollection.Rows M C)) :
    Run (Vector (Vector Cell C) M) :=
  OriginalRowCollection.execute (G:=GraphOwnBandRuntime.groups shape S)
    (fun g => child (Fin.cast (GraphOwnBandRuntime.groups_eq shape) g))

 theorem collect_eq {M C : ℕ} (child : Fin (GraphOwnBandRouter.count S p.L p.m) → Run (OriginalRowCollection.Rows M C)) :
    collect f p shape child=OriginalRowCollection.execute child := by
  rcases shape with ⟨K,hK⟩
  subst K
  rfl

 def execute (base : Index f p) (scheme : RectangularBatch.Scheme) (hD : 0 < D f p base)
    (tile : AutoFullyRetainedRootBatch.Tile scheme (D f p base))
    (requests : GraphOwnBandCompletion.Requests f p) (masks : GraphOwnBandCompletion.Masks f p)
    (tree : GraphOwnBandCompletion.Tree f p (S:=S))
    (banks : (g : Fin (GraphOwnBandCollection.G f p (S:=S))) →
      GraphAdaptiveRootBatch.Prepared f p (GraphOwnBandCollection.index f p base g)) :=
  collect f p shape (child f p shape base scheme hD tile requests masks tree banks)

 theorem execute_eq (base : Index f p) (scheme : RectangularBatch.Scheme) (hD : 0 < D f p base)
    (tile : AutoFullyRetainedRootBatch.Tile scheme (D f p base))
    (requests : GraphOwnBandCompletion.Requests f p) (masks : GraphOwnBandCompletion.Masks f p)
    (tree : GraphOwnBandCompletion.Tree f p (S:=S))
    (banks : (g : Fin (GraphOwnBandCollection.G f p (S:=S))) →
      GraphAdaptiveRootBatch.Prepared f p (GraphOwnBandCollection.index f p base g)) :
    execute f p shape base scheme hD tile requests masks tree banks=
      GraphOwnBandCollection.execute f p base scheme hD tile requests masks tree banks := by
  simp only [execute,collect_eq,GraphOwnBandCollection.execute]
  congr 1
  funext g
  exact child_eq f p shape base scheme hD tile requests masks tree banks g

#print axioms complete_eq
#print axioms index_eq
#print axioms child_eq
#print axioms collect_eq
#print axioms execute_eq
end ThinMatrix.GraphOwnBandRuntimeCompletion
