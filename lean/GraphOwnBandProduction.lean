import GraphOwnBandPreparation
import GraphOwnBandCanonical

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

/-! The production boundary separates one source store for the whole shape,
one router per orientation, and one completion tile/bank per root type.
Only `complete` is evaluated after these retained preparations. All S*K²
own-band groups gather requests from every opposite band in that single call. -/
namespace ThinMatrix.GraphOwnBandProduction
open BinaryCell BinaryGroupedCoordinates GraphAdaptiveRootBatch
open scoped BigOperators
variable {n h r S : ℕ} (f : CompactBlocks.PhysicalFactorization r)
  (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f)

structure Ready (base : Index f p) (scheme : RectangularBatch.Scheme) where
  tile : AutoFullyRetainedRootBatch.Tile scheme (D f p base)
  banks : GraphOwnBandPreparation.BankRows f p base (S:=S)

variable (hm : p.m ≤ p.L-p.m) (input : BinaryFoldedFormation.Inputs n)
  (base : Index f p) (scheme : RectangularBatch.Scheme)
  (hnum : scheme.num=861) (hden : scheme.den=500) (hz : scheme.z=15)
  (hD : 0 < D f p base)
  (stored : GraphOwnBandPreparation.Stores f p (S:=S))
  (hc : ∀ a : Fin S,GraphAdaptiveBatchSources.Correct f p hm input a.val a.val (stored.get a))

/-- Per-type setup is outside every own-band and request loop. -/
def prepare : Run (Ready f p base scheme (S:=S)) :=
  let tile := AutoFullyRetainedRootBatch.prepare scheme hnum hden hz (D f p base) hD
  let banks := GraphOwnBandPreparation.banks f p hm input base stored hc
  ⟨⟨tile.value,banks.value⟩,tile.bitSteps+banks.bitSteps,banks.control+16⟩

 theorem prepare_bits : (prepare f p hm input base scheme hnum hden hz hD stored hc).bitSteps=
    (AutoFullyRetainedRootBatch.prepare scheme hnum hden hz (D f p base) hD).bitSteps+
      (GraphOwnBandPreparation.banks f p hm input base stored hc).bitSteps := rfl

 theorem prepare_control : (prepare f p hm input base scheme hnum hden hz hD stored hc).control=
    (GraphOwnBandPreparation.banks f p hm input base stored hc).control+16 := rfl

omit hm input hnum hden hz stored hc in
def complete (ready : Ready f p base scheme (S:=S))
    (requests : GraphOwnBandCompletion.Requests f p) (masks : GraphOwnBandCompletion.Masks f p)
    (tree : GraphOwnBandCompletion.Tree f p (S:=S)) :=
  GraphOwnBandCollection.execute f p base scheme hD ready.tile requests masks tree
    (GraphOwnBandPreparation.get f p base ready.banks)

/-- One concrete oriented execution. The source store is retained externally
across every translation, degree run and channel. A caller retaining the
router across types may call `complete` directly. -/
def execute (requests : GraphOwnBandCompletion.Requests f p) (masks : GraphOwnBandCompletion.Masks f p)
    (hb : ∀ i,(requests.get i).bandL<S ∧ (requests.get i).bandR<S) :=
  let ready := prepare f p hm input base scheme hnum hden hz hD stored hc
  let routed := GraphOwnBandRouter.run base.right requests hb
  let out := complete f p base scheme hD ready.value requests masks routed.value
  { out with bitSteps := ready.bitSteps+routed.bitSteps+out.bitSteps, control := ready.control+routed.control+out.control+16 }

 theorem execute_bits (requests : GraphOwnBandCompletion.Requests f p)
    (masks : GraphOwnBandCompletion.Masks f p)
    (hb : ∀ i,(requests.get i).bandL<S ∧ (requests.get i).bandR<S) :
    (execute f p hm input base scheme hnum hden hz hD stored hc requests masks hb).bitSteps=
      (prepare f p hm input base scheme hnum hden hz hD stored hc).bitSteps+
      (GraphOwnBandRouter.run base.right requests hb).bitSteps+
      (complete f p base scheme hD (prepare f p hm input base scheme hnum hden hz hD stored hc).value
        requests masks (GraphOwnBandRouter.run base.right requests hb).value).bitSteps := rfl

 theorem execute_control (requests : GraphOwnBandCompletion.Requests f p)
    (masks : GraphOwnBandCompletion.Masks f p)
    (hb : ∀ i,(requests.get i).bandL<S ∧ (requests.get i).bandR<S) :
    (execute f p hm input base scheme hnum hden hz hD stored hc requests masks hb).control=
      (prepare f p hm input base scheme hnum hden hz hD stored hc).control+
      (GraphOwnBandRouter.run base.right requests hb).control+
      (complete f p base scheme hD (prepare f p hm input base scheme hnum hden hz hD stored hc).value
        requests masks (GraphOwnBandRouter.run base.right requests hb).value).control+16 := rfl

attribute [local irreducible] GraphAdaptiveRootBatch.prepare GraphAdaptiveBatchSources.Correct

theorem correct (requests : GraphOwnBandCompletion.Requests f p)
    (masks : GraphOwnBandCompletion.Masks f p)
    (hb : ∀ i,(requests.get i).bandL<S ∧ (requests.get i).bandR<S)
    (hreq : requests=(GraphSharedTargets.prepare f p input.target).physical.value)
    (hmask : masks=(GraphSharedTargets.keys f p).value.masks)
    (hv : scheme.Valid) (request : Fin (FoldedBackendExecution.windowQuerySize n))
    (col : Fin (CompactBlocks.blockCount n h*((p.m+1)*f.cyclic))) :
    view (((execute f p hm input base scheme hnum hden hz hD stored hc requests masks hb).value.get request).get col)=
      GraphOwnBandCollection.expected f p base requests input request col := by
  exact GraphOwnBandCollection.correct f p base scheme hD
    (prepare f p hm input base scheme hnum hden hz hD stored hc).value.tile requests masks
    (GraphOwnBandRouter.run base.right requests hb).value
    (GraphOwnBandPreparation.get f p base (prepare f p hm input base scheme hnum hden hz hD stored hc).value.banks)
    hm input (fun a => stored.get a) hc hreq hmask
    (fun g => GraphOwnBandPreparation.banks_get f p hm input base stored hc g) hv hb rfl request col

theorem canonical (requests : GraphOwnBandCompletion.Requests f p)
    (masks : GraphOwnBandCompletion.Masks f p)
    (hb : ∀ i,(requests.get i).bandL<S ∧ (requests.get i).bandR<S)
    (hreq : requests=(GraphSharedTargets.prepare f p input.target).physical.value)
    (hmask : masks=(GraphSharedTargets.keys f p).value.masks)
    (hv : scheme.Valid) (request : Fin (FoldedBackendExecution.windowQuerySize n))
    (block : Fin (CompactBlocks.blockCount n h)) (c : Fin ((p.m+1)*f.cyclic)) :
    view (((execute f p hm input base scheme hnum hden hz hD stored hc requests masks hb).value.get request).get
      (PrefixBlockBatch.column block c))=
      GraphOwnRootSpec.rootValue f p input base.u base.v base.run base.channel base.right request block c := by
  rw [correct f p hm input base scheme hnum hden hz hD stored hc requests masks hb hreq hmask hv]
  exact GraphOwnBandCanonical.expected_eq f p base input requests hreq request block c

#print axioms prepare_bits
#print axioms prepare_control
#print axioms execute_bits
#print axioms execute_control
#print axioms correct
#print axioms canonical
end ThinMatrix.GraphOwnBandProduction
