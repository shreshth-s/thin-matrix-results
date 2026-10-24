import GraphOwnBandRuntimePreparation
import GraphOwnBandProduction

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

/-! Target geometry, original-coordinate masks and both orientation routers
are prepared once for the entire callback. Subsequent root types only read
them. The existing target/setup mixed ledger remains separate from the binary
completion and its indexed-control counter. -/
namespace ThinMatrix.GraphOwnBandTargets
open BinaryCell BinaryGroupedCoordinates GraphAdaptiveRootBatch
variable {n h r S : ℕ} (f : CompactBlocks.PhysicalFactorization r)
  (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f)

structure Prepared where
  requests : GraphOwnBandCompletion.Requests f p
  masks : GraphOwnBandCompletion.Masks f p
  leftTree : GraphOwnBandCompletion.Tree f p (S:=S)
  rightTree : GraphOwnBandCompletion.Tree f p (S:=S)

def tree (out : Prepared f p (S:=S)) (right : Bool) :=
  if right then out.rightTree else out.leftTree

variable (input : BinaryFoldedFormation.Inputs n)
  (hb : ∀ i,((GraphSharedTargets.prepare f p input.target).physical.value.get i).bandL<S ∧
    ((GraphSharedTargets.prepare f p input.target).physical.value.get i).bandR<S)

/-- Both orientation routers and the physical query array are retained.
All intermediate binary geometry and target-formation costs are included. -/
def prepare : SourceFormation.Program (Prepared f p (S:=S)) :=
  let shape := GraphSharedTargets.shape f p
  let keys := ResidualFamilyKeys.prepare shape.layout p.t
  let targets := GraphCompletionRequests.prepare f p shape input.target
  let left := GraphOwnBandRouter.run false targets.physical.value hb
  let right := GraphOwnBandRouter.run true targets.physical.value hb
  ⟨⟨targets.physical.value,keys.value.masks,left.value,right.value⟩,
    shape.operations+keys.bitSteps+keys.control+targets.folded.geometry.bitSteps+
    targets.folded.requests.bitSteps+targets.physical.bitSteps+targets.physical.control+
    left.bitSteps+left.control+right.bitSteps+right.control+32⟩

def prepareRuntime : SourceFormation.Program (Prepared f p (S:=S)) :=
  let shape := GraphSharedTargets.shape f p
  let keys := ResidualFamilyKeys.prepare shape.layout p.t
  let targets := GraphCompletionRequests.prepare f p shape input.target
  let retained := GraphOwnBandRuntime.prepare keys.value.masks
  let left := GraphOwnBandRuntime.run retained false targets.physical.value hb
  let right := GraphOwnBandRuntime.run retained true targets.physical.value hb
  ⟨⟨targets.physical.value,keys.value.masks,left.value,right.value⟩,
    shape.operations+keys.bitSteps+keys.control+targets.folded.geometry.bitSteps+
    targets.folded.requests.bitSteps+targets.physical.bitSteps+targets.physical.control+
    left.bitSteps+left.control+right.bitSteps+right.control+32⟩


@[csimp] theorem prepare_eq_runtime : @prepare=@prepareRuntime := by
  funext n h r S f p input hb
  simp only [prepareRuntime,GraphOwnBandRuntime.run_eq,prepare]

#print axioms prepare_eq_runtime

 theorem requests_eq : (prepare f p input hb).value.requests=
    (GraphSharedTargets.prepare f p input.target).physical.value := rfl

 theorem masks_eq : (prepare f p input hb).value.masks=(GraphSharedTargets.keys f p).value.masks := rfl

 theorem tree_eq (right : Bool) : tree f p (prepare f p input hb).value right=
    (GraphOwnBandRouter.run right (GraphSharedTargets.prepare f p input.target).physical.value hb).value := by
  cases right <;> rfl

 theorem work : (prepare f p input hb).operations=
    (GraphSharedTargets.shape f p).operations+
    (GraphSharedTargets.keys f p).bitSteps+(GraphSharedTargets.keys f p).control+
    (GraphSharedTargets.prepare f p input.target).folded.geometry.bitSteps+
    (GraphSharedTargets.prepare f p input.target).folded.requests.bitSteps+
    (GraphSharedTargets.prepare f p input.target).physical.bitSteps+
    (GraphSharedTargets.prepare f p input.target).physical.control+
    (GraphOwnBandRouter.run false (GraphSharedTargets.prepare f p input.target).physical.value hb).bitSteps+
    (GraphOwnBandRouter.run false (GraphSharedTargets.prepare f p input.target).physical.value hb).control+
    (GraphOwnBandRouter.run true (GraphSharedTargets.prepare f p input.target).physical.value hb).bitSteps+
    (GraphOwnBandRouter.run true (GraphSharedTargets.prepare f p input.target).physical.value hb).control+32 := rfl

variable (hm : p.m ≤ p.L-p.m) (base : Index f p) (scheme : RectangularBatch.Scheme)
  (hnum : scheme.num=861) (hden : scheme.den=500) (hz : scheme.z=15)
  (hD : 0 < D f p base)
  (stored : GraphOwnBandPreparation.Stores f p (S:=S))
  (hc : ∀ a : Fin S,GraphAdaptiveBatchSources.Correct f p hm input a.val a.val (stored.get a))

omit hb in
/-- Per-type production using already retained source stores and both target
routers. Setup/formation is not inside the per-type execution. -/
def execute (targets : Prepared f p (S:=S)) :=
  let ready := GraphOwnBandProduction.prepare f p hm input base scheme hnum hden hz hD stored hc
  let out := GraphOwnBandProduction.complete f p base scheme hD ready.value
    targets.requests targets.masks (tree f p targets base.right)
  { out with bitSteps := ready.bitSteps+out.bitSteps, control := ready.control+out.control+16 }

omit hb in
def readyRuntime (retained : GraphOwnBandRuntime.Shape p.L p.m) :
    Run (GraphOwnBandProduction.Ready f p base scheme (S:=S)) :=
  let tile := AutoFullyRetainedRootBatch.prepare scheme hnum hden hz (D f p base) hD
  let banks := GraphOwnBandRuntimePreparation.banks f p retained hm input base stored hc
  ⟨⟨tile.value,banks.value⟩,tile.bitSteps+banks.bitSteps,banks.control+16⟩

omit hb in
theorem readyRuntime_eq (retained : GraphOwnBandRuntime.Shape p.L p.m) :
    readyRuntime f p input hm base scheme hnum hden hz hD stored hc retained=
      GraphOwnBandProduction.prepare f p hm input base scheme hnum hden hz hD stored hc := by
  simp only [readyRuntime,GraphOwnBandRuntimePreparation.banks_eq,GraphOwnBandProduction.prepare]

omit hb in
def executeRuntime (targets : Prepared f p (S:=S)) :=
  let retained := GraphOwnBandRuntime.prepare targets.masks
  let ready := readyRuntime f p input hm base scheme hnum hden hz hD stored hc retained
  let out := GraphOwnBandRuntimeCompletion.execute f p retained base scheme hD ready.value.tile
    targets.requests targets.masks (tree f p targets base.right)
    (GraphOwnBandPreparation.get f p base ready.value.banks)
  {out with bitSteps := ready.bitSteps+out.bitSteps,control := ready.control+out.control+16}

@[csimp] theorem execute_eq_runtime : @execute=@executeRuntime := by
  funext n h r S f p input hm base scheme hnum hden hz hD stored hc targets
  simp only [executeRuntime,readyRuntime_eq,GraphOwnBandRuntimeCompletion.execute_eq,
    execute,GraphOwnBandProduction.complete]

#print axioms readyRuntime_eq
#print axioms execute_eq_runtime

omit hb in
theorem bits (targets : Prepared f p (S:=S)) :
    (execute f p input hm base scheme hnum hden hz hD stored hc targets).bitSteps=
      (GraphOwnBandProduction.prepare f p hm input base scheme hnum hden hz hD stored hc).bitSteps+
      (GraphOwnBandProduction.complete f p base scheme hD
        (GraphOwnBandProduction.prepare f p hm input base scheme hnum hden hz hD stored hc).value
        targets.requests targets.masks (tree f p targets base.right)).bitSteps := rfl

omit hb in
theorem control (targets : Prepared f p (S:=S)) :
    (execute f p input hm base scheme hnum hden hz hD stored hc targets).control=
      (GraphOwnBandProduction.prepare f p hm input base scheme hnum hden hz hD stored hc).control+
      (GraphOwnBandProduction.complete f p base scheme hD
        (GraphOwnBandProduction.prepare f p hm input base scheme hnum hden hz hD stored hc).value
        targets.requests targets.masks (tree f p targets base.right)).control+16 := rfl

attribute [local irreducible] GraphAdaptiveRootBatch.prepare GraphAdaptiveBatchSources.Correct

theorem correct (hv : scheme.Valid) (request : Fin (FoldedBackendExecution.windowQuerySize n))
    (block : Fin (CompactBlocks.blockCount n h)) (c : Fin ((p.m+1)*f.cyclic)) :
    view (((execute f p input hm base scheme hnum hden hz hD stored hc
      (prepare f p input hb).value).value.get request).get (PrefixBlockBatch.column block c))=
      GraphOwnRootSpec.rootValue f p input base.u base.v base.run base.channel base.right request block c := by
  let ready := GraphOwnBandProduction.prepare f p hm input base scheme hnum hden hz hD stored hc
  have hh := GraphOwnBandCollection.correct f p base scheme hD ready.value.tile
    (prepare f p input hb).value.requests (prepare f p input hb).value.masks
    (tree f p (prepare f p input hb).value base.right)
    (GraphOwnBandPreparation.get f p base ready.value.banks)
    hm input (fun a => stored.get a) hc (requests_eq f p input hb) (masks_eq f p input hb)
    (fun g => GraphOwnBandPreparation.banks_get f p hm input base stored hc g)
    hv hb (tree_eq f p input hb base.right) request (PrefixBlockBatch.column block c)
  exact hh.trans (GraphOwnBandCanonical.expected_eq f p base input _ (requests_eq f p input hb) request block c)

#print axioms requests_eq
#print axioms masks_eq
#print axioms tree_eq
#print axioms work
#print axioms bits
#print axioms control
#print axioms correct
end ThinMatrix.GraphOwnBandTargets
