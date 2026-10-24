import GraphOwnBandPriced
import GraphOwnBankCopyCosts
import SharedCompletionWidths
open ThinMatrix RecursiveTable
set_option exponentiation.threshold 10000
set_option maxRecDepth 20000

private def emptyBase : RetainedEqualCopy.Base 0 1 (prod (fin (2^861)) (fin (2^500)))
    (prod (fin (2^500)) (fin ((2^500)^15))) (prod (fin ((2^500)^15)) (fin (2^861))) ℚ :=
  ⟨store _ (fun p => Fin.elim0 p.1),store _ (fun p => Fin.elim0 p.1),store _ (fun p => Fin.elim0 p.1)⟩

private def shapeOnlyScheme : RectangularBatch.Scheme :=
  ⟨2^861,2^500,(2^500)^15,861,500,15,0,1,
    by norm_num,by decide,by decide,by decide,
    by rw [←pow_mul,←pow_mul],rfl,emptyBase⟩


private def physical : CompactBlocks.PhysicalFactorization 1 := ⟨1,1,by decide,by decide,by decide,by decide⟩
private def plan : BinaryFoldedFactory.Plan (n:=0) (h:=1) physical :=
  ⟨2,1,1,FoldedCounts.foldWidth 3,FoldedBackendExecution.outerSize 0 3,
    FoldedBackendExecution.middleSize 1 3,3,16,rfl,rfl,rfl,rfl,by decide,by decide,by decide⟩
private def input : BinaryFoldedFormation.Inputs 0 :=
  (BinaryFoldedFormation.encodeInputs (Vector.replicate 0 (Vector.replicate 0 0))
    (Vector.replicate 0 (Vector.replicate 0 0)) (Vector.replicate 0 (Vector.replicate 0 0))).value
private theorem positive_masks : 0 < (GoodMapEmbedding.goodSlots plan.L plan.m).card := by
  have hh := GoodMapEmbedding.goodSlots_density 2 1
  norm_num at hh
  change 0 < (GoodMapEmbedding.goodSlots 2 1).card
  omega
private def base (right : Bool) : GraphAdaptiveRootBatch.Index physical plan :=
  ⟨⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩,⟨0,positive_masks⟩,⟨0,positive_masks⟩,⟨0,by decide⟩,right⟩
private theorem hb : ∀ i,((GraphSharedTargets.prepare physical plan input.target).physical.value.get i).bandL<2 ∧
    ((GraphSharedTargets.prepare physical plan input.target).physical.value.get i).bandR<2 := by
  intro i
  exact Fin.elim0 i

def main : IO Unit := do
  let stores := GraphOwnBandPreparation.sources physical plan (by decide) input (S:=2)
  let cap := HalfSourceCapSetup.execute plan.m (plan.L-plan.m)
  unless stores.operations=cap.bitSteps+24 do
    throw (IO.userError "The source cap was not charged exactly once outside the two empty-block band stores")
  let targets := GraphOwnBandTargets.prepare physical plan input hb
  let mut checked := 0
  for right in [false,true] do
    let b := base right
    let D := GraphAdaptiveRootBatch.D physical plan b
    if hd : 0<D then
      let banks := GraphOwnBandPreparation.banks physical plan (by decide) input b stores.value
        (GraphOwnBandPreparation.sources_correct physical plan (by decide) input)
      unless banks.value.toArray.size=GraphOwnBandRouter.count 2 plan.L plan.m do
        throw (IO.userError "Own-band completion bank count acquired an opposite-band factor")
      let ready := GraphOwnBandProduction.prepare physical plan (by decide) input b shapeOnlyScheme rfl rfl rfl hd stores.value
        (GraphOwnBandPreparation.sources_correct physical plan (by decide) input)
      let completed := GraphOwnBandProduction.complete physical plan b shapeOnlyScheme hd ready.value
        targets.value.requests targets.value.masks (GraphOwnBandTargets.tree physical plan targets.value right)
      let out := GraphOwnBandTargets.execute physical plan input (by decide) b shapeOnlyScheme rfl rfl rfl hd stores.value
        (GraphOwnBandPreparation.sources_correct physical plan (by decide) input) targets.value
      unless out.bitSteps=ready.bitSteps+completed.bitSteps && out.control=ready.control+completed.control+16 do
        throw (IO.userError "Retained-target type setup was omitted or charged twice")
      unless out.value.toArray.size=0 do
        throw (IO.userError "Empty original request list gained output rows")
      let family := GraphOwnBandPreparation.get physical plan b banks.value
      for price in [0,1,7] do
        let envelopes := (List.finRange (GraphOwnBandCollection.G physical plan (S:=2))).foldl (fun acc g =>
          let root := GraphOwnBandPriced.auto physical plan b shapeOnlyScheme rfl rfl rfl hd
            targets.value.requests targets.value.masks (GraphOwnBandTargets.tree physical plan targets.value right) family g
          acc+root.bitSteps+price*root.control) 0
        unless out.bitSteps+price*out.control ≤ banks.bitSteps+price*banks.control+envelopes+
            GraphOwnBandPriced.extra physical plan (S:=2) price do
          throw (IO.userError "Actual own-band priced decomposition failed")
      unless banks.bitSteps ≤ GraphOwnBandCollection.G physical plan (S:=2)*GraphOwnBankCopyCosts.bits physical plan b do
        throw (IO.userError "Actual retained-bank copy bit bound failed")
      checked := checked+banks.value.toArray.size
    else throw (IO.userError "Unexpected empty support")
  IO.println s!"PASS: {checked} retained own-band/mask banks across both orientations; one actual binary cap, one shared physical-target/two-router preparation, per-type binary tile/setup and exact final counters; actual bank-copy bound and three global indexed-control prices."
  IO.println "SCOPE: empty graph/middle-block production integration with a shape-only zero-rank base; nonempty source algebra, routing and root coefficients are independently covered by existing fixtures, and production correctness for valid schemes is proved in Lean."
