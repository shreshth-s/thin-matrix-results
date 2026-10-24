import AutoFullyRetainedRootBatch
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

def main : IO Unit := do
  let D := WindowSharedCompletion.D 0 0 0 0 0
  if hD : 0 < D then
    let sources : Vector (Vector (OppositeWindowLayer.Source 0 0) 1) 1 :=
      Vector.replicate 1 (Vector.replicate 1 (Vector.replicate 1 (Vector.replicate 0 BinaryCell.zero)))
    let encoded := sources.map (fun xs => (WindowSharedCompletion.encode 0 0 0 0 xs).value)
    let banks := encoded.map (fun xs => (SharedPrefixSourceBank.prepare xs).value)
    let layouts := Vector.replicate 1 (RetainedWindowPermutation.build 0 0 false ⟨0,by decide⟩).value
    let tile := AutoFullyRetainedRootBatch.prepare shapeOnlyScheme rfl rfl rfl D hD
    unless tile.value.A=SharedCompletionTile.row D && tile.value.Z=SharedCompletionTile.col D do
      throw (IO.userError "Retained tile does not consume actual binary dimensions")
    for labels in ([#[],#[Vector.replicate 0 0,Vector.replicate 0 0]] : List (Array (Vector (Fin 4) 0))) do
      let reused := AutoFullyRetainedRootBatch.executeWith shapeOnlyScheme hD tile.value banks layouts labels
      let auto := AutoFullyRetainedRootBatch.execute shapeOnlyScheme rfl rfl rfl hD banks layouts labels
      unless auto.bitSteps=tile.bitSteps+reused.bitSteps && auto.control=reused.control+16 do
        throw (IO.userError "Auto root setup was not counted exactly once")
      for j in List.finRange labels.size do
        unless (RootProductCollection.output auto.value j).map BinaryCell.view=
          (RootProductCollection.output reused.value j).map BinaryCell.view do
          throw (IO.userError "Auto root output differs from reused binary tile")
      IO.println s!"PASS: auto root shape setup, requests={labels.size}; tile={tile.value.A}x{tile.value.Z}; binary setup={tile.bitSteps}."
  else throw (IO.userError "Unexpected zero support")
  let mut checks := 0
  for U in [0,1,3,8] do
    unless SharedCompletionWidths.controlPrice U ≤ 108900*(U+1)^2 do
      throw (IO.userError "Inclusive global address price bound failed")
    for M in [0,1] do
      for D in [0,1] do
        let span := SharedFullyAddressedBatch.addressSpan M D 1 1 1
        unless span ≤ 12*2^U && span.size ≤ U+5 do
          throw (IO.userError "Global prefix address-span bound failed")
        checks := checks+1
  IO.println s!"PASS: {checks} inclusive address widths and prices. SCOPE: auto-wrapper setup reuse/empty-column control smoke test with an explicit shape-only zero-rank fixture, not a valid matrix-multiplication base. Full nonempty coefficients are covered by the retained-root2856-output fixture; correctness for valid schemes is proved in Lean."
