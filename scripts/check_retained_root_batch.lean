import RetainedRootBatch
open ThinMatrix RecursiveTable
open scoped BigOperators

private def smallBase : RetainedEqualCopy.Base 9 1 (prod (fin 2) (fin 2))
    (prod (fin 2) (fin 2)) (prod (fin 2) (fin 2)) ℚ :=
  ⟨store _ (fun p => if p.1.val < 8 && p.2.2.1.val == p.1.val/4 && p.2.2.2.val == (p.1.val/2)%2 then 1/2 else 0),
   store _ (fun p => if p.1.val < 8 && p.2.2.1.val == (p.1.val/2)%2 && p.2.2.2.val == p.1.val%2 then -2 else 0),
   store _ (fun p => if p.1.val < 8 && p.2.2.1.val == p.1.val%2 && p.2.2.2.val == p.1.val/4 then -1 else 0)⟩

private def scheme : RectangularBatch.Scheme :=
  ⟨2,2,2,1,1,1,9,1,by decide,by decide,by decide,by decide,rfl,rfl,smallBase⟩

private def digit (base code position : Nat) : Nat := code/base^position%base

private def labels (n code : Nat) : Vector (Fin 4) n :=
  Vector.ofFn (fun i => ⟨digit 4 code i.val,Nat.mod_lt _ (by decide)⟩)

private def sourceValue (seed : Int) (block word col : Nat) : Int :=
  let magnitude := seed+(block:Int)*5+(col:Int)*3
  if word%3=0 then magnitude else if word%3=1 then -magnitude else 0

private def entry (q a : Nat) : Int :=
  if q=0 then (if a=0 || a=2 then 1 else 0)
  else if q=1 then (if a=0 then 1 else 0)
  else if q=2 then (if a=1 then 1 else if a=2 then -1 else 0)
  else if a=1 then 1 else 0

private def check (k ell total cn co B C A Z : Nat) (seed : Int) (normal noRequests : Bool) : IO Nat := do
  let D := WindowSharedCompletion.D k ell total cn co
  if hD : 0<D then
    if hA : 0<A then
      if hZ : 0<Z then
        if hf : (A-1)^scheme.den≤D^scheme.num then
          if hl : Z≤D^scheme.z then
            let W := RetainedRootWindows.slots k
            let sources : Vector (Vector (OppositeWindowLayer.Source (2*k) C) B) W := Vector.ofFn (fun s =>
              Vector.ofFn (fun b => Vector.ofFn (fun w => Vector.ofFn (fun c =>
                (BinaryMultiplierAdapter.encodeInteger (sourceValue (seed+(s.val:Int)*11) b.val w.val c.val)).value))))
            let encoded := Vector.ofFn (fun s => (WindowSharedCompletion.encode ell total cn co (sources.get s)).value)
            let banks := Vector.ofFn (fun s => (SharedPrefixSourceBank.prepare (encoded.get s)).value)
            let layouts := Vector.ofFn (fun s => (RetainedWindowPermutation.build k (min ell k) normal s).value)
            let requests := if noRequests then #[] else
              ((List.range (4^(2*k))).map (labels (2*k))).toArray++#[labels (2*k) 0,labels (2*k) 0]
            let out := RetainedRootBatch.execute scheme hD hA hZ hf hl banks layouts requests
            let H := 2^(WindowPrefixProgram.prefixLength k ell)*(seed.natAbs+W*11+B*5+C*3)
            let mut childBits := 0
            for s in List.finRange W do
              childBits := childBits+(RetainedWindowBatch.execute scheme hD hA hZ hf hl (banks.get s) (layouts.get s) requests).bitSteps
            unless out.bitSteps≤childBits+requests.size*(W*((B*C)*BackendScalarBits.backendScalarUnit (W*(D*H)).size)) do
              throw (IO.userError "Root batch addition bit budget exceeded")
            unless out.control≤RootProductCollection.controlBudget
              (fun s => (RetainedWindowBatch.execute scheme hD hA hZ hf hl (banks.get s) (layouts.get s) requests).control) requests.size (B*C) do
              throw (IO.userError "Root batch control budget exceeded")
            for j in List.finRange requests.size do
              for b in List.finRange B do
                for c in List.finRange C do
                  let mut expected := 0
                  for s in List.finRange W do
                    let old := WindowCompletionProgram.execute
                      (WindowPrefixProgram.execute ell total cn co ((sources.get s).get b)).value (layouts.get s) requests
                    expected := expected+BinaryCell.view ((old.completed.value.requests[j.val]'(by simp [old])).output.get c)
                  unless BinaryCell.view ((RootProductCollection.output out.value j).get (PrefixBlockBatch.column b c))=expected do
                    throw (IO.userError "Root batch differs from sum of production windows")
            return requests.size*B*C
  throw (IO.userError "Invalid fixture shape")

def main : IO Unit := do
  let mut checked := 0
  for seed in ([-7,65537] : List Int) do
    for normal in [false,true] do
      checked := checked+(← check 0 0 0 0 0 2 3 1 1 seed normal false)
      checked := checked+(← check 1 1 1 0 0 3 2 2 2 seed normal false)
      checked := checked+(← check 2 1 1 1 0 2 1 1 1 seed normal false)
      checked := checked+(← check 1 9 1 0 1 2 2 1 1 seed normal false)
      checked := checked+(← check 1 1 0 0 0 1 0 1 1 seed normal false)
      checked := checked+(← check 1 1 1 0 0 0 3 2 2 seed normal false)
      checked := checked+(← check 1 1 1 0 0 2 2 2 2 seed normal true)
  IO.println s!"PASS: {checked} complete shared root outputs against sum of original per-window completions; independent data for each window, both orientations, duplicate and empty requests, and both aggregate cost counters."
  IO.println "SCOPE: retained window sum with full block/coefficient columns; full APSP caller connection remains open."
