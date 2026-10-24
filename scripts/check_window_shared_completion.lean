import RetainedWindowBatch
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
            let sources : Vector (OppositeWindowLayer.Source (2*k) C) B := Vector.ofFn (fun b =>
              Vector.ofFn (fun w => Vector.ofFn (fun c =>
                (BinaryMultiplierAdapter.encodeInteger (sourceValue seed b.val w.val c.val)).value)))
            for slot in List.finRange (RetainedRootWindows.slots k) do
              let layout := (RetainedWindowPermutation.build k (min ell k) normal slot).value
              let requests := if noRequests then #[] else
                ((List.range (4^(2*k))).map (labels (2*k))).toArray++#[labels (2*k) 0,labels (2*k) 0]
              let full := WindowSharedCompletion.execute scheme hD hA hZ hf hl sources layout requests
              let encoded := WindowSharedCompletion.encode ell total cn co sources
              let reused := WindowSharedCompletion.complete scheme hD hA hZ hf hl encoded.value layout requests
              let bank := SharedPrefixSourceBank.prepare encoded.value
              let retained := RetainedWindowBatch.execute scheme hD hA hZ hf hl bank.value layout requests
              unless retained.bitSteps+bank.bitSteps=reused.bitSteps do
                throw (IO.userError "Retained matrix bank charge is not paid exactly once")
              let mut checked := 0
              for original in List.finRange requests.size do
                for b in List.finRange B do
                  let old := WindowCompletionProgram.execute
                    (WindowPrefixProgram.execute ell total cn co (sources.get b)).value layout requests
                  for c in List.finRange C do
                    let actual := (full.value.get original).get (PrefixBlockBatch.column b c)
                    unless BinaryCell.view actual=BinaryCell.view ((old.completed.value.requests[original.val]'(by simp [old])).output.get c) do
                      throw (IO.userError "Shared window completion differs from production result")
                    unless BinaryCell.view actual=BinaryCell.view ((reused.value.get original).get (PrefixBlockBatch.column b c)) do
                      throw (IO.userError "Reused encoding differs from newly encoded result")
                    unless BinaryCell.view actual=BinaryCell.view ((retained.value.get original).get (PrefixBlockBatch.column b c)) do
                      throw (IO.userError "Retained completion matrix result differs")
                    checked := checked+1
              IO.println s!"PASS: k={k}, suffix={ell}, cap={total}, counts=({cn},{co}), normal={normal}, slot={slot.val}, blocks={B}, coefficients={C}, requests={requests.size}, seed={seed}; {checked} full outputs."
            return (RetainedRootWindows.slots k)*(if noRequests then 0 else 4^(2*k)+2)*B*C
  throw (IO.userError "Invalid rectangular fixture shape")

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
  IO.println s!"PASS: {checked} shared window/block outputs compared with production completion; both layouts, every rotation, clamped suffixes, own channel caps, retained encoding reuse, duplicate requests and empty cases."
  IO.println "SCOPE: fixed common-type window batch and production correctness; full APSP counter connection remains open."
