import SelectedRootProduct
open ThinMatrix BinaryCell BinaryResidualPolynomial

private def number (seed : Int) (d r : Nat) : Int :=
  let z := seed+(d:Int)*3+(r:Int)*5
  if (d+r)%3=0 then z else if (d+r)%3=1 then -z else 0

private def make (F q : Nat) (seed : Int) : Block F q :=
  Vector.ofFn (fun d => Vector.ofFn (fun r =>
    (BinaryMultiplierAdapter.encodeInteger (number seed d.val r.val)).value))

private def naive (F q t card r : Nat) (wa : Nat → Int) (a b : Nat → Nat → Int) : Int := Id.run do
  let mut out := 0
  for d in List.range t do
    if card≤d then
      for d1 in List.range F do
        for d2 in List.range F do
          if d1+d2=d-card then
            for r1 in List.range q do
              for r2 in List.range q do
                if (r1+r2)%q=r then
                  out := out+wa d*a d1 r1*b d2 r2
  return out

private def check (F q t card : Nat) (seed : Int) : IO Nat := do
  if hq : 0<q then
    letI : NeZero q := ⟨Nat.ne_of_gt hq⟩
    let a := make F q seed
    let b := make F q (-seed-2)
    let ws : Vector Cell t := Vector.ofFn (fun d => (BinaryMultiplierAdapter.encodeInteger (number 7 d.val 0)).value)
    let A := seed.natAbs+2+3*F+5*q
    let W := 7+3*t
    for r in List.finRange q do
      let out := SelectedRootProduct.execute ws a b card r
      let reference := naive F q t card r.val (fun d => number 7 d 0) (number seed) (number (-seed-2))
      unless view out.value=reference do
        throw (IO.userError s!"Selected root mismatch: F={F},q={q},t={t},card={card},r={r.val}")
      let old := WeightedRootProducts.execute ws (CompletedRootProducts.execute a b).value card
      unless view out.value=view (old.value.sum.value.get r) do
        throw (IO.userError "Selected coefficient differs from original complete product")
      unless out.bitSteps≤SelectedRootProduct.bitBudget q t W A do
        throw (IO.userError "Selected root bit budget exceeded")
      unless out.control≤SelectedRootProduct.controlBudget q t do
        throw (IO.userError "Selected root control budget exceeded")
    return q
  throw (IO.userError "Zero cyclic length")

def main : IO Unit := do
  let mut checked := 0
  for seed in ([-7,65537] : List Int) do
    for F in [0,1,3] do
      for q in [1,3,5,7] do
        for t in [0,1,4,7] do
          for card in [0,1,3,9] do
            checked := checked+(← check F q t card seed)
  IO.println s!"PASS: {checked} selected cyclic coefficients against independent signed convolution and original complete weighted product; empty degree ranges, wrapped residues, excluded channels and both cost counters."
  IO.println "SCOPE: finite selected-coefficient root product; full APSP cost connection remains open."
