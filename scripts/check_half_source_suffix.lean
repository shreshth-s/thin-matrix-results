import HalfSourceSuffixFeasible

open ThinMatrix
open HalfSourceSuffixChoice

def bruteCount (ell rare : ℕ) : ℕ :=
  ((List.range (2^ell)).filter (fun x => x.bits.count true ≤ rare)).length

def bruteChoice (k rare cap : ℕ) : ℕ :=
  ((List.range (k+1)).filter (fun ell => bruteCount ell (rare*ell/k) ≤ cap)).foldl max 0

def main : IO Unit := do
  let mut countChecks := 0
  let mut choiceChecks := 0
  let mut shapeChecks := 0
  for ell in List.range 10 do
    for rare in List.range 12 do
      if CappedSubsetList.count ell rare != bruteCount ell rare then
        throw (IO.userError s!"count mismatch ell={ell} rare={rare}")
      countChecks := countChecks+1
  for k in List.range 9 do
    for rare in List.range (k+1) do
      for cap in List.range 19 do
        let got := choose k rare cap
        let expected := bruteChoice k rare cap
        if got != expected then
          throw (IO.userError s!"choice mismatch k={k} rare={rare} cap={cap} got={got} expected={expected}")
        if got > k then throw (IO.userError "selected suffix exceeds physical half")
        if cap > 0 && bruteCount got (rare*got/k) > cap then
          throw (IO.userError "selected support does not fit cap")
        choiceChecks := choiceChecks+1
  for m in List.range 500 do
    let L := OptimizedFoldedPlan.ordinaryLength m
    let t := OptimizedFoldedPlan.channelLength m
    if L*100000000000000 < 1042290323194818*m ||
        (L>0 && (L-1)*100000000000000 >= 1042290323194818*m) then
      throw (IO.userError s!"ordinary rounding mismatch m={m}")
    if t*100000000000000 < 13136812853998*m ||
        (t>0 && (t-1)*100000000000000 >= 13136812853998*m) then
      throw (IO.userError s!"channel rounding mismatch m={m}")
    if t > m || L < m then throw (IO.userError "invalid rounded shape")
    shapeChecks := shapeChecks+1
  IO.println s!"PASS {countChecks} exact support counts against exhaustive Boolean subsets"
  IO.println s!"PASS {choiceChecks} suffix choices against exhaustive support counts"
  IO.println s!"PASS {shapeChecks} exact integer ordinary/channel ceil roundings"
  IO.println "Scope: finite selector/rounding checks; not an asymptotic production cost certificate."
