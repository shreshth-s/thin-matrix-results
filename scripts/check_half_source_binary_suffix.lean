import HalfSourceSuffixProgram

open ThinMatrix

def bruteCount (ell rare : Nat) : Nat :=
  (List.range (2^ell)).countP (fun mask => mask.bits.count true ≤ rare)

def bruteChoice (k rare cap : Nat) : Nat := Id.run do
  let mut best := 0
  for ell in List.range (k+1) do
    if bruteCount ell (rare*ell/k) ≤ cap then best := ell
  return best

def main : IO Unit := do
  let mut checks := 0
  for k in List.range 8 do
    for rare in List.range (k+1) do
      if hr : rare ≤ k then
        for cap in List.range 21 do
          let out := HalfSourceSuffixProgram.execute k rare cap hr
          let expected := bruteChoice k rare cap
          if out.value.2.2 != expected then
            throw (IO.userError s!"binary selector mismatch {(k,rare,cap)}: {out.value.2.2} != {expected}")
          if out.bitSteps > HalfSourceSuffixProgram.bitBudget k cap.size then
            throw (IO.userError "binary bit budget exceeded")
          if out.control > HalfSourceSuffixProgram.controlBudget k cap.size then
            throw (IO.userError "binary control budget exceeded")
          checks := checks+1
  IO.println s!"PASS {checks} binary Pascal/division/comparison suffix selectors against exhaustive Boolean subsets"
  IO.println "PASS actual bit/control counters within the proved polynomial budgets"
  IO.println "Scope: finite exact suffix setup fixture; not a full APSP runtime proof."
