import HalfSourceCapSetup

open ThinMatrix

def main : IO Unit := do
  let mut checks := 0
  for m in List.range 3 do
    for k in [0,1,10*m] do
      let actual := HalfSourceCapSetup.execute m k
      let expected := HalfSourceSuffixChoice.limit m k
      if actual.value != expected then throw (IO.userError s!"cap mismatch m={m}, k={k}")
      if actual.bitSteps > HalfSourceCapSetup.bitBudget m k then throw (IO.userError "cap bit budget exceeded")
      checks := checks+1
  IO.println s!"PASS {checks} binary shared-cap constructions against exact integer power comparisons"
  IO.println "PASS actual bit counters within the proved O(4^m poly(m+size(k))) bound"
  IO.println "Scope: shared shape setup only, with native control/address lowering separate."
