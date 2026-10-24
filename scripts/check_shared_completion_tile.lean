import SharedCompletionTile
import FullyRetainedWindowCosts
open ThinMatrix

set_option maxRecDepth 20000
set_option exponentiation.threshold 2048

def main : IO Unit := do
  for s in [0,1] do
    let out := SharedCompletionTile.execute s
    unless out.value=(SharedCompletionTile.row s,SharedCompletionTile.col s) do
      throw (IO.userError "Actual binary tile setup disagrees with canonical rounded dimensions")
    unless out.bitSteps ≤ SharedCompletionTile.bitBudget s do
      throw (IO.userError "Binary tile setup bit bound exceeded")
    if 0 < s then
      unless (out.value.1-1)^500 ≤ s^861 do
        throw (IO.userError "Exact integer tile fit failed")
      unless s^861 < out.value.1^500 do
        throw (IO.userError "Exact strict rounding lower bound failed")
      unless out.value.1 ≤ 2*s^2 do
        throw (IO.userError "Rounded tile coarse upper bound failed")
      unless out.bitSteps ≤ 1000000000000000*out.value.2*(s.size+2)^2 do
        throw (IO.userError "Shared tile setup not absorbed by independent full coefficient batch")
    IO.println s!"PASS: support={s}; row={out.value.1}; columns={out.value.2}; binary bitsteps={out.bitSteps}."
  for s in [2,3,7] do
    let A := SharedCompletionTile.row s
    unless (A-1)^500 ≤ s^861 && s^861 < A^500 do
      throw (IO.userError "Independent integer rounded tile geometry failed")
    IO.println s!"PASS: integer tile geometry support={s}, row={A}, columns={SharedCompletionTile.col s}."
  let mut count := 0
  for k in [0,1,3] do
    for P in [0,1,3] do
      for ell in [0,1,2] do
        for M in [0,1,4] do
          for Q in [1,2,7] do
            let L := k+P+ell+2
            unless FullyRetainedWindowCosts.overhead k P ell M Q ≤ 512*L^2*Q*(M+2^ell*4^P) do
              throw (IO.userError "Retained window routing/transport/scatter overhead bound failed")
            count := count+1
  IO.println s!"PASS: {count} retained window overhead comparisons; actual binary square/root/increment/power/decode runs for support0/1, integer rounded geometry for support2/3/7, exact fit and absorbed complete batch cost. All support sizes and native setup counters are covered by the Lean proofs."
