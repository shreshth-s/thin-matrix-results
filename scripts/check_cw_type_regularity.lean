import CWTypePrimeChoice
import CWFiniteKeys

open ThinMatrix PolynomialDegeneration CWSixBlocks CWBlockWords CWTypeCounts
open CWFilteredHashCounts CWQuantitativeCleanup CWTypeRegularity CWTypeCardinalities CWMultinomialSurvival

private def blocks : List Block := [.b011,.b101,.b110,.b002,.b020,.b200]

private def check (n : Nat) : IO Unit := do
  let words := CWFiniteKeys.keys blocks n
  let mut seen : List (List Nat) := []
  let mut fibers := 0
  let mut pairs := 0
  for reference in words do
    let histogram := blocks.map (fun b => count b n reference)
    if !seen.contains histogram then
      seen := histogram::seen
      let E := fullClass n reference
      let T := E.card
      unless T == jointCount n reference do throw (IO.userError "Joint multinomial mismatch")
      for k in [cx,cy,cz] do
        let X := E.image (mapWord k n)
        unless X == marginalClass n (mapWord k n reference) do
          throw (IO.userError "Full marginal image mismatch")
        unless X.card == marginalCount n reference k do
          throw (IO.userError "Marginal multinomial mismatch")
        let D := degree n reference k
        unless 0 < D && X.card*D == T && T/X.card == D do
          throw (IO.userError "Fiber division or positivity mismatch")
        for x in CWFiniteKeys.keys ([0,1,2] : List (Fin 3)) n do
          if x ∈ X then
            unless (fiber n reference k x).card == D do
              throw (IO.userError "Actual fiber regularity mismatch")
            fibers := fibers+1
      let P := (allCollisions n reference).card
      unless P == T*(degreeSum n reference-3) do
        throw (IO.userError "Actual ordered collision count mismatch")
      pairs := pairs+T*(T-1)
      let M := CWTypePrimeChoice.selected n reference
      unless CWTypePrimeChoice.smallestMarginal n reference*M ≤ 12*T do
        throw (IO.userError "Smallest marginal density bound mismatch")
      unless decide (Nat.Prime M) && 2*degreeSum n reference < M && M ≤ 4*degreeSum n reference do
        throw (IO.userError "Actual selected prime mismatch")
  IO.println s!"PASS: n={n}: {seen.length} actual classes, {words.length} words, {fibers} coordinate fibers, {pairs} ordered distinct pairs."

def main : IO Unit := do
  check 0
  check 1
  check 2
  check 3
  IO.println "SCOPE: executable constructed classes, fiber/cardinality formulas, actual collisions and prime selector; no execution-cost or entropy-rate assertion."
