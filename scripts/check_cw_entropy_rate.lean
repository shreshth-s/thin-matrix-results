import CWTargetExtractionRate
import CWFiniteKeys

open ThinMatrix PolynomialDegeneration CWSixBlocks CWBlockWords CWTypeCounts CWCanonicalType

private def checkCoefficients : IO Unit := do
  let mut checked := 0
  for a in List.range 7 do
    for b in List.range 7 do
      for c in List.range 7 do
        let n := a+b+c
        let m := TernaryEntropy.coefficient a b c
        unless m == n.choose a*(b+c).choose b do throw (IO.userError "Ternary factorization failed")
        let numerator := n^n
        let denominator := a^a*b^b*c^c
        unless m*denominator ≤ numerator && numerator ≤ m*(n+1)^2*denominator do
          throw (IO.userError "Exact entropy-weight inequality failed")
        checked := checked+1
  IO.println s!"PASS: {checked} actual ternary coefficient cases and exact entropy-weight inequalities."

private def checkTarget : IO Unit := do
  let scales := [0,1,2,3,17,101]
  for s in scales do
    for axis in List.finRange 3 do
      for a in List.finRange 3 do
        let actual := ([Block.b011,.b101,.b110,.b002,.b020,.b200]).foldl (fun total b =>
          total + if CWTargetMarginals.color axis b == a then s*targetCounts b else 0) 0
        unless actual == s*CWTargetMarginals.counts axis a do
          throw (IO.userError "Target marginal table mismatch")
  IO.println "PASS: 18 scaled target marginal histograms, from actual block colors and counts."
  let P := period
  let lengths := [0,1,P-1,P,P+1,2*P-1,2*P,2*P+1,17*P-1,17*P,17*P+1,101*P+999]
  for N in lengths do
    let s := CWEntropyFloors.scale N
    unless s*P ≤ N && N < s*P+P && (s > 0) == (N ≥ P) do
      throw (IO.userError "Floor arithmetic failed")
  unless CWTargetMarginals.size 0 == 0 do throw (IO.userError "Zero-size target failed")
  for axis in List.finRange 3 do
    unless CWTypeCardinalities.marginalCount 0 (reference 0) (CWTargetMarginals.color axis) == 1 do
      throw (IO.userError "Zero-scale marginal cardinality failed")
  IO.println "PASS: 12 floor boundary cases and actual zero-scale target cardinalities."

private def checkWords : IO Unit := do
  let mut checked := 0
  for n in List.range 5 do
    for w in CWFiniteKeys.keys ([Block.b011,.b101,.b110,.b002,.b020,.b200]) n do
      for axis in List.finRange 3 do
        for a in List.finRange 3 do
          let aggregate := ([Block.b011,.b101,.b110,.b002,.b020,.b200]).foldl
            (fun t b => t+if CWTargetMarginals.color axis b == a then count b n w else 0) 0
          unless count a n (mapWord (CWTargetMarginals.color axis) n w) == aggregate do
            throw (IO.userError "Actual bounded word marginal mismatch")
      checked := checked+1
  IO.println s!"PASS: {checked} actual bounded CW words and marginal histograms."

def main : IO Unit := do
  checkCoefficients
  checkTarget
  checkWords
  IO.println "SCOPE: actual finite arithmetic and zero scale; real entropy/rate proofs are kernel-checked. No positive-scale target word is materialized."
