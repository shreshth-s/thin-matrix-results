import CWFiniteSurvival

open ThinMatrix PolynomialDegeneration CWBlockWords CWSixBlocks CWHashFibers CWPairHashFibers
open CWFilteredHashCounts CWQuantitativeCleanup

private def values (M : Nat) : List (ZMod M) := List.ofFn (fun i : Fin M => (i.val:ZMod M))
private def samples (M n : Nat) : List (Sample (ZMod M) n) :=
  (values M).flatMap fun b => (values M).flatMap fun w0 =>
    (CWFiniteKeys.keys (values M) n).map fun w => (b,w0,w)
private def blocks : List Block := [.b011,.b101,.b110,.b002,.b020,.b200]

private def checkFibers (M n : Nat) [Fact (Nat.Prime M)] (words : List (Word n)) : IO Unit := do
  let rs := samples M n
  unless rs.length == M^(n+2) do throw (IO.userError "Sample enumeration length mismatch")
  let mut single := 0
  let mut joint := 0
  for u in words do
    for c in values M do
      let count := (rs.filter fun r => decide (WordEvent n u c r)).length
      unless count == M^n do throw (IO.userError "Actual single-bucket fiber mismatch")
      single := single+1
    for v in words do
      if decide (u≠v ∧ (wx n u=wx n v ∨ wy n u=wy n v ∨ wz n u=wz n v)) then
        for c in values M do
          let count := (rs.filter fun r => decide (WordEvent n u c r ∧ WordEvent n v c r)).length
          unless count == M^(n-1) do throw (IO.userError "Actual shared-pair bucket fiber mismatch")
          joint := joint+1
  IO.println s!"PASS: M={M}, n={n}: {rs.length} actual samples, {single} single fibers, {joint} shared-pair fibers."

private def checkCleanup (M n : Nat) [Fact (Nat.Prime M)] (reference : Word n)
    (B : Finset (ZMod M)) : IO Unit := do
  let T := (fullClass n reference).card
  let P := (allCollisions n reference).card
  let mut candidates := 0
  let mut collisions := 0
  let mut maximum := 0
  for r in samples M n do
    let before := (filtered M n reference B r).card
    let kept := (survivors M n reference B r).card
    let lost := (filteredCollisions M n reference B r).card
    unless before ≤ kept+lost do throw (IO.userError "Actual cleanup inequality failed")
    candidates := candidates+before
    collisions := collisions+lost
    maximum := max maximum kept
  unless candidates == T*B.card*M^n && collisions == P*B.card*M^(n-1) do
    throw (IO.userError "Actual total candidate/collision count mismatch")
  unless T*B.card*M^n ≤ M^(n+2)*maximum+P*B.card*M^(n-1) do
    throw (IO.userError "Actual quantitative survivor bound failed")
  IO.println s!"PASS: cleanup M={M}, n={n}, |B|={B.card}, T={T}, P={P}: totals {candidates}/{collisions}, best kept {maximum}."

instance : Fact (Nat.Prime 3) := ⟨by decide⟩
instance : Fact (Nat.Prime 5) := ⟨by decide⟩
instance : Fact (Nat.Prime 7) := ⟨by decide⟩

def main : IO Unit := do
  checkFibers 3 0 [PUnit.unit]
  checkFibers 3 1 (CWFiniteKeys.keys blocks 1)
  checkFibers 5 1 (CWFiniteKeys.keys blocks 1)
  checkFibers 7 1 (CWFiniteKeys.keys blocks 1)
  let u : Word 2 := (.b011,.b101,PUnit.unit)
  let v : Word 2 := (.b101,.b011,PUnit.unit)
  checkFibers 5 2 [u,v]
  checkCleanup 3 0 PUnit.unit {0}
  checkCleanup 3 0 PUnit.unit ∅
  checkCleanup 5 2 u {0,1}
  IO.println "SCOPE: exact finite hash counts and actual cleanup; no execution-cost or entropy-scale assertion."
