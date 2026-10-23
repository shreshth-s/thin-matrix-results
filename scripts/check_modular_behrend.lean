import CWBehrendSurvival
import CWFiniteKeys

open ThinMatrix PolynomialDegeneration CWBlockWords CWSixBlocks CWHashFibers
open CWFilteredHashCounts CWQuantitativeCleanup CWTypePrimeChoice ModularBehrendBuckets FiniteAPSearch

private def values (M : Nat) : List (ZMod M) := List.ofFn (fun i : Fin M => (i.val:ZMod M))
private def samples (M n : Nat) : List (Sample (ZMod M) n) :=
  (values M).flatMap fun b => (values M).flatMap fun w0 =>
    (CWFiniteKeys.keys (values M) n).map fun w => (b,w0,w)

private def checkIntervals : IO Unit := do
  let expected := [0,1,2,2,3,4,4,4,4,5,5,6,6]
  for N in List.range 13 do
    let s := chosen N
    unless decide (Good s) && decide (s ⊆ Finset.range N) do
      throw (IO.userError "Actual integer set is not admissible")
    unless s.card == expected[N]! && (subsets N).length == 2^N do
      throw (IO.userError "Integer selector/cardinality mismatch")
  IO.println "PASS: actual interval selector for N=0..12; 8191 candidate subsets."
  for M in List.range 26 do
    let B := buckets M
    unless B.card == (chosen (M/2)).card do throw (IO.userError "Modular cardinality mismatch")
    unless decide (∀ a ∈ B,∀ b ∈ B,∀ c ∈ B,a+c=b+b → a=b) do
      throw (IO.userError "Actual modular set contains a nontrivial progression")
  IO.println "PASS: actual modular buckets for M=0..25, including empty and singleton cases."

private def checkCleanup (n : Nat) (reference : Word n) : IO Unit := do
  let M := selected n reference
  let B := buckets M
  let T := (fullClass n reference).card
  let P := (allCollisions n reference).card
  let mut candidates := 0
  let mut collisions := 0
  let mut maximum := 0
  let rs := samples M n
  for r in rs do
    let before := (filtered M n reference B r).card
    let kept := (survivors M n reference B r).card
    let lost := (filteredCollisions M n reference B r).card
    unless before ≤ kept+lost do throw (IO.userError "Actual cleanup inequality failed")
    candidates := candidates+before
    collisions := collisions+lost
    maximum := max maximum kept
  unless candidates == T*B.card*M^n && collisions == P*B.card*M^(n-1) do
    throw (IO.userError "Actual constructed-bucket totals mismatch")
  unless smallestMarginal n reference*B.card ≤ 24*M*maximum do
    throw (IO.userError "Actual density survival bound failed")
  IO.println s!"PASS: actual cleanup n={n}, selected M={M}, constructed |B|={B.card}: {rs.length} samples, totals {candidates}/{collisions}, best kept {maximum}."

def main : IO Unit := do
  checkIntervals
  checkCleanup 0 PUnit.unit
  checkCleanup 1 (.b011,PUnit.unit)
  checkCleanup 2 (.b011,.b101,PUnit.unit)
  IO.println "SCOPE: actual exhaustive bucket construction and cleanup; real Behrend inequalities are kernel-checked, not runtime float checks; no generation-cost assertion."
