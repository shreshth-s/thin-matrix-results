import PaddedMatrix
open ThinMatrix FiniteTrilinear RecursiveTable
open scoped BigOperators
private def rectTerms (s : Fin 25) : Term (Fin 2×Fin 4) (Fin 2×Fin 6) (Fin 2×Fin 6) ℚ :=
  if s.val<24 then
    let copy := s.val/12
    let row := (s.val%12)/6
    let inner := (s.val%6)/3
    let col := s.val%3
    let sign : ℚ := if s.val%2=0 then 1 else -1
    ⟨fun i => if i.1.val=copy ∧ i.2.val=2*row+inner then sign else 0,
     fun j => if j.1.val=copy ∧ j.2.val=3*inner+col then sign else 0,
     fun z => if z.1.val=copy ∧ z.2.val=3*row+col then 1 else 0⟩
  else ⟨fun _ => 0,fun _ => 0,fun _ => 0⟩

private def matrixBase : RetainedEqualCopy.Base 25 2 (prod (fin 2) (fin 2))
    (prod (fin 2) (fin 3)) (prod (fin 3) (fin 2)) ℚ :=
  ⟨store _ (fun p => (rectTerms p.1).left (p.2.1,⟨2*p.2.2.1.val+p.2.2.2.val,by omega⟩)),
   store _ (fun p => (rectTerms p.1).middle (p.2.1,⟨3*p.2.2.1.val+p.2.2.2.val,by omega⟩)),
   store _ (fun p => (rectTerms p.1).right (p.2.1,⟨3*p.2.2.2.val+p.2.2.1.val,by omega⟩))⟩


private def check (n m p : Nat) (seed : Int) : IO Nat := do
  let lx := PaddedMatrix.matrix n m
  let ly := PaddedMatrix.matrix m p
  let x := store lx (fun i => (BinaryMultiplierAdapter.encodeInteger (seed+3*(lx.index i).val-4)).value)
  let y := store ly (fun i => (BinaryMultiplierAdapter.encodeInteger (2*seed-2*(ly.index i).val+7)).value)
  let answer := PaddedMatrix.atSize (fin 2) (fin 2) (fin 3) (by decide)
    (by decide) (by decide) (by decide) matrixBase x y
  let k := PaddedMatrix.depth 2 2 3 n m p
  let magnitude := (x.toList ++ y.toList).foldl (fun b z => max b (BinaryCell.view z).natAbs) 1
  unless answer.bitSteps ≤ BinaryRecursiveCost.bits matrixBase k magnitude do
    throw (IO.userError "Padded execution exceeds the complete binary arithmetic budget")
  for i in List.finRange n do
    for j in List.finRange p do
      let expected := ∑ v : Fin m, BinaryCell.view (read x (i,v))*BinaryCell.view (read y (v,j))
      unless BinaryCell.view (read answer.value (i,j)) == expected do
        throw (IO.userError "Padded matrix result differs from direct original product")
  IO.println s!"PASS: padded {n}x{m} by {m}x{p}, depth {k}, seed {seed}; {n*p} entries."
  return n*p

def main : IO Unit := do
  let mut checked := 0
  for dims in ([(0,0,0),(0,3,2),(2,0,3),(1,1,1),(1,2,3),(2,2,3),(3,2,4),(3,3,4)] : List (Nat×Nat×Nat)) do
    for seed in ([-3,65537] : List Int) do
      checked := checked + (← check dims.1 dims.2.1 dims.2.2 seed)
  IO.println s!"PASS: {checked} original matrix entries after selected-depth padding and cropping; complete arithmetic budget checked."
  IO.println "SCOPE: address and depth-selection binary costs and the full APSP bound remain unproved."
