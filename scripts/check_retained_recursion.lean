import CWRetainedArithmetic
import BinaryRecursiveCost
import BinaryMatrixPowers

open ThinMatrix FiniteTrilinear PolynomialDegeneration RecursiveTable
open scoped BigOperators

private def fromTerms {r t i j o : ℕ}
    (d : Fin r → Term (Fin t×Fin i) (Fin t×Fin j) (Fin t×Fin o) ℚ) :
    RetainedEqualCopy.Base r t (fin i) (fin j) (fin o) ℚ :=
  ⟨store _ (fun p => (d p.1).left p.2),store _ (fun p => (d p.1).middle p.2),
    store _ (fun p => (d p.1).right p.2)⟩

private def dotTerms (s : Fin 5) : Term (Fin 2×Fin 2) (Fin 2×Fin 2) (Fin 2×Fin 1) ℚ :=
  let weights : Fin 4 → ℚ := ![2,-1/2,1/2,-2]
  if h : s.val<4 then
    let w := weights ⟨s.val,h⟩
    ⟨fun i => if i.1.val=s.val/2 ∧ i.2.val=s.val%2 then w else 0,
     fun j => if j.1.val=s.val/2 ∧ j.2.val=s.val%2 then w⁻¹ else 0,
     fun z => if z.1.val=s.val/2 then 1 else 0⟩
  else ⟨fun _ => 0,fun _ => 0,fun _ => 0⟩

/-- Two 2-by-2 times 2-by-3 products and a padded 25th request. -/
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

private def check {r i j o : ℕ} (name : String)
    (d : RetainedEqualCopy.Base r 2 (fin i) (fin j) (fin o) ℚ)
    (u : Tensor (Fin i) (Fin j) (Fin o) ℤ) (k : ℕ) (seed : ℤ) : IO Nat := do
  let lx := RetainedEqualCopy.copies 2 (fin i) k
  let ly := RetainedEqualCopy.copies 2 (fin j) k
  let lz := RetainedEqualCopy.copies 2 (fin o) k
  let x := store lx (fun p => seed+3*(lx.index p).val-4)
  let y := store ly (fun p => 2*seed-2*(ly.index p).val+7)
  let bx := x.map (fun z => (BinaryMultiplierAdapter.encodeInteger z).value)
  let bys := y.map (fun z => (BinaryMultiplierAdapter.encodeInteger z).value)
  let qx := x.map (fun (z : ℤ) => (z:ℚ))
  let qy := y.map (fun (z : ℤ) => (z:ℚ))
  let rational := RetainedEqualCopy.run (fin i) (fin j) (fin o) (by decide) d k qx qy
  let encoded := ClearedRecursiveBase.encode d
  let binary := BinaryRetainedEqualCopy.run (fin i) (fin j) (fin o) (by decide) encoded.value k bx bys
  let recovered := BinaryRecursiveRecovery.execute (by decide) d k bx bys
  let den := ClearedRecursiveBase.common d
  let magnitude := (x.toList ++ y.toList).foldl (fun b z => max b z.natAbs) 1
  unless recovered.bitSteps ≤ BinaryRecursiveCost.bits d k magnitude do
    throw (IO.userError "Complete binary cost exceeds its derived input-bound budget")
  unless rational.arithmetic == RetainedEqualCopyCosts.arithmetic r 2 i j o k do
    throw (IO.userError "Arithmetic recurrence differs from executed counter")
  unless rational.control == RetainedEqualCopyCosts.control r 2 i j o k && binary.control == rational.control do
    throw (IO.userError "Control recurrence differs from executed counter")
  for slot in List.finRange lz.size do
    let z := lz.index.symm slot
    let expected := bilinear (tensorPower u k) (fun p => read x (z.1,p)) (fun p => read y (z.1,p)) z.2
    unless read rational.value z == (expected:ℚ) do throw (IO.userError "Rational evaluator differs from dense tensor")
    unless BinaryCell.view (read binary.value z) == (den:ℤ)^(3*k)*expected do
      throw (IO.userError "Integer numerator has the wrong common factor")
    unless BinaryCell.view (read recovered.value z) == expected do
      throw (IO.userError "Binary recovery differs from dense tensor")
  IO.println s!"PASS: {name}, depth {k}, seed {seed}, {lz.size} outputs; {rational.arithmetic} ring operations; {binary.bitSteps} binary steps."
  return lz.size

private def matrixBase : RetainedEqualCopy.Base 25 2 (prod (fin 2) (fin 2))
    (prod (fin 2) (fin 3)) (prod (fin 3) (fin 2)) ℚ :=
  ⟨store _ (fun p => (rectTerms p.1).left (p.2.1,⟨2*p.2.2.1.val+p.2.2.2.val,by omega⟩)),
   store _ (fun p => (rectTerms p.1).middle (p.2.1,⟨3*p.2.2.1.val+p.2.2.2.val,by omega⟩)),
   store _ (fun p => (rectTerms p.1).right (p.2.1,⟨3*p.2.2.2.val+p.2.2.1.val,by omega⟩))⟩

private def checkMatrix (k : ℕ) (seed : ℤ) : IO Nat := do
  let lx := BinaryMatrixPowers.matrixLayout 2 (fin 2) (fin 2) k
  let ly := BinaryMatrixPowers.matrixLayout 2 (fin 2) (fin 3) k
  let lz := BinaryMatrixPowers.matrixLayout 2 (fin 3) (fin 2) k
  let x := store lx (fun p => (BinaryMultiplierAdapter.encodeInteger (seed+3*(lx.index p).val-4)).value)
  let y := store ly (fun p => (BinaryMultiplierAdapter.encodeInteger (2*seed-2*(ly.index p).val+7)).value)
  let got := BinaryMatrixPowers.execute (fin 2) (fin 2) (fin 3) (by decide) matrixBase k x y
  for slot in List.finRange lz.size do
    let z := lz.index.symm slot
    let expected := ∑ v : PowerIndex (Fin 2) k,
      BinaryCell.view (read x (z.1,(z.2.2,v)))*BinaryCell.view (read y (z.1,(v,z.2.1)))
    unless BinaryCell.view (read got.value z) == expected do
      throw (IO.userError "Ordinary matrix adapter differs from direct row/column product")
  IO.println s!"PASS: matrix coordinates, depth {k}, seed {seed}, {lz.size} output entries."
  return lz.size

def main : IO Unit := do
  let mut checked := 0
  for k in List.range 4 do
    for seed in ([0,3,-65537] : List ℤ) do
      checked := checked + (← check "rational dot/incomplete batch" (fromTerms dotTerms)
        (fun i j _ => if i=j then 1 else 0) k seed)
  for k in List.range 3 do
    for seed in ([2,-3] : List ℤ) do
      checked := checked + (← check "rectangular/multiple outputs" (fromTerms rectTerms)
        (fun i j z => if i.val/2=z.val/3 ∧ i.val%2=j.val/3 ∧ j.val%3=z.val%3 then 1 else 0) k seed)
    checked := checked + (← check "empty rank/zero tensor"
      (fromTerms (r:=0) (i:=2) (j:=3) (o:=1) (fun s => Fin.elim0 s))
      (fun _ _ _ => 0) k 0)
  IO.println s!"PASS: {checked} outputs checked against independent dense tensors, including zero rank, signed rational bases, incomplete batches and the 16-bit boundary."
  let mut matrixChecked := 0
  for k in List.range 3 do
    for seed in ([2,-3] : List ℤ) do
      matrixChecked := matrixChecked + (← checkMatrix k seed)
  IO.println s!"PASS: {matrixChecked} ordinary matrix output entries after the executable coordinate adapters."
  IO.println "SCOPE: bounded runtime fixtures for the retained arithmetic and binary programs; full APSP execution costs remain separate."
