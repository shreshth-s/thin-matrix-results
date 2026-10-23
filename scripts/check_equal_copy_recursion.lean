import CWRectangularRanks
import CWFiniteKeys

open ThinMatrix FiniteTrilinear FiniteDirectSum PolynomialDegeneration EqualCopyRecursion
open scoped BigOperators

private def weights : Fin 4 → ℚ := ![2/3,-5/7,3/11,-11/13]

/-- Two independent length-two dot products and an unused fifth term. -/
private def base (j : Fin 5) : Term (Fin 2×Fin 2) (Fin 2×Fin 2) (Fin 2×Fin 1) ℚ :=
  if h : j.val<4 then
    let p : Fin 4 := ⟨j.val,h⟩
    ⟨fun x => if x.1.val=j.val/2 ∧ x.2.val=j.val%2 then weights p else 0,
     fun y => if y.1.val=j.val/2 ∧ y.2.val=j.val%2 then (weights p)⁻¹ else 0,
     fun z => if z.1.val=j.val/2 then 1 else 0⟩
  else ⟨fun _ => 0,fun _ => 0,fun _ => 0⟩

private def budgetKeys : (k : ℕ) → List (Budget 5 2 k)
  | 0 => List.finRange 2
  | k+1 => (List.finRange 3).flatMap (fun g => (budgetKeys k).map (fun j => (g,j)))

private def inputValue : (k : ℕ) → PowerIndex (Fin 2) k → ℤ
  | 0,_ => 1
  | k+1,(i,x) => 3*inputValue k x+(i.val:ℤ)-2

private def checkLevel (k : ℕ) : IO Unit := do
  let xs := CWFiniteKeys.keys (List.finRange 2) k
  let zs := CWFiniteKeys.keys (List.finRange 1) k
  let jobs := budgetKeys k
  unless jobs.length == 2*3^k do throw (IO.userError "Recursive term count mismatch")
  let d := FiniteRationalCoefficients.denominator base
  let H := FiniteRationalCoefficients.height base
  let mut checked := 0
  for j in jobs do
    let a := terms (by decide : 0<2) base k j
    for c in List.finRange 2 do
      for x in xs do
        for v in [a.left (c,x),a.middle (c,x)] do
          unless (d^k)%v.den == 0 && |v| ≤ (5*H)^k do
            throw (IO.userError "Coefficient height/common denominator mismatch")
          checked := checked+1
      for z in zs do
        let v := a.right (c,z)
        unless (d^k)%v.den == 0 && |v| ≤ (5*H)^k do
          throw (IO.userError "Output coefficient height/common denominator mismatch")
        checked := checked+1
  for seed in List.range 3 do
    let x (c : Fin 2) (v : PowerIndex (Fin 2) k) : ℚ :=
      inputValue k v+(seed:ℤ)-2*(c.val:ℤ)
    let y (c : Fin 2) (v : PowerIndex (Fin 2) k) : ℚ :=
      2*inputValue k v-(seed:ℤ)+(c.val:ℤ)
    let products := jobs.map (fun j =>
      let a := terms (by decide : 0<2) base k j
      let left := ((List.finRange 2).flatMap (fun c => xs.map (fun v => a.left (c,v)*x c v))).sum
      let right := ((List.finRange 2).flatMap (fun c => xs.map (fun v => a.middle (c,v)*y c v))).sum
      (j,left*right))
    for c in List.finRange 2 do
      for z in zs do
        let got := (products.map (fun p => (terms (by decide : 0<2) base k p.1).right (c,z)*p.2)).sum
        let expected := (xs.map (fun v => x c v*y c v)).sum
        unless got == expected do throw (IO.userError "Recursive simultaneous product mismatch")
  IO.println s!"PASS: depth {k}, {jobs.length} terms, {checked} coefficient checks, six independent dot products."

private def checkRouting : IO Unit := do
  let mut checked := 0
  for r in List.range 24 do
    for t0 in List.range 7 do
      let t := t0+1
      let routes := (List.finRange r).map (slot r t (by omega))
      unless routes.eraseDups.length == r do throw (IO.userError "Padded routing collision")
      checked := checked+1
  IO.println s!"PASS: {checked} padded-routing cases, including empty and incomplete batches."

def main : IO Unit := do
  checkRouting
  for k in List.range 4 do checkLevel k
  IO.println "SCOPE: executes the coefficient recursion and exact bounded products; no binary multiplier or APSP runtime claim."
