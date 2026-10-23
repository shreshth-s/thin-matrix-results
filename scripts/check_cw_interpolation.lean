import CWExactDecomposition
import CWInterpolationWidths

/-! Bounded executable tests. Independent Horner evaluation and direct CW
contraction, not the semantic polynomial definitions used by the proofs. -/
open ThinMatrix CWPowerSpecialization CWFiniteKeys CWInterpolationProgram
open IntegerInterpolationWeights IntegerCoefficientExtraction

private def horner (xs : List ℤ) (t : ℤ) : ℤ := xs.foldr (fun a b => a+t*b) 0

private def checkInterpolation (d : ℕ) : IO Unit := do
  let coeff : Vector ℤ (d+1) := Vector.ofFn (fun i => if i.val%2=0 then i.val+1 else -(i.val+1:ℤ))
  let values := Vector.ofFn (fun i : Fin (d+1) => horner coeff.toList i.val)
  for k in List.ofFn (id : Fin (d+1) → Fin (d+1)) do
    let table := prepare d k
    let r := applyTable table values
    unless r.denominator != 0 && r.numerator == r.denominator*coeff.get k do
      throw (IO.userError s!"interpolation failed d={d}, k={k.val}")
    unless table.operations ≤ CWInterpolationCosts.setupWork d do
      throw (IO.userError "setup charge bound failed")
    for i in List.ofFn (id : Fin (d+1) → Fin (d+1)) do
      unless (table.weights.get i).natAbs.size ≤ bitEnvelope d do
        throw (IO.userError "weight bit bound failed")
  IO.println s!"PASS: d={d}: all {d+1} coefficients recovered exactly by the retained integer table."

private def label : CWPolynomialCertificate.Axis 16 → ℕ
  | none => 0
  | some none => 17
  | some (some i) => i.val+1

private def direct (x y : ℕ → ℤ) (k : ℕ) : ℤ :=
  if k=0 then ((List.range 16).map (fun i => x (i+1)*y (i+1))).sum+x 17*y 0+x 0*y 17
  else if k=17 then x 0*y 0 else x 0*y k+x k*y 0

private def checkCW (mode : ℕ) : IO Unit := do
  let x : ℕ → ℤ := fun i => if mode=0 then (i:ℤ)-8 else if mode=1 then (if i=0 then 1 else 0) else (i%3:ℤ)-1
  let y : ℕ → ℤ := fun i => if mode=0 then 3-(i:ℤ) else if mode=1 then (if i=17 then -7 else 0) else 2-(i%5:ℤ)
  let out := execute 1 (fun i => x (label i.1)) (fun i => y (label i.1))
  unless out.retainedProducts.length=198 && out.outputs.length=18 && out.operations≤CWInterpolationCosts.workBound 1 do
    throw (IO.userError "CW layout or charge bound failed")
  for o in out.outputs do
    unless o.quotient == direct x y (label o.key.1) && o.numerator == out.table.denominator*o.quotient do
      throw (IO.userError s!"CW output mismatch mode={mode}, label={label o.key.1}")
  IO.println s!"PASS: CW n=1 mode={mode}: 198 retained products and all 18 outputs match direct contraction; {out.operations} arithmetic operations."

def main : IO Unit := do
  for d in [0,1,2,3,10,20] do checkInterpolation d
  let zero := execute 0 (fun _ => -7) (fun _ => 11)
  unless zero.table.denominator=1 && zero.outputs.length=1 && zero.outputs.all (fun o => o.quotient == -77) do
    throw (IO.userError "zero tensor power failed")
  IO.println "PASS: n=0 executes the scalar product with denominator 1 and one output."
  for mode in [0,1,2] do checkCW mode
  IO.println "PASS: bounded integer interpolation and exact CW execution; no large tensor-power or graph/FFT runtime claim."
