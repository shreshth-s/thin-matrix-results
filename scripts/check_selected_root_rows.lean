import SelectedRootRows
open ThinMatrix BinaryCell BinaryResidualPolynomial

private def number (seed : Int) (d r : Nat) : Int :=
  let z := seed+(d:Int)*3+(r:Int)*5
  if (d+r)%3=0 then z else if (d+r)%3=1 then -z else 0

private def make (F q : Nat) (seed : Int) : Block F q :=
  Vector.ofFn (fun d => Vector.ofFn (fun r =>
    (BinaryMultiplierAdapter.encodeInteger (number seed d.val r.val)).value))

private def naive (F q t card r : Nat) (wa : Nat → Int) (a b : Nat → Nat → Int) : Int := Id.run do
  let mut out := 0
  for d in List.range t do
    if card≤d then
      for d1 in List.range F do
        for d2 in List.range F do
          if d1+d2=d-card then
            for r1 in List.range q do
              for r2 in List.range q do
                if (r1+r2)%q=r then
                  out := out+wa d*a d1 r1*b d2 r2
  return out

private def ensure (ok : Bool) (message : String) : IO Unit :=
  if ok then pure () else throw (IO.userError message)

private def checkCore (F q t card B M : Nat) [NeZero q] (seed : Int) : IO Nat := do
  let leftValue := fun (j b d r : Nat) => number (seed+(j:Int)*13+(b:Int)*17) d r
  let rightValue := fun (j b d r : Nat) => number (-seed-2-(j:Int)*11+(b:Int)*7) d r
  let left : Vector (Vector Cell (B*(F*q))) M := Vector.ofFn (fun j => Vector.ofFn (fun col =>
    let bc : Fin B × Fin (F*q) := finProdFinEquiv.symm col
    let dr : Fin F × Fin q := finProdFinEquiv.symm bc.2
    (BinaryMultiplierAdapter.encodeInteger (leftValue j.val bc.1.val dr.1.val dr.2.val)).value))
  let right : Vector (Vector Cell (B*(F*q))) M := Vector.ofFn (fun j => Vector.ofFn (fun col =>
    let bc : Fin B × Fin (F*q) := finProdFinEquiv.symm col
    let dr : Fin F × Fin q := finProdFinEquiv.symm bc.2
    (BinaryMultiplierAdapter.encodeInteger (rightValue j.val bc.1.val dr.1.val dr.2.val)).value))
  let ws : Vector Cell t := Vector.ofFn (fun d => (BinaryMultiplierAdapter.encodeInteger (number 7 d.val 0)).value)
  let residues : Vector (Fin q) M := Vector.ofFn (fun j => ⟨(2*j.val+1)%q,Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne q))⟩)
  let out := SelectedRootRows.execute ws left right card residues
  let A := seed.natAbs+2+13*M+17*B+3*F+5*q
  let W := 7+3*t
  ensure (decide (out.bitSteps≤M*(B*SelectedRootProduct.bitBudget q t W A))) "Root row bit budget exceeded"
  ensure (decide (out.control≤SelectedRootRows.controlBudget F q t B M)) "Root row control budget exceeded"
  for j in List.finRange M do
    for b in List.finRange B do
      let reference := naive F q t card (residues.get j).val (fun d => number 7 d 0) (leftValue j.val b.val) (rightValue j.val b.val)
      ensure (decide (view ((out.value.get j).get b)=reference)) "Root row block/coefficient mismatch"
  return M*B

private def check (F q t card B M : Nat) (seed : Int) : IO Nat := do
  if hq : 0<q then
    letI : NeZero q := ⟨Nat.ne_of_gt hq⟩
    checkCore F q t card B M seed
  else throw (IO.userError "Zero cyclic length")

def main : IO Unit := do
  let mut checked := 0
  for seed in ([-7,65537] : List Int) do
    for F in [0,1,3] do
      for q in [1,3,5] do
        for B in [0,1,3] do
          for M in [0,2,4] do
            for card in [0,1,7] do
              checked := checked+(← check F q 4 card B M seed)
  IO.println s!"PASS: {checked} selected scalar outputs with occurrence/block/formal-degree/cyclic indexing against independent signed convolution; requested residues vary, empty axes and both cost counters checked."
  IO.println "SCOPE: retained root row contraction; full APSP caller connection remains open."
