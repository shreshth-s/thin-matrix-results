import BinaryAddressedRecursion
open ThinMatrix RecursiveTable PolynomialDegeneration

private def base (r t a b c : Nat) : RetainedEqualCopy.Base r t (prod (fin a) (fin b))
    (prod (fin b) (fin c)) (prod (fin c) (fin a)) BinaryCell.Cell :=
  ⟨store _ (fun p => (BinaryMultiplierAdapter.encodeInteger ((p.1.val:Int)-2*p.2.1.val+3*p.2.2.1.val-p.2.2.2.val)).value),
   store _ (fun p => (BinaryMultiplierAdapter.encodeInteger (2*(p.1.val:Int)+p.2.1.val-p.2.2.1.val+5*p.2.2.2.val)).value),
   store _ (fun p => (BinaryMultiplierAdapter.encodeInteger (-(p.1.val:Int)+4*p.2.1.val+p.2.2.1.val-p.2.2.2.val)).value)⟩

private def check (r t a b c k : Nat) (seed : Int) : IO Nat := do
  if ht : 0<t then
    if ha : 0<a then
      if hb : 0<b then
        if hc : 0<c then
          let x := store (BinaryRecursiveTable.layout t a b k) (fun p =>
            (BinaryMultiplierAdapter.encodeInteger (seed+2*((BinaryRecursiveTable.layout t a b k).index p).val)).value)
          let y := store (BinaryRecursiveTable.layout t b c k) (fun p =>
            (BinaryMultiplierAdapter.encodeInteger (seed-3*((BinaryRecursiveTable.layout t b c k).index p).val)).value)
          let d := base r t a b c
          let out := BinaryAddressedRecursion.run ha hb hc ht d k x y
          let old := BinaryRetainedEqualCopy.run (prod (fin a) (fin b)) (prod (fin b) (fin c))
            (prod (fin c) (fin a)) ht d k x y
          unless out.value.toList.map BinaryCell.view == old.value.toList.map BinaryCell.view do
            throw (IO.userError "Binary recursive addresses changed output")
          unless old.bitSteps≤out.bitSteps do throw (IO.userError "Missing scalar bit work")
          IO.println s!"PASS: rank={r}, copies={t}, dimensions={a}x{b}x{c}, depth={k}, seed={seed}; {out.value.size} cells, {out.bitSteps-old.bitSteps} binary address steps."
          return out.value.size
  throw (IO.userError "Invalid fixture")

def main : IO Unit := do
  let mut total := 0
  for dims in ([(0,1,1,1,1,0),(0,1,2,1,3,1),(1,2,1,2,1,1),
      (5,2,2,1,2,1),(5,2,2,1,2,2),(3,2,1,2,3,2),(9,1,2,2,2,2)] :
      List (Nat×Nat×Nat×Nat×Nat×Nat)) do
    for seed in ([-11,65537] : List Int) do
      total := total+(←check dims.1 dims.2.1 dims.2.2.1 dims.2.2.2.1 dims.2.2.2.2.1 dims.2.2.2.2.2 seed)
  IO.println s!"PASS: {total} binary-addressed recursive output cells, signed values, zero rank, incomplete final child group, and asymmetric matrix dimensions."
