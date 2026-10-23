import BinaryPowerAddress
open ThinMatrix PolynomialDegeneration RecursiveTable

private def checkPower (q k : Nat) (hq : 0 < q) : IO Nat := do
  let layout := power (fin q) k
  for i in List.finRange (q^k) do
    let word := BinaryPowerAddress.unrank q hq k i
    let address := BinaryPowerAddress.rank q k word.value
    unless address.value == i.val do
      throw (IO.userError "Binary tensor address failed round trip")
    unless (layout.index word.value).val == i.val do
      throw (IO.userError "Binary inverse disagrees with original tensor layout")
    let budget := 8192*(k+1)^2*(BinaryPowerAddress.width q k+1)^2
    unless word.bitSteps ≤ budget && address.bitSteps ≤ budget do
      throw (IO.userError "Binary tensor address exceeds its proved bound")
  IO.println s!"PASS: radix {q}, depth {k}; {q^k} complete forward/inverse addresses and budgets."
  return q^k

private def checkShape (q D : Nat) (hq : 2 ≤ q) (hD : 0 < D) : IO Unit := do
  let out := BinaryMatrixSetup.select q D
  let mut power := 1
  let mut depth := 0
  while power ≤ D do
    power := power*q
    depth := depth+1
  unless out.value == (power,depth) do
    throw (IO.userError "Binary depth selection disagrees with independent next-power loop")
  unless out.operations ≤ 1400*(D.size+3)*(q.size+D.size+6)^2 do
    throw (IO.userError "Binary depth selection exceeds proved budget")
  -- Exercise theorem-instantiated public hypotheses as well as the independent loop.
  let _ := BinaryMatrixSetup.select_bounds q D hq hD
  IO.println s!"PASS: base {q}, middle dimension {D}, selected depth {out.value.2}; binary setup budget."

def main : IO Unit := do
  let mut checked := 0
  for q in ([1,2,3,6] : List Nat) do
    if hq : 0 < q then
      for k in [0,1,2,3] do
        checked := checked + (← checkPower q k hq)
  for q in ([2,3,16] : List Nat) do
    if hq : 2 ≤ q then
      for D in ([1,2,3,4,15,16,17,65535,65536,65537] : List Nat) do
        if hD : 0 < D then checkShape q D hq hD
  for n in ([1,2,3,17,65536,65537] : List Nat) do
    for high in [0,1,2,65535,65536] do
      for low in [0,1,n-1] do
        let out := BinaryMatrixAddress.join n high low
        let cut := BinaryMatrixAddress.split n out.value
        unless out.value == low+n*high do throw (IO.userError "Product address is incorrect")
        unless cut.value == (out.value/n,out.value%n) do throw (IO.userError "Inverse product address is incorrect")
  IO.println s!"PASS: {checked} tensor addresses; 30 depth selections; 90 product/inverse checks."
  IO.println "SCOPE: these are setup/address routines, not the full APSP theorem or complete evaluator address integration."
