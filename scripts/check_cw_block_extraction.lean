import CWExtractionExample
import CWCanonicalType

open ThinMatrix PolynomialDegeneration CWPolynomialCertificate CWSixBlocks CWBlockWords
open CWExtractionExample CWIsolatedCandidates

private def xaxis (copy : Bool) (r b : Fin 2) : PowerIndex (Axis 2) 3 :=
  if copy then leftWord 2 3 second ((PUnit.unit,(PUnit.unit,(r,PUnit.unit))),(b,(PUnit.unit,(PUnit.unit,PUnit.unit))))
  else leftWord 2 3 reference ((PUnit.unit,(r,(PUnit.unit,PUnit.unit))),(PUnit.unit,(PUnit.unit,(b,PUnit.unit))))
private def yaxis (copy : Bool) (b c : Fin 2) : PowerIndex (Axis 2) 3 :=
  if copy then middleWord 2 3 second ((b,(PUnit.unit,(PUnit.unit,PUnit.unit))),(PUnit.unit,(c,(PUnit.unit,PUnit.unit))))
  else middleWord 2 3 reference ((PUnit.unit,(PUnit.unit,(b,PUnit.unit))),(c,(PUnit.unit,(PUnit.unit,PUnit.unit))))
private def zaxis (copy : Bool) (c r : Fin 2) : PowerIndex (Axis 2) 3 :=
  if copy then rightWord 2 3 second ((PUnit.unit,(c,(PUnit.unit,PUnit.unit))),(PUnit.unit,(PUnit.unit,(r,PUnit.unit))))
  else rightWord 2 3 reference ((c,(PUnit.unit,(PUnit.unit,PUnit.unit))),(PUnit.unit,(r,(PUnit.unit,PUnit.unit))))

def main : IO Unit := do
  let E := candidates 3 reference X Y Z
  let S := selected 3 reference X Y Z
  unless E == {reference,second} && S == E && S.card == 2 do
    throw (IO.userError "Actual hash selection or cleanup differs from independent two-copy fixture")
  IO.println "PASS: actual mod-7 candidate construction and collision cleanup retain exactly two copies."
  let indices := [false,true].flatMap fun c => (List.ofFn (id : Fin 2 → Fin 2)).flatMap fun i =>
    (List.ofFn (id : Fin 2 → Fin 2)).map fun j => (c,i,j)
  let mut checked := 0
  for a in indices do
    for b in indices do
      for c in indices do
        let actual := tensorPower (target (R:=Int) 2) 3 (xaxis a.1 a.2.1 a.2.2)
          (yaxis b.1 b.2.1 b.2.2) (zaxis c.1 c.2.1 c.2.2)
        let expected : Int := if a.1 == b.1 && a.1 == c.1 && a.2.1 == c.2.2 &&
          a.2.2 == b.2.1 && b.2.2 == c.2.1 then 1 else 0
        unless actual == expected do throw (IO.userError "Mixed coordinate tensor mismatch")
        checked := checked+1
  IO.println s!"PASS: {checked} actual word-embedding coordinates equal the independently computed direct-sum tensor."
  let zero := selected 0 PUnit.unit {PUnit.unit} {PUnit.unit} {PUnit.unit}
  let empty := selected 0 PUnit.unit ∅ {PUnit.unit} {PUnit.unit}
  unless zero.card == 1 && empty.card == 0 do throw (IO.userError "Zero/empty selection mismatch")
  IO.println "PASS: zero tensor power retains one scalar; empty coordinate restriction retains no copy."
  IO.println "SCOPE: bounded executable finite isolation; generic exact decomposition is kernel-checked separately."
