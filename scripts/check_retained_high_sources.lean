import GraphHighPreparation
open ThinMatrix
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace RetainedHighFixture
/-- Independent literal coefficient tables and raw-word enumeration. -/
def referenceNormal (row col : Nat) : Int :=
  ([[1,0,0,1],[1,0,0,0],[0,1,0,-1],[0,1,0,0],[-1,-1,1,0]].getD row []).getD col 0

def referenceOpposite (row col : Nat) : Int :=
  ([[1,1,0],[1,-1,0],[1,1,-1],[1,-1,1],[2,0,0]].getD row []).getD col 0

def digit (base code position : Nat) : Nat := code/base^position%base

def sourceValue {L : Nat} (seed A : Nat) (normal : Fin L → WalshEmbedding.NormalLetter)
    (opposite : Fin L → WalshEmbedding.OppositeLetter) (r : Nat) : Int :=
  let h := (List.ofFn (fun i : Fin L => (i.val+1)*(SourceFormation.normalIndex (normal i)).val+
    (i.val+3)*(SourceFormation.oppositeIndex (opposite i)).val)).sum+seed+r
  if h%3=0 then (A : Int) else if h%3=1 then -(A : Int) else 0

def rawFixture (L q seed A : Nat) : BinarySourceFormation.RawStore L q :=
  (BinarySourceFormation.rawBuild fun normal opposite =>
    ⟨Vector.ofFn (fun r => (BinaryMultiplierAdapter.encodeInteger (sourceValue seed A normal opposite r.val)).value),0⟩).value

def directLeaf (L q cap seed A : Nat) (side : Bool) (key : ArrayKeys.Key (2*L)) : Vector Int q :=
  Vector.ofFn fun r => ((List.range (4^L)).map fun nc =>
    ((List.range (3^L)).map fun oc =>
      let normal := fun i : Fin L => SourceFormation.indexNormal ⟨digit 4 nc i.val,Nat.mod_lt _ (by decide)⟩
      let opposite := fun i : Fin L => SourceFormation.indexOpposite ⟨digit 3 oc i.val,Nat.mod_lt _ (by decide)⟩
      let weight := ((List.range L).filter fun i => digit 3 oc i==2).length
      if weight≤cap then sourceValue seed A normal opposite r.val *
        ((List.finRange (2*L)).map fun i =>
          let normalHere := if i.val<L then side else !side
          let j := i.val%L
          if normalHere then referenceNormal (key.get i).val (digit 4 nc j)
          else referenceOpposite (key.get i).val (digit 3 oc j)).prod
      else 0).sum).sum

def wordKeys (L alphabet : Nat) (h : alphabet≤6) (hp : 0<alphabet) : List (ArrayKeys.Key (2*L)) :=
  (List.range (alphabet^(2*L))).map fun code => Vector.ofFn fun i =>
    ⟨digit alphabet code i.val,(Nat.mod_lt _ hp).trans_le h⟩



def family (L q seed A : Nat) : ExactHalfBandSources.Families L 0 q :=
  Vector.ofFn fun _ => Vector.ofFn fun _ =>
    (Vector.ofFn (fun _ => rawFixture L q seed A),Vector.ofFn (fun _ => rawFixture L q (seed+7) A))

def checkBank (L q : Nat) : IO Nat := do
  let sources : Vector (ExactHalfBandSources.Families L 0 q) 3 := Vector.ofFn fun i => family L q (i.val*3) 2
  let out := RetainedHighSources.bank 0 0 sources
  let u : Fin (ExactHalfSourcePlan.J 0) := ⟨0,ExactHalfCroppedEmbedding.shifts_nonempty 0⟩
  let run : Fin 1 := ⟨0,by decide⟩
  let mut checks := 0
  let mut directWork := 0
  for i in List.finRange 3 do
    for side in [false,true] do
      let stored := (((if side then (out.value.get i).2 else (out.value.get i).1).get u).get u).get run
      let seed := i.val*3+(if side then 7 else 0)
      let direct := BinaryCroppedHighEncoder.execute L 0 0 q 0 (!side) (rawFixture L q seed 2)
      directWork := directWork+direct.bitSteps
      if stored.bitSteps != direct.bitSteps then throw (IO.userError "retained HIGH encoder work changed")
      let keys := (wordKeys L 5 (by decide) (by decide)).filter fun k => (ArrayKeys.baseTest L 0 0 k).1
      for key in keys do
        let values := (BinaryHighExecution.readBase stored key).value
        let expected := directLeaf L q 0 seed 2 (!side) key
        for r in List.finRange q do
          if (values.get r).view != expected.get r then throw (IO.userError "retained HIGH encoder coefficient mismatch")
          checks := checks+1
  if out.operations != directWork+240 then throw (IO.userError "retained HIGH bank loop cost mismatch")
  return checks

def main : IO Unit := do
  let mut checks := 0
  for L in [0,1,2] do
    for q in [1,3,8] do
      checks := checks+(← checkBank L q)
  IO.println s!"PASS {checks} retained HIGH bank coefficients against independent raw-word contractions"
  IO.println "PASS three distinct source bands, both orientations, q=1,3,8, L=0,1,2, crop-before-encode, and exact bank loop cost"
end RetainedHighFixture

def main := RetainedHighFixture.main
