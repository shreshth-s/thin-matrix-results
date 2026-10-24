import BinaryAddressedUniform

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 5000
set_option backward.isDefEq.respectTransparency false

/-! Padding directly into paired tensor words, avoiding an intermediate
matrix-word reshape. All data-dependent address ranks and boundary tests are
binary computations whose outputs select the retained cell. -/
namespace ThinMatrix.BinaryAddressedPadding
open scoped BigOperators
open BinaryCell BinaryGroupedCoordinates
open RecursiveTable (Table prod fin power)
open PolynomialDegeneration RetainedEqualCopy
open BinaryAddressedRecursion
variable {a b c t n m p : ℕ}

def padEntry (k : ℕ) (x : Table (PaddedMatrix.matrix n m) Cell)
    (z : Fin t×PowerIndex (Fin a×Fin b) k) : Run Cell :=
  let coordinates := MatrixPowerReindex.unpair k z.2
  let row := BinaryPowerAddress.rank a k coordinates.1
  let col := BinaryPowerAddress.rank b k coordinates.2
  let first := BinaryChunkAddress.less z.1.val 1
  let rowFits := BinaryChunkAddress.less row.value n
  let colFits := BinaryChunkAddress.less col.value m
  let setup := row.bitSteps+col.bitSteps+first.bitSteps+rowFits.bitSteps+colFits.bitSteps+8*(k+1)
  if _h0 : first.value=true then
    if hi : rowFits.value=true then
      if hj : colFits.value=true then
        let input := BinaryChunkAddress.matrixRead x
          ⟨row.value,(BinaryChunkAddress.less_true _ _).mp hi⟩
          ⟨col.value,(BinaryChunkAddress.less_true _ _).mp hj⟩
        ⟨input.value,setup+input.bitSteps,24+8*(k+1)⟩
      else ⟨zero,setup,24+8*(k+1)⟩
    else ⟨zero,setup,24+8*(k+1)⟩
  else ⟨zero,setup,24+8*(k+1)⟩

def pad (ha : 0<a) (hb : 0<b) (k : ℕ) (x : Table (PaddedMatrix.matrix n m) Cell) : Run (Cells t a b k) :=
  BinaryRecursiveTable.tabulate ha hb k (padEntry k x)

theorem padEntry_value (k : ℕ) (x : Table (PaddedMatrix.matrix n m) Cell)
    (z : Fin t×PowerIndex (Fin a×Fin b) k) :
    (padEntry k x z).value=RecursiveTable.read
      (PaddedMatrix.pad (power (fin a) k) (power (fin b) k) t n m x).value
      (z.1,MatrixPowerReindex.unpair k z.2) := by
  simp only [padEntry,PaddedMatrix.pad_value]
  have h0 : (BinaryChunkAddress.less z.1.val 1).value=true ↔ z.1.val=0 := by
    rw [BinaryChunkAddress.less_true];omega
  simp only [h0,BinaryChunkAddress.less_true,BinaryPowerAddress.rank_value]
  split_ifs <;> try rfl
  rw [BinaryChunkAddress.matrixRead_value]

theorem pad_value (ha : 0<a) (hb : 0<b) (k : ℕ) (x : Table (PaddedMatrix.matrix n m) Cell) :
    (pad (t:=t) ha hb k x).value=
      (BinaryMatrixPowers.toWords (fin a) (fin b) k
        (PaddedMatrix.pad (power (fin a) k) (power (fin b) k) t n m x).value).value := by
  apply table_ext (BinaryRecursiveTable.layout t a b k)
  intro z
  simp only [pad,BinaryRecursiveTable.tabulate_read,padEntry_value,
    BinaryMatrixPowers.toWords,BinaryRecursiveDot.tabulate_read]

def cropEntry (ha : 0<a) (hc : 0<c) (ht : 0<t) (k : ℕ)
    (hn : n≤a^k) (hp : p≤c^k) (x : Cells t c a k) (i : Fin (n*p)) : Run Cell :=
  have hpos : 0<p := by nlinarith [i.isLt]
  let coordinate := BinaryMatrixAddress.split p i.val
  have hv := BinaryMatrixAddress.split_value p i.val hpos
  let row : Fin n := ⟨coordinate.value.1,by rw [hv];exact (Nat.div_lt_iff_lt_mul hpos).mpr i.isLt⟩
  let col : Fin p := ⟨coordinate.value.2,by rw [hv];exact Nat.mod_lt _ hpos⟩
  let rwrd := BinaryPowerAddress.unrank a ha k ⟨row.val,row.isLt.trans_le hn⟩
  let cwrd := BinaryPowerAddress.unrank c hc k ⟨col.val,col.isLt.trans_le hp⟩
  let output := BinaryRecursiveTable.read k x (⟨0,ht⟩,FiniteMatrixPowers.pair k (cwrd.value,rwrd.value))
  ⟨output.value,coordinate.bitSteps+rwrd.bitSteps+cwrd.bitSteps+output.bitSteps+8*(k+1),24+8*(k+1)⟩

def crop (ha : 0<a) (hc : 0<c) (ht : 0<t) (k : ℕ)
    (hn : n≤a^k) (hp : p≤c^k) (x : Cells t c a k) : Run (Table (PaddedMatrix.matrix n p) Cell) :=
  let rows := Vector.ofFn (cropEntry ha hc ht k hn hp x)
  ⟨rows.map Run.value,(rows.toList.map Run.bitSteps).sum,(rows.toList.map Run.control).sum+32*(n*p)+8⟩

theorem cropEntry_value (ha : 0<a) (hc : 0<c) (ht : 0<t) (k : ℕ)
    (hn : n≤a^k) (hp : p≤c^k) (x : Cells t c a k) (i : Fin n×Fin p) :
    (cropEntry ha hc ht k hn hp x (finProdFinEquiv i)).value=
      RecursiveTable.read x (⟨0,ht⟩,FiniteMatrixPowers.pair k
        (PaddedMatrix.embed (power (fin c) k) (by simpa only [RecursiveTable.power_size,fin] using hp) i.2,
         PaddedMatrix.embed (power (fin a) k) (by simpa only [RecursiveTable.power_size,fin] using hn) i.1)) := by
  have hp0 : 0<p := (Nat.zero_le _).trans_lt i.2.isLt
  have split : (BinaryMatrixAddress.split p (finProdFinEquiv i).val).value=(i.1.val,i.2.val) := by
    rw [BinaryMatrixAddress.split_value _ _ hp0]
    exact congrArg (fun v : Fin n×Fin p => (v.1.val,v.2.val)) (finProdFinEquiv.symm_apply_apply i)
  simp only [cropEntry,BinaryRecursiveTable.read_value,BinaryPowerAddress.unrank_value,PaddedMatrix.embed]
  apply congrArg (fun q => RecursiveTable.read x (⟨0,ht⟩,FiniteMatrixPowers.pair k q))
  apply Prod.ext
  · change (power (fin c) k).index.symm _=(power (fin c) k).index.symm _
    apply congrArg (power (fin c) k).index.symm
    apply Fin.ext
    exact congrArg Prod.snd split
  · change (power (fin a) k).index.symm _=(power (fin a) k).index.symm _
    apply congrArg (power (fin a) k).index.symm
    apply Fin.ext
    exact congrArg Prod.fst split

theorem crop_value (ha : 0<a) (hc : 0<c) (ht : 0<t) (k : ℕ)
    (hn : n≤a^k) (hp : p≤c^k) (x : Cells t c a k) :
    (crop ha hc ht k hn hp x).value=
      (PaddedMatrix.crop (power (fin a) k) (power (fin c) k) ht
        (by simpa only [RecursiveTable.power_size,fin] using hn) (by simpa only [RecursiveTable.power_size,fin] using hp)
        (BinaryMatrixPowers.fromWords (fin c) (fin a) k x).value).value := by
  apply table_ext (PaddedMatrix.matrix n p)
  intro i
  have hh := cropEntry_value ha hc ht k hn hp x i
  have hread : RecursiveTable.read (crop ha hc ht k hn hp x).value i=
      (cropEntry ha hc ht k hn hp x (finProdFinEquiv i)).value := by
    simp [crop,RecursiveTable.read,PaddedMatrix.matrix,prod,fin]
  rw [hread,PaddedMatrix.crop_value]
  change _=RecursiveTable.read
    (BinaryRecursiveDot.tabulate (prod (fin t) (prod (power (fin c) k) (power (fin a) k)))
      (fun q => (⟨RecursiveTable.read x (q.1,FiniteMatrixPowers.pair k q.2),0,8⟩ : Run Cell))).value _
  rw [BinaryRecursiveDot.tabulate_read]
  exact hh

#print axioms padEntry_value
#print axioms pad_value
#print axioms cropEntry_value
#print axioms crop_value
end ThinMatrix.BinaryAddressedPadding
