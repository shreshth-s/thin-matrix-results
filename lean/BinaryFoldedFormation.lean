import FoldedBackendExecution
import BinaryCell
import BinaryMultiplierAdapter
import GlobalAddressBitBounds
import AdaptiveQueryBitBounds
import BinaryModularCell
import FoldedFormationArithmetic

/-!
# Original-input encoding and binary folded coefficient formation

The original three integer tables are encoded once into stored binary
cells. Subsequent producers consume those cells, with integer views used
only in refinement proofs. Every padded cyclic coefficient slot is stored.
-/
namespace ThinMatrix.BinaryFoldedFormation
open scoped BigOperators
open BinaryCell StoredMinPlusAPSP
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

abbrev BinaryTable (n : ℕ) := Vector (Vector Cell n) n
abbrev Left (N D q : ℕ) := Vector (Vector Cell q) (N*D)
abbrev Right (N D q : ℕ) := Vector (Vector Cell q) (D*N)

def viewTable {n : ℕ} (a : BinaryTable n) : IntTable n :=
  a.map (fun row=>row.map BinaryCell.view)

def viewLeft {N D q : ℕ} (a : Left N D q) : ThinMatrixBackend.OriginalLeft N D q :=
  a.map (fun row=>row.map BinaryCell.view)

def viewRight {N D q : ℕ} (a : Right N D q) : ThinMatrixBackend.OriginalRight N D q :=
  a.map (fun row=>row.map BinaryCell.view)

/-- Each original stored scalar is visited once. The joint array retains
both its value and its returned serialization counter. -/
def encodeTable {n : ℕ} (a : IntTable n) : Result (BinaryTable n) :=
  let cells := Vector.ofFn (fun i : Fin n=>Vector.ofFn (fun j : Fin n=>
    BinaryMultiplierAdapter.encodeInteger ((a.get i).get j)))
  ⟨cells.map (fun row=>row.map (fun cell=>cell.value)),
    (∑ i : Fin n,∑ j : Fin n,((cells.get i).get j).bitSteps)+10*n^2*(n.size+1)⟩

theorem encodeTable_view {n : ℕ} (a : IntTable n) : viewTable (encodeTable a).value=a := by
  apply Vector.ext
  intro i hi
  apply Vector.ext
  intro j hj
  simp only [viewTable,encodeTable,Vector.getElem_map,Vector.getElem_ofFn]
  exact BinaryMultiplierAdapter.encodeInteger_view _

theorem encodeTable_get {n : ℕ} (a : IntTable n) (i j : Fin n) :
    BinaryCell.view (((encodeTable a).value.get i).get j)=decode a i j := by
  have h:=congrArg (fun table : IntTable n=>(table.get i).get j) (encodeTable_view a)
  simpa only [viewTable,Vector.get_map,decode] using h

theorem encodeTable_cost {n : ℕ} (a : IntTable n) (W : ℕ)
    (ha : ∀ i j, (decode a i j).natAbs.size ≤ W) :
    (encodeTable a).bitSteps ≤ 10*n^2*((W+1)^2+n.size+1) := by
  have hcell (i j : Fin n) :
      (BinaryMultiplierAdapter.encodeInteger ((a.get i).get j)).bitSteps ≤ 10*(W+1)^2 := by
    apply (BinaryMultiplierAdapter.encodeInteger_cost _).trans
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by simpa only [decode] using Nat.add_le_add_right (ha i j) 1) 2)
  have hsum := Finset.sum_le_sum (s:=Finset.univ) (fun i _=>
    Finset.sum_le_sum (s:=Finset.univ) (fun j _=>hcell i j))
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] at hsum
  simp only [encodeTable,Vector.get_ofFn]
  calc
    _ ≤ n*(n*(10*(W+1)^2))+10*n^2*(n.size+1) := Nat.add_le_add_right hsum _
    _ = _ := by ring

structure Inputs (n : ℕ) where
  left : BinaryTable n
  right : BinaryTable n
  target : BinaryTable n

/-- This boundary is evaluated once before candidate, restart, block and
coefficient loops. All later calls reuse its three stored tables. -/
def encodeInputs {n : ℕ} (A B T : IntTable n) : Result (Inputs n) :=
  let a:=encodeTable A
  let b:=encodeTable B
  let t:=encodeTable T
  ⟨⟨a.value,b.value,t.value⟩,a.bitSteps+b.bitSteps+t.bitSteps⟩

theorem encodeInputs_views {n : ℕ} (A B T : IntTable n) :
    viewTable (encodeInputs A B T).value.left=A ∧
    viewTable (encodeInputs A B T).value.right=B ∧
    viewTable (encodeInputs A B T).value.target=T :=
  ⟨encodeTable_view A,encodeTable_view B,encodeTable_view T⟩

theorem encodeInputs_cost {n : ℕ} (A B T : IntTable n) (W : ℕ)
    (hA : ∀ i j, (decode A i j).natAbs.size ≤ W)
    (hB : ∀ i j, (decode B i j).natAbs.size ≤ W)
    (hT : ∀ i j, (decode T i j).natAbs.size ≤ W) :
    (encodeInputs A B T).bitSteps ≤ 30*n^2*((W+1)^2+n.size+1) := by
  have ha:=encodeTable_cost A W hA
  have hb:=encodeTable_cost B W hB
  have ht:=encodeTable_cost T W hT
  simp only [encodeInputs]
  nlinarith

/-- Public bounded addresses are encoded through the counted boundary
serializer; a computed integer coefficient never enters this function. -/
def publicNat (n : ℕ) : Result Cell := BinaryMultiplierAdapter.encodeInteger (n:ℤ)
@[simp] theorem publicNat_view (n : ℕ) : BinaryCell.view (publicNat n).value=n :=
  BinaryMultiplierAdapter.encodeInteger_view _
theorem publicNat_cost (n : ℕ) : (publicNat n).bitSteps ≤ 10*(n.size+1)^2 := by
  simpa only [publicNat,Int.natAbs_natCast] using BinaryMultiplierAdapter.encodeInteger_cost (n:ℤ)

/-- This integer table lookup is a specification of the bounded stored
read below. It is not called by the binary source producer. -/
def nativeRead {n : ℕ} (a : IntTable n) (i j : ℕ) : ℤ :=
  if hi:i<n then if hj:j<n then decode a ⟨i,hi⟩ ⟨j,hj⟩ else 0 else 0

/-- Guarded original array reads inspect only bounded control addresses.
The returned payload is copied through the counted binary cell operation. -/
def readTable {n : ℕ} (a : BinaryTable n) (i j : ℕ) : Result Cell :=
  if hi:i<n then
    if hj:j<n then
      let copied:=BinaryCell.copy ((a.get ⟨i,hi⟩).get ⟨j,hj⟩)
      ⟨copied.value,copied.bitSteps+8*(i.size+j.size+n.size+1)⟩
    else ⟨BinaryCell.zero,8*(i.size+j.size+n.size+1)⟩
  else ⟨BinaryCell.zero,8*(i.size+j.size+n.size+1)⟩

theorem readTable_view {n : ℕ} (a : BinaryTable n) (i j : ℕ) :
    BinaryCell.view (readTable a i j).value=nativeRead (viewTable a) i j := by
  simp only [readTable,nativeRead]
  split_ifs <;> simp only [BinaryCell.copy_view,BinaryCell.zero_view,viewTable,decode,Vector.get_map]

theorem readTable_size {n : ℕ} (a : BinaryTable n) (W : ℕ)
    (ha : ∀ i j, (BinaryCell.view ((a.get i).get j)).natAbs.size ≤ W) (i j : ℕ) :
    (BinaryCell.view (readTable a i j).value).natAbs.size ≤ W := by
  unfold readTable
  split_ifs
  · simpa only [BinaryCell.copy_view] using ha _ _
  all_goals simp only [BinaryCell.zero_view,Int.natAbs_zero,Nat.size_zero]; omega

theorem readTable_cost {n : ℕ} (a : BinaryTable n) (W : ℕ)
    (ha : ∀ i j, (BinaryCell.view ((a.get i).get j)).natAbs.size ≤ W) (i j : ℕ) :
    (readTable a i j).bitSteps ≤ BackendScalarBits.backendScalarUnit W+8*(i.size+j.size+n.size+1) := by
  unfold readTable
  split_ifs
  · exact Nat.add_le_add_right (BinaryCell.copy_price W _ (ha _ _)) _
  all_goals dsimp only; omega

/-- Read-only binary copies of the public dimensions. The block offset is
formed by an actual binary multiplication, rather than a native product. -/
structure Geometry (n h d q block : ℕ) where
  nCell : Cell
  dCell : Cell
  qCell : Cell
  widthCell : Cell
  outerCell : Cell
  middleCell : Cell
  rawCell : Cell
  offsetCell : Cell
  n_view : view nCell=(n:ℤ)
  d_view : view dCell=(d:ℤ)
  q_view : view qCell=(q:ℤ)
  width_view : view widthCell=(FoldedCounts.foldWidth d:ℤ)
  outer_view : view outerCell=(FoldedBackendExecution.outerSize n d:ℤ)
  middle_view : view middleCell=(FoldedBackendExecution.middleSize h d:ℤ)
  raw_view : view rawCell=(FoldedBackendExecution.rawMiddle h d:ℤ)
  offset_view : view offsetCell=((block*h:ℕ):ℤ)

attribute [simp] Geometry.n_view Geometry.d_view Geometry.q_view Geometry.width_view
  Geometry.outer_view Geometry.middle_view Geometry.raw_view Geometry.offset_view

def makeGeometry (n h d q block : ℕ) : Result (Geometry n h d q block) :=
  let nc:=publicNat n
  let dc:=publicNat d
  let qc:=publicNat q
  let wc:=publicNat (FoldedCounts.foldWidth d)
  let oc:=publicNat (FoldedBackendExecution.outerSize n d)
  let mc:=publicNat (FoldedBackendExecution.middleSize h d)
  let rc:=publicNat (FoldedBackendExecution.rawMiddle h d)
  let bc:=publicNat block
  let hc:=publicNat h
  let offset:=BinaryCell.mul bc.value hc.value
  ⟨⟨nc.value,dc.value,qc.value,wc.value,oc.value,mc.value,rc.value,offset.value,
      publicNat_view _,publicNat_view _,publicNat_view _,publicNat_view _,publicNat_view _,
      publicNat_view _,publicNat_view _,by dsimp [offset,bc,hc]; simp only [BinaryCell.mul_view,publicNat_view]⟩,
    nc.bitSteps+dc.bitSteps+qc.bitSteps+wc.bitSteps+oc.bitSteps+mc.bitSteps+rc.bitSteps+
      bc.bitSteps+hc.bitSteps+offset.bitSteps+20⟩

structure Coordinates where
  original : ℕ
  label : ℕ
  sigma : Cell
  residue : Cell
  padded : Bool
  active : Bool

/-- Every quotient and remainder is computed by the binary modular
primitive. Only already stored bits are decoded into bounded read addresses. -/
def coordinates {n h d q block : ℕ} (right : Bool) (g : Geometry n h d q block)
    (address : ℕ) : Result Coordinates :=
  let addressCell:=publicNat address
  let flat:=BinaryModularCell.split (if right then g.outerCell else g.middleCell) addressCell.value
  let middle:=if right then flat.value.1 else flat.value.2
  let outer:=if right then flat.value.2 else flat.value.1
  let mid:=BinaryModularCell.split g.dCell middle
  let out:=BinaryModularCell.split g.widthCell outer
  let originalLabel:=BinaryCell.add g.offsetCell mid.value.1
  let original:=BinaryModularCell.decodeUnsigned out.value.1
  let label:=BinaryModularCell.decodeUnsigned originalLabel.value
  let padded:=BinaryModularCell.lessUnsigned middle g.rawCell
  let active:=BinaryModularCell.lessUnsigned originalLabel.value g.nCell
  ⟨⟨original.value,label.value,mid.value.2,out.value.2,padded.value,active.value⟩,
    addressCell.bitSteps+flat.bitSteps+mid.bitSteps+out.bitSteps+originalLabel.bitSteps+
      original.bitSteps+label.bitSteps+padded.bitSteps+active.bitSteps+20*(address.size+1)⟩

/-- Proof-only natural coordinates of the same bounded address. -/
def outerAddress (right : Bool) (n h d address : ℕ) : ℕ :=
  if right then address % FoldedBackendExecution.outerSize n d
  else address / FoldedBackendExecution.middleSize h d

def middleAddress (right : Bool) (n h d address : ℕ) : ℕ :=
  if right then address / FoldedBackendExecution.outerSize n d
  else address % FoldedBackendExecution.middleSize h d

/-- The literal stored binary integer three. -/
def three : Cell := ⟨⟨false,[true,true]⟩,by decide⟩
@[simp] theorem three_view : view three=3 := rfl

def rightResidue {n h d q block : ℕ} (g : Geometry n h d q block)
    (value residue : Cell) : Result Cell :=
  let multiple:=BinaryCell.mul g.widthCell residue
  let negative:=BinaryCell.neg value
  let result:=BinaryCell.sub negative.value multiple.value
  ⟨result.value,multiple.bitSteps+negative.bitSteps+result.bitSteps⟩

theorem rightResidue_view {n h d q block : ℕ} (g : Geometry n h d q block) (value residue : Cell) :
    view (rightResidue g value residue).value = -view value-(FoldedCounts.foldWidth d:ℤ)*view residue := by
  simp only [rightResidue,BinaryCell.sub_view,BinaryCell.mul_view,BinaryCell.neg_view,Geometry.width_view]

/-- Joint scalar formation. Inactive right slots keep their zero monomial;
the left source additionally enforces the original-label active predicate. -/
def coefficient {n h d q block : ℕ} (right : Bool) (g : Geometry n h d q block)
    (a : BinaryTable n) (address coeff : ℕ) : Result Cell :=
  let loc:=coordinates right g address
  let original:=if right then readTable a loc.value.label loc.value.original
    else readTable a loc.value.original loc.value.label
  let value:=BinaryCell.mul three original.value
  let rhs:=if right then rightResidue g value.value loc.value.residue
    else BinaryCell.add value.value loc.value.residue
  let residue:=BinaryModularCell.remainder g.dCell rhs.value
  let cyclic:=BinaryModularCell.remainder g.qCell value.value
  let requested:=publicNat coeff
  let sameSigma:=BinaryModularCell.equal loc.value.sigma residue.value
  let sameCoeff:=BinaryModularCell.equal requested.value cyclic.value
  let accepted:=loc.value.padded && (if right then true else loc.value.active) && sameSigma.value && sameCoeff.value
  ⟨if accepted then BinaryModularCell.one else BinaryCell.zero,
    loc.bitSteps+original.bitSteps+value.bitSteps+rhs.bitSteps+residue.bitSteps+cyclic.bitSteps+
      requested.bitSteps+sameSigma.bitSteps+sameCoeff.bitSteps+20⟩

/-- Full left backing array. Every joint coefficient result is retained
once before projecting the payload and summing those returned counters. -/
def formLeft {n h d q block : ℕ} (g : Geometry n h d q block) (a : BinaryTable n) :
    Result (Left (FoldedBackendExecution.outerSize n d) (FoldedBackendExecution.middleSize h d) q) :=
  let N:=FoldedBackendExecution.outerSize n d
  let D:=FoldedBackendExecution.middleSize h d
  let cells:=Vector.ofFn (fun address : Fin (N*D)=>Vector.ofFn (fun coeff : Fin q=>
    coefficient false g a address.val coeff.val))
  ⟨cells.map (fun row=>row.map (fun result=>result.value)),
    (∑ address : Fin (N*D),∑ coeff : Fin q,((cells.get address).get coeff).bitSteps)+
      20*(N*D)*q*((N*D).size+q.size+1)⟩

def formRight {n h d q block : ℕ} (g : Geometry n h d q block) (a : BinaryTable n) :
    Result (Right (FoldedBackendExecution.outerSize n d) (FoldedBackendExecution.middleSize h d) q) :=
  let N:=FoldedBackendExecution.outerSize n d
  let D:=FoldedBackendExecution.middleSize h d
  let cells:=Vector.ofFn (fun address : Fin (D*N)=>Vector.ofFn (fun coeff : Fin q=>
    coefficient true g a address.val coeff.val))
  ⟨cells.map (fun row=>row.map (fun result=>result.value)),
    (∑ address : Fin (D*N),∑ coeff : Fin q,((cells.get address).get coeff).bitSteps)+
      20*(D*N)*q*((D*N).size+q.size+1)⟩

@[simp] theorem formLeft_get {n h d q block : ℕ} (g : Geometry n h d q block) (a : BinaryTable n)
    (address : Fin (FoldedBackendExecution.outerSize n d*FoldedBackendExecution.middleSize h d)) (coeff : Fin q) :
    ((formLeft g a).value.get address).get coeff=(coefficient false g a address.val coeff.val).value := by
  simp only [formLeft,Vector.get_map,Vector.get_ofFn]

@[simp] theorem formRight_get {n h d q block : ℕ} (g : Geometry n h d q block) (a : BinaryTable n)
    (address : Fin (FoldedBackendExecution.middleSize h d*FoldedBackendExecution.outerSize n d)) (coeff : Fin q) :
    ((formRight g a).value.get address).get coeff=(coefficient true g a address.val coeff.val).value := by
  simp only [formRight,Vector.get_map,Vector.get_ofFn]

structure Sources (n h d q block : ℕ) where
  geometry : Geometry n h d q block
  left : Left (FoldedBackendExecution.outerSize n d) (FoldedBackendExecution.middleSize h d) q
  right : Right (FoldedBackendExecution.outerSize n d) (FoldedBackendExecution.middleSize h d) q

/-- Only binary original table cells enter this producer. The original
native integer tables are not retained or read again here. -/
def formSources {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (b : Fin (CompactBlocks.blockCount n h)) (input : Inputs n) :
    Result (Sources n h (FoldedBackendExecution.physicalFold f) f.cyclic b.val) :=
  let geometry:=makeGeometry n h (FoldedBackendExecution.physicalFold f) f.cyclic b.val
  let left:=formLeft geometry.value input.left
  let right:=formRight geometry.value input.right
  ⟨⟨geometry.value,left.value,right.value⟩,geometry.bitSteps+left.bitSteps+right.bitSteps⟩

/-- Cached public dimensions supplied by the separately executed parameter
program. The erased equalities certify their meaning without reevaluating
sqrt, clog or padding inside the binary producer. -/
def makeGeometryCached (n h d q block w N D R : ℕ)
    (hw : w=FoldedCounts.foldWidth d) (hN : N=FoldedBackendExecution.outerSize n d)
    (hD : D=FoldedBackendExecution.middleSize h d) (hR : R=FoldedBackendExecution.rawMiddle h d) :
    Result (Geometry n h d q block) :=
  let nc:=publicNat n
  let dc:=publicNat d
  let qc:=publicNat q
  let wc:=publicNat w
  let oc:=publicNat N
  let mc:=publicNat D
  let rc:=publicNat R
  let bc:=publicNat block
  let hc:=publicNat h
  let offset:=BinaryCell.mul bc.value hc.value
  ⟨⟨nc.value,dc.value,qc.value,wc.value,oc.value,mc.value,rc.value,offset.value,
      publicNat_view _,publicNat_view _,publicNat_view _,
      (publicNat_view w).trans (congrArg Int.ofNat hw),
      (publicNat_view N).trans (congrArg Int.ofNat hN),
      (publicNat_view D).trans (congrArg Int.ofNat hD),
      (publicNat_view R).trans (congrArg Int.ofNat hR),
      by dsimp [offset,bc,hc]; simp only [BinaryCell.mul_view,publicNat_view]⟩,
    nc.bitSteps+dc.bitSteps+qc.bitSteps+wc.bitSteps+oc.bitSteps+mc.bitSteps+rc.bitSteps+
      bc.bitSteps+hc.bitSteps+offset.bitSteps+20⟩

theorem makeGeometryCached_refines (n h d q block w N D R : ℕ)
    (hw : w=FoldedCounts.foldWidth d) (hN : N=FoldedBackendExecution.outerSize n d)
    (hD : D=FoldedBackendExecution.middleSize h d) (hR : R=FoldedBackendExecution.rawMiddle h d) :
    makeGeometryCached n h d q block w N D R hw hN hD hR=makeGeometry n h d q block := by
  subst w N D R
  rfl

def formLeftCached {n h d q block : ℕ} (g : Geometry n h d q block) (a : BinaryTable n)
    (N D : ℕ) (hN : N=FoldedBackendExecution.outerSize n d)
    (hD : D=FoldedBackendExecution.middleSize h d) :
    Result (Left (FoldedBackendExecution.outerSize n d) (FoldedBackendExecution.middleSize h d) q) :=
  let cells:=Vector.ofFn (fun address : Fin (N*D)=>Vector.ofFn (fun coeff : Fin q=>
    coefficient false g a address.val coeff.val))
  ⟨Vector.cast (congrArg₂ Nat.mul hN hD) (cells.map (fun row=>row.map (fun result=>result.value))),
    (∑ address : Fin (N*D),∑ coeff : Fin q,((cells.get address).get coeff).bitSteps)+
      20*(N*D)*q*((N*D).size+q.size+1)⟩

def formRightCached {n h d q block : ℕ} (g : Geometry n h d q block) (a : BinaryTable n)
    (N D : ℕ) (hN : N=FoldedBackendExecution.outerSize n d)
    (hD : D=FoldedBackendExecution.middleSize h d) :
    Result (Right (FoldedBackendExecution.outerSize n d) (FoldedBackendExecution.middleSize h d) q) :=
  let cells:=Vector.ofFn (fun address : Fin (D*N)=>Vector.ofFn (fun coeff : Fin q=>
    coefficient true g a address.val coeff.val))
  ⟨Vector.cast (congrArg₂ Nat.mul hD hN) (cells.map (fun row=>row.map (fun result=>result.value))),
    (∑ address : Fin (D*N),∑ coeff : Fin q,((cells.get address).get coeff).bitSteps)+
      20*(D*N)*q*((D*N).size+q.size+1)⟩

theorem formLeftCached_refines {n h d q block : ℕ} (g : Geometry n h d q block) (a : BinaryTable n)
    (N D : ℕ) (hN : N=FoldedBackendExecution.outerSize n d)
    (hD : D=FoldedBackendExecution.middleSize h d) : formLeftCached g a N D hN hD=formLeft g a := by
  subst N D
  rfl

theorem formRightCached_refines {n h d q block : ℕ} (g : Geometry n h d q block) (a : BinaryTable n)
    (N D : ℕ) (hN : N=FoldedBackendExecution.outerSize n d)
    (hD : D=FoldedBackendExecution.middleSize h d) : formRightCached g a N D hN hD=formRight g a := by
  subst N D
  rfl

def formSourcesCached {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (b : Fin (CompactBlocks.blockCount n h)) (input : Inputs n) (w N D R : ℕ)
    (hw : w=FoldedCounts.foldWidth (FoldedBackendExecution.physicalFold f))
    (hN : N=FoldedBackendExecution.outerSize n (FoldedBackendExecution.physicalFold f))
    (hD : D=FoldedBackendExecution.middleSize h (FoldedBackendExecution.physicalFold f))
    (hR : R=FoldedBackendExecution.rawMiddle h (FoldedBackendExecution.physicalFold f)) :
    Result (Sources n h (FoldedBackendExecution.physicalFold f) f.cyclic b.val) :=
  let geometry:=makeGeometryCached n h (FoldedBackendExecution.physicalFold f) f.cyclic b.val w N D R hw hN hD hR
  let left:=formLeftCached geometry.value input.left N D hN hD
  let right:=formRightCached geometry.value input.right N D hN hD
  ⟨⟨geometry.value,left.value,right.value⟩,geometry.bitSteps+left.bitSteps+right.bitSteps⟩

theorem formSourcesCached_refines {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (b : Fin (CompactBlocks.blockCount n h)) (input : Inputs n) (w N D R : ℕ)
    (hw : w=FoldedCounts.foldWidth (FoldedBackendExecution.physicalFold f))
    (hN : N=FoldedBackendExecution.outerSize n (FoldedBackendExecution.physicalFold f))
    (hD : D=FoldedBackendExecution.middleSize h (FoldedBackendExecution.physicalFold f))
    (hR : R=FoldedBackendExecution.rawMiddle h (FoldedBackendExecution.physicalFold f)) :
    formSourcesCached f b input w N D R hw hN hD hR=formSources f b input := by
  subst w N D R
  rfl

end
end ThinMatrix.BinaryFoldedFormation

#print axioms ThinMatrix.BinaryFoldedFormation.encodeTable_view
#print axioms ThinMatrix.BinaryFoldedFormation.encodeInputs_cost
#print axioms ThinMatrix.BinaryFoldedFormation.readTable_view
#print axioms ThinMatrix.BinaryFoldedFormation.readTable_cost
#print axioms ThinMatrix.BinaryFoldedFormation.formLeft_get
#print axioms ThinMatrix.BinaryFoldedFormation.formRight_get
#print axioms ThinMatrix.BinaryFoldedFormation.makeGeometryCached_refines
#print axioms ThinMatrix.BinaryFoldedFormation.formLeftCached_refines
#print axioms ThinMatrix.BinaryFoldedFormation.formRightCached_refines
#print axioms ThinMatrix.BinaryFoldedFormation.formSourcesCached_refines
