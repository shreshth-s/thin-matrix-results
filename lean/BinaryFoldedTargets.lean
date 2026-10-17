import BinaryFoldedFormation

/-! Binary target locators for the frozen folded backend. The executable
path reads one stored target cell, then uses counted cell arithmetic and
bounded decoding. Integer views, ZMod, and Fin casts occur only in proofs. -/
namespace ThinMatrix.BinaryFoldedTargets

open BinaryCell BinaryFoldedFormation StoredMinPlusAPSP
open Fin.CommRing
open scoped BigOperators
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
noncomputable section

/-- The three literal signed-window cells. -/
def negativeOne : Cell := ⟨⟨true,[true]⟩,by decide⟩
def windowCell (w : Fin 3) : Cell :=
  if w.val=0 then negativeOne else if w.val=1 then BinaryCell.zero else BinaryModularCell.one

@[simp] theorem windowCell_view (w : Fin 3) : view (windowCell w)=CompleteAPSP.windowValue w := by
  fin_cases w <;> decide

theorem windowCell_size (w : Fin 3) : (view (windowCell w)).natAbs.size ≤ 1 := by
  fin_cases w <;> decide

def formTarget {n : ℕ} (T : BinaryTable n) (i j : Fin n) (w : Fin 3) : Result Cell :=
  let original:=readTable T i.val j.val
  let shifted:=BinaryCell.sub original.value (windowCell w)
  let scaled:=BinaryCell.mul three shifted.value
  ⟨scaled.value,original.bitSteps+shifted.bitSteps+scaled.bitSteps+10⟩

@[simp] theorem formTarget_view {n : ℕ} (T : BinaryTable n) (i j : Fin n) (w : Fin 3) :
    view (formTarget T i j w).value = FoldedBackendExecution.target (viewTable T) i j w := by
  simp [formTarget,BinaryCell.mul_view,BinaryCell.sub_view,readTable_view,
    nativeRead,i.isLt,j.isLt,FoldedBackendExecution.target]

structure RawLocator where
  row : ℕ
  column : ℕ
  coefficient : ℕ

/-- Every returned digit comes from the magnitude bits of an actual cell.
The stored geometry is shared with all source producers. -/
def locateRaw {n h d q block : ℕ} (g : Geometry n h d q block)
    (T : BinaryTable n) (i j : Fin n) (w : Fin 3) : Result RawLocator :=
  let target:=formTarget T i j w
  let residue:=BinaryModularCell.remainder g.dCell target.value
  let digits:=BinaryModularCell.split g.widthCell residue.value
  let negative:=BinaryCell.neg target.value
  let cyclic:=BinaryModularCell.remainder g.qCell negative.value
  let ic:=publicNat i.val
  let jc:=publicNat j.val
  let rowBase:=BinaryCell.mul ic.value g.widthCell
  let columnBase:=BinaryCell.mul jc.value g.widthCell
  let rowCell:=BinaryCell.add rowBase.value digits.value.2
  let columnCell:=BinaryCell.add columnBase.value digits.value.1
  let row:=BinaryModularCell.decodeUnsigned rowCell.value
  let column:=BinaryModularCell.decodeUnsigned columnCell.value
  let coefficient:=BinaryModularCell.decodeUnsigned cyclic.value
  ⟨⟨row.value,column.value,coefficient.value⟩,
    target.bitSteps+residue.bitSteps+digits.bitSteps+negative.bitSteps+cyclic.bitSteps+
      ic.bitSteps+jc.bitSteps+rowBase.bitSteps+columnBase.bitSteps+rowCell.bitSteps+
      columnCell.bitSteps+row.bitSteps+column.bitSteps+coefficient.bitSteps+20⟩

private theorem decoded_eq_nat (x : Cell) (v : ℕ) (hv : view x=(v:ℤ)) :
    (BinaryModularCell.decodeUnsigned x).value=v := by
  rw [BinaryModularCell.decodeUnsigned_value,hv,Int.natAbs_natCast]

/-- Projection to the unique frozen folded position and cyclic coefficient. -/
theorem locateRaw_values {n h d q block : ℕ} [NeZero d] [NeZero q]
    (g : Geometry n h d q block) (T : BinaryTable n) (i j : Fin n) (w : Fin 3) :
    let value:=FoldedBackendExecution.target (viewTable T) i j w
    (locateRaw g T i j w).value.row =
      (CompactBlocks.outerEquiv n d (i,FoldedCounts.residueLow (value : ZMod d))).val ∧
    (locateRaw g T i j w).value.column =
      (CompactBlocks.outerEquiv n d (j,FoldedCounts.residueHigh (value : ZMod d))).val ∧
    (locateRaw g T i j w).value.coefficient = ((-value:ℤ):Fin q).val := by
  let target:=formTarget T i j w
  let residue:=BinaryModularCell.remainder g.dCell target.value
  let digits:=BinaryModularCell.split g.widthCell residue.value
  let negative:=BinaryCell.neg target.value
  let cyclic:=BinaryModularCell.remainder g.qCell negative.value
  let ic:=publicNat i.val
  let jc:=publicNat j.val
  let rowBase:=BinaryCell.mul ic.value g.widthCell
  let columnBase:=BinaryCell.mul jc.value g.widthCell
  let rowCell:=BinaryCell.add rowBase.value digits.value.2
  let columnCell:=BinaryCell.add columnBase.value digits.value.1
  let value:=FoldedBackendExecution.target (viewTable T) i j w
  have hdp : 0<view g.dCell := by rw [g.d_view]; exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  have hqp : 0<view g.qCell := by rw [g.q_view]; exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hwp : 0<view g.widthCell := by rw [g.width_view]; exact_mod_cast FoldedCounts.foldWidth_pos d
  have ht : view target.value=value := formTarget_view T i j w
  have hr : view residue.value = (((value:ZMod d).val:ℕ):ℤ) := by
    simp only [residue,BinaryModularCell.remainder_view _ _ hdp,ht,g.d_view]
    exact (ZMod.val_intCast value).symm
  have hlo : view digits.value.2 = ((FoldedCounts.residueLow (value:ZMod d)).val:ℤ) := by
    rw [BinaryModularCell.split_remainder_view _ _ hwp,hr,g.width_view]
    exact (Int.natCast_mod _ _).symm
  have hhi : view digits.value.1 = ((FoldedCounts.residueHigh (value:ZMod d)).val:ℤ) := by
    rw [BinaryModularCell.split_quotient_view _ _ hwp.le,hr,g.width_view]
    exact (Int.natCast_div _ _).symm
  have hrow : view rowCell.value =
      ((CompactBlocks.outerEquiv n d (i,FoldedCounts.residueLow (value:ZMod d))).val:ℤ) := by
    simp only [rowCell,rowBase,BinaryCell.add_view,BinaryCell.mul_view,ic,publicNat_view,g.width_view,hlo]
    simp only [CompactBlocks.outerEquiv,finProdFinEquiv,Equiv.coe_fn_mk,Nat.cast_add,Nat.cast_mul]
    ring
  have hcolumn : view columnCell.value =
      ((CompactBlocks.outerEquiv n d (j,FoldedCounts.residueHigh (value:ZMod d))).val:ℤ) := by
    simp only [columnCell,columnBase,BinaryCell.add_view,BinaryCell.mul_view,jc,publicNat_view,g.width_view,hhi]
    simp only [CompactBlocks.outerEquiv,finProdFinEquiv,Equiv.coe_fn_mk,Nat.cast_add,Nat.cast_mul]
    ring
  have hcyclic : view cyclic.value = ((((-value:ℤ):Fin q).val:ℕ):ℤ) := by
    simp only [cyclic,BinaryModularCell.remainder_view _ _ hqp,negative,BinaryCell.neg_view,ht,g.q_view]
    rw [Fin.val_intCast]
    exact (Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast NeZero.ne q))).symm
  change (BinaryModularCell.decodeUnsigned rowCell.value).value=_ ∧
    (BinaryModularCell.decodeUnsigned columnCell.value).value=_ ∧
    (BinaryModularCell.decodeUnsigned cyclic.value).value=_
  exact ⟨decoded_eq_nat _ _ hrow,decoded_eq_nat _ _ hcolumn,decoded_eq_nat _ _ hcyclic⟩

/-- Proof arguments bound the decoded bits and are erased at execution. -/
def locate {n h d q block : ℕ} [NeZero d] [NeZero q]
    (g : Geometry n h d q block) (T : BinaryTable n) (i j : Fin n) (w : Fin 3) :
    Result (TilingCosts.Request (FoldedBackendExecution.outerSize n d) q) :=
  let out:=locateRaw g T i j w
  ⟨⟨⟨out.value.row,by rw [(locateRaw_values g T i j w).1]; exact Fin.isLt _⟩,
      ⟨out.value.column,by rw [(locateRaw_values g T i j w).2.1]; exact Fin.isLt _⟩,
      ⟨out.value.coefficient,by rw [(locateRaw_values g T i j w).2.2]; exact Fin.isLt _⟩⟩,
    out.bitSteps⟩

theorem locate_values {n h d q block : ℕ} [NeZero d] [NeZero q]
    (g : Geometry n h d q block) (T : BinaryTable n) (i j : Fin n) (w : Fin 3) :
    let value:=FoldedBackendExecution.target (viewTable T) i j w
    (locate g T i j w).value =
      ⟨CompactBlocks.outerEquiv n d (i,FoldedCounts.residueLow (value:ZMod d)),
        CompactBlocks.outerEquiv n d (j,FoldedCounts.residueHigh (value:ZMod d)),
        ((-value:ℤ):Fin q)⟩ := by
  have hv:=locateRaw_values g T i j w
  simpa only [locate,TilingCosts.Request.mk.injEq,Fin.ext_iff] using hv


/-- Retain each joint locator result once. The request vector is independent
of the middle block and can be reused by every block query. -/
def requests {n h r block : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (g : Geometry n h (FoldedBackendExecution.physicalFold f) f.cyclic block)
    (T : BinaryTable n) :
    Result (Vector (TilingCosts.Request (FoldedBackendExecution.outerSize n
      (FoldedBackendExecution.physicalFold f)) f.cyclic) (FoldedBackendExecution.windowQuerySize n)) :=
  let cells:=Vector.ofFn (fun index : Fin (FoldedBackendExecution.windowQuerySize n) =>
    let x:=(FoldedBackendExecution.windowQueryEquiv n).symm index
    locate g T x.1.1 x.1.2 x.2)
  ⟨cells.map (fun cell=>cell.value),
    (∑ index : Fin (FoldedBackendExecution.windowQuerySize n),(cells.get index).bitSteps)+
      20*(FoldedBackendExecution.windowQuerySize n)*((FoldedBackendExecution.windowQuerySize n).size+1)⟩

theorem requests_values {n h r block : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (g : Geometry n h (FoldedBackendExecution.physicalFold f) f.cyclic block)
    (T : BinaryTable n) :
    (requests f g T).value=FoldedBackendExecution.requests f (viewTable T) := by
  apply Vector.ext
  intro index hindex
  simp only [requests,FoldedBackendExecution.requests,Vector.getElem_map,Vector.getElem_ofFn]
  exact locate_values _ _ _ _ _

/-- Only public dimensions used by target arithmetic are capped here. -/
structure MetadataBound (n d q B : ℕ) : Prop where
  n_size : n.size ≤ B
  d_size : d.size ≤ B
  q_size : q.size ≤ B
  width_size : (FoldedCounts.foldWidth d).size ≤ B

theorem formTarget_size {n : ℕ} (T : BinaryTable n) (W : ℕ)
    (hT : ∀ i j, (view ((T.get i).get j)).natAbs.size ≤ W)
    (i j : Fin n) (w : Fin 3) :
    (view (formTarget T i j w).value).natAbs.size ≤ W+4 := by
  have hr:=readTable_size T W hT i.val j.val
  have hs:=BinaryModularCell.sub_size (readTable T i.val j.val).value (windowCell w)
  have hw:=windowCell_size w
  have hthree : (view three).natAbs.size=2 := by decide
  have hm:=BinaryModularCell.mul_size three
    (BinaryCell.sub (readTable T i.val j.val).value (windowCell w)).value
  change (view (BinaryCell.mul three
    (BinaryCell.sub (readTable T i.val j.val).value (windowCell w)).value).value).natAbs.size ≤ _
  rw [hthree] at hm
  have hmax : max (view (readTable T i.val j.val).value).natAbs.size
      (view (windowCell w)).natAbs.size ≤ W+1 := max_le (hr.trans (by omega)) (hw.trans (by omega))
  omega

theorem formTarget_cost {n d q W B : ℕ} (T : BinaryTable n)
    (hb : MetadataBound n d q B)
    (hT : ∀ i j, (view ((T.get i).get j)).natAbs.size ≤ W)
    (i j : Fin n) (w : Fin 3) :
    (formTarget T i j w).bitSteps ≤ 100000*(W+B+10)^2 := by
  let C:=W+B+10
  have hr:=readTable_size T W hT i.val j.val
  have hw:=windowCell_size w
  have hswidth:=BinaryModularCell.sub_size (readTable T i.val j.val).value (windowCell w)
  have hmax : max (view (readTable T i.val j.val).value).natAbs.size
      (view (windowCell w)).natAbs.size ≤ W+1 := max_le (hr.trans (by omega)) (hw.trans (by omega))
  have hswidth' : (view (BinaryCell.sub (readTable T i.val j.val).value (windowCell w)).value).natAbs.size ≤ C := by
    dsimp [C]; omega
  have hthree : (view three).natAbs.size ≤ C := by
    have h : (view three).natAbs.size=2 := by decide
    rw [h]
    dsimp [C]; omega
  have hread:=readTable_cost T W hT i.val j.val
  have hsub:=BinaryCell.sub_price C (readTable T i.val j.val).value (windowCell w)
    (hr.trans (by dsimp [C]; omega)) (hw.trans (by dsimp [C]; omega))
  have hmul:=BinaryCell.mul_price C three
    (BinaryCell.sub (readTable T i.val j.val).value (windowCell w)).value hthree hswidth'
  have hi : i.val.size ≤ B := (Nat.size_le_size i.isLt.le).trans hb.n_size
  have hj : j.val.size ≤ B := (Nat.size_le_size j.isLt.le).trans hb.n_size
  unfold BackendScalarBits.backendScalarUnit BackendScalarBits.scalarUnit at hread hsub hmul
  change (readTable T i.val j.val).bitSteps+
    (BinaryCell.sub (readTable T i.val j.val).value (windowCell w)).bitSteps+
    (BinaryCell.mul three (BinaryCell.sub (readTable T i.val j.val).value (windowCell w)).value).bitSteps+10 ≤ _
  dsimp [C] at hsub hmul
  have hn:=hb.n_size
  nlinarith only [hread,hsub,hmul,hi,hj,hn,Nat.zero_le W,Nat.zero_le B,Nat.zero_le (W*B)]

/-- Every intermediate operand bound is derived from the original table
width and public metadata. No global register-width assumption is used. -/
theorem locateRaw_cost {n h d q block W B : ℕ} [NeZero d] [NeZero q]
    (g : Geometry n h d q block) (T : BinaryTable n) (hb : MetadataBound n d q B)
    (hT : ∀ i j, (view ((T.get i).get j)).natAbs.size ≤ W)
    (i j : Fin n) (w : Fin 3) :
    (locateRaw g T i j w).bitSteps ≤ 1000000*(W+B+10)^2 := by
  let C:=W+B+10
  let K:=2*C
  let target:=formTarget T i j w
  let residue:=BinaryModularCell.remainder g.dCell target.value
  let digits:=BinaryModularCell.split g.widthCell residue.value
  let negative:=BinaryCell.neg target.value
  let cyclic:=BinaryModularCell.remainder g.qCell negative.value
  let ic:=publicNat i.val
  let jc:=publicNat j.val
  let rowBase:=BinaryCell.mul ic.value g.widthCell
  let columnBase:=BinaryCell.mul jc.value g.widthCell
  let rowCell:=BinaryCell.add rowBase.value digits.value.2
  let columnCell:=BinaryCell.add columnBase.value digits.value.1
  have hdp : 0<view g.dCell := by rw [g.d_view]; exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  have hqp : 0<view g.qCell := by rw [g.q_view]; exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hwp : 0<view g.widthCell := by rw [g.width_view]; exact_mod_cast FoldedCounts.foldWidth_pos d
  have hds : (view g.dCell).natAbs.size ≤ B := by simpa only [g.d_view,Int.natAbs_natCast] using hb.d_size
  have hqs : (view g.qCell).natAbs.size ≤ B := by simpa only [g.q_view,Int.natAbs_natCast] using hb.q_size
  have hws : (view g.widthCell).natAbs.size ≤ B := by simpa only [g.width_view,Int.natAbs_natCast] using hb.width_size
  have ht : (view target.value).natAbs.size ≤ W+4 := formTarget_size T W hT i j w
  have hr : (view residue.value).natAbs.size ≤ B :=
    (BinaryModularCell.remainder_size g.dCell target.value hdp).trans hds
  have hh : (view digits.value.1).natAbs.size ≤ B :=
    BinaryModularCell.split_quotient_size B g.widthCell residue.value hwp.le hr
  have hl : (view digits.value.2).natAbs.size ≤ B :=
    BinaryModularCell.split_remainder_size B g.widthCell residue.value hwp hws
  have hn : (view negative.value).natAbs.size ≤ W+4 := by simpa only [negative,BinaryCell.neg_view,Int.natAbs_neg] using ht
  have hc : (view cyclic.value).natAbs.size ≤ B :=
    (BinaryModularCell.remainder_size g.qCell negative.value hqp).trans hqs
  have hi : i.val.size ≤ B := (Nat.size_le_size i.isLt.le).trans hb.n_size
  have hj : j.val.size ≤ B := (Nat.size_le_size j.isLt.le).trans hb.n_size
  have hic : (view ic.value).natAbs.size ≤ B := by simpa only [ic,publicNat_view,Int.natAbs_natCast] using hi
  have hjc : (view jc.value).natAbs.size ≤ B := by simpa only [jc,publicNat_view,Int.natAbs_natCast] using hj
  have hrb : (view rowBase.value).natAbs.size ≤ 2*B :=
    (BinaryModularCell.mul_size ic.value g.widthCell).trans (by omega)
  have hcb : (view columnBase.value).natAbs.size ≤ 2*B :=
    (BinaryModularCell.mul_size jc.value g.widthCell).trans (by omega)
  have hrow : (view rowCell.value).natAbs.size ≤ 2*B+1 :=
    (BinaryModularCell.add_size rowBase.value digits.value.2).trans (by
      have hm : max (view rowBase.value).natAbs.size (view digits.value.2).natAbs.size ≤ 2*B :=
        max_le hrb (hl.trans (by omega))
      omega)
  have hcolumn : (view columnCell.value).natAbs.size ≤ 2*B+1 :=
    (BinaryModularCell.add_size columnBase.value digits.value.1).trans (by
      have hm : max (view columnBase.value).natAbs.size (view digits.value.1).natAbs.size ≤ 2*B :=
        max_le hcb (hh.trans (by omega))
      omega)
  have hbK : B ≤ K := by dsimp [K,C]; omega
  have htK : W+4 ≤ K := by dsimp [K,C]; omega
  have h2bK : 2*B+1 ≤ K := by dsimp [K,C]; omega
  have htarget : target.bitSteps ≤ 100000*(W+B+10)^2 := formTarget_cost (d:=d) (q:=q) T hb hT i j w
  have hresidue : residue.bitSteps ≤ 6000*(K+1)^2 :=
    BinaryModularCell.split_price_square K g.dCell target.value hdp (hds.trans hbK) (ht.trans htK)
  have hdigits : digits.bitSteps ≤ 6000*(K+1)^2 := BinaryModularCell.split_price_square K g.widthCell residue.value hwp (hws.trans hbK) (hr.trans hbK)
  have hnegative : negative.bitSteps ≤ 800*(K+1)^2 := by
    have hs:=BinaryCell.sub_price K BinaryCell.zero target.value (by simp) (ht.trans htK)
    unfold BackendScalarBits.backendScalarUnit BackendScalarBits.scalarUnit at hs
    exact hs.trans_eq (by ring)
  have hcyclic : cyclic.bitSteps ≤ 6000*(K+1)^2 :=
    BinaryModularCell.split_price_square K g.qCell negative.value hqp (hqs.trans hbK) (hn.trans htK)
  have hiprice : ic.bitSteps ≤ 10*(K+1)^2 := (publicNat_cost i.val).trans (by gcongr; exact hi.trans hbK)
  have hjprice : jc.bitSteps ≤ 10*(K+1)^2 := (publicNat_cost j.val).trans (by gcongr; exact hj.trans hbK)
  have hrbprice : rowBase.bitSteps ≤ BackendScalarBits.backendScalarUnit K := BinaryCell.mul_price K ic.value g.widthCell (hic.trans hbK) (hws.trans hbK)
  have hcbprice : columnBase.bitSteps ≤ BackendScalarBits.backendScalarUnit K := BinaryCell.mul_price K jc.value g.widthCell (hjc.trans hbK) (hws.trans hbK)
  have hrowprice : rowCell.bitSteps ≤ BackendScalarBits.backendScalarUnit K := BinaryCell.add_price K rowBase.value digits.value.2 (hrb.trans (by omega)) (hl.trans hbK)
  have hcolumnprice : columnCell.bitSteps ≤ BackendScalarBits.backendScalarUnit K := BinaryCell.add_price K columnBase.value digits.value.1 (hcb.trans (by omega)) (hh.trans hbK)
  have hrowdecode:=BinaryModularCell.decodeUnsigned_price K rowCell.value (hrow.trans h2bK)
  have hcolumndecode:=BinaryModularCell.decodeUnsigned_price K columnCell.value (hcolumn.trans h2bK)
  have hcoeffdecode:=BinaryModularCell.decodeUnsigned_price K cyclic.value (hc.trans hbK)
  unfold BackendScalarBits.backendScalarUnit BackendScalarBits.scalarUnit at hrbprice hcbprice hrowprice hcolumnprice
  change target.bitSteps+residue.bitSteps+digits.bitSteps+negative.bitSteps+cyclic.bitSteps+
    ic.bitSteps+jc.bitSteps+rowBase.bitSteps+columnBase.bitSteps+rowCell.bitSteps+columnCell.bitSteps+
    (BinaryModularCell.decodeUnsigned rowCell.value).bitSteps+
    (BinaryModularCell.decodeUnsigned columnCell.value).bitSteps+
    (BinaryModularCell.decodeUnsigned cyclic.value).bitSteps+20 ≤ _
  dsimp [K,C] at hresidue hdigits hnegative hcyclic hiprice hjprice hrbprice hcbprice hrowprice hcolumnprice hrowdecode hcolumndecode hcoeffdecode
  nlinarith only [htarget,hresidue,hdigits,hnegative,hcyclic,hiprice,hjprice,
    hrbprice,hcbprice,hrowprice,hcolumnprice,hrowdecode,hcolumndecode,hcoeffdecode,
    Nat.zero_le W,Nat.zero_le B,Nat.zero_le (W*B)]

theorem locate_cost {n h d q block W B : ℕ} [NeZero d] [NeZero q]
    (g : Geometry n h d q block) (T : BinaryTable n) (hb : MetadataBound n d q B)
    (hT : ∀ i j, (view ((T.get i).get j)).natAbs.size ≤ W)
    (i j : Fin n) (w : Fin 3) :
    (locate g T i j w).bitSteps ≤ 1000000*(W+B+10)^2 :=
  locateRaw_cost g T hb hT i j w


/-- Formation is paid once for the three windows of every original pair,
independently of the number of middle blocks that reuse the requests. -/
theorem requests_cost {n h r block W B : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (g : Geometry n h (FoldedBackendExecution.physicalFold f) f.cyclic block)
    (T : BinaryTable n)
    (hb : MetadataBound n (FoldedBackendExecution.physicalFold f) f.cyclic B)
    (hT : ∀ i j, (view ((T.get i).get j)).natAbs.size ≤ W) :
    (requests f g T).bitSteps ≤
      2000000*(FoldedBackendExecution.windowQuerySize n)*(W+B+10)^2 := by
  let M:=FoldedBackendExecution.windowQuerySize n
  let C:=W+B+10
  have hcell (index : Fin M) :
      (locate g T (((FoldedBackendExecution.windowQueryEquiv n).symm index).1.1)
        (((FoldedBackendExecution.windowQueryEquiv n).symm index).1.2)
        (((FoldedBackendExecution.windowQueryEquiv n).symm index).2)).bitSteps ≤
      1000000*C^2 := locate_cost g T hb hT _ _ _
  have hsum:=Finset.sum_le_sum (s:=Finset.univ) (fun index _=>hcell index)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] at hsum
  have hnn:=BinaryMultiplierAdapter.size_mul n n
  have hM:=BinaryMultiplierAdapter.size_mul (n*n) 3
  have hthree : (3:ℕ).size=2 := by decide
  have hMsize : M.size ≤ 2*B+2 := by
    dsimp [M,FoldedBackendExecution.windowQuerySize]
    rw [hthree] at hM
    have hn:=hb.n_size
    omega
  have hC : 1≤C := by dsimp [C]; omega
  have hCC : C ≤ C^2 := by simpa using Nat.pow_le_pow_right hC (show 1≤2 by decide)
  have hB : B≤C := by dsimp [C]; omega
  have hover : 20*(M.size+1) ≤ 1000000*C^2 := by
    nlinarith only [hMsize,hCC,hB,hC]
  simp only [requests,Vector.get_ofFn]
  calc
    _ ≤ M*(1000000*C^2)+20*M*(M.size+1) := Nat.add_le_add_right hsum _
    _ = M*(1000000*C^2)+M*(20*(M.size+1)) := by ring
    _ ≤ M*(1000000*C^2)+M*(1000000*C^2) :=
      Nat.add_le_add_left (Nat.mul_le_mul_left M hover) _
    _ = _ := by dsimp [M,C]; ring

#print axioms requests_cost
#print axioms requests_values
#print axioms locate_cost
#print axioms locateRaw_values
#print axioms locate_values
end
end ThinMatrix.BinaryFoldedTargets
