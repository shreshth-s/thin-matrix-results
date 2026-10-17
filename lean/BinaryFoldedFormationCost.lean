import BinaryFoldedFormation

/-! Original-input bit budgets for the literal folded source producer.
All intermediate sizes are derived from original coefficient widths and
public dimension/address widths. No bound on all intermediate registers
is supplied as an assumption. -/

namespace ThinMatrix.BinaryFoldedFormationCost

open BinaryCell BinaryFoldedFormation
open scoped BigOperators

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

structure MetadataBound (n h d q block B : ℕ) : Prop where
  n_size : n.size ≤ B
  h_size : h.size ≤ B
  d_size : d.size ≤ B
  q_size : q.size ≤ B
  block_size : block.size ≤ B
  width_size : (FoldedCounts.foldWidth d).size ≤ B
  outer_size : (FoldedBackendExecution.outerSize n d).size ≤ B
  middle_size : (FoldedBackendExecution.middleSize h d).size ≤ B
  raw_size : (FoldedBackendExecution.rawMiddle h d).size ≤ B

structure CoordinatesBound (B : ℕ) (loc : BinaryFoldedFormation.Coordinates) : Prop where
  original_size : loc.original.size ≤ B
  label_size : loc.label.size ≤ 2*B+1
  sigma_size : (view loc.sigma).natAbs.size ≤ B
  residue_size : (view loc.residue).natAbs.size ≤ B

theorem offset_size {n h d q block B : ℕ} (g : Geometry n h d q block)
    (hb : MetadataBound n h d q block B) : (view g.offsetCell).natAbs.size ≤ 2*B := by
  rw [g.offset_view,Int.natAbs_natCast]
  exact (BinaryMultiplierAdapter.size_mul block h).trans (by
    have h1:=hb.block_size
    have h2:=hb.h_size
    omega)

theorem geometry_cell_sizes {n h d q block B : ℕ} (g : Geometry n h d q block)
    (hb : MetadataBound n h d q block B) :
    (view g.nCell).natAbs.size ≤ B ∧ (view g.dCell).natAbs.size ≤ B ∧
    (view g.qCell).natAbs.size ≤ B ∧ (view g.widthCell).natAbs.size ≤ B ∧
    (view g.outerCell).natAbs.size ≤ B ∧ (view g.middleCell).natAbs.size ≤ B ∧
    (view g.rawCell).natAbs.size ≤ B := by
  simp only [Geometry.n_view,Geometry.d_view,Geometry.q_view,Geometry.width_view,
    Geometry.outer_view,Geometry.middle_view,Geometry.raw_view,Int.natAbs_natCast]
  exact ⟨hb.n_size,hb.d_size,hb.q_size,hb.width_size,hb.outer_size,hb.middle_size,hb.raw_size⟩

/-- A binary addition creates at most one more magnitude bit than the
common input cap. This applies equally to signed stored cells. -/
theorem coordinate_add_size (W : ℕ) (a b : Cell)
    (ha : (view a).natAbs.size ≤ W) (hb : (view b).natAbs.size ≤ W) :
    (view (BinaryCell.add a b).value).natAbs.size ≤ W+1 := by
  apply Nat.size_le.mpr
  rw [BinaryCell.add_view]
  calc
    (view a+view b).natAbs ≤ (view a).natAbs+(view b).natAbs := Int.natAbs_add_le _ _
    _ < 2^W+2^W := Nat.add_lt_add (Nat.size_le.mp ha) (Nat.size_le.mp hb)
    _ = 2^(W+1) := by ring

/-- Every address register cap follows from the public metadata and input
address caps. In particular the block offset is a genuine stored product,
and the original label is a genuine stored addition. -/
theorem coordinates_bounds {n h d q block B : ℕ} (g : Geometry n h d q block)
    (hb : MetadataBound n h d q block B) (hn : 0<n) (hd : 0<d)
    (right : Bool) (address : ℕ) (ha : address.size ≤ B) :
    CoordinatesBound B (coordinates right g address).value ∧
    (coordinates right g address).bitSteps ≤ 100000*(B+1)^2 := by
  let addressCell:=publicNat address
  let divisor:=if right then g.outerCell else g.middleCell
  let flat:=BinaryModularCell.split divisor addressCell.value
  let middle:=if right then flat.value.1 else flat.value.2
  let outer:=if right then flat.value.2 else flat.value.1
  let mid:=BinaryModularCell.split g.dCell middle
  let out:=BinaryModularCell.split g.widthCell outer
  let originalLabel:=BinaryCell.add g.offsetCell mid.value.1
  have gs:=geometry_cell_sizes g hb
  have hnc:=gs.1
  have hdc:=gs.2.1
  have hqc:=gs.2.2.1
  have hwc:=gs.2.2.2.1
  have hoc:=gs.2.2.2.2.1
  have hmc:=gs.2.2.2.2.2.1
  have hrc:=gs.2.2.2.2.2.2
  have hdp : 0<view g.dCell := by simpa using hd
  have hwp : 0<view g.widthCell := by
    rw [g.width_view]
    exact_mod_cast FoldedCounts.foldWidth_pos d
  have hop : 0<view g.outerCell := by
    rw [g.outer_view]
    exact_mod_cast Nat.mul_pos hn (FoldedCounts.foldWidth_pos d)
  have hmp : 0<view g.middleCell := by
    rw [g.middle_view,FoldedBackendExecution.middleSize,PhaseGeometry.pad4]
    positivity
  have hdivp : 0<view divisor := by
    cases right with
    | false => simpa [divisor] using hmp
    | true => simpa [divisor] using hop
  have hdivw : (view divisor).natAbs.size ≤ B := by
    cases right with
    | false => simpa [divisor] using hmc
    | true => simpa [divisor] using hoc
  have haw : (view addressCell.value).natAbs.size ≤ B := by simpa [addressCell] using ha
  have hf1 : (view flat.value.1).natAbs.size ≤ B :=
    BinaryModularCell.split_quotient_size B divisor addressCell.value hdivp.le haw
  have hf2 : (view flat.value.2).natAbs.size ≤ B :=
    BinaryModularCell.split_remainder_size B divisor addressCell.value hdivp hdivw
  have hmiddle : (view middle).natAbs.size ≤ B := by
    cases right with
    | false => simpa [middle] using hf2
    | true => simpa [middle] using hf1
  have houter : (view outer).natAbs.size ≤ B := by
    cases right with
    | false => simpa [outer] using hf1
    | true => simpa [outer] using hf2
  have hmid1 : (view mid.value.1).natAbs.size ≤ B :=
    BinaryModularCell.split_quotient_size B g.dCell middle hdp.le hmiddle
  have hmid2 : (view mid.value.2).natAbs.size ≤ B :=
    BinaryModularCell.split_remainder_size B g.dCell middle hdp hdc
  have hout1 : (view out.value.1).natAbs.size ≤ B :=
    BinaryModularCell.split_quotient_size B g.widthCell outer hwp.le houter
  have hout2 : (view out.value.2).natAbs.size ≤ B :=
    BinaryModularCell.split_remainder_size B g.widthCell outer hwp hwc
  have hoff : (view g.offsetCell).natAbs.size ≤ 2*B := offset_size g hb
  have hlabel : (view originalLabel.value).natAbs.size ≤ 2*B+1 :=
    coordinate_add_size (2*B) g.offsetCell mid.value.1 hoff (hmid1.trans (by omega))
  have hbound : CoordinatesBound B (coordinates right g address).value := by
    constructor
    · simpa only [coordinates,BinaryModularCell.decodeUnsigned_value] using hout1
    · simpa only [coordinates,BinaryModularCell.decodeUnsigned_value] using hlabel
    · exact hmid2
    · exact hout2
  have hacost : addressCell.bitSteps ≤ 10*(B+1)^2 :=
    (publicNat_cost address).trans (by gcongr)
  have hflatcost : flat.bitSteps ≤ 6000*(B+1)^2 :=
    BinaryModularCell.split_price_square B divisor addressCell.value hdivp hdivw haw
  have hmidcost : mid.bitSteps ≤ 6000*(B+1)^2 :=
    BinaryModularCell.split_price_square B g.dCell middle hdp hdc hmiddle
  have houtcost : out.bitSteps ≤ 6000*(B+1)^2 :=
    BinaryModularCell.split_price_square B g.widthCell outer hwp hwc houter
  have hlabelcost : originalLabel.bitSteps ≤ 800*(2*B+1)^2 := by
    have hs:=BinaryCell.add_price (2*B) g.offsetCell mid.value.1 hoff (hmid1.trans (by omega))
    unfold BackendScalarBits.backendScalarUnit BackendScalarBits.scalarUnit at hs
    nlinarith
  have horiginalcost : (BinaryModularCell.decodeUnsigned out.value.1).bitSteps ≤ 8*(B+1)^2 :=
    BinaryModularCell.decodeUnsigned_price B out.value.1 hout1
  have hdecodecost : (BinaryModularCell.decodeUnsigned originalLabel.value).bitSteps ≤ 8*(2*B+2)^2 :=
    BinaryModularCell.decodeUnsigned_price (2*B+1) originalLabel.value hlabel
  have hpaddedcost : (BinaryModularCell.lessUnsigned middle g.rawCell).bitSteps ≤ 12*B+1 := by
    rw [BinaryModularCell.lessUnsigned_price]
    have hm : max (view middle).natAbs.size (view g.rawCell).natAbs.size ≤ B := max_le hmiddle hrc
    omega
  have hactivecost : (BinaryModularCell.lessUnsigned originalLabel.value g.nCell).bitSteps ≤ 12*(2*B+1)+1 := by
    rw [BinaryModularCell.lessUnsigned_price]
    have hm : max (view originalLabel.value).natAbs.size (view g.nCell).natAbs.size ≤ 2*B+1 :=
      max_le hlabel (hnc.trans (by omega))
    omega
  refine ⟨hbound,?_⟩
  change addressCell.bitSteps+flat.bitSteps+mid.bitSteps+out.bitSteps+originalLabel.bitSteps+
    (BinaryModularCell.decodeUnsigned out.value.1).bitSteps+
    (BinaryModularCell.decodeUnsigned originalLabel.value).bitSteps+
    (BinaryModularCell.lessUnsigned middle g.rawCell).bitSteps+
    (BinaryModularCell.lessUnsigned originalLabel.value g.nCell).bitSteps+
    20*(address.size+1) ≤ _
  nlinarith only [hacost,hflatcost,hmidcost,houtcost,hlabelcost,horiginalcost,hdecodecost,hpaddedcost,hactivecost,ha]

 theorem coordinates_widths {n h d q block B : ℕ} (g : Geometry n h d q block)
    (hb : MetadataBound n h d q block B) (hn : 0<n) (hd : 0<d)
    (right : Bool) (address : ℕ) (ha : address.size ≤ B) :
    CoordinatesBound B (coordinates right g address).value :=
  (coordinates_bounds g hb hn hd right address ha).1

 theorem coordinates_cost {n h d q block B : ℕ} (g : Geometry n h d q block)
    (hb : MetadataBound n h d q block B) (hn : 0<n) (hd : 0<d)
    (right : Bool) (address : ℕ) (ha : address.size ≤ B) :
    (coordinates right g address).bitSteps ≤ 100000*(B+1)^2 :=
  (coordinates_bounds g hb hn hd right address ha).2


def TableBound {n : ℕ} (W : ℕ) (a : BinaryTable n) : Prop :=
  ∀ i j, (view ((a.get i).get j)).natAbs.size ≤ W

private theorem backendUnit_le (W B : ℕ) :
    BackendScalarBits.backendScalarUnit (2*(W+B+10)) ≤ 10000*(W+B+10)^3 := by
  let K:=W+B+10
  have hk : 1≤K := by dsimp [K];omega
  have hp : (2*K+1)^2 ≤ (3*K)^2 := Nat.pow_le_pow_left (by omega) 2
  have hpow : K^2≤K^3 := Nat.pow_le_pow_right hk (by decide)
  unfold BackendScalarBits.backendScalarUnit BackendScalarBits.scalarUnit
  change 8*(100*(2*K+1)^2) ≤ 10000*K^3
  nlinarith

private theorem modularUnit_le (W B : ℕ) :
    100000*(2*(W+B+10)+1)^3 ≤ 3000000*(W+B+10)^3 := by
  let K:=W+B+10
  have hk : 1≤K := by dsimp [K];omega
  have hp : (2*K+1)^3 ≤ (3*K)^3 := Nat.pow_le_pow_left (by omega) 3
  change 100000*(2*K+1)^3 ≤ 3000000*K^3
  nlinarith

private theorem budget_square_le_cube (W B : ℕ) :
    (B+1)^2 ≤ (W+B+10)^3 := by
  apply (Nat.pow_le_pow_left (by omega : B+1≤W+B+10) 2).trans
  exact Nat.pow_le_pow_right (by omega) (by decide)

private theorem budget_cube_le_cube (W B : ℕ) :
    (B+1)^3 ≤ (W+B+10)^3 := Nat.pow_le_pow_left (by omega) 3

/-- Width and work of the right residue expression, derived from the
original value width and the original/public metadata width. -/
theorem rightResidue_cost_and_size {n h d q block W B : ℕ} (g : Geometry n h d q block)
    (hb : MetadataBound n h d q block B) (value residue : Cell)
    (hv : (view value).natAbs.size ≤ W+2) (hr : (view residue).natAbs.size ≤ B) :
    (rightResidue g value residue).bitSteps ≤ 30000*(W+B+10)^3 ∧
      (view (rightResidue g value residue).value).natAbs.size ≤ 2*(W+B+10) := by
  let C:=2*(W+B+10)
  have hw : (view g.widthCell).natAbs.size ≤ B := by
    simpa only [Geometry.width_view,Int.natAbs_natCast] using hb.width_size
  have hmult : (view (BinaryCell.mul g.widthCell residue).value).natAbs.size ≤ 2*B :=
    (BinaryModularCell.mul_size _ _).trans (by omega)
  have hneg : (view (BinaryCell.neg value).value).natAbs.size ≤ W+2 := by
    simpa only [BinaryCell.neg_view,Int.natAbs_neg] using hv
  have hresult := BinaryModularCell.sub_size (BinaryCell.neg value).value
    (BinaryCell.mul g.widthCell residue).value
  have hmulprice := BinaryCell.mul_price C g.widthCell residue (hw.trans (by dsimp [C];omega))
    (hr.trans (by dsimp [C];omega))
  have hnegprice := BinaryCell.sub_price C BinaryCell.zero value
    (by simp only [BinaryCell.zero_view,Int.natAbs_zero,Nat.size_zero];omega)
    (hv.trans (by dsimp [C];omega))
  have hsubprice := BinaryCell.sub_price C (BinaryCell.neg value).value
    (BinaryCell.mul g.widthCell residue).value (hneg.trans (by dsimp [C];omega))
    (hmult.trans (by dsimp [C];omega))
  have hunit : BackendScalarBits.backendScalarUnit C ≤ 10000*(W+B+10)^3 := backendUnit_le W B
  constructor
  · change (BinaryCell.mul g.widthCell residue).bitSteps+(BinaryCell.neg value).bitSteps+
      (BinaryCell.sub (BinaryCell.neg value).value (BinaryCell.mul g.widthCell residue).value).bitSteps ≤ _
    change (BinaryCell.neg value).bitSteps ≤ _ at hnegprice
    omega
  · change (view (BinaryCell.sub (BinaryCell.neg value).value
        (BinaryCell.mul g.widthCell residue).value).value).natAbs.size ≤ _
    exact hresult.trans (by dsimp [C] at *;omega)

/-- This local theorem consumes only the separately derived coordinate
budget, not assumed bounds on the later coefficient intermediates. -/
theorem coefficient_cost_of_coordinates {n h d q block W B : ℕ}
    (right : Bool) (g : Geometry n h d q block) (a : BinaryTable n)
    (hb : MetadataBound n h d q block B) (ha : TableBound W a)
    (hd : 0<d) (hq : 0<q) (address coeff : ℕ)
    (hc : coeff.size≤B)
    (hloc : CoordinatesBound B (coordinates right g address).value)
    (hlocprice : (coordinates right g address).bitSteps ≤ 1000000000*(B+1)^3) :
    (coefficient right g a address coeff).bitSteps ≤ 1000000000000*(W+B+10)^3 := by
  let C:=2*(W+B+10)
  let loc:=coordinates right g address
  let original:=if right then readTable a loc.value.label loc.value.original
    else readTable a loc.value.original loc.value.label
  let value:=BinaryCell.mul three original.value
  let rhs:=if right then rightResidue g value.value loc.value.residue
    else BinaryCell.add value.value loc.value.residue
  have hlocres : (view loc.value.residue).natAbs.size≤B := hloc.residue_size
  have hlocsigma : (view loc.value.sigma).natAbs.size≤B := hloc.sigma_size
  have hgeom:=geometry_cell_sizes g hb
  have hdw:=hgeom.2.1
  have hqw:=hgeom.2.2.1
  have horig : (view original.value).natAbs.size≤W := by
    dsimp [original]
    split <;> exact readTable_size a W ha _ _
  have horigprice : original.bitSteps ≤ 11000*(W+B+10)^3 := by
    have hread : original.bitSteps ≤ BackendScalarBits.backendScalarUnit W+8*(4*B+2) := by
      dsimp [original]
      split <;> apply (readTable_cost a W ha _ _).trans <;>
        have hi:=hloc.original_size <;> have hj:=hloc.label_size <;> have hn:=hb.n_size <;>
        dsimp [loc] at * <;> omega
    have hmon : BackendScalarBits.backendScalarUnit W ≤ BackendScalarBits.backendScalarUnit C := by
      unfold BackendScalarBits.backendScalarUnit BackendScalarBits.scalarUnit
      dsimp [C]
      gcongr
      omega
    have hunit : BackendScalarBits.backendScalarUnit C ≤ 10000*(W+B+10)^3 := backendUnit_le W B
    have hlinear : 8*(4*B+2)≤1000*(W+B+10)^3 := by
      have hk : W+B+10≤(W+B+10)^3 := Nat.le_self_pow (by decide) _
      omega
    omega
  have hthree : (view three).natAbs.size≤C := by
    rw [three_view]
    change 2≤C
    dsimp [C]
    omega
  have hvalue : (view value.value).natAbs.size≤W+2 :=
    (BinaryModularCell.mul_size three original.value).trans (by
      rw [three_view]
      change 2+(view original.value).natAbs.size≤W+2
      omega)
  have hvalueprice : value.bitSteps≤10000*(W+B+10)^3 := by
    apply (BinaryCell.mul_price C three original.value hthree (horig.trans (by dsimp [C];omega))).trans
    exact backendUnit_le W B
  have hrhs : rhs.bitSteps≤30000*(W+B+10)^3 ∧ (view rhs.value).natAbs.size≤C := by
    dsimp only [rhs]
    split
    · exact rightResidue_cost_and_size g hb value.value loc.value.residue hvalue hlocres
    · have hs:=BinaryModularCell.add_size value.value loc.value.residue
      constructor
      · apply (BinaryCell.add_price C _ _ (hvalue.trans (by dsimp [C];omega))
          (hlocres.trans (by dsimp [C];omega))).trans
        exact (backendUnit_le W B).trans (by omega)
      · exact hs.trans (by dsimp [C];omega)
  have hdpos : 0<view g.dCell := by rw [Geometry.d_view];exact_mod_cast hd
  have hqpos : 0<view g.qCell := by rw [Geometry.q_view];exact_mod_cast hq
  have hresprice : (BinaryModularCell.remainder g.dCell rhs.value).bitSteps≤3000000*(W+B+10)^3 := by
    apply (BinaryModularCell.remainder_price C _ _ hdpos (hdw.trans (by dsimp [C];omega)) hrhs.2).trans
    exact modularUnit_le W B
  have hcycprice : (BinaryModularCell.remainder g.qCell value.value).bitSteps≤3000000*(W+B+10)^3 := by
    apply (BinaryModularCell.remainder_price C _ _ hqpos (hqw.trans (by dsimp [C];omega))
      (hvalue.trans (by dsimp [C];omega))).trans
    exact modularUnit_le W B
  have hreswidth : (view (BinaryModularCell.remainder g.dCell rhs.value).value).natAbs.size≤B :=
    (BinaryModularCell.remainder_size _ _ hdpos).trans hdw
  have hcycwidth : (view (BinaryModularCell.remainder g.qCell value.value).value).natAbs.size≤B :=
    (BinaryModularCell.remainder_size _ _ hqpos).trans hqw
  have hrequested : (view (publicNat coeff).value).natAbs.size≤B := by
    simpa only [publicNat_view,Int.natAbs_natCast] using hc
  have hrequestprice : (publicNat coeff).bitSteps≤10*(W+B+10)^3 :=
    (publicNat_cost coeff).trans (Nat.mul_le_mul_left _
      ((Nat.pow_le_pow_left (Nat.add_le_add_right hc 1) 2).trans (budget_square_le_cube W B)))
  have hsigma : (BinaryModularCell.equal loc.value.sigma
      (BinaryModularCell.remainder g.dCell rhs.value).value).bitSteps≤3000000*(W+B+10)^3 := by
    apply (BinaryModularCell.equal_price C _ _ (hlocsigma.trans (by dsimp [C];omega))
      (hreswidth.trans (by dsimp [C];omega))).trans
    exact modularUnit_le W B
  have hcoeff : (BinaryModularCell.equal (publicNat coeff).value
      (BinaryModularCell.remainder g.qCell value.value).value).bitSteps≤3000000*(W+B+10)^3 := by
    apply (BinaryModularCell.equal_price C _ _ (hrequested.trans (by dsimp [C];omega))
      (hcycwidth.trans (by dsimp [C];omega))).trans
    exact modularUnit_le W B
  have hlocprice' : loc.bitSteps≤1000000000*(W+B+10)^3 :=
    hlocprice.trans (Nat.mul_le_mul_left _ (budget_cube_le_cube W B))
  have hpow : 1≤(W+B+10)^3 := Nat.one_le_pow _ _ (by omega)
  change loc.bitSteps+original.bitSteps+value.bitSteps+rhs.bitSteps+
    (BinaryModularCell.remainder g.dCell rhs.value).bitSteps+
    (BinaryModularCell.remainder g.qCell value.value).bitSteps+
    (publicNat coeff).bitSteps+
    (BinaryModularCell.equal loc.value.sigma (BinaryModularCell.remainder g.dCell rhs.value).value).bitSteps+
    (BinaryModularCell.equal (publicNat coeff).value (BinaryModularCell.remainder g.qCell value.value).value).bitSteps+20≤_
  omega

/-- Complete coefficient budget from original table bits and public address
bits; every later register cap is derived inside the preceding proof. -/
theorem coefficient_cost {n h d q block W B : ℕ}
    (right : Bool) (g : Geometry n h d q block) (a : BinaryTable n)
    (hb : MetadataBound n h d q block B) (ha : TableBound W a)
    (hn : 0<n) (hd : 0<d) (hq : 0<q) (address coeff : ℕ)
    (haddress : address.size≤B) (hc : coeff.size≤B) :
    (coefficient right g a address coeff).bitSteps ≤ 1000000000000*(W+B+10)^3 := by
  have hloc:=coordinates_bounds g hb hn hd right address haddress
  apply coefficient_cost_of_coordinates right g a hb ha hd hq address coeff hc hloc.1
  have hp : (B+1)^2≤(B+1)^3 := Nat.pow_le_pow_right (by omega) (by decide)
  exact hloc.2.trans ((Nat.mul_le_mul_left 100000 hp).trans
    (Nat.mul_le_mul_right _ (by decide)))

theorem makeGeometry_cost {n h d q block B : ℕ} (hb : MetadataBound n h d q block B) :
    (makeGeometry n h d q block).bitSteps≤10000*(B+1)^2 := by
  have hp (x : ℕ) (hx : x.size≤B) : (publicNat x).bitSteps≤10*(B+1)^2 :=
    (publicNat_cost x).trans (Nat.mul_le_mul_left _
      (Nat.pow_le_pow_left (Nat.add_le_add_right hx 1) 2))
  have hn:=hp n hb.n_size
  have hd:=hp d hb.d_size
  have hq:=hp q hb.q_size
  have hw:=hp (FoldedCounts.foldWidth d) hb.width_size
  have hN:=hp (FoldedBackendExecution.outerSize n d) hb.outer_size
  have hD:=hp (FoldedBackendExecution.middleSize h d) hb.middle_size
  have hr:=hp (FoldedBackendExecution.rawMiddle h d) hb.raw_size
  have hblock:=hp block hb.block_size
  have hh:=hp h hb.h_size
  have hmul:=BinaryCell.mul_price B (publicNat block).value (publicNat h).value
    (by simpa only [publicNat_view,Int.natAbs_natCast] using hb.block_size)
    (by simpa only [publicNat_view,Int.natAbs_natCast] using hb.h_size)
  unfold BackendScalarBits.backendScalarUnit BackendScalarBits.scalarUnit at hmul
  have hone : 1≤(B+1)^2 := Nat.one_le_pow _ _ (by omega)
  change (publicNat n).bitSteps+(publicNat d).bitSteps+(publicNat q).bitSteps+
    (publicNat (FoldedCounts.foldWidth d)).bitSteps+
    (publicNat (FoldedBackendExecution.outerSize n d)).bitSteps+
    (publicNat (FoldedBackendExecution.middleSize h d)).bitSteps+
    (publicNat (FoldedBackendExecution.rawMiddle h d)).bitSteps+
    (publicNat block).bitSteps+(publicNat h).bitSteps+
    (BinaryCell.mul (publicNat block).value (publicNat h).value).bitSteps+20≤_
  omega

theorem formLeft_cost_of_coefficient {n h d q block M : ℕ}
    (g : Geometry n h d q block) (a : BinaryTable n)
    (hc : ∀ address : Fin (FoldedBackendExecution.outerSize n d*FoldedBackendExecution.middleSize h d),
      ∀ coeff : Fin q, (coefficient false g a address.val coeff.val).bitSteps≤M) :
    (formLeft g a).bitSteps ≤
      (FoldedBackendExecution.outerSize n d*FoldedBackendExecution.middleSize h d)*q*
        (M+20*((FoldedBackendExecution.outerSize n d*FoldedBackendExecution.middleSize h d).size+q.size+1)) := by
  have hs:=Finset.sum_le_sum (s:=Finset.univ) (fun address _=>
    Finset.sum_le_sum (s:=Finset.univ) (fun coeff _=>hc address coeff))
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] at hs
  simp only [formLeft,Vector.get_ofFn]
  calc
    _ ≤ (FoldedBackendExecution.outerSize n d*FoldedBackendExecution.middleSize h d)*(q*M)+
      20*(FoldedBackendExecution.outerSize n d*FoldedBackendExecution.middleSize h d)*q*
        ((FoldedBackendExecution.outerSize n d*FoldedBackendExecution.middleSize h d).size+q.size+1) :=
      Nat.add_le_add_right hs _
    _ = _ := by ring

theorem formRight_cost_of_coefficient {n h d q block M : ℕ}
    (g : Geometry n h d q block) (a : BinaryTable n)
    (hc : ∀ address : Fin (FoldedBackendExecution.middleSize h d*FoldedBackendExecution.outerSize n d),
      ∀ coeff : Fin q, (coefficient true g a address.val coeff.val).bitSteps≤M) :
    (formRight g a).bitSteps ≤
      (FoldedBackendExecution.outerSize n d*FoldedBackendExecution.middleSize h d)*q*
        (M+20*((FoldedBackendExecution.outerSize n d*FoldedBackendExecution.middleSize h d).size+q.size+1)) := by
  have hs:=Finset.sum_le_sum (s:=Finset.univ) (fun address _=>
    Finset.sum_le_sum (s:=Finset.univ) (fun coeff _=>hc address coeff))
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] at hs
  simp only [formRight,Vector.get_ofFn]
  calc
    _ ≤ (FoldedBackendExecution.middleSize h d*FoldedBackendExecution.outerSize n d)*(q*M)+
      20*(FoldedBackendExecution.middleSize h d*FoldedBackendExecution.outerSize n d)*q*
        ((FoldedBackendExecution.middleSize h d*FoldedBackendExecution.outerSize n d).size+q.size+1) :=
      Nat.add_le_add_right hs _
    _ = _ := by rw [Nat.mul_comm (FoldedBackendExecution.middleSize h d)];ring

private theorem traversal_price {n h d q block W B : ℕ}
    (hb : MetadataBound n h d q block B)
    (hbacking : (FoldedBackendExecution.outerSize n d*FoldedBackendExecution.middleSize h d).size≤B) :
    20*((FoldedBackendExecution.outerSize n d*FoldedBackendExecution.middleSize h d).size+q.size+1)
      ≤100*(W+B+10)^3 := by
  have hq:=hb.q_size
  have hk : W+B+10≤(W+B+10)^3 := Nat.le_self_pow (by decide) _
  omega

theorem formLeft_cost {n h d q block W B : ℕ} (g : Geometry n h d q block) (a : BinaryTable n)
    (hb : MetadataBound n h d q block B) (ha : TableBound W a)
    (hn : 0<n) (hd : 0<d) (hq : 0<q)
    (hbacking : (FoldedBackendExecution.outerSize n d*FoldedBackendExecution.middleSize h d).size≤B) :
    (formLeft g a).bitSteps ≤ 2000000000000*(W+B+10)^3*
      (q*FoldedBackendExecution.outerSize n d*FoldedBackendExecution.middleSize h d) := by
  have hc : ∀ address : Fin (FoldedBackendExecution.outerSize n d*FoldedBackendExecution.middleSize h d),
      ∀ coeff : Fin q, (coefficient false g a address.val coeff.val).bitSteps≤1000000000000*(W+B+10)^3 := by
    intro address coeff
    exact coefficient_cost false g a hb ha hn hd hq _ _
      ((Nat.size_le_size address.isLt.le).trans hbacking)
      ((Nat.size_le_size coeff.isLt.le).trans hb.q_size)
  have hs:=formLeft_cost_of_coefficient g a hc
  have ht:=traversal_price (W:=W) hb hbacking
  calc
    _ ≤ (FoldedBackendExecution.outerSize n d*FoldedBackendExecution.middleSize h d)*q*
      (1000000000000*(W+B+10)^3+
        20*((FoldedBackendExecution.outerSize n d*FoldedBackendExecution.middleSize h d).size+q.size+1)) := hs
    _ ≤ (FoldedBackendExecution.outerSize n d*FoldedBackendExecution.middleSize h d)*q*
      (2000000000000*(W+B+10)^3) := Nat.mul_le_mul_left _ (by omega)
    _ = _ := by ring

theorem formRight_cost {n h d q block W B : ℕ} (g : Geometry n h d q block) (a : BinaryTable n)
    (hb : MetadataBound n h d q block B) (ha : TableBound W a)
    (hn : 0<n) (hd : 0<d) (hq : 0<q)
    (hbacking : (FoldedBackendExecution.outerSize n d*FoldedBackendExecution.middleSize h d).size≤B) :
    (formRight g a).bitSteps ≤ 2000000000000*(W+B+10)^3*
      (q*FoldedBackendExecution.outerSize n d*FoldedBackendExecution.middleSize h d) := by
  have hc : ∀ address : Fin (FoldedBackendExecution.middleSize h d*FoldedBackendExecution.outerSize n d),
      ∀ coeff : Fin q, (coefficient true g a address.val coeff.val).bitSteps≤1000000000000*(W+B+10)^3 := by
    intro address coeff
    have hab : address.val.size≤B := (Nat.size_le_size address.isLt.le).trans (by
      simpa only [Nat.mul_comm] using hbacking)
    exact coefficient_cost true g a hb ha hn hd hq _ _ hab
      ((Nat.size_le_size coeff.isLt.le).trans hb.q_size)
  have hs:=formRight_cost_of_coefficient g a hc
  have ht:=traversal_price (W:=W) hb hbacking
  calc
    _ ≤ (FoldedBackendExecution.outerSize n d*FoldedBackendExecution.middleSize h d)*q*
      (1000000000000*(W+B+10)^3+
        20*((FoldedBackendExecution.outerSize n d*FoldedBackendExecution.middleSize h d).size+q.size+1)) := hs
    _ ≤ (FoldedBackendExecution.outerSize n d*FoldedBackendExecution.middleSize h d)*q*
      (2000000000000*(W+B+10)^3) := Nat.mul_le_mul_left _ (by omega)
    _ = _ := by ring

theorem formSources_cost {n h r W B : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (b : Fin (CompactBlocks.blockCount n h)) (input : Inputs n)
    (hb : MetadataBound n h (FoldedBackendExecution.physicalFold f) f.cyclic b.val B)
    (ha : TableBound W input.left) (hc : TableBound W input.right)
    (hn : 0<n) (hd : 0<FoldedBackendExecution.physicalFold f) (hq : 0<f.cyclic)
    (hbacking : (FoldedBackendExecution.outerSize n (FoldedBackendExecution.physicalFold f)*
      FoldedBackendExecution.middleSize h (FoldedBackendExecution.physicalFold f)).size≤B) :
    (formSources f b input).bitSteps≤3000000000000*(W+B+10)^3*
      (2*f.cyclic*FoldedBackendExecution.outerSize n (FoldedBackendExecution.physicalFold f)*
        FoldedBackendExecution.middleSize h (FoldedBackendExecution.physicalFold f)) := by
  let d:=FoldedBackendExecution.physicalFold f
  let N:=FoldedBackendExecution.outerSize n d
  let D:=FoldedBackendExecution.middleSize h d
  let geometry:=makeGeometry n h d f.cyclic b.val
  let Z:=(W+B+10)^3*(f.cyclic*N*D)
  have hN : 0<N := Nat.mul_pos hn (FoldedCounts.foldWidth_pos d)
  have hD : 0<D := by
    dsimp [D,FoldedBackendExecution.middleSize,PhaseGeometry.pad4]
    positivity
  have hcells : 1≤f.cyclic*N*D := Nat.mul_pos (Nat.mul_pos hq hN) hD
  have hg0 : geometry.bitSteps≤10000*(W+B+10)^3 :=
    (makeGeometry_cost hb).trans (Nat.mul_le_mul_left _ (budget_square_le_cube W B))
  have hg : geometry.bitSteps≤10000*Z := by
    apply hg0.trans
    calc
      10000*(W+B+10)^3 ≤ 10000*(W+B+10)^3*(f.cyclic*N*D) := by
        simpa only [Nat.mul_one] using Nat.mul_le_mul_left (10000*(W+B+10)^3) hcells
      _ = 10000*Z := by dsimp [Z];ring
  have hl : (formLeft geometry.value input.left).bitSteps≤2000000000000*Z := by
    simpa only [Z,N,D,d,Nat.mul_assoc] using formLeft_cost geometry.value input.left hb ha hn hd hq hbacking
  have hr : (formRight geometry.value input.right).bitSteps≤2000000000000*Z := by
    simpa only [Z,N,D,d,Nat.mul_assoc] using formRight_cost geometry.value input.right hb hc hn hd hq hbacking
  calc
    (formSources f b input).bitSteps = geometry.bitSteps+
      (formLeft geometry.value input.left).bitSteps+(formRight geometry.value input.right).bitSteps := rfl
    _ ≤ 6000000000000*Z := by omega
    _ = _ := by dsimp [Z,N,D,d];ring

/-- The original three tables are encoded once, followed by one complete
pair of q-coefficient folded backing arrays. No encoded intermediate is
converted through a semantic integer in this program. -/
theorem encode_and_formSources_cost {n h r W B : ℕ}
    (f : CompactBlocks.PhysicalFactorization r) (b : Fin (CompactBlocks.blockCount n h))
    (A C T : StoredMinPlusAPSP.IntTable n)
    (hb : MetadataBound n h (FoldedBackendExecution.physicalFold f) f.cyclic b.val B)
    (hA : ∀ i j, (StoredMinPlusAPSP.decode A i j).natAbs.size≤W)
    (hC : ∀ i j, (StoredMinPlusAPSP.decode C i j).natAbs.size≤W)
    (hT : ∀ i j, (StoredMinPlusAPSP.decode T i j).natAbs.size≤W)
    (hn : 0<n) (hd : 0<FoldedBackendExecution.physicalFold f) (hq : 0<f.cyclic)
    (hbacking : (FoldedBackendExecution.outerSize n (FoldedBackendExecution.physicalFold f)*
      FoldedBackendExecution.middleSize h (FoldedBackendExecution.physicalFold f)).size≤B) :
    (encodeInputs A C T).bitSteps+(formSources f b (encodeInputs A C T).value).bitSteps≤
      10000000000000*(W+B+10)^3*
        (n^2+2*f.cyclic*FoldedBackendExecution.outerSize n (FoldedBackendExecution.physicalFold f)*
          FoldedBackendExecution.middleSize h (FoldedBackendExecution.physicalFold f)) := by
  have hleft : TableBound W (encodeInputs A C T).value.left := by
    intro i j
    change (view (((encodeTable A).value.get i).get j)).natAbs.size≤W
    rw [encodeTable_get]
    exact hA i j
  have hright : TableBound W (encodeInputs A C T).value.right := by
    intro i j
    change (view (((encodeTable C).value.get i).get j)).natAbs.size≤W
    rw [encodeTable_get]
    exact hC i j
  have hs:=formSources_cost f b (encodeInputs A C T).value hb hleft hright hn hd hq hbacking
  have he0:=encodeInputs_cost A C T W hA hC hT
  have he : (encodeInputs A C T).bitSteps≤1000*(W+B+10)^3*n^2 := by
    have hnsize:=hb.n_size
    have hsquare : (W+1)^2≤(W+B+10)^3 :=
      (Nat.pow_le_pow_left (by omega) 2).trans (Nat.pow_le_pow_right (by omega) (by decide))
    have hlinear : n.size+1≤(W+B+10)^3 := by
      have hpow : W+B+10≤(W+B+10)^3 := Nat.le_self_pow (by decide) _
      omega
    calc
      _ ≤ 30*n^2*((W+1)^2+n.size+1) := he0
      _ ≤ 30*n^2*(2*(W+B+10)^3) := Nat.mul_le_mul_left _ (by omega)
      _ ≤ 1000*(W+B+10)^3*n^2 := by nlinarith
  calc
    _ ≤ 10000000000000*(W+B+10)^3*n^2+
      10000000000000*(W+B+10)^3*
        (2*f.cyclic*FoldedBackendExecution.outerSize n (FoldedBackendExecution.physicalFold f)*
          FoldedBackendExecution.middleSize h (FoldedBackendExecution.physicalFold f)) := by
      apply Nat.add_le_add
      · exact he.trans (Nat.mul_le_mul_right (n^2)
          (Nat.mul_le_mul_right ((W+B+10)^3) (by decide : (1000:ℕ)≤10000000000000)))
      · exact hs.trans (Nat.mul_le_mul_right _
          (Nat.mul_le_mul_right ((W+B+10)^3) (by decide : (3000000000000:ℕ)≤10000000000000)))
    _ = _ := by ring

#print axioms coordinates_cost
#print axioms coefficient_cost
#print axioms formSources_cost
#print axioms encode_and_formSources_cost

end ThinMatrix.BinaryFoldedFormationCost
