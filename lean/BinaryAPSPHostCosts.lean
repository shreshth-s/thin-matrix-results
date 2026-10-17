import BinaryAPSPCaller
import AdaptiveQueryBitBounds

/-!
# Bounds for the actual binary min-plus/APSP host

These bounds price the caller's own bit-cell operations. Oracle work remains
the work returned by the same actual calls, summed once by BinaryAPSPCaller.
No statement here identifies Lean evaluator allocation with an array action.
-/

namespace ThinMatrix.BinaryAPSPHostCosts
open BinaryAPSPCaller
open scoped BigOperators
set_option maxHeartbeats 4000000
set_option maxRecDepth 4000

abbrev bits (c : Cell) : ℕ := (BinaryCell.view c).natAbs.size

local macro "bit_omega" : tactic => `(tactic| first | (unfold bits at *; omega) | omega)
def Fits {n : ℕ} (B : ℕ) (A : IntTable n) : Prop :=
  ∀ i j, bits (StoredMinPlusAPSP.decode A i j) ≤ B
def OptionalFits {n : ℕ} (B : ℕ) (A : OptionalTable n) : Prop :=
  ∀ i j c, StoredMinPlusAPSP.decode A i j = some c → bits c ≤ B

@[simp] theorem zero_bits : bits BinaryCell.zero = 0 := rfl
theorem one_bits : bits one ≤ 2 := BinaryModularCell.one_size
theorem two_bits : bits two ≤ 2 := BinaryModularCell.two_size

theorem half_fits {n : ℕ} (B : ℕ) (A : IntTable n) (hA : Fits B A) :
    Fits B (half A).value := by
  intro i j
  simp only [half,tabulate_get]
  exact (BinaryModularCell.floor_size two _ (by decide)).trans (hA i j)

theorem refineCell_size (C : ℕ) (hC : 2 ≤ C) (c : Cell) (hc : bits c ≤ C) (z0 z1 : Bool) :
    bits (refineCell c z0 z1).value ≤ C+2 := by
  have hd : bits (BinaryCell.add c c).value ≤ C+1 :=
    (BinaryModularCell.add_size c c).trans (by simp only [max_self]; bit_omega)
  have ha (offset : Cell) (ho : bits offset ≤ 2) :
      bits (BinaryCell.add (BinaryCell.add c c).value offset).value ≤ C+2 :=
    (BinaryModularCell.add_size _ _).trans (by bit_omega)
  cases z0 <;> cases z1 <;> simp only [refineCell, Bool.false_eq_true, if_false, if_true]
  · exact ha two two_bits
  · exact ha one one_bits
  · exact hd.trans (by bit_omega)
  · exact hd.trans (by bit_omega)

/-- Boolean oracle answers cannot make this digit-refinement accumulator
grow faster than two additional bits per level. -/
theorem bitScale_fits {n : ℕ} {Payload : Type} (O : Oracle n Payload) (d : ℕ)
    (A B : IntTable n) : Fits (2*d+2) (bitScale O d A B).value := by
  induction d generalizing A B with
  | zero =>
    intro i j
    simp [bitScale,tabulate_get,bits,BinaryCell.zero_view]
  | succ d ih =>
    intro i j
    have hc := ih (half A).value (half B).value i j
    simpa only [bitScale,tabulate_get, Nat.mul_add, Nat.mul_one, Nat.add_assoc] using
      refineCell_size (2*d+2) (by bit_omega)
        (StoredMinPlusAPSP.decode (bitScale O d (half A).value (half B).value).value i j)
        hc _ _

def scalarPrice (W : ℕ) : ℕ := 1000000*(W+3)^3+10
def tablePrice (n W : ℕ) : ℕ := scalarPrice W+8*(n.size+1)+4

theorem primitive_price_le (W : ℕ) :
    3*BackendScalarBits.backendScalarUnit W+6 ≤ scalarPrice W := by
  have hp : (W+1)^2 ≤ (W+3)^3 :=
    (Nat.pow_le_pow_left (by bit_omega) 2).trans
      (Nat.pow_le_pow_right (by bit_omega) (by decide))
  unfold scalarPrice BackendScalarBits.backendScalarUnit BackendScalarBits.scalarUnit
  nlinarith

theorem half_price_le (W : ℕ) (c : Cell) (hc : bits c ≤ W) :
    (halfCell c).bitSteps ≤ scalarPrice W := by
  have h := BinaryModularCell.half_price W c hc
  unfold scalarPrice
  nlinarith

theorem targetCell_price_le (C W : ℕ) (hC : 2 ≤ C) (hW : C+2 ≤ W)
    (c offset : Cell) (hc : bits c ≤ C) (ho : bits offset ≤ 2) :
    (targetCell c offset).bitSteps ≤ scalarPrice W := by
  have hd : bits (BinaryCell.add c c).value ≤ C+1 :=
    (BinaryModularCell.add_size c c).trans (by simp only [max_self]; bit_omega)
  have ha : bits (BinaryCell.add (BinaryCell.add c c).value offset).value ≤ C+2 :=
    (BinaryModularCell.add_size _ _).trans (by bit_omega)
  have hp0 := BinaryCell.add_price W c c (by bit_omega) (by bit_omega)
  have hp1 := BinaryCell.add_price W (BinaryCell.add c c).value offset (by bit_omega) (by bit_omega)
  have hp2 := BinaryCell.sub_price W BinaryCell.zero
    (BinaryCell.add (BinaryCell.add c c).value offset).value (by simp) (by bit_omega)
  have hp := primitive_price_le W
  change (BinaryCell.add c c).bitSteps+
    (BinaryCell.add (BinaryCell.add c c).value offset).bitSteps+
    (BinaryCell.sub BinaryCell.zero (BinaryCell.add (BinaryCell.add c c).value offset).value).bitSteps ≤ _
  bit_omega

theorem refineCell_price_le (C W : ℕ) (hC : 2 ≤ C) (hW : C+1 ≤ W)
    (c : Cell) (hc : bits c ≤ C) (z0 z1 : Bool) :
    (refineCell c z0 z1).bitSteps ≤ scalarPrice W := by
  have hd : bits (BinaryCell.add c c).value ≤ C+1 :=
    (BinaryModularCell.add_size c c).trans (by simp only [max_self]; bit_omega)
  have hp0 := BinaryCell.add_price W c c (by bit_omega) (by bit_omega)
  have hp1 (offset : Cell) (ho : bits offset ≤ 2) :=
    BinaryCell.add_price W (BinaryCell.add c c).value offset (by bit_omega) (by bit_omega)
  have hp := primitive_price_le W
  have hone := hp1 one one_bits
  have htwo := hp1 two two_bits
  cases z0 <;> cases z1 <;> simp only [refineCell, Bool.false_eq_true, if_false, if_true] <;> bit_omega

theorem tablePrice_ge (n W : ℕ) : 1 ≤ tablePrice n W ∧ W ≤ tablePrice n W := by
  have hp : W+3 ≤ (W+3)^3 := le_self_pow₀ (by bit_omega) (by decide)
  unfold tablePrice scalarPrice
  constructor <;> nlinarith

theorem bitScale_hostBits_le {n : ℕ} {Payload : Type} (hn : 0 < n)
    (O : Oracle n Payload) (d P W : ℕ) (A B : IntTable n)
    (hA : Fits P A) (hB : Fits P B) (hW : P+2*d+10 ≤ W) :
    (bitScale O d A B).hostBits ≤ (6*d+1)*n^2*tablePrice n W := by
  induction d generalizing A B with
  | zero =>
    have ht := tabulate_price (n:=n) (fun _ _ => (⟨BinaryCell.zero,1⟩ : Result Cell))
      (scalarPrice W) (by intro i j; change 1 ≤ scalarPrice W; unfold scalarPrice; bit_omega)
    simpa only [bitScale, Nat.mul_zero, Nat.zero_add, Nat.one_mul, tablePrice] using ht
  | succ d ih =>
    let coarse := bitScale O d (half A).value (half B).value
    have hcoarse := ih (half A).value (half B).value (half_fits P A hA) (half_fits P B hB) (by bit_omega)
    have hfits : Fits (2*d+2) coarse.value := bitScale_fits O d _ _
    have hhalfA : (half A).bitSteps ≤ n^2*tablePrice n W := by
      apply tabulate_price
      intro i j
      exact half_price_le W _ ((hA i j).trans (by bit_omega))
    have hhalfB : (half B).bitSteps ≤ n^2*tablePrice n W := by
      apply tabulate_price
      intro i j
      exact half_price_le W _ ((hB i j).trans (by bit_omega))
    have htarget (offset : Cell) (ho : bits offset ≤ 2) :
        (tabulate (fun i j => targetCell (StoredMinPlusAPSP.decode coarse.value i j) offset)).bitSteps ≤
          n^2*tablePrice n W := by
      apply tabulate_price
      intro i j
      exact targetCell_price_le (2*d+2) W (by bit_omega) (by bit_omega) _ offset (hfits i j) ho
    have ht0 := htarget BinaryCell.zero (by simp)
    have ht1 := htarget one one_bits
    have hrefine (Z0 Z1 : BoolTable n) :
        (tabulate (fun i j => refineCell (StoredMinPlusAPSP.decode coarse.value i j)
          (StoredMinPlusAPSP.decode Z0 i j) (StoredMinPlusAPSP.decode Z1 i j))).bitSteps ≤
            n^2*tablePrice n W := by
      apply tabulate_price
      intro i j
      exact refineCell_price_le (2*d+2) W (by bit_omega) (by bit_omega) _ (hfits i j) _ _
    have hr := hrefine
      (O A B (tabulate (fun i j => targetCell (StoredMinPlusAPSP.decode coarse.value i j) BinaryCell.zero)).value).answers
      (O A B (tabulate (fun i j => targetCell (StoredMinPlusAPSP.decode coarse.value i j) one)).value).answers
    have hcontrol : coarse.calls.length+8 ≤ n^2*tablePrice n W := by
      have hlen : coarse.calls.length = 2*d := bitScale_calls O d _ _
      have hwidth : 2*d+8 ≤ tablePrice n W := (by bit_omega : 2*d+8 ≤ W).trans (tablePrice_ge n W).2
      have hbase : tablePrice n W ≤ n^2*tablePrice n W :=
        Nat.le_mul_of_pos_left _ (by positivity)
      bit_omega
    change coarse.hostBits+(half A).bitSteps+(half B).bitSteps+
      (tabulate (fun i j => targetCell (StoredMinPlusAPSP.decode coarse.value i j) BinaryCell.zero)).bitSteps+
      (tabulate (fun i j => targetCell (StoredMinPlusAPSP.decode coarse.value i j) one)).bitSteps+
      (tabulate (fun i j => refineCell (StoredMinPlusAPSP.decode coarse.value i j)
        (StoredMinPlusAPSP.decode (O A B (tabulate (fun i j => targetCell
          (StoredMinPlusAPSP.decode coarse.value i j) BinaryCell.zero)).value).answers i j)
        (StoredMinPlusAPSP.decode (O A B (tabulate (fun i j => targetCell
          (StoredMinPlusAPSP.decode coarse.value i j) one)).value).answers i j))).bitSteps+
      coarse.calls.length+8 ≤ _
    change coarse.hostBits ≤ _ at hcoarse
    nlinarith only [hcoarse,hhalfA,hhalfB,ht0,ht1,hr,hcontrol]

#print axioms half_fits
#print axioms refineCell_size
#print axioms bitScale_fits
#print axioms targetCell_price_le
#print axioms refineCell_price_le
#print axioms bitScale_hostBits_le

end ThinMatrix.BinaryAPSPHostCosts
