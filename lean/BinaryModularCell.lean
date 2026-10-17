import BinaryCell
import BinaryMultiplierAdapter

/-! Modular and comparison operations on already stored binary coefficient
cells. Executable definitions consume Boolean lists only; integer views occur
in refinement and width proofs. No intermediate integer-to-bits conversion
is used. -/

namespace ThinMatrix.BinaryModularCell

open IntegerArithmetic BinaryCell

def one : Cell := ⟨⟨false,[true]⟩,by decide⟩
def two : Cell := ⟨⟨false,[false,true]⟩,by decide⟩

@[simp] theorem one_view : view one = 1 := rfl
@[simp] theorem two_view : view two = 2 := rfl
theorem one_size : (view one).natAbs.size ≤ 2 := by decide
theorem two_size : (view two).natAbs.size ≤ 2 := by decide

def floor (d x : Cell) : Result Cell :=
  let out := FFTBitCost.binaryFloor d.bits.magnitude x.bits
  ⟨⟨out.1,FFTBitCost.binaryFloor_canonical d.bits.magnitude x.bits⟩,out.2⟩

theorem magnitude_value (x : Cell) : value x.bits.magnitude = (view x).natAbs :=
  (signedValue_natAbs x.bits).symm

theorem magnitude_cast (x : Cell) (hx : 0 ≤ view x) :
    (value x.bits.magnitude : ℤ) = view x := by
  rw [magnitude_value]
  exact Int.natAbs_of_nonneg hx

@[simp] theorem floor_view (d x : Cell) (hd : 0 ≤ view d) :
    view (floor d x).value = view x / view d := by
  change signedValue (FFTBitCost.binaryFloor d.bits.magnitude x.bits).1 = _
  rw [FFTBitCost.binaryFloor_correct,magnitude_cast d hd]
  rfl

theorem floor_size (d x : Cell) (hd : 0 ≤ view d) :
    (view (floor d x).value).natAbs.size ≤ (view x).natAbs.size := by
  rw [floor_view d x hd]
  exact Nat.size_le_size (Int.natAbs_ediv_le_natAbs _ _)

theorem floor_price_square (B : ℕ) (d x : Cell)
    (hd : (view d).natAbs.size ≤ B) (hx : (view x).natAbs.size ≤ B) :
    (floor d x).bitSteps ≤ 1024*(B+1)^2 := by
  have h := FFTBitCost.binaryFloor_cost d.bits.magnitude x.bits
  rw [canonical d,canonical x] at h
  have hm : max (view x).natAbs.size (view d).natAbs.size ≤ B := max_le hx hd
  change (FFTBitCost.binaryFloor d.bits.magnitude x.bits).2 ≤ _
  calc
    _ ≤ 256*(max (view x).natAbs.size (view d).natAbs.size+2)^2 := h
    _ ≤ 256*(2*(B+1))^2 := Nat.mul_le_mul_left _
      (Nat.pow_le_pow_left (by omega) 2)
    _ = _ := by ring

theorem floor_price (B : ℕ) (d x : Cell)
    (hd : (view d).natAbs.size ≤ B) (hx : (view x).natAbs.size ≤ B) :
    (floor d x).bitSteps ≤ 100000*(B+1)^3 := by
  have h := floor_price_square B d x hd hx
  have hp : (B+1)^2 ≤ (B+1)^3 := Nat.pow_le_pow_right (by omega) (by decide)
  nlinarith

/-- The quotient is formed once, reused in the product, and returned together
with the Euclidean remainder. Stored input charge tags are not replayed. -/
def split (d x : Cell) : Result (Cell × Cell) :=
  let quotient := floor d x
  let multiple := BinaryCell.mul d quotient.value
  let rest := BinaryCell.sub x multiple.value
  ⟨(quotient.value,rest.value),quotient.bitSteps+multiple.bitSteps+rest.bitSteps+4⟩

@[simp] theorem split_quotient_view (d x : Cell) (hd : 0 ≤ view d) :
    view (split d x).value.1 = view x / view d := floor_view d x hd

@[simp] theorem split_remainder_view (d x : Cell) (hd : 0 < view d) :
    view (split d x).value.2 = view x % view d := by
  simp only [split,BinaryCell.sub_view,BinaryCell.mul_view,floor_view d x hd.le]
  exact (Int.emod_def _ _).symm

def remainder (d x : Cell) : Result Cell :=
  let result := split d x
  ⟨result.value.2,result.bitSteps⟩

@[simp] theorem remainder_view (d x : Cell) (hd : 0 < view d) :
    view (remainder d x).value = view x % view d := split_remainder_view d x hd

theorem split_quotient_size (B : ℕ) (d x : Cell) (hd : 0 ≤ view d)
    (hx : (view x).natAbs.size ≤ B) :
    (view (split d x).value.1).natAbs.size ≤ B := (floor_size d x hd).trans hx

theorem split_remainder_nonneg (d x : Cell) (hd : 0 < view d) :
    0 ≤ view (split d x).value.2 := by
  rw [split_remainder_view d x hd]
  exact Int.emod_nonneg _ (ne_of_gt hd)

theorem split_remainder_lt (d x : Cell) (hd : 0 < view d) :
    view (split d x).value.2 < view d := by
  rw [split_remainder_view d x hd]
  exact Int.emod_lt_of_pos _ hd

theorem split_remainder_size (B : ℕ) (d x : Cell) (hd : 0 < view d)
    (hdb : (view d).natAbs.size ≤ B) :
    (view (split d x).value.2).natAbs.size ≤ B := by
  apply (Nat.size_le_size _).trans hdb
  exact (Int.natAbs_lt_natAbs_of_nonneg_of_lt (split_remainder_nonneg d x hd)
    (split_remainder_lt d x hd)).le

theorem split_product_size (B : ℕ) (d x : Cell) (hd : 0 ≤ view d)
    (hdb : (view d).natAbs.size ≤ B) (hx : (view x).natAbs.size ≤ B) :
    (view (BinaryCell.mul d (floor d x).value).value).natAbs.size ≤ 2*B := by
  rw [BinaryCell.mul_view,Int.natAbs_mul]
  exact (BinaryMultiplierAdapter.size_mul _ _).trans (by
    have hq := (floor_size d x hd).trans hx
    omega)

theorem split_price_square (B : ℕ) (d x : Cell) (hd : 0 < view d)
    (hdb : (view d).natAbs.size ≤ B) (hx : (view x).natAbs.size ≤ B) :
    (split d x).bitSteps ≤ 6000*(B+1)^2 := by
  have hq := floor_price_square B d x hdb hx
  have hqw := (floor_size d x hd.le).trans hx
  have hm := BinaryCell.mul_price B d (floor d x).value hdb hqw
  have hmw := split_product_size B d x hd.le hdb hx
  have hs := BinaryCell.sub_price (2*B) x (BinaryCell.mul d (floor d x).value).value
    (hx.trans (by omega)) hmw
  unfold BackendScalarBits.backendScalarUnit BackendScalarBits.scalarUnit at hm hs
  change (floor d x).bitSteps+(BinaryCell.mul d (floor d x).value).bitSteps+
    (BinaryCell.sub x (BinaryCell.mul d (floor d x).value).value).bitSteps+4 ≤ _
  nlinarith

theorem split_price (B : ℕ) (d x : Cell) (hd : 0 < view d)
    (hdb : (view d).natAbs.size ≤ B) (hx : (view x).natAbs.size ≤ B) :
    (split d x).bitSteps ≤ 100000*(B+1)^3 := by
  have h := split_price_square B d x hd hdb hx
  have hp : (B+1)^2 ≤ (B+1)^3 := Nat.pow_le_pow_right (by omega) (by decide)
  nlinarith

theorem remainder_price (B : ℕ) (d x : Cell) (hd : 0 < view d)
    (hdb : (view d).natAbs.size ≤ B) (hx : (view x).natAbs.size ≤ B) :
    (remainder d x).bitSteps ≤ 100000*(B+1)^3 := split_price B d x hd hdb hx

theorem isEmpty_true (x : Cell) : x.bits.magnitude.isEmpty = true ↔ view x = 0 := by
  have hc := canonical x
  cases he : x.bits.magnitude with
  | nil =>
      have hz : view x = 0 := by simp [view,BinaryArrayFFT.Integer.view,signedValue,he,value]
      simp [hz]
  | cons b bs =>
      have hn : view x ≠ 0 := by
        intro hz
        rw [he,hz] at hc
        simp at hc
      simp [hn]

def equal (a b : Cell) : Result Bool :=
  let difference := BinaryCell.sub a b
  ⟨difference.value.bits.magnitude.isEmpty,difference.bitSteps+1⟩

@[simp] theorem equal_true (a b : Cell) : (equal a b).value = true ↔ view a = view b := by
  simp only [equal,isEmpty_true,BinaryCell.sub_view,sub_eq_zero]

theorem equal_view (a b : Cell) : (equal a b).value = decide (view a = view b) := by
  have h := equal_true a b
  cases he : (equal a b).value <;> simp_all

theorem equal_price (B : ℕ) (a b : Cell)
    (ha : (view a).natAbs.size ≤ B) (hb : (view b).natAbs.size ≤ B) :
    (equal a b).bitSteps ≤ 100000*(B+1)^3 := by
  have h := BinaryCell.sub_price B a b ha hb
  unfold BackendScalarBits.backendScalarUnit BackendScalarBits.scalarUnit at h
  have hp : (B+1)^2 ≤ (B+1)^3 := Nat.pow_le_pow_right (by omega) (by decide)
  change (BinaryCell.sub a b).bitSteps+1 ≤ _
  nlinarith

def lessUnsigned (x y : Cell) : Result Bool :=
  let difference := subCounted x.bits.magnitude y.bits.magnitude false
  ⟨difference.1.2,difference.2⟩

@[simp] theorem lessUnsigned_true (x y : Cell) (hx : 0 ≤ view x) (hy : 0 ≤ view y) :
    (lessUnsigned x y).value = true ↔ view x < view y := by
  simp only [lessUnsigned,(subCounted_projections _ _ _).1]
  rw [subBits_borrow]
  rw [← Int.ofNat_lt,magnitude_cast x hx,magnitude_cast y hy]

theorem lessUnsigned_view (x y : Cell) (hx : 0 ≤ view x) (hy : 0 ≤ view y) :
    (lessUnsigned x y).value = decide (view x < view y) := by
  have h := lessUnsigned_true x y hx hy
  cases he : (lessUnsigned x y).value <;> simp_all

theorem lessUnsigned_price (x y : Cell) :
    (lessUnsigned x y).bitSteps = 12*max (view x).natAbs.size (view y).natAbs.size+1 := by
  simp only [lessUnsigned,(subCounted_projections _ _ _).2,columnSteps_eq,canonical]

def decodeUnsigned (x : Cell) : Result ℕ := BinaryMultiplierAdapter.decodeNat x.bits.magnitude

@[simp] theorem decodeUnsigned_value (x : Cell) : (decodeUnsigned x).value = (view x).natAbs := by
  rw [decodeUnsigned,BinaryMultiplierAdapter.decodeNat_value,magnitude_value]

theorem decodeUnsigned_cast (x : Cell) (hx : 0 ≤ view x) :
    ((decodeUnsigned x).value : ℤ) = view x := by
  rw [decodeUnsigned_value]
  exact Int.natAbs_of_nonneg hx

theorem decodeUnsigned_view (x : Cell) (hx : 0 ≤ view x) :
    (decodeUnsigned x).value = (view x).toNat := by
  exact_mod_cast (decodeUnsigned_cast x hx).trans (Int.toNat_of_nonneg hx).symm

theorem decodeUnsigned_price (B : ℕ) (x : Cell) (hx : (view x).natAbs.size ≤ B) :
    (decodeUnsigned x).bitSteps ≤ 8*(B+1)^2 := by
  have h := BinaryMultiplierAdapter.decodeNat_cost x.bits.magnitude
  rw [canonical x] at h
  exact h.trans (by gcongr)

def half (x : Cell) : Result Cell := floor two x

@[simp] theorem half_view (x : Cell) : view (half x).value = view x / 2 :=
  floor_view two x (by decide)

theorem half_price (B : ℕ) (x : Cell) (hx : (view x).natAbs.size ≤ B) :
    (half x).bitSteps ≤ 100000*(B+3)^3 := by
  exact (floor_price (B+2) two x (two_size.trans (by omega)) (hx.trans (by omega))).trans_eq (by rfl)

def signedLess (a b : Cell) : Result Bool :=
  let difference := BinaryCell.sub a b
  ⟨difference.value.bits.negative && !difference.value.bits.magnitude.isEmpty,
    difference.bitSteps+4⟩

theorem negative_nonempty_true (x : Cell) :
    (x.bits.negative && !x.bits.magnitude.isEmpty) = true ↔ view x < 0 := by
  have hz := isEmpty_true x
  cases hn : x.bits.negative with
  | false =>
      have hv : 0 ≤ view x := by simp [view,BinaryArrayFFT.Integer.view,signedValue,hn]
      simp [not_lt_of_ge hv]
  | true =>
      have hv : view x ≤ 0 := by simp [view,BinaryArrayFFT.Integer.view,signedValue,hn]
      have hnot (b : Bool) : (!b) = true ↔ ¬b = true := by cases b <;> decide
      simp only [Bool.true_and]
      rw [hnot,hz]
      omega

theorem add_size (a b : Cell) :
    (view (BinaryCell.add a b).value).natAbs.size ≤
      max (view a).natAbs.size (view b).natAbs.size+1 := by
  have h := signedAddIntCounted_size (view a) (view b)
  rwa [signedAddIntCounted_correct,← BinaryCell.add_view] at h

theorem sub_size (a b : Cell) :
    (view (BinaryCell.sub a b).value).natAbs.size ≤
      max (view a).natAbs.size (view b).natAbs.size+1 := by
  have h := signedAddIntCounted_size (view a) (-view b)
  rw [signedAddIntCounted_correct] at h
  simpa only [BinaryCell.sub_view,sub_eq_add_neg,Int.natAbs_neg] using h

theorem mul_size (a b : Cell) :
    (view (BinaryCell.mul a b).value).natAbs.size ≤
      (view a).natAbs.size+(view b).natAbs.size := by
  rw [BinaryCell.mul_view,Int.natAbs_mul]
  exact BinaryMultiplierAdapter.size_mul _ _

theorem remainder_size (d x : Cell) (hd : 0 < view d) :
    (view (remainder d x).value).natAbs.size ≤ (view d).natAbs.size :=
  split_remainder_size _ d x hd le_rfl

@[simp] theorem signedLess_true (a b : Cell) :
    (signedLess a b).value = true ↔ view a < view b := by
  simp only [signedLess,negative_nonempty_true,BinaryCell.sub_view,sub_neg]

theorem signedLess_price (B : ℕ) (a b : Cell)
    (ha : (view a).natAbs.size ≤ B) (hb : (view b).natAbs.size ≤ B) :
    (signedLess a b).bitSteps ≤ 100000*(B+1)^3 := by
  have h := BinaryCell.sub_price B a b ha hb
  unfold BackendScalarBits.backendScalarUnit BackendScalarBits.scalarUnit at h
  have hp : (B+1)^2 ≤ (B+1)^3 := Nat.pow_le_pow_right (by omega) (by decide)
  change (BinaryCell.sub a b).bitSteps+4 ≤ _
  nlinarith

theorem signedLess_view (a b : Cell) :
    (signedLess a b).value = decide (view a < view b) := by
  have h := signedLess_true a b
  cases he : (signedLess a b).value <;> simp_all

/- Original/public address digits may be divided and decoded at the
boundary. Intermediate source arithmetic instead retains `split` cells. -/
namespace UnsignedBits
open BinaryMultiplierAdapter FFTBitCost

def unsignedSplit (divisor input : List Bool) : BinaryResult (ℕ × ℕ) :=
  let division := divideCounted divisor input
  let quotient := decodeNat division.1.1
  let remainder := decodeNat division.1.2
  ⟨(quotient.value,remainder.value),
    division.2+quotient.bitSteps+remainder.bitSteps+4⟩

theorem quotient_length (divisor input : List Bool) :
    (divideCounted divisor input).1.1.length = input.length := by
  rw [(divideCounted_projections divisor input).1]
  exact divideBits_quotient_length divisor input

theorem remainder_length (divisor input : List Bool) :
    (divideCounted divisor input).1.2.length ≤ input.length+divisor.length := by
  rw [(divideCounted_projections divisor input).1]
  exact divideBits_remainder_length divisor input

theorem unsignedSplit_spec (divisor input : List Bool) (hD : 0 < value divisor) :
    value input = (unsignedSplit divisor input).value.1*value divisor+
      (unsignedSplit divisor input).value.2 ∧
      (unsignedSplit divisor input).value.2 < value divisor := by
  simpa only [unsignedSplit,decodeNat_value,(divideCounted_projections divisor input).1]
    using divideBits_correct divisor input hD

@[simp] theorem unsignedSplit_quotient (divisor input : List Bool) (hD : 0 < value divisor) :
    (unsignedSplit divisor input).value.1 = value input / value divisor := by
  simp only [unsignedSplit,decodeNat_value,(divideCounted_projections divisor input).1]
  exact divideBits_quotient divisor input hD

@[simp] theorem unsignedSplit_remainder (divisor input : List Bool) (hD : 0 < value divisor) :
    (unsignedSplit divisor input).value.2 = value input % value divisor := by
  obtain ⟨he,hr⟩ := unsignedSplit_spec divisor input hD
  symm
  rw [he,Nat.add_mod]
  simp [Nat.mul_mod_left,Nat.mod_eq_of_lt hr]

theorem unsignedSplit_value (divisor input : List Bool) (hD : 0 < value divisor) :
    (unsignedSplit divisor input).value =
      (value input / value divisor,value input % value divisor) := by
  apply Prod.ext
  · exact unsignedSplit_quotient divisor input hD
  · exact unsignedSplit_remainder divisor input hD

theorem unsignedSplit_quotient_size (divisor input : List Bool) :
    (unsignedSplit divisor input).value.1.size ≤ input.length := by
  have h := value_size (divideCounted divisor input).1.1
  simpa only [unsignedSplit,decodeNat_value,quotient_length] using h

theorem unsignedSplit_remainder_size (divisor input : List Bool)
    (hD : 0 < value divisor) :
    (unsignedSplit divisor input).value.2.size ≤ divisor.length := by
  exact (Nat.size_le_size (unsignedSplit_spec divisor input hD).2.le).trans
    (value_size divisor)

theorem unsignedSplit_price_quadratic (B : ℕ) (divisor input : List Bool)
    (hi : input.length ≤ B) (hd : divisor.length ≤ B) :
    (unsignedSplit divisor input).bitSteps ≤ 84*(B+1)^2 := by
  have hdivide := divideSteps_bound divisor input
  have hquotient := decodeNat_cost (divideCounted divisor input).1.1
  have hremainder := decodeNat_cost (divideCounted divisor input).1.2
  have hql : (divideCounted divisor input).1.1.length ≤ B := by
    rw [quotient_length]
    exact hi
  have hrl : (divideCounted divisor input).1.2.length ≤ 2*B :=
    (remainder_length divisor input).trans (by omega)
  have hdprice : (divideCounted divisor input).2 ≤ 20*(B+1)*(2*B+1) := by
    rw [(divideCounted_projections divisor input).2]
    apply hdivide.trans
    gcongr
    omega
  have hqprice : (decodeNat (divideCounted divisor input).1.1).bitSteps ≤ 8*(B+1)^2 :=
    hquotient.trans (by gcongr)
  have hrprice : (decodeNat (divideCounted divisor input).1.2).bitSteps ≤ 8*(2*B+1)^2 :=
    hremainder.trans (by gcongr)
  change (divideCounted divisor input).2+
    (decodeNat (divideCounted divisor input).1.1).bitSteps+
    (decodeNat (divideCounted divisor input).1.2).bitSteps+4 ≤ _
  nlinarith

theorem unsignedSplit_price (B : ℕ) (divisor input : List Bool)
    (hi : input.length ≤ B) (hd : divisor.length ≤ B) :
    (unsignedSplit divisor input).bitSteps ≤ 100000*(B+1)^3 := by
  apply (unsignedSplit_price_quadratic B divisor input hi hd).trans
  exact Nat.mul_le_mul (by decide : 84 ≤ 100000)
    (Nat.pow_le_pow_right (by omega : 0 < B+1) (by decide : 2 ≤ 3))

end UnsignedBits

#print axioms floor_view
#print axioms split_remainder_view
#print axioms split_price
#print axioms equal_true
#print axioms lessUnsigned_true
#print axioms signedLess_true
#print axioms decodeUnsigned_view
#print axioms equal_view
#print axioms lessUnsigned_view
#print axioms signedLess_view
#print axioms UnsignedBits.unsignedSplit_value
#print axioms UnsignedBits.unsignedSplit_price

end ThinMatrix.BinaryModularCell
