import PaddedMatrix

set_option autoImplicit false
set_option exponentiation.threshold 1000

/-! Exact integer size bounds for padding into the extracted CW base.
The native logarithm and recursive address arithmetic are not priced here;
the bit bound covers the binary scalar program and the indexed copies retain
separate control charges. This is not a full APSP resource theorem. -/
namespace ThinMatrix.PaddedMatrixScale
open scoped BigOperators
open CWHomogeneousCopies

/-- One extra fixed-base level handles upward rounding of the first axis. -/
def depth (s D : ℕ) := Nat.clog (rows s) D+1

theorem bases_gt_one (s : ℕ) (hs : 0 < s) : 1 < cols s ∧ 1 < rows s ∧ 1 < inners s := by
  unfold cols rows inners
  refine ⟨?_,?_,?_⟩ <;> apply one_lt_pow₀ (by decide : (1:ℕ)<16) <;> omega

theorem aspect (s : ℕ) : (cols s)^500=(rows s)^861 ∧ inners s=(rows s)^15 := by
  simpa only [CWRectangularRanks.dimensions,pow_one] using CWRectangularRanks.aspect s 1

theorem fits (s D n p : ℕ) (hs : 0 < s)
    (hn : (n-1)^500≤D^861) (hp : p≤D^15) :
    n≤(cols s)^depth s D ∧ D≤(rows s)^depth s D ∧ p≤(inners s)^depth s D := by
  have hb := bases_gt_one s hs
  have ha := aspect s
  let k := Nat.clog (rows s) D
  have hD : D≤rows s^k := Nat.le_pow_clog hb.2.1 D
  have hfirst : n-1≤cols s^k := by
    have hpow := hn.trans (Nat.pow_le_pow_left hD 861)
    have eqpow : (rows s^k)^861=(cols s^k)^500 := by
      calc
        _ = (rows s^861)^k := by rw [←pow_mul,←pow_mul,Nat.mul_comm k 861]
        _ = (cols s^500)^k := by rw [ha.1]
        _ = _ := by rw [←pow_mul,←pow_mul,Nat.mul_comm 500 k]
    rw [eqpow] at hpow
    exact (Nat.pow_le_pow_iff_left (by decide : 500≠0)).mp hpow
  refine ⟨?_,?_,?_⟩
  · have h1 : 1≤cols s^k := one_le_pow₀ hb.1.le
    have hn' : n≤cols s^k+1 := by omega
    have hc : 2≤cols s := hb.1
    calc
      n≤cols s^k+1 := hn'
      _ ≤ 2*cols s^k := by omega
      _ ≤ cols s*cols s^k := Nat.mul_le_mul_right _ hc
      _ = _ := by simp only [depth,k,pow_succ']
  · exact hD.trans (Nat.pow_le_pow_right hb.2.1.le (Nat.le_succ k))
  · have hd := hp.trans (Nat.pow_le_pow_left hD 15)
    rw [←pow_mul,Nat.mul_comm k 15,pow_mul,←ha.2] at hd
    exact hd.trans (Nat.pow_le_pow_right hb.2.2.le (Nat.le_succ k))

theorem clog_power_le (q D : ℕ) (hq : 1 < q) (hD : 1≤D) :
    q^Nat.clog q D≤q*D := by
  by_cases hd : D=1
  · simpa [hd] using hq.le
  · have hd' : 1 < D := by omega
    have hc := Nat.clog_pos hq hd'
    have hh := Nat.pow_pred_clog_lt_self hq hd'
    calc
      _ = q*q^(Nat.clog q D-1) := by
        rw [←pow_succ',Nat.sub_add_cancel hc]
      _ ≤ q*D := Nat.mul_le_mul_left _ hh.le

theorem size_bound (s D : ℕ) (hs : 0 < s) (hD : 1≤D) :
    rows s^depth s D≤(rows s)^2*D ∧ depth s D≤D.size+1 := by
  have hb := (bases_gt_one s hs).2.1
  constructor
  · have hh := Nat.mul_le_mul_left (rows s) (clog_power_le (rows s) D hb hD)
    simpa only [depth,pow_succ',pow_two,pow_zero,one_mul,mul_assoc] using hh
  · have hh : D≤rows s^D.size :=
      (AdaptiveBitBounds.nat_le_pow_size D).trans (Nat.pow_le_pow_left hb D.size)
    exact Nat.add_le_add_right (Nat.clog_le_of_le_pow hh) 1

open RecursiveTable (Table fin prod read)
open BinaryCell
variable {n D p : ℕ}

noncomputable def execute (s : ℕ) (hs : 0 < s) (h : CWTargetExtractionRate.Sample s)
    (ht : 0<CWHomogeneousCopies.copies s h) (hn : (n-1)^500≤D^861) (hp : p≤D^15)
    (x : Table (PaddedMatrix.matrix n D) Cell) (y : Table (PaddedMatrix.matrix D p) Cell) :=
  let hf := fits s D n p hs hn hp
  PaddedMatrix.execute (fin (cols s)) (fin (rows s)) (fin (inners s)) ht
    (CWRetainedArithmetic.base s h) (depth s D) hf.1 hf.2.2 x y

theorem execute_correct (s : ℕ) (hs : 0 < s) (h : CWTargetExtractionRate.Sample s)
    (ht : 0<CWHomogeneousCopies.copies s h) (hn : (n-1)^500≤D^861) (hp : p≤D^15)
    (x : Table (PaddedMatrix.matrix n D) Cell) (y : Table (PaddedMatrix.matrix D p) Cell)
    (i : Fin n×Fin p) :
    view (read (execute s hs h ht hn hp x y).value i)=
      ∑ j : Fin D,view (read x (i.1,j))*view (read y (j,i.2)) :=
  PaddedMatrix.execute_correct _ _ _ ht _ (CWRetainedArithmetic.base_total s h) _
    (fits s D n p hs hn hp).1 (fits s D n p hs hn hp).2.1 (fits s D n p hs hn hp).2.2 x y i

theorem execute_bits (s H : ℕ) (hs : 0 < s) (hH : 1≤H) (h : CWTargetExtractionRate.Sample s)
    (ht : 0<CWHomogeneousCopies.copies s h) (hn : (n-1)^500≤D^861) (hp : p≤D^15)
    (x : Table (PaddedMatrix.matrix n D) Cell) (y : Table (PaddedMatrix.matrix D p) Cell)
    (hx : BinaryRetainedBounds.Bounded x H) (hy : BinaryRetainedBounds.Bounded y H) :
    (execute s hs h ht hn hp x y).bitSteps≤BinaryRecursiveCost.bits (CWRetainedArithmetic.base s h) (depth s D) H :=
  PaddedMatrix.execute_bits _ _ _ ht _ _ H (fits s D n p hs hn hp).1
    (fits s D n p hs hn hp).2.2 hH x y hx hy

#print axioms execute_correct
#print axioms execute_bits
#print axioms bases_gt_one
#print axioms aspect
#print axioms fits
#print axioms clog_power_le
#print axioms size_bound
end ThinMatrix.PaddedMatrixScale
