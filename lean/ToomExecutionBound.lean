import ToomCook
import IntegerArithmetic
import ToomBitCost
import ToomLocalBudget
import ToomInterpolationCost

/-!
# Global bit-complexity assembly for the materialized Toom program

The recurrence and padding lemmas below are purely mathematical. The public
execution theorem will instantiate them with the actual array-program counter
and the Boolean-list integer arithmetic counter; no runtime domination axiom
or cost assigned independently of execution is introduced.
-/

namespace ThinMatrix.ToomExecutionBound

noncomputable section

open scoped BigOperators
open ThinMatrix.ToomCook

set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

/-- Elementary binary-size multiplication bound, including zero inputs. -/
theorem size_mul_le (a b : ℕ) : (a*b).size ≤ a.size+b.size := by
  apply Nat.size_le.mpr
  calc
    a*b ≤ 2^a.size*b := Nat.mul_le_mul_right b (Nat.lt_size_self a).le
    _ < 2^a.size*2^b.size := Nat.mul_lt_mul_of_pos_left (Nat.lt_size_self b) (by positivity)
    _ = 2^(a.size+b.size) := (pow_add _ _ _).symm

/-- Fixed arity-dependent contributions: interpolation weights,
denominator, evaluation powers and address words. The constant is kept
symbolic even for the arity `2^100000000`. -/
def bitSlope (k : ℕ) : ℕ :=
  4*(k.size+(growthConstant k).size+(commonDenominator (2*k-1)).size+10)

/-- A global bound which absorbs the coefficient growth of each actual
recursive evaluation step rather than squaring the bound recursively. -/
def bitBudget (k s A : ℕ) : ℕ := bitSlope k*(s+1)+2*A.size+10

theorem bitBudget_pos (k s A : ℕ) : 0 < bitBudget k s A := by
  unfold bitBudget
  omega

theorem bitBudget_mono_input (k s A B : ℕ) (hAB : A ≤ B) :
    bitBudget k s A ≤ bitBudget k s B := by
  unfold bitBudget
  have h := Nat.size_le_size hAB
  omega

/-- Child input coefficients are bounded by `growthConstant*k`'s
actual evaluation row sum. Their enlarged input budget is paid by one
unit of parent depth. -/
theorem bitBudget_child (k s A : ℕ) :
    bitBudget k s (growthConstant k*A) ≤ bitBudget k (s+1) A := by
  have h := size_mul_le (growthConstant k) A
  unfold bitBudget bitSlope
  nlinarith

/-- The recurrence derived from a fixed local bit-loop overhead. -/
def bitRecurrence (k c : ℕ) : ℕ → ℕ
  | 0 => c
  | s+1 => (2*k-1)*bitRecurrence k c s+c*k^(s+1)

theorem bitRecurrence_eq (k c s : ℕ) :
    bitRecurrence k c s=c*recurrence (2*k-1) k 1 s := by
  induction s with
  | zero => simp [bitRecurrence,recurrence]
  | succ s ih => simp only [bitRecurrence,recurrence,ih];ring

theorem bitRecurrence_bound (k c s : ℕ) (hk : 2 ≤ k) :
    bitRecurrence k c s ≤ 3*c*(2*k)^s := by
  rw [bitRecurrence_eq]
  have h := toom_recurrence_bound k 1 hk s
  simpa only [show 2*1+1=3 by omega, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
    Nat.mul_le_mul_left c h

/-- All arities `2^B` give the usual exact fixed exponent. -/
theorem bitRecurrence_rpow (B c s : ℕ) (hB : 0 < B) :
    (bitRecurrence (2^B) c s : ℝ) ≤
      (3*c : ℕ)*((((2^B)^s : ℕ) : ℝ)^(1+1/(B:ℝ))) := by
  rw [bitRecurrence_eq,Nat.cast_mul]
  have h := toom_recurrence_rpow B s 1 hB
  have h' := mul_le_mul_of_nonneg_left h (Nat.cast_nonneg c : (0:ℝ) ≤ c)
  norm_num only [Nat.cast_one] at h'
  simpa only [Nat.cast_mul,Nat.cast_ofNat,mul_assoc,mul_comm,mul_left_comm] using h'

/-- Next-arity-power padding has logarithmic recursion depth in `q`. -/
theorem padded_depth_le_size (k q : ℕ) (hk : 2 ≤ k) (hq : 0 < q) :
    Nat.log k q+1 ≤ q.size+1 := by
  have hqpow : q<k^q.size := by
    calc
      q<2^q.size := Nat.lt_size_self q
      _≤k^q.size := Nat.pow_le_pow_left hk _
  have h := Nat.log_lt_of_lt_pow (Nat.ne_of_gt hq) hqpow
  omega

/-- Thus the actual path bit budget is polynomial in the input binary
lengths, with only a fixed arity-dependent multiplier. -/
theorem padded_bitBudget_bound (k q A : ℕ) (hk : 2 ≤ k) (hq : 0 < q) :
    bitBudget k (Nat.log k q+1) A ≤
      (bitSlope k+12)*(q.size+A.size+2) := by
  have hs := padded_depth_le_size k q hk hq
  unfold bitBudget
  nlinarith


/-- The already-proved literal downward-path numerator estimate fits the
single budget for the root's total recursion depth. -/
theorem actual_path_numerator_bits (k S s : ℕ) (hk : 2≤k) (f g : Polynomial ℤ)
    (xs ys : List (ℕ×Fin (2*k-1))) (hlen : ys.length=xs.length)
    (hdepth : s+xs.length ≤ S) (A : ℕ)
    (hf : ToomCook.CoeffBound f A) (hg : ToomCook.CoeffBound g A)
    (d : Fin (2*k-1)) (j : ℕ) :
    ((interpolationNumeratorPolynomial (2*k-1) (fun r=>multiplyInteger k s
      (evaluatedIntegerChunk k (k^s) (evaluationPath k f xs) r)
      (evaluatedIntegerChunk k (k^s) (evaluationPath k g ys) r)) d).coeff j).natAbs.size ≤
      bitBudget k S A := by
  apply (recursive_numerator_path_bits k s hk f g xs ys hlen A hf hg d j).trans
  unfold bitBudget bitSlope
  nlinarith

/-- Mathematical majorant used after the actual local loop-cost theorem
has been instantiated. This definition is not an independently assigned
program counter. -/
def bitMajorant (k c s A : ℕ) : ℕ := bitRecurrence k c s*(bitBudget k s A+1)^3

theorem bitMajorant_step (k c s A : ℕ) :
    (2*k-1)*bitMajorant k c s (growthConstant k*A)+
      c*k^(s+1)*(bitBudget k (s+1) A+1)^3 ≤ bitMajorant k c (s+1) A := by
  unfold bitMajorant
  have hb : (bitBudget k s (growthConstant k*A)+1)^3 ≤
      (bitBudget k (s+1) A+1)^3 :=
    Nat.pow_le_pow_left (Nat.add_le_add_right (bitBudget_child k s A) 1) 3
  calc
    _ ≤ (2*k-1)*(bitRecurrence k c s*(bitBudget k (s+1) A+1)^3)+
        c*k^(s+1)*(bitBudget k (s+1) A+1)^3 := by
      exact Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hb)) _
    _ = _ := by rw [bitRecurrence];ring

theorem bitMajorant_at_length (B c q A : ℕ) (hB : 0<B) (hq : 0<q) :
    (bitMajorant (2^B) c (Nat.log (2^B) q+1) A : ℝ) ≤
      (3*c : ℕ)*((2:ℝ)^B)^(1+1/(B:ℝ))*
        ((bitSlope (2^B)+13 : ℕ) : ℝ)^3*
        (q:ℝ)^(1+1/(B:ℝ))*((q.size+A.size+2 : ℕ) : ℝ)^3 := by
  let k : ℕ:=2^B
  let s : ℕ:=Nat.log k q+1
  have hk : 2≤k := two_le_two_pow B hB
  have hrec := bitRecurrence_rpow B c s hB
  have hp : k^s ≤ k*q := (padded_length_bounds k q hk hq).2
  have hrpow : (((k^s : ℕ) : ℝ)^(1+1/(B:ℝ))) ≤
      (((k*q : ℕ) : ℝ)^(1+1/(B:ℝ))) :=
    Real.rpow_le_rpow (by positivity) (by exact_mod_cast hp) (by positivity)
  have hrec' : (bitRecurrence k c s : ℝ) ≤
      (3*c : ℕ)*(k:ℝ)^(1+1/(B:ℝ))*(q:ℝ)^(1+1/(B:ℝ)) := by
    calc
      _ ≤ (3*c : ℕ)*(((k^s : ℕ) : ℝ)^(1+1/(B:ℝ))) := hrec
      _ ≤ (3*c : ℕ)*(((k*q : ℕ) : ℝ)^(1+1/(B:ℝ))) := by gcongr
      _ = _ := by
        simp only [Nat.cast_mul]
        rw [Real.mul_rpow (by positivity) (by positivity)]
        ring
  have hbits := padded_bitBudget_bound k q A hk hq
  have hbits' : bitBudget k s A+1 ≤ (bitSlope k+13)*(q.size+A.size+2) := by
    dsimp [s]
    nlinarith
  have hbitsReal : ((bitBudget k s A+1 : ℕ) : ℝ)^3 ≤
      ((bitSlope k+13 : ℕ) : ℝ)^3*((q.size+A.size+2 : ℕ) : ℝ)^3 := by
    have hcast : ((bitBudget k s A+1 : ℕ) : ℝ) ≤
        ((bitSlope k+13 : ℕ) : ℝ)*((q.size+A.size+2 : ℕ) : ℝ) := by exact_mod_cast hbits'
    calc
      _ ≤ (((bitSlope k+13 : ℕ) : ℝ)*((q.size+A.size+2 : ℕ) : ℝ))^3 := by gcongr
      _ = _ := mul_pow _ _ _
  unfold bitMajorant
  rw [Nat.cast_mul,Nat.cast_pow]
  have hm := mul_le_mul hrec' hbitsReal (by positivity) (by positivity)
  simpa only [k,Nat.cast_pow,Nat.cast_ofNat,mul_assoc,mul_comm,mul_left_comm] using hm

/-- The certified arithmetic epsilon is the actual fixed Toom arity's
exponent; constants stay symbolic instead of evaluating the enormous arity. -/
theorem fixed_bitMajorant_at_length (c q A : ℕ) (hq : 0<q) :
    (bitMajorant (2^100000000) c (Nat.log (2^100000000) q+1) A : ℝ) ≤
      (3*c : ℕ)*((2:ℝ)^100000000)^(1.00000001:ℝ)*
        ((bitSlope (2^100000000)+13 : ℕ) : ℝ)^3*
        (q:ℝ)^(1.00000001:ℝ)*((q.size+A.size+2 : ℕ) : ℝ)^3 := by
  have h := bitMajorant_at_length 100000000 c q A (by norm_num) hq
  have he : (1:ℝ)+1/(100000000:ℕ)=1.00000001 := by norm_num
  rwa [he] at h


/-- The recursive child is an actual evaluated coefficient array. -/
theorem evaluated_input_size (k h : ℕ) (a : Array ℤ) (r : Fin (2*k-1)) :
    ((ToomBitCost.evaluateCounted ToomBitCost.bitPrimitives k h a r).value).size=h := by
  rw [ToomBitCost.evaluateCounted_value _ ToomBitCost.bitPrimitives_correct]
  exact Array.size_ofFn

theorem evaluated_input_polynomial (k h : ℕ) (hh : 0<h) (a : Array ℤ)
    (r : Fin (2*k-1)) :
    ToomBitCost.arrayPolynomial
      (ToomBitCost.evaluateCounted ToomBitCost.bitPrimitives k h a r).value =
      evaluatedIntegerChunk k h (ToomBitCost.arrayPolynomial a) r := by
  rw [ToomBitCost.evaluateCounted_value _ ToomBitCost.bitPrimitives_correct]
  exact ToomBitCost.arrayPolynomial_ofFn h _ (evaluatedIntegerChunk_natDegree k h hh _ r)

theorem evaluated_input_coeffBound (k h A : ℕ) (hh : 0<h) (a : Array ℤ)
    (ha : ToomCook.CoeffBound (ToomBitCost.arrayPolynomial a) A) (r : Fin (2*k-1)) :
    ToomCook.CoeffBound (ToomBitCost.arrayPolynomial
      (ToomBitCost.evaluateCounted ToomBitCost.bitPrimitives k h a r).value) (growthConstant k*A) := by
  rw [evaluated_input_polynomial k h hh a r]
  simpa only [Nat.cast_mul] using
    evaluatedIntegerChunk_bound k h (ToomBitCost.arrayPolynomial a) r A (by positivity) ha

/-- Input padding materializes each coefficient once, including zero
slots, using actual read/copy/write counters. -/
def padInput (n : ℕ) (a : Array ℤ) : ToomCook.Counted (Array ℤ) :=
  ToomBitCost.tabulateInteger n (fun i=>ToomBitCost.readInteger a i.val)

theorem padInput_value (n : ℕ) (a : Array ℤ) :
    (padInput n a).value=Array.ofFn (fun i : Fin n=>(a[i.val]?).getD 0) := by
  simp only [padInput,ToomBitCost.tabulateInteger_value,ToomBitCost.readInteger]

theorem padInput_size (n : ℕ) (a : Array ℤ) : (padInput n a).value.size=n := by
  rw [padInput_value]
  exact Array.size_ofFn

theorem padInput_polynomial (n : ℕ) (a : Array ℤ) (ha : a.size ≤ n) :
    ToomBitCost.arrayPolynomial (padInput n a).value=ToomBitCost.arrayPolynomial a := by
  ext j
  rw [ToomBitCost.arrayPolynomial_coeff,ToomBitCost.arrayPolynomial_coeff,padInput_value]
  by_cases hj : j<n
  · simp [hj]
  · have hj' : a.size≤j := by omega
    simp [hj,Array.getElem?_eq_none hj']

theorem padInput_operations_bound (n A : ℕ) (a : Array ℤ)
    (ha : ToomCook.CoeffBound (ToomBitCost.arrayPolynomial a) A) :
    (padInput n a).operations ≤ 2*n*(A.size+n.size+2) := by
  rw [padInput,ToomBitCost.tabulateInteger_operations]
  have hbits (i : Fin n) : ((a[i.val]?).getD 0).natAbs.size≤A.size := by
    have h := ha i.val
    rw [ToomBitCost.arrayPolynomial_coeff] at h
    have hz : ((a[i.val]?).getD 0).natAbs≤A := by
      exact_mod_cast (show (((a[i.val]?).getD 0).natAbs : ℤ)≤A by simpa only [Int.natCast_natAbs] using h)
    exact Nat.size_le_size hz
  have haddr (i : Fin n) : i.val.size≤n.size := Nat.size_le_size i.isLt.le
  have hsum : (∑ i : Fin n,
      ((ToomBitCost.readInteger a i.val).operations+
      (ToomBitCost.readInteger a i.val).value.natAbs.size+i.val.size+1)) ≤
      n*(2*(A.size+n.size+1)) := by
    calc
      _ ≤ ∑ _i : Fin n, 2*(A.size+n.size+1) := by
        apply Finset.sum_le_sum
        intro i hi
        simp only [ToomBitCost.readInteger]
        have := hbits i
        have := haddr i
        omega
      _ = _ := by simp
  calc
    _ ≤ n*(2*(A.size+n.size+1))+2*n := Nat.add_le_add_right hsum _
    _ = _ := by ring


theorem bitBudget_eq_program (k s A : ℕ) : bitBudget k s A=ToomBitCost.bitBudget k s A := rfl

/-- Structural induction on the actual executable recursion. The local
counter equalities/inequalities will be supplied by the concrete loop-cost
proof, never by a hypothesis asserting the final near-linear bound. -/
private theorem execute_cost_induction (k c : ℕ) (hk : 2≤k)
    (hbase : ∀ (a b : Array ℤ) (A : ℕ), a.size=1 → b.size=1 →
      ToomCook.CoeffBound (ToomBitCost.arrayPolynomial a) A →
      ToomCook.CoeffBound (ToomBitCost.arrayPolynomial b) A →
      (ToomBitCost.execute ToomBitCost.bitPrimitives k 0 a b).operations ≤
        c*(bitBudget k 0 A+1)^3)
    (hstep : ∀ (s : ℕ) (a b : Array ℤ) (A : ℕ), a.size=k^(s+1) → b.size=k^(s+1) →
      ToomCook.CoeffBound (ToomBitCost.arrayPolynomial a) A →
      ToomCook.CoeffBound (ToomBitCost.arrayPolynomial b) A →
      (ToomBitCost.execute ToomBitCost.bitPrimitives k (s+1) a b).operations ≤
        (∑ r : Fin (2*k-1), (ToomBitCost.execute ToomBitCost.bitPrimitives k s
          (ToomBitCost.evaluateCounted ToomBitCost.bitPrimitives k (k^s) a r).value
          (ToomBitCost.evaluateCounted ToomBitCost.bitPrimitives k (k^s) b r).value).operations)+
          c*k^(s+1)*(bitBudget k (s+1) A+1)^3)
    (s : ℕ) (a b : Array ℤ) (A : ℕ) (ha : a.size=k^s) (hb : b.size=k^s)
    (hfa : ToomCook.CoeffBound (ToomBitCost.arrayPolynomial a) A)
    (hfb : ToomCook.CoeffBound (ToomBitCost.arrayPolynomial b) A) :
    (ToomBitCost.execute ToomBitCost.bitPrimitives k s a b).operations ≤ bitMajorant k c s A := by
  induction s generalizing a b A with
  | zero =>
    exact hbase a b A (by simpa using ha) (by simpa using hb) hfa hfb
  | succ s ih =>
    have hh : 0<k^s := pow_pos (by omega) _
    have hchild (r : Fin (2*k-1)) := ih
      (ToomBitCost.evaluateCounted ToomBitCost.bitPrimitives k (k^s) a r).value
      (ToomBitCost.evaluateCounted ToomBitCost.bitPrimitives k (k^s) b r).value
      (growthConstant k*A)
      (evaluated_input_size k (k^s) a r) (evaluated_input_size k (k^s) b r)
      (evaluated_input_coeffBound k (k^s) A hh a hfa r)
      (evaluated_input_coeffBound k (k^s) A hh b hfb r)
    calc
      _ ≤ (∑ r : Fin (2*k-1), (ToomBitCost.execute ToomBitCost.bitPrimitives k s
          (ToomBitCost.evaluateCounted ToomBitCost.bitPrimitives k (k^s) a r).value
          (ToomBitCost.evaluateCounted ToomBitCost.bitPrimitives k (k^s) b r).value).operations)+
          c*k^(s+1)*(bitBudget k (s+1) A+1)^3 := hstep s a b A ha hb hfa hfb
      _ ≤ (2*k-1)*bitMajorant k c s (growthConstant k*A)+
          c*k^(s+1)*(bitBudget k (s+1) A+1)^3 := by
        apply Nat.add_le_add_right
        calc
          _ ≤ ∑ _r : Fin (2*k-1), bitMajorant k c s (growthConstant k*A) :=
            Finset.sum_le_sum (fun r _ => hchild r)
          _ = _ := by simp
      _ ≤ _ := bitMajorant_step k c s A


theorem power_size_le (k s : ℕ) : (k^s).size ≤ k.size*s+1 := by
  simpa using size_powerProduct_bound k 1 1 s 0 0

theorem budget_ge_depth (k S A : ℕ) : S+1 ≤ bitBudget k S A := by
  unfold bitBudget bitSlope
  nlinarith

theorem budget_ge_arity_size (k S A : ℕ) : k.size ≤ bitBudget k S A := by
  unfold bitBudget bitSlope
  nlinarith

theorem power_size_le_budget (k S A j : ℕ) (hj : j ≤ S) :
    (k^j).size ≤ bitBudget k S A := by
  apply (power_size_le k j).trans
  have hmul := Nat.mul_le_mul_left k.size hj
  unfold bitBudget bitSlope
  nlinarith

/-- The actual counted child-length calculation is polynomial in the
same global bit budget, including every multiply, ROM read and write. -/
theorem powerCounted_root_bound (k S A s : ℕ) (hs : s ≤ S) :
    (ToomBitCost.powerCounted ToomBitCost.bitPrimitives k s).operations ≤
      (s+1)*200*(bitBudget k S A+1)^2 := by
  apply ToomBitCost.powerCounted_bit_cost
  · exact budget_ge_arity_size k S A
  · intro j hj
    exact power_size_le_budget k S A j (hj.trans hs)
  · intro j hj
    have hsize : j.size ≤ j := Nat.size_le.mpr Nat.lt_two_pow_self
    exact hsize.trans ((hj.trans hs).trans (by have := budget_ge_depth k S A;omega))


/-- Binary comparison is the actual subtraction loop's borrow flag. -/
def natLtCounted (a b : ℕ) : ToomCook.Counted Bool :=
  let p := IntegerArithmetic.subCounted a.bits b.bits false
  ⟨p.1.2,p.2⟩

theorem natLtCounted_value (a b : ℕ) : (natLtCounted a b).value=decide (a<b) := by
  have h := IntegerArithmetic.subBits_borrow a.bits b.bits
  rw [IntegerArithmetic.value_bits,IntegerArithmetic.value_bits] at h
  simp only [natLtCounted,(IntegerArithmetic.subCounted_projections _ _ _).1]
  by_cases hab : a<b
  · simpa only [hab,decide_true] using h.mpr hab
  · have hb : (IntegerArithmetic.subBits a.bits b.bits false).2=false := by
      cases he : (IntegerArithmetic.subBits a.bits b.bits false).2
      · rfl
      · exact False.elim (hab (h.mp he))
    simpa only [hab,decide_false] using hb

theorem natLtCounted_operations (a b : ℕ) :
    (natLtCounted a b).operations=12*max a.size b.size+1 := by
  simp only [natLtCounted,(IntegerArithmetic.subCounted_projections _ _ _).2,
    IntegerArithmetic.columnSteps_eq,Nat.size_eq_bits_len]

/-- The padding exponent is chosen by a real bounded loop: compare the
current power against q, multiply by the fixed arity, and increment depth.
The mathematical `Nat.log` occurs only in its correctness theorem. -/
def paddingLoop (k q : ℕ) : ℕ→ℕ→ℕ→ToomCook.Counted (ℕ×ℕ)
  | 0,n,d => ⟨(n,d),1⟩
  | fuel+1,n,d => ToomBitCost.Counted.bind (natLtCounted q n) (fun stop=>
      ToomBitCost.Counted.bind (show ToomCook.Counted Unit from ⟨(),(fuel+1).size+1⟩) (fun _=>
      if stop then ⟨(n,d),n.size+d.size+1⟩
      else ToomBitCost.Counted.bind (ToomBitCost.readConstant k) (fun base=>
        ToomBitCost.Counted.bind (ToomBitCost.bitPrimitives.mul base n) (fun length=>
        ToomBitCost.Counted.bind (ToomBitCost.bitPrimitives.add d 1) (fun depth=>
          paddingLoop k q fuel length.natAbs depth.natAbs)))))

theorem paddingLoop_step_value (k q fuel d : ℕ) :
    (paddingLoop k q (fuel+1) (k^d) d).value=
      if q<k^d then (k^d,d) else (paddingLoop k q fuel (k^(d+1)) (d+1)).value := by
  simp only [paddingLoop,ToomBitCost.Counted.bind,natLtCounted_value,
    ToomBitCost.readConstant,ToomBitCost.bitPrimitives_correct.mul,
    ToomBitCost.bitPrimitives_correct.add]
  by_cases h : q<k^d
  · simp only [h,decide_true,if_true]
  · have hd : ((d:ℤ)+1).natAbs=d+1 := by omega
    simp only [h,decide_false,Bool.false_eq_true,if_false,
      ←Nat.cast_mul,Int.natAbs_natCast,pow_succ',hd]

theorem paddingLoop_value (k q fuel d : ℕ) (hk : 2≤k) (hq : 0<q)
    (hd : d≤Nat.log k q+1) (hf : Nat.log k q+1-d+1≤fuel) :
    (paddingLoop k q fuel (k^d) d).value=
      (k^(Nat.log k q+1),Nat.log k q+1) := by
  induction fuel generalizing d with
  | zero => omega
  | succ fuel ih =>
    rw [paddingLoop_step_value]
    by_cases he : d=Nat.log k q+1
    · subst d
      rw [if_pos ((padded_length_bounds k q hk hq).1)]
    · have hd' : d≤Nat.log k q := by omega
      have hp : k^d≤q := (Nat.pow_le_pow_right (by omega) hd').trans
        (Nat.pow_log_le_self k (Nat.ne_of_gt hq))
      rw [if_neg (by omega)]
      apply ih (d+1) (by omega) (by omega)

/-- An actual scan computes the input binary length; this avoids making
`Nat.size` a free setup primitive in the padding chooser. -/
def bitLengthCounted : List Bool→ToomCook.Counted ℕ
  | [] => ⟨0,1⟩
  | _b::bs => ToomBitCost.Counted.bind (show ToomCook.Counted Unit from ⟨(),1⟩) (fun _=>
      ToomBitCost.Counted.bind (bitLengthCounted bs) (fun previous=>
      ToomBitCost.Counted.bind (ToomBitCost.bitPrimitives.add previous 1)
        (fun next=>⟨next.natAbs,next.natAbs.size+1⟩)))

theorem bitLengthCounted_value (bs : List Bool) : (bitLengthCounted bs).value=bs.length := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    simp only [bitLengthCounted,ToomBitCost.Counted.bind,ih,
      ToomBitCost.bitPrimitives_correct.add,List.length_cons]
    omega

theorem bitLengthCounted_operations (bs : List Bool) :
    (bitLengthCounted bs).operations≤200*(bs.length+1)^2 := by
  induction bs with
  | nil => simp [bitLengthCounted]
  | cons b bs ih =>
    have hadd := ToomBitCost.bitPrimitive_add_cost (bs.length:ℤ) 1
    simp only [Int.natAbs_natCast,show (1:ℤ).natAbs.size=1 by decide] at hadd
    have hsize : bs.length.size≤bs.length := Nat.size_le.mpr Nat.lt_two_pow_self
    have hmax : max bs.length.size 1≤bs.length+1 := by omega
    have hadd' : (ToomBitCost.bitPrimitives.add (bs.length:ℤ) 1).operations≤50*(bs.length+2) := by omega
    have habs : ((bs.length:ℤ)+1).natAbs=bs.length+1 := by omega
    have hreturn : (bs.length+1).size≤bs.length+1 := Nat.size_le.mpr Nat.lt_two_pow_self
    simp only [bitLengthCounted,ToomBitCost.Counted.bind,bitLengthCounted_value,
      ToomBitCost.bitPrimitives_correct.add,habs,List.length_cons]
    nlinarith

/-- The root loop scans the input binary representation, computes its
fuel by actual signed addition, and never computes a free logarithm. -/
def choosePadding (k q : ℕ) : ToomCook.Counted (ℕ×ℕ) :=
  ToomBitCost.Counted.bind (bitLengthCounted q.bits) (fun length=>
    ToomBitCost.Counted.bind (ToomBitCost.readConstant 2) (fun two=>
    ToomBitCost.Counted.bind (ToomBitCost.bitPrimitives.add length two)
      (fun fuel=>paddingLoop k q fuel.natAbs 1 0)))

theorem choosePadding_value (k q : ℕ) (hk : 2≤k) (hq : 0<q) :
    (choosePadding k q).value=(k^(Nat.log k q+1),Nat.log k q+1) := by
  have h := paddingLoop_value k q (q.size+2) 0 hk hq (by omega)
    (by have := padded_depth_le_size k q hk hq;omega)
  have hfuel : ((q.size:ℤ)+2).natAbs=q.size+2 := by omega
  simpa only [choosePadding,ToomBitCost.Counted.bind,bitLengthCounted_value,
    Nat.size_eq_bits_len,ToomBitCost.readConstant,ToomBitCost.bitPrimitives_correct.add,
    hfuel,pow_zero] using h


/-- All indices in one node, including signed recombination differences,
fit the same coefficient word budget. -/
theorem index_size_le_budget (k S A n : ℕ) (hn : n≤4*k^S) :
    n.size ≤ bitBudget k S A := by
  apply (Nat.size_le_size hn).trans
  have h := size_powerProduct_bound k 4 1 S 1 0
  simp only [pow_one,pow_zero,mul_one,mul_zero,add_zero,show (4:ℕ).size=3 by decide] at h
  have h' : (4*k^S).size ≤ k.size*S+4 := by
    rw [Nat.mul_comm] at h
    omega
  apply h'.trans
  unfold bitBudget bitSlope
  nlinarith


/-- Concrete fixed-arity local-loop constant used by the numeric kernel
assembly. It depends on arity alone, never input length or coefficients. -/
def localFactor (k : ℕ) : ℕ := 10000*(k+1)^4

theorem localFactor_ge (k : ℕ) : 150 ≤ localFactor k := by
  have hp : 0<(k+1)^4 := by positivity
  unfold localFactor
  nlinarith

theorem array_coefficient_size_le (a : Array ℤ) (A j : ℕ)
    (ha : ToomCook.CoeffBound (ToomBitCost.arrayPolynomial a) A) :
    ((a[j]?).getD 0).natAbs.size≤A.size := by
  have h := ha j
  rw [ToomBitCost.arrayPolynomial_coeff] at h
  have hn : ((a[j]?).getD 0).natAbs≤A := by
    exact_mod_cast (show (((a[j]?).getD 0).natAbs : ℤ)≤A by simpa only [Int.natCast_natAbs] using h)
  exact Nat.size_le_size hn

/-- Actual constant-size multiplication execution, refined through the
canonical Boolean-list scalar programs, with original input bounds. -/
theorem execute_zero_cost_bound (k A : ℕ) (a b : Array ℤ)
    (ha : ToomCook.CoeffBound (ToomBitCost.arrayPolynomial a) A)
    (hb : ToomCook.CoeffBound (ToomBitCost.arrayPolynomial b) A) :
    (ToomBitCost.execute ToomBitCost.bitPrimitives k 0 a b).operations ≤
      localFactor k*(bitBudget k 0 A+1)^3 := by
  have has := array_coefficient_size_le a A 0 ha
  have hbs := array_coefficient_size_le b A 0 hb
  have hW : 1≤bitBudget k 0 A := Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt (bitBudget_pos k 0 A))
  have htwo : 2*A.size≤bitBudget k 0 A := by unfold bitBudget;omega
  have hz : (((a[0]?).getD 0)*((b[0]?).getD 0)).natAbs.size≤bitBudget k 0 A := by
    rw [Int.natAbs_mul]
    exact (size_mul_le _ _).trans (by omega)
  have h := ToomBitCost.execute_zero_bit_cost (k := k) a b (bitBudget k 0 A) hW
    (has.trans (by omega)) (hbs.trans (by omega)) hz
  apply h.trans
  apply Nat.mul_le_mul (localFactor_ge k)
  exact Nat.pow_le_pow_right (by omega) (by decide : 2≤3)


set_option maxHeartbeats 4000000 in
/-- The padding-length chooser charges every real comparison, multiply,
increment, branch and returned-size copy. Its cost is polynomial in the
input binary length, not linear in the value q. -/
theorem paddingLoop_operations_bound (k q fuel d : ℕ) (hk : 2≤k) (hq : 0<q)
    (hd : d≤Nat.log k q+1) (hf : fuel≤q.size+2) :
    (paddingLoop k q fuel (k^d) d).operations ≤
      1000*(fuel+1)*(k.size+q.size+6)^2 := by
  let W := k.size+q.size+5
  have hW : 1≤W := by dsimp [W];omega
  have hqW : q.size≤W := by dsimp [W];omega
  have hkW : k.size≤W := by dsimp [W];omega
  have hn (j : ℕ) (hj : j≤Nat.log k q+1) : (k^j).size≤W := by
    have hp : k^j≤k*q := (Nat.pow_le_pow_right (by omega) hj).trans
      (padded_length_bounds k q hk hq).2
    exact (Nat.size_le_size hp).trans ((size_mul_le k q).trans (by dsimp [W];omega))
  have hc (j : ℕ) (hj : j≤q.size+2) : j.size≤W := by
    exact (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by dsimp [W];omega)
  induction fuel generalizing d with
  | zero =>
    simp only [paddingLoop]
    dsimp [W] at hW
    nlinarith
  | succ fuel ih =>
    have hdepth : d.size≤W := hc d (by have := padded_depth_le_size k q hk hq;omega)
    have hcontrol : (fuel+1).size≤W := hc (fuel+1) hf
    have hcompare : (natLtCounted q (k^d)).operations≤12*W+1 := by
      rw [natLtCounted_operations]
      have hm : max q.size (k^d).size≤W := max_le hqW (hn d hd)
      omega
    by_cases hstop : q<k^d
    · simp only [paddingLoop,ToomBitCost.Counted.bind,natLtCounted_value,
        hstop,decide_true,if_true]
      have hcurrent := hn d hd
      have hreturn : (k^d).size+d.size+1≤2*W+1 := by omega
      have hlocal : (natLtCounted q (k^d)).operations+(fuel+1).size+1+
          ((k^d).size+d.size+1)≤1000*(W+1)^2 := by nlinarith
      have hfactor : 1000*(W+1)^2≤1000*(fuel+2)*(W+1)^2 := by nlinarith
      simpa [W,Nat.add_assoc] using hlocal.trans hfactor
    · have hd' : d+1≤Nat.log k q+1 := by
        by_contra h
        have he : d=Nat.log k q+1 := by omega
        subst d
        exact hstop (padded_length_bounds k q hk hq).1
      have hchild := ih (d+1) hd' (by omega)
      have hmul := ToomBitCost.bitPrimitive_mul_cost (k:ℤ) ((k^d:ℕ):ℤ)
      simp only [Int.natAbs_natCast] at hmul
      have hmul' : (ToomBitCost.bitPrimitives.mul (k:ℤ) ((k^d:ℕ):ℤ)).operations≤120*(W+1)^2+4 := by
        have hcur := hn d hd
        nlinarith
      have hadd := ToomBitCost.bitPrimitive_add_cost (d:ℤ) 1
      simp only [Int.natAbs_natCast,show (1:ℤ).natAbs.size=1 by decide] at hadd
      have hmax : max d.size 1≤W := max_le hdepth hW
      have hadd' : (ToomBitCost.bitPrimitives.add (d:ℤ) 1).operations≤50*(W+1) := by omega
      have hdabs : ((d:ℤ)+1).natAbs=d+1 := by omega
      simp only [paddingLoop,ToomBitCost.Counted.bind,natLtCounted_value,
        hstop,decide_false,Bool.false_eq_true,if_false,ToomBitCost.readConstant,
        ToomBitCost.bitPrimitives_correct.mul,ToomBitCost.bitPrimitives_correct.add,
        ←Nat.cast_mul,Int.natAbs_natCast,pow_succ',hdabs]
      have hlocal : (natLtCounted q (k^d)).operations+(fuel+1).size+1+
          (k.size+1+((ToomBitCost.bitPrimitives.mul (k:ℤ) ((k^d:ℕ):ℤ)).operations+
            (ToomBitCost.bitPrimitives.add (d:ℤ) 1).operations))≤1000*(W+1)^2 := by nlinarith
      have hchild' : (paddingLoop k q fuel (k^(d+1)) (d+1)).operations≤
          1000*(fuel+1)*(W+1)^2 := by simpa only [W,Nat.add_assoc] using hchild
      have hsum := Nat.add_le_add hlocal hchild'
      have he : 1000*(W+1)^2+1000*(fuel+1)*(W+1)^2=1000*(fuel+2)*(W+1)^2 := by ring
      rw [he] at hsum
      convert hsum using 1 <;> simp only [W,pow_succ',Nat.add_assoc]

-- Keep registered counter values opaque to tactic simplification. Their
-- actual recursive definitions were unfolded in the loop proofs above.
attribute [local irreducible] paddingLoop bitLengthCounted natLtCounted

theorem choosePadding_operations_bound (k q : ℕ) (hk : 2≤k) (hq : 0<q) :
    (choosePadding k q).operations≤1400*(q.size+3)*(k.size+q.size+6)^2 := by
  have hloop := paddingLoop_operations_bound k q (q.size+2) 0 hk hq (by omega) (by omega)
  simp only [pow_zero] at hloop
  have hlength := bitLengthCounted_operations q.bits
  rw [Nat.size_eq_bits_len] at hlength
  have hadd := ToomBitCost.bitPrimitive_add_cost (q.size:ℤ) 2
  simp only [Int.natAbs_natCast,show (2:ℤ).natAbs.size=2 by decide] at hadd
  have hsize : q.size.size≤q.size := Nat.size_le.mpr Nat.lt_two_pow_self
  have hmax : max q.size.size 2≤q.size+2 := by omega
  have hadd' : (ToomBitCost.bitPrimitives.add (q.size:ℤ) 2).operations≤50*(q.size+3) := by omega
  let T := (q.size+3)*(k.size+q.size+6)^2
  have hW : 1≤(k.size+q.size+6)^2 := by
    have hp : 0<(k.size+q.size+6)^2 := by positivity
    omega
  have hfactor : (k.size+q.size+6)^2≤T := by
    dsimp [T]
    exact Nat.le_mul_of_pos_left _ (by omega)
  have hlength' : (bitLengthCounted q.bits).operations≤200*T := by
    apply hlength.trans
    apply Nat.mul_le_mul_left
    exact (Nat.pow_le_pow_left (by omega : q.size+1≤k.size+q.size+6) 2).trans hfactor
  have hadd'' : (ToomBitCost.bitPrimitives.add (q.size:ℤ) 2).operations≤50*T := by
    apply hadd'.trans
    apply Nat.mul_le_mul_left
    simpa only [T,Nat.mul_one] using Nat.mul_le_mul_left (q.size+3) hW
  have hloop' : (paddingLoop k q (q.size+2) 1 0).operations≤1000*T := by
    apply hloop.trans
    have he : 1000*(q.size+2+1)*(k.size+q.size+6)^2=1000*T := by
      dsimp [T]
      ring
    exact he.le
  have hT : 1≤T := hW.trans hfactor
  have hfuel : ((q.size:ℤ)+2).natAbs=q.size+2 := by omega
  simp only [choosePadding,ToomBitCost.Counted.bind,bitLengthCounted_value,
    Nat.size_eq_bits_len,ToomBitCost.readConstant,ToomBitCost.bitPrimitives_correct.add,hfuel]
  have hread : (2:ℤ).natAbs.size+1=3 := by decide
  rw [hread]
  have heq : 1400*T=1400*(q.size+3)*(k.size+q.size+6)^2 := by
    dsimp [T]
    ring
  rw [←heq]
  nlinarith


/-- All actual local kernels are now instantiated by their register-
aware bit-program proofs. No local or global runtime bound is a premise. -/
theorem execute_step_cost_bound (k s A : ℕ) (hk : 2≤k) (a b : Array ℤ)
    (ha : ToomCook.CoeffBound (ToomBitCost.arrayPolynomial a) A)
    (hb : ToomCook.CoeffBound (ToomBitCost.arrayPolynomial b) A) :
    (ToomBitCost.execute ToomBitCost.bitPrimitives k (s+1) a b).operations ≤
      (∑ r : Fin (2*k-1), (ToomBitCost.execute ToomBitCost.bitPrimitives k s
        (ToomBitCost.evaluateCounted ToomBitCost.bitPrimitives k (k^s) a r).value
        (ToomBitCost.evaluateCounted ToomBitCost.bitPrimitives k (k^s) b r).value).operations)+
        localFactor k*k^(s+1)*(bitBudget k (s+1) A+1)^3 := by
  let W := bitBudget k (s+1) A
  let u := W+1
  let M := 2*k-1
  let E := k^s*(k*(180*u^2+150*u^2)+2*W+4)
  let I := M*(2*k^s*(M*(3*W+2+150*u^2)+80*u^2+2*W+8)+2)
  let R := 2*k*k^s*(M*(190*u^2+150*u^2)+2*W+4)
  have hE (r : Fin (2*k-1)) :
      (ToomBitCost.evaluateCounted ToomBitCost.bitPrimitives k (k^s) a r).operations≤E := by
    have h := ToomLocalBudget.evaluation_counted_cost k s A hk a ha r
    have he : E=k^s*(k*330*(ToomBitCost.bitBudget k (s+1) A+1)^2+
        2*ToomBitCost.bitBudget k (s+1) A+4) := by
      dsimp [E,u,W]
      rw [bitBudget_eq_program]
      ring
    rw [he]
    exact h
  have hE' (r : Fin (2*k-1)) :
      (ToomBitCost.evaluateCounted ToomBitCost.bitPrimitives k (k^s) b r).operations≤E := by
    have h := ToomLocalBudget.evaluation_counted_cost k s A hk b hb r
    have he : E=k^s*(k*330*(ToomBitCost.bitBudget k (s+1) A+1)^2+
        2*ToomBitCost.bitBudget k (s+1) A+4) := by
      dsimp [E,u,W]
      rw [bitBudget_eq_program]
      ring
    rw [he]
    exact h
  have hI : (ToomBitCost.interpolateCounted ToomBitCost.bitPrimitives (2*k-1) (k^s)
      (ToomBitCost.childProducts ToomBitCost.bitPrimitives k s a b)).operations≤I := by
    simpa only [I,M,u,W,bitBudget_eq_program] using
      ToomBitCost.actual_interpolate_cost k s A hk a b ha hb
  have hR : (ToomBitCost.recombineCounted ToomBitCost.bitPrimitives k (k^s)
      (ToomBitCost.interpolateCounted ToomBitCost.bitPrimitives (2*k-1) (k^s)
        (ToomBitCost.childProducts ToomBitCost.bitPrimitives k s a b)).value).operations≤R := by
    simpa only [R,M,u,W,bitBudget_eq_program] using
      ToomBitCost.actual_recombine_cost k s A hk a b ha hb
  have hindex (r : Fin (2*k-1)) : r.val.size≤W := by
    apply index_size_le_budget k (s+1) A r.val
    have hpow : 1≤k^s := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by omega))
    rw [pow_succ']
    have hr : r.val≤2*k := r.isLt.le.trans (Nat.sub_le (2*k) 1)
    have hkpow : k≤k*k^s := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left k hpow
    nlinarith
  have hpower : (ToomBitCost.powerCounted ToomBitCost.bitPrimitives k s).operations≤
      200*(s+1)*u^2 := by
    have h := powerCounted_root_bound k (s+1) A s (by omega)
    simpa only [u,W,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using h
  have hW : 1≤W := Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt (bitBudget_pos k (s+1) A))
  have hdepth : s+1≤W := by have h := budget_ge_depth k (s+1) A;dsimp [W];omega
  have hcontrol : (s+1).size+1≤W+1 := by
    have hsize : (s+1).size ≤ s+1 := Nat.size_le.mpr Nat.lt_two_pow_self
    omega
  have hcounter := ToomBitCost.execute_step_cost_of_kernels ToomBitCost.bitPrimitives
    ToomBitCost.bitPrimitives_correct k s a b E I R
    (ToomBitCost.powerCounted ToomBitCost.bitPrimitives k s).operations W
    hE hE' hI hR (le_refl _) hindex
  have hnum := ToomBitCost.kernel_assembly_padded k W s
    (ToomBitCost.powerCounted ToomBitCost.bitPrimitives k s).operations
    ((s+1).size+1) hk hW hdepth hpower hcontrol
  have hrest : 2*(2*k-1)*(E+W+4)+I+R+
      (ToomBitCost.powerCounted ToomBitCost.bitPrimitives k s).operations+(s+1).size+1 ≤
      localFactor k*k^(s+1)*(bitBudget k (s+1) A+1)^3 := by
    convert hnum using 1 <;> dsimp [E,I,R,M,u,W,localFactor] <;> simp only [pow_succ'] <;> ring
  calc
    _ ≤ (∑ r : Fin (2*k-1), (ToomBitCost.execute ToomBitCost.bitPrimitives k s
        (ToomBitCost.evaluateCounted ToomBitCost.bitPrimitives k (k^s) a r).value
        (ToomBitCost.evaluateCounted ToomBitCost.bitPrimitives k (k^s) b r).value).operations)+
        (2*(2*k-1)*(E+W+4)+I+R+
        (ToomBitCost.powerCounted ToomBitCost.bitPrimitives k s).operations+(s+1).size+1) := by
      simpa only [Nat.add_assoc] using hcounter
    _ ≤ _ := Nat.add_le_add_left hrest _

/-- Full global bit bound for the actual materialized recursive array
program, derived from bounded original coefficients and actual kernels. -/
theorem execute_cost_bound (k s A : ℕ) (hk : 2≤k) (a b : Array ℤ)
    (ha : a.size=k^s) (hb : b.size=k^s)
    (hfa : ToomCook.CoeffBound (ToomBitCost.arrayPolynomial a) A)
    (hfb : ToomCook.CoeffBound (ToomBitCost.arrayPolynomial b) A) :
    (ToomBitCost.execute ToomBitCost.bitPrimitives k s a b).operations ≤ bitMajorant k (localFactor k) s A :=
  execute_cost_induction k (localFactor k) hk
    (fun a b A _ _ hfa hfb=>execute_zero_cost_bound k A a b hfa hfb)
    (fun s a b A _ _ hfa hfb=>execute_step_cost_bound k s A hk a b hfa hfb)
    s a b A ha hb hfa hfb

/-- Correct complete integer polynomial multiplication and its actual
bit execution bound are established for the same returned array. -/
theorem execute_correct_and_cost (k s A : ℕ) (hk : 2≤k) (a b : Array ℤ)
    (ha : a.size=k^s) (hb : b.size=k^s)
    (hfa : ToomCook.CoeffBound (ToomBitCost.arrayPolynomial a) A)
    (hfb : ToomCook.CoeffBound (ToomBitCost.arrayPolynomial b) A) :
    (ToomBitCost.execute ToomBitCost.bitPrimitives k s a b).value=
      Array.ofFn (fun j : Fin (2*(k^s))=>
        (ToomBitCost.arrayPolynomial a*ToomBitCost.arrayPolynomial b).coeff j.val) ∧
    (ToomBitCost.execute ToomBitCost.bitPrimitives k s a b).operations≤bitMajorant k (localFactor k) s A :=
  ⟨ToomBitCost.execute_value _ ToomBitCost.bitPrimitives_correct k s hk a b ha hb,
    execute_cost_bound k s A hk a b ha hb hfa hfb⟩

/-- The actual recursive program, with padding chosen for q, has the
certified exponent and a cubic polynomial in binary input sizes. -/
theorem padded_execute_fixed_cost (q A : ℕ) (hq : 0<q) (a b : Array ℤ)
    (ha : a.size=(2^100000000)^(Nat.log (2^100000000) q+1))
    (hb : b.size=(2^100000000)^(Nat.log (2^100000000) q+1))
    (hfa : ToomCook.CoeffBound (ToomBitCost.arrayPolynomial a) A)
    (hfb : ToomCook.CoeffBound (ToomBitCost.arrayPolynomial b) A) :
    ((ToomBitCost.execute ToomBitCost.bitPrimitives (2^100000000)
      (Nat.log (2^100000000) q+1) a b).operations : ℝ) ≤
      (3*localFactor (2^100000000) : ℕ)*((2:ℝ)^100000000)^(1.00000001:ℝ)*
        ((bitSlope (2^100000000)+13 : ℕ) : ℝ)^3*
        (q:ℝ)^(1.00000001:ℝ)*((q.size+A.size+2 : ℕ) : ℝ)^3 := by
  have h := execute_cost_bound (2^100000000) (Nat.log (2^100000000) q+1) A
    (two_le_two_pow 100000000 (by norm_num)) a b ha hb hfa hfb
  have hcast : ((ToomBitCost.execute ToomBitCost.bitPrimitives (2^100000000)
      (Nat.log (2^100000000) q+1) a b).operations : ℝ)≤
      (bitMajorant (2^100000000) (localFactor (2^100000000))
        (Nat.log (2^100000000) q+1) A : ℝ) := Nat.cast_le.mpr h
  exact hcast.trans (fixed_bitMajorant_at_length (localFactor (2^100000000)) q A hq)


/-- Full arbitrary-length materialized polynomial multiplication. Padding
selection, both input arrays, and the recursive program are all executed
and charged once. The depth is chosen by the counted loop above. -/
def multiplyAtLength (k q : ℕ) (a b : Array ℤ) : ToomCook.Counted (Array ℤ) :=
  ToomBitCost.Counted.bind (choosePadding k q) (fun shape=>
    ToomBitCost.Counted.bind (padInput shape.1 a) (fun left=>
    ToomBitCost.Counted.bind (padInput shape.1 b) (fun right=>
      ToomBitCost.execute ToomBitCost.bitPrimitives k shape.2 left right)))

theorem multiplyAtLength_value (k q : ℕ) (hk : 2≤k) (hq : 0<q) (a b : Array ℤ)
    (ha : a.size=q) (hb : b.size=q) :
    (multiplyAtLength k q a b).value=
      Array.ofFn (fun j : Fin (2*(k^(Nat.log k q+1)))=>
        (ToomBitCost.arrayPolynomial a*ToomBitCost.arrayPolynomial b).coeff j.val) := by
  have hN : q≤k^(Nat.log k q+1) := (padded_length_bounds k q hk hq).1.le
  simp only [multiplyAtLength,ToomBitCost.Counted.bind,choosePadding_value k q hk hq]
  rw [ToomBitCost.execute_value _ ToomBitCost.bitPrimitives_correct k (Nat.log k q+1) hk
    _ _ (padInput_size _ a) (padInput_size _ b)]
  rw [padInput_polynomial _ a (by omega),padInput_polynomial _ b (by omega)]

/-- Actual complete execution cost, including binary-length scanning,
padding-length selection, dense padding copies and recursive arithmetic. -/
theorem multiplyAtLength_operations_bound (k q A : ℕ) (hk : 2≤k) (hq : 0<q)
    (a b : Array ℤ) (ha : a.size=q) (hb : b.size=q)
    (hfa : ToomCook.CoeffBound (ToomBitCost.arrayPolynomial a) A)
    (hfb : ToomCook.CoeffBound (ToomBitCost.arrayPolynomial b) A) :
    (multiplyAtLength k q a b).operations≤
      bitMajorant k (localFactor k) (Nat.log k q+1) A+
        1400*(q.size+3)*(k.size+q.size+6)^2+
        4*k*q*(A.size+k.size+q.size+2) := by
  let N := k^(Nat.log k q+1)
  have hN0 : q≤N := (padded_length_bounds k q hk hq).1.le
  have hN : N≤k*q := (padded_length_bounds k q hk hq).2
  have hsize : N.size≤k.size+q.size := (Nat.size_le_size hN).trans (size_mul_le k q)
  have hchoose := choosePadding_operations_bound k q hk hq
  have hpadA := padInput_operations_bound N A a hfa
  have hpadB := padInput_operations_bound N A b hfb
  have hpA : (padInput N a).operations≤2*k*q*(A.size+k.size+q.size+2) := by
    apply hpadA.trans
    have h := Nat.mul_le_mul (Nat.mul_le_mul_left 2 hN)
      (show A.size+N.size+2≤A.size+k.size+q.size+2 by omega)
    simpa only [Nat.mul_assoc] using h
  have hpB : (padInput N b).operations≤2*k*q*(A.size+k.size+q.size+2) := by
    apply hpadB.trans
    have h := Nat.mul_le_mul (Nat.mul_le_mul_left 2 hN)
      (show A.size+N.size+2≤A.size+k.size+q.size+2 by omega)
    simpa only [Nat.mul_assoc] using h
  have hpfa : ToomCook.CoeffBound (ToomBitCost.arrayPolynomial (padInput N a).value) A := by
    rw [padInput_polynomial N a (by omega)]
    exact hfa
  have hpfb : ToomCook.CoeffBound (ToomBitCost.arrayPolynomial (padInput N b).value) A := by
    rw [padInput_polynomial N b (by omega)]
    exact hfb
  have hexec := execute_cost_bound k (Nat.log k q+1) A hk
    (padInput N a).value (padInput N b).value (padInput_size N a) (padInput_size N b) hpfa hpfb
  simp only [multiplyAtLength,ToomBitCost.Counted.bind,choosePadding_value k q hk hq]
  change (choosePadding k q).operations+((padInput N a).operations+
      ((padInput N b).operations+
        (ToomBitCost.execute ToomBitCost.bitPrimitives k (Nat.log k q+1)
          (padInput N a).value (padInput N b).value).operations))≤_
  nlinarith


theorem setup_polynomial_bound (k q A : ℕ) :
    1400*(q.size+3)*(k.size+q.size+6)^2 ≤
      2800*(k.size+6)^2*(q.size+A.size+2)^3 := by
  let Q := q.size+A.size+2
  have hF : q.size+3≤2*Q := by dsimp [Q];omega
  have hW : k.size+q.size+6≤(k.size+6)*Q := by dsimp [Q];nlinarith
  calc
    _ ≤ 1400*(2*Q)*((k.size+6)*Q)^2 := by gcongr
    _ = _ := by dsimp [Q];ring

theorem padding_polynomial_bound (k q A : ℕ) :
    4*k*q*(A.size+k.size+q.size+2) ≤
      (4*k*(k.size+1))*q*(q.size+A.size+2)^3 := by
  let Q := q.size+A.size+2
  have hQ : 1≤Q := by dsimp [Q];omega
  have hterm : A.size+k.size+q.size+2≤(k.size+1)*Q := by dsimp [Q];nlinarith
  have hpow : Q≤Q^3 := by
    simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 0<Q) (by decide : 1≤3)
  calc
    _ ≤ 4*k*q*((k.size+1)*Q) := Nat.mul_le_mul_left _ hterm
    _ = (4*k*(k.size+1))*q*Q := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ hpow

/-- Fixed arity-dependent constant for the complete multiplication
program, including all setup and dense-array materialization. -/
def bitConstant (B : ℕ) : ℝ :=
  (3*localFactor (2^B) : ℕ)*((2:ℝ)^B)^(1+1/(B:ℝ))*
    ((bitSlope (2^B)+13 : ℕ) : ℝ)^3+
    ((2800*((2^B).size+6)^2+4*(2^B)*((2^B).size+1) : ℕ) : ℝ)

-- Counter values are mathematical observations of the already-proved
-- executable definition; avoid tactic reduction through its array loops.
attribute [local irreducible] multiplyAtLength

/-- Full arbitrary-length all-coefficient multiplication, with its actual
binary-operation counter. There is no assumed fast-arithmetic primitive. -/
theorem multiplyAtLength_rpow_bound (B q A : ℕ) (hB : 0<B) (hq : 0<q)
    (a b : Array ℤ) (ha : a.size=q) (hb : b.size=q)
    (hfa : ToomCook.CoeffBound (ToomBitCost.arrayPolynomial a) A)
    (hfb : ToomCook.CoeffBound (ToomBitCost.arrayPolynomial b) A) :
    ((multiplyAtLength (2^B) q a b).operations : ℝ) ≤
      bitConstant B*(q:ℝ)^(1+1/(B:ℝ))*((q.size+A.size+2 : ℕ) : ℝ)^3 := by
  let k : ℕ:=2^B
  let Q : ℕ:=q.size+A.size+2
  let e : ℝ:=1+1/(B:ℝ)
  let C0 : ℝ:=(3*localFactor k : ℕ)*((2:ℝ)^B)^e*((bitSlope k+13 : ℕ) : ℝ)^3
  let C1 : ℕ:=2800*(k.size+6)^2
  let C2 : ℕ:=4*k*(k.size+1)
  have hk : 2≤k := two_le_two_pow B hB
  have hqR : (1:ℝ)≤q := by exact_mod_cast hq
  have he : (1:ℝ)≤e := by
    have hd : (0:ℝ)≤1/(B:ℝ) := by positivity
    dsimp [e]
    linarith
  have hself : (q:ℝ)≤(q:ℝ)^e := Real.self_le_rpow_of_one_le hqR he
  have hpow : (1:ℝ)≤(q:ℝ)^e := hqR.trans hself
  have hQ : (0:ℝ)≤(Q:ℝ)^3 := by positivity
  have hmajor := bitMajorant_at_length B (localFactor k) q A hB hq
  have hmajor' : (bitMajorant k (localFactor k) (Nat.log k q+1) A : ℝ)≤
      C0*(q:ℝ)^e*(Q:ℝ)^3 := hmajor
  have hsetupN := setup_polynomial_bound k q A
  have hsetup : ((1400*(q.size+3)*(k.size+q.size+6)^2 : ℕ) : ℝ)≤
      (C1:ℝ)*(Q:ℝ)^3 := by
    have hcast : ((1400*(q.size+3)*(k.size+q.size+6)^2 : ℕ) : ℝ)≤
        ((C1*Q^3 : ℕ) : ℝ) := Nat.cast_le.mpr hsetupN
    simpa only [Nat.cast_mul,Nat.cast_pow] using hcast
  have hsetup' : ((1400*(q.size+3)*(k.size+q.size+6)^2 : ℕ) : ℝ)≤
      (C1:ℝ)*(q:ℝ)^e*(Q:ℝ)^3 := by
    apply hsetup.trans
    have h := mul_le_mul_of_nonneg_left hpow (by positivity : (0:ℝ)≤C1)
    exact mul_le_mul_of_nonneg_right (by simpa only [mul_one] using h) hQ
  have hpadN := padding_polynomial_bound k q A
  have hpad : ((4*k*q*(A.size+k.size+q.size+2) : ℕ) : ℝ)≤
      (C2:ℝ)*(q:ℝ)*(Q:ℝ)^3 := by
    have hcast : ((4*k*q*(A.size+k.size+q.size+2) : ℕ) : ℝ)≤
        ((C2*q*Q^3 : ℕ) : ℝ) := Nat.cast_le.mpr hpadN
    simpa only [Nat.cast_mul,Nat.cast_pow] using hcast
  have hpad' : ((4*k*q*(A.size+k.size+q.size+2) : ℕ) : ℝ)≤
      (C2:ℝ)*(q:ℝ)^e*(Q:ℝ)^3 := by
    apply hpad.trans
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hself (Nat.cast_nonneg C2)) hQ
  have hcostN := multiplyAtLength_operations_bound k q A hk hq a b ha hb hfa hfb
  have hcost : ((multiplyAtLength k q a b).operations : ℝ)≤
      (bitMajorant k (localFactor k) (Nat.log k q+1) A : ℝ)+
        ((1400*(q.size+3)*(k.size+q.size+6)^2 : ℕ) : ℝ)+
        ((4*k*q*(A.size+k.size+q.size+2) : ℕ) : ℝ) := by
    have hcast : ((multiplyAtLength k q a b).operations : ℝ)≤
        ((bitMajorant k (localFactor k) (Nat.log k q+1) A+
          1400*(q.size+3)*(k.size+q.size+6)^2+4*k*q*(A.size+k.size+q.size+2) : ℕ) : ℝ) :=
      Nat.cast_le.mpr hcostN
    simpa only [Nat.cast_add] using hcast
  have hsum := hcost.trans (add_le_add (add_le_add hmajor' hsetup') hpad')
  have hC : C0+(C1:ℝ)+(C2:ℝ)=bitConstant B := by
    dsimp [C0,C1,C2,bitConstant,k,e]
    simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
    ring
  calc
    _ ≤ C0*(q:ℝ)^e*(Q:ℝ)^3+(C1:ℝ)*(q:ℝ)^e*(Q:ℝ)^3+
        (C2:ℝ)*(q:ℝ)^e*(Q:ℝ)^3 := hsum
    _ = (C0+(C1:ℝ)+(C2:ℝ))*(q:ℝ)^e*(Q:ℝ)^3 := by ring
    _ = _ := by rw [hC]

/-- The exact epsilon charged in ArithmeticSlack is attained by this
concrete full array/bit program, including q=1. -/
theorem multiplyAtLength_fixed_bound (q A : ℕ) (hq : 0<q)
    (a b : Array ℤ) (ha : a.size=q) (hb : b.size=q)
    (hfa : ToomCook.CoeffBound (ToomBitCost.arrayPolynomial a) A)
    (hfb : ToomCook.CoeffBound (ToomBitCost.arrayPolynomial b) A) :
    ((multiplyAtLength (2^100000000) q a b).operations : ℝ) ≤
      bitConstant 100000000*(q:ℝ)^(1.00000001:ℝ)*((q.size+A.size+2 : ℕ) : ℝ)^3 := by
  have h := multiplyAtLength_rpow_bound 100000000 q A (by norm_num) hq a b ha hb hfa hfb
  have he : (1:ℝ)+1/(100000000:ℕ)=1.00000001 := by norm_num
  rwa [he] at h

end
end ThinMatrix.ToomExecutionBound

#print axioms ThinMatrix.ToomExecutionBound.bitBudget_child
#print axioms ThinMatrix.ToomExecutionBound.bitRecurrence_bound
#print axioms ThinMatrix.ToomExecutionBound.bitRecurrence_rpow
#print axioms ThinMatrix.ToomExecutionBound.padded_bitBudget_bound

#print axioms ThinMatrix.ToomExecutionBound.actual_path_numerator_bits
#print axioms ThinMatrix.ToomExecutionBound.bitMajorant_step
#print axioms ThinMatrix.ToomExecutionBound.fixed_bitMajorant_at_length

#print axioms ThinMatrix.ToomExecutionBound.evaluated_input_coeffBound
#print axioms ThinMatrix.ToomExecutionBound.padInput_polynomial
#print axioms ThinMatrix.ToomExecutionBound.padInput_operations_bound

#print axioms ThinMatrix.ToomExecutionBound.powerCounted_root_bound

#print axioms ThinMatrix.ToomExecutionBound.choosePadding_value

#print axioms ThinMatrix.ToomExecutionBound.index_size_le_budget

#print axioms ThinMatrix.ToomExecutionBound.execute_zero_cost_bound

#print axioms ThinMatrix.ToomExecutionBound.choosePadding_operations_bound

#print axioms ThinMatrix.ToomExecutionBound.bitLengthCounted_operations

#print axioms ThinMatrix.ToomExecutionBound.execute_step_cost_bound
#print axioms ThinMatrix.ToomExecutionBound.execute_correct_and_cost
#print axioms ThinMatrix.ToomExecutionBound.padded_execute_fixed_cost

#print axioms ThinMatrix.ToomExecutionBound.multiplyAtLength_value
#print axioms ThinMatrix.ToomExecutionBound.multiplyAtLength_operations_bound

#print axioms ThinMatrix.ToomExecutionBound.multiplyAtLength_fixed_bound
