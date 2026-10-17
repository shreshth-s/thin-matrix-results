import ArrayFFT
import IntegerArithmetic

/-!
# Bit circuits for the integer-cell FFT

This module prices integer instructions by the concrete Boolean-list circuits.
The literal-operand `Instruction` and `rootTrace` are proof-only arithmetic
schedules, not runtime trace generators or a lowering of the FFT. Their
`ofInt` wrappers specify canonical binary input for an individual circuit;
no free conversion of semantic intermediate integers is asserted. Array indexing and materialization
are separate from these bit circuits; no word-RAM compilation is asserted.
-/

set_option maxRecDepth 4000
set_option maxHeartbeats 2000000

namespace ThinMatrix.FFTBitCost
open scoped BigOperators
open IntegerArithmetic

def nonzeroBits : List Bool → Bool
  | [] => false
  | b::bs => b || nonzeroBits bs

theorem nonzeroBits_false (bs : List Bool) : nonzeroBits bs = false ↔ value bs = 0 := by
  induction bs with
  | nil => simp [nonzeroBits, value]
  | cons b bs ih => cases b <;> simp [nonzeroBits, value, digit, ih]

/-- Euclidean division by a positive natural divisor. The quotient/remainder
child is stored once; negative non-exact inputs increment the magnitude. -/
def floorCounted (D : ℕ) (z : ℤ) : ℤ × ℕ :=
  if D = 0 then (0,1) else
  let input := ofInt z
  let qr := divideCounted D.bits input.magnitude
  let hasRemainder := nonzeroBits qr.1.2
  if input.negative && hasRemainder then
    let inc := addCounted qr.1.1 [true] false
    (signedValue ⟨true, inc.1⟩, qr.2 + qr.1.2.length + inc.2 + 8)
  else (signedValue ⟨input.negative, qr.1.1⟩, qr.2 + qr.1.2.length + 8)

theorem floorCounted_correct (D : ℕ) (z : ℤ) : (floorCounted D z).1 = z / (D : ℤ) := by
  by_cases hD : D = 0
  · simp [floorCounted, hD]
  have hpos : 0 < D := Nat.pos_of_ne_zero hD
  have hDi : (0 : ℤ) < D := by exact_mod_cast hpos
  have hp := divideCounted_projections D.bits z.natAbs.bits
  have hi := divideBits_correct D.bits z.natAbs.bits (by simpa [value_bits] using hpos)
  simp only [value_bits] at hi
  have hie : (z.natAbs : ℤ) = (value (divideBits D.bits z.natAbs.bits).1 : ℤ) * D +
      value (divideBits D.bits z.natAbs.bits).2 := by exact_mod_cast hi.1
  have hre : (value (divideBits D.bits z.natAbs.bits).2 : ℤ) < D := by exact_mod_cast hi.2
  have hr0 : (0 : ℤ) ≤ value (divideBits D.bits z.natAbs.bits).2 := by positivity
  simp only [floorCounted, if_neg hD, ofInt, hp.1]
  by_cases hz : z < 0
  · have hzabs : z = -(z.natAbs : ℤ) := Int.eq_neg_natAbs_of_nonpos hz.le
    simp only [decide_eq_true hz, Bool.true_and]
    split_ifs with hn
    · have hn' : value (divideBits D.bits z.natAbs.bits).2 ≠ 0 := by
        intro he
        have hf := (nonzeroBits_false _).mpr he
        rw [hf] at hn
        contradiction
      have hrp : (0 : ℤ) < value (divideBits D.bits z.natAbs.bits).2 := by exact_mod_cast Nat.pos_of_ne_zero hn'
      rw [(addCounted_projections _ _ _).1]
      simp only [signedValue, if_true, addBits_correct, value, digit_true,
        digit_false, mul_zero, add_zero, Nat.cast_add, Nat.cast_one]
      symm
      apply (Int.ediv_eq_iff_of_pos hDi).mpr
      constructor <;> nlinarith
    · have hf : nonzeroBits (divideBits D.bits z.natAbs.bits).2 = false := by
        cases he : nonzeroBits (divideBits D.bits z.natAbs.bits).2 with
        | false => rfl
        | true => exact False.elim (hn he)
      have hn' := (nonzeroBits_false _).mp hf
      have hnz : (value (divideBits D.bits z.natAbs.bits).2 : ℤ) = 0 := by exact_mod_cast hn'
      simp only [signedValue, if_true]
      symm
      apply (Int.ediv_eq_iff_of_pos hDi).mpr
      constructor <;> nlinarith
  · have hzabs : z = (z.natAbs : ℤ) := (Int.natAbs_of_nonneg (by omega)).symm
    simp only [decide_eq_false hz, Bool.false_and, Bool.false_eq_true, if_false, signedValue]
    symm
    apply (Int.ediv_eq_iff_of_pos hDi).mpr
    constructor <;> nlinarith

theorem floorCounted_bound (D : ℕ) (z : ℤ) :
    (floorCounted D z).2 ≤ 64*(z.natAbs.size+D.size+2)^2 := by
  by_cases hD : D = 0
  · simp only [floorCounted, if_pos hD]
    have hp : 1 ≤ (z.natAbs.size+D.size+2)^2 := Nat.one_le_pow _ _ (by omega)
    omega
  have hp := divideCounted_projections D.bits (ofInt z).magnitude
  have hc := divideSteps_bound D.bits (ofInt z).magnitude
  have hl := divideBits_remainder_length D.bits (ofInt z).magnitude
  have hq := divideBits_quotient_length D.bits (ofInt z).magnitude
  have ha := addCounted_projections (divideBits D.bits (ofInt z).magnitude).1 [true] false
  simp only [ofInt_length, Nat.size_eq_bits_len] at hc hl hq
  simp only [floorCounted, if_neg hD, hp.1, hp.2]
  split_ifs
  · rw [ha.2, columnSteps_eq, hq]
    simp only [List.length_cons, List.length_nil]
    simp only [Nat.zero_add]
    have hm : max z.natAbs.size 1 ≤ z.natAbs.size+1 := by omega
    have hp : (z.natAbs.size+1)*(z.natAbs.size+D.size+1) ≤ (z.natAbs.size+D.size+2)^2 := by
      rw [pow_two]
      exact Nat.mul_le_mul (by omega) (by omega)
    nlinarith
  · change divideSteps D.bits (ofInt z).magnitude + (divideBits D.bits (ofInt z).magnitude).2.length + 8 ≤ _
    nlinarith

/-- Closed integer instructions carry their actual operand values. Their
counter is obtained by executing the corresponding bit-serial circuit. -/
inductive Instruction where
  | add (x y : ℤ)
  | sub (x y : ℤ)
  | mul (x y : ℤ)
  | floorDiv (D : ℕ) (x : ℤ)
  | neg (x : ℤ)

def Instruction.run : Instruction → ℤ × ℕ
  | .add x y => signedAddIntCounted x y
  | .sub x y => signedSubIntCounted x y
  | .mul x y => signedMulIntCounted x y
  | .floorDiv D x => floorCounted D x
  | .neg x => signedNegIntCounted x

def Instruction.denotation : Instruction → ℤ
  | .add x y => x+y
  | .sub x y => x-y
  | .mul x y => x*y
  | .floorDiv D x => x/(D:ℤ)
  | .neg x => -x

theorem instruction_correct (i : Instruction) : i.run.1 = i.denotation := by
  cases i
  · exact signedAddIntCounted_correct _ _
  · exact signedSubIntCounted_correct _ _
  · exact signedMulIntCounted_correct _ _
  · exact floorCounted_correct _ _
  · exact signedNegIntCounted_correct _

def Instruction.width : Instruction → ℕ
  | .add x y | .sub x y | .mul x y => max x.natAbs.size y.natAbs.size
  | .floorDiv D x => max D.size x.natAbs.size
  | .neg x => x.natAbs.size

theorem instruction_cost (i : Instruction) : i.run.2 ≤ 256*(i.width+2)^2 := by
  cases i with
  | add x y =>
      simp only [Instruction.run, Instruction.width]
      have h := signedAddIntCounted_bound x y
      change _ ≤ 256*(max x.natAbs.size y.natAbs.size+2)^2
      nlinarith
  | sub x y =>
      simp only [Instruction.run, Instruction.width]
      have h := signedSubIntCounted_bound x y
      change _ ≤ 256*(max x.natAbs.size y.natAbs.size+2)^2
      nlinarith
  | mul x y =>
      simp only [Instruction.run, Instruction.width]
      have h := signedMulIntCounted_bound x y
      have hx := le_max_left x.natAbs.size y.natAbs.size
      have hy := le_max_right x.natAbs.size y.natAbs.size
      change _ ≤ 256*(max x.natAbs.size y.natAbs.size+2)^2
      nlinarith
  | floorDiv D x =>
      simp only [Instruction.run, Instruction.width]
      have h := floorCounted_bound D x
      have hx := le_max_right D.size x.natAbs.size
      have hd := le_max_left D.size x.natAbs.size
      change _ ≤ 256*(max D.size x.natAbs.size+2)^2
      nlinarith
  | neg x =>
      simp only [Instruction.run, Instruction.width, signedNegIntCounted]
      have hp : 1 ≤ (x.natAbs.size+2)^2 := Nat.one_le_pow _ _ (by omega)
      omega

def traceCost (trace : List Instruction) : ℕ := (trace.map (fun i => i.run.2)).sum

theorem traceCost_bound (trace : List Instruction) (W : ℕ)
    (h : ∀ i ∈ trace, i.width ≤ W) : traceCost trace ≤ trace.length*(256*(W+2)^2) := by
  induction trace with
  | nil => simp [traceCost]
  | cons i trace ih =>
      have hi := (instruction_cost i).trans (show 256*(i.width+2)^2 ≤ 256*(W+2)^2 by gcongr; exact h i (by simp))
      have ht := ih (fun j hj => h j (by simp [hj]))
      simp only [traceCost, List.map_cons, List.sum_cons, List.length_cons] at *
      nlinarith

/-! Instruction traces for the unreduced root evaluator. These are ghost
traces of the displayed arithmetic schedule; tracing is not an additional
runtime computation. Every entry is priced by its concrete bit circuit. -/

open RationalWorkBounds

def rawAddTrace (x y : Raw) : List Instruction :=
  [.mul x.re y.den, .mul y.re x.den, .add (x.re*y.den) (y.re*x.den),
   .mul x.im y.den, .mul y.im x.den, .add (x.im*y.den) (y.im*x.den),
   .mul x.den y.den]
def rawMulTrace (x y : Raw) : List Instruction :=
  [.mul x.re y.re, .mul x.im y.im, .sub (x.re*y.re) (x.im*y.im),
   .mul x.re y.im, .mul x.im y.re, .add (x.re*y.im) (x.im*y.re),
   .mul x.den y.den]
def rawNegTrace (x : Raw) : List Instruction := [.neg x.re, .neg x.im]
def rawDivTrace (x : Raw) (d : ℕ) : List Instruction := [.mul x.den d]
def rawPowTrace (x : Raw) : ℕ → List Instruction
  | 0 => []
  | k+1 => rawPowTrace x k ++ rawMulTrace (pow x k) x
def rawSumTrace (f : ℕ → Raw) (work : ℕ → List Instruction) : ℕ → List Instruction
  | 0 => []
  | n+1 => rawSumTrace f work n ++ work n ++ rawAddTrace (sum f n) (f n)
def natPowerTrace (a : ℕ) : ℕ → List Instruction
  | 0 => []
  | k+1 => natPowerTrace a k ++ [.mul ((a^k : ℕ):ℤ) (a:ℤ)]
def intPowerTrace (a : ℤ) : ℕ → List Instruction
  | 0 => []
  | k+1 => intPowerTrace a k ++ [.mul (a^k) a]
def factorialTrace : ℕ → List Instruction
  | 0 => []
  | k+1 => factorialTrace k ++ [.add (k:ℤ) 1, .mul (k.factorial:ℤ) ((k+1:ℕ):ℤ)]
def atanTermTrace (a k : ℕ) : List Instruction :=
  intPowerTrace (-1) k ++ [.mul (2:ℤ) (k:ℤ), .add ((2*k:ℕ):ℤ) 1] ++
    natPowerTrace a (2*k+1) ++ [.mul ((2*k+1:ℕ):ℤ) ((a^(2*k+1):ℕ):ℤ)]
def atanSumTrace (a n : ℕ) : List Instruction := rawSumTrace (atanTerm a) (atanTermTrace a) n
def piTrace (B : ℕ) : List Instruction :=
  atanSumTrace 5 (B+10) ++ rawMulTrace (ofInt 16) (atanSum 5 (B+10)) ++
  atanSumTrace 239 (B+10) ++ rawMulTrace (ofInt 4) (atanSum 239 (B+10)) ++
  rawNegTrace (mul (ofInt 4) (atanSum 239 (B+10))) ++
  rawAddTrace (mul (ofInt 16) (atanSum 5 (B+10))) (neg (mul (ofInt 4) (atanSum 239 (B+10))))
def angleTrace (N j B : ℕ) : List Instruction :=
  piTrace B ++ [.mul 2 j] ++ rawMulTrace (ofInt (2*j)) (piRaw B) ++
  rawDivTrace (mul (ofInt (2*j)) (piRaw B)) N
def taylorTermTrace (x : Raw) (k : ℕ) : List Instruction :=
  rawPowTrace (imaginary x) k ++ factorialTrace k ++ rawDivTrace (pow (imaginary x) k) k.factorial
def taylorTrace (x : Raw) (n : ℕ) : List Instruction :=
  rawSumTrace (taylorTerm x) (taylorTermTrace x) n
def rootTrace (N j B : ℕ) : List Instruction :=
  angleTrace N j B ++ taylorTrace (angleRaw N j B) (B+68)

@[simp] theorem rawAddTrace_length (x y : Raw) : (rawAddTrace x y).length = 7 := rfl
@[simp] theorem rawMulTrace_length (x y : Raw) : (rawMulTrace x y).length = 7 := rfl
@[simp] theorem rawNegTrace_length (x : Raw) : (rawNegTrace x).length = 2 := rfl
@[simp] theorem rawDivTrace_length (x : Raw) (d : ℕ) : (rawDivTrace x d).length = 1 := rfl
@[simp] theorem rawPowTrace_length (x : Raw) (k : ℕ) : (rawPowTrace x k).length = 7*k := by
  induction k <;> simp_all [rawPowTrace]; omega
theorem rawSumTrace_length (f : ℕ → Raw) (work : ℕ → List Instruction) (n : ℕ) :
    (rawSumTrace f work n).length = (sumC (fun k => ⟨f k,(work k).length⟩) n).operations := by
  induction n <;> simp_all [rawSumTrace, sumC, literal, addC, Nat.add_assoc]
@[simp] theorem natPowerTrace_length (a k : ℕ) : (natPowerTrace a k).length = k := by
  induction k <;> simp_all [natPowerTrace]
@[simp] theorem intPowerTrace_length (a : ℤ) (k : ℕ) : (intPowerTrace a k).length = k := by
  induction k <;> simp_all [intPowerTrace]
@[simp] theorem factorialTrace_length (k : ℕ) : (factorialTrace k).length = 2*k := by
  induction k <;> simp_all [factorialTrace]; omega
@[simp] theorem atanTermTrace_length (a k : ℕ) : (atanTermTrace a k).length = 3*k+4 := by
  simp [atanTermTrace]; omega
theorem atanSumTrace_length (a n : ℕ) : (atanSumTrace a n).length = (atanSumC a n).operations := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change (rawSumTrace (atanTerm a) (atanTermTrace a) n ++ atanTermTrace a n ++
        rawAddTrace (sum (atanTerm a) n) (atanTerm a n)).length = _
      simp only [List.length_append, atanTermTrace_length, rawAddTrace_length]
      change (atanSumTrace a n).length + (3*n+4)+7 = _
      rw [ih]
      simp only [atanSumC, sumC, addC]
      rw [atanTermC_operations]
theorem piTrace_length (B : ℕ) : (piTrace B).length = (piC B).operations := by
  simp only [piTrace, List.length_append, atanSumTrace_length, rawMulTrace_length,
    rawNegTrace_length, rawAddTrace_length, piC, addC, mulC, negC, literal]
  omega
theorem angleTrace_length (N j B : ℕ) : (angleTrace N j B).length = (angleC N j B).operations := by
  simp only [angleTrace, List.length_append, piTrace_length, rawMulTrace_length, rawDivTrace_length,
    List.length_cons, List.length_nil, angleC, divNatC, mulC]
  omega
@[simp] theorem taylorTermTrace_length (x : Raw) (k : ℕ) :
    (taylorTermTrace x k).length = (taylorTermC x k).operations := by
  simp only [taylorTermTrace, List.length_append, rawPowTrace_length, factorialTrace_length,
    rawDivTrace_length, taylorTermC_operations]
  omega
theorem taylorTrace_length (x : Raw) (n : ℕ) : (taylorTrace x n).length = (taylorC x n).operations := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change (rawSumTrace (taylorTerm x) (taylorTermTrace x) n ++ taylorTermTrace x n ++
        rawAddTrace (sum (taylorTerm x) n) (taylorTerm x n)).length = _
      simp only [List.length_append, taylorTermTrace_length, rawAddTrace_length]
      change (taylorTrace x n).length + (taylorTermC x n).operations + 7 = _
      rw [ih]
      rfl
theorem rootTrace_length (N j B : ℕ) : (rootTrace N j B).length = (rootC N j B).operations := by
  simp only [rootTrace, List.length_append, angleTrace_length, taylorTrace_length,
    rootC, angleC_result]

def TraceWidth (W : ℕ) (trace : List Instruction) : Prop := ∀ i ∈ trace, i.width ≤ W

theorem traceWidth_append {W : ℕ} {a b : List Instruction}
    (ha : TraceWidth W a) (hb : TraceWidth W b) : TraceWidth W (a++b) := by
  intro i hi
  rcases List.mem_append.mp hi with hi | hi
  · exact ha i hi
  · exact hb i hi

theorem traceWidth_mono {W K : ℕ} {a : List Instruction} (h : TraceWidth W a) (hWK : W ≤ K) : TraceWidth K a :=
  fun i hi => (h i hi).trans hWK

theorem magnitude_size {z : ℤ} {R : ℕ} (h : z.natAbs ≤ 2^R) : z.natAbs.size ≤ R+1 := by
  apply Nat.size_le.mpr
  apply h.trans_lt
  rw [pow_succ]
  have hp : 0 < (2:ℕ)^R := by positivity
  omega

theorem natural_size {z R : ℕ} (h : z ≤ 2^R) : z.size ≤ R+1 := by
  simpa using magnitude_size (z := (z:ℤ)) (by simpa using h)

theorem product_size {x y : ℤ} {R : ℕ} (hx : x.natAbs ≤ 2^R) (hy : y.natAbs ≤ 2^R) :
    (x*y).natAbs.size ≤ 2*R+1 := by
  apply magnitude_size (R := 2*R)
  rw [Int.natAbs_mul]
  calc
    _ ≤ 2^R*2^R := Nat.mul_le_mul hx hy
    _ = _ := by rw [← pow_add]; congr 1; omega

theorem rawAddTrace_width {x y : Raw} {R : ℕ} (hx : Fits x R) (hy : Fits y R) :
    TraceWidth (2*R+2) (rawAddTrace x y) := by
  have hxd : (x.den:ℤ).natAbs ≤ 2^R := by simpa using hx.2.2
  have hyd : (y.den:ℤ).natAbs ≤ 2^R := by simpa using hy.2.2
  have hp₁ := product_size hx.1 hyd
  have hp₂ := product_size hy.1 hxd
  have hp₃ := product_size hx.2.1 hyd
  have hp₄ := product_size hy.2.1 hxd
  have hx₁ := magnitude_size hx.1
  have hx₂ := magnitude_size hx.2.1
  have hy₁ := magnitude_size hy.1
  have hy₂ := magnitude_size hy.2.1
  have hdx := magnitude_size hxd
  have hdy := magnitude_size hyd
  intro i hi
  simp only [rawAddTrace, List.mem_cons, List.mem_nil_iff, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [Instruction.width, max_le_iff] <;> constructor <;> omega

theorem rawMulTrace_width {x y : Raw} {R : ℕ} (hx : Fits x R) (hy : Fits y R) :
    TraceWidth (2*R+2) (rawMulTrace x y) := by
  have hp₁ := product_size hx.1 hy.1
  have hp₂ := product_size hx.2.1 hy.2.1
  have hp₃ := product_size hx.1 hy.2.1
  have hp₄ := product_size hx.2.1 hy.1
  have hx₁ := magnitude_size hx.1
  have hx₂ := magnitude_size hx.2.1
  have hy₁ := magnitude_size hy.1
  have hy₂ := magnitude_size hy.2.1
  have hdx := natural_size hx.2.2
  have hdy := natural_size hy.2.2
  intro i hi
  simp only [rawMulTrace, List.mem_cons, List.mem_nil_iff, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [Instruction.width, Int.natAbs_natCast, max_le_iff] <;> constructor <;> omega

theorem rawDivTrace_width {x : Raw} {R d : ℕ} (hx : Fits x R) (hd : d ≤ 2^R) :
    TraceWidth (2*R+2) (rawDivTrace x d) := by
  have hx' := natural_size hx.2.2
  have hd' := natural_size hd
  intro i hi
  simp only [rawDivTrace, List.mem_cons, List.mem_nil_iff, or_false] at hi
  subst i
  simp only [Instruction.width, Int.natAbs_natCast, max_le_iff]
  constructor <;> omega

theorem rawNegTrace_width {x : Raw} {R : ℕ} (hx : Fits x R) :
    TraceWidth (2*R+2) (rawNegTrace x) := by
  have hr := magnitude_size hx.1
  have hi := magnitude_size hx.2.1
  intro i hm
  simp only [rawNegTrace, List.mem_cons, List.mem_nil_iff, or_false] at hm
  rcases hm with rfl | rfl <;> simp only [Instruction.width] <;> omega

theorem rawSumTrace_width {f : ℕ → Raw} {work : ℕ → List Instruction} {R n : ℕ}
    (hs : ∀ k ≤ n, Fits (sum f k) R) (hf : ∀ k < n, Fits (f k) R)
    (hw : ∀ k < n, TraceWidth (2*R+2) (work k)) :
    TraceWidth (2*R+2) (rawSumTrace f work n) := by
  induction n with
  | zero => simp [TraceWidth, rawSumTrace]
  | succ n ih =>
      apply traceWidth_append
      · apply traceWidth_append
        · exact ih (fun k hk => hs k (by omega)) (fun k hk => hf k (by omega)) (fun k hk => hw k (by omega))
        · exact hw n (by omega)
      · exact rawAddTrace_width (hs n (by omega)) (hf n (by omega))

theorem rawPowTrace_width {x : Raw} {R n : ℕ} (hx : Fits x R)
    (hp : ∀ k ≤ n, Fits (pow x k) R) : TraceWidth (2*R+2) (rawPowTrace x n) := by
  induction n with
  | zero => simp [TraceWidth, rawPowTrace]
  | succ n ih =>
      apply traceWidth_append (ih (fun k hk => hp k (by omega)))
      exact rawMulTrace_width (hp n (by omega)) hx

theorem natPowerTrace_width {a n R : ℕ} (ha : a ≤ 2^R)
    (hp : ∀ k ≤ n, a^k ≤ 2^R) : TraceWidth (2*R+2) (natPowerTrace a n) := by
  induction n with
  | zero => simp [TraceWidth, natPowerTrace]
  | succ n ih =>
      apply traceWidth_append (ih (fun k hk => hp k (by omega)))
      intro i hi
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
      subst i
      simp only [Instruction.width, Int.natAbs_natCast, max_le_iff]
      have h₁ := natural_size (hp n (by omega))
      have h₂ := natural_size ha
      constructor <;> omega

theorem intPowerTrace_width {a : ℤ} {n R : ℕ} (ha : a.natAbs ≤ 2^R)
    (hp : ∀ k ≤ n, (a^k).natAbs ≤ 2^R) : TraceWidth (2*R+2) (intPowerTrace a n) := by
  induction n with
  | zero => simp [TraceWidth, intPowerTrace]
  | succ n ih =>
      apply traceWidth_append (ih (fun k hk => hp k (by omega)))
      intro i hi
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
      subst i
      simp only [Instruction.width, max_le_iff]
      have h₁ := magnitude_size (hp n (by omega))
      have h₂ := magnitude_size ha
      constructor <;> omega

theorem factorialTrace_width {n R : ℕ} (hp : ∀ k ≤ n, k.factorial ≤ 2^R)
    (hi : ∀ k ≤ n, k ≤ 2^R) : TraceWidth (2*R+2) (factorialTrace n) := by
  induction n with
  | zero => simp [TraceWidth, factorialTrace]
  | succ n ih =>
      apply traceWidth_append (ih (fun k hk => hp k (by omega)) (fun k hk => hi k (by omega)))
      intro i hm
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hm
      have h₁ := natural_size (hi n (by omega))
      have h₂ := natural_size (hi (n+1) (by omega))
      have h₃ := natural_size (hp n (by omega))
      rcases hm with rfl | rfl <;>
        simp only [Instruction.width, Int.natAbs_natCast, Int.natAbs_one, Nat.size_one, max_le_iff] <;> constructor <;> omega

theorem atanTermTrace_width {a k R : ℕ} (ha : a ≤ 2^R) (hk : k ≤ 2^R)
    (he : 2*k+1 ≤ 2^R) (h₂ : 2 ≤ 2^R) (hp : ∀ r ≤ 2*k+1, a^r ≤ 2^R) :
    TraceWidth (2*R+2) (atanTermTrace a k) := by
  apply traceWidth_append
  · apply traceWidth_append
    · apply traceWidth_append
      · exact intPowerTrace_width (by simp; exact Nat.one_le_two_pow)
          (fun r _ => by simp; exact Nat.one_le_two_pow)
      · intro i hi
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
        have hs₁ := natural_size h₂
        have hs₂ := natural_size hk
        have hs₃ := natural_size (show 2*k ≤ 2^R by omega)
        rcases hi with rfl | rfl <;>
          norm_num only [Instruction.width, Int.natAbs_natCast, Nat.size_one, max_le_iff] <;> constructor <;> omega
    · exact natPowerTrace_width ha hp
  · intro i hi
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
    subst i
    have hs₁ := natural_size he
    have hs₂ := natural_size (hp (2*k+1) le_rfl)
    simp only [Instruction.width, Int.natAbs_natCast, max_le_iff]
    constructor <;> omega

/-- Root-synthesis widths are derived from the actual term and prefix bounds,
not supplied as an all-register-bounded premise. -/
theorem rootTrace_width {N j B L : ℕ} (hNL : N ≤ 2^L) (hj : j < N) :
    TraceWidth (2*(rootBits B L+8)+2) (rootTrace N j B) := by
  let R := rootBits B L+8
  have hR : rootBits B L ≤ R := by dsimp [R]; omega
  have hpR : 2^(rootBits B L) ≤ 2^R := Nat.pow_le_pow_right (by decide) hR
  rcases root_stored_intermediates hNL hj with ⟨has, hat, hpi, hang, hpow, hterm, hts, hexp, hn, hj₂⟩
  rcases root_integer_prefixes B L with ⟨hnp, hfact, hsign⟩
  have hbase (a : ℕ) (ha : a ≤ 256) : a ≤ 2^R := by
    have h := hnp a ha 0 (by omega) 1 (by omega)
    simpa using h.trans hpR
  have hs (a : ℕ) (ha : a ≤ 256) (k : ℕ) (hk : k ≤ B+10) : Fits (atanSum a k) R :=
    fits_mono (has a ha k hk) hR
  have ht (a : ℕ) (ha : a ≤ 256) (k : ℕ) (hk : k < B+10) : Fits (atanTerm a k) R :=
    fits_mono (hat a ha k hk) hR
  have hatWork (a : ℕ) (ha : a ≤ 256) (k : ℕ) (hk : k < B+10) :
      TraceWidth (2*R+2) (atanTermTrace a k) := by
    apply atanTermTrace_width (hbase a ha)
      ((root_loop_indices B L k (by omega)).trans hpR) ((hexp k hk).trans hpR) (hbase 2 (by decide))
    intro r hr
    exact (hnp a ha k hk r hr).trans hpR
  have hasWork (a : ℕ) (ha : a ≤ 256) : TraceWidth (2*R+2) (atanSumTrace a (B+10)) :=
    rawSumTrace_width (hs a ha) (ht a ha) (hatWork a ha)
  have h16 : Fits (ofInt 16) R := fits_mono (fits_ofInt (z:=16) (M:=4) (by norm_num)) (by dsimp [R]; omega)
  have h4 : Fits (ofInt 4) R := fits_mono (fits_ofInt (z:=4) (M:=2) (by norm_num)) (by dsimp [R]; omega)
  have hπR : Fits (piRaw B) R := fits_mono hpi hR
  have haR : Fits (angleRaw N j B) R := fits_mono hang hR
  have hb := root_stage_budgets B L
  have hπbound : piBits B ≤ R := hb.1.trans (hb.2.1.trans (by omega))
  have h16sum : Fits (mul (ofInt 16) (atanSum 5 (B+10))) R := by
    have h := fits_mul (fits_ofInt (z:=16) (M:=4) (by norm_num)) (fits_atanSum (a:=5) (by decide) (B+10))
    apply fits_mono h
    have hh : 4+atanBits (B+10)+1 ≤ piBits B := by unfold piBits; omega
    exact hh.trans hπbound
  have h4sum : Fits (mul (ofInt 4) (atanSum 239 (B+10))) R := by
    have h := fits_mul (fits_ofInt (z:=4) (M:=2) (by norm_num)) (fits_atanSum (a:=239) (by decide) (B+10))
    apply fits_mono h
    have hh : 2+atanBits (B+10)+1 ≤ piBits B := by unfold piBits; omega
    exact hh.trans hπbound
  have hpiWork : TraceWidth (2*R+2) (piTrace B) := by
    apply traceWidth_append
    · apply traceWidth_append
      · apply traceWidth_append
        · apply traceWidth_append
          · apply traceWidth_append (hasWork 5 (by decide))
            exact rawMulTrace_width h16 (hs 5 (by decide) _ le_rfl)
          · exact hasWork 239 (by decide)
        · exact rawMulTrace_width h4 (hs 239 (by decide) _ le_rfl)
      · exact rawNegTrace_width h4sum
    · exact rawAddTrace_width h16sum (fits_neg h4sum)
  have hjabs : (2*(j:ℤ)).natAbs = 2*j := by rw [Int.natAbs_mul, Int.natAbs_natCast]; rfl
  have hjR : Fits (ofInt (2*j)) R := fits_ofInt (by rw [hjabs]; exact hj₂.trans hpR)
  have hangleProduct : Fits (mul (ofInt (2*j)) (piRaw B)) R := by
    have hj' : (2*(j:ℤ)).natAbs ≤ 2^(L+1) := by
      simp only [Int.natAbs_mul, Int.natAbs_natCast]
      calc
        2*j ≤ 2*2^L := Nat.mul_le_mul_left _ (hj.le.trans hNL)
        _ = _ := by rw [pow_succ]; ring
    have h := fits_mul (fits_ofInt hj') (fits_piRaw B)
    apply fits_mono h
    have hA : L+1+piBits B+1 ≤ angleBits B L := by unfold angleBits; omega
    exact hA.trans (hb.2.1.trans (by omega))
  have hangleWork : TraceWidth (2*R+2) (angleTrace N j B) := by
    apply traceWidth_append
    · apply traceWidth_append
      · apply traceWidth_append hpiWork
        intro i hi
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
        subst i
        have h₂ := natural_size (hbase 2 (by decide))
        have hj' := natural_size (show j ≤ 2^R by omega)
        norm_num only [Instruction.width, Int.natAbs_natCast, max_le_iff]
        constructor <;> omega
      · exact rawMulTrace_width hjR hπR
    · exact rawDivTrace_width hangleProduct (hn.trans hpR)
  have htermWork (k : ℕ) (hk : k < B+68) : TraceWidth (2*R+2) (taylorTermTrace (angleRaw N j B) k) := by
    apply traceWidth_append
    · apply traceWidth_append
      · exact rawPowTrace_width (fits_imaginary haR) (fun r hr => fits_mono (hpow r (by omega)) hR)
      · exact factorialTrace_width
          (fun r hr => (hfact r (by omega)).trans hpR)
          (fun r hr => (root_loop_indices B L r (by omega)).trans hpR)
    · exact rawDivTrace_width (fits_mono (hpow k (by omega)) hR) ((hfact k (by omega)).trans hpR)
  apply traceWidth_append hangleWork
  exact rawSumTrace_width
    (fun k hk => fits_mono (hts k hk) hR)
    (fun k hk => fits_mono (hterm k hk) hR) htermWork

theorem rootTrace_bitCost {N j B L : ℕ} (hNL : N ≤ 2^L) (hj : j < N) :
    traceCost (rootTrace N j B) ≤ rootOperations B * (256*(2*(rootBits B L+8)+4)^2) := by
  have h := traceCost_bound (rootTrace N j B) _ (rootTrace_width hNL hj)
  rw [rootTrace_length] at h
  exact h.trans (Nat.mul_le_mul_right _ (rootC_operations N j B))

/-! ## Binary registers

The definitions below consume and return binary data. Semantic `Int` values
appear only in their correctness statements, never as intermediate inputs.
Removing high zero bits is a charged Boolean traversal; without it a small
integer could occupy an arbitrarily padded register.
-/

def trimCounted : List Bool → List Bool × ℕ
  | [] => ([], 1)
  | b::bs =>
    let child := trimCounted bs
    let output := match child.1, b with
      | [], false => []
      | _, _ => b::child.1
    (output, child.2+4)

theorem trimCounted_spec (bs : List Bool) :
    IntegerArithmetic.value (trimCounted bs).1 = IntegerArithmetic.value bs ∧
    (trimCounted bs).1.length = (IntegerArithmetic.value bs).size ∧
    (trimCounted bs).2 = 4*bs.length+1 := by
  induction bs with
  | nil => simp [trimCounted, IntegerArithmetic.value]
  | cons b bs ih =>
    rcases ih with ⟨hv, hl, hc⟩
    cases hchild : (trimCounted bs).1 with
    | nil =>
      have hz : IntegerArithmetic.value bs = 0 := by simpa [hchild, IntegerArithmetic.value] using hv.symm
      cases b <;> simp [trimCounted, hchild, hz, hc, IntegerArithmetic.value, digit] <;> omega
    | cons c cs =>
      have hn : IntegerArithmetic.value bs ≠ 0 := by
        intro hz
        simp [hchild, hz] at hl
      have hb : Nat.bit b (IntegerArithmetic.value bs) ≠ 0 := by
        cases b <;> simp [Nat.bit, hn]
      have hsize := Nat.size_bit hb
      have he : digit b + 2*IntegerArithmetic.value bs = Nat.bit b (IntegerArithmetic.value bs) := by
        cases b <;> simp [digit, Nat.bit]; omega
      simp only [trimCounted, hchild, IntegerArithmetic.value, List.length_cons]
      have hvc : digit c+2*IntegerArithmetic.value cs = IntegerArithmetic.value bs := by
        simpa only [hchild, IntegerArithmetic.value] using hv
      constructor
      · rw [hvc]
      constructor
      · rw [he, hsize]
        simpa [hchild] using congrArg Nat.succ hl
      · rw [hc]; omega

def canonicalize (x : SignedBits) : SignedBits × ℕ :=
  let child := trimCounted x.magnitude
  (⟨x.negative, child.1⟩, child.2+1)

theorem canonicalize_spec (x : SignedBits) :
    signedValue (canonicalize x).1 = signedValue x ∧
    (canonicalize x).1.magnitude.length = (signedValue x).natAbs.size ∧
    (canonicalize x).2 = 4*x.magnitude.length+2 := by
  rcases trimCounted_spec x.magnitude with ⟨hv, hl, hc⟩
  constructor
  · simp only [canonicalize, signedValue, hv]
  constructor
  · simpa [canonicalize, signedValue_natAbs] using hl
  · simp [canonicalize, hc]

/-- Every binary primitive stores its child once, then removes padding once. -/
def binaryAdd (x y : SignedBits) : SignedBits × ℕ :=
  let child := signedAddCounted x y
  let out := canonicalize child.1
  (out.1, child.2+out.2)
def binaryNeg (x : SignedBits) : SignedBits × ℕ := (signedNeg x, 1)
def binarySub (x y : SignedBits) : SignedBits × ℕ :=
  let ny := binaryNeg y
  let child := binaryAdd x ny.1
  (child.1, ny.2+child.2)
def binaryMul (x y : SignedBits) : SignedBits × ℕ :=
  let child := signedMulCounted x y
  let out := canonicalize child.1
  (out.1, child.2+out.2)

theorem binaryAdd_spec (x y : SignedBits) :
    signedValue (binaryAdd x y).1 = signedValue x+signedValue y ∧
    (binaryAdd x y).1.magnitude.length = (signedValue x+signedValue y).natAbs.size := by
  have hp := signedAddCounted_projections x y
  have hc := canonicalize_spec (signedAddCounted x y).1
  simpa [binaryAdd, hp.1, signedAdd_correct] using And.intro hc.1 hc.2.1

theorem binaryNeg_spec (x : SignedBits) :
    signedValue (binaryNeg x).1 = -signedValue x := signedNeg_correct x

theorem binarySub_spec (x y : SignedBits) :
    signedValue (binarySub x y).1 = signedValue x-signedValue y ∧
    (binarySub x y).1.magnitude.length = (signedValue x-signedValue y).natAbs.size := by
  have h := binaryAdd_spec x (binaryNeg y).1
  simpa [binarySub, binaryNeg_spec, sub_eq_add_neg] using h

theorem binaryMul_spec (x y : SignedBits) :
    signedValue (binaryMul x y).1 = signedValue x*signedValue y ∧
    (binaryMul x y).1.magnitude.length = (signedValue x*signedValue y).natAbs.size := by
  have hp := signedMulCounted_projections x y
  have hc := canonicalize_spec (signedMulCounted x y).1
  simpa [binaryMul, hp.1, signedMul_correct] using And.intro hc.1 hc.2.1

theorem binaryAdd_cost (x y : SignedBits) :
    (binaryAdd x y).2 ≤ 64*(max x.magnitude.length y.magnitude.length+2)^2 := by
  have hp := signedAddCounted_projections x y
  have hc := (canonicalize_spec (signedAdd x y)).2.2
  have hs := signedAddSteps_bound x y
  have hl := signedAdd_length x y
  simp only [binaryAdd, hp.1, hp.2, hc]
  have hpos : 1 ≤ max x.magnitude.length y.magnitude.length+2 := by omega
  nlinarith

theorem binaryMul_cost (x y : SignedBits) :
    (binaryMul x y).2 ≤ 128*(max x.magnitude.length y.magnitude.length+2)^2 := by
  have hp := signedMulCounted_projections x y
  have hc := (canonicalize_spec (signedMulCounted x y).1).2.2
  have hs := signedMulSteps_bound x y
  have hl := mulBits_length x.magnitude y.magnitude
  have hx := le_max_left x.magnitude.length y.magnitude.length
  have hy := le_max_right x.magnitude.length y.magnitude.length
  change (signedMulCounted x y).2 + (canonicalize (signedMulCounted x y).1).2 ≤ _
  rw [hc, hp.1, hp.2]
  change signedMulSteps x y+(4*(mulBits x.magnitude y.magnitude).length+2) ≤ _
  have hm : (x.magnitude.length+1)*(x.magnitude.length+y.magnitude.length+2) ≤
      2*(max x.magnitude.length y.magnitude.length+2)^2 := by
    calc
      _ ≤ (max x.magnitude.length y.magnitude.length+2)*(2*(max x.magnitude.length y.magnitude.length+2)) :=
        Nat.mul_le_mul (by omega) (by omega)
      _ = _ := by ring
  nlinarith

theorem binarySub_cost (x y : SignedBits) :
    (binarySub x y).2 ≤ 128*(max x.magnitude.length y.magnitude.length+2)^2 := by
  have h := binaryAdd_cost x (binaryNeg y).1
  simpa only [binarySub, binaryNeg, signedNeg] using
    (show 1+(binaryAdd x (signedNeg y)).2 ≤ _ by
      change (binaryAdd x (signedNeg y)).2 ≤ 64*(max x.magnitude.length y.magnitude.length+2)^2 at h
      have hp : 1 ≤ (max x.magnitude.length y.magnitude.length+2)^2 := Nat.one_le_pow _ _ (by omega)
      nlinarith)

/-- Euclidean quotient on existing binary registers. The divisor scan,
quotient/remainder child, negative correction, and final trimming are charged. -/
def binaryFloor (divisor : List Bool) (x : SignedBits) : SignedBits × ℕ :=
  if nonzeroBits divisor then
    let child := divideCounted divisor x.magnitude
    let rem := nonzeroBits child.1.2
    let corrected := if x.negative && rem then
      let inc := addCounted child.1.1 [true] false
      (⟨true, inc.1⟩, inc.2+8)
      else (⟨x.negative, child.1.1⟩, 8)
    let out := canonicalize corrected.1
    (out.1, divisor.length+child.2+child.1.2.length+corrected.2+out.2)
  else (⟨false, []⟩, divisor.length+2)

theorem binaryFloor_correct (divisor : List Bool) (x : SignedBits) :
    signedValue (binaryFloor divisor x).1 = signedValue x/(IntegerArithmetic.value divisor:ℤ) := by
  by_cases hD : nonzeroBits divisor = true
  · have hpos : 0 < IntegerArithmetic.value divisor := by
      by_contra hn
      have hz : IntegerArithmetic.value divisor = 0 := by omega
      have hf := (nonzeroBits_false divisor).mpr hz
      rw [hf] at hD; contradiction
    have hDi : (0:ℤ) < IntegerArithmetic.value divisor := by exact_mod_cast hpos
    have hp := divideCounted_projections divisor x.magnitude
    have hi := divideBits_correct divisor x.magnitude hpos
    have hie : (IntegerArithmetic.value x.magnitude:ℤ) =
        (IntegerArithmetic.value (divideBits divisor x.magnitude).1:ℤ)*IntegerArithmetic.value divisor+
        IntegerArithmetic.value (divideBits divisor x.magnitude).2 := by exact_mod_cast hi.1
    have hre : (IntegerArithmetic.value (divideBits divisor x.magnitude).2:ℤ) < IntegerArithmetic.value divisor := by exact_mod_cast hi.2
    have hr0 : (0:ℤ) ≤ IntegerArithmetic.value (divideBits divisor x.magnitude).2 := by positivity
    simp only [binaryFloor, hD, if_true, hp.1]
    split_ifs with hn
    · rw [(canonicalize_spec _).1, (addCounted_projections _ _ _).1]
      have hx : x.negative = true := (Bool.and_eq_true_iff.mp hn).1
      have hr : nonzeroBits (divideBits divisor x.magnitude).2 = true := (Bool.and_eq_true_iff.mp hn).2
      have hn' : IntegerArithmetic.value (divideBits divisor x.magnitude).2 ≠ 0 := by
        intro he
        rw [(nonzeroBits_false _).mpr he] at hr; contradiction
      have hrp : (0:ℤ) < IntegerArithmetic.value (divideBits divisor x.magnitude).2 := by exact_mod_cast Nat.pos_of_ne_zero hn'
      simp only [signedValue, hx, if_true, addBits_correct, IntegerArithmetic.value,
        digit_true, digit_false, mul_zero, add_zero, Nat.cast_add, Nat.cast_one]
      symm
      apply (Int.ediv_eq_iff_of_pos hDi).mpr
      constructor <;> nlinarith
    · rw [(canonicalize_spec _).1]
      cases hx : x.negative with
      | false =>
        simp only [signedValue, hx, Bool.false_eq_true, if_false]
        symm
        apply (Int.ediv_eq_iff_of_pos hDi).mpr
        constructor <;> nlinarith
      | true =>
        have hr : nonzeroBits (divideBits divisor x.magnitude).2 = false := by
          simpa only [hx, Bool.true_and, Bool.not_eq_true] using hn
        have hn' := (nonzeroBits_false _).mp hr
        have hnz : (IntegerArithmetic.value (divideBits divisor x.magnitude).2:ℤ) = 0 := by exact_mod_cast hn'
        simp only [signedValue, hx, if_true]
        symm
        apply (Int.ediv_eq_iff_of_pos hDi).mpr
        constructor <;> nlinarith
  · have hf : nonzeroBits divisor = false := by cases he : nonzeroBits divisor <;> simp_all
    have hz := (nonzeroBits_false divisor).mp hf
    simp [binaryFloor, hf, hz, signedValue, IntegerArithmetic.value]

theorem binaryFloor_canonical (divisor : List Bool) (x : SignedBits) :
    (binaryFloor divisor x).1.magnitude.length = (signedValue (binaryFloor divisor x).1).natAbs.size := by
  unfold binaryFloor
  split
  · exact (canonicalize_spec _).2.1.trans (congrArg (fun z:ℤ => z.natAbs.size) (canonicalize_spec _).1.symm)
  · rfl

theorem binaryFloor_cost (divisor : List Bool) (x : SignedBits) :
    (binaryFloor divisor x).2 ≤ 256*(max x.magnitude.length divisor.length+2)^2 := by
  have hd := le_max_right x.magnitude.length divisor.length
  have hx := le_max_left x.magnitude.length divisor.length
  by_cases hD : nonzeroBits divisor = true
  · have hp := divideCounted_projections divisor x.magnitude
    have hc := divideSteps_bound divisor x.magnitude
    have hl := divideBits_remainder_length divisor x.magnitude
    have hq := divideBits_quotient_length divisor x.magnitude
    have ha := addCounted_projections (divideBits divisor x.magnitude).1 [true] false
    have hal := addBits_length (divideBits divisor x.magnitude).1 [true] false
    have hm : (x.magnitude.length+1)*(x.magnitude.length+divisor.length+1) ≤
        2*(max x.magnitude.length divisor.length+2)^2 := by
      calc
        _ ≤ (max x.magnitude.length divisor.length+2)*(2*(max x.magnitude.length divisor.length+2)) :=
          Nat.mul_le_mul (by omega) (by omega)
        _ = _ := by ring
    simp only [binaryFloor, hD, if_true, hp.1, hp.2]
    split_ifs
    · simp only [ha.1, ha.2, (canonicalize_spec _).2.2, columnSteps_eq,
        List.length_cons, List.length_nil, hq] at *
      have hh : max x.magnitude.length (0+1) ≤ max x.magnitude.length divisor.length+1 := by omega
      nlinarith
    · simp only [(canonicalize_spec _).2.2, hq]
      nlinarith
  · have hf : nonzeroBits divisor = false := by cases he : nonzeroBits divisor <;> simp_all
    simp only [binaryFloor, hf, Bool.false_eq_true, if_false]
    have hp : max x.magnitude.length divisor.length+2 ≤ (max x.magnitude.length divisor.length+2)^2 := by
      nlinarith
    omega

/-! ## Typed binary dataflow for unreduced roots

Indices in `Register` and `RawRegisters` are denotational specifications.
The executable fields are Boolean lists. Arithmetic constructors below do
not convert a computed semantic integer back to bits.
-/
structure Register (z : ℤ) where
  bits : SignedBits
  denotes : signedValue bits = z
  canonical : bits.magnitude.length = z.natAbs.size

structure BinaryResult (α : Type) where
  value : α
  bitSteps : ℕ

/-- Boundary loading copies a canonical sign-and-magnitude encoding; the
magnitude traversal and sign cell are explicitly charged. It is used for
input and small public control constants, never semantic arithmetic results. -/
def registerInput (z : ℤ) : BinaryResult (Register z) :=
  ⟨⟨IntegerArithmetic.ofInt z, ofInt_correct z, ofInt_length z⟩, z.natAbs.size+2⟩

def Register.cast {x y : ℤ} (h : x=y) (r : Register x) : Register y :=
  ⟨r.bits, r.denotes.trans h, r.canonical.trans (congrArg (fun z:ℤ => z.natAbs.size) h)⟩

def registerAdd {x y : ℤ} (a : Register x) (b : Register y) : BinaryResult (Register (x+y)) :=
  let child := binaryAdd a.bits b.bits
  ⟨⟨child.1, by simpa only [a.denotes, b.denotes] using (binaryAdd_spec a.bits b.bits).1,
    by simpa only [a.denotes, b.denotes] using (binaryAdd_spec a.bits b.bits).2⟩, child.2⟩
def registerSub {x y : ℤ} (a : Register x) (b : Register y) : BinaryResult (Register (x-y)) :=
  let child := binarySub a.bits b.bits
  ⟨⟨child.1, by simpa only [a.denotes, b.denotes] using (binarySub_spec a.bits b.bits).1,
    by simpa only [a.denotes, b.denotes] using (binarySub_spec a.bits b.bits).2⟩, child.2⟩
def registerMul {x y : ℤ} (a : Register x) (b : Register y) : BinaryResult (Register (x*y)) :=
  let child := binaryMul a.bits b.bits
  ⟨⟨child.1, by simpa only [a.denotes, b.denotes] using (binaryMul_spec a.bits b.bits).1,
    by simpa only [a.denotes, b.denotes] using (binaryMul_spec a.bits b.bits).2⟩, child.2⟩
def registerNeg {x : ℤ} (a : Register x) : BinaryResult (Register (-x)) :=
  let child := binaryNeg a.bits
  ⟨⟨child.1, by simpa only [a.denotes] using binaryNeg_spec a.bits,
    by change a.bits.magnitude.length = (-x).natAbs.size; simpa using a.canonical⟩, child.2⟩
def registerFloor {x : ℤ} {d : ℕ} (a : Register x) (b : Register (d:ℤ)) :
    BinaryResult (Register (x/(d:ℤ))) :=
  let child := binaryFloor b.bits.magnitude a.bits
  have hd : IntegerArithmetic.value b.bits.magnitude = d := by
    simpa only [signedValue_natAbs, Int.natAbs_natCast] using congrArg Int.natAbs b.denotes
  have he : signedValue child.1 = x/(d:ℤ) := by
    simpa only [hd, a.denotes] using binaryFloor_correct b.bits.magnitude a.bits
  ⟨⟨child.1, he, (binaryFloor_canonical b.bits.magnitude a.bits).trans (congrArg (fun z:ℤ => z.natAbs.size) he)⟩, child.2⟩

structure RawRegisters (r : Raw) where
  re : Register r.re
  im : Register r.im
  den : Register (r.den:ℤ)

def binaryRawInput (z : ℤ) : BinaryResult (RawRegisters (RationalWorkBounds.ofInt z)) :=
  let re := registerInput z
  let im := registerInput 0
  let den := registerInput 1
  ⟨⟨re.value, im.value, den.value⟩, re.bitSteps+im.bitSteps+den.bitSteps⟩

def binaryRawAdd {x y : Raw} (a : RawRegisters x) (b : RawRegisters y) :
    BinaryResult (RawRegisters (add x y)) :=
  let r1 := registerMul a.re b.den
  let r2 := registerMul b.re a.den
  let re := registerAdd r1.value r2.value
  let i1 := registerMul a.im b.den
  let i2 := registerMul b.im a.den
  let im := registerAdd i1.value i2.value
  let den := registerMul a.den b.den
  ⟨⟨re.value, im.value, den.value.cast (by simp only [add, Nat.cast_mul])⟩,
    r1.bitSteps+r2.bitSteps+re.bitSteps+i1.bitSteps+i2.bitSteps+im.bitSteps+den.bitSteps⟩

def binaryRawMul {x y : Raw} (a : RawRegisters x) (b : RawRegisters y) :
    BinaryResult (RawRegisters (mul x y)) :=
  let r1 := registerMul a.re b.re
  let r2 := registerMul a.im b.im
  let re := registerSub r1.value r2.value
  let i1 := registerMul a.re b.im
  let i2 := registerMul a.im b.re
  let im := registerAdd i1.value i2.value
  let den := registerMul a.den b.den
  ⟨⟨re.value, im.value, den.value.cast (by simp only [mul, Nat.cast_mul])⟩,
    r1.bitSteps+r2.bitSteps+re.bitSteps+i1.bitSteps+i2.bitSteps+im.bitSteps+den.bitSteps⟩

def binaryRawNeg {x : Raw} (a : RawRegisters x) : BinaryResult (RawRegisters (neg x)) :=
  let re := registerNeg a.re
  let im := registerNeg a.im
  ⟨⟨re.value, im.value, a.den⟩, re.bitSteps+im.bitSteps⟩

def binaryRawDivNat {x : Raw} {d : ℕ} (a : RawRegisters x) (b : Register (d:ℤ)) :
    BinaryResult (RawRegisters (divNat x d)) :=
  let den := registerMul a.den b
  ⟨⟨a.re, a.im, den.value.cast (by simp only [divNat, Nat.cast_mul])⟩, den.bitSteps⟩

def binaryRawImaginary {x : Raw} (a : RawRegisters x) : BinaryResult (RawRegisters (imaginary x)) :=
  let zero := registerInput 0
  ⟨⟨zero.value, a.re, a.den⟩, zero.bitSteps⟩

def binaryRawPow {x : Raw} (a : RawRegisters x) : (k : ℕ) → BinaryResult (RawRegisters (pow x k))
  | 0 => binaryRawInput 1
  | k+1 =>
    let child := binaryRawPow a k
    let output := binaryRawMul child.value a
    ⟨output.value, child.bitSteps+output.bitSteps⟩

def binaryRawSum (f : ℕ → Raw) (work : (k : ℕ) → BinaryResult (RawRegisters (f k))) :
    (n : ℕ) → BinaryResult (RawRegisters (sum f n))
  | 0 => binaryRawInput 0
  | n+1 =>
    let child := binaryRawSum f work n
    let term := work n
    let output := binaryRawAdd child.value term.value
    ⟨output.value, child.bitSteps+term.bitSteps+output.bitSteps⟩

def binaryRegisterPower {a : ℤ} (base : Register a) : (k : ℕ) → BinaryResult (Register (a^k))
  | 0 =>
    let child := registerInput 1
    ⟨child.value.cast (by simp only [pow_zero]), child.bitSteps⟩
  | k+1 =>
    let child := binaryRegisterPower base k
    let output := registerMul child.value base
    ⟨output.value.cast (by rw [pow_succ]), child.bitSteps+output.bitSteps⟩

def binaryFactorial : (k : ℕ) → BinaryResult (Register (k.factorial:ℤ))
  | 0 => registerInput 1
  | k+1 =>
    let child := binaryFactorial k
    let index := registerInput (k:ℤ)
    let one := registerInput 1
    let next := registerAdd index.value one.value
    let output := registerMul child.value next.value
    ⟨output.value.cast (by rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]; ring),
      child.bitSteps+index.bitSteps+one.bitSteps+next.bitSteps+output.bitSteps⟩

def binaryAtanTerm (a k : ℕ) : BinaryResult (RawRegisters (atanTerm a k)) :=
  let minusOne := registerInput (-1)
  let sign := binaryRegisterPower minusOne.value k
  let index := registerInput (k:ℤ)
  let two := registerInput 2
  let one := registerInput 1
  let twice := registerMul two.value index.value
  let exponent := registerAdd twice.value one.value
  let base := registerInput (a:ℤ)
  let power := binaryRegisterPower base.value (2*k+1)
  let denominator := registerMul exponent.value power.value
  let zero := registerInput 0
  ⟨⟨sign.value, zero.value, denominator.value.cast (by simp only [atanTerm, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat])⟩,
    minusOne.bitSteps+sign.bitSteps+index.bitSteps+two.bitSteps+one.bitSteps+
      twice.bitSteps+exponent.bitSteps+base.bitSteps+power.bitSteps+denominator.bitSteps+zero.bitSteps⟩

def binaryAtanSum (a n : ℕ) : BinaryResult (RawRegisters (atanSum a n)) :=
  binaryRawSum (atanTerm a) (binaryAtanTerm a) n

def binaryPi (B : ℕ) : BinaryResult (RawRegisters (piRaw B)) :=
  let first := binaryAtanSum 5 (B+10)
  let sixteen := binaryRawInput 16
  let firstScaled := binaryRawMul sixteen.value first.value
  let second := binaryAtanSum 239 (B+10)
  let four := binaryRawInput 4
  let secondScaled := binaryRawMul four.value second.value
  let secondNeg := binaryRawNeg secondScaled.value
  let output := binaryRawAdd firstScaled.value secondNeg.value
  ⟨output.value, first.bitSteps+sixteen.bitSteps+firstScaled.bitSteps+second.bitSteps+
    four.bitSteps+secondScaled.bitSteps+secondNeg.bitSteps+output.bitSteps⟩

def binaryAngle (N j B : ℕ) : BinaryResult (RawRegisters (angleRaw N j B)) :=
  let pi := binaryPi B
  let two := registerInput 2
  let index := registerInput (j:ℤ)
  let twice := registerMul two.value index.value
  let zero := registerInput 0
  let one := registerInput 1
  let multiplier : RawRegisters (RationalWorkBounds.ofInt (2*j)) := ⟨twice.value, zero.value, one.value⟩
  let numerator := binaryRawMul multiplier pi.value
  let denominator := registerInput (N:ℤ)
  let output := binaryRawDivNat numerator.value denominator.value
  ⟨output.value, pi.bitSteps+two.bitSteps+index.bitSteps+twice.bitSteps+zero.bitSteps+one.bitSteps+
    numerator.bitSteps+denominator.bitSteps+output.bitSteps⟩

@[inline] def binaryTaylorTerm {x : Raw} (a : RawRegisters x) (k : ℕ) : BinaryResult (RawRegisters (taylorTerm x k)) :=
  let imaginary := binaryRawImaginary a
  let power := binaryRawPow imaginary.value k
  let factorial := binaryFactorial k
  let output := binaryRawDivNat power.value factorial.value
  ⟨output.value, imaginary.bitSteps+power.bitSteps+factorial.bitSteps+output.bitSteps⟩

def binaryTaylor {x : Raw} (a : RawRegisters x) (n : ℕ) : BinaryResult (RawRegisters (taylor x n)) :=
  binaryRawSum (taylorTerm x) (fun k => binaryTaylorTerm a k) n

/-- Actual bit dataflow for the finite unreduced root formula. All large
intermediate numerators and denominators are passed as existing registers. -/
def binaryRoot (N j B : ℕ) : BinaryResult (RawRegisters (rootRaw N j B)) :=
  let angle := binaryAngle N j B
  let output := binaryTaylor angle.value (B+68)
  ⟨output.value, angle.bitSteps+output.bitSteps⟩

theorem binaryRoot_correct (N j B : ℕ) :
    signedValue (binaryRoot N j B).value.re.bits = (rootRaw N j B).re ∧
    signedValue (binaryRoot N j B).value.im.bits = (rootRaw N j B).im ∧
    signedValue (binaryRoot N j B).value.den.bits = ((rootRaw N j B).den:ℤ) :=
  ⟨(binaryRoot N j B).value.re.denotes, (binaryRoot N j B).value.im.denotes,
    (binaryRoot N j B).value.den.denotes⟩

def instructionPrice (i : Instruction) : ℕ := 256*(i.width+2)^2
def schedulePrice (t : List Instruction) : ℕ := (t.map instructionPrice).sum

@[simp] theorem schedulePrice_nil : schedulePrice [] = 0 := rfl
@[simp] theorem schedulePrice_cons (i : Instruction) (t : List Instruction) :
    schedulePrice (i::t) = instructionPrice i+schedulePrice t := rfl

@[simp] theorem schedulePrice_append (s t : List Instruction) :
    schedulePrice (s++t) = schedulePrice s+schedulePrice t := by simp [schedulePrice]

 theorem registerAdd_price {x y : ℤ} (a : Register x) (b : Register y) :
    (registerAdd a b).bitSteps ≤ instructionPrice (.add x y) := by
  have h := binaryAdd_cost a.bits b.bits
  rw [a.canonical, b.canonical] at h
  change _ ≤ 256*(max x.natAbs.size y.natAbs.size+2)^2
  exact h.trans (Nat.mul_le_mul_right _ (by decide))
 theorem registerSub_price {x y : ℤ} (a : Register x) (b : Register y) :
    (registerSub a b).bitSteps ≤ instructionPrice (.sub x y) := by
  have h := binarySub_cost a.bits b.bits
  rw [a.canonical, b.canonical] at h
  change _ ≤ 256*(max x.natAbs.size y.natAbs.size+2)^2
  exact h.trans (Nat.mul_le_mul_right _ (by decide))
 theorem registerMul_price {x y : ℤ} (a : Register x) (b : Register y) :
    (registerMul a b).bitSteps ≤ instructionPrice (.mul x y) := by
  have h := binaryMul_cost a.bits b.bits
  rw [a.canonical, b.canonical] at h
  change _ ≤ 256*(max x.natAbs.size y.natAbs.size+2)^2
  exact h.trans (Nat.mul_le_mul_right _ (by decide))
 theorem registerNeg_price {x : ℤ} (a : Register x) :
    (registerNeg a).bitSteps ≤ instructionPrice (.neg x) := by
  change 1 ≤ 256*(x.natAbs.size+2)^2
  have hp : 1 ≤ (x.natAbs.size+2)^2 := Nat.one_le_pow _ _ (by omega)
  omega
 theorem registerFloor_price {x : ℤ} {d : ℕ} (a : Register x) (b : Register (d:ℤ)) :
    (registerFloor a b).bitSteps ≤ instructionPrice (.floorDiv d x) := by
  have h := binaryFloor_cost b.bits.magnitude a.bits
  rw [a.canonical, b.canonical, Int.natAbs_natCast, max_comm] at h
  exact h

 theorem binaryRawAdd_price {x y : Raw} (a : RawRegisters x) (b : RawRegisters y) :
    (binaryRawAdd a b).bitSteps ≤ schedulePrice (rawAddTrace x y) := by
  have h1 := registerMul_price a.re b.den
  have h2 := registerMul_price b.re a.den
  have h3 := registerAdd_price (registerMul a.re b.den).value (registerMul b.re a.den).value
  have h4 := registerMul_price a.im b.den
  have h5 := registerMul_price b.im a.den
  have h6 := registerAdd_price (registerMul a.im b.den).value (registerMul b.im a.den).value
  have h7 := registerMul_price a.den b.den
  simp only [binaryRawAdd, rawAddTrace, schedulePrice, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil] at *
  omega
 theorem binaryRawMul_price {x y : Raw} (a : RawRegisters x) (b : RawRegisters y) :
    (binaryRawMul a b).bitSteps ≤ schedulePrice (rawMulTrace x y) := by
  have h1 := registerMul_price a.re b.re
  have h2 := registerMul_price a.im b.im
  have h3 := registerSub_price (registerMul a.re b.re).value (registerMul a.im b.im).value
  have h4 := registerMul_price a.re b.im
  have h5 := registerMul_price a.im b.re
  have h6 := registerAdd_price (registerMul a.re b.im).value (registerMul a.im b.re).value
  have h7 := registerMul_price a.den b.den
  simp only [binaryRawMul, rawMulTrace, schedulePrice, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil] at *
  omega
 theorem binaryRawNeg_price {x : Raw} (a : RawRegisters x) :
    (binaryRawNeg a).bitSteps ≤ schedulePrice (rawNegTrace x) := by
  have h1 := registerNeg_price a.re
  have h2 := registerNeg_price a.im
  simp only [binaryRawNeg, rawNegTrace, schedulePrice, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil] at *
  omega
 theorem binaryRawDivNat_price {x : Raw} {d : ℕ} (a : RawRegisters x) (b : Register (d:ℤ)) :
    (binaryRawDivNat a b).bitSteps ≤ schedulePrice (rawDivTrace x d) := by
  simpa only [binaryRawDivNat, rawDivTrace, schedulePrice, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, Nat.add_zero] using registerMul_price a.den b

 theorem schedulePrice_width (t : List Instruction) (W : ℕ) (h : TraceWidth W t) :
    schedulePrice t ≤ t.length*(256*(W+2)^2) := by
  induction t with
  | nil => simp [schedulePrice]
  | cons i t ih =>
    have hi : instructionPrice i ≤ 256*(W+2)^2 := by
      unfold instructionPrice; gcongr; exact h i (by simp)
    have ht := ih (fun j hj => h j (by simp [hj]))
    simp only [schedulePrice, List.map_cons, List.sum_cons, List.length_cons] at *
    nlinarith

theorem registerInput_bound {z : ℤ} {R : ℕ} (h : z.natAbs ≤ 2^R) :
    (registerInput z).bitSteps ≤ R+3 := by
  have hs := magnitude_size h
  change z.natAbs.size+2 ≤ _
  omega

theorem binaryRawPow_cost {x : Raw} (a : RawRegisters x) (k : ℕ) :
    (binaryRawPow a k).bitSteps ≤ schedulePrice (rawPowTrace x k)+8 := by
  induction k with
  | zero => simp [binaryRawPow, rawPowTrace, schedulePrice, binaryRawInput, registerInput]
  | succ k ih =>
    have h := binaryRawMul_price (binaryRawPow a k).value a
    simp only [binaryRawPow, rawPowTrace, schedulePrice_append]
    omega

theorem binaryRawSum_cost (f : ℕ → Raw) (work : (k : ℕ) → BinaryResult (RawRegisters (f k)))
    (traces : ℕ → List Instruction) (n C : ℕ)
    (hwork : ∀ k < n, (work k).bitSteps ≤ schedulePrice (traces k)+C) :
    (binaryRawSum f work n).bitSteps ≤ schedulePrice (rawSumTrace f traces n)+7+n*C := by
  induction n with
  | zero => simp [binaryRawSum, rawSumTrace, schedulePrice, binaryRawInput, registerInput]
  | succ n ih =>
    have hc := ih (fun k hk => hwork k (by omega))
    have ht := hwork n (by omega)
    have ha := binaryRawAdd_price (binaryRawSum f work n).value (work n).value
    simp only [binaryRawSum, rawSumTrace, schedulePrice_append]
    nlinarith

theorem binaryRegisterPower_cost {a : ℤ} (base : Register a) (k : ℕ) :
    (binaryRegisterPower base k).bitSteps ≤ schedulePrice (intPowerTrace a k)+3 := by
  induction k with
  | zero => simp [binaryRegisterPower, intPowerTrace, schedulePrice, registerInput]
  | succ k ih =>
    have h := registerMul_price (binaryRegisterPower base k).value base
    simp only [binaryRegisterPower, intPowerTrace, schedulePrice_append, schedulePrice_cons, schedulePrice_nil, Nat.add_zero]
    omega

theorem natPowerTrace_eq (a k : ℕ) : natPowerTrace a k = intPowerTrace (a:ℤ) k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [natPowerTrace, intPowerTrace, ih, Nat.cast_pow]

theorem binaryFactorial_cost (k R : ℕ) (hindex : ∀ r ≤ k, r ≤ 2^R) :
    (binaryFactorial k).bitSteps ≤ schedulePrice (factorialTrace k)+(2*k+1)*(R+3) := by
  induction k with
  | zero => simp [binaryFactorial, factorialTrace, schedulePrice, registerInput]
  | succ k ih =>
    have hc := ih (fun r hr => hindex r (by omega))
    have hi := registerInput_bound (z:=(k:ℤ)) (by simpa only [Int.natAbs_natCast] using hindex k (by omega))
    have ha := registerAdd_price (registerInput (k:ℤ)).value (registerInput 1).value
    have hm := registerMul_price (binaryFactorial k).value
      (registerAdd (registerInput (k:ℤ)).value (registerInput 1).value).value
    simp only [binaryFactorial, factorialTrace, schedulePrice_append, schedulePrice_cons, schedulePrice_nil, Nat.add_zero]
    have hcast : ((k+1:ℕ):ℤ) = (k:ℤ)+1 := by norm_cast
    rw [hcast]
    have hone : (registerInput 1).bitSteps = 3 := rfl
    rw [hone]
    nlinarith

theorem binaryAtanTerm_cost (a k R : ℕ) (ha : a ≤ 2^R) (hk : k ≤ 2^R) :
    (binaryAtanTerm a k).bitSteps ≤ schedulePrice (atanTermTrace a k)+8*(R+3) := by
  have hs := binaryRegisterPower_cost (registerInput (-1)).value k
  have hp := binaryRegisterPower_cost (registerInput (a:ℤ)).value (2*k+1)
  have hi := registerInput_bound (z:=(k:ℤ)) (by simpa only [Int.natAbs_natCast] using hk)
  have hb := registerInput_bound (z:=(a:ℤ)) (by simpa only [Int.natAbs_natCast] using ha)
  have ht := registerMul_price (registerInput 2).value (registerInput (k:ℤ)).value
  have he := registerAdd_price (registerMul (registerInput 2).value (registerInput (k:ℤ)).value).value
    (registerInput 1).value
  have hd := registerMul_price
    (registerAdd (registerMul (registerInput 2).value (registerInput (k:ℤ)).value).value (registerInput 1).value).value
    (binaryRegisterPower (registerInput (a:ℤ)).value (2*k+1)).value
  have hcast : ((2*k+1:ℕ):ℤ) = 2*(k:ℤ)+1 := by norm_cast
  simp only [binaryAtanTerm, atanTermTrace, schedulePrice_append, natPowerTrace_eq, schedulePrice_cons, schedulePrice_nil, Nat.add_zero]
  simp only [Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat, hcast]
  have h₀ : (registerInput 0).bitSteps = 2 := rfl
  have h₁ : (registerInput 1).bitSteps = 3 := rfl
  have h₂ : (registerInput 2).bitSteps = 4 := rfl
  have hm : (registerInput (-1)).bitSteps = 3 := rfl
  rw [h₀, h₁, h₂, hm]
  nlinarith

theorem binaryAtanSum_cost (a n R : ℕ) (ha : a ≤ 2^R) (hi : ∀ k < n, k ≤ 2^R) :
    (binaryAtanSum a n).bitSteps ≤ schedulePrice (atanSumTrace a n)+7+n*(8*(R+3)) :=
  binaryRawSum_cost _ _ _ n _ (fun k hk => binaryAtanTerm_cost a k R ha (hi k hk))

theorem binaryPi_cost (B R : ℕ) (ha : 239 ≤ 2^R) (hi : ∀ k < B+10, k ≤ 2^R) :
    (binaryPi B).bitSteps ≤ schedulePrice (piTrace B)+36+16*(B+10)*(R+3) := by
  have h1 := binaryAtanSum_cost 5 (B+10) R (by omega) hi
  have h2 := binaryRawMul_price (binaryRawInput 16).value (binaryAtanSum 5 (B+10)).value
  have h3 := binaryAtanSum_cost 239 (B+10) R ha hi
  have h4 := binaryRawMul_price (binaryRawInput 4).value (binaryAtanSum 239 (B+10)).value
  have h5 := binaryRawNeg_price (binaryRawMul (binaryRawInput 4).value (binaryAtanSum 239 (B+10)).value).value
  have h6 := binaryRawAdd_price
    (binaryRawMul (binaryRawInput 16).value (binaryAtanSum 5 (B+10)).value).value
    (binaryRawNeg (binaryRawMul (binaryRawInput 4).value (binaryAtanSum 239 (B+10)).value).value).value
  simp only [binaryPi, piTrace, schedulePrice_append]
  have hs : (binaryRawInput 16).bitSteps = 12 := rfl
  have hf : (binaryRawInput 4).bitSteps = 10 := rfl
  rw [hs, hf]
  nlinarith

theorem binaryAngle_cost (N j B R : ℕ) (ha : 239 ≤ 2^R)
    (hi : ∀ k < B+10, k ≤ 2^R) (hj : j ≤ 2^R) (hN : N ≤ 2^R) :
    (binaryAngle N j B).bitSteps ≤ schedulePrice (angleTrace N j B)+36+16*(B+10)*(R+3)+5*(R+3) := by
  have hp := binaryPi_cost B R ha hi
  have hm := registerMul_price (registerInput 2).value (registerInput (j:ℤ)).value
  have hj' := registerInput_bound (z:=(j:ℤ)) (by simpa only [Int.natAbs_natCast] using hj)
  have hN' := registerInput_bound (z:=(N:ℤ)) (by simpa only [Int.natAbs_natCast] using hN)
  let a : RawRegisters (RationalWorkBounds.ofInt (2*j)) :=
    ⟨(registerMul (registerInput 2).value (registerInput (j:ℤ)).value).value,
      (registerInput 0).value, (registerInput 1).value⟩
  have hx := binaryRawMul_price a (binaryPi B).value
  have hd := binaryRawDivNat_price (binaryRawMul a (binaryPi B).value).value (registerInput (N:ℤ)).value
  change _ ≤ _ at hx hd
  simp only [binaryAngle, angleTrace, schedulePrice_append, schedulePrice_cons, schedulePrice_nil, Nat.add_zero]
  have h₀ : (registerInput 0).bitSteps = 2 := rfl
  have h₁ : (registerInput 1).bitSteps = 3 := rfl
  have h₂ : (registerInput 2).bitSteps = 4 := rfl
  rw [h₀, h₁, h₂]
  dsimp only [a] at hx hd
  nlinarith

theorem binaryTaylorTerm_cost {x : Raw} (a : RawRegisters x) (k R : ℕ)
    (hi : ∀ r ≤ k, r ≤ 2^R) :
    (binaryTaylorTerm a k).bitSteps ≤ schedulePrice (taylorTermTrace x k)+10+(2*k+1)*(R+3) := by
  have hp := binaryRawPow_cost (binaryRawImaginary a).value k
  have hf := binaryFactorial_cost k R hi
  have hd := binaryRawDivNat_price (binaryRawPow (binaryRawImaginary a).value k).value (binaryFactorial k).value
  simp only [binaryTaylorTerm, taylorTermTrace, schedulePrice_append]
  have hz : (binaryRawImaginary a).bitSteps = 2 := rfl
  rw [hz]
  omega

def rootLoadAllowance (B R : ℕ) : ℕ :=
  36+16*(B+10)*(R+3)+5*(R+3)+7+(B+68)*(10+(2*(B+68)+1)*(R+3))

/-- This is the cost of the actual binary root program, not replayed literal
operands. Arithmetic is linked to the ghost schedule and every boundary load
of a public dimension, index, or small constant is separately charged. -/
theorem binaryRoot_bitCost {N j B L : ℕ} (hNL : N ≤ 2^L) (hj : j < N) :
    (binaryRoot N j B).bitSteps ≤
      rootOperations B*(256*(2*(rootBits B L+8)+4)^2)+rootLoadAllowance B (rootBits B L+8) := by
  let R := rootBits B L+8
  have hpR : 2^(rootBits B L) ≤ 2^R := Nat.pow_le_pow_right (by decide) (by dsimp [R]; omega)
  have hi : ∀ k ≤ B+68, k ≤ 2^R := fun k hk => (root_loop_indices B L k hk).trans hpR
  have ha : 239 ≤ 2^R := by
    have h := (root_integer_prefixes B L).1 239 (by decide) 0 (by omega) 1 (by omega)
    simpa using h.trans hpR
  have hN : N ≤ 2^R := (root_stored_intermediates hNL hj).2.2.2.2.2.2.2.2.1.trans hpR
  have hang := binaryAngle_cost N j B R ha (fun k hk => hi k (by omega)) (by omega) hN
  have ht := binaryRawSum_cost (taylorTerm (angleRaw N j B))
    (fun k => binaryTaylorTerm (binaryAngle N j B).value k) (taylorTermTrace (angleRaw N j B)) (B+68)
    (10+(2*(B+68)+1)*(R+3)) (by
      intro k hk
      have h := binaryTaylorTerm_cost (binaryAngle N j B).value k R (fun r hr => hi r (by omega))
      have hm : (2*k+1)*(R+3) ≤ (2*(B+68)+1)*(R+3) := Nat.mul_le_mul_right _ (by omega)
      omega)
  have hs := schedulePrice_width (rootTrace N j B) _ (rootTrace_width hNL hj)
  rw [rootTrace_length] at hs
  have hs' := hs.trans (Nat.mul_le_mul_right _ (rootC_operations N j B))
  simp only [rootTrace, taylorTrace, schedulePrice_append] at hs'
  norm_num only [Nat.add_assoc] at hs'
  simp only [binaryRoot, binaryTaylor, rootLoadAllowance]
  dsimp only [R] at hang ht
  omega

theorem rootLoadAllowance_bound (B R : ℕ) :
    rootLoadAllowance B R ≤ 100*(B+79)^2*(R+3) := by
  unfold rootLoadAllowance
  nlinarith

/-- Concrete polynomial bit-circuit budget for root synthesis. The exponent
includes the unreduced numerator widths, all Boolean trimming, and public
index/constant input loading. Public loop control is a separate index model. -/
theorem binaryRoot_polynomial {N j B L : ℕ} (hNL : N ≤ 2^L) (hj : j < N) :
    (binaryRoot N j B).bitSteps ≤ 4294967296*(B+L+79)^10 := by
  let S := B+L+79
  have hS : 1 ≤ S := by dsimp [S]; omega
  have hS4 : 1 ≤ S^4 := Nat.one_le_pow _ _ hS
  have hb : rootBits B L ≤ 128*S^4 := by
    apply (rootBits_polynomial B L).trans
    gcongr
    dsimp [S]; omega
  have ho : rootOperations B ≤ 100*S^2 := by
    apply (rootOperations_polynomial B L).trans
    gcongr
    dsimp [S]; omega
  have hw : 2*(rootBits B L+8)+4 ≤ 276*S^4 := by omega
  have harith : rootOperations B*(256*(2*(rootBits B L+8)+4)^2) ≤ 1950105600*S^10 := by
    calc
      _ ≤ (100*S^2)*(256*(276*S^4)^2) := Nat.mul_le_mul ho (Nat.mul_le_mul_left 256 (Nat.pow_le_pow_left hw 2))
      _ = _ := by ring
  have hload : rootLoadAllowance B (rootBits B L+8) ≤ 13900*S^10 := by
    calc
      _ ≤ 100*(B+79)^2*(rootBits B L+8+3) := rootLoadAllowance_bound _ _
      _ ≤ 100*S^2*(139*S^4) := by
        apply Nat.mul_le_mul
        · gcongr; dsimp [S]; omega
        · omega
      _ = 13900*S^6 := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hS (by decide))
  have h := binaryRoot_bitCost (B:=B) hNL hj
  change _ ≤ 4294967296*S^10
  nlinarith

#print axioms trimCounted_spec
#print axioms canonicalize_spec
#print axioms binaryAdd_spec
#print axioms binaryMul_spec
#print axioms binaryFloor_correct
#print axioms binaryFloor_cost
#print axioms binaryRoot_correct
#print axioms binaryRoot_bitCost
#print axioms binaryRoot_polynomial
#print axioms rootTrace_width
#print axioms rootTrace_bitCost
#print axioms rawSumTrace_width
#print axioms rawPowTrace_width
#print axioms rootTrace_length

#print axioms floorCounted_correct
#print axioms floorCounted_bound
#print axioms instruction_correct
#print axioms instruction_cost
#print axioms traceCost_bound
end ThinMatrix.FFTBitCost
