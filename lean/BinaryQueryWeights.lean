import BitArraySimulation
import BackendScalarBits

/-!
Actual signed-bit construction of the LOW residual weights. The factorial
state carries its binary loop index as well as its binary accumulator. No
integer interpretation, integer-to-bits conversion, or native factorial is
used by the executable definitions. Natural parameters control finite loops.
-/
namespace ThinMatrix.BinaryQueryWeights

open BitArraySimulation
open ToomBitCost.Counted
abbrev Counted := ToomCook.Counted

set_option maxRecDepth 10000
set_option maxHeartbeats 3000000

structure FactorialState where
  index : Signed
  accumulator : Signed

def factorialLoop : ℕ → Counted FactorialState
  | 0 => ⟨⟨zero,one⟩,2⟩
  | n+1 =>
    let prev := factorialLoop n
    let next := add prev.value.index one
    let product := mul next.value prev.value.accumulator
    ⟨⟨next.value,product.value⟩,prev.operations+next.operations+product.operations+2⟩

theorem factorialLoop_value (n : ℕ) :
    denote (factorialLoop n).value.index = (n:ℤ) ∧
    denote (factorialLoop n).value.accumulator = (n.factorial:ℤ) := by
  induction n with
  | zero => simp [factorialLoop]
  | succ n ih =>
    simp only [factorialLoop,add_value,mul_value,denote_one,ih.1,ih.2]
    constructor
    · push_cast; rfl
    · rw [Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one]

def factorial (n : ℕ) : Counted Signed :=
  let result := factorialLoop n
  ⟨result.value.accumulator,result.operations+1⟩

theorem factorial_value (n : ℕ) : denote (factorial n).value = (n.factorial:ℤ) :=
  (factorialLoop_value n).2

def choose (n h : ℕ) : Counted Signed :=
  if h ≤ n then
    let a := factorial n
    let b := factorial h
    let c := factorial (n-h)
    let denominator := mul b.value c.value
    let result := divide denominator.value.val.magnitude a.value
    ⟨result.value,a.operations+b.operations+c.operations+denominator.operations+result.operations+2⟩
  else ⟨zero,1⟩

theorem positive_magnitude_bits (x : Signed) (D : ℕ) (hx : denote x = (D:ℤ)) :
    x.val.magnitude = D.bits := by
  have h := congrArg IntegerArithmetic.SignedBits.magnitude (canonical_eq x)
  simpa only [IntegerArithmetic.ofInt,hx,Int.natAbs_natCast] using h

theorem choose_value (n h : ℕ) : denote (choose n h).value = (n.choose h:ℤ) := by
  unfold choose
  split_ifs with hh
  · let d := mul (factorial h).value (factorial (n-h)).value
    have hd : denote d.value = (h.factorial*(n-h).factorial:ℕ) := by
      simp only [d,mul_value,factorial_value,Nat.cast_mul]
    have hbits := positive_magnitude_bits d.value _ hd
    rw [divide_value _ _ _ hbits]
    apply ToomBitCost.bitPrimitives_correct.divide
    · exact Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _)
    · rw [factorial_value]
      exact_mod_cast (show n.factorial = (h.factorial*(n-h).factorial)*n.choose h by
        rw [←Nat.choose_mul_factorial_mul_factorial hh]; ring)
  · rw [denote_zero,Nat.choose_eq_zero_of_lt (by omega)]
    rfl

def sign : ℕ → Counted Signed
  | 0 => ⟨one,1⟩
  | n+1 =>
    let previous := sign n
    let result := negate previous.value
    ⟨result.value,previous.operations+result.operations+1⟩

theorem sign_value (n : ℕ) : denote (sign n).value = (-1:ℤ)^n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [sign,negate_value,ih,pow_succ]; ring

theorem sign_cost (n : ℕ) : (sign n).operations = 5*n+1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [sign,negate_cost,ih]; omega

def weight (k t degree : ℕ) : Counted Signed :=
  let a := sign (t-degree-1)
  let b := choose (k-degree-1) (t-degree-1)
  let result := mul a.value b.value
  ⟨result.value,a.operations+b.operations+result.operations+2⟩

theorem weight_value (k t degree : ℕ) :
    denote (weight k t degree).value = (CachedLowQuery.weightCounted k t degree).1 := by
  simp only [weight,mul_value,sign_value,choose_value,CachedLowQuery.weightCounted,
    CachedLowQuery.signCounted_value,CachedLowQuery.chooseCounted_value]

theorem add_price (B : ℕ) (x y : Signed)
    (hx : (denote x).natAbs.size ≤ B) (hy : (denote y).natAbs.size ≤ B) :
    (add x y).operations ≤ BackendScalarBits.scalarUnit B := by
  rw [add_cost]
  have hc := ToomBitCost.bitPrimitive_add_cost (denote x) (denote y)
  have hm : max (denote x).natAbs.size (denote y).natAbs.size ≤ B := max_le hx hy
  unfold BackendScalarBits.scalarUnit
  nlinarith

theorem mul_price (B : ℕ) (x y : Signed)
    (hx : (denote x).natAbs.size ≤ B) (hy : (denote y).natAbs.size ≤ B) :
    (mul x y).operations ≤ 2*BackendScalarBits.scalarUnit B := by
  rw [mul_cost]
  have hc := ToomBitCost.bitPrimitive_mul_cost (denote x) (denote y)
  have hm : 60*((denote x).natAbs.size+1)*
      ((denote x).natAbs.size+(denote y).natAbs.size+2)+4 ≤
      60*(B+1)*(2*B+2)+4 := by gcongr; omega
  unfold BackendScalarBits.scalarUnit
  nlinarith

theorem divide_price (B : ℕ) (d x : Signed)
    (hd : (denote d).natAbs.size ≤ B) (hx : (denote x).natAbs.size ≤ B) :
    (divide d.val.magnitude x).operations ≤ BackendScalarBits.scalarUnit B := by
  have hc := IntegerArithmetic.normalizedDivideCounted_steps d.val.magnitude x.val
  simp only [divide,copyBits_value,copyBits_cost,magnitude_length] at hc ⊢
  have hm : 30*((denote x).natAbs.size+1)*
      ((denote x).natAbs.size+(denote d).natAbs.size+1)+4 ≤
      30*(B+1)*(2*B+1)+4 := by gcongr; omega
  unfold BackendScalarBits.scalarUnit
  nlinarith

theorem factorial_width (M n : ℕ) (hn : n ≤ M) :
    n.factorial.size ≤ (M+1)^2+1 := by
  have h := CachedLowQuery.factorial_temporary_bound M n hn
  rw [CachedLowQuery.factorialCounted_value] at h
  exact (Nat.size_le_size h).trans_eq Nat.size_pow

theorem index_width (M n : ℕ) (hn : n ≤ M) : n.size ≤ (M+1)^2+1 := by
  exact (Nat.size_le_size (hn.trans (Nat.self_le_factorial M))).trans (factorial_width M M le_rfl)

theorem factorialLoop_cost (M n B : ℕ) (hn : n ≤ M)
    (hB : (M+1)^2+1 ≤ B) :
    (factorialLoop n).operations ≤ (5*n+2)*BackendScalarBits.scalarUnit B := by
  induction n with
  | zero => simp only [factorialLoop]; unfold BackendScalarBits.scalarUnit; nlinarith
  | succ n ih =>
    have ih := ih (by omega)
    have hi := factorialLoop_value n
    have hnext : denote (add (factorialLoop n).value.index one).value = (n+1:ℕ) := by
      rw [add_value,hi.1,denote_one]; push_cast; rfl
    have ha := add_price B (factorialLoop n).value.index one
      (by rw [hi.1,Int.natAbs_natCast]; exact (index_width M n (by omega)).trans hB)
      (by simp only [denote_one,Int.natAbs_one,Nat.size_one]; omega)
    have hm := mul_price B (add (factorialLoop n).value.index one).value
      (factorialLoop n).value.accumulator
      (by rw [hnext,Int.natAbs_natCast]; exact (index_width M (n+1) hn).trans hB)
      (by rw [hi.2,Int.natAbs_natCast]; exact (factorial_width M n (by omega)).trans hB)
    simp only [factorialLoop]
    unfold BackendScalarBits.scalarUnit at *
    nlinarith

theorem factorial_cost (M n B : ℕ) (hn : n ≤ M) (hB : (M+1)^2+1 ≤ B) :
    (factorial n).operations ≤ (5*n+3)*BackendScalarBits.scalarUnit B := by
  have h := factorialLoop_cost M n B hn hB
  simp only [factorial]
  unfold BackendScalarBits.scalarUnit at *
  nlinarith

theorem choose_le_factorial (n h : ℕ) : n.choose h ≤ n.factorial := by
  by_cases hh : h ≤ n
  · have hd : 0 < h.factorial*(n-h).factorial :=
      Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _)
    calc
      n.choose h ≤ n.choose h*(h.factorial*(n-h).factorial) :=
        Nat.le_mul_of_pos_right _ hd
      _ = n.factorial := by rw [←mul_assoc,Nat.choose_mul_factorial_mul_factorial hh]
  · rw [Nat.choose_eq_zero_of_lt (by omega)]
    exact Nat.zero_le _

theorem choose_width (M n h : ℕ) (hn : n ≤ M) :
    (denote (choose n h).value).natAbs.size ≤ (M+1)^2+1 := by
  rw [choose_value,Int.natAbs_natCast]
  exact (Nat.size_le_size (choose_le_factorial n h)).trans (factorial_width M n hn)

theorem choose_cost (k t degree : ℕ) :
    (choose (k-degree-1) (t-degree-1)).operations ≤
      20*(k+t+2)*BackendScalarBits.scalarUnit (CachedLowQuery.weightBitWidth k t) := by
  let B := CachedLowQuery.weightBitWidth k t
  have hB : (k+t+1+1)^2+1 ≤ B := by
    dsimp [B,CachedLowQuery.weightBitWidth]
    nlinarith
  have ha := factorial_cost (k+t+1) (k-degree-1) B (by omega) hB
  have hb := factorial_cost (k+t+1) (t-degree-1) B (by omega) hB
  have hc := factorial_cost (k+t+1) (k-degree-1-(t-degree-1)) B (by omega) hB
  have hw := BackendScalarBits.weight_setup_widths k t degree
  dsimp only at hw
  simp only [CachedLowQuery.factorialCounted_value] at hw
  have hm := mul_price B (factorial (t-degree-1)).value
      (factorial (k-degree-1-(t-degree-1))).value
    (by rw [factorial_value,Int.natAbs_natCast]; exact hw.2.1)
    (by rw [factorial_value,Int.natAbs_natCast]; exact hw.2.2.1)
  have hd := divide_price B
    (mul (factorial (t-degree-1)).value
      (factorial (k-degree-1-(t-degree-1))).value).value
    (factorial (k-degree-1)).value
    (by simp only [mul_value,factorial_value,←Nat.cast_mul,Int.natAbs_natCast]; exact hw.2.2.2)
    (by rw [factorial_value,Int.natAbs_natCast]; exact hw.1)
  change _ ≤ 20*(k+t+2)*BackendScalarBits.scalarUnit B
  unfold choose
  split_ifs with hh
  · dsimp only
    have hn : k-degree-1 ≤ k+t+1 := by omega
    have hh' : t-degree-1 ≤ k+t+1 := by omega
    have hr : k-degree-1-(t-degree-1) ≤ k+t+1 := by omega
    have hsum : 5*(k-degree-1)+3+(5*(t-degree-1)+3)+
        (5*(k-degree-1-(t-degree-1))+3)+3 ≤ 20*(k+t+2)-1 := by omega
    have hU : 2 ≤ BackendScalarBits.scalarUnit B := by
      unfold BackendScalarBits.scalarUnit; nlinarith
    nlinarith
  · dsimp only
    unfold BackendScalarBits.scalarUnit
    nlinarith

theorem sign_width (n : ℕ) : (denote (sign n).value).natAbs.size = 1 := by
  rw [sign_value,Int.natAbs_pow]
  norm_num

theorem weight_width (k t degree : ℕ) :
    (denote (weight k t degree).value).natAbs.size ≤ CachedLowQuery.weightBitWidth k t := by
  have hw := choose_width (k+t+1) (k-degree-1) (t-degree-1) (by omega)
  simp only [weight,mul_value,Int.natAbs_mul,sign_value,Int.natAbs_pow] at *
  norm_num at *
  unfold CachedLowQuery.weightBitWidth
  nlinarith

theorem weight_cost (k t degree : ℕ) :
    (weight k t degree).operations ≤
      100*(k+t+2)*BackendScalarBits.scalarUnit (CachedLowQuery.weightBitWidth k t) := by
  let B := CachedLowQuery.weightBitWidth k t
  have hB : (k+t+1+1)^2+1 ≤ B := by dsimp [B,CachedLowQuery.weightBitWidth]; nlinarith
  have hs := sign_cost (t-degree-1)
  have hc := choose_cost k t degree
  have hm := mul_price B (sign (t-degree-1)).value (choose (k-degree-1) (t-degree-1)).value
    (by rw [sign_width]; dsimp [B,CachedLowQuery.weightBitWidth]; omega)
    ((choose_width (k+t+1) (k-degree-1) (t-degree-1) (by omega)).trans hB)
  have hU : 10 ≤ BackendScalarBits.scalarUnit B := by
    unfold BackendScalarBits.scalarUnit; nlinarith
  change _ ≤ 100*(k+t+2)*BackendScalarBits.scalarUnit B
  change (choose (k-degree-1) (t-degree-1)).operations ≤
      20*(k+t+2)*BackendScalarBits.scalarUnit B at hc
  simp only [weight]
  nlinarith [show t-degree-1 ≤ k+t+2 by omega]

#print axioms factorialLoop_value
#print axioms choose_value
#print axioms weight_value
#print axioms factorial_cost
#print axioms choose_cost
#print axioms weight_width
#print axioms weight_cost

end ThinMatrix.BinaryQueryWeights
