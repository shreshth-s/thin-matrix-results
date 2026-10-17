import Mathlib
import RootsApproximation

/-!
# Unreduced rational arithmetic budgets

Numerators are integers and the shared denominator is a natural number.
The operations below never compute a gcd. `Fits M` bounds magnitudes by `2^M`,
so each integer has at most `M+1` magnitude bits (plus a sign).
Operation counts describe the displayed arithmetic schedule, not the runtime
of Lean's rational implementation or an extracted word-RAM program.
-/

namespace ThinMatrix.RationalWorkBounds
open scoped BigOperators

structure Raw where
  re : ℤ
  im : ℤ
  den : ℕ
  deriving DecidableEq

def Valid (x : Raw) : Prop := 0 < x.den

def Fits (x : Raw) (M : ℕ) : Prop :=
  x.re.natAbs ≤ 2^M ∧ x.im.natAbs ≤ 2^M ∧ x.den ≤ 2^M

def value (x : Raw) : ℚ × ℚ := ((x.re : ℚ) / x.den, (x.im : ℚ) / x.den)
def ofInt (z : ℤ) : Raw := ⟨z, 0, 1⟩
def add (x y : Raw) : Raw :=
  ⟨x.re*(y.den : ℤ)+y.re*(x.den : ℤ),
   x.im*(y.den : ℤ)+y.im*(x.den : ℤ), x.den*y.den⟩
def neg (x : Raw) : Raw := ⟨-x.re, -x.im, x.den⟩
def mul (x y : Raw) : Raw :=
  ⟨x.re*y.re-x.im*y.im, x.re*y.im+x.im*y.re, x.den*y.den⟩
def divNat (x : Raw) (d : ℕ) : Raw := ⟨x.re, x.im, x.den*d⟩
def imaginary (x : Raw) : Raw := ⟨0, x.re, x.den⟩
def pow (x : Raw) : ℕ → Raw
  | 0 => ofInt 1
  | k+1 => mul (pow x k) x
def sum (f : ℕ → Raw) : ℕ → Raw
  | 0 => ofInt 0
  | n+1 => add (sum f n) (f n)

theorem valid_ofInt (z : ℤ) : Valid (ofInt z) := by simp [Valid, ofInt]
theorem valid_add {x y : Raw} (hx : Valid x) (hy : Valid y) : Valid (add x y) :=
  Nat.mul_pos hx hy
theorem valid_neg {x : Raw} (hx : Valid x) : Valid (neg x) := hx
theorem valid_mul {x y : Raw} (hx : Valid x) (hy : Valid y) : Valid (mul x y) :=
  Nat.mul_pos hx hy
theorem valid_divNat {x : Raw} (hx : Valid x) {d : ℕ} (hd : 0 < d) : Valid (divNat x d) :=
  Nat.mul_pos hx hd
theorem valid_pow {x : Raw} (hx : Valid x) (k : ℕ) : Valid (pow x k) := by
  induction k with
  | zero => exact valid_ofInt _
  | succ k ih => exact valid_mul ih hx
theorem valid_sum {f : ℕ → Raw} {n : ℕ} (h : ∀ k < n, Valid (f k)) : Valid (sum f n) := by
  induction n with
  | zero => exact valid_ofInt _
  | succ n ih => exact valid_add (ih (fun k hk => h k (by omega))) (h n (by omega))

theorem value_ofInt (z : ℤ) : value (ofInt z) = ((z : ℚ), 0) := by simp [value, ofInt]
theorem value_add {x y : Raw} (hx : Valid x) (hy : Valid y) :
    value (add x y) = value x + value y := by
  have hx' : (x.den : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hx
  have hy' : (y.den : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hy
  apply Prod.ext <;> simp only [value, add, Int.cast_add, Int.cast_mul,
    Int.cast_natCast, Nat.cast_mul, Prod.fst_add, Prod.snd_add] <;> field_simp
theorem value_neg (x : Raw) : value (neg x) = -value x := by
  apply Prod.ext <;> simp [value, neg, neg_div]
def complexMul (x y : ℚ × ℚ) : ℚ × ℚ :=
  (x.1*y.1-x.2*y.2, x.1*y.2+x.2*y.1)
theorem value_mul {x y : Raw} (hx : Valid x) (hy : Valid y) :
    value (mul x y) = complexMul (value x) (value y) := by
  have hx' : (x.den : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hx
  have hy' : (y.den : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hy
  apply Prod.ext <;> simp only [value, mul, complexMul, Int.cast_sub, Int.cast_add,
    Int.cast_mul, Nat.cast_mul] <;> field_simp
theorem value_divNat (x : Raw) (d : ℕ) :
    value (divNat x d) = ((value x).1 / d, (value x).2 / d) := by
  apply Prod.ext <;> simp [value, divNat, div_mul_eq_div_div]

theorem fits_mono {x : Raw} {M K : ℕ} (h : Fits x M) (hMK : M ≤ K) : Fits x K := by
  have hp : 2^M ≤ 2^K := Nat.pow_le_pow_right (by decide) hMK
  exact ⟨h.1.trans hp, h.2.1.trans hp, h.2.2.trans hp⟩

theorem fits_ofInt {z : ℤ} {M : ℕ} (hz : z.natAbs ≤ 2^M) : Fits (ofInt z) M := by
  exact ⟨hz, by simp [ofInt], by simpa [ofInt] using Nat.one_le_two_pow⟩

theorem fits_neg {x : Raw} {M : ℕ} (hx : Fits x M) : Fits (neg x) M := by
  simpa [Fits, neg] using hx

theorem abs_cross {a b : ℤ} {d e M K : ℕ}
    (ha : a.natAbs ≤ 2^M) (hb : b.natAbs ≤ 2^K)
    (hd : d ≤ 2^M) (he : e ≤ 2^K) :
    (a*(e : ℤ)+b*(d : ℤ)).natAbs ≤ 2^(M+K+1) := by
  calc
    _ ≤ (a*(e : ℤ)).natAbs+(b*(d : ℤ)).natAbs := Int.natAbs_add_le _ _
    _ ≤ 2^M*2^K+2^K*2^M := by
      simp only [Int.natAbs_mul, Int.natAbs_natCast]
      exact Nat.add_le_add (Nat.mul_le_mul ha he) (Nat.mul_le_mul hb hd)
    _ = _ := by simp [pow_add]; ring

theorem fits_add {x y : Raw} {M K : ℕ} (hx : Fits x M) (hy : Fits y K) :
    Fits (add x y) (M+K+1) := by
  refine ⟨abs_cross hx.1 hy.1 hx.2.2 hy.2.2,
    abs_cross hx.2.1 hy.2.1 hx.2.2 hy.2.2, ?_⟩
  change x.den*y.den ≤ _
  calc
    _ ≤ 2^M*2^K := Nat.mul_le_mul hx.2.2 hy.2.2
    _ = 2^(M+K) := (pow_add ..).symm
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (by omega)

theorem abs_two_products {a b c d : ℤ} {M K : ℕ}
    (ha : a.natAbs ≤ 2^M) (hb : b.natAbs ≤ 2^M)
    (hc : c.natAbs ≤ 2^K) (hd : d.natAbs ≤ 2^K) :
    (a*c+b*d).natAbs ≤ 2^(M+K+1) := by
  calc
    _ ≤ (a*c).natAbs+(b*d).natAbs := Int.natAbs_add_le _ _
    _ ≤ 2^M*2^K+2^M*2^K := by
      simp only [Int.natAbs_mul]
      exact Nat.add_le_add (Nat.mul_le_mul ha hc) (Nat.mul_le_mul hb hd)
    _ = _ := by simp [pow_add]; ring

theorem fits_mul {x y : Raw} {M K : ℕ} (hx : Fits x M) (hy : Fits y K) :
    Fits (mul x y) (M+K+1) := by
  refine ⟨?_, abs_two_products hx.1 hx.2.1 hy.2.1 hy.1, ?_⟩
  · change (x.re*y.re-x.im*y.im).natAbs ≤ _
    simpa [sub_eq_add_neg, neg_mul] using
      abs_two_products hx.1 (show (-x.im).natAbs ≤ 2^M by simpa using hx.2.1) hy.1 hy.2.1
  · change x.den*y.den ≤ _
    calc
      _ ≤ 2^M*2^K := Nat.mul_le_mul hx.2.2 hy.2.2
      _ = 2^(M+K) := (pow_add ..).symm
      _ ≤ _ := Nat.pow_le_pow_right (by decide) (by omega)

theorem fits_divNat {x : Raw} {M K d : ℕ} (hx : Fits x M) (hd : d ≤ 2^K) :
    Fits (divNat x d) (M+K) := by
  have hp : 2^M ≤ 2^(M+K) := Nat.pow_le_pow_right (by decide) (by omega)
  exact ⟨hx.1.trans hp, hx.2.1.trans hp, by
    change x.den*d ≤ _
    simpa [pow_add] using Nat.mul_le_mul hx.2.2 hd⟩

theorem fits_imaginary {x : Raw} {M : ℕ} (hx : Fits x M) : Fits (imaginary x) M :=
  ⟨by simp [imaginary], hx.1, hx.2.2⟩

theorem fits_pow {x : Raw} {M : ℕ} (hx : Fits x M) (k : ℕ) :
    Fits (pow x k) (k*(M+1)) := by
  induction k with
  | zero => exact fits_ofInt (by norm_num)
  | succ k ih =>
      convert fits_mul ih hx using 1; congr 1; ring

/-- Summing n unreduced fractions with M-bit magnitude bounds uses at most
n(M+1)+1 magnitude bits. This includes denominator and both numerators. -/
theorem fits_sum {f : ℕ → Raw} {n M : ℕ} (h : ∀ k < n, Fits (f k) M) :
    Fits (sum f n) (n*(M+1)) := by
  induction n with
  | zero => exact fits_ofInt (by norm_num)
  | succ n ih =>
      have hs := fits_add (ih (fun k hk => h k (by omega))) (h n (by omega))
      convert hs using 1; congr 1; ring

theorem factorial_bound (k : ℕ) : k.factorial ≤ 2^(k*k) := by
  calc
    _ ≤ k^k := Nat.factorial_le_pow k
    _ ≤ (2^k)^k := Nat.pow_le_pow_left (Nat.lt_two_pow_self (n := k)).le _
    _ = _ := by rw [pow_mul]

/-- `Fits` is an explicit bit-length certificate, without reduced fractions. -/
theorem fits_bits {x : Raw} {M : ℕ} (hx : Fits x M) :
    x.re.natAbs.size ≤ M+1 ∧ x.im.natAbs.size ≤ M+1 ∧ x.den.size ≤ M+1 := by
  have hlt : 2^M < 2^(M+1) := by
    calc
      2^M < 2^M*2 := by
        have : 0 < 2^M := by positivity
        omega
      _ = 2^(M+1) := (pow_succ ..).symm
  exact ⟨Nat.size_le.mpr (hx.1.trans_lt hlt), Nat.size_le.mpr (hx.2.1.trans_lt hlt),
    Nat.size_le.mpr (hx.2.2.trans_lt hlt)⟩

/-! Direct unreduced implementation of the finite Machin/Taylor formulas. -/

def atanTerm (a k : ℕ) : Raw :=
  ⟨(-1)^k, 0, (2*k+1)*a^(2*k+1)⟩
def atanSum (a n : ℕ) : Raw := sum (atanTerm a) n
def piRaw (B : ℕ) : Raw :=
  add (mul (ofInt 16) (atanSum 5 (B+10)))
    (neg (mul (ofInt 4) (atanSum 239 (B+10))))
def angleRaw (N j B : ℕ) : Raw := divNat (mul (ofInt (2*j)) (piRaw B)) N
def taylorTerm (x : Raw) (k : ℕ) : Raw := divNat (pow (imaginary x) k) k.factorial
def taylor (x : Raw) (n : ℕ) : Raw := sum (taylorTerm x) n
def rootRaw (N j B : ℕ) : Raw := taylor (angleRaw N j B) (B+68)

theorem valid_atanTerm {a : ℕ} (ha : 0 < a) (k : ℕ) : Valid (atanTerm a k) := by
  unfold Valid atanTerm
  positivity
theorem valid_atanSum {a : ℕ} (ha : 0 < a) (n : ℕ) : Valid (atanSum a n) :=
  valid_sum (fun k _ => valid_atanTerm ha k)
theorem valid_piRaw (B : ℕ) : Valid (piRaw B) :=
  valid_add (valid_mul (valid_ofInt _) (valid_atanSum (by decide) _))
    (valid_neg (valid_mul (valid_ofInt _) (valid_atanSum (by decide) _)))
theorem valid_angleRaw {N : ℕ} (hN : 0 < N) (j B : ℕ) : Valid (angleRaw N j B) :=
  valid_divNat (valid_mul (valid_ofInt _) (valid_piRaw B)) hN
theorem valid_taylorTerm {x : Raw} (hx : Valid x) (k : ℕ) : Valid (taylorTerm x k) :=
  valid_divNat (valid_pow (x := imaginary x) hx k) (Nat.factorial_pos k)
theorem valid_taylor {x : Raw} (hx : Valid x) (n : ℕ) : Valid (taylor x n) :=
  valid_sum (fun k _ => valid_taylorTerm hx k)
theorem valid_rootRaw {N : ℕ} (hN : 0 < N) (j B : ℕ) : Valid (rootRaw N j B) :=
  valid_taylor (valid_angleRaw hN j B) _

theorem value_sum {f : ℕ → Raw} {n : ℕ} (h : ∀ k < n, Valid (f k)) :
    value (sum f n) = ∑ k ∈ Finset.range n, value (f k) := by
  induction n with
  | zero => simp [sum, value_ofInt]
  | succ n ih =>
      rw [sum, value_add (valid_sum (fun k hk => h k (by omega))) (h n (by omega)),
        ih (fun k hk => h k (by omega)), Finset.sum_range_succ]

theorem value_atanTerm {a : ℕ} (ha : 0 < a) (k : ℕ) :
    value (atanTerm a k) = ((-1)^k*(1/(a : ℚ))^(2*k+1)/(2*k+1), 0) := by
  have ha' : (a : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt ha
  have hk : (2*(k : ℚ)+1) ≠ 0 := by positivity
  apply Prod.ext
  · simp only [value, atanTerm, Int.cast_pow, Int.cast_neg, Int.cast_one,
      Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one, Nat.cast_pow, one_div_pow]
    field_simp
  · simp [value, atanTerm]

theorem value_atanSum {a : ℕ} (ha : 0 < a) (n : ℕ) :
    value (atanSum a n) = (RootsApproximation.atanApprox (1/(a : ℚ)) n, 0) := by
  rw [atanSum, value_sum (fun k _ => valid_atanTerm ha k)]
  simp_rw [value_atanTerm ha]
  apply Prod.ext <;> simp [RootsApproximation.atanApprox, Prod.fst_sum, Prod.snd_sum]

theorem value_piRaw (B : ℕ) : value (piRaw B) = (RootsApproximation.piApprox B, 0) := by
  rw [piRaw, value_add
    (valid_mul (valid_ofInt _) (valid_atanSum (by decide) _))
    (valid_neg (valid_mul (valid_ofInt _) (valid_atanSum (by decide) _))),
    value_mul (valid_ofInt _) (valid_atanSum (by decide) _), value_neg,
    value_mul (valid_ofInt _) (valid_atanSum (by decide) _),
    value_ofInt, value_ofInt, value_atanSum (by decide), value_atanSum (by decide)]
  apply Prod.ext <;> simp [complexMul, RootsApproximation.piApprox]; ring

theorem value_angleRaw (N j B : ℕ) :
    value (angleRaw N j B) = (RootsApproximation.rootAngle N j B, 0) := by
  rw [angleRaw, value_divNat, value_mul (valid_ofInt _) (valid_piRaw B),
    value_ofInt, value_piRaw]
  apply Prod.ext <;> simp [complexMul, RootsApproximation.rootAngle]; ring

theorem value_pow {x : Raw} (hx : Valid x) (k : ℕ) :
    value (pow x k) = RootsApproximation.ratPow (value x) k := by
  induction k with
  | zero => simp [pow, value_ofInt, RootsApproximation.ratPow]
  | succ k ih =>
      rw [pow, value_mul (valid_pow hx k) hx, ih, RootsApproximation.ratPow]
      rfl

theorem value_imaginary (x : Raw) : value (imaginary x) = (0, (value x).1) := by
  simp [value, imaginary]

theorem value_taylorTerm {x : Raw} (hx : Valid x) (k : ℕ) :
    value (taylorTerm x k) = RootsApproximation.ratScale (1/(k.factorial : ℚ))
      (RootsApproximation.ratPow (0, (value x).1) k) := by
  rw [taylorTerm, value_divNat, value_pow (x := imaginary x) hx, value_imaginary]
  apply Prod.ext <;> simp [RootsApproximation.ratScale, div_eq_mul_inv, mul_comm]

theorem value_taylor {x : Raw} (hx : Valid x) (n : ℕ) :
    value (taylor x n) = RootsApproximation.expApprox (value x).1 n := by
  rw [taylor, value_sum (fun k _ => valid_taylorTerm hx k)]
  simp_rw [value_taylorTerm hx]
  rfl

/-- The unreduced evaluator computes exactly the independently bounded formula. -/
theorem value_rootRaw {N : ℕ} (hN : 0 < N) (j B : ℕ) :
    value (rootRaw N j B) = RootsApproximation.rootApprox N j B := by
  rw [rootRaw, value_taylor (valid_angleRaw hN j B), value_angleRaw]
  rfl

theorem fits_atanTerm {a : ℕ} (ha : a ≤ 256) (k : ℕ) :
    Fits (atanTerm a k) (9*(2*k+1)) := by
  refine ⟨?_, by simp [atanTerm], ?_⟩
  · simp only [atanTerm, Int.natAbs_pow, Int.natAbs_neg, Int.natAbs_one, one_pow]
    exact Nat.one_le_two_pow
  · change (2*k+1)*a^(2*k+1) ≤ _
    calc
      _ ≤ 2^(2*k+1)*(2^8)^(2*k+1) :=
        Nat.mul_le_mul (Nat.lt_two_pow_self (n := 2*k+1)).le
          (Nat.pow_le_pow_left ha _)
      _ = _ := by rw [← pow_mul, ← pow_add]; congr 1; ring

def atanBits (n : ℕ) : ℕ := n*(18*n+10)
def piBits (B : ℕ) : ℕ := 2*atanBits (B+10)+9
def angleBits (B L : ℕ) : ℕ := piBits B+2*L+2
def rootBits (B L : ℕ) : ℕ :=
  (B+68)*((B+68)*(angleBits B L+1)+(B+68)^2+1)

theorem fits_atanSum {a : ℕ} (ha : a ≤ 256) (n : ℕ) :
    Fits (atanSum a n) (atanBits n) := by
  apply fits_sum
  intro k hk
  exact fits_mono (fits_atanTerm ha k) (by omega)

theorem fits_piRaw (B : ℕ) : Fits (piRaw B) (piBits B) := by
  have h₅ := fits_mul (fits_ofInt (z := 16) (M := 4) (by norm_num)) (fits_atanSum (a := 5) (by decide) (B+10))
  have h₂₃₉ := fits_neg (fits_mul (fits_ofInt (z := 4) (M := 2) (by norm_num)) (fits_atanSum (a := 239) (by decide) (B+10)))
  have hh := fits_add h₅ h₂₃₉
  change Fits (piRaw B) (4+atanBits (B+10)+1+(2+atanBits (B+10)+1)+1) at hh
  have he : piBits B = 4+atanBits (B+10)+1+(2+atanBits (B+10)+1)+1 := by
    unfold piBits
    omega
  rw [he]
  exact hh

theorem fits_angleRaw {N j B L : ℕ} (hN : N ≤ 2^L) (hj : j < N) :
    Fits (angleRaw N j B) (angleBits B L) := by
  have hj' : (2*(j : ℤ)).natAbs ≤ 2^(L+1) := by
    simp only [Int.natAbs_mul, Int.natAbs_natCast]
    calc
      2*j ≤ 2*2^L := Nat.mul_le_mul_left _ (hj.le.trans hN)
      _ = _ := by rw [pow_succ]; ring
  have hm := fits_mul (fits_ofInt hj') (fits_piRaw B)
  have hh := fits_divNat hm hN
  change Fits (angleRaw N j B) (L+1+piBits B+1+L) at hh
  have he : angleBits B L = L+1+piBits B+1+L := by
    unfold angleBits
    omega
  rw [he]
  exact hh

theorem fits_taylorTerm {x : Raw} {M : ℕ} (hx : Fits x M) (k : ℕ) :
    Fits (taylorTerm x k) (k*(M+1)+k*k) :=
  fits_divNat (fits_pow (fits_imaginary hx) k) (factorial_bound k)

theorem fits_taylor {x : Raw} {M : ℕ} (hx : Fits x M) (n : ℕ) :
    Fits (taylor x n) (n*(n*(M+1)+n*n+1)) := by
  apply fits_sum
  intro k hk
  apply fits_mono (fits_taylorTerm hx k)
  exact Nat.add_le_add (Nat.mul_le_mul_right _ hk.le) (Nat.mul_le_mul hk.le hk.le)

theorem fits_rootRaw {N j B L : ℕ} (hN : N ≤ 2^L) (hj : j < N) :
    Fits (rootRaw N j B) (rootBits B L) := by
  simpa [rootRaw, rootBits, pow_two] using fits_taylor (fits_angleRaw hN hj) (B+68)

theorem rootRaw_bits {N j B L : ℕ} (hN : N ≤ 2^L) (hj : j < N) :
    (rootRaw N j B).re.natAbs.size ≤ rootBits B L+1 ∧
    (rootRaw N j B).im.natAbs.size ≤ rootBits B L+1 ∧
    (rootRaw N j B).den.size ≤ rootBits B L+1 := fits_bits (fits_rootRaw hN hj)

/-! A joint result/work evaluator for the explicitly unreduced schedule.
Each integer addition, subtraction, or multiplication costs one here.
The seven operations in `add`/`mul` include the denominator multiplication.
This is a finite arithmetic-operation ledger, separate from bit-cost pricing.
-/

structure Computation where
  result : Raw
  operations : ℕ

def literal (x : Raw) : Computation := ⟨x, 0⟩
def addC (x y : Computation) : Computation :=
  ⟨add x.result y.result, x.operations+y.operations+7⟩
def mulC (x y : Computation) : Computation :=
  ⟨mul x.result y.result, x.operations+y.operations+7⟩
def negC (x : Computation) : Computation := ⟨neg x.result, x.operations+2⟩
def divNatC (x : Computation) (d dOperations : ℕ) : Computation :=
  ⟨divNat x.result d, x.operations+dOperations+1⟩
def powC (x : Raw) : ℕ → Computation
  | 0 => literal (ofInt 1)
  | k+1 => mulC (powC x k) (literal x)
def sumC (f : ℕ → Computation) : ℕ → Computation
  | 0 => literal (ofInt 0)
  | n+1 => addC (sumC f n) (f n)

def natPowerC (a : ℕ) : ℕ → ℕ × ℕ
  | 0 => (1, 0)
  | k+1 => let previous := natPowerC a k; (previous.1*a, previous.2+1)
def intPowerC (a : ℤ) : ℕ → ℤ × ℕ
  | 0 => (1, 0)
  | k+1 => let previous := intPowerC a k; (previous.1*a, previous.2+1)
def factorialC : ℕ → ℕ × ℕ
  | 0 => (1, 0)
  | k+1 => let previous := factorialC k; (previous.1*(k+1), previous.2+2)

theorem natPowerC_eq (a k : ℕ) : natPowerC a k = (a^k, k) := by
  induction k with
  | zero => rfl
  | succ k ih => simp [natPowerC, ih, pow_succ]
theorem intPowerC_eq (a : ℤ) (k : ℕ) : intPowerC a k = (a^k, k) := by
  induction k with
  | zero => simp [intPowerC]
  | succ k ih => simp [intPowerC, ih, pow_succ]
theorem factorialC_eq (k : ℕ) : factorialC k = (k.factorial, 2*k) := by
  induction k with
  | zero => rfl
  | succ k ih => simp [factorialC, ih, Nat.factorial_succ, Nat.mul_comm, Nat.mul_add, Nat.add_mul]

theorem powC_result (x : Raw) (k : ℕ) : (powC x k).result = pow x k := by
  induction k <;> simp_all [powC, pow, literal, mulC]
theorem powC_operations (x : Raw) (k : ℕ) : (powC x k).operations = 7*k := by
  induction k <;> simp_all [powC, literal, mulC, Nat.mul_add]
theorem sumC_result (f : ℕ → Computation) (n : ℕ) :
    (sumC f n).result = sum (fun k => (f k).result) n := by
  induction n <;> simp_all [sumC, sum, literal, addC]
theorem sumC_operations {f : ℕ → Computation} {n K : ℕ}
    (h : ∀ k < n, (f k).operations ≤ K) : (sumC f n).operations ≤ n*(K+7) := by
  induction n with
  | zero => simp [sumC, literal]
  | succ n ih =>
      have hp := ih (fun k hk => h k (by omega))
      have hf := h n (by omega)
      simp only [sumC, addC]
      nlinarith

def atanTermC (a k : ℕ) : Computation :=
  let sign := intPowerC (-1) k
  let exponent := 2*k+1
  let denominatorPower := natPowerC a exponent
  ⟨⟨sign.1, 0, exponent*denominatorPower.1⟩, sign.2+denominatorPower.2+3⟩
def atanSumC (a n : ℕ) : Computation := sumC (atanTermC a) n
def piC (B : ℕ) : Computation :=
  addC (mulC (literal (ofInt 16)) (atanSumC 5 (B+10)))
    (negC (mulC (literal (ofInt 4)) (atanSumC 239 (B+10))))
def angleC (N j B : ℕ) : Computation :=
  divNatC (mulC ⟨ofInt (2*j), 1⟩ (piC B)) N 0
def taylorTermC (x : Raw) (k : ℕ) : Computation :=
  let factorial := factorialC k
  divNatC (powC (imaginary x) k) factorial.1 factorial.2
def taylorC (x : Raw) (n : ℕ) : Computation := sumC (taylorTermC x) n
def rootC (N j B : ℕ) : Computation :=
  let angle := angleC N j B
  let exponential := taylorC angle.result (B+68)
  ⟨exponential.result, angle.operations+exponential.operations⟩

theorem atanTermC_result (a k : ℕ) : (atanTermC a k).result = atanTerm a k := by
  simp [atanTermC, intPowerC_eq, natPowerC_eq, atanTerm]
theorem atanTermC_operations (a k : ℕ) : (atanTermC a k).operations = 3*k+4 := by
  simp [atanTermC, intPowerC_eq, natPowerC_eq]
  omega
theorem atanSumC_result (a n : ℕ) : (atanSumC a n).result = atanSum a n := by
  simp [atanSumC, sumC_result, atanTermC_result, atanSum]
theorem atanSumC_operations (a n : ℕ) :
    (atanSumC a n).operations ≤ n*(3*n+11) := by
  apply sumC_operations
  intro k hk
  rw [atanTermC_operations]
  omega
theorem piC_result (B : ℕ) : (piC B).result = piRaw B := by
  simp [piC, addC, mulC, negC, literal, atanSumC_result, piRaw]
theorem piC_operations (B : ℕ) :
    (piC B).operations ≤ 2*(B+10)*(3*(B+10)+11)+23 := by
  have h₅ := atanSumC_operations 5 (B+10)
  have h₂₃₉ := atanSumC_operations 239 (B+10)
  simp only [piC, addC, mulC, literal, negC]
  nlinarith
theorem angleC_result (N j B : ℕ) : (angleC N j B).result = angleRaw N j B := by
  simp [angleC, divNatC, mulC, piC_result, angleRaw]
theorem angleC_operations (N j B : ℕ) :
    (angleC N j B).operations ≤ 2*(B+10)*(3*(B+10)+11)+32 := by
  have hp := piC_operations B
  simp only [angleC, divNatC, mulC]
  omega
theorem taylorTermC_result (x : Raw) (k : ℕ) :
    (taylorTermC x k).result = taylorTerm x k := by
  simp [taylorTermC, factorialC_eq, divNatC, powC_result, taylorTerm]
theorem taylorTermC_operations (x : Raw) (k : ℕ) :
    (taylorTermC x k).operations = 9*k+1 := by
  simp [taylorTermC, factorialC_eq, divNatC, powC_operations]
  omega
theorem taylorC_result (x : Raw) (n : ℕ) : (taylorC x n).result = taylor x n := by
  simp [taylorC, sumC_result, taylorTermC_result, taylor]
theorem taylorC_operations (x : Raw) (n : ℕ) :
    (taylorC x n).operations ≤ n*(9*n+8) := by
  apply sumC_operations
  intro k hk
  rw [taylorTermC_operations]
  omega

def rootOperations (B : ℕ) : ℕ :=
  2*(B+10)*(3*(B+10)+11)+32+(B+68)*(9*(B+68)+8)

theorem rootC_result (N j B : ℕ) : (rootC N j B).result = rootRaw N j B := by
  simp [rootC, taylorC_result, angleC_result, rootRaw]
theorem rootC_operations (N j B : ℕ) :
    (rootC N j B).operations ≤ rootOperations B := by
  exact Nat.add_le_add (angleC_operations N j B) (taylorC_operations _ (B+68))

/-- Exact value, positive denominator, bit budget, and arithmetic-operation
budget all refer to this same computable unreduced evaluator. -/
theorem rootC_certificate {N j B L : ℕ} (hN : 0 < N) (hNL : N ≤ 2^L) (hj : j < N) :
    value (rootC N j B).result = RootsApproximation.rootApprox N j B ∧
    Valid (rootC N j B).result ∧ Fits (rootC N j B).result (rootBits B L) ∧
    (rootC N j B).operations ≤ rootOperations B := by
  rw [rootC_result]
  exact ⟨value_rootRaw hN j B, valid_rootRaw hN j B, fits_rootRaw hNL hj,
    rootC_operations N j B⟩

/-- Generic product and sum prefixes obey the same budgets as their final
values, so the bounds include retained intermediate results. -/
theorem fits_pow_prefix {x : Raw} {M k n : ℕ} (hx : Fits x M) (hk : k ≤ n) :
    Fits (pow x k) (n*(M+1)) :=
  fits_mono (fits_pow hx k) (Nat.mul_le_mul_right _ hk)

theorem fits_sum_prefix {f : ℕ → Raw} {M k n : ℕ}
    (h : ∀ i < n, Fits (f i) M) (hk : k ≤ n) :
    Fits (sum f k) (n*(M+1)) :=
  fits_mono (fits_sum (fun i hi => h i (hi.trans_le hk))) (Nat.mul_le_mul_right _ hk)

theorem fits_atan_prefix {a n k : ℕ} (ha : a ≤ 256) (hk : k ≤ n) :
    Fits (atanSum a k) (atanBits n) := by
  apply fits_sum_prefix (n := n) (M := 18*n+9) _ hk
  intro i hi
  exact fits_mono (fits_atanTerm ha i) (by omega)

theorem fits_taylor_prefix {x : Raw} {M k n : ℕ} (hx : Fits x M) (hk : k ≤ n) :
    Fits (taylor x k) (n*(n*(M+1)+n*n+1)) := by
  apply fits_sum_prefix (n := n) (M := n*(M+1)+n*n) _ hk
  intro i hi
  exact fits_mono (fits_taylorTerm hx i)
    (Nat.add_le_add (Nat.mul_le_mul_right _ hi.le) (Nat.mul_le_mul hi.le hi.le))

theorem angleBits_polynomial (B L : ℕ) : angleBits B L ≤ 69*(B+L+78)^2 := by
  let H := B+L+78
  have hA : B+10 ≤ H := by omega
  have hL : L ≤ H := by omega
  have hH : 1 ≤ H := by omega
  have hπ : piBits B ≤ 65*H^2 := by
    unfold piBits atanBits
    calc
      2*((B+10)*(18*(B+10)+10))+9 ≤ 2*(H*(18*H+10))+9 := by gcongr
      _ ≤ 65*H^2 := by nlinarith
  unfold angleBits
  change piBits B+2*L+2 ≤ 69*H^2
  nlinarith

/-- A convenient uniform fourth-degree envelope for all final integers. -/
theorem rootBits_polynomial (B L : ℕ) : rootBits B L ≤ 128*(B+L+78)^4 := by
  let H := B+L+78
  have hn : B+68 ≤ H := by omega
  have hH : 0 < H := by omega
  have ha : angleBits B L ≤ 69*H^2 := angleBits_polynomial B L
  have hp₁ : H ≤ H^4 := by
    simpa using Nat.pow_le_pow_right hH (show 1 ≤ 4 by decide)
  have hp₂ : H^2 ≤ H^4 := Nat.pow_le_pow_right hH (by decide)
  have hp₃ : H^3 ≤ H^4 := Nat.pow_le_pow_right hH (by decide)
  unfold rootBits
  calc
    _ ≤ H*(H*(69*H^2+1)+H^2+1) := by gcongr
    _ ≤ 128*H^4 := by nlinarith

theorem rootOperations_polynomial (B L : ℕ) :
    rootOperations B ≤ 100*(B+L+78)^2 := by
  let H := B+L+78
  have hA : B+10 ≤ H := by omega
  have hT : B+68 ≤ H := by omega
  have hH : 1 ≤ H := by omega
  unfold rootOperations
  calc
    _ ≤ 2*H*(3*H+11)+32+H*(9*H+8) := by gcongr
    _ ≤ 100*H^2 := by nlinarith

theorem dimension_binary_bound {N : ℕ} (hN : 0 < N) : N ≤ 2^(N.log2+1) := by
  exact (Nat.log2_lt (Nat.ne_of_gt hN) |>.mp (Nat.lt_succ_self _)).le

/-- In terms of the actual dimension, magnitude-bit budgets are polynomial in
B+log₂N and the number of integer arithmetic operations is quadratic in B.
No gcd normalization or constant-time large-integer operation is assumed. -/
theorem rootC_polynomial {N j B : ℕ} (hN : 0 < N) (hj : j < N) :
    Fits (rootC N j B).result (128*(B+N.log2+79)^4) ∧
    (rootC N j B).operations ≤ 100*(B+N.log2+79)^2 := by
  constructor
  · rw [rootC_result]
    apply fits_mono (fits_rootRaw (dimension_binary_bound hN) hj)
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rootBits_polynomial B (N.log2+1)
  · exact (rootC_operations N j B).trans (by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rootOperations_polynomial B (N.log2+1))

/-! Bounds for integer temporaries, including products before cancellation. -/

def arithmeticIntegers (x y : Raw) : List ℤ :=
  [x.re*y.re, x.im*y.im, x.re*y.im, x.im*y.re,
   x.re*(y.den : ℤ), y.re*(x.den : ℤ),
   x.im*(y.den : ℤ), y.im*(x.den : ℤ),
   (x.den*y.den : ℕ),
   (mul x y).re, (mul x y).im, (add x y).re, (add x y).im]
def ArithmeticBound (x y : Raw) (M : ℕ) : Prop :=
  ∀ z ∈ arithmeticIntegers x y, z.natAbs ≤ 2^M

theorem abs_product {a b : ℤ} {M K : ℕ}
    (ha : a.natAbs ≤ 2^M) (hb : b.natAbs ≤ 2^K) :
    (a*b).natAbs ≤ 2^(M+K+1) := by
  rw [Int.natAbs_mul]
  calc
    _ ≤ 2^M*2^K := Nat.mul_le_mul ha hb
    _ = 2^(M+K) := (pow_add ..).symm
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (by omega)

theorem arithmetic_bound {x y : Raw} {M K : ℕ} (hx : Fits x M) (hy : Fits y K) :
    ArithmeticBound x y (M+K+1) := by
  intro z hz
  have hxd : (x.den : ℤ).natAbs ≤ 2^M := by simpa using hx.2.2
  have hyd : (y.den : ℤ).natAbs ≤ 2^K := by simpa using hy.2.2
  have hm := fits_mul hx hy
  have ha := fits_add hx hy
  simp only [arithmeticIntegers, List.mem_cons, List.mem_nil_iff, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact abs_product hx.1 hy.1
  · exact abs_product hx.2.1 hy.2.1
  · exact abs_product hx.1 hy.2.1
  · exact abs_product hx.2.1 hy.1
  · exact abs_product hx.1 hyd
  · simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using abs_product hy.1 hxd
  · exact abs_product hx.2.1 hyd
  · simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using abs_product hy.2.1 hxd
  · simpa [mul, Int.natAbs_mul] using hm.2.2
  · exact hm.1
  · exact hm.2.1
  · exact ha.1
  · exact ha.2.1

theorem arithmetic_mono {x y : Raw} {M K : ℕ}
    (h : ArithmeticBound x y M) (hMK : M ≤ K) : ArithmeticBound x y K :=
  fun z hz => (h z hz).trans (Nat.pow_le_pow_right (by decide) hMK)

theorem atan_step_arithmetic {a n k : ℕ} (ha : a ≤ 256) (hk : k < n) :
    ArithmeticBound (atanSum a k) (atanTerm a k) (atanBits n) := by
  have hs : Fits (atanSum a k) (k*(18*n+10)) := by
    apply fits_sum
    intro i hi
    exact fits_mono (fits_atanTerm ha i) (by omega)
  have ht := fits_mono (fits_atanTerm ha k) (show 9*(2*k+1) ≤ 18*n+9 by omega)
  apply arithmetic_mono (arithmetic_bound hs ht)
  unfold atanBits
  calc
    k*(18*n+10)+(18*n+9)+1 = (k+1)*(18*n+10) := by ring
    _ ≤ n*(18*n+10) := Nat.mul_le_mul_right _ hk

theorem taylor_pow_arithmetic {x : Raw} {M k n : ℕ} (hx : Fits x M) (hk : k < n) :
    ArithmeticBound (pow (imaginary x) k) (imaginary x) (n*(M+1)) := by
  apply arithmetic_mono (arithmetic_bound (fits_pow (fits_imaginary hx) k) (fits_imaginary hx))
  calc
    k*(M+1)+M+1 = (k+1)*(M+1) := by ring
    _ ≤ n*(M+1) := Nat.mul_le_mul_right _ hk

theorem taylor_step_arithmetic {x : Raw} {M k n : ℕ} (hx : Fits x M) (hk : k < n) :
    ArithmeticBound (taylor x k) (taylorTerm x k) (n*(n*(M+1)+n*n+1)) := by
  let F := n*(M+1)+n*n
  have ht : ∀ i < n, Fits (taylorTerm x i) F := by
    intro i hi
    exact fits_mono (fits_taylorTerm hx i)
      (Nat.add_le_add (Nat.mul_le_mul_right _ hi.le) (Nat.mul_le_mul hi.le hi.le))
  have hs : Fits (taylor x k) (k*(F+1)) :=
    fits_sum (fun i hi => ht i (hi.trans hk))
  apply arithmetic_mono (arithmetic_bound hs (ht k hk))
  calc
    k*(F+1)+F+1 = (k+1)*(F+1) := by ring
    _ ≤ n*(F+1) := Nat.mul_le_mul_right _ hk

theorem root_stage_budgets (B L : ℕ) :
    piBits B ≤ angleBits B L ∧ angleBits B L ≤ (B+68)*(angleBits B L+1) ∧
    (B+68)*(angleBits B L+1)+(B+68)^2 ≤ rootBits B L := by
  refine ⟨by unfold angleBits; omega, ?_, ?_⟩
  · exact (Nat.le_succ _).trans (Nat.le_mul_of_pos_left _ (by omega))
  · unfold rootBits
    exact (Nat.le_succ _).trans (Nat.le_mul_of_pos_left _ (by omega))

/-- Every binary raw-arithmetic stage in the Machin/Taylor evaluator is
covered here, including every cross-product before addition/subtraction. -/
theorem root_binary_arithmetic {N j B L : ℕ} (hNL : N ≤ 2^L) (hj : j < N) :
    (∀ a ≤ 256, ∀ k < B+10,
      ArithmeticBound (atanSum a k) (atanTerm a k) (rootBits B L)) ∧
    ArithmeticBound (ofInt 16) (atanSum 5 (B+10)) (rootBits B L) ∧
    ArithmeticBound (ofInt 4) (atanSum 239 (B+10)) (rootBits B L) ∧
    ArithmeticBound (mul (ofInt 16) (atanSum 5 (B+10)))
      (neg (mul (ofInt 4) (atanSum 239 (B+10)))) (rootBits B L) ∧
    ArithmeticBound (ofInt (2*j)) (piRaw B) (rootBits B L) ∧
    (∀ k < B+68, ArithmeticBound (pow (imaginary (angleRaw N j B)) k)
      (imaginary (angleRaw N j B)) (rootBits B L)) ∧
    (∀ k < B+68, ArithmeticBound (taylor (angleRaw N j B) k)
      (taylorTerm (angleRaw N j B) k) (rootBits B L)) := by
  have hb := root_stage_budgets B L
  have hA : angleBits B L ≤ rootBits B L := hb.2.1.trans (by omega)
  have hP : piBits B ≤ rootBits B L := hb.1.trans hA
  have hS : atanBits (B+10) ≤ piBits B := by unfold piBits; omega
  have h₁₆ := fits_ofInt (z := 16) (M := 4) (by norm_num)
  have h₄ := fits_ofInt (z := 4) (M := 2) (by norm_num)
  have h₅ := fits_atanSum (a := 5) (by decide) (B+10)
  have h₂₃₉ := fits_atanSum (a := 239) (by decide) (B+10)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha k hk
    exact arithmetic_mono (atan_step_arithmetic ha hk) (hS.trans hP)
  · apply arithmetic_mono (arithmetic_bound h₁₆ h₅)
    exact (show 4+atanBits (B+10)+1 ≤ piBits B by unfold piBits; omega).trans hP
  · apply arithmetic_mono (arithmetic_bound h₄ h₂₃₉)
    exact (show 2+atanBits (B+10)+1 ≤ piBits B by unfold piBits; omega).trans hP
  · apply arithmetic_mono (arithmetic_bound (fits_mul h₁₆ h₅) (fits_neg (fits_mul h₄ h₂₃₉)))
    exact (show 4+atanBits (B+10)+1+(2+atanBits (B+10)+1)+1 ≤ piBits B by unfold piBits; omega).trans hP
  · have hj' : (2*(j : ℤ)).natAbs ≤ 2^(L+1) := by
      simp only [Int.natAbs_mul, Int.natAbs_natCast]
      calc
        2*j ≤ 2*2^L := Nat.mul_le_mul_left _ (hj.le.trans hNL)
        _ = _ := by rw [pow_succ]; ring
    apply arithmetic_mono (arithmetic_bound (fits_ofInt hj') (fits_piRaw B))
    exact (show L+1+piBits B+1 ≤ angleBits B L by unfold angleBits; omega).trans hA
  · intro k hk
    exact arithmetic_mono (taylor_pow_arithmetic (fits_angleRaw hNL hj) hk) (by omega)
  · intro k hk
    simpa [rootBits, pow_two] using taylor_step_arithmetic (fits_angleRaw hNL hj) hk

/-- Integer power and factorial prefixes used to form the term denominators
also obey the same budget; this covers multiplication results before a term
is inserted into the rational sum. -/
theorem root_integer_prefixes (B L : ℕ) :
    (∀ a ≤ 256, ∀ k < B+10, ∀ r ≤ 2*k+1, a^r ≤ 2^(rootBits B L)) ∧
    (∀ k ≤ B+68, k.factorial ≤ 2^(rootBits B L)) ∧
    (∀ k : ℕ, ((-1 : ℤ)^k).natAbs ≤ 2^(rootBits B L)) := by
  have hb := root_stage_budgets B L
  have hA : angleBits B L ≤ rootBits B L := hb.2.1.trans (by omega)
  have hP : piBits B ≤ rootBits B L := hb.1.trans hA
  refine ⟨?_, ?_, ?_⟩
  · intro a ha k hk r hr
    calc
      a^r ≤ (2^8)^r := Nat.pow_le_pow_left ha _
      _ = 2^(8*r) := (pow_mul ..).symm
      _ ≤ 2^(rootBits B L) := Nat.pow_le_pow_right (by decide) (by
        have hs : 8*r ≤ atanBits (B+10) := by unfold atanBits; nlinarith
        exact hs.trans ((show atanBits (B+10) ≤ piBits B by unfold piBits; omega).trans hP))
  · intro k hk
    exact (factorial_bound k).trans (Nat.pow_le_pow_right (by decide)
      ((Nat.mul_le_mul hk hk).trans (by nlinarith [hb.2.2])))
  · intro k
    simp only [Int.natAbs_pow, Int.natAbs_neg, Int.natAbs_one, one_pow]
    exact Nat.one_le_two_pow

/-- Stored results and denominator-only multiplications have no larger hidden
temporaries: the denominator product is itself the resulting stored integer.
This also bounds the small exponents, dimension, and angle index operands. -/
theorem root_stored_intermediates {N j B L : ℕ} (hNL : N ≤ 2^L) (hj : j < N) :
    (∀ a ≤ 256, ∀ k ≤ B+10, Fits (atanSum a k) (rootBits B L)) ∧
    (∀ a ≤ 256, ∀ k < B+10, Fits (atanTerm a k) (rootBits B L)) ∧
    Fits (piRaw B) (rootBits B L) ∧ Fits (angleRaw N j B) (rootBits B L) ∧
    (∀ k ≤ B+68, Fits (pow (imaginary (angleRaw N j B)) k) (rootBits B L)) ∧
    (∀ k < B+68, Fits (taylorTerm (angleRaw N j B) k) (rootBits B L)) ∧
    (∀ k ≤ B+68, Fits (taylor (angleRaw N j B) k) (rootBits B L)) ∧
    (∀ k < B+10, 2*k+1 ≤ 2^(rootBits B L)) ∧
    N ≤ 2^(rootBits B L) ∧ 2*j ≤ 2^(rootBits B L) := by
  have hb := root_stage_budgets B L
  have hPow : (B+68)*(angleBits B L+1) ≤ rootBits B L := by omega
  have hA : angleBits B L ≤ rootBits B L := hb.2.1.trans hPow
  have hP : piBits B ≤ rootBits B L := hb.1.trans hA
  have hS : atanBits (B+10) ≤ rootBits B L :=
    (show atanBits (B+10) ≤ piBits B by unfold piBits; omega).trans hP
  have hAngle := fits_angleRaw (B := B) hNL hj
  refine ⟨?_, ?_, fits_mono (fits_piRaw B) hP, fits_mono hAngle hA, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha k hk
    exact fits_mono (fits_atan_prefix ha hk) hS
  · intro a ha k hk
    apply fits_mono (fits_atanTerm ha k)
    exact (show 9*(2*k+1) ≤ atanBits (B+10) by unfold atanBits; nlinarith).trans hS
  · intro k hk
    exact fits_mono (fits_pow_prefix (fits_imaginary hAngle) hk) hPow
  · intro k hk
    apply fits_mono (fits_taylorTerm hAngle k)
    exact (Nat.add_le_add (Nat.mul_le_mul_right _ hk.le)
      (Nat.mul_le_mul hk.le hk.le)).trans (by simpa [pow_two] using hb.2.2)
  · intro k hk
    simpa [rootBits, pow_two] using fits_taylor_prefix hAngle hk
  · intro k hk
    exact (Nat.lt_two_pow_self (n := 2*k+1)).le.trans
      (Nat.pow_le_pow_right (by decide) (by
        have hs : 2*k+1 ≤ atanBits (B+10) := by unfold atanBits; nlinarith
        exact hs.trans hS))
  · exact hNL.trans (Nat.pow_le_pow_right (by decide) (by unfold angleBits at hA; omega))
  · calc
      2*j ≤ 2*2^L := Nat.mul_le_mul_left _ (hj.le.trans hNL)
      _ = 2^(L+1) := by rw [pow_succ]; ring
      _ ≤ _ := Nat.pow_le_pow_right (by decide) (by unfold angleBits at hA; omega)

theorem root_loop_indices (B L : ℕ) :
    ∀ k ≤ B+68, k ≤ 2^(rootBits B L) := by
  have hb := root_stage_budgets B L
  have hPow : (B+68)*(angleBits B L+1) ≤ rootBits B L := by omega
  have hn : B+68 ≤ rootBits B L :=
    (Nat.le_mul_of_pos_right _ (by omega : 0 < angleBits B L+1)).trans hPow
  intro k hk
  exact (Nat.lt_two_pow_self (n := k)).le.trans
    (Nat.pow_le_pow_right (by decide) (hk.trans hn))

#print axioms fits_add
#print axioms fits_mul
#print axioms fits_pow
#print axioms fits_sum
#print axioms factorial_bound
#print axioms fits_bits
#print axioms value_rootRaw
#print axioms fits_rootRaw
#print axioms rootRaw_bits
#print axioms rootC_result
#print axioms rootC_operations
#print axioms rootC_certificate
#print axioms rootC_polynomial
#print axioms root_binary_arithmetic
#print axioms root_integer_prefixes
#print axioms root_stored_intermediates
#print axioms root_loop_indices

end ThinMatrix.RationalWorkBounds
