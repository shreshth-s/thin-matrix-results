import Mathlib

/-!
# Explicit rational approximations for FFT roots

Finite rational formulas are separated from their real/complex error bounds.
No density-based choice of approximants is used.
-/

open scoped BigOperators Topology

namespace ThinMatrix.RootsApproximation

/-- Computable finite Maclaurin sum for arctangent. -/
def atanApprox (x : ℚ) (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range n, (-1) ^ k * x ^ (2 * k + 1) / (2 * k + 1)

noncomputable def atanMagnitude (x : ℝ) (n : ℕ) : ℝ := x ^ (2 * n + 1) / (2 * n + 1)

theorem atanMagnitude_nonneg {x : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    0 ≤ atanMagnitude x n := by unfold atanMagnitude; positivity

theorem atanMagnitude_le_pow {x : ℝ} (hx : 0 ≤ x) (hx₁ : x ≤ 1) (n : ℕ) :
    atanMagnitude x n ≤ x ^ n := by
  calc
    atanMagnitude x n ≤ x ^ (2 * n + 1) := by
      unfold atanMagnitude
      exact div_le_self (by positivity) (by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith)
    _ ≤ x ^ n := pow_le_pow_of_le_one hx hx₁ (by omega)

theorem atanMagnitude_antitone {x : ℝ} (hx : 0 ≤ x) (hx₁ : x ≤ 1) :
    Antitone (atanMagnitude x) := by
  apply antitone_nat_of_succ_le
  intro n
  unfold atanMagnitude
  apply div_le_div₀ (by positivity)
  · exact pow_le_pow_of_le_one hx hx₁ (by omega)
  · positivity
  · have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    push_cast
    linarith

theorem atanApprox_cast (x : ℚ) (n : ℕ) :
    (atanApprox x n : ℝ) = ∑ k ∈ Finset.range n,
      (-1 : ℝ) ^ k * atanMagnitude (x : ℝ) k := by
  simp only [atanApprox, Rat.cast_sum, Rat.cast_div, Rat.cast_mul, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_one, atanMagnitude]
  apply Finset.sum_congr rfl
  intro k hk
  push_cast
  ring

theorem atanApprox_error (x : ℚ) (hx : 0 ≤ (x : ℝ)) (hx₁ : (x : ℝ) < 1) (n : ℕ) :
    |Real.arctan (x : ℝ) - (atanApprox x n : ℝ)| ≤ (x : ℝ) ^ n := by
  have hxnorm : ‖(x : ℝ)‖ < 1 := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg hx] using hx₁
  have hg : Summable (fun k : ℕ => (x : ℝ) ^ k) := summable_geometric_of_norm_lt_one hxnorm
  have hf : Summable (atanMagnitude (x : ℝ)) :=
    Summable.of_nonneg_of_le (atanMagnitude_nonneg hx)
      (atanMagnitude_le_pow hx hx₁.le) hg
  have hs : HasSum (fun k : ℕ => (-1 : ℝ) ^ k * atanMagnitude (x : ℝ) k)
      (Real.arctan (x : ℝ)) := by
    convert Real.hasSum_arctan hxnorm using 1
    funext k
    unfold atanMagnitude
    push_cast
    ring
  rw [atanApprox_cast, ← hs.tsum_eq]
  exact (alternating_series_error_bound _ (atanMagnitude_antitone hx hx₁.le) hf n).trans
    (atanMagnitude_le_pow hx hx₁.le n)

/-- Machin's explicit rational approximation to pi. -/
def piApprox (B : ℕ) : ℚ :=
  16 * atanApprox (1 / 5) (B + 10) - 4 * atanApprox (1 / 239) (B + 10)

theorem piApprox_error_raw (B : ℕ) :
    |(piApprox B : ℝ) - Real.pi| ≤ 20 * (1 / 2 : ℝ) ^ (B + 10) := by
  have h₅ := atanApprox_error (1 / 5) (by norm_num) (by norm_num) (B + 10)
  have h₂₃₉ := atanApprox_error (1 / 239) (by norm_num) (by norm_num) (B + 10)
  norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] at h₅ h₂₃₉
  have hm := Real.four_mul_arctan_inv_5_sub_arctan_inv_239
  have hm' : Real.pi = 16 * Real.arctan (1 / 5) - 4 * Real.arctan (1 / 239) := by
    norm_num [inv_eq_one_div] at hm
    linarith
  have hpow₅ : (1 / 5 : ℝ) ^ (B + 10) ≤ (1 / 2 : ℝ) ^ (B + 10) := by gcongr; norm_num
  have hpow₂₃₉ : (1 / 239 : ℝ) ^ (B + 10) ≤ (1 / 2 : ℝ) ^ (B + 10) := by
    gcongr; norm_num
  rw [piApprox]
  push_cast
  rw [hm']
  calc
    _ = |16 * ((atanApprox (1 / 5) (B + 10) : ℝ) - Real.arctan (1 / 5)) -
        4 * ((atanApprox (1 / 239) (B + 10) : ℝ) - Real.arctan (1 / 239))| := by congr 1; ring
    _ ≤ |16 * ((atanApprox (1 / 5) (B + 10) : ℝ) - Real.arctan (1 / 5))| +
        |4 * ((atanApprox (1 / 239) (B + 10) : ℝ) - Real.arctan (1 / 239))| := abs_sub _ _
    _ ≤ 20 * (1 / 2 : ℝ) ^ (B + 10) := by
      rw [abs_mul, abs_mul, abs_sub_comm (atanApprox _ _ : ℝ),
        abs_sub_comm (atanApprox _ _ : ℝ)]
      norm_num
      nlinarith [h₅.trans hpow₅, h₂₃₉.trans hpow₂₃₉]

#print axioms atanApprox_error
#print axioms piApprox_error_raw

theorem piApprox_error (B : ℕ) :
    |(piApprox B : ℝ) - Real.pi| ≤ (1 / 32 : ℝ) * (1 / 2 : ℝ) ^ B := by
  apply (piApprox_error_raw B).trans
  rw [pow_add]
  norm_num
  nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) B]

theorem piApprox_abs_le (B : ℕ) : |(piApprox B : ℝ)| ≤ 4 := by
  have he := piApprox_error B
  have hp : (1 / 2 : ℝ) ^ B ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hpi := Real.pi_lt_d2
  have hpipos := Real.pi_pos
  rw [abs_sub_le_iff] at he
  rw [abs_le]
  constructor <;> nlinarith

/-- Pair operations over rational numbers, with complex multiplication. -/
def ratMul (a b : ℚ × ℚ) : ℚ × ℚ :=
  (a.1 * b.1 - a.2 * b.2, a.1 * b.2 + a.2 * b.1)

def ratScale (a : ℚ) (z : ℚ × ℚ) : ℚ × ℚ := (a * z.1, a * z.2)

def ratPow (z : ℚ × ℚ) : ℕ → ℚ × ℚ
  | 0 => (1, 0)
  | n + 1 => ratMul (ratPow z n) z

noncomputable def ratComplex : (ℚ × ℚ) →+ ℂ where
  toFun z := (z.1 : ℂ) + (z.2 : ℂ) * Complex.I
  map_zero' := by simp
  map_add' := by intro a b; simp [add_mul]; ring

theorem ratComplex_mul (a b : ℚ × ℚ) :
    ratComplex (ratMul a b) = ratComplex a * ratComplex b := by
  simp only [ratComplex, AddMonoidHom.coe_mk, ZeroHom.coe_mk, ratMul,
    Rat.cast_sub, Rat.cast_add, Rat.cast_mul]
  linear_combination -(a.2 : ℂ) * (b.2 : ℂ) * Complex.I_sq

theorem ratComplex_scale (a : ℚ) (z : ℚ × ℚ) :
    ratComplex (ratScale a z) = (a : ℂ) * ratComplex z := by
  simp only [ratComplex, AddMonoidHom.coe_mk, ZeroHom.coe_mk, ratScale, Rat.cast_mul]
  ring

theorem ratComplex_pow (z : ℚ × ℚ) (n : ℕ) : ratComplex (ratPow z n) = ratComplex z ^ n := by
  induction n with
  | zero => simp [ratPow, ratComplex]
  | succ n ih => rw [ratPow, ratComplex_mul, ih, pow_succ]

/-- Computable rational-complex exponential Taylor polynomial. -/
def expApprox (x : ℚ) (n : ℕ) : ℚ × ℚ :=
  ∑ k ∈ Finset.range n, ratScale (1 / (k.factorial : ℚ)) (ratPow (0, x) k)

theorem expApprox_cast (x : ℚ) (n : ℕ) :
    ratComplex (expApprox x n) =
      ∑ k ∈ Finset.range n, (Complex.I * (x : ℂ)) ^ k / (k.factorial : ℂ) := by
  simp only [expApprox, map_sum, ratComplex_scale, ratComplex_pow]
  apply Finset.sum_congr rfl
  intro k hk
  simp [ratComplex, div_eq_mul_inv, mul_comm]

#print axioms piApprox_error
#print axioms expApprox_cast

theorem factorial_lower (B : ℕ) :
    (16 : ℝ) ^ (B + 53) ≤ ((B + 68).factorial : ℝ) := by
  have h := @Nat.factorial_mul_pow_le_factorial 15 (B + 53)
  have h₁ : (16 : ℕ) ^ (B + 53) ≤ (15 : ℕ).factorial * 16 ^ (B + 53) := by
    simpa using Nat.mul_le_mul_right (16 ^ (B + 53))
      (Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero 15))
  have h₂ : (16 : ℕ) ^ (B + 53) ≤ (B + 68).factorial := by
    exact h₁.trans (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h)
  exact_mod_cast h₂

theorem taylor_tail_algebra (B : ℕ) :
    (8 : ℝ) ^ (B + 68) / 16 ^ (B + 53) * 2 =
      (1 / 128 : ℝ) * (1 / 2 : ℝ) ^ B := by
  rw [pow_add, pow_add, div_pow]
  norm_num
  have h₈ : (8 : ℝ) ^ B = ((1 / 2 : ℝ) * 16) ^ B := by norm_num
  rw [h₈, mul_pow]
  have hi : (1 / 2 : ℝ) ^ B * 2 ^ B = 1 := by rw [← mul_pow]; norm_num
  field_simp
  nlinarith only [hi]

theorem expApprox_error (x : ℚ) (hx : |(x : ℝ)| ≤ 8) (B : ℕ) :
    ‖Complex.exp (Complex.I * (x : ℂ)) - ratComplex (expApprox x (B + 68))‖ ≤
      (1 / 128 : ℝ) * (1 / 2 : ℝ) ^ B := by
  have hn : ‖Complex.I * (x : ℂ)‖ ≤ 8 := by
    simpa only [norm_mul, Complex.norm_I, one_mul, Complex.norm_ratCast,
      Rat.norm_cast_real] using hx
  have hcond : ‖Complex.I * (x : ℂ)‖ / ((B + 68).succ : ℝ) ≤ 1 / 2 := by
    rw [div_le_iff₀ (by positivity)]
    have hB : (0 : ℝ) ≤ B := Nat.cast_nonneg B
    push_cast
    nlinarith
  rw [expApprox_cast]
  calc
    _ ≤ ‖Complex.I * (x : ℂ)‖ ^ (B + 68) / ((B + 68).factorial : ℝ) * 2 :=
      Complex.exp_bound' hcond
    _ ≤ (8 : ℝ) ^ (B + 68) / 16 ^ (B + 53) * 2 := by
      gcongr
      exact factorial_lower B
    _ = _ := taylor_tail_algebra B

#print axioms expApprox_error

/-- Rational angle and rational-complex twiddle, both computable. -/
def rootAngle (N j B : ℕ) : ℚ := 2 * piApprox B * (j : ℚ) / (N : ℚ)

def rootApprox (N j B : ℕ) : ℚ × ℚ := expApprox (rootAngle N j B) (B + 68)

theorem rootAngle_cast (N j B : ℕ) :
    (rootAngle N j B : ℝ) = 2 * (piApprox B : ℝ) * (j : ℝ) / (N : ℝ) := by
  simp [rootAngle]

theorem angle_ratio (N j : ℕ) (hN : 0 < N) (hj : j < N) :
    0 ≤ (j : ℝ) / (N : ℝ) ∧ (j : ℝ) / (N : ℝ) ≤ 1 := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  constructor
  · positivity
  · rw [div_le_one hNr]
    exact_mod_cast hj.le

theorem rootAngle_abs_le (N j B : ℕ) (hN : 0 < N) (hj : j < N) :
    |(rootAngle N j B : ℝ)| ≤ 8 := by
  rw [rootAngle_cast]
  have hr := angle_ratio N j hN hj
  have he := piApprox_abs_le B
  have heq : 2 * (piApprox B : ℝ) * (j : ℝ) / (N : ℝ) =
      2 * (piApprox B : ℝ) * ((j : ℝ) / (N : ℝ)) := by ring
  rw [heq, abs_mul, abs_mul, abs_of_nonneg hr.1]
  norm_num
  nlinarith [abs_nonneg (piApprox B : ℝ)]

theorem rootAngle_error (N j B : ℕ) (hN : 0 < N) (hj : j < N) :
    |(rootAngle N j B : ℝ) - 2 * Real.pi * (j : ℝ) / (N : ℝ)| ≤
      (1 / 16 : ℝ) * (1 / 2 : ℝ) ^ B := by
  rw [rootAngle_cast]
  have hr := angle_ratio N j hN hj
  have he := piApprox_error B
  have heq : 2 * (piApprox B : ℝ) * (j : ℝ) / (N : ℝ) -
      2 * Real.pi * (j : ℝ) / (N : ℝ) =
      2 * ((piApprox B : ℝ) - Real.pi) * ((j : ℝ) / (N : ℝ)) := by ring
  rw [heq, abs_mul, abs_mul, abs_of_nonneg hr.1]
  norm_num
  have hp : 0 ≤ (1 / 2 : ℝ) ^ B := by positivity
  nlinarith [abs_nonneg ((piApprox B : ℝ) - Real.pi)]

theorem phase_lipschitz (a b : ℝ) :
    ‖Complex.exp (Complex.I * (a : ℂ)) - Complex.exp (Complex.I * (b : ℂ))‖ ≤ |a - b| := by
  have he : Complex.exp (Complex.I * (b : ℂ)) *
      Complex.exp (Complex.I * ((a - b : ℝ) : ℂ)) = Complex.exp (Complex.I * (a : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have heq : Complex.exp (Complex.I * (a : ℂ)) - Complex.exp (Complex.I * (b : ℂ)) =
      Complex.exp (Complex.I * (b : ℂ)) *
        (Complex.exp (Complex.I * ((a - b : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, mul_one, he]
  rw [heq, norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul]
  simpa only [Real.norm_eq_abs] using
    (Real.norm_exp_I_mul_ofReal_sub_one_le (x := a - b))

/-- Fully explicit rational root approximation with dyadic absolute error. -/
theorem rootApprox_error (N j B : ℕ) (hN : 0 < N) (hj : j < N) :
    ‖ratComplex (rootApprox N j B) -
      Complex.exp (Complex.I * ((2 * Real.pi * (j : ℝ) / (N : ℝ) : ℝ) : ℂ))‖ ≤
      (1 / 2 : ℝ) ^ B := by
  have ht := expApprox_error (rootAngle N j B) (rootAngle_abs_le N j B hN hj) B
  have ha := rootAngle_error N j B hN hj
  have hl := phase_lipschitz (rootAngle N j B : ℝ) (2 * Real.pi * (j : ℝ) / (N : ℝ))
  have hc : ((rootAngle N j B : ℝ) : ℂ) = (rootAngle N j B : ℂ) := by simp
  rw [hc] at hl
  rw [norm_sub_rev] at ht
  change ‖ratComplex (expApprox (rootAngle N j B) (B + 68)) - _‖ ≤ _
  exact (norm_sub_le_norm_sub_add_norm_sub _
    (Complex.exp (Complex.I * (rootAngle N j B : ℂ))) _).trans
    (by nlinarith [hl.trans ha, pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) B])

#print axioms rootApprox_error

theorem dyadic_error_eq (B : ℕ) : (1 / 2 : ℝ) ^ B = 1 / (2 : ℝ) ^ B := by
  rw [div_pow, one_pow]

theorem stdAddChar_phase (N : ℕ) [NeZero N] (j : ℕ) :
    ZMod.stdAddChar (j : ZMod N) =
      Complex.exp (Complex.I * ((2 * Real.pi * (j : ℝ) / (N : ℝ) : ℝ) : ℂ)) := by
  have h := ZMod.stdAddChar_coe (N := N) (j : ℤ)
  push_cast at h
  rw [h]
  congr 1
  push_cast
  ring

/-- Direct error interface to Mathlib's standard DFT character. -/
theorem rootApprox_stdAddChar_error (N j B : ℕ) [NeZero N] (hj : j < N) :
    ‖ratComplex (rootApprox N j B) - ZMod.stdAddChar (j : ZMod N)‖ ≤
      1 / (2 : ℝ) ^ B := by
  rw [stdAddChar_phase]
  simpa only [dyadic_error_eq] using rootApprox_error N j B
    (Nat.pos_of_ne_zero (NeZero.ne N)) hj

#print axioms rootApprox_stdAddChar_error

end ThinMatrix.RootsApproximation
