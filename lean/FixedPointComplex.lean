import Mathlib

/-!
Fixed-point complex cells have two integer coordinates and a common binary
scale. Addition, subtraction, multiplication and integer recovery below use
integer operations. Quantization of an arbitrary mathematical complex number
is a specification; no algorithm for computing roots of unity is asserted.
The error and magnitude lemmas do not assume a constant-cost complex primitive.
-/

namespace ThinMatrix.FixedPointComplex

structure Cell where
  re : ℤ
  im : ℤ
  deriving DecidableEq

@[ext] theorem Cell.ext {x y : Cell} (hr : x.re = y.re) (hi : x.im = y.im) : x = y := by
  cases x
  cases y
  simp_all

def scaleZ (B : ℕ) : ℤ := 2 ^ B
def scale (B : ℕ) : ℝ := 2 ^ B
noncomputable def eps (B : ℕ) : ℝ := 2 / scale B

theorem scaleZ_pos (B : ℕ) : 0 < scaleZ B := by unfold scaleZ; positivity
theorem scale_pos (B : ℕ) : 0 < scale B := by unfold scale; positivity
theorem scaleZ_one_le (B : ℕ) : 1 ≤ scaleZ B := by have := scaleZ_pos B; omega
@[simp] theorem scaleZ_cast (B : ℕ) : (scaleZ B : ℝ) = scale B := by simp [scaleZ, scale]
theorem eps_pos (B : ℕ) : 0 < eps B := by unfold eps; exact div_pos (by norm_num) (scale_pos B)

noncomputable def decode (B : ℕ) (c : Cell) : ℂ :=
  ⟨(c.re : ℝ) / scale B, (c.im : ℝ) / scale B⟩

noncomputable def quantize (B : ℕ) (z : ℂ) : Cell :=
  ⟨⌊z.re * scale B⌋, ⌊z.im * scale B⌋⟩

def add (x y : Cell) : Cell := ⟨x.re + y.re, x.im + y.im⟩
def sub (x y : Cell) : Cell := ⟨x.re - y.re, x.im - y.im⟩
def mulRe (x y : Cell) : ℤ := x.re * y.re - x.im * y.im
def mulIm (x y : Cell) : ℤ := x.re * y.im + x.im * y.re
def mul (B : ℕ) (x y : Cell) : Cell :=
  ⟨mulRe x y / scaleZ B, mulIm x y / scaleZ B⟩

theorem decode_add (B : ℕ) (x y : Cell) :
    decode B (add x y) = decode B x + decode B y := by
  apply Complex.ext <;> simp [decode, add, add_div]

theorem decode_sub (B : ℕ) (x y : Cell) :
    decode B (sub x y) = decode B x - decode B y := by
  apply Complex.ext <;> simp [decode, sub, sub_div]

theorem floor_error (x : ℝ) : |(⌊x⌋ : ℤ) - x| ≤ 1 := by
  have hl := Int.floor_le x
  have hu := Int.lt_floor_add_one x
  apply abs_le.mpr
  constructor <;> linarith

theorem quantize_coordinate_error (B : ℕ) (x : ℝ) :
    |((⌊x * scale B⌋ : ℤ) : ℝ) / scale B - x| ≤ 1 / scale B := by
  have hs := scale_pos B
  have he := floor_error (x * scale B)
  rw [show ((⌊x * scale B⌋ : ℤ) : ℝ) / scale B - x =
      (((⌊x * scale B⌋ : ℤ) : ℝ) - x * scale B) / scale B by
    field_simp, abs_div, abs_of_pos hs]
  exact div_le_div_of_nonneg_right he hs.le

theorem quantize_error (B : ℕ) (z : ℂ) : ‖decode B (quantize B z) - z‖ ≤ eps B := by
  have hr := quantize_coordinate_error B z.re
  have hi := quantize_coordinate_error B z.im
  calc
    ‖decode B (quantize B z) - z‖ ≤
        |(decode B (quantize B z) - z).re| +
        |(decode B (quantize B z) - z).im| := Complex.norm_le_abs_re_add_abs_im _
    _ ≤ 1 / scale B + 1 / scale B := by
      exact add_le_add (by simpa [decode, quantize] using hr)
        (by simpa [decode, quantize] using hi)
    _ = eps B := by unfold eps; ring

theorem quantize_decode (B : ℕ) (c : Cell) : quantize B (decode B c) = c := by
  have hs := ne_of_gt (scale_pos B)
  apply Cell.ext <;> simp [quantize, decode, hs]

theorem floor_int_div (u s : ℤ) (hs : 0 < s) :
    ⌊(u : ℝ) / (s : ℝ)⌋ = u / s := by
  simpa only [Int.floor_intCast] using
    (Int.floor_div_cast_of_nonneg (k := ℝ) hs.le (u : ℝ))

theorem mul_eq_quantize (B : ℕ) (x y : Cell) :
    mul B x y = quantize B (decode B x * decode B y) := by
  have hr : (decode B x * decode B y).re * scale B =
      (mulRe x y : ℝ) / (scaleZ B : ℝ) := by
    simp [decode, mulRe]
    field_simp
  have hi : (decode B x * decode B y).im * scale B =
      (mulIm x y : ℝ) / (scaleZ B : ℝ) := by
    simp [decode, mulIm]
    field_simp
  apply Cell.ext
  · change mulRe x y / scaleZ B = ⌊(decode B x * decode B y).re * scale B⌋
    rw [hr, floor_int_div _ _ (scaleZ_pos B)]
  · change mulIm x y / scaleZ B = ⌊(decode B x * decode B y).im * scale B⌋
    rw [hi, floor_int_div _ _ (scaleZ_pos B)]

theorem mul_rounding_error (B : ℕ) (x y : Cell) :
    ‖decode B (mul B x y) - decode B x * decode B y‖ ≤ eps B := by
  rw [mul_eq_quantize]
  exact quantize_error _ _

theorem add_error (B : ℕ) (x y : Cell) (a b : ℂ) (ex ey : ℝ)
    (hx : ‖decode B x - a‖ ≤ ex) (hy : ‖decode B y - b‖ ≤ ey) :
    ‖decode B (add x y) - (a + b)‖ ≤ ex + ey := by
  rw [decode_add, show decode B x + decode B y - (a + b) =
    (decode B x - a) + (decode B y - b) by ring]
  exact (norm_add_le _ _).trans (add_le_add hx hy)

theorem sub_error (B : ℕ) (x y : Cell) (a b : ℂ) (ex ey : ℝ)
    (hx : ‖decode B x - a‖ ≤ ex) (hy : ‖decode B y - b‖ ≤ ey) :
    ‖decode B (sub x y) - (a - b)‖ ≤ ex + ey := by
  rw [decode_sub, show decode B x - decode B y - (a - b) =
    (decode B x - a) - (decode B y - b) by ring]
  exact (norm_sub_le _ _).trans (add_le_add hx hy)

theorem mul_error (B : ℕ) (x y : Cell) (a b : ℂ) (ex ey : ℝ)
    (hx : ‖decode B x - a‖ ≤ ex) (hy : ‖decode B y - b‖ ≤ ey) :
    ‖decode B (mul B x y) - a * b‖ ≤
      eps B + ex * ‖decode B y‖ + ‖a‖ * ey := by
  have hprod : ‖decode B x * decode B y - a * b‖ ≤
      ex * ‖decode B y‖ + ‖a‖ * ey := by
    rw [show decode B x * decode B y - a * b =
      (decode B x - a) * decode B y + a * (decode B y - b) by ring]
    calc
      _ ≤ ‖(decode B x - a) * decode B y‖ + ‖a * (decode B y - b)‖ := norm_add_le _ _
      _ = ‖decode B x - a‖ * ‖decode B y‖ + ‖a‖ * ‖decode B y - b‖ := by
        rw [norm_mul, norm_mul]
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_right hx (norm_nonneg _))
        (mul_le_mul_of_nonneg_left hy (norm_nonneg _))
  have htri : ‖decode B (mul B x y) - a * b‖ ≤
      ‖decode B (mul B x y) - decode B x * decode B y‖ +
      ‖decode B x * decode B y - a * b‖ := by
    calc
      _ = ‖(decode B (mul B x y) - decode B x * decode B y) +
          (decode B x * decode B y - a * b)‖ := by congr 1; ring
      _ ≤ _ := norm_add_le _ _
  have hr := mul_rounding_error B x y
  linarith

theorem butterfly_add_error (B : ℕ) (u v w : Cell) (a b omega : ℂ)
    (eu ev ew : ℝ) (hu : ‖decode B u - a‖ ≤ eu)
    (hv : ‖decode B v - b‖ ≤ ev) (hw : ‖decode B w - omega‖ ≤ ew) :
    ‖decode B (add u (mul B w v)) - (a + omega * b)‖ ≤
      eu + eps B + ew * ‖decode B v‖ + ‖omega‖ * ev := by
  have hm := mul_error B w v omega b ew ev hw hv
  have ha := add_error B u (mul B w v) a (omega * b) eu
    (eps B + ew * ‖decode B v‖ + ‖omega‖ * ev) hu hm
  linarith

theorem butterfly_sub_error (B : ℕ) (u v w : Cell) (a b omega : ℂ)
    (eu ev ew : ℝ) (hu : ‖decode B u - a‖ ≤ eu)
    (hv : ‖decode B v - b‖ ≤ ev) (hw : ‖decode B w - omega‖ ≤ ew) :
    ‖decode B (sub u (mul B w v)) - (a - omega * b)‖ ≤
      eu + eps B + ew * ‖decode B v‖ + ‖omega‖ * ev := by
  have hm := mul_error B w v omega b ew ev hw hv
  have ha := sub_error B u (mul B w v) a (omega * b) eu
    (eps B + ew * ‖decode B v‖ + ‖omega‖ * ev) hu hm
  linarith

/-- The common FFT-stage bound allows twiddle error up to `tau * eps B`. -/
theorem butterfly_stage (B : ℕ) (u v w : Cell) (a b omega : ℂ)
    (E M tau : ℝ) (htau : 0 ≤ tau)
    (hu : ‖decode B u - a‖ ≤ E) (hv : ‖decode B v - b‖ ≤ E)
    (hw : ‖decode B w - omega‖ ≤ tau * eps B)
    (hunit : ‖omega‖ ≤ 1) (hsize : ‖decode B v‖ ≤ M) :
    ‖decode B (add u (mul B w v)) - (a + omega * b)‖ ≤
        2 * E + (tau * M + 1) * eps B ∧
    ‖decode B (sub u (mul B w v)) - (a - omega * b)‖ ≤
        2 * E + (tau * M + 1) * eps B := by
  have hE : 0 ≤ E := (norm_nonneg _).trans hu
  have htw : tau * eps B * ‖decode B v‖ ≤ tau * eps B * M :=
    mul_le_mul_of_nonneg_left hsize (mul_nonneg htau (eps_pos B).le)
  have he : ‖omega‖ * E ≤ E := by simpa using mul_le_mul_of_nonneg_right hunit hE
  have ha := butterfly_add_error B u v w a b omega E E (tau * eps B) hu hv hw
  have hs := butterfly_sub_error B u v w a b omega E E (tau * eps B) hu hv hw
  constructor <;> nlinarith

noncomputable def errorBudget (B : ℕ) (M tau : ℝ) : ℕ → ℝ
  | 0 => eps B
  | k + 1 => 2 * errorBudget B M tau k + (tau * M + 1) * eps B

theorem errorBudget_closed (B k : ℕ) (M tau : ℝ) :
    errorBudget B M tau k =
      (2 : ℝ) ^ k * eps B + ((2 : ℝ) ^ k - 1) * (tau * M + 1) * eps B := by
  induction k with
  | zero => simp [errorBudget]
  | succ k ih => simp only [errorBudget, ih, pow_succ]; ring

theorem errorBudget_bound (B k : ℕ) (M tau : ℝ) (hM : 0 ≤ M) (htau : 0 ≤ tau) :
    errorBudget B M tau k ≤ (2 : ℝ) ^ k * (tau * M + 2) * eps B := by
  rw [errorBudget_closed]
  have h := mul_nonneg (by positivity : 0 ≤ tau * M + 1) (eps_pos B).le
  nlinarith

/-- Concrete integer nearest-recovery, with ties rounded toward positive infinity. -/
def recover (B : ℕ) (c : Cell) : ℤ :=
  (2 * c.re + scaleZ B) / (2 * scaleZ B)

theorem recover_eq_floor (B : ℕ) (c : Cell) :
    recover B c = ⌊(decode B c).re + 1 / 2⌋ := by
  have hden : 0 < 2 * scaleZ B := by have := scaleZ_pos B; omega
  rw [recover, ← floor_int_div _ _ hden]
  congr 1
  simp [decode]
  field_simp [ne_of_gt (scale_pos B)]

theorem nearest_integer (x : ℝ) (z : ℤ) (h : |x - (z : ℝ)| < 1 / 2) :
    ⌊x + 1 / 2⌋ = z := by
  obtain ⟨hl, hu⟩ := abs_lt.mp h
  apply Int.floor_eq_iff.mpr
  constructor <;> linarith

theorem recover_correct (B : ℕ) (c : Cell) (z : ℤ)
    (h : ‖decode B c - (z : ℂ)‖ < 1 / 2) : recover B c = z := by
  rw [recover_eq_floor]
  apply nearest_integer
  have hr := Complex.abs_re_le_norm (decode B c - (z : ℂ))
  exact lt_of_le_of_lt (by simpa using hr) h

theorem recover_of_budget (B k : ℕ) (M tau : ℝ) (c : Cell) (z : ℤ)
    (h : ‖decode B c - (z : ℂ)‖ ≤ errorBudget B M tau k)
    (hsmall : errorBudget B M tau k < 1 / 2) : recover B c = z :=
  recover_correct _ _ _ (h.trans_lt hsmall)

/-- This quantizer is computable because its input coordinates are rational. -/
def ofRat (B : ℕ) (z : ℚ × ℚ) : Cell :=
  ⟨⌊z.1 * (2 : ℚ) ^ B⌋, ⌊z.2 * (2 : ℚ) ^ B⌋⟩

noncomputable def ratComplex (z : ℚ × ℚ) : ℂ := ⟨z.1, z.2⟩

theorem floor_rat_cast (r : ℚ) : ⌊(r : ℝ)⌋ = ⌊r⌋ := by
  apply Int.floor_eq_iff.mpr
  constructor
  · exact_mod_cast Int.floor_le r
  · exact_mod_cast Int.lt_floor_add_one r

theorem ofRat_eq_quantize (B : ℕ) (z : ℚ × ℚ) :
    ofRat B z = quantize B (ratComplex z) := by
  apply Cell.ext
  · change ⌊z.1 * (2 : ℚ) ^ B⌋ = ⌊(z.1 : ℝ) * scale B⌋
    rw [← floor_rat_cast]
    congr 1
    simp [scale]
  · change ⌊z.2 * (2 : ℚ) ^ B⌋ = ⌊(z.2 : ℝ) * scale B⌋
    rw [← floor_rat_cast]
    congr 1
    simp [scale]

theorem ofRat_error (B : ℕ) (z : ℚ × ℚ) (target : ℂ) (e : ℝ)
    (h : ‖ratComplex z - target‖ ≤ e) :
    ‖decode B (ofRat B z) - target‖ ≤ eps B + e := by
  rw [ofRat_eq_quantize]
  have htri : ‖decode B (quantize B (ratComplex z)) - target‖ ≤
      ‖decode B (quantize B (ratComplex z)) - ratComplex z‖ +
      ‖ratComplex z - target‖ := by
    calc
      _ = ‖(decode B (quantize B (ratComplex z)) - ratComplex z) +
        (ratComplex z - target)‖ := by congr 1; ring
      _ ≤ _ := norm_add_le _ _
  exact htri.trans (add_le_add (quantize_error B _) h)

/-- Bounds on each integer cell, including arbitrary signed coordinates. -/
def CellBound (M : ℤ) (c : Cell) : Prop := |c.re| ≤ M ∧ |c.im| ≤ M

theorem floor_integer_bound (x : ℝ) (M : ℤ) (h : |x| ≤ (M : ℝ)) : |⌊x⌋| ≤ M := by
  obtain ⟨hl, hu⟩ := abs_le.mp h
  apply abs_le.mpr
  constructor
  · exact Int.le_floor.mpr (by simpa using hl)
  · calc
      ⌊x⌋ ≤ ⌊(M : ℝ)⌋ := Int.floor_mono hu
      _ = M := Int.floor_intCast M

theorem quantize_cell_bound (B A : ℕ) (z : ℂ) (hz : ‖z‖ ≤ A) :
    CellBound ((A : ℤ) * scaleZ B) (quantize B z) := by
  have hs := (scale_pos B).le
  have hr : |z.re * scale B| ≤ ((A : ℤ) * scaleZ B : ℤ) := by
    rw [abs_mul, abs_of_nonneg hs]
    have h := mul_le_mul_of_nonneg_right ((Complex.abs_re_le_norm z).trans hz) hs
    simpa using h
  have hi : |z.im * scale B| ≤ ((A : ℤ) * scaleZ B : ℤ) := by
    rw [abs_mul, abs_of_nonneg hs]
    have h := mul_le_mul_of_nonneg_right ((Complex.abs_im_le_norm z).trans hz) hs
    simpa using h
  exact ⟨floor_integer_bound _ _ hr, floor_integer_bound _ _ hi⟩

theorem decoded_cell_bound (B A : ℕ) (c : Cell) (hc : ‖decode B c‖ ≤ A) :
    CellBound ((A : ℤ) * scaleZ B) c := by
  have h := quantize_cell_bound B A (decode B c) hc
  simpa only [quantize_decode] using h

theorem add_cell_bound (M : ℤ) (x y : Cell) (hx : CellBound M x) (hy : CellBound M y) :
    CellBound (2 * M) (add x y) := by
  constructor
  · exact (abs_add_le x.re y.re).trans (by have := hx.1; have := hy.1; omega)
  · exact (abs_add_le x.im y.im).trans (by have := hx.2; have := hy.2; omega)

theorem sub_cell_bound (M : ℤ) (x y : Cell) (hx : CellBound M x) (hy : CellBound M y) :
    CellBound (2 * M) (sub x y) := by
  constructor
  · exact (abs_sub x.re y.re).trans (by have := hx.1; have := hy.1; omega)
  · exact (abs_sub x.im y.im).trans (by have := hx.2; have := hy.2; omega)

theorem mul_numerators_bound (M : ℤ) (x y : Cell)
    (hx : CellBound M x) (hy : CellBound M y) :
    |mulRe x y| ≤ 2 * M ^ 2 ∧ |mulIm x y| ≤ 2 * M ^ 2 := by
  have hM : 0 ≤ M := (abs_nonneg x.re).trans hx.1
  have hrr : |x.re * y.re| ≤ M * M := by
    rw [abs_mul]; exact mul_le_mul hx.1 hy.1 (abs_nonneg _) hM
  have hii : |x.im * y.im| ≤ M * M := by
    rw [abs_mul]; exact mul_le_mul hx.2 hy.2 (abs_nonneg _) hM
  have hri : |x.re * y.im| ≤ M * M := by
    rw [abs_mul]; exact mul_le_mul hx.1 hy.2 (abs_nonneg _) hM
  have hir : |x.im * y.re| ≤ M * M := by
    rw [abs_mul]; exact mul_le_mul hx.2 hy.1 (abs_nonneg _) hM
  constructor
  · exact (abs_sub _ _).trans (by nlinarith)
  · exact (abs_add_le _ _).trans (by nlinarith)

theorem mul_cell_bound (B : ℕ) (M : ℤ) (x y : Cell)
    (hx : CellBound M x) (hy : CellBound M y) :
    CellBound (2 * M ^ 2) (mul B x y) := by
  obtain ⟨hr, hi⟩ := mul_numerators_bound M x y hx hy
  exact ⟨(Int.abs_ediv_le_abs _ _).trans hr, (Int.abs_ediv_le_abs _ _).trans hi⟩

/-- Magnitude bits, with one additional bit sufficient for the sign. -/
def FitsMagnitudeBits (bits : ℕ) (u : ℤ) : Prop := u.natAbs < 2 ^ bits
def CellFits (bits : ℕ) (c : Cell) : Prop :=
  FitsMagnitudeBits bits c.re ∧ FitsMagnitudeBits bits c.im
def storedBits (B A : ℕ) : ℕ := B + A.log2 + 1
def productBits (B A : ℕ) : ℕ := 2 * storedBits B A + 1

theorem nat_lt_binary_bound (A : ℕ) : A < 2 ^ (A.log2 + 1) := by
  by_cases h : A = 0
  · simp [h]
  · exact (Nat.log2_lt h).mp (by omega)

theorem abs_bound_fits (u : ℤ) (M bits : ℕ) (hu : |u| ≤ (M : ℤ))
    (hM : M < 2 ^ bits) : FitsMagnitudeBits bits u := by
  have hn : u.natAbs ≤ M := by
    rw [← Int.natCast_natAbs] at hu
    exact_mod_cast hu
  exact hn.trans_lt hM

theorem scaled_magnitude_lt (B A : ℕ) : A * 2 ^ B < 2 ^ storedBits B A := by
  calc
    A * 2 ^ B < 2 ^ (A.log2 + 1) * 2 ^ B :=
      Nat.mul_lt_mul_of_pos_right (nat_lt_binary_bound A) (by positivity)
    _ = 2 ^ storedBits B A := by
      rw [← pow_add]
      congr 1
      unfold storedBits
      omega

theorem cell_bound_fits (B A : ℕ) (c : Cell)
    (h : CellBound ((A : ℤ) * scaleZ B) c) : CellFits (storedBits B A) c := by
  constructor
  · apply abs_bound_fits c.re (A * 2 ^ B) _
    · simpa [scaleZ] using h.1
    · exact scaled_magnitude_lt B A
  · apply abs_bound_fits c.im (A * 2 ^ B) _
    · simpa [scaleZ] using h.2
    · exact scaled_magnitude_lt B A

theorem quantize_bits (B A : ℕ) (z : ℂ) (hz : ‖z‖ ≤ A) :
    CellFits (storedBits B A) (quantize B z) :=
  cell_bound_fits B A _ (quantize_cell_bound B A z hz)

theorem decoded_bits (B A : ℕ) (c : Cell) (hc : ‖decode B c‖ ≤ A) :
    CellFits (storedBits B A) c :=
  cell_bound_fits B A _ (decoded_cell_bound B A c hc)

theorem squared_magnitude_lt (M bits : ℕ) (hM : M < 2 ^ bits) :
    2 * M ^ 2 < 2 ^ (2 * bits + 1) := by
  have hs : M ^ 2 < (2 ^ bits) ^ 2 := by nlinarith [pow_pos (by norm_num : 0 < (2 : ℕ)) bits]
  calc
    2 * M ^ 2 < 2 * (2 ^ bits) ^ 2 := Nat.mul_lt_mul_of_pos_left hs (by norm_num)
    _ = 2 ^ (2 * bits + 1) := by
      rw [← pow_mul]
      calc
        2 * 2 ^ (bits * 2) = 2 ^ (bits * 2) * 2 := by ring
        _ = 2 ^ (bits * 2 + 1) := (pow_succ _ _).symm
        _ = 2 ^ (2 * bits + 1) := by congr 1; omega

theorem mul_working_bits (B A : ℕ) (x y : Cell)
    (hx : CellBound ((A : ℤ) * scaleZ B) x)
    (hy : CellBound ((A : ℤ) * scaleZ B) y) :
    FitsMagnitudeBits (productBits B A) (mulRe x y) ∧
      FitsMagnitudeBits (productBits B A) (mulIm x y) ∧
      CellFits (productBits B A) (mul B x y) := by
  have hm := mul_numerators_bound ((A : ℤ) * scaleZ B) x y hx hy
  have hc := mul_cell_bound B ((A : ℤ) * scaleZ B) x y hx hy
  have hlimit : 2 * (A * 2 ^ B) ^ 2 < 2 ^ productBits B A :=
    squared_magnitude_lt _ _ (scaled_magnitude_lt B A)
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply abs_bound_fits _ (2 * (A * 2 ^ B) ^ 2) _ _ hlimit
    simpa [scaleZ] using hm.1
  · apply abs_bound_fits _ (2 * (A * 2 ^ B) ^ 2) _ _ hlimit
    simpa [scaleZ] using hm.2
  · apply abs_bound_fits _ (2 * (A * 2 ^ B) ^ 2) _ _ hlimit
    simpa [scaleZ] using hc.1
  · apply abs_bound_fits _ (2 * (A * 2 ^ B) ^ 2) _ _ hlimit
    simpa [scaleZ] using hc.2

theorem bitwidth_formulas (B A : ℕ) :
    storedBits B A = B + A.log2 + 1 ∧ productBits B A = 2 * B + 2 * A.log2 + 3 := by
  constructor
  · rfl
  · unfold productBits storedBits
    omega

theorem scale_bits (B : ℕ) : FitsMagnitudeBits (B + 1) (scaleZ B) := by
  have he : (scaleZ B).natAbs = 2 ^ B := by simp [scaleZ, Int.natAbs_pow]
  unfold FitsMagnitudeBits
  rw [he, pow_succ]
  have h : 0 < (2 : ℕ) ^ B := by positivity
  omega

/-- An explicit binary precision sufficient for the proved uniform stage budget. -/
def precision (k M tau : ℕ) : ℕ := k + (4 * (tau * M + 2)).log2 + 1

theorem precision_threshold (k M tau : ℕ) :
    4 * (2 : ℝ) ^ k * ((tau : ℝ) * M + 2) < scale (precision k M tau) := by
  have h := scaled_magnitude_lt k (4 * (tau * M + 2))
  have hn : 4 * (2 : ℕ) ^ k * (tau * M + 2) < 2 ^ precision k M tau := by
    simpa only [storedBits, precision, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using h
  unfold scale
  exact_mod_cast hn

theorem errorBudget_precision (k M tau : ℕ) :
    errorBudget (precision k M tau) M tau k < 1 / 2 := by
  have hb := errorBudget_bound (precision k M tau) k (M : ℝ) (tau : ℝ)
    (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have ht := precision_threshold k M tau
  have hs := scale_pos (precision k M tau)
  have he : (2 : ℝ) ^ k * ((tau : ℝ) * M + 2) * eps (precision k M tau) < 1 / 2 := by
    unfold eps
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ hs).mpr
    nlinarith
  exact hb.trans_lt he

theorem recover_at_precision (k M tau : ℕ) (c : Cell) (z : ℤ)
    (h : ‖decode (precision k M tau) c - (z : ℂ)‖ ≤
      errorBudget (precision k M tau) M tau k) :
    recover (precision k M tau) c = z :=
  recover_of_budget _ _ _ _ _ _ h (errorBudget_precision k M tau)

theorem rational_twiddle_error (B : ℕ) (z : ℚ × ℚ) (omega : ℂ)
    (h : ‖ratComplex z - omega‖ ≤ 1 / scale B) :
    ‖decode B (ofRat B z) - omega‖ ≤ 2 * eps B := by
  have he := ofRat_error B z omega (1 / scale B) h
  have hs := scale_pos B
  have hc : eps B + 1 / scale B ≤ 2 * eps B := by
    unfold eps
    have hpos : 0 ≤ (scale B)⁻¹ := inv_nonneg.mpr hs.le
    simp only [div_eq_mul_inv, one_mul]
    linarith
  exact he.trans hc

end ThinMatrix.FixedPointComplex

#print axioms ThinMatrix.FixedPointComplex.quantize_error
#print axioms ThinMatrix.FixedPointComplex.decode_add
#print axioms ThinMatrix.FixedPointComplex.mul_eq_quantize
#print axioms ThinMatrix.FixedPointComplex.mul_error
#print axioms ThinMatrix.FixedPointComplex.butterfly_stage
#print axioms ThinMatrix.FixedPointComplex.errorBudget_bound
#print axioms ThinMatrix.FixedPointComplex.recover_correct
#print axioms ThinMatrix.FixedPointComplex.ofRat_eq_quantize
#print axioms ThinMatrix.FixedPointComplex.ofRat_error
#print axioms ThinMatrix.FixedPointComplex.quantize_cell_bound
#print axioms ThinMatrix.FixedPointComplex.quantize_bits
#print axioms ThinMatrix.FixedPointComplex.mul_working_bits
#print axioms ThinMatrix.FixedPointComplex.bitwidth_formulas
#print axioms ThinMatrix.FixedPointComplex.errorBudget_precision
#print axioms ThinMatrix.FixedPointComplex.recover_at_precision
#print axioms ThinMatrix.FixedPointComplex.rational_twiddle_error
