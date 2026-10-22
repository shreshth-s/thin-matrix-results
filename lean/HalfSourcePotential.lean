import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

set_option autoImplicit false

/-!
# Uniform potential margin for the exact-half translation list

This is the analytic part of the shrinking-bias construction, for every
positive tensor parameter. It does not assume numerical logarithm boxes.
The list construction, coordinate-character argument, masked embedding and
its execution costs are separate obligations.
-/

namespace ThinMatrix.HalfSourcePotential
noncomputable section
open scoped BigOperators

def step (m : ℕ) : ℝ := 1 / (4 * (m : ℝ))
def base (m : ℕ) : ℝ := 1 + step m
def meanFactor (m : ℕ) : ℝ := (base m + (base m)⁻¹) / 2
def bias (m : ℕ) : ℝ := 1 / (2 * (m : ℝ))
def listLength (m : ℕ) : ℕ := 64 * m^3

theorem log_lower {x : ℝ} (hx : 0 ≤ x) :
    x - x^2/2 ≤ Real.log (1+x) := by
  apply le_trans _ (Real.le_log_one_add_of_nonneg hx)
  apply (le_div_iff₀ (by linarith : 0 < x+2)).mpr
  nlinarith [mul_nonneg hx (sq_nonneg x)]

theorem mean_log_upper {x : ℝ} (hx : 0 ≤ x) :
    Real.log ((1+x+(1+x)⁻¹)/2) ≤ x^2/2 := by
  have hp : 0 < 1+x := by linarith
  have h := Real.log_le_sub_one_of_pos
    (show 0 < (1+x+(1+x)⁻¹)/2 by positivity)
  have he : (1+x+(1+x)⁻¹)/2-1 = x^2/(2*(1+x)) := by
    field_simp
    ring
  rw [he] at h
  apply le_trans h
  apply (div_le_iff₀ (by positivity : 0 < 2*(1+x))).mpr
  nlinarith [mul_nonneg hx (sq_nonneg x)]

theorem one_step_margin {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1/4) :
    (5/4)*x^2 ≤ 2*x*Real.log (1+x) -
      Real.log ((1+x+(1+x)⁻¹)/2) := by
  have hl := mul_le_mul_of_nonneg_left (log_lower hx) (by positivity : 0 ≤ 2*x)
  have hu := mean_log_upper hx
  have hc := mul_nonneg (sq_nonneg x) (sub_nonneg.mpr hx1)
  nlinarith

theorem uniform_log_margin (m : ℕ) (hm : 0 < m) :
    5*(m : ℝ) ≤ (listLength m : ℝ) *
      (bias m * Real.log (base m) - Real.log (meanFactor m)) := by
  have hm0 : 0 < (m : ℝ) := by exact_mod_cast hm
  have hm1 : 1 ≤ (m : ℝ) := by exact_mod_cast hm
  have hx : 0 ≤ step m := by unfold step; positivity
  have hx1 : step m ≤ 1/4 := by
    unfold step
    apply (div_le_iff₀ (by positivity : 0 < 4*(m : ℝ))).mpr
    nlinarith
  have hb : bias m = 2*step m := by
    unfold bias step
    ring
  have he : (listLength m : ℝ) * ((5/4)*step m^2) = 5*(m : ℝ) := by
    simp only [listLength, step, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]
    field_simp
    ring
  have h := mul_le_mul_of_nonneg_left (one_step_margin hx hx1)
    (Nat.cast_nonneg (listLength m) : (0:ℝ) ≤ listLength m)
  rw [he] at h
  simpa only [hb,base,meanFactor] using h

theorem log_character_count_lt (m : ℕ) (hm : 0 < m) :
    Real.log (2*((2:ℝ)^m-1)) < 2*(m:ℝ) := by
  have hm1 : 1 ≤ (m : ℝ) := by exact_mod_cast hm
  have hpow : 1 < (2:ℝ)^m := one_lt_pow₀ (by norm_num) (by omega)
  have hc : 0 < 2*((2:ℝ)^m-1) := by linarith
  have hl := Real.log_lt_log hc (show 2*((2:ℝ)^m-1) < 2*(2:ℝ)^m by linarith)
  rw [Real.log_mul (x := 2) (y := (2:ℝ)^m) (by norm_num)
    (by positivity), Real.log_pow] at hl
  have htwo : Real.log (2:ℝ) < 1 := by
    have h := Real.log_lt_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
      (by norm_num : (2:ℝ) ≠ 1)
    norm_num at h
    exact h
  have h := mul_lt_mul_of_pos_left htwo (show 0 < 1+(m:ℝ) by positivity)
  nlinarith

theorem uniform_initial_gap (m : ℕ) (hm : 0 < m) :
    3*(m : ℝ) < (listLength m : ℝ) *
      (bias m * Real.log (base m) - Real.log (meanFactor m)) -
        Real.log (2*((2:ℝ)^m-1)) := by
  have hmargin := uniform_log_margin m hm
  have hcount := log_character_count_lt m hm
  linarith

/-- Integer weights and the strict mean bound give the exact half cap for
both parities of m. J denotes list indices, including repeated entries. -/
theorem exists_half_of_sum {m J : ℕ} (hJ : 0 < J) (weight : Fin J → ℕ)
    (hmean : (∑ j, (weight j : ℝ)) < (J:ℝ)*((m:ℝ)/2+1/4)) :
    ∃ j, weight j ≤ m/2 := by
  by_contra! h
  have hlow : (J:ℝ)*((m/2+1:ℕ):ℝ) ≤ ∑ j, (weight j:ℝ) := by
    have hs := Finset.sum_le_sum (s := Finset.univ)
      (f := fun _ : Fin J => ((m/2+1:ℕ):ℝ))
      (g := fun j => (weight j:ℝ)) (by
        intro j _
        exact_mod_cast (show m/2+1 ≤ weight j by have := h j; omega))
    simpa [mul_add] using hs
  have hfloor : m ≤ 2*(m/2)+1 := by omega
  have hfloorR : (m:ℝ) ≤ 2*((m/2:ℕ):ℝ)+1 := by exact_mod_cast hfloor
  have hj : 0 < (J:ℝ) := by exact_mod_cast hJ
  have hg : (m:ℝ)/2+1/4 < ((m/2+1:ℕ):ℝ) := by push_cast; linarith
  have := mul_lt_mul_of_pos_left hg hj
  linarith

#print axioms log_lower
#print axioms mean_log_upper
#print axioms one_step_margin
#print axioms uniform_log_margin
#print axioms log_character_count_lt
#print axioms uniform_initial_gap
#print axioms exists_half_of_sum

end
end ThinMatrix.HalfSourcePotential
