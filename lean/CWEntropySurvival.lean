import CWTargetMarginals
import CWBehrendSurvival
import ExtractionLoss

set_option autoImplicit false
namespace ThinMatrix.CWEntropySurvival
open Filter
open scoped Topology
open CWCanonicalType CWTargetMarginals CWTypeCardinalities CWTypePrimeChoice CWQuantitativeCleanup

noncomputable def rate : ℝ := min (entropy 0) (min (entropy 1) (entropy 2))

theorem rate_le (axis : Fin 3) : rate ≤ entropy axis := by
  fin_cases axis
  · exact min_le_left _ _
  · exact (min_le_right _ _).trans (min_le_left _ _)
  · exact (min_le_right _ _).trans (min_le_right _ _)

theorem rate_pos : 0<rate := by
  have hp (axis : Fin 3) : 0<entropy axis := by
    apply TernaryEntropy.entropy_pos
    all_goals exact_mod_cast counts_pos axis _
  exact lt_min (hp 0) (lt_min (hp 1) (hp 2))

theorem smallest_lower (s : ℕ) :
    Real.exp ((size s:ℝ)*rate)/(size s+1)^2 ≤ smallestMarginal (size s) (reference s) := by
  have hb (axis : Fin 3) : Real.exp ((size s:ℝ)*rate)/(size s+1)^2 ≤
      marginalCount (size s) (reference s) (color axis) := by
    apply le_trans _ (marginal_bounds s axis).1
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (rate_le axis) (by positivity))
  have hx := hb 0;have hy := hb 1;have hz := hb 2
  rw [smallestMarginal,Nat.cast_min,Nat.cast_min]
  exact le_min hx (le_min hy hz)

theorem finite_survival (s : ℕ) (hs : 0<s) :
    ∃ r : CWHashFibers.Sample (ZMod (selected (size s) (reference s))) (size s),
      Real.exp ((size s:ℝ)*rate-ExtractionLoss.loss (size s)) ≤
        (survivors (selected (size s) (reference s)) (size s) (reference s)
          (ModularBehrendBuckets.buckets (selected (size s) (reference s))) r).card := by
  have hn : 0<size s := by rw [size_eq];exact Nat.mul_pos hs (by norm_num [period])
  obtain ⟨r,hr⟩ := CWBehrendSurvival.exists_survivors_explicit_loss (size s) hn (reference s)
  refine ⟨r,le_trans ?_ hr⟩
  rw [ExtractionLoss.exp_loss _ _ (by positivity)]
  exact mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right (smallest_lower s) (by norm_num)) (by positivity)

theorem size_tendsto : Tendsto (fun s : ℕ => (size s:ℝ)) atTop atTop := by
  have h := (tendsto_natCast_atTop_atTop (R:=ℝ)).atTop_mul_const
    (show (0:ℝ)<period by norm_num [period])
  simpa only [size_eq,Nat.cast_mul] using h

/-- The actual rational target family has the minimum marginal Shannon
entropy as its independent-copy rate, with every positive strict slack. -/
theorem exponential_survival (ε : ℝ) (he : 0<ε) :
    ∀ᶠ s : ℕ in atTop,
      ∃ r : CWHashFibers.Sample (ZMod (selected (size s) (reference s))) (size s),
        Real.exp ((size s:ℝ)*(rate-ε)) ≤
          (survivors (selected (size s) (reference s)) (size s) (reference s)
            (ModularBehrendBuckets.buckets (selected (size s) (reference s))) r).card := by
  have hl := size_tendsto.eventually (ExtractionLoss.eventually_loss_le ε he)
  filter_upwards [hl,eventually_ge_atTop 1] with s hl hs
  obtain ⟨r,hr⟩ := finite_survival s (by omega)
  refine ⟨r,le_trans ?_ hr⟩
  apply Real.exp_le_exp.mpr
  nlinarith

#print axioms rate_le
#print axioms rate_pos
#print axioms smallest_lower
#print axioms finite_survival
#print axioms size_tendsto
#print axioms exponential_survival
end ThinMatrix.CWEntropySurvival
