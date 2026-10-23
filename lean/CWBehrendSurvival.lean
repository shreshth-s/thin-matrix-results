import CWTypePrimeChoice
import ModularBehrendBuckets

set_option autoImplicit false
namespace ThinMatrix.CWBehrendSurvival
open PolynomialDegeneration CWSixBlocks CWTypeRegularity CWTypeCollisionCount CWMultinomialSurvival CWFilteredHashCounts CWBlockWords CWTypePrimeChoice CWQuantitativeCleanup ModularBehrendBuckets

/-- The bucket set and its density are constructed internally. The surviving
sample is for the repository's actual coordinate filtering and cleanup. This
is a finite existence bound, not a generation or execution-cost theorem. -/
theorem exists_survivors (n : ℕ) (hn : 0<n) (reference : Word n) :
    ∃ r : CWHashFibers.Sample (ZMod (selected n reference)) n,
      (smallestMarginal n reference:ℝ)/72*
        Real.exp (-4*Real.sqrt (Real.log (selected n reference)))≤
        (survivors (selected n reference) n reference (buckets (selected n reference)) r).card := by
  obtain ⟨r,hr⟩ := selected_density_survival n hn reference (buckets (selected n reference))
    (buckets_free _)
  have hq : (smallestMarginal n reference:ℝ)*(buckets (selected n reference)).card/
      (24*selected n reference)≤
      (survivors (selected n reference) n reference (buckets (selected n reference)) r).card := by
    have hcast := (Rat.cast_le (K:=ℝ)).mpr hr
    push_cast at hcast
    exact hcast
  refine ⟨r,?_⟩
  calc
    _ = (smallestMarginal n reference:ℝ)/24*
        ((1/3:ℝ)*Real.exp (-4*Real.sqrt (Real.log (selected n reference)))) := by ring
    _ ≤ (smallestMarginal n reference:ℝ)/24*
        ((buckets (selected n reference)).card/(selected n reference:ℝ)) :=
      mul_le_mul_of_nonneg_left (buckets_density _ (selected_gt_two n reference)) (by positivity)
    _ = (smallestMarginal n reference:ℝ)*(buckets (selected n reference)).card/
        (24*selected n reference) := by ring
    _ ≤ _ := hq

theorem selected_le_power (n : ℕ) (reference : Word n) : selected n reference≤12*6^n := by
  have hd (k : Block → Fin 3) : degree n reference k≤(fullClass n reference).card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  have hD : totalDegree n reference≤3*(fullClass n reference).card := by
    have hx := hd cx;have hy := hd cy;have hz := hd cz
    unfold totalDegree
    omega
  have hM : selected n reference≤4*totalDegree n reference := by
    simpa only [degreeSum_eq] using (selected_spec n reference).2.2
  have hE : (fullClass n reference).card≤6^n := by
    calc
      _ ≤ Fintype.card (Word n) := Finset.card_le_univ _
      _ = (Fintype.card Block)^n := powerIndex_card n
      _ = 6^n := rfl
  omega

theorem log_selected_le (n : ℕ) (reference : Word n) :
    Real.log (selected n reference)≤Real.log 12+(n:ℝ)*Real.log 6 := by
  have hm : (0:ℝ)<selected n reference := by
    exact_mod_cast (show 0<selected n reference by have := selected_gt_two n reference;omega)
  have hu : (selected n reference:ℝ)≤12*(6:ℝ)^n := by exact_mod_cast selected_le_power n reference
  calc
    _ ≤ Real.log (12*(6:ℝ)^n) := Real.log_le_log hm hu
    _ = _ := by rw [Real.log_mul (by norm_num) (by positivity),Real.log_pow]

/-- An explicit loss depending on the tensor-power length, with no
bucket-set or density hypothesis. Multinomial entropy estimates remain
necessary to turn the smallest marginal cardinality into an exponential rate. -/
theorem exists_survivors_explicit_loss (n : ℕ) (hn : 0<n) (reference : Word n) :
    ∃ r : CWHashFibers.Sample (ZMod (selected n reference)) n,
      (smallestMarginal n reference:ℝ)/72*
        Real.exp (-4*Real.sqrt (Real.log 12+(n:ℝ)*Real.log 6))≤
        (survivors (selected n reference) n reference (buckets (selected n reference)) r).card := by
  obtain ⟨r,hr⟩ := exists_survivors n hn reference
  refine ⟨r,le_trans ?_ hr⟩
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  have hs := Real.sqrt_le_sqrt (log_selected_le n reference)
  nlinarith

#print axioms exists_survivors
#print axioms selected_le_power
#print axioms log_selected_le
#print axioms exists_survivors_explicit_loss
end ThinMatrix.CWBehrendSurvival
