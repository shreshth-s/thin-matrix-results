import CWTargetMarginals
import CWEntropySurvival
import RealCertificate

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000

/-! Kernel-checked logarithm bounds for the actual CW target marginals.
The rational finite sums have proved analytic tails; no floating-point
calculation or external numerical certificate is trusted by Lean. -/
namespace ThinMatrix.CWEntropyCertificate
open CWTargetMarginals CWCanonicalType
open scoped BigOperators
noncomputable section

theorem log_0_0 : (-1904858142849/1000000000000:ℝ) < Real.log (11200343770853/75249000000000:ℝ) ∧
    Real.log (11200343770853/75249000000000:ℝ) < (-1904858142847/1000000000000:ℝ) := by
  have h := RealCertificate.atanhLogBounds (1794218770853/20606468770853:ℝ) (by norm_num) (by norm_num) 16
  have hq : (174583398831/1000000000000:ℝ) ≤ Real.log (11200343770853/9406125000000:ℝ) ∧ Real.log (11200343770853/9406125000000:ℝ) ≤ (10911462427/62500000000:ℝ) := by
    norm_num [Finset.sum_range_succ] at h ⊢
    constructor <;> linarith [h.1,h.2]
  have h2 := RealCertificate.logTwo
  have he := Real.log_mul (by positivity : (2:ℝ)^3≠0) (by norm_num : (11200343770853/75249000000000:ℝ)≠0)
  rw [Real.log_pow] at he
  norm_num at he h2 ⊢
  constructor <;> linarith [hq.1,hq.2,h2.1,h2.2]

theorem log_0_1 : (-32383906229/200000000000:ℝ) < Real.log (64000/75249:ℝ) ∧
    Real.log (64000/75249:ℝ) < (-161919531143/1000000000000:ℝ) := by
  have h := RealCertificate.atanhLogBounds (52751/203249:ℝ) (by norm_num) (by norm_num) 16
  have hq : (106245529883/200000000000:ℝ) ≤ Real.log (128000/75249:ℝ) ∧ Real.log (128000/75249:ℝ) ≤ (66403456177/125000000000:ℝ) := by
    norm_num [Finset.sum_range_succ] at h ⊢
    constructor <;> linarith [h.1,h.2]
  have h2 := RealCertificate.logTwo
  have he := Real.log_mul (by positivity : (2:ℝ)^1≠0) (by norm_num : (64000/75249:ℝ)≠0)
  rw [Real.log_pow] at he
  norm_num at he h2 ⊢
  constructor <;> linarith [hq.1,hq.2,h2.1,h2.2]

theorem log_0_2 : (-7343778053031/1000000000000:ℝ) < Real.log (646603/1000000000:ℝ) ∧
    Real.log (646603/1000000000:ℝ) < (-7343778053029/1000000000000:ℝ) := by
  have h := RealCertificate.atanhLogBounds (633287/4539537:ℝ) (by norm_num) (by norm_num) 16
  have hq : (280840933129/1000000000000:ℝ) ≤ Real.log (2586412/1953125:ℝ) ∧ Real.log (2586412/1953125:ℝ) ≤ (28084093313/100000000000:ℝ) := by
    norm_num [Finset.sum_range_succ] at h ⊢
    constructor <;> linarith [h.1,h.2]
  have h2 := RealCertificate.logTwo
  have he := Real.log_mul (by positivity : (2:ℝ)^11≠0) (by norm_num : (646603/1000000000:ℝ)≠0)
  rw [Real.log_pow] at he
  norm_num at he h2 ⊢
  constructor <;> linarith [hq.1,hq.2,h2.1,h2.2]

theorem log_1_0 : (-2890371757897/1000000000000:ℝ) < Real.log (1/18:ℝ) ∧
    Real.log (1/18:ℝ) < (-578074351579/200000000000:ℝ) := by
  have h := RealCertificate.atanhLogBounds (7/25:ℝ) (by norm_num) (by norm_num) 16
  have hq : (575364144903/1000000000000:ℝ) ≤ Real.log (16/9:ℝ) ∧ Real.log (16/9:ℝ) ≤ (71920518113/125000000000:ℝ) := by
    norm_num [Finset.sum_range_succ] at h ⊢
    constructor <;> linarith [h.1,h.2]
  have h2 := RealCertificate.logTwo
  have he := Real.log_mul (by positivity : (2:ℝ)^5≠0) (by norm_num : (1/18:ℝ)≠0)
  rw [Real.log_pow] at he
  norm_num at he h2 ⊢
  constructor <;> linarith [hq.1,hq.2,h2.1,h2.2]

theorem log_1_1 : (-117783035657/1000000000000:ℝ) < Real.log (8/9:ℝ) ∧
    Real.log (8/9:ℝ) < (-23556607131/200000000000:ℝ) := by
  have h := RealCertificate.atanhLogBounds (7/25:ℝ) (by norm_num) (by norm_num) 16
  have hq : (575364144903/1000000000000:ℝ) ≤ Real.log (16/9:ℝ) ∧ Real.log (16/9:ℝ) ≤ (71920518113/125000000000:ℝ) := by
    norm_num [Finset.sum_range_succ] at h ⊢
    constructor <;> linarith [h.1,h.2]
  have h2 := RealCertificate.logTwo
  have he := Real.log_mul (by positivity : (2:ℝ)^1≠0) (by norm_num : (8/9:ℝ)≠0)
  rw [Real.log_pow] at he
  norm_num at he h2 ⊢
  constructor <;> linarith [hq.1,hq.2,h2.1,h2.2]

theorem log_1_2 : (-2890371757897/1000000000000:ℝ) < Real.log (1/18:ℝ) ∧
    Real.log (1/18:ℝ) < (-578074351579/200000000000:ℝ) := by
  have h := RealCertificate.atanhLogBounds (7/25:ℝ) (by norm_num) (by norm_num) 16
  have hq : (575364144903/1000000000000:ℝ) ≤ Real.log (16/9:ℝ) ∧ Real.log (16/9:ℝ) ≤ (71920518113/125000000000:ℝ) := by
    norm_num [Finset.sum_range_succ] at h ⊢
    constructor <;> linarith [h.1,h.2]
  have h2 := RealCertificate.logTwo
  have he := Real.log_mul (by positivity : (2:ℝ)^5≠0) (by norm_num : (1/18:ℝ)≠0)
  rw [Real.log_pow] at he
  norm_num at he h2 ⊢
  constructor <;> linarith [hq.1,hq.2,h2.1,h2.2]

theorem log_2_0 : (-158345360031/1000000000000:ℝ) < Real.log (21409718743049/25083000000000:ℝ) ∧
    Real.log (21409718743049/25083000000000:ℝ) < (-158345360029/1000000000000:ℝ) := by
  have h := RealCertificate.atanhLogBounds (8868218743049/33951218743049:ℝ) (by norm_num) (by norm_num) 16
  have hq : (534801820529/1000000000000:ℝ) ≤ Real.log (21409718743049/12541500000000:ℝ) ∧ Real.log (21409718743049/12541500000000:ℝ) ≤ (53480182053/100000000000:ℝ) := by
    norm_num [Finset.sum_range_succ] at h ⊢
    constructor <;> linarith [h.1,h.2]
  have h2 := RealCertificate.logTwo
  have he := Real.log_mul (by positivity : (2:ℝ)^1≠0) (by norm_num : (21409718743049/25083000000000:ℝ)≠0)
  rw [Real.log_pow] at he
  norm_num at he h2 ⊢
  constructor <;> linarith [hq.1,hq.2,h2.1,h2.2]

theorem log_2_1 : (-483285337289/250000000000:ℝ) < Real.log (10888/75249:ℝ) ∧
    Real.log (10888/75249:ℝ) < (-966570674577/500000000000:ℝ) := by
  have h := RealCertificate.atanhLogBounds (11855/162353:ℝ) (by norm_num) (by norm_num) 16
  have hq : (36575048131/250000000000:ℝ) ≤ Real.log (87104/75249:ℝ) ∧ Real.log (87104/75249:ℝ) ≤ (5852007701/40000000000:ℝ) := by
    norm_num [Finset.sum_range_succ] at h ⊢
    constructor <;> linarith [h.1,h.2]
  have h2 := RealCertificate.logTwo
  have he := Real.log_mul (by positivity : (2:ℝ)^3≠0) (by norm_num : (10888/75249:ℝ)≠0)
  rw [Real.log_pow] at he
  norm_num at he h2 ⊢
  constructor <;> linarith [hq.1,hq.2,h2.1,h2.2]

theorem log_2_2 : (-3173470112999/500000000000:ℝ) < Real.log (131843770853/75249000000000:ℝ) ∧
    Real.log (131843770853/75249000000000:ℝ) < (-1586735056499/250000000000:ℝ) := by
  have h := RealCertificate.atanhLogBounds (116716838581/410658244831:ℝ) (by norm_num) (by norm_num) 16
  have hq : (292265789801/500000000000:ℝ) ≤ Real.log (263687541706/146970703125:ℝ) ∧ Real.log (263687541706/146970703125:ℝ) ≤ (584531579603/1000000000000:ℝ) := by
    norm_num [Finset.sum_range_succ] at h ⊢
    constructor <;> linarith [h.1,h.2]
  have h2 := RealCertificate.logTwo
  have he := Real.log_mul (by positivity : (2:ℝ)^10≠0) (by norm_num : (131843770853/75249000000000:ℝ)≠0)
  rw [Real.log_pow] at he
  norm_num at he h2 ⊢
  constructor <;> linarith [hq.1,hq.2,h2.1,h2.2]

theorem log_eighteen : Real.log (18:ℝ) < (2890371757897/10^12:ℝ) := by
  have h := RealCertificate.atanhLogBounds (1/17:ℝ) (by norm_num) (by norm_num) 16
  have hq : Real.log (9/8:ℝ) ≤ (117783035657/1000000000000:ℝ) := by
    norm_num [Finset.sum_range_succ] at h ⊢
    linarith [h.2]
  have h2 := RealCertificate.logTwo
  have he := Real.log_mul (by norm_num : (2:ℝ)^4≠0) (by norm_num : (9/8:ℝ)≠0)
  rw [Real.log_pow] at he
  norm_num at he h2 ⊢
  linarith [h2.2]

theorem log_sixteen : Real.log (16:ℝ)=4*Real.log 2 := by
  convert Real.log_pow (2:ℝ) 4 using 1 <;> norm_num

/-- The strict arithmetic margin reserves 1e-7 below the stated endpoint. -/
theorem marginal_margin (axis : Fin 3) :
    Real.log 18 < entropy axis+(4000/75249:ℝ)*(167220001/10000000:ℝ)*Real.log 16 := by
  have h2 := RealCertificate.logTwo
  have h18 := log_eighteen
  rw [entropy_shannon,log_sixteen]
  fin_cases axis
  · have h0 := log_0_0; have h1 := log_0_1; have h3 := log_0_2
    norm_num [counts,period,Fin.sum_univ_succ] at h2 ⊢
    linarith [h0.2,h1.2,h3.2,h2.1]
  · have h0 := log_1_0; have h1 := log_1_1; have h3 := log_1_2
    norm_num [counts,period,Fin.sum_univ_succ] at h2 ⊢
    linarith [h0.2,h1.2,h3.2,h2.1]
  · have h0 := log_2_0; have h1 := log_2_1; have h3 := log_2_2
    norm_num [counts,period,Fin.sum_univ_succ] at h2 ⊢
    linarith [h0.2,h1.2,h3.2,h2.1]

theorem rate_margin : Real.log 18 < CWEntropySurvival.rate+
    (4000/75249:ℝ)*(167220001/10000000:ℝ)*Real.log 16 := by
  have h0 := marginal_margin 0; have h1 := marginal_margin 1; have h2 := marginal_margin 2
  unfold CWEntropySurvival.rate
  rcases le_total (entropy 0) (min (entropy 1) (entropy 2)) with h | h
  · rw [min_eq_left h]; exact h0
  · rw [min_eq_right h]
    rcases le_total (entropy 1) (entropy 2) with h | h
    · rw [min_eq_left h]; exact h1
    · rw [min_eq_right h]; exact h2

#print axioms marginal_margin
#print axioms rate_margin
end
end ThinMatrix.CWEntropyCertificate
