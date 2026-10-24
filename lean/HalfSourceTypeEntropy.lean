import HalfSourceCertificate
import EntropyBounds

/-! Global channel-type envelope for the exact-half source encoder. The
endpoint derivative certificate is propagated across the whole admissible
interval using monotonicity of the entropy derivative; unbalanced types are
then dominated by their balanced midpoint. No concavity premise is assumed. -/
namespace ThinMatrix.HalfSourceTypeEntropy
open HalfSourceParameters
open Set Filter
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def probability (r : ℝ) : ℝ := (1/2-r)/(c-1)
def gamma (r : ℝ) : ℝ := Real.binEntropy (probability r)/Real.log 4
def entropyPrime (r : ℝ) : ℝ := Real.log (1-r)-Real.log r
def gammaPrime (r : ℝ) : ℝ := -entropyPrime (probability r)/((c-1)*Real.log 4)
def score (r : ℝ) : ℝ := 2*Real.binEntropy r/Real.log 4-zeta/(2*gamma r)
def scorePrime (r : ℝ) : ℝ := 2*entropyPrime r/Real.log 4+zeta*gammaPrime r/(2*gamma r*gamma r)
def typeScore (x y : ℝ) : ℝ := (Real.binEntropy x+Real.binEntropy y)/Real.log 4-zeta/(2*gamma (max x y))

theorem constants : 0  <  theta ∧ 2*theta  <  1/2 ∧ 0  <  c-1 ∧ 0  <  zeta ∧ 0  <  Real.log 4 := by
  norm_num [theta,c,zeta]
  exact Real.log_pos (by norm_num)

theorem probability_bounds {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 2*theta) :
    0 < probability r ∧ probability r < 1/2 := by
  have hc := constants
  constructor
  · unfold probability; exact div_pos (by linarith [hc.2.1]) hc.2.2.1
  · apply (div_lt_iff₀ hc.2.2.1).mpr
    norm_num [c] at *
    linarith

theorem gamma_positive {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 2*theta) : 0 < gamma r := by
  have hp := probability_bounds hr0 hr1
  exact div_pos (Real.binEntropy_pos hp.1 (by linarith [hp.2])) constants.2.2.2.2

theorem gamma_antitone {r s : ℝ} (hr0 : 0 ≤ r) (hrs : r ≤ s) (hs1 : s ≤ 2*theta) : gamma s ≤ gamma r := by
  have hp := probability_bounds hr0 (hrs.trans hs1)
  have hq := probability_bounds (hr0.trans hrs) hs1
  have harg : probability s ≤ probability r := by
    exact div_le_div_of_nonneg_right (by linarith) constants.2.2.1.le
  exact div_le_div_of_nonneg_right
    (Real.binEntropy_strictMonoOn.monotoneOn ⟨hq.1.le,by simpa only [one_div] using hq.2.le⟩ ⟨hp.1.le,by simpa only [one_div] using hp.2.le⟩ harg)
    constants.2.2.2.2.le

theorem entropyPrime_antitone {r s : ℝ} (hr0 : 0 < r) (hrs : r ≤ s) (hs1 : s < 1) :
    entropyPrime s ≤ entropyPrime r := by
  have h1 := Real.log_le_log (by linarith : 0 < 1-s) (show 1-s ≤ 1-r by linarith)
  have h2 := Real.log_le_log hr0 hrs
  unfold entropyPrime
  linarith

theorem entropyPrime_nonneg {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1/2) : 0 ≤ entropyPrime r := by
  have h := Real.log_le_log hr0 (show r ≤ 1-r by linarith)
  unfold entropyPrime
  linarith

theorem gammaPrime_nonpos {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 2*theta) : gammaPrime r ≤ 0 := by
  have hp := probability_bounds hr0 hr1
  unfold gammaPrime
  exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (entropyPrime_nonneg hp.1 hp.2.le))
    (mul_pos constants.2.2.1 constants.2.2.2.2).le

theorem gammaPrime_antitone {r s : ℝ} (hr0 : 0 ≤ r) (hrs : r ≤ s) (hs1 : s ≤ 2*theta) :
    gammaPrime s ≤ gammaPrime r := by
  have hp := probability_bounds hr0 (hrs.trans hs1)
  have hq := probability_bounds (hr0.trans hrs) hs1
  have harg : probability s ≤ probability r :=
    div_le_div_of_nonneg_right (by linarith) constants.2.2.1.le
  have he := entropyPrime_antitone hq.1 harg (by linarith [hp.2])
  exact div_le_div_of_nonneg_right (neg_le_neg he) (mul_pos constants.2.2.1 constants.2.2.2.2).le

theorem gamma_derivative {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 2*theta) :
    HasDerivAt gamma (gammaPrime r) r := by
  have hp := probability_bounds hr0 hr1
  have ha : HasDerivAt probability (-1/(c-1)) r := by
    exact ((hasDerivAt_id r).const_sub (1/2)).div_const (c-1)
  have hh := ((Real.hasDerivAt_binEntropy hp.1.ne' (by linarith [hp.2])).comp r ha).div_const (Real.log 4)
  have he : gammaPrime r=(Real.log (1-probability r)-Real.log (probability r))*(-1/(c-1))/Real.log 4 := by
    unfold gammaPrime entropyPrime
    field_simp
  rw [he]
  exact hh

theorem score_derivative {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ theta) :
    HasDerivAt score (scorePrime r) r := by
  have htwo : r ≤ 2*theta := by linarith [constants.1]
  have hrOne : r ≠ 1 := by linarith [constants.2.1]
  have hgamma := gamma_positive hr0.le htwo
  have hh := ((Real.hasDerivAt_binEntropy hr0.ne' hrOne).const_mul 2).div_const (Real.log 4)
  have hg := (hasDerivAt_const r zeta).div ((gamma_derivative hr0.le htwo).const_mul 2) (by positivity : 2*gamma r ≠ 0)
  have he : scorePrime r=2*(Real.log (1-r)-Real.log r)/Real.log 4-
      (0*(2*gamma r)-zeta*(2*gammaPrime r))/(2*gamma r)^2 := by
    unfold scorePrime entropyPrime
    field_simp
    ring
  rw [he]
  exact hh.sub hg

/-- The negative reciprocal contribution is most negative at theta. -/
theorem scorePrime_lower {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ theta) : scorePrime theta ≤ scorePrime r := by
  have ht0 := constants.1
  have ht2 : theta ≤ 2*theta := by linarith
  have hr2 : r ≤ 2*theta := hr1.trans ht2
  have hgr := gamma_positive hr0.le hr2
  have hgt := gamma_positive ht0.le ht2
  have hgm := gamma_antitone hr0.le hr1 ht2
  have hpm := gammaPrime_antitone hr0.le hr1 ht2
  have hpn := gammaPrime_nonpos hr0.le hr2
  have hden : 2*gamma theta*gamma theta  ≤  2*gamma r*gamma r := by nlinarith
  have hfrac1 := div_le_div_of_nonneg_right hpm (by positivity : 0 ≤ 2*gamma theta*gamma theta)
  have hfrac2 : gammaPrime r/(2*gamma theta*gamma theta)  ≤  gammaPrime r/(2*gamma r*gamma r) :=
    (div_le_div_iff₀ (by positivity) (by positivity)).mpr (mul_le_mul_of_nonpos_left hden hpn)
  have hf := mul_le_mul_of_nonneg_left (hfrac1.trans hfrac2) constants.2.2.2.1.le
  have he := entropyPrime_antitone hr0 hr1 (by linarith [constants.2.1])
  have hh := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left he (by norm_num : 0 ≤ (2:ℝ))) constants.2.2.2.2.le
  simp only [← mul_div_assoc] at hf
  unfold scorePrime
  linarith only [hf,hh]

theorem gamma_at_theta : gamma theta=gamt := by
  unfold gamma probability gamt
  rw [EntropyBounds.binEntropy_eq]
  rfl

theorem scorePrime_endpoint : scorePrime theta=HalfSourceCertificate.sourceDerivative := by
  have ht0 := constants.1
  have hp := probability_bounds ht0.le (show theta ≤ 2*theta by linarith)
  have he (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) : entropyPrime x=Real.log ((1-x)/x) := by
    rw [Real.log_div (by linarith : 1-x ≠ 0) hx0.ne']
    rfl
  unfold scorePrime gammaPrime
  rw [gamma_at_theta,he theta ht0 (by linarith [constants.2.1]),he (probability theta) hp.1 (by linarith [hp.2])]
  rfl

theorem scorePrime_positive {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ theta) : 0 < scorePrime r := by
  have h := scorePrime_lower hr0 hr1
  rw [scorePrime_endpoint] at h
  exact HalfSourceCertificate.sourceDerivative_positive.trans_le h

theorem gamma_continuous : Continuous gamma := by
  unfold gamma probability
  fun_prop

theorem score_continuousOn : ContinuousOn score (Icc 0 theta) := by
  apply ContinuousOn.sub ((Real.binEntropy_continuous.const_mul 2).div_const (Real.log 4)).continuousOn
  apply continuousOn_const.div (gamma_continuous.const_mul 2).continuousOn
  intro r hr
  exact mul_ne_zero (by norm_num) (gamma_positive hr.1 (by linarith [hr.2,constants.1])).ne'

theorem score_monotone : MonotoneOn score (Icc 0 theta) := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc 0 theta) score_continuousOn
  · intro r hr
    rw [interior_Icc] at hr
    exact (score_derivative hr.1 hr.2.le).differentiableAt.differentiableWithinAt
  · intro r hr
    rw [interior_Icc] at hr
    rw [(score_derivative hr.1 hr.2.le).deriv]
    exact (scorePrime_positive hr.1 hr.2.le).le

theorem entropy_balanced {x y : ℝ} (hx0 : 0 ≤ x) (hy0 : 0 ≤ y)
    (hs : x+y ≤ 2*theta) : Real.binEntropy x+Real.binEntropy y ≤ 2*Real.binEntropy ((x+y)/2) := by
  have ht := constants.2.1
  have h := Real.strictConcave_binEntropy.concaveOn.2
    (show x∈Icc (0:ℝ) 1 from ⟨hx0,by linarith⟩)
    (show y∈Icc (0:ℝ) 1 from ⟨hy0,by linarith⟩)
    (by norm_num : 0 ≤ (1/2:ℝ)) (by norm_num : 0 ≤ (1/2:ℝ)) (by norm_num : (1/2:ℝ)+1/2=1)
  simp only [smul_eq_mul] at h
  rw [show (1/2:ℝ)*x+1/2*y=(x+y)/2 by ring] at h
  linarith

theorem type_balanced {x y : ℝ} (hx0 : 0 ≤ x) (hy0 : 0 ≤ y)
    (hs : x+y ≤ 2*theta) : typeScore x y ≤ score ((x+y)/2) := by
  have hr0 : 0 ≤ (x+y)/2 := by positivity
  have hmax : max x y ≤ 2*theta := max_le (by linarith) (by linarith)
  have hrm : (x+y)/2 ≤ max x y := by have := le_max_left x y; have := le_max_right x y; linarith
  have hgm := gamma_antitone hr0 hrm hmax
  have hgmax := gamma_positive (hx0.trans (le_max_left x y)) hmax
  have hden : 2*gamma (max x y) ≤ 2*gamma ((x+y)/2) := by linarith
  have hf := div_le_div_of_nonneg_left constants.2.2.2.1.le (by positivity : 0 < 2*gamma (max x y)) hden
  have he := div_le_div_of_nonneg_right (entropy_balanced hx0 hy0 hs) constants.2.2.2.2.le
  unfold typeScore score
  linarith only [hf,he]

theorem score_at_theta : score theta=Q-zeta/(2*gamt) := by
  unfold score
  rw [gamma_at_theta]
  congr 1
  unfold Q
  rw [EntropyBounds.binEntropy_eq]
  rfl

/-- This is the complete real channel-type maximum used in (L3), for all
balanced and unbalanced admissible channel fractions simultaneously. -/
theorem type_envelope {x y : ℝ} (hx0 : 0 ≤ x) (hy0 : 0 ≤ y)
    (hs : x+y ≤ 2*theta) : typeScore x y ≤ Q-zeta/(2*gamt) := by
  have hr : (x+y)/2∈Icc (0:ℝ) theta := ⟨by positivity,by linarith⟩
  have h := score_monotone hr ⟨constants.1.le,le_rfl⟩ hr.2
  rw [score_at_theta] at h
  exact (type_balanced hx0 hy0 hs).trans h

#print axioms score_monotone
#print axioms entropy_balanced
#print axioms type_balanced
#print axioms type_envelope

#print axioms probability_bounds
#print axioms gamma_antitone
#print axioms gamma_derivative
#print axioms score_derivative
#print axioms scorePrime_lower
#print axioms scorePrime_positive
end
end ThinMatrix.HalfSourceTypeEntropy
