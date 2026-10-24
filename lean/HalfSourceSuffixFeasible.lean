import HalfSourceSuffixPlan

set_option autoImplicit false
set_option maxHeartbeats 1500000

/-! The actual canonical channel types meet the suffix feasibility guard.
The proof uses a coarse strict analytic margin and handles all rounding in
L, the channel cap and the half-source rare budget. -/
namespace ThinMatrix.HalfSourceSuffixFeasible
open HalfSourceBatchFit HalfSourceSuffixChoice HalfSourceSuffixPlan

 theorem suffix_eight (m : ℕ) : 8*m ≤ OptimizedFoldedPlan.ordinaryLength m-m := by
  have hc : (9:ℝ) ≤ OptimizedFoldedPlan.c := by norm_num [OptimizedFoldedPlan.c]
  have h := (mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg m)).trans
    (OptimizedFoldedPlan.rounded_bounds m).1
  have hn : 9*m ≤ OptimizedFoldedPlan.ordinaryLength m := by exact_mod_cast h
  omega

theorem rare_quarter (m cn co : ℕ) (hm : 32 ≤ m)
    (hchannel : max cn co ≤ OptimizedFoldedPlan.channelLength m) :
    m ≤ 4*(m/2-max cn co) := by
  unfold OptimizedFoldedPlan.channelLength at hchannel
  omega

theorem type_ratio (m cn co : ℕ) (hm : 32 ≤ m)
    (hchannel : max cn co ≤ OptimizedFoldedPlan.channelLength m) :
    0 < ((m/2-max cn co:ℕ):ℝ)/((OptimizedFoldedPlan.ordinaryLength m-m:ℕ):ℝ) ∧
    ((m/2-max cn co:ℕ):ℝ)/((OptimizedFoldedPlan.ordinaryLength m-m:ℕ):ℝ) ≤ 1/16 := by
  have hk := suffix_eight m
  have hr := rare_quarter m cn co hm hchannel
  have hk0 : (0:ℝ) < ((OptimizedFoldedPlan.ordinaryLength m-m:ℕ):ℝ) := by exact_mod_cast (show 0 < OptimizedFoldedPlan.ordinaryLength m-m by omega)
  constructor
  · exact div_pos (by exact_mod_cast (show 0 < m/2-max cn co by omega)) hk0
  · apply (div_le_iff₀ hk0).mpr
    have hnat : 16*(m/2-max cn co) ≤ OptimizedFoldedPlan.ordinaryLength m-m := by omega
    have hreal : 16*((m/2-max cn co:ℕ):ℝ) ≤ ((OptimizedFoldedPlan.ordinaryLength m-m:ℕ):ℝ) := by exact_mod_cast hnat
    linarith

theorem entropy_lower {p : ℝ} (hp : 0 < p) (hp16 : p ≤ 1/16) :
    p*(4*Real.log 2) ≤ Real.binEntropy p := by
  have hinv : (16:ℝ) ≤ p⁻¹ := by
    rw [← one_div]
    exact (le_div_iff₀ hp).mpr (by linarith)
  have hlog := Real.log_le_log (by norm_num : (0:ℝ)<16) hinv
  have h16 : Real.log (16:ℝ)=4*Real.log 2 := by
    have h := Real.log_pow (2:ℝ) 4
    norm_num only [show (2:ℝ)^4=16 by norm_num,Nat.cast_ofNat] at h
    exact h
  rw [h16] at hlog
  have hcomp : 1 ≤ (1-p)⁻¹ := (one_le_inv₀ (by linarith)).mpr (by linarith)
  have hnonneg : 0 ≤ (1-p)*Real.log (1-p)⁻¹ :=
    mul_nonneg (by linarith) (Real.log_nonneg hcomp)
  unfold Real.binEntropy
  nlinarith [mul_le_mul_of_nonneg_left hlog hp.le]

/-- No suffix-feasibility assumption remains for a valid canonical channel
type once m≥32. Small tensor powers can be handled directly. -/
theorem quotient_fits (m cn co : ℕ) (hm : 32 ≤ m)
    (hchannel : max cn co ≤ OptimizedFoldedPlan.channelLength m) :
    let k := OptimizedFoldedPlan.ordinaryLength m-m
    let rare := m/2-max cn co
    0 < Real.binEntropy ((rare:ℝ)/k) ∧
    (m:ℝ)*zeta*Real.log 4 / Real.binEntropy ((rare:ℝ)/k) ≤ (k:ℝ) := by
  let k := OptimizedFoldedPlan.ordinaryLength m-m
  let rare := m/2-max cn co
  have hp := type_ratio m cn co hm hchannel
  have hH : 0 < Real.binEntropy ((rare:ℝ)/k) := Real.binEntropy_pos hp.1 (by linarith [hp.2])
  have hk : 0 < k := by have := suffix_eight m; dsimp [k]; omega
  have hkR : 0 < (k:ℝ) := by exact_mod_cast hk
  have hlow := mul_le_mul_of_nonneg_left (entropy_lower hp.1 hp.2) hkR.le
  have hid : (k:ℝ)*(((rare:ℝ)/k)*(4*Real.log 2))=(rare:ℝ)*(4*Real.log 2) := by field_simp
  rw [hid] at hlow
  have hr : (m:ℝ) ≤ 4*(rare:ℝ) := by exact_mod_cast rare_quarter m cn co hm hchannel
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hrare := mul_le_mul_of_nonneg_right hr hlog.le
  have hguard : (m:ℝ)*zeta*Real.log 4 ≤ (k:ℝ)*Real.binEntropy ((rare:ℝ)/k) := by
    rw [RealCertificate.logFour]
    norm_num [zeta]
    nlinarith
  exact ⟨hH,(div_le_iff₀ hH).mpr hguard⟩

theorem selected_length (m cn co : ℕ) (hm : 32 ≤ m)
    (hchannel : max cn co ≤ OptimizedFoldedPlan.channelLength m) :
    let k := OptimizedFoldedPlan.ordinaryLength m-m
    let rare := m/2-max cn co
    (m:ℝ)*zeta*Real.log 4 / Real.binEntropy ((rare:ℝ)/k)-1 <
      (forType (OptimizedFoldedPlan.ordinaryLength m) m cn co:ℝ) :=
  selected_length_lower m cn co (quotient_fits m cn co hm hchannel).1
    (quotient_fits m cn co hm hchannel).2

#print axioms suffix_eight
#print axioms rare_quarter
#print axioms type_ratio
#print axioms entropy_lower
#print axioms quotient_fits
#print axioms selected_length
end ThinMatrix.HalfSourceSuffixFeasible
