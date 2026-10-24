import HalfSourceBatchFit
import WindowPrefixProgram

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! A type-dependent suffix selector using exact capped-binomial counts.
It chooses the largest feasible suffix, rather than a real-log oracle or one
uniform suffix for all channel types. Its finite support fit is unconditional;
the entropy comparison gives a lower bound against every feasible real-entropy
candidate. This module does not yet price the native binomial arithmetic. -/
namespace ThinMatrix.HalfSourceSuffixChoice
open scoped BigOperators
open HalfSourceBatchFit

/-- The suffix's own rare budget, computed from its original channel type. -/
def radius (k rare ell : ℕ) : ℕ := rare*ell/k

def limit (m k : ℕ) : ℕ := (k+1)*ComputableParameters.roundedPower 11 50 (4^m)

def candidates (k rare cap : ℕ) : Finset ℕ :=
  (Finset.range (k+1)).filter (fun ell => CappedSubsetList.count ell (radius k rare ell) ≤ cap)

def choose (k rare cap : ℕ) : ℕ := (candidates k rare cap).sup id

def forType (L m cn co : ℕ) : ℕ :=
  choose (L-m) (m/2-max cn co) (limit m (L-m))

theorem limit_pos (m k : ℕ) : 0 < limit m k := by
  unfold limit ComputableParameters.roundedPower
  positivity

theorem zero_mem (k rare cap : ℕ) (hcap : 0 < cap) : 0 ∈ candidates k rare cap := by
  simp only [candidates,Finset.mem_filter,Finset.mem_range,radius,Nat.mul_zero,Nat.zero_div]
  constructor
  · omega
  · simpa [CappedSubsetList.count] using (show 1 ≤ cap by omega)

theorem choice_mem (k rare cap : ℕ) (hcap : 0 < cap) : choose k rare cap ∈ candidates k rare cap := by
  obtain ⟨ell,hell,heq⟩ := Finset.exists_mem_eq_sup (s:=candidates k rare cap)
    (f:=id) ⟨0,zero_mem k rare cap hcap⟩
  simpa only [choose,id_eq,heq] using hell

theorem choice_bounds (k rare cap : ℕ) (hcap : 0 < cap) :
    choose k rare cap ≤ k ∧ CappedSubsetList.count (choose k rare cap)
      (radius k rare (choose k rare cap)) ≤ cap := by
  have h := Finset.mem_filter.mp (choice_mem k rare cap hcap)
  exact ⟨by have := Finset.mem_range.mp h.1; omega,h.2⟩

theorem choice_maximal (k rare cap ell : ℕ) (hell : ell ≤ k)
    (hfit : CappedSubsetList.count ell (radius k rare ell) ≤ cap) : ell ≤ choose k rare cap := by
  exact Finset.le_sup (f:=id) (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),hfit⟩)

theorem forType_fit (L m cn co : ℕ) :
    forType L m cn co ≤ L-m ∧
    CappedSubsetList.count (forType L m cn co)
      (WindowPrefixProgram.cap (L-m) (forType L m cn co) (m/2) cn co) ≤ limit m (L-m) := by
  have h := choice_bounds (L-m) (m/2-max cn co) (limit m (L-m)) (limit_pos m (L-m))
  refine ⟨h.1,?_⟩
  simpa only [WindowPrefixProgram.cap,WindowPrefixProgram.length,Nat.min_eq_left h.1,forType,radius] using h.2

theorem radius_ratio (k rare ell : ℕ) (hk : 0 < k) (hell : 0 < ell) :
    (radius k rare ell:ℝ)/(ell:ℝ) ≤ (rare:ℝ)/k := by
  have hdiv : radius k rare ell*k ≤ rare*ell := Nat.div_mul_le_self _ _
  have hkR : 0 < (k:ℝ) := by exact_mod_cast hk
  have hellR : 0 < (ell:ℝ) := by exact_mod_cast hell
  apply (div_le_div_iff₀ hellR hkR).mpr
  exact_mod_cast hdiv

theorem radius_le (k rare ell : ℕ) (hr : rare ≤ k) : radius k rare ell ≤ ell := by
  by_cases hk : k=0
  · simp [radius,hk]
  · have h := Nat.div_le_div_right (c:=k) (Nat.mul_le_mul_right ell hr)
    simpa only [radius,Nat.mul_div_cancel_left ell (Nat.pos_of_ne_zero hk)] using h

theorem count_entropy (k rare ell : ℕ) (hell : ell ≤ k) (hhalf : 2*rare ≤ k) :
    (CappedSubsetList.count ell (radius k rare ell):ℝ) ≤
      (k+1:ℝ)*Real.exp ((ell:ℝ)*Real.binEntropy ((rare:ℝ)/k)) := by
  by_cases hzero : ell=0
  · subst ell
    simp [radius,CappedSubsetList.count]
  have hk : 0 < k := by omega
  have hellpos : 0 < ell := by omega
  have ht : (rare:ℝ)/k ≤ 1/2 := by
    apply (div_le_iff₀ (by exact_mod_cast hk : (0:ℝ)<k)).mpr
    have h : 2*(rare:ℝ) ≤ k := by exact_mod_cast hhalf
    linarith
  have hr := radius_ratio k rare ell hk hellpos
  have he := (EntropyBounds.channelTail_entropy ell (radius k rare ell) hellpos (hr.trans ht)).2
  have hm : Real.binEntropy ((radius k rare ell:ℝ)/ell) ≤ Real.binEntropy ((rare:ℝ)/k) := by
    apply Real.binEntropy_strictMonoOn.monotoneOn
    · exact ⟨by positivity,by simpa only [one_div] using hr.trans ht⟩
    · exact ⟨by positivity,by simpa only [one_div] using ht⟩
    · exact hr
  have hrc : radius k rare ell ≤ k := (radius_le k rare ell (by omega)).trans hell
  have hrcR : (radius k rare ell:ℝ)+1 ≤ (k:ℝ)+1 := by exact_mod_cast Nat.add_le_add_right hrc 1
  have htail : EntropyBounds.channelTail ell (radius k rare ell)=
      (CappedSubsetList.count ell (radius k rare ell):ℝ) := by
    simp only [EntropyBounds.channelTail,CappedSubsetList.count,Nat.cast_sum]
  rw [htail] at he
  exact he.trans (mul_le_mul hrcR (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hm (Nat.cast_nonneg ell)))
    (Real.exp_nonneg _) (by positivity))

/-- Any suffix satisfying the entropy inequality passes the exact integer
support test, including all polynomial loss from the capped-binomial sum. -/
theorem entropy_candidate (m k rare ell : ℕ) (hell : ell ≤ k) (hhalf : 2*rare ≤ k)
    (hentropy : (ell:ℝ)*Real.binEntropy ((rare:ℝ)/k) ≤ (m:ℝ)*zeta*Real.log 4) :
    CappedSubsetList.count ell (radius k rare ell) ≤ limit m k := by
  have hc := count_entropy k rare ell hell hhalf
  have hr := (ComputableParameters.roundedPower_bounds 11 50 (4^m)
    (by norm_num) (by norm_num) (by exact one_le_pow₀ (by norm_num))).1
  have heq : Real.exp ((m:ℝ)*zeta*Real.log 4)=((4^m:ℕ):ℝ)^zeta := by
    rw [Nat.cast_pow,Nat.cast_ofNat,← Real.rpow_natCast,← Real.rpow_mul (by norm_num : (0:ℝ)≤4)]
    rw [Real.rpow_def_of_pos (by norm_num)]
    congr 1
    ring
  have hexp := Real.exp_le_exp.mpr hentropy
  rw [heq] at hexp
  have hr' : ((4^m:ℕ):ℝ)^zeta ≤ (ComputableParameters.roundedPower 11 50 (4^m):ℝ) := hr
  have hu := hc.trans (mul_le_mul_of_nonneg_left (hexp.trans hr') (by positivity : (0:ℝ)≤(k:ℝ)+1))
  exact_mod_cast hu

theorem choice_dominates_entropy (m k rare ell : ℕ) (hell : ell ≤ k) (hhalf : 2*rare ≤ k)
    (hentropy : (ell:ℝ)*Real.binEntropy ((rare:ℝ)/k) ≤ (m:ℝ)*zeta*Real.log 4) :
    ell ≤ choose k rare (limit m k) :=
  choice_maximal k rare (limit m k) ell hell (entropy_candidate m k rare ell hell hhalf hentropy)

/-- Explicit lower bound on the selected length; the real quotient is used
only in this theorem, never evaluated by the selector. -/
theorem choice_floor_lower (m k rare : ℕ) (hhalf : 2*rare ≤ k)
    (hH : 0 < Real.binEntropy ((rare:ℝ)/k)) :
    min k (Nat.floor ((m:ℝ)*zeta*Real.log 4 / Real.binEntropy ((rare:ℝ)/k))) ≤
      choose k rare (limit m k) := by
  apply choice_dominates_entropy m k rare _ (Nat.min_le_left _ _) hhalf
  have hX : 0 ≤ (m:ℝ)*zeta*Real.log 4 / Real.binEntropy ((rare:ℝ)/k) := by
    have hz : 0 ≤ zeta := by norm_num [zeta]
    have hl : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    positivity
  have hfloor := Nat.floor_le hX
  have hle : ((min k (Nat.floor ((m:ℝ)*zeta*Real.log 4 / Real.binEntropy ((rare:ℝ)/k))):ℕ):ℝ) ≤
      (Nat.floor ((m:ℝ)*zeta*Real.log 4 / Real.binEntropy ((rare:ℝ)/k)):ℝ) := by
    exact_mod_cast Nat.min_le_right k _
  exact (le_div_iff₀ hH).mp (hle.trans hfloor)

theorem zero_entropy_full_length (m k rare : ℕ) (hhalf : 2*rare ≤ k)
    (hH : Real.binEntropy ((rare:ℝ)/k)=0) : choose k rare (limit m k)=k := by
  apply Nat.le_antisymm (choice_bounds k rare (limit m k) (limit_pos m k)).1
  apply choice_dominates_entropy m k rare k le_rfl hhalf
  rw [hH,mul_zero]
  have hz : 0 ≤ zeta := by norm_num [zeta]
  have hl : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  positivity

theorem choice_quotient_slack (m k rare : ℕ) (hhalf : 2*rare ≤ k)
    (hH : 0 < Real.binEntropy ((rare:ℝ)/k))
    (hfit : (m:ℝ)*zeta*Real.log 4 / Real.binEntropy ((rare:ℝ)/k) ≤ (k:ℝ)) :
    (m:ℝ)*zeta*Real.log 4 / Real.binEntropy ((rare:ℝ)/k)-1 <
      (choose k rare (limit m k):ℝ) := by
  have hX : 0 ≤ (m:ℝ)*zeta*Real.log 4 / Real.binEntropy ((rare:ℝ)/k) := by
    have hz : 0 ≤ zeta := by norm_num [zeta]
    have hl : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    positivity
  have hf : Nat.floor ((m:ℝ)*zeta*Real.log 4 / Real.binEntropy ((rare:ℝ)/k)) ≤ k := by
    exact_mod_cast (Nat.floor_le hX).trans hfit
  have hc := choice_floor_lower m k rare hhalf hH
  rw [Nat.min_eq_right hf] at hc
  have hcR : (Nat.floor ((m:ℝ)*zeta*Real.log 4 / Real.binEntropy ((rare:ℝ)/k)):ℝ) ≤
      (choose k rare (limit m k):ℝ) := by exact_mod_cast hc
  linarith [Nat.lt_floor_add_one ((m:ℝ)*zeta*Real.log 4 / Real.binEntropy ((rare:ℝ)/k))]

#print axioms choice_floor_lower
#print axioms zero_entropy_full_length
#print axioms choice_quotient_slack
#print axioms limit_pos
#print axioms zero_mem
#print axioms choice_mem
#print axioms choice_bounds
#print axioms choice_maximal
#print axioms forType_fit
#print axioms radius_ratio
#print axioms radius_le
#print axioms count_entropy
#print axioms entropy_candidate
#print axioms choice_dominates_entropy
end ThinMatrix.HalfSourceSuffixChoice
