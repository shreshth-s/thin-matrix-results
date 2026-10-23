import CWHomogeneousCopies
import CWEntropyCertificate

set_option autoImplicit false

/-! Strict finite-base selection for the actual rational CW decomposition.
Interpolation, the copy-count loss and the last padded batch are all charged
in the finite term multiplier. This is a rank construction, not yet a bound
for a binary execution of dense coefficient arrays. -/
namespace ThinMatrix.CWFiniteBase
open Filter
open scoped Topology
open CWHomogeneousCopies CWTargetExtractionRate CWTargetMarginals CWEntropySurvival

noncomputable def exponent : ℝ := 167220001/10000000
noncomputable def growth : ℝ := (4000/75249:ℝ)*exponent*Real.log 16

theorem growth_pos : 0<growth := by unfold growth exponent;positivity
theorem gap_pos : 0<growth-(Real.log 18-rate) := by
  have h := CWEntropyCertificate.rate_margin
  change Real.log 18<rate+growth at h
  linarith

theorem linear_absorbed (ε : ℝ) (he : 0<ε) :
    ∀ᶠ x : ℝ in atTop, 10*x+2≤Real.exp (x*ε) := by
  have h := (isLittleO_pow_exp_pos_mul_atTop 1 he).bound
    (show (0:ℝ)<1/12 by norm_num)
  filter_upwards [h,eventually_ge_atTop (1:ℝ)] with x hx hx1
  have hh : x≤(1/12:ℝ)*Real.exp (ε*x) := by
    simpa only [pow_one,Real.norm_eq_abs,abs_of_nonneg (show 0≤x by linarith),
      abs_of_pos (Real.exp_pos _)] using hx
  rw [mul_comm x ε]
  linarith

theorem rounded_ratio (r t : ℕ) (ht : 0<t) :
    (((r+t-1)/t:ℕ):ℝ)≤(r:ℝ)/t+1 := by
  have hn : ((r+t-1)/t)*t≤r+t :=
    (Nat.div_mul_le_self _ _).trans (Nat.sub_le _ _)
  have hp : (0:ℝ)<t := by exact_mod_cast ht
  rw [show (r:ℝ)/t+1=((r:ℝ)+t)/t by field_simp]
  apply (le_div_iff₀ hp).mpr
  exact_mod_cast hn

theorem eventual_base : ∀ᶠ s : ℕ in atTop, ∃ h : Sample s,
    0<copies s h ∧
      (((ranks s+copies s h-1)/copies s h:ℕ):ℝ)≤
        Real.exp ((size s:ℝ)*growth) := by
  let ε : ℝ := min (growth-(Real.log 18-rate)) growth/4
  have he : 0<ε := by dsimp [ε];exact div_pos (lt_min gap_pos growth_pos) (by norm_num)
  have heg : ε≤(growth-(Real.log 18-rate))/4 := by
    exact div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
  have hel : ε≤growth/4 := by
    exact div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
  have hslack : Real.log 18-rate+ε≤growth-ε := by linarith
  have hpositive : 0≤growth-ε := by linarith [growth_pos]
  filter_upwards [CWTargetExtractionRate.exponential_extraction ε he,
    size_tendsto.eventually (linear_absorbed ε he)] with s hs hp
  obtain ⟨h,ht,_,_,_⟩ := hs
  have htn : 0<copies s h := by
    have htr : (0:ℝ)<copies s h := lt_of_lt_of_le (Real.exp_pos _) ht
    exact_mod_cast htr
  refine ⟨h,htn,?_⟩
  have hn : (0:ℝ) ≤ size s := by positivity
  have hnum : (ranks s:ℝ)=(10*(size s:ℝ)+1)*Real.exp ((size s:ℝ)*Real.log 18) := by
    simp only [ranks,Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat,Nat.cast_pow]
    rw [Real.exp_nat_mul,Real.exp_log (by norm_num : (0:ℝ)<18)]
  have hd : (ranks s:ℝ)/copies s h≤
      (10*(size s:ℝ)+1)*Real.exp ((size s:ℝ)*(growth-ε)) := by
    calc
      _ ≤ (ranks s:ℝ)/Real.exp ((size s:ℝ)*(rate-ε)) :=
        div_le_div_of_nonneg_left (by positivity) (Real.exp_pos _) ht
      _ = (10*(size s:ℝ)+1)*Real.exp ((size s:ℝ)*(Real.log 18-rate+ε)) := by
        rw [hnum,mul_div_assoc,←Real.exp_sub]
        congr 2
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hslack hn)) (by positivity)
  have hlarge : 1≤Real.exp ((size s:ℝ)*(growth-ε)) :=
    Real.one_le_exp (mul_nonneg hn hpositive)
  calc
    _ ≤ (ranks s:ℝ)/copies s h+1 := rounded_ratio _ _ htn
    _ ≤ (10*(size s:ℝ)+2)*Real.exp ((size s:ℝ)*(growth-ε)) := by nlinarith
    _ ≤ Real.exp ((size s:ℝ)*ε)*Real.exp ((size s:ℝ)*(growth-ε)) :=
      mul_le_mul_of_nonneg_right hp (Real.exp_nonneg _)
    _ = _ := by rw [←Real.exp_add];congr 1;ring

theorem exists_positive_base : ∃ s : ℕ, 0<s ∧ ∃ h : Sample s,
    0<copies s h ∧
      (((ranks s+copies s h-1)/copies s h:ℕ):ℝ)≤
        Real.exp ((size s:ℝ)*growth) := by
  obtain ⟨s,hs,hn⟩ := (eventual_base.and (eventually_ge_atTop 1)).exists
  exact ⟨s,by omega,hs⟩

#print axioms growth_pos
#print axioms gap_pos
#print axioms linear_absorbed
#print axioms rounded_ratio
#print axioms eventual_base
#print axioms exists_positive_base
end ThinMatrix.CWFiniteBase
