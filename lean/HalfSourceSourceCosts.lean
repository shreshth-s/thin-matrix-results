import HalfSourceParameters
import SourceFormation

/-! The existing explicit binary Walsh source builds 12^L coordinates and
performs 2^(L-m) reads per coordinate. This module charges that actual dense
source budget to the residual encoder term, with strict slack; the smaller
distinguished-root term is not used to pay it. -/
namespace ThinMatrix.HalfSourceSourceCosts
open HalfSourceParameters Filter Asymptotics
open SourceFormation (sourceBudget sourceBudget_polynomial logTwelve)
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000
noncomputable def directSourceExponent : ℝ := (23/10 : ℝ)*HalfSourceParameters.c-1/2

theorem directSource_gap : directSourceExponent + 1/1000 < T+E := by
  have ht := TEnclosure.1
  have hq := QEnclosure.1
  have ha := AEnclosure.2
  norm_num [directSourceExponent,HalfSourceParameters.c,E,zeta] at *
  linarith

theorem rounded_raw_cost (m : ℕ) :
    (12:ℝ)^(Nat.ceil (HalfSourceParameters.c*(m:ℝ))) *
      (2:ℝ)^(Nat.ceil (HalfSourceParameters.c*(m:ℝ))-m) ≤
      64 * (((4:ℝ)^m)^directSourceExponent) := by
  let L := Nat.ceil (c*(m:ℝ))
  change (12:ℝ)^L * (2:ℝ)^(L-m) ≤ 64 * (((4:ℝ)^m)^directSourceExponent)
  have hm0 : (0:ℝ) ≤ m := Nat.cast_nonneg m
  have hc : 1 ≤ HalfSourceParameters.c := by norm_num [HalfSourceParameters.c]
  have hceil : HalfSourceParameters.c*(m:ℝ) ≤ (L:ℝ) := Nat.le_ceil _
  have hml : m ≤ L := by exact_mod_cast (show (m:ℝ) ≤ (L:ℝ) by nlinarith)
  have hL : (L:ℝ) ≤ HalfSourceParameters.c*(m:ℝ)+1 :=
    (Nat.ceil_lt_add_one (show 0 ≤ HalfSourceParameters.c*(m:ℝ) by positivity)).le
  have h4pos : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have h2 : Real.log 2 = Real.log 4/2 := by linarith [RealCertificate.logFour]
  have h64 : Real.log 64 = 3 * Real.log 4 := by
    convert Real.log_pow (4:ℝ) 3 using 1 <;> norm_num
  have h12L := mul_le_mul_of_nonneg_left logTwelve.le (Nat.cast_nonneg L)
  have hceil4 := mul_le_mul_of_nonneg_right hL h4pos.le
  apply (Real.log_le_log_iff (by positivity) (by positivity)).mp
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow,
    Real.log_mul (by norm_num : (64:ℝ) ≠ 0) (by positivity),
    Real.log_rpow (by positivity), Real.log_pow, h64, Nat.cast_sub hml, h2]
  norm_num [directSourceExponent, HalfSourceParameters.c] at hceil4 ⊢
  nlinarith

private theorem dimension_exp (m : ℕ) (a : ℝ) :
    (((4:ℝ)^m)^a) = Real.exp ((a*Real.log 4)*(m:ℝ)) := by
  rw [Real.rpow_def_of_pos (by positivity), Real.log_pow]
  congr 1
  ring

/-- Every fixed polynomial overhead in the logarithmic dimension fits
inside the proved strict source-versus-residual gap, with constant one
eventually. This includes metadata, all matching degree runs, direct
good-table preparation, and a polynomially bounded input-address routine. -/
theorem eventual_polynomial_source_fit (degree : ℕ) (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ m : ℕ in Filter.atTop,
      C*((m:ℝ)+1)^degree *
        (12:ℝ)^(Nat.ceil (HalfSourceParameters.c*(m:ℝ))) *
        (2:ℝ)^(Nat.ceil (HalfSourceParameters.c*(m:ℝ))-m) ≤
      (((4:ℝ)^m)^(T+E)) := by
  have hgap : directSourceExponent*Real.log 4 <
      (T+E)*Real.log 4 := by
    apply mul_lt_mul_of_pos_right _ (Real.log_pos (by norm_num))
    linarith [directSource_gap]
  have hsmall := (isLittleO_exp_mul_rpow_of_lt (degree:ℝ) hgap).natCast_atTop
  have hscaled := hsmall.const_mul_left (C*64*2^degree)
  have hb := hscaled.bound (show (0:ℝ)<1 by norm_num)
  filter_upwards [hb, Filter.eventually_ge_atTop (1:ℕ)] with m hm hmn
  have hm1 : (1:ℝ) ≤ m := by exact_mod_cast hmn
  have hpow : ((m:ℝ)+1)^degree ≤ (2:ℝ)^degree*(m:ℝ)^degree := by
    rw [← mul_pow]
    gcongr
    linarith
  have hraw := rounded_raw_cost m
  have hCm : 0 ≤ C*((m:ℝ)+1)^degree := by positivity
  have hfirst := mul_le_mul_of_nonneg_left hraw hCm
  have hsecond := mul_le_mul_of_nonneg_left hpow
    (show 0 ≤ C*(64*((4:ℝ)^m)^directSourceExponent) by positivity)
  have hbound : (C*64*2^degree)*
      (Real.exp ((directSourceExponent*Real.log 4)*(m:ℝ))*(m:ℝ)^degree) ≤
      Real.exp (((T+E)*Real.log 4)*(m:ℝ)) := by
    simpa only [Real.rpow_natCast, Real.norm_of_nonneg (by positivity :
      0 ≤ (C*64*2^degree)*(Real.exp ((directSourceExponent*Real.log 4)*(m:ℝ))*
        (m:ℝ)^degree)), Real.norm_of_nonneg (Real.exp_pos _).le, one_mul] using hm
  rw [dimension_exp] at hfirst hsecond
  rw [dimension_exp]
  nlinarith

/-- Instantiation for the actual finite source counter. The address
routine may take any fixed polynomial number of sites in `m`; every
complete cyclic coefficient is still charged by the displayed `q`. -/
theorem eventual_sourceBudget_fit (degree C : ℕ) :
    ∀ᶠ m : ℕ in atTop, ∀ q B : ℕ, 1 ≤ q → B ≤ C*(m+1)^degree →
      (sourceBudget (Nat.ceil (HalfSourceParameters.c*(m:ℝ))) m
        (Nat.ceil (HalfSourceParameters.c*(m:ℝ))-m) q B : ℝ) ≤
        (q:ℝ)*(((4:ℝ)^m)^(T+E)) := by
  let A : ℝ := 2*HalfSourceParameters.c+3
  let constant : ℝ := 200*((C:ℝ)+1)*A^2
  have hA : 0 < A := by norm_num [A, HalfSourceParameters.c]
  have hconstant : 0 ≤ constant := by positivity
  have hfit := eventual_polynomial_source_fit (degree+2) constant hconstant
  filter_upwards [hfit] with m hm
  intro q B hq hB
  let L := Nat.ceil (HalfSourceParameters.c*(m:ℝ))
  let k := L-m
  have hL : (L:ℝ) ≤ HalfSourceParameters.c*(m:ℝ)+1 :=
    (Nat.ceil_lt_add_one (by unfold HalfSourceParameters.c; positivity :
      0 ≤ HalfSourceParameters.c*(m:ℝ))).le
  have hk : (k:ℝ) ≤ L := by exact_mod_cast (Nat.sub_le L m)
  have hm0 : (0:ℝ) ≤ m := Nat.cast_nonneg m
  have hP : ((L:ℝ)+(m:ℝ)+(k:ℝ)+1) ≤ A*((m:ℝ)+1) := by
    norm_num [A, HalfSourceParameters.c] at hL ⊢
    nlinarith
  have hp : 1 ≤ ((m:ℝ)+1)^degree := one_le_pow₀ (by linarith : (1:ℝ) ≤ m+1)
  have hBc : (B:ℝ) ≤ (C:ℝ)*((m:ℝ)+1)^degree := by exact_mod_cast hB
  have hB' : (B:ℝ)+1 ≤ ((C:ℝ)+1)*((m:ℝ)+1)^degree := by nlinarith
  have hc : 200*((B:ℝ)+1)*((L:ℝ)+(m:ℝ)+(k:ℝ)+1)^2 ≤
      constant*((m:ℝ)+1)^(degree+2) := by
    calc
      _ ≤ 200*(((C:ℝ)+1)*((m:ℝ)+1)^degree)*(A*((m:ℝ)+1))^2 := by gcongr
      _ = _ := by unfold constant; rw [pow_add]; ring
  have hs := sourceBudget_polynomial L m k q B hq
  have hsR : (sourceBudget L m k q B:ℝ) ≤
      200*((B:ℝ)+1)*((L:ℝ)+(m:ℝ)+(k:ℝ)+1)^2*(q:ℝ)*(12:ℝ)^L*(2:ℝ)^k := by
    exact_mod_cast hs
  change (sourceBudget L m k q B:ℝ) ≤ _
  calc
    _ ≤ 200*((B:ℝ)+1)*((L:ℝ)+(m:ℝ)+(k:ℝ)+1)^2*(q:ℝ)*(12:ℝ)^L*(2:ℝ)^k := hsR
    _ ≤ constant*((m:ℝ)+1)^(degree+2)*(q:ℝ)*(12:ℝ)^L*(2:ℝ)^k := by gcongr
    _ = (q:ℝ)*(constant*((m:ℝ)+1)^(degree+2)*(12:ℝ)^L*(2:ℝ)^k) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hm (Nat.cast_nonneg q)

#print axioms directSource_gap
#print axioms rounded_raw_cost
#print axioms eventual_polynomial_source_fit
#print axioms eventual_sourceBudget_fit
end
end ThinMatrix.HalfSourceSourceCosts
