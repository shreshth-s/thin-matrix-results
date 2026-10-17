import CertificationParameters
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Tactic

/-!
# Integer programs for the rounded research parameters

All data-producing definitions in this module use natural-number
arithmetic and finite loops. Real powers and logarithms occur only in
theorems comparing their outputs with the geometry bounds.
-/
namespace ThinMatrix.ComputableParameters

open scoped BigOperators
open Filter Real

/-- A literal finite search. Each candidate is tested by two fixed-degree
integer powers. This deliberately simple program has n+1 test sites. -/
def rootScan (p q n : ℕ) : ℕ :=
  (Finset.range (n+1)).sup (fun x => if x^q ≤ n^p then x else 0)

theorem rootScan_eq_nthRoot (p q n : ℕ) (hq : q ≠ 0)
    (hpq : p ≤ q) (hn : 1 ≤ n) :
    rootScan p q n = Nat.nthRoot q (n^p) := by
  have hroot : Nat.nthRoot q (n^p) ≤ n := by
    have hp : n^p ≤ n^q := Nat.pow_le_pow_right hn hpq
    have hlt : n^q < (n+1)^q := Nat.pow_lt_pow_left (by omega) hq
    have h := (Nat.nthRoot_lt_iff hq).mpr (hp.trans_lt hlt)
    omega
  apply Nat.le_antisymm
  · apply Finset.sup_le
    intro x hx
    split_ifs with h
    · exact (Nat.le_nthRoot_iff hq).mpr h
    · exact Nat.zero_le _
  · have hm : Nat.nthRoot q (n^p) ∈ Finset.range (n+1) :=
      Finset.mem_range.mpr (by omega)
    have h := Finset.le_sup (f := fun x => if x^q ≤ n^p then x else 0) hm
    simpa only [rootScan, if_pos (Nat.pow_nthRoot_le (a := n^p) (Or.inl hq))] using h

theorem nthRoot_real_bounds (n p q : ℕ) (hq : q ≠ 0) :
    (Nat.nthRoot q (n^p):ℝ) ≤ (n:ℝ)^((p:ℝ)/q) ∧
    (n:ℝ)^((p:ℝ)/q) < (Nat.nthRoot q (n^p):ℝ)+1 := by
  have hp : ((n:ℝ)^((p:ℝ)/q))^q = (n:ℝ)^p := by
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg n)]
    have hqR : (q:ℝ) ≠ 0 := by exact_mod_cast hq
    rw [div_mul_cancel₀ _ hqR, Real.rpow_natCast]
  have hroot : (Nat.nthRoot q (n^p):ℝ)^q ≤ (n:ℝ)^p := by
    exact_mod_cast Nat.pow_nthRoot_le (a := n^p) (Or.inl hq)
  have hroot' : (n:ℝ)^p < ((Nat.nthRoot q (n^p):ℝ)+1)^q := by
    exact_mod_cast Nat.lt_pow_nthRoot_add_one hq (n^p)
  constructor
  · apply (pow_le_pow_iff_left₀ (Nat.cast_nonneg _)
      (Real.rpow_nonneg (Nat.cast_nonneg _) _) hq).mp
    rwa [hp]
  · apply (pow_lt_pow_iff_left₀ (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      (by positivity) hq).mp
    rwa [hp]

def roundedPower (p q n : ℕ) : ℕ := rootScan p q n+1

theorem roundedPower_bounds (p q n : ℕ) (hq : q ≠ 0)
    (hpq : p ≤ q) (hn : 1 ≤ n) :
    (n:ℝ)^((p:ℝ)/q) ≤ (roundedPower p q n:ℝ) ∧
      (roundedPower p q n:ℝ) ≤ 2*(n:ℝ)^((p:ℝ)/q) := by
  have hr := nthRoot_real_bounds n p q hq
  have hpow : 1 ≤ (n:ℝ)^((p:ℝ)/q) :=
    Real.one_le_rpow (by exact_mod_cast hn) (by positivity)
  unfold roundedPower
  rw [rootScan_eq_nthRoot p q n hq hpq hn, Nat.cast_add, Nat.cast_one]
  constructor <;> linarith

/-- Fixed explicit numerator and denominator; these are not reduced by
normalizing any parameter-sized power. -/
def bNumerator : ℕ := 46046346
def bDenominator : ℕ := 1000000000
def factorCount : ℕ := 1000000000

def block (n : ℕ) : ℕ := roundedPower bNumerator bDenominator n
def scale (n : ℕ) : ℕ :=
  roundedPower bNumerator (bDenominator*factorCount) n * n.size^4

theorem b_ratio : (bNumerator:ℝ)/bDenominator = AsymptoticCosts.b := by
  norm_num [bNumerator, bDenominator, AsymptoticCosts.b, AlignedCertificate.b]

theorem eta_ratio :
    (bNumerator:ℝ)/(bDenominator*factorCount) = AsymptoticCosts.eta := by
  norm_num [bNumerator, bDenominator, factorCount, AsymptoticCosts.eta,
    AlignedCertificate.eta, AlignedCertificate.b, AlignedCertificate.R]

theorem block_bounds (n : ℕ) (hn : 1 ≤ n) :
    (n:ℝ)^AsymptoticCosts.b ≤ (block n:ℝ) ∧
      (block n:ℝ) ≤ 2*(n:ℝ)^AsymptoticCosts.b := by
  have h := roundedPower_bounds bNumerator bDenominator n
    (by norm_num [bDenominator]) (by norm_num [bNumerator, bDenominator]) hn
  simpa only [block, b_ratio] using h

def rootTestSites (n : ℕ) : Finset ℕ := Finset.range (n+1)

theorem rootTestSites_card (n : ℕ) : (rootTestSites n).card = n+1 := by
  simp [rootTestSites]

/-- A finite power-operation charge for the simple search, with fixed
arity exponents and a comparison/max charge at each candidate. -/
def rootSearchWork (p q n : ℕ) : ℕ := (n+1)*(p+q+2)

theorem rootSearchWork_linear (p q n : ℕ) (hn : 1 ≤ n) :
    rootSearchWork p q n ≤ (2*(p+q+2))*n := by
  unfold rootSearchWork
  nlinarith

lemma log_two_bounds : (1 / 2 : ℝ) ≤ Real.log 2 ∧ Real.log 2 ≤ 1 := by
  constructor
  · have h := Real.one_sub_inv_le_log_of_pos (x := (2 : ℝ)) (by norm_num)
    norm_num at h ⊢
    exact h
  · have h := Real.log_le_sub_one_of_pos (x := (2 : ℝ)) (by norm_num)
    norm_num at h ⊢
    exact h

lemma log_le_size (n : ℕ) (hn : 0 < n) : Real.log n ≤ (n.size : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hpow : (n : ℝ) ≤ (2 : ℝ) ^ n.size := by
    exact_mod_cast (Nat.lt_size_self n).le
  have hlog := Real.log_le_log hnR hpow
  rw [Real.log_pow] at hlog
  have hs : (0 : ℝ) ≤ n.size := by positivity
  have hmul := mul_le_mul_of_nonneg_left log_two_bounds.2 hs
  simpa using hlog.trans hmul

lemma size_le_four_log (n : ℕ) (hn : 3 ≤ n) :
    (n.size : ℝ) ≤ 4 * Real.log n := by
  have hnpos : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hspos : 0 < n.size := Nat.size_pos.mpr hnpos
  have hpN : 2 ^ (n.size - 1) ≤ n := Nat.lt_size.mp (by omega)
  have hpR : (2 : ℝ) ^ (n.size - 1) ≤ (n : ℝ) := by exact_mod_cast hpN
  have hlog := Real.log_le_log (by positivity : (0 : ℝ) < (2 : ℝ) ^ (n.size - 1)) hpR
  rw [Real.log_pow] at hlog
  have hsCast : ((n.size - 1 : ℕ) : ℝ) = (n.size : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  rw [hsCast] at hlog
  have hsize : (0 : ℝ) ≤ (n.size : ℝ) - 1 := by
    have hh : (1 : ℝ) ≤ n.size := by exact_mod_cast (show 1 ≤ n.size from hspos)
    linarith
  have hmul := mul_le_mul_of_nonneg_left log_two_bounds.1 hsize
  have htwo : (2 : ℝ) ≤ n := by exact_mod_cast (show 2 ≤ n from by omega)
  have hlogtwo := Real.log_le_log (by norm_num : (0 : ℝ) < 2) htwo
  have hhalf : (1 / 2 : ℝ) ≤ Real.log n := log_two_bounds.1.trans hlogtwo
  nlinarith

lemma size_log_comparison (n : ℕ) (hn : 3 ≤ n) :
    (1 / 2 : ℝ) * Real.log n ≤ (n.size : ℝ) ∧
      (n.size : ℝ) ≤ 4 * Real.log n := by
  constructor
  · have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast (show 1 ≤ n from by omega))
    have h := log_le_size n (by omega)
    linarith
  · exact size_le_four_log n hn


open PrimePool PhaseGeometry CertificationParameters

theorem scale_log_upper (n P : ℕ) (eta A : ℝ)
    (hn : 3 ≤ n) (hA : 0 < A) (hP : 0 < P)
    (hu : (P : ℝ) ≤ A*(n : ℝ)^eta*(Real.log (n : ℝ))^4) :
    Real.log (P : ℝ) ≤ (|Real.log A|+eta+4)*Real.log (n : ℝ) := by
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (show 0<n by omega)
  have hl1 := one_le_log_nat n hn
  have hlpos : 0 < Real.log (n : ℝ) := by linarith
  have hxpos : 0 < (n : ℝ)^eta := Real.rpow_pos_of_pos hnpos eta
  have hlog := Real.log_le_log (by exact_mod_cast hP : (0:ℝ)<P) hu
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_mul hA.ne' hxpos.ne', Real.log_rpow hnpos,
    Real.log_pow] at hlog
  have hCabs : Real.log A ≤ |Real.log A| := le_abs_self _
  have hCmul : |Real.log A| ≤ |Real.log A| * Real.log (n : ℝ) :=
    le_mul_of_one_le_right (abs_nonneg _) hl1
  have hll := Real.log_le_self hlpos.le
  norm_num only [Nat.cast_ofNat] at hlog
  nlinarith

theorem scale_tendsto (P : ℕ → ℕ) {eta a : ℝ}
    (heta : 0 < eta) (ha : 0 < a)
    (hl : ∀ᶠ n : ℕ in atTop,
      a*(n : ℝ)^eta*(Real.log (n : ℝ))^4 ≤ (P n : ℝ)) :
    Tendsto P atTop atTop := by
  apply (tendsto_natCast_atTop_iff (R := ℝ)).mp
  have hx := (tendsto_rpow_atTop heta).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have hax := hx.const_mul_atTop ha
  apply Filter.tendsto_atTop_mono' atTop _ hax
  filter_upwards [hl, eventually_ge_atTop (3 : ℕ)] with n hl hn
  change a*(n : ℝ)^eta ≤ (P n : ℝ)
  have hlog : 1 ≤ (Real.log (n : ℝ))^4 := one_le_pow₀ (one_le_log_nat n hn)
  exact (le_mul_of_one_le_right (by positivity) hlog).trans hl

theorem eventual_scale_pool_sub_lower (P : ℕ → ℕ) {eta a A : ℝ}
    (heta : 0 < eta) (ha : 0 < a) (hA : 0 < A)
    (hl : ∀ᶠ n : ℕ in atTop,
      a*(n : ℝ)^eta*(Real.log (n : ℝ))^4 ≤ (P n : ℝ))
    (hu : ∀ᶠ n : ℕ in atTop,
      (P n : ℝ) ≤ A*(n : ℝ)^eta*(Real.log (n : ℝ))^4)
    (B : ℝ) (hB : 0 < B) (R : ℕ) (excluded : Finset ℕ) :
    ∀ᶠ n : ℕ in atTop,
      B*(n : ℝ)^eta*Real.log (n : ℝ) ≤
        (((PrimePool.available (P n) excluded).card-R : ℕ) : ℝ) := by
  let K := |Real.log A|+eta+4
  have hK : 0 < K := by dsimp [K]; positivity
  have ht := scale_tendsto P heta ha hl
  have hx := (tendsto_rpow_atTop heta).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have hlog := Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have hp := ht.eventually (PrimePool.eventually_available_card_lower excluded)
  have hP2 := ht.eventually (eventually_ge_atTop (2 : ℕ))
  have hlarge := hlog.eventually (eventually_ge_atTop (16*K*B/a))
  have hR := hx.eventually (eventually_ge_atTop ((R : ℝ)/B))
  filter_upwards [hp, hP2, hlarge, hR, hl, hu, eventually_ge_atTop (3 : ℕ)] with
    n hp hP2 hlarge hR hl hu hn
  dsimp only [Function.comp_apply] at hlarge hR
  have hl1 := one_le_log_nat n hn
  have hlpos : 0 < Real.log (n : ℝ) := by linarith
  have hx0 : 0 ≤ (n : ℝ)^eta := Real.rpow_nonneg (Nat.cast_nonneg n) eta
  have hPpos : 0 < Real.log (P n : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < P n by omega)
  have hT : 16*K*B ≤ a*(Real.log (n : ℝ))^2 := by
    have hT1 := (div_le_iff₀ ha).mp hlarge
    have hll : Real.log (n : ℝ) ≤ (Real.log (n : ℝ))^2 := by nlinarith
    have := mul_le_mul_of_nonneg_left hll ha.le
    nlinarith
  have hlogBound := scale_log_upper n (P n) eta A hn hA (by omega) hu
  change Real.log (P n : ℝ) ≤ K*Real.log (n : ℝ) at hlogBound
  have hnum :
      (2*B*(n : ℝ)^eta*Real.log (n : ℝ))*(8*Real.log (P n : ℝ)) ≤
      (P n : ℝ) := by
    calc
      _ ≤ (2*B*(n : ℝ)^eta*Real.log (n : ℝ))*(8*K*Real.log (n : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        nlinarith [hlogBound]
      _ = (16*K*B)*((n : ℝ)^eta*(Real.log (n : ℝ))^2) := by ring
      _ ≤ (a*(Real.log (n : ℝ))^2)*((n : ℝ)^eta*(Real.log (n : ℝ))^2) :=
        mul_le_mul_of_nonneg_right hT (by positivity)
      _ = a*(n : ℝ)^eta*(Real.log (n : ℝ))^4 := by ring
      _ ≤ (P n : ℝ) := hl
  have hcard : 2*B*(n : ℝ)^eta*Real.log (n : ℝ) ≤
      ((PrimePool.available (P n) excluded).card : ℝ) :=
    ((le_div_iff₀ (by positivity : 0 < 8*Real.log (P n : ℝ))).mpr hnum).trans hp
  have hR' : (R : ℝ) ≤ B*(n : ℝ)^eta*Real.log (n : ℝ) := by
    have hRB : (R : ℝ) ≤ (n : ℝ)^eta*B := (div_le_iff₀ hB).mp hR
    calc
      (R : ℝ) ≤ (n : ℝ)^eta*B := hRB
      _ ≤ ((n : ℝ)^eta*B)*Real.log (n : ℝ) :=
        le_mul_of_one_le_right (by positivity) hl1
      _ = _ := by ring
  have hRcard : R ≤ (PrimePool.available (P n) excluded).card := by
    exact_mod_cast (show (R : ℝ) ≤ ((PrimePool.available (P n) excluded).card : ℝ) by
      nlinarith [mul_nonneg hB.le hx0])
  rw [Nat.cast_sub hRcard]
  linarith

theorem eventual_sufficient_scale (P H : ℕ → ℕ) (b eta C κ a upper : ℝ) (R : ℕ)
    (hH : ∀ᶠ n : ℕ in atTop, (H n:ℝ) ≤ 2*(n:ℝ)^b)
    (hR : 0 < R) (heta : 0 < eta) (hbalance : (R:ℝ)*eta=b) (hC : 0 < C)
    (ha : 0 < a) (hUpper : 0 < upper)
    (hl : ∀ᶠ n : ℕ in atTop,
      a*(n : ℝ)^eta*(Real.log (n : ℝ))^4 ≤ (P n : ℝ))
    (hu : ∀ᶠ n : ℕ in atTop,
      (P n : ℝ) ≤ upper*(n : ℝ)^eta*(Real.log (n : ℝ))^4) :
    ∀ᶠ n : ℕ in atTop, ∀ U : ℕ, (U:ℝ) ≤ C*(n:ℝ)^κ →
      2 ≤ P n ∧
      0 < (pool (P n)).card-R ∧
      2*U.size ≤ (pool (P n)).card-R ∧
      4*H n*U.size^R ≤ ((pool (P n)).card-R)^R := by
  let L := (|Real.log C|+|κ|)/Real.log 2+1
  let A := 8*(L+1)
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hA : 0 < A := by dsimp [A]; linarith
  have hpool := eventual_scale_pool_sub_lower P heta ha hUpper hl hu A hA R {3}
  have hsize := uniform_size_log C κ hC
  have hP := (scale_tendsto P heta ha hl).eventually (eventually_ge_atTop (2:ℕ))
  filter_upwards [hpool, hsize, hP, hH, eventually_ge_atTop (3:ℕ)] with
    n hpooln hsizen hPn hblock hn
  intro U hU
  have hn1 : 1 ≤ n := by omega
  have hna : 1 ≤ (n:ℝ)^eta := Real.one_le_rpow (by exact_mod_cast hn1) heta.le
  have hlog := one_le_log_nat n hn
  have hlu : (U.size:ℝ)+1 ≤ (L+1)*Real.log (n:ℝ) := by
    have h := hsizen U hU
    change (U.size:ℝ) ≤ L*Real.log (n:ℝ) at h
    nlinarith
  have hrel : 8*(n:ℝ)^eta*((U.size:ℝ)+1) ≤
      (((pool (P n)).card-R:ℕ):ℝ) := by
    rw [pool_eq_available]
    have h := mul_le_mul_of_nonneg_left hlu
      (show 0 ≤ 8*(n:ℝ)^eta by positivity)
    dsimp [A] at hpooln
    nlinarith
  have hsmall : 8*((U.size:ℝ)+1) ≤
      (((pool (P n)).card-R:ℕ):ℝ) := by
    have h := mul_le_mul_of_nonneg_left hna
      (show 0 ≤ 8*((U.size:ℝ)+1) by positivity)
    nlinarith
  have hM : 0 < (pool (P n)).card-R := by
    have h : (0:ℝ) < (((pool (P n)).card-R:ℕ):ℝ) := by
      nlinarith
    exact_mod_cast h
  have hhalf : 2*U.size ≤ (pool (P n)).card-R := by
    have h : (2:ℝ)*(U.size:ℝ) ≤
        (((pool (P n)).card-R:ℕ):ℝ) := by nlinarith
    exact_mod_cast h
  have hRreal : (0:ℝ) < R := by exact_mod_cast hR
  have hb : 0 ≤ b := by nlinarith
  have hpow : (8*(n:ℝ)^eta*(U.size:ℝ))^R ≤
      ((((pool (P n)).card-R:ℕ):ℝ))^R := by
    apply pow_le_pow_left₀ (by positivity)
    nlinarith [mul_nonneg (show 0 ≤ 8*(n:ℝ)^eta by positivity)
      (show 0 ≤ (1:ℝ) by norm_num)]
  have hexponent : ((n:ℝ)^eta)^R = (n:ℝ)^b := by
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg n)]
    congr 1
    linarith
  have height : (8:ℝ) ≤ (8:ℝ)^R := by
    have h : (8:ℕ) ≤ 8^R := by
      calc
        8 = 8^1 := by norm_num
        _ ≤ 8^R := Nat.pow_le_pow_right (by norm_num) (by omega)
    exact_mod_cast h
  have hrate : 4*H n*U.size^R ≤
      ((pool (P n)).card-R)^R := by
    have hreal : (4:ℝ)*(H n:ℝ)*(U.size:ℝ)^R ≤
        ((((pool (P n)).card-R:ℕ):ℝ))^R := by
      calc
        (4:ℝ)*(H n:ℝ)*(U.size:ℝ)^R
            ≤ 8*(n:ℝ)^b*(U.size:ℝ)^R := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          linarith
        _ ≤ (8:ℝ)^R*(n:ℝ)^b*(U.size:ℝ)^R := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right height (by positivity)) (by positivity)
        _ = (8*(n:ℝ)^eta*(U.size:ℝ))^R := by
          rw [mul_pow, mul_pow, hexponent]
        _ ≤ _ := hpow
    exact_mod_cast hreal
  exact ⟨hPn, hM, hhalf, hrate⟩


theorem generationWork_scale_eventually (P : ℕ → ℕ) {eta a upper : ℝ}
    (heta : 0 < eta) (ha : 0 < a) (_hUpper : 0 < upper)
    (hl : ∀ᶠ n : ℕ in atTop,
      a*(n : ℝ)^eta*(Real.log (n : ℝ))^4 ≤ (P n : ℝ))
    (hu : ∀ᶠ n : ℕ in atTop,
      (P n : ℝ) ≤ upper*(n : ℝ)^eta*(Real.log (n : ℝ))^4)
    (d C : ℝ) (K : ℕ) (hC : 0 ≤ C) (hgap : 2*eta < d) :
    ∀ᶠ n : ℕ in atTop,
      C*(Real.log (n : ℝ))^K*(generationWork (P n) : ℝ) ≤ (n : ℝ)^d := by
  have ht := (scale_tendsto P heta ha hl).eventually (eventually_ge_atTop (1 : ℕ))
  have hfit := AsymptoticCosts.eventualPowerFit hgap (K+8) (C*72*upper^2)
  filter_upwards [hu, ht, hfit, eventually_ge_atTop (3 : ℕ)] with n hu hP hfit hn
  have hlog := one_le_log_nat n hn
  have he : ((n : ℝ)^eta)^2 = (n : ℝ)^(2*eta) := by
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg n)]
    congr 1
    ring
  have hw : (generationWork (P n) : ℝ) ≤
      72*upper^2*(Real.log (n : ℝ))^8*(n : ℝ)^(2*eta) := by
    calc
      _ ≤ 72*(P n : ℝ)^2 := generationWork_le (P n) hP
      _ ≤ 72*(upper*(n : ℝ)^eta*(Real.log (n : ℝ))^4)^2 := by
        gcongr
      _ = _ := by rw [mul_pow, mul_pow, ← pow_mul, he]; ring
  calc
    _ ≤ C*(Real.log (n : ℝ))^K*
        (72*upper^2*(Real.log (n : ℝ))^8*(n : ℝ)^(2*eta)) :=
      mul_le_mul_of_nonneg_left hw (by positivity)
    _ = (C*72*upper^2)*(Real.log (n : ℝ))^(K+8)*(n : ℝ)^(2*eta) := by
      rw [pow_add]
      ring
    _ ≤ _ := hfit


theorem scale_bounds (n : ℕ) (hn : 3 ≤ n) :
    (n:ℝ)^AsymptoticCosts.eta*(Real.log (n:ℝ))^4 ≤ (scale n:ℝ) ∧
      (scale n:ℝ) ≤ 512*(n:ℝ)^AsymptoticCosts.eta*(Real.log (n:ℝ))^4 := by
  have hr := roundedPower_bounds bNumerator (bDenominator*factorCount) n
    (by norm_num [bDenominator, factorCount])
    (by norm_num [bNumerator, bDenominator, factorCount]) (by omega)
  have hr' :
      (n:ℝ)^AsymptoticCosts.eta ≤
        (roundedPower bNumerator (bDenominator*factorCount) n:ℝ) ∧
      (roundedPower bNumerator (bDenominator*factorCount) n:ℝ) ≤
        2*(n:ℝ)^AsymptoticCosts.eta := by
    simpa only [Nat.cast_mul, eta_ratio] using hr
  have hslo := log_le_size n (by omega)
  have hshi := size_le_four_log n hn
  have hlog : 0 ≤ Real.log (n:ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1≤n by omega))
  unfold scale
  rw [Nat.cast_mul, Nat.cast_pow]
  constructor
  · exact mul_le_mul hr'.1 (pow_le_pow_left₀ hlog hslo 4) (by positivity) (by positivity)
  · calc
      _ ≤ (2*(n:ℝ)^AsymptoticCosts.eta)*(4*Real.log (n:ℝ))^4 := by
        gcongr
        · exact hr'.2
      _ = _ := by ring

theorem scale_compare_primeScale (n : ℕ) (hn : 3 ≤ n) :
    PhaseGeometry.primeScale n AsymptoticCosts.eta 4 ≤ scale n ∧
      (scale n:ℝ) ≤ 512*(PhaseGeometry.primeScale n AsymptoticCosts.eta 4:ℝ) := by
  have hs := scale_bounds n hn
  constructor
  · exact Nat.ceil_le.mpr hs.1
  · have hp := (PhaseGeometry.primeScale_bounds n AsymptoticCosts.eta 4 hn
      (by norm_num [AsymptoticCosts.eta, AlignedCertificate.eta,
        AlignedCertificate.b, AlignedCertificate.R])).1
    nlinarith

def ordinaryLength (m : ℕ) : ℕ := (1066550171*m+100000000-1)/100000000
def channelLength (m : ℕ) : ℕ := (1305956428*m+10000000000-1)/10000000000

theorem ceilingDiv_eq (n q : ℕ) (hq : 0 < q) :
    Nat.ceil ((n:ℝ)/(q:ℝ)) = n ⌈/⌉ q := by
  have hqR : (0:ℝ) < q := by exact_mod_cast hq
  apply eq_of_forall_ge_iff
  intro k
  rw [Nat.ceil_le, ceilDiv_le_iff_le_mul hq, div_le_iff₀ hqR]
  norm_cast
  exact Nat.mul_comm k q ▸ Iff.rfl

theorem ceilingMulDiv_eq (a m q : ℕ) (hq : 0 < q) :
    Nat.ceil ((a:ℝ)*m/q) = (a*m+q-1)/q := by
  rw [← Nat.cast_mul, ceilingDiv_eq _ q hq, Nat.ceilDiv_eq_add_pred_div]

theorem ordinaryLength_eq (m : ℕ) :
    ordinaryLength m = Nat.ceil (RealCertificate.c*(m:ℝ)) := by
  unfold ordinaryLength
  symm
  convert ceilingMulDiv_eq 1066550171 m 100000000 (by norm_num) using 1
  congr 1
  norm_num [RealCertificate.c]
  ring

theorem channelLength_eq (m : ℕ) :
    channelLength m = Nat.ceil (2*RealCertificate.theta*(m:ℝ)) := by
  unfold channelLength
  symm
  convert ceilingMulDiv_eq 1305956428 m 10000000000 (by norm_num) using 1
  congr 1
  norm_num [RealCertificate.theta]
  ring

def computedPool (n : ℕ) : Finset ℕ :=
  PrimePool.enumeratedCandidates (scale n) \ {3}

def reserve (n : ℕ) : ℕ := (computedPool n).card-factorCount

theorem computedPool_eq (n : ℕ) :
    computedPool n = CertificationParameters.pool (scale n) := rfl

/-- The decidable finite conditions are checked by the same total
parameter program for every input; there is no chosen asymptotic cutoff. -/
def Good (n U : ℕ) : Prop :=
  2 ≤ scale n ∧ 0 < reserve n ∧ 2*U.size ≤ reserve n ∧
    4*block n*U.size^factorCount ≤ (reserve n)^factorCount

instance (n U : ℕ) : Decidable (Good n U) := by
  unfold Good
  infer_instance

def finiteComputedParameters (n U : ℕ) (h : Good n U) :
    CompleteAPSP.Parameters (block n) U where
  pool := computedPool n
  P := scale n
  lam := U.size
  k := factorCount-1
  M := reserve n
  stages := (2*n).size
  prime _p hp := CertificationParameters.pool_prime (computedPool_eq n ▸ hp)
  lower _p hp := CertificationParameters.pool_lower (computedPool_eq n ▸ hp)
  P_pos := by have hh := h.1; omega
  power := CertificationParameters.magnitude_power _ _ h.1
  threshold := CertificationParameters.threshold_of_half _ _ h.2.1 h.2.2.1
  size := by
    have hM := h.2.1
    unfold reserve at hM ⊢
    have hR := CertificationParameters.reserve_size (scale n) factorCount (by
      rw [← computedPool_eq]
      omega)
    simpa only [← computedPool_eq] using hR
  rate := by
    have hr := CertificationParameters.rate_of_sufficient (block n) U.size (reserve n)
      factorCount (by norm_num [factorCount]) h.2.2.1 h.2.2.2
    simpa only [Nat.sub_add_cancel (show 1 ≤ factorCount by norm_num [factorCount])] using hr

/-- Executable parameter selection. A caller handles none by the direct
algorithm; some contains its fully checked finite configuration. -/
def program (n U : ℕ) : Option (CompleteAPSP.Parameters (block n) U) :=
  if h : Good n U then some (finiteComputedParameters n U h) else none

theorem program_isSome_iff (n U : ℕ) : (program n U).isSome = true ↔ Good n U := by
  unfold program
  split_ifs <;> simp_all

theorem program_sound (n U : ℕ) (p : CompleteAPSP.Parameters (block n) U)
    (hp : program n U = some p) :
    p.pool = computedPool n ∧ p.P = scale n ∧ p.lam = U.size ∧
      p.k = factorCount-1 ∧ p.M = reserve n ∧ p.stages = (2*n).size := by
  unfold program at hp
  split_ifs at hp with h
  · have heq : finiteComputedParameters n U h = p := Option.some.inj hp
    subst p
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem eventually_good (C κ : ℝ) (hC : 0 < C) :
    ∀ᶠ n : ℕ in atTop, ∀ U : ℕ, (U:ℝ) ≤ C*(n:ℝ)^κ → Good n U := by
  have hlo : ∀ᶠ n : ℕ in atTop,
      (1:ℝ)*(n:ℝ)^AsymptoticCosts.eta*(Real.log (n:ℝ))^4 ≤ (scale n:ℝ) := by
    filter_upwards [eventually_ge_atTop (3:ℕ)] with n hn
    simpa only [one_mul] using (scale_bounds n hn).1
  have hhi : ∀ᶠ n : ℕ in atTop,
      (scale n:ℝ) ≤ 512*(n:ℝ)^AsymptoticCosts.eta*(Real.log (n:ℝ))^4 := by
    filter_upwards [eventually_ge_atTop (3:ℕ)] with n hn
    exact (scale_bounds n hn).2
  have hh : ∀ᶠ n : ℕ in atTop, (block n:ℝ) ≤ 2*(n:ℝ)^AsymptoticCosts.b := by
    filter_upwards [eventually_ge_atTop (1:ℕ)] with n hn
    exact (block_bounds n hn).2
  have h := eventual_sufficient_scale scale block AsymptoticCosts.b AsymptoticCosts.eta
    C κ 1 512 factorCount hh (by norm_num [factorCount])
    (by norm_num [AsymptoticCosts.eta, AlignedCertificate.eta,
      AlignedCertificate.b, AlignedCertificate.R])
    (by norm_num [factorCount, AsymptoticCosts.eta, AsymptoticCosts.b,
      AlignedCertificate.eta, AlignedCertificate.b, AlignedCertificate.R])
    hC (by norm_num) (by norm_num) hlo hhi
  filter_upwards [h] with n hn
  intro U hU
  simpa only [Good, reserve, computedPool_eq] using hn U hU

/-- The one executable program succeeds eventually on every
polynomially bounded magnitude. This is stronger than a pointwise
existence statement for configurations. -/
theorem eventually_program_isSome (C κ : ℝ) (hC : 0 < C) :
    ∀ᶠ n : ℕ in atTop, ∀ U : ℕ, (U:ℝ) ≤ C*(n:ℝ)^κ →
      (program n U).isSome = true := by
  filter_upwards [eventually_good C κ hC] with n hn
  intro U hU
  exact (program_isSome_iff n U).mpr (hn U hU)

theorem block_compare_blockSize (n : ℕ) (hn : 1 ≤ n) :
    PhaseGeometry.blockSize n AsymptoticCosts.b ≤ block n ∧
      block n ≤ 2*PhaseGeometry.blockSize n AsymptoticCosts.b := by
  have hb := block_bounds n hn
  constructor
  · exact Nat.ceil_le.mpr hb.1
  · have hc : (n:ℝ)^AsymptoticCosts.b ≤
        (PhaseGeometry.blockSize n AsymptoticCosts.b:ℝ) := Nat.le_ceil _
    have h : (block n:ℝ) ≤ 2*(PhaseGeometry.blockSize n AsymptoticCosts.b:ℝ) := by
      linarith
    exact_mod_cast h

theorem block_le_n (n : ℕ) (hn : 2 ≤ n) : block n ≤ n := by
  unfold block roundedPower
  rw [rootScan_eq_nthRoot bNumerator bDenominator n
    (by norm_num [bDenominator]) (by norm_num [bNumerator, bDenominator]) (by omega)]
  have hp : n^bNumerator < n^bDenominator :=
    Nat.pow_lt_pow_right (by omega) (by norm_num [bNumerator, bDenominator])
  have hr := (Nat.nthRoot_lt_iff (show bDenominator ≠ 0 by norm_num [bDenominator])).mpr hp
  omega

theorem ordinaryLength_lower (m : ℕ) : m ≤ ordinaryLength m := by
  rw [ordinaryLength_eq]
  have hc : (1:ℝ) ≤ RealCertificate.c := by norm_num [RealCertificate.c]
  have h : (m:ℝ) ≤ (Nat.ceil (RealCertificate.c*(m:ℝ)):ℝ) := by
    calc
      (m:ℝ) ≤ RealCertificate.c*(m:ℝ) := by nlinarith
      _ ≤ _ := Nat.le_ceil _
  exact_mod_cast h

theorem channelLength_upper (m : ℕ) : channelLength m ≤ m := by
  unfold channelLength
  rw [← Nat.ceilDiv_eq_add_pred_div]
  apply (ceilDiv_le_iff_le_mul (show 0 < (10000000000:ℕ) by norm_num)).mpr
  nlinarith

/-- Literal fixed-degree multiplication loops used by the search tests. -/
def powerCounted (x : ℕ) : ℕ → ℕ × ℕ
  | 0 => (1, 0)
  | e+1 =>
      let previous := powerCounted x e
      (previous.1*x, previous.2+1)

theorem powerCounted_value (x e : ℕ) : (powerCounted x e).1 = x^e := by
  induction e with
  | zero => rfl
  | succ e ih => simp [powerCounted, ih, pow_succ]

theorem powerCounted_work (x e : ℕ) : (powerCounted x e).2 = e := by
  induction e with
  | zero => rfl
  | succ e ih => simp [powerCounted, ih]

def scanCounted (p q n : ℕ) : List ℕ → ℕ × ℕ
  | [] => (0, 0)
  | x :: xs =>
      let left := powerCounted x q
      let right := powerCounted n p
      let tail := scanCounted p q n xs
      (max (if left.1 ≤ right.1 then x else 0) tail.1,
        left.2+right.2+tail.2+2)

theorem scanCounted_value (p q n : ℕ) (xs : List ℕ) :
    (scanCounted p q n xs).1 =
      xs.toFinset.sup (fun x => if x^q ≤ n^p then x else 0) := by
  induction xs with
  | nil => simp [scanCounted]
  | cons x xs ih =>
      simp [scanCounted, powerCounted_value, List.toFinset_cons, Finset.sup_insert, ih]

theorem scanCounted_work (p q n : ℕ) (xs : List ℕ) :
    (scanCounted p q n xs).2 = xs.length*(p+q+2) := by
  induction xs with
  | nil => simp [scanCounted]
  | cons x xs ih =>
      simp [scanCounted, powerCounted_work, ih]
      ring

def rootProgram (p q n : ℕ) : ℕ × ℕ := scanCounted p q n (List.range (n+1))

theorem rootProgram_value (p q n : ℕ) : (rootProgram p q n).1 = rootScan p q n := by
  have hr : (List.range (n+1)).toFinset = Finset.range (n+1) := by
    ext x
    simp
  simp only [rootProgram, scanCounted_value, hr, rootScan]

theorem rootProgram_work (p q n : ℕ) :
    (rootProgram p q n).2 = rootSearchWork p q n := by
  simp [rootProgram, scanCounted_work, rootSearchWork]

/-- Every partial power register used in a search has polynomial
magnitude with an exponent fixed independently of n. -/
theorem root_power_register (p q n x e : ℕ) (hn : 1 ≤ n)
    (hx : x ≤ n) (he : e ≤ p+q+1) : x^e ≤ n^(p+q+1) := by
  exact (Nat.pow_le_pow_left hx e).trans (Nat.pow_le_pow_right hn he)

theorem root_register_bits (p q : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ z : ℕ, z ≤ n^(p+q+1) →
      (z.size:ℝ) ≤
        ((|((p+q+1:ℕ):ℝ)|)/Real.log 2+1)*Real.log (n:ℝ) := by
  have h := CertificationParameters.uniform_size_log 1 (p+q+1:ℕ) (by norm_num)
  filter_upwards [h] with n hn
  intro z hz
  have hzR : (z:ℝ) ≤ 1*(n:ℝ)^((p+q+1:ℕ):ℝ) := by
    simpa only [one_mul, Real.rpow_natCast, Nat.cast_pow] using
      (show (z:ℝ) ≤ (n^(p+q+1):ℕ) by exact_mod_cast hz)
  simpa using hn z hzR

/-- Even the simple linear search, with any fixed polylogarithmic
bit-arithmetic overhead, has setup cost below n squared eventually. -/
theorem rootSearchWork_eventually (p q K : ℕ) (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ n : ℕ in atTop,
      C*(Real.log (n:ℝ))^K*(rootSearchWork p q n:ℝ) ≤ (n:ℝ)^2 := by
  have hfit := AsymptoticCosts.eventualPowerFit (show (1:ℝ)<2 by norm_num)
    K (C*(2*(p+q+2:ℕ)))
  filter_upwards [hfit, eventually_ge_atTop (1:ℕ), eventually_ge_atTop (3:ℕ)] with
    n hfit hn hn3
  have hw : (rootSearchWork p q n:ℝ) ≤ (2*(p+q+2:ℕ):ℝ)*(n:ℝ) := by
    exact_mod_cast rootSearchWork_linear p q n hn
  have hlog := PhaseGeometry.one_le_log_nat n hn3
  calc
    _ ≤ C*(Real.log (n:ℝ))^K*((2*(p+q+2:ℕ):ℝ)*(n:ℝ)) :=
      mul_le_mul_of_nonneg_left hw (by positivity)
    _ = (C*(2*(p+q+2:ℕ)))*(Real.log (n:ℝ))^K*(n:ℝ) := by ring
    _ ≤ _ := by simpa using hfit

theorem computed_generationWork_eventually (C : ℝ) (K : ℕ) (hC : 0 ≤ C) :
    ∀ᶠ n : ℕ in atTop,
      C*(Real.log (n:ℝ))^K*
        (CertificationParameters.generationWork (scale n):ℝ) ≤ (n:ℝ) := by
  have hlo : ∀ᶠ n : ℕ in atTop,
      (1:ℝ)*(n:ℝ)^AsymptoticCosts.eta*(Real.log (n:ℝ))^4 ≤ (scale n:ℝ) := by
    filter_upwards [eventually_ge_atTop (3:ℕ)] with n hn
    simpa only [one_mul] using (scale_bounds n hn).1
  have hhi : ∀ᶠ n : ℕ in atTop,
      (scale n:ℝ) ≤ 512*(n:ℝ)^AsymptoticCosts.eta*(Real.log (n:ℝ))^4 := by
    filter_upwards [eventually_ge_atTop (3:ℕ)] with n hn
    exact (scale_bounds n hn).2
  simpa using generationWork_scale_eventually scale
    (by norm_num [AsymptoticCosts.eta, AlignedCertificate.eta,
      AlignedCertificate.b, AlignedCertificate.R])
    (by norm_num : (0:ℝ)<1) (by norm_num : (0:ℝ)<512) hlo hhi 1 C K hC
    (by norm_num [AsymptoticCosts.eta, AlignedCertificate.eta,
      AlignedCertificate.b, AlignedCertificate.R])

def setupWork (n : ℕ) : ℕ :=
  rootSearchWork bNumerator bDenominator n +
    rootSearchWork bNumerator (bDenominator*factorCount) n +
    CertificationParameters.generationWork (scale n) + (2*factorCount+16)

/-- Both literal root scans, the actual prime enumeration, and the
fixed number of parameter-condition power operations are charged
additively. Fixed polylogarithmic arithmetic overhead is harmless. -/
theorem setupWork_eventually (C : ℝ) (K : ℕ) (hC : 0 ≤ C) :
    ∀ᶠ n : ℕ in atTop,
      C*(Real.log (n:ℝ))^K*(setupWork n:ℝ) ≤ 4*(n:ℝ)^2 := by
  have h1 := rootSearchWork_eventually bNumerator bDenominator K C hC
  have h2 := rootSearchWork_eventually bNumerator (bDenominator*factorCount) K C hC
  have hp := computed_generationWork_eventually C K hC
  have hc := AsymptoticCosts.eventualPowerFit (show (0:ℝ)<2 by norm_num)
    K (C*(2*factorCount+16))
  filter_upwards [h1, h2, hp, hc, eventually_ge_atTop (1:ℕ)] with
    n h1n h2n hpn hcn hn
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hcn' : C*(Real.log (n:ℝ))^K*(2*factorCount+16:ℕ) ≤ (n:ℝ)^2 := by
    simpa [Real.rpow_zero, mul_comm, mul_left_comm, mul_assoc] using hcn
  unfold setupWork
  push_cast
  push_cast at hcn'
  have hnsq : (n:ℝ) ≤ (n:ℝ)^2 := by nlinarith [hnR]
  calc
    _ = C*(Real.log (n:ℝ))^K*(rootSearchWork bNumerator bDenominator n:ℝ) +
        C*(Real.log (n:ℝ))^K*(rootSearchWork bNumerator (bDenominator*factorCount) n:ℝ) +
        C*(Real.log (n:ℝ))^K*(generationWork (scale n):ℝ) +
        C*(Real.log (n:ℝ))^K*(2*(factorCount:ℝ)+16) := by ring
    _ ≤ (n:ℝ)^2+(n:ℝ)^2+(n:ℝ)^2+(n:ℝ)^2 :=
      add_le_add (add_le_add (add_le_add h1n h2n) (hpn.trans hnsq)) hcn'
    _ = _ := by ring

theorem apspCap_polynomial (degree n W : ℕ) (hn : 1 ≤ n) (hW : W ≤ n^degree) :
    192*n*W+40 ≤ 232*n^(degree+1) := by
  have hw := Nat.mul_le_mul_left (192*n) hW
  have hp : 1 ≤ n^(degree+1) := one_le_pow₀ hn
  rw [pow_succ] at hp ⊢
  nlinarith

/-- Uniform success for the actual adaptive APSP magnitude cap. The
same program and finite checks are used for every input weight table. -/
theorem eventually_program_apspCap (degree : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ W : ℕ, W ≤ n^degree →
      (program n (192*n*W+40)).isSome = true := by
  have h := eventually_program_isSome 232 (degree+1:ℕ) (by norm_num)
  filter_upwards [h, eventually_ge_atTop (1:ℕ)] with n hn hn1
  intro W hW
  apply hn (192*n*W+40)
  have hc := apspCap_polynomial degree n W hn1 hW
  exact_mod_cast hc

end ThinMatrix.ComputableParameters

#print axioms ThinMatrix.ComputableParameters.rootScan_eq_nthRoot
#print axioms ThinMatrix.ComputableParameters.roundedPower_bounds
#print axioms ThinMatrix.ComputableParameters.block_bounds
#print axioms ThinMatrix.ComputableParameters.scale_bounds
#print axioms ThinMatrix.ComputableParameters.ordinaryLength_eq
#print axioms ThinMatrix.ComputableParameters.channelLength_eq
#print axioms ThinMatrix.ComputableParameters.program_sound
#print axioms ThinMatrix.ComputableParameters.eventually_program_isSome
#print axioms ThinMatrix.ComputableParameters.rootProgram_value
#print axioms ThinMatrix.ComputableParameters.rootProgram_work
#print axioms ThinMatrix.ComputableParameters.rootSearchWork_eventually
#print axioms ThinMatrix.ComputableParameters.computed_generationWork_eventually
#print axioms ThinMatrix.ComputableParameters.setupWork_eventually
#print axioms ThinMatrix.ComputableParameters.eventually_program_apspCap
