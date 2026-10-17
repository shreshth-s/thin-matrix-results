import CompleteAPSP
import PhaseGeometry
import Mathlib.Data.Nat.Size
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic

/-!
# Nondegenerate finite composite-certification parameters

The candidate pool is the actual enumerated prime interval, with three
excluded.  Magnitude bounds and the two elementary rate inequalities are
proved separately from the certification algorithm.
-/
namespace ThinMatrix.CertificationParameters

open scoped BigOperators
open Filter Real
open PrimePool PhaseGeometry
noncomputable section

/-- The same trial-division enumeration as the algorithm, with the fixed
physical factor three omitted from its cyclic-prime candidates. -/
def pool (P : ℕ) : Finset ℕ := PrimePool.enumeratedCandidates P \ {3}

theorem pool_eq_available (P : ℕ) : pool P = PrimePool.available P {3} := by
  simp [pool, PrimePool.available, PrimePool.enumeratedCandidates_eq]

theorem pool_prime {P p : ℕ} (hp : p ∈ pool P) : Nat.Prime p := by
  rw [pool_eq_available] at hp
  exact PrimePool.available_prime hp

theorem pool_lower {P p : ℕ} (hp : p ∈ pool P) : P ≤ p := by
  rw [pool_eq_available] at hp
  exact PrimePool.available_lower hp

theorem pool_ne_three {P p : ℕ} (hp : p ∈ pool P) : p ≠ 3 := by
  have h := (Finset.mem_sdiff.mp hp).2
  simpa using h

/-- Reserving R primes leaves sufficient room for all R−1 selections. -/
theorem reserve_size (P R : ℕ) (hR : R ≤ (pool P).card) :
    (pool P).card - R + (R - 1) ≤ (pool P).card := by omega

/-- The finite sufficient rate conditions do not require taking roots or
normalizing a potentially enormous fixed power. -/
theorem rate_of_sufficient (h lam M R : ℕ) (hR : 0 < R)
    (hhalf : 2*lam ≤ M) (hpower : 4*h*lam^R ≤ M^R) :
    2*h*lam^R ≤ (M-lam)*M^(R-1) := by
  have hlinear : M ≤ 2*(M-lam) := by omega
  have hmul := Nat.mul_le_mul_right (M^(R-1)) hlinear
  have heq : M^R = M*M^(R-1) := by
    rw [← pow_succ']
    congr 1
    omega
  rw [← heq] at hmul
  nlinarith

theorem threshold_of_half (lam M : ℕ) (hM : 0 < M) (hhalf : 2*lam ≤ M) :
    lam < M := by omega

/-- Binary length supplies a genuine bound on the number of distinct
prime divisors of any nonzero integer of magnitude at most U. -/
theorem magnitude_power (P U : ℕ) (hP : 2 ≤ P) :
    U < P^(U.size+1) := by
  calc
    U < 2^U.size := Nat.lt_size_self U
    _ ≤ P^U.size := Nat.pow_le_pow_left hP _
    _ ≤ P^(U.size+1) := Nat.pow_le_pow_right (by omega) (by omega)

/-- A finite, fully constructed configuration from the two sufficient
inequalities. Its divisor premise follows from the actual input bound. -/
def finiteParameters (h U P R stages : ℕ) (hR : 0 < R) (hP : 2 ≤ P)
    (hM : 0 < (pool P).card-R)
    (hhalf : 2*U.size ≤ (pool P).card-R)
    (hrate : 4*h*U.size^R ≤ ((pool P).card-R)^R) :
    CompleteAPSP.Parameters h U where
  pool := pool P
  P := P
  lam := U.size
  k := R-1
  M := (pool P).card-R
  stages := stages
  prime _p hp := pool_prime hp
  lower _p hp := pool_lower hp
  P_pos := by omega
  power := magnitude_power P U hP
  threshold := threshold_of_half _ _ hM hhalf
  size := reserve_size P R (by omega)
  rate := by
    have h := rate_of_sufficient h U.size ((pool P).card-R) R hR hhalf hrate
    simpa only [Nat.sub_add_cancel (show 1 ≤ R by omega)] using h

theorem size_log2 (U : ℕ) (hU : U ≠ 0) : U.size = U.log2 + 1 := by
  apply Nat.le_antisymm
  · rw [Nat.size_le]
    exact (Nat.log2_lt hU).mp (by omega)
  · have hh : U.log2 < U.size := (Nat.log2_lt hU).mpr (Nat.lt_size_self U)
    omega

theorem size_le_log (U : ℕ) : (U.size : ℝ) ≤ Real.log U / Real.log 2 + 1 := by
  by_cases hU : U = 0
  · simp [hU]
  · rw [size_log2 U hU, Nat.cast_add, Nat.cast_one]
    simpa [Real.logb, add_comm] using add_le_add_right (Real.log2_le_logb U) 1

/-- A single threshold controls the binary lengths of every polynomially
bounded input magnitude, including zero. -/
theorem uniform_size_log (C κ : ℝ) (hC : 0 < C) :
    ∀ᶠ n : ℕ in atTop, ∀ U : ℕ, (U:ℝ) ≤ C*(n:ℝ)^κ →
      (U.size:ℝ) ≤ ((|Real.log C|+|κ|)/Real.log 2+1)*Real.log (n:ℝ) := by
  have hlog : ∀ᶠ n : ℕ in atTop, 1 ≤ Real.log (n:ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop 1)
  filter_upwards [hlog, eventually_ge_atTop 1] with n hn hn1
  intro U hU
  have hnpos : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL0 : 0 ≤ (|Real.log C|+|κ|)/Real.log 2+1 := by positivity
  by_cases hU0 : U=0
  · subst U
    simpa using mul_nonneg hL0 (le_trans (by norm_num : (0:ℝ) ≤ 1) hn)
  have hUp : 0 < U := Nat.pos_of_ne_zero hU0
  have hlogU := Real.log_le_log (by exact_mod_cast hUp : (0:ℝ) < U) hU
  rw [Real.log_mul (ne_of_gt hC) (ne_of_gt (Real.rpow_pos_of_pos hnpos κ)),
    Real.log_rpow hnpos κ] at hlogU
  have hlin : Real.log (U:ℝ) ≤ (|Real.log C|+|κ|)*Real.log (n:ℝ) := by
    have hCabs : Real.log C ≤ |Real.log C| := le_abs_self _
    have habsmul : |Real.log C| ≤ |Real.log C| * Real.log (n:ℝ) :=
      le_mul_of_one_le_right (abs_nonneg _) hn
    have hk := mul_le_mul_of_nonneg_right (le_abs_self κ)
      (le_trans (by norm_num : (0:ℝ) ≤ 1) hn)
    nlinarith
  have hdiv := div_le_div_of_nonneg_right hlin h2.le
  calc
    (U.size:ℝ) ≤ Real.log (U:ℝ)/Real.log 2+1 := size_le_log U
    _ ≤ ((|Real.log C|+|κ|)/Real.log 2)*Real.log (n:ℝ)+1 := by
      simpa only [div_mul_eq_mul_div, add_comm] using add_le_add_right hdiv 1
    _ ≤ ((|Real.log C|+|κ|)/Real.log 2+1)*Real.log (n:ℝ) := by nlinarith

theorem primeScale_log_upper (n : ℕ) (eta : ℝ)
    (hn : 3 ≤ n) (heta : 0 ≤ eta) :
    Real.log (primeScale n eta 4 : ℝ) ≤ (eta+5)*Real.log (n : ℝ) := by
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (show 0<n by omega)
  have hl1 := one_le_log_nat n hn
  have hlpos : 0 < Real.log (n : ℝ) := by linarith
  have hxpos : 0 < (n : ℝ)^eta := Real.rpow_pos_of_pos hnpos eta
  have hs := primeScale_bounds n eta 4 hn heta
  have h1 : 1 ≤ (n : ℝ)^eta * (Real.log (n : ℝ))^4 :=
    one_le_mul_of_one_le_of_one_le
      (Real.one_le_rpow (by exact_mod_cast (show 1≤n by omega)) heta)
      (one_le_pow₀ hl1)
  have hPpos : 0 < (primeScale n eta 4 : ℝ) := by linarith [hs.1]
  have hlog := Real.log_le_log hPpos hs.2
  rw [Real.log_mul (by norm_num : (2:ℝ) ≠ 0) (by positivity),
    Real.log_mul hxpos.ne' (by positivity), Real.log_rpow hnpos,
    Real.log_pow] at hlog
  have h2 : Real.log (2 : ℝ) ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    linarith
  have hll := Real.log_le_self hlpos.le
  norm_num only [Nat.cast_ofNat] at hlog
  nlinarith

theorem primeScale_tendsto {eta : ℝ} (heta : 0 < eta) :
    Tendsto (fun n : ℕ => primeScale n eta 4) atTop atTop := by
  apply (tendsto_natCast_atTop_iff (R := ℝ)).mp
  have hx := (tendsto_rpow_atTop heta).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  apply Filter.tendsto_atTop_mono' atTop _ hx
  filter_upwards [eventually_ge_atTop (3 : ℕ)] with n hn
  exact (prime_factor_bounds n eta 4 (primeScale n eta 4) hn heta.le
    ⟨le_rfl, by omega⟩).1

theorem eventual_pool_sub_lower {eta : ℝ} (heta : 0 < eta)
    (A : ℝ) (hA : 0 < A) (R : ℕ) (excluded : Finset ℕ) :
    ∀ᶠ n : ℕ in atTop,
      A*(n : ℝ)^eta*Real.log (n : ℝ) ≤
        (((PrimePool.available (primeScale n eta 4) excluded).card-R : ℕ) : ℝ) := by
  have ht := primeScale_tendsto heta
  have hx := (tendsto_rpow_atTop heta).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have hlog := Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have hp := ht.eventually (PrimePool.eventually_available_card_lower excluded)
  have hP2 := ht.eventually (eventually_ge_atTop (2 : ℕ))
  have hlarge := hlog.eventually
    (eventually_ge_atTop (16*(eta+5)*A))
  have hR := hx.eventually (eventually_ge_atTop ((R : ℝ)/A))
  filter_upwards [hp, hP2, hlarge, hR, eventually_ge_atTop (3 : ℕ)] with
    n hp hP2 hlarge hR hn
  dsimp only [Function.comp_apply] at hlarge hR
  have hl1 := one_le_log_nat n hn
  have hlpos : 0 < Real.log (n : ℝ) := by linarith
  have hx0 : 0 ≤ (n : ℝ)^eta := Real.rpow_nonneg (Nat.cast_nonneg n) eta
  have hL : 0 < eta+5 := by linarith
  have hPpos : 0 < Real.log (primeScale n eta 4 : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < primeScale n eta 4 by omega)
  have hT : 16*(eta+5)*A ≤ (Real.log (n : ℝ))^2 := by nlinarith
  have hlogBound := primeScale_log_upper n eta hn heta.le
  have hnum :
      (2*A*(n : ℝ)^eta*Real.log (n : ℝ))*
        (8*Real.log (primeScale n eta 4 : ℝ)) ≤
      (primeScale n eta 4 : ℝ) := by
    calc
      _ ≤ (2*A*(n : ℝ)^eta*Real.log (n : ℝ))*
          (8*(eta+5)*Real.log (n : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        nlinarith [hlogBound]
      _ = (16*(eta+5)*A)*((n : ℝ)^eta*(Real.log (n : ℝ))^2) := by ring
      _ ≤ (Real.log (n : ℝ))^2*((n : ℝ)^eta*(Real.log (n : ℝ))^2) :=
        mul_le_mul_of_nonneg_right hT (by positivity)
      _ = (n : ℝ)^eta*(Real.log (n : ℝ))^4 := by ring
      _ ≤ (primeScale n eta 4 : ℝ) := (primeScale_bounds n eta 4 hn heta.le).1
  have hcard : 2*A*(n : ℝ)^eta*Real.log (n : ℝ) ≤
      ((PrimePool.available (primeScale n eta 4) excluded).card : ℝ) :=
    ((le_div_iff₀ (by positivity : 0 < 8*Real.log (primeScale n eta 4 : ℝ))).mpr
      hnum).trans hp
  have hR' : (R : ℝ) ≤ A*(n : ℝ)^eta*Real.log (n : ℝ) := by
    have hRA : (R : ℝ) ≤ (n : ℝ)^eta*A := (div_le_iff₀ hA).mp hR
    calc
      (R : ℝ) ≤ (n : ℝ)^eta*A := hRA
      _ ≤ ((n : ℝ)^eta*A)*Real.log (n : ℝ) :=
        le_mul_of_one_le_right (by positivity) hl1
      _ = _ := by ring
  have hRcard : R ≤ (PrimePool.available (primeScale n eta 4) excluded).card := by
    exact_mod_cast (show (R : ℝ) ≤
      ((PrimePool.available (primeScale n eta 4) excluded).card : ℝ) by
        nlinarith [mul_nonneg hA.le hx0])
  rw [Nat.cast_sub hRcard]
  linarith


/-- The actual rounded scale and polynomial magnitude bound imply every
finite condition, uniformly in the magnitude U. No pool-size or rate
premise is supplied by the caller. -/
theorem eventual_sufficient (b eta C κ : ℝ) (R : ℕ)
    (hR : 0 < R) (heta : 0 < eta) (hbalance : (R:ℝ)*eta=b) (hC : 0 < C) :
    ∀ᶠ n : ℕ in atTop, ∀ U : ℕ, (U:ℝ) ≤ C*(n:ℝ)^κ →
      2 ≤ primeScale n eta 4 ∧
      0 < (pool (primeScale n eta 4)).card-R ∧
      2*U.size ≤ (pool (primeScale n eta 4)).card-R ∧
      4*blockSize n b*U.size^R ≤ ((pool (primeScale n eta 4)).card-R)^R := by
  let L := (|Real.log C|+|κ|)/Real.log 2+1
  let A := 8*(L+1)
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hA : 0 < A := by dsimp [A]; linarith
  have hpool := eventual_pool_sub_lower heta A hA R {3}
  have hsize := uniform_size_log C κ hC
  have hP := (primeScale_tendsto heta).eventually (eventually_ge_atTop (2:ℕ))
  filter_upwards [hpool, hsize, hP, eventually_ge_atTop (3:ℕ)] with
    n hpooln hsizen hPn hn
  intro U hU
  have hn1 : 1 ≤ n := by omega
  have hna : 1 ≤ (n:ℝ)^eta := Real.one_le_rpow (by exact_mod_cast hn1) heta.le
  have hlog := one_le_log_nat n hn
  have hlu : (U.size:ℝ)+1 ≤ (L+1)*Real.log (n:ℝ) := by
    have h := hsizen U hU
    change (U.size:ℝ) ≤ L*Real.log (n:ℝ) at h
    nlinarith
  have hrel : 8*(n:ℝ)^eta*((U.size:ℝ)+1) ≤
      (((pool (primeScale n eta 4)).card-R:ℕ):ℝ) := by
    rw [pool_eq_available]
    have h := mul_le_mul_of_nonneg_left hlu
      (show 0 ≤ 8*(n:ℝ)^eta by positivity)
    dsimp [A] at hpooln
    nlinarith
  have hsmall : 8*((U.size:ℝ)+1) ≤
      (((pool (primeScale n eta 4)).card-R:ℕ):ℝ) := by
    have h := mul_le_mul_of_nonneg_left hna
      (show 0 ≤ 8*((U.size:ℝ)+1) by positivity)
    nlinarith
  have hM : 0 < (pool (primeScale n eta 4)).card-R := by
    have h : (0:ℝ) < (((pool (primeScale n eta 4)).card-R:ℕ):ℝ) := by
      nlinarith
    exact_mod_cast h
  have hhalf : 2*U.size ≤ (pool (primeScale n eta 4)).card-R := by
    have h : (2:ℝ)*(U.size:ℝ) ≤
        (((pool (primeScale n eta 4)).card-R:ℕ):ℝ) := by nlinarith
    exact_mod_cast h
  have hRreal : (0:ℝ) < R := by exact_mod_cast hR
  have hb : 0 ≤ b := by nlinarith
  have hblock := (blockSize_bounds n b hn1 hb).2
  have hpow : (8*(n:ℝ)^eta*(U.size:ℝ))^R ≤
      ((((pool (primeScale n eta 4)).card-R:ℕ):ℝ))^R := by
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
  have hrate : 4*blockSize n b*U.size^R ≤
      ((pool (primeScale n eta 4)).card-R)^R := by
    have hreal : (4:ℝ)*(blockSize n b:ℝ)*(U.size:ℝ)^R ≤
        ((((pool (primeScale n eta 4)).card-R:ℕ):ℝ))^R := by
      calc
        (4:ℝ)*(blockSize n b:ℝ)*(U.size:ℝ)^R
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

/-- The eventual configuration exposes the actual pool and all selected
parameters. Its only asymptotic input is a polynomial magnitude bound. -/
theorem eventual_configuration_at (b eta C κ : ℝ) (R : ℕ)
    (hR : 0 < R) (heta : 0 < eta) (hbalance : (R:ℝ)*eta=b) (hC : 0 < C)
    (stages : ℕ → ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ U : ℕ, (U:ℝ) ≤ C*(n:ℝ)^κ →
      ∃ p : CompleteAPSP.Parameters (blockSize n b) U,
        p.pool = pool (primeScale n eta 4) ∧ p.P = primeScale n eta 4 ∧
        p.lam = U.size ∧ p.k = R-1 ∧
        p.M = (pool (primeScale n eta 4)).card-R ∧ p.stages = stages n := by
  filter_upwards [eventual_sufficient b eta C κ R hR heta hbalance hC] with n hn
  intro U hU
  rcases hn U hU with ⟨hP, hM, hhalf, hrate⟩
  exact ⟨finiteParameters (blockSize n b) U (primeScale n eta 4) R (stages n)
    hR hP hM hhalf hrate, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem eventual_configuration (b C κ : ℝ) (R : ℕ)
    (hb : 0 < b) (hR : 0 < R) (hC : 0 < C) (stages : ℕ → ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ U : ℕ, (U:ℝ) ≤ C*(n:ℝ)^κ →
      ∃ p : CompleteAPSP.Parameters (blockSize n b) U,
        p.pool = pool (primeScale n (b/(R:ℝ)) 4) ∧ p.P = primeScale n (b/(R:ℝ)) 4 ∧
        p.lam = U.size ∧ p.k = R-1 ∧
        p.M = (pool (primeScale n (b/(R:ℝ)) 4)).card-R ∧ p.stages = stages n := by
  have hRreal : (0:ℝ) < R := by exact_mod_cast hR
  apply eventual_configuration_at b (b/(R:ℝ)) C κ R hR (div_pos hb hRreal) _ hC stages
  field_simp

/-- The R=10^9 aligned-cache witness is instantiated without expanding
any R-th power. All threshold, pool-size and rate conditions are derived. -/
theorem aligned_eventual_configuration (C κ : ℝ) (hC : 0 < C) (stages : ℕ → ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ U : ℕ, (U:ℝ) ≤ C*(n:ℝ)^κ →
      ∃ p : CompleteAPSP.Parameters (blockSize n AsymptoticCosts.b) U,
        p.pool = pool (primeScale n AsymptoticCosts.eta 4) ∧
        p.P = primeScale n AsymptoticCosts.eta 4 ∧ p.lam = U.size ∧
        p.k = AlignedCertificate.R-1 ∧
        p.M = (pool (primeScale n AsymptoticCosts.eta 4)).card-AlignedCertificate.R ∧
        p.stages = stages n := by
  apply eventual_configuration_at AsymptoticCosts.b AsymptoticCosts.eta C κ
    AlignedCertificate.R _ _ _ hC stages
  · norm_num [AlignedCertificate.R]
  · norm_num [AsymptoticCosts.eta, AlignedCertificate.eta,
      AlignedCertificate.b, AlignedCertificate.R]
  · norm_num [AsymptoticCosts.eta, AsymptoticCosts.b, AlignedCertificate.eta,
      AlignedCertificate.b, AlignedCertificate.R]

/-- Any constructed configuration gives the actual finite divisor bound
for its original integer sums; no divisor-count oracle is assumed. -/
theorem parameters_divisorBound {X V : Type*} {h U : ℕ}
    (p : CompleteAPSP.Parameters h U) (A : CompositeCertification.Instance X V)
    (hmag : ∀ x v, v ∈ A.block x → (A.value x v).natAbs ≤ U) :
    A.DivisorBound p.pool p.lam :=
  A.divisorBound_of_prime_power p.pool p.P U p.lam p.prime p.lower
    p.P_pos hmag p.power

/-- A finite upper charge for the literal trial-division and range loops. -/
def generationWork (P : ℕ) : ℕ :=
  (∑ p ∈ Finset.range (8*P), p) + 8*P

theorem generationWork_le (P : ℕ) (hP : 1 ≤ P) :
    (generationWork P:ℝ) ≤ 72*(P:ℝ)^2 := by
  have ht : ((∑ p ∈ Finset.range (8*P), p:ℕ):ℝ) ≤ 64*(P:ℝ)^2 := by
    exact_mod_cast PrimePool.trialDivisionWork_le P
  have hP' : 1 ≤ (P:ℝ) := by exact_mod_cast hP
  have hsq : (P:ℝ) ≤ (P:ℝ)^2 := by nlinarith
  dsimp [generationWork]
  push_cast at ht ⊢
  nlinarith

theorem primeScale_generationWork_le (n : ℕ) (eta : ℝ) (K : ℕ)
    (hn : 3 ≤ n) (heta : 0 ≤ eta) :
    (Real.log (n:ℝ))^K*(generationWork (primeScale n eta 4):ℝ) ≤
      288*(Real.log (n:ℝ))^(K+8)*(n:ℝ)^(2*eta) := by
  have hl := one_le_log_nat n hn
  have hna : 1 ≤ (n:ℝ)^eta :=
    Real.one_le_rpow (by exact_mod_cast (show 1≤n by omega)) heta
  have hscale1 : 1 ≤ (n:ℝ)^eta*(Real.log (n:ℝ))^4 :=
    one_le_mul_of_one_le_of_one_le hna (one_le_pow₀ hl)
  have hs := primeScale_bounds n eta 4 hn heta
  have hP : 1 ≤ primeScale n eta 4 := by exact_mod_cast hscale1.trans hs.1
  have hpow : ((n:ℝ)^eta)^2 = (n:ℝ)^(2*eta) := by
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg n)]
    congr 1
    ring
  have hw : (generationWork (primeScale n eta 4):ℝ) ≤
      288*(Real.log (n:ℝ))^8*(n:ℝ)^(2*eta) := by
    calc
      (generationWork (primeScale n eta 4):ℝ)
          ≤ 72*(primeScale n eta 4:ℝ)^2 := generationWork_le _ hP
      _ ≤ 72*(2*((n:ℝ)^eta*(Real.log (n:ℝ))^4))^2 := by
        gcongr
        exact hs.2
      _ = _ := by
        rw [mul_pow, mul_pow, ← pow_mul, hpow]
        ring
  calc
    (Real.log (n:ℝ))^K*(generationWork (primeScale n eta 4):ℝ)
        ≤ (Real.log (n:ℝ))^K*
          (288*(Real.log (n:ℝ))^8*(n:ℝ)^(2*eta)) :=
      mul_le_mul_of_nonneg_left hw (pow_nonneg (by linarith) _)
    _ = _ := by rw [pow_add]; ring

/-- Any fixed polylogarithmic charge for the exact divisibility tests
fits additively below a power exponent strictly larger than 2 eta. -/
theorem primeScale_generationWork_eventually (eta d C : ℝ) (K : ℕ)
    (heta : 0 ≤ eta) (hC : 0 ≤ C) (hgap : 2*eta < d) :
    ∀ᶠ n : ℕ in atTop,
      C*(Real.log (n:ℝ))^K*(generationWork (primeScale n eta 4):ℝ) ≤ (n:ℝ)^d := by
  have hfit := AsymptoticCosts.eventualPowerFit hgap (K+8) (C*288)
  filter_upwards [eventually_ge_atTop (3:ℕ), hfit] with n hn hfitn
  calc
    C*(Real.log (n:ℝ))^K*(generationWork (primeScale n eta 4):ℝ)
        = C*((Real.log (n:ℝ))^K*(generationWork (primeScale n eta 4):ℝ)) := by ring
    _ ≤ C*(288*(Real.log (n:ℝ))^(K+8)*(n:ℝ)^(2*eta)) :=
      mul_le_mul_of_nonneg_left (primeScale_generationWork_le n eta K hn heta) hC
    _ = (C*288)*(Real.log (n:ℝ))^(K+8)*(n:ℝ)^(2*eta) := by ring
    _ ≤ _ := hfitn

theorem aligned_generationWork_eventually (C : ℝ) (K : ℕ) (hC : 0 ≤ C) :
    ∀ᶠ n : ℕ in atTop,
      C*(Real.log (n:ℝ))^K*
        (generationWork (primeScale n AsymptoticCosts.eta 4):ℝ) ≤ (n:ℝ) := by
  simpa using primeScale_generationWork_eventually AsymptoticCosts.eta 1 C K
    (by norm_num [AsymptoticCosts.eta, AlignedCertificate.eta,
      AlignedCertificate.b, AlignedCertificate.R]) hC
    (by norm_num [AsymptoticCosts.eta, AlignedCertificate.eta,
      AlignedCertificate.b, AlignedCertificate.R])

end
end ThinMatrix.CertificationParameters

#print axioms ThinMatrix.CertificationParameters.rate_of_sufficient
#print axioms ThinMatrix.CertificationParameters.magnitude_power
#print axioms ThinMatrix.CertificationParameters.finiteParameters
#print axioms ThinMatrix.CertificationParameters.eventual_sufficient
#print axioms ThinMatrix.CertificationParameters.aligned_eventual_configuration
#print axioms ThinMatrix.CertificationParameters.parameters_divisorBound
#print axioms ThinMatrix.CertificationParameters.aligned_generationWork_eventually
