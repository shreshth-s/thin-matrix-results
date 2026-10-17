import ComputableParameters
import PhaseGeometry

/-!
# Geometry of the executable integer parameters

The actual prime interval is based on ComputableParameters.scale.
Its upper endpoint may be 512 times the former rounded interval.
Every upper bound below therefore carries the enlarged fixed overhead.
-/
namespace ThinMatrix.ComputedPhaseGeometry

open scoped BigOperators
open Filter Real
open AsymptoticCosts
open PhaseGeometry

abbrev Call (R n : ℕ) := PhaseGeometry.PhaseCall R (ComputableParameters.scale n)

noncomputable def phaseOverhead (R n : ℕ) : ℝ :=
  (8192:ℝ)^R*(Real.log (n:ℝ))^(4*R)

theorem phaseOverhead_ge_one (R n : ℕ) (hn : 3 ≤ n) : 1 ≤ phaseOverhead R n := by
  exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num))
    (one_le_pow₀ (PhaseGeometry.one_le_log_nat n hn))

theorem block_pos (n : ℕ) : 0 < ComputableParameters.block n := by
  change 0 < ComputableParameters.rootScan _ _ n+1
  omega

def blockCount (n : ℕ) : ℕ := n ⌈/⌉ ComputableParameters.block n
def queryCount (n : ℕ) : ℕ := n^2*blockCount n

theorem n_div_block_le_rpow (n : ℕ) (hn : 1 ≤ n) :
    (n:ℝ)/(ComputableParameters.block n:ℝ) ≤ (n:ℝ)^(1-b) := by
  have hn0 : 0 < (n:ℝ) := by exact_mod_cast (show 0<n by omega)
  calc
    (n:ℝ)/(ComputableParameters.block n:ℝ) ≤ (n:ℝ)/(n:ℝ)^b :=
      div_le_div_of_nonneg_left hn0.le (Real.rpow_pos_of_pos hn0 b)
        (ComputableParameters.block_bounds n hn).1
    _ = _ := by rw [Real.rpow_sub hn0, Real.rpow_one]

theorem blockCount_upper (n : ℕ) (hn : 2 ≤ n) :
    (blockCount n:ℝ) ≤ 2*(n:ℝ)^(1-b) := by
  calc
    (blockCount n:ℝ) ≤ 2*(n:ℝ)/(ComputableParameters.block n:ℝ) :=
      PhaseGeometry.ceilDiv_cast_le_two_mul_div n (ComputableParameters.block n)
        (block_pos n) (ComputableParameters.block_le_n n hn)
    _ = 2*((n:ℝ)/(ComputableParameters.block n:ℝ)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (n_div_block_le_rpow n (by omega)) (by norm_num)

theorem queryCount_upper (n : ℕ) (hn : 2 ≤ n) :
    (queryCount n:ℝ) ≤ 2*(n:ℝ)^(3-b) := by
  unfold queryCount
  push_cast
  calc
    (n:ℝ)^2*(blockCount n:ℝ) ≤ (n:ℝ)^2*(2*(n:ℝ)^(1-b)) :=
      mul_le_mul_of_nonneg_left (blockCount_upper n hn) (sq_nonneg _)
    _ = 2*((n:ℝ)^2*(n:ℝ)^(1-b)) := by ring
    _ = _ := by rw [PhaseGeometry.pair_times_block_exponent n b (by omega)]

theorem candidate_count_le (n : ℕ) :
    (PrimePool.candidates (ComputableParameters.scale n)).card ≤
      8*ComputableParameters.scale n :=
  PhaseGeometry.candidate_count_le _

theorem actual_candidate_count (n : ℕ) (hn : 3 ≤ n) :
    ((PrimePool.candidates (ComputableParameters.scale n)).card:ℝ) ≤
      8192*(Real.log (n:ℝ))^4*(n:ℝ)^eta := by
  have hs := (ComputableParameters.scale_bounds n hn).2
  have hc : ((PrimePool.candidates (ComputableParameters.scale n)).card:ℝ) ≤
      8*(ComputableParameters.scale n:ℝ) := by exact_mod_cast candidate_count_le n
  nlinarith [mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) eta)
    (pow_nonneg (show 0 ≤ Real.log (n:ℝ) by linarith [one_le_log_nat n hn]) 4)]

theorem computedPool_subset_candidates (n : ℕ) :
    ComputableParameters.computedPool n ⊆
      PrimePool.candidates (ComputableParameters.scale n) := by
  intro p hp
  have h := (Finset.mem_sdiff.mp hp).1
  simpa only [PrimePool.enumeratedCandidates_eq] using h

theorem actual_pool_count (n : ℕ) (hn : 3 ≤ n) :
    ((ComputableParameters.computedPool n).card:ℝ) ≤
      8192*(Real.log (n:ℝ))^4*(n:ℝ)^eta := by
  have h : ((ComputableParameters.computedPool n).card:ℝ) ≤
      ((PrimePool.candidates (ComputableParameters.scale n)).card:ℝ) := by
    exact_mod_cast Finset.card_le_card (computedPool_subset_candidates n)
  exact h.trans (actual_candidate_count n hn)

/-- A concrete candidate list from the executable pool supplies a genuine
phase call at the computed interval, rather than the former interval. -/
def phaseCallOfPool (R n : ℕ) (factors : List ℕ) (hlen : factors.length ≤ R)
    (hvalid : ∀ p ∈ factors, p ∈ ComputableParameters.computedPool n) : Call R n where
  factors := factors
  length_le := hlen
  valid p hp := computedPool_subset_candidates n (hvalid p hp)

def candidateCallOfPool (R n : ℕ) (selected : List ℕ) (hlen : selected.length < R)
    (hvalid : ∀ p ∈ selected, p ∈ ComputableParameters.computedPool n)
    (p : ℕ) (hp : p ∈ ComputableParameters.computedPool n) : Call R n where
  factors := selected++[p]
  length_le := by simp only [List.length_append, List.length_singleton]; omega
  valid q hq := by
    rcases List.mem_append.mp hq with hq | hq
    · exact computedPool_subset_candidates n (hvalid q hq)
    · simpa only [List.mem_singleton.mp hq] using computedPool_subset_candidates n hp

theorem factor_bounds (n p : ℕ) (hn : 3 ≤ n)
    (hp : ComputableParameters.scale n ≤ p ∧ p ≤ 8*ComputableParameters.scale n) :
    (n : ℝ)^eta ≤ (p : ℝ) ∧
      (p : ℝ) ≤ 8192*((n : ℝ)^eta * (Real.log (n : ℝ))^4) := by
  have hs := ComputableParameters.scale_bounds n hn
  have hn0 : 0 ≤ (n : ℝ)^eta := Real.rpow_nonneg (Nat.cast_nonneg n) eta
  have hl : 1 ≤ (Real.log (n : ℝ))^4 := one_le_pow₀ (one_le_log_nat n hn)
  have hP : (ComputableParameters.scale n : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.1
  have hp8 : (p : ℝ) ≤ 8*(ComputableParameters.scale n : ℝ) := by exact_mod_cast hp.2
  constructor
  · exact (show (n : ℝ)^eta ≤ (n : ℝ)^eta * (Real.log (n : ℝ))^4 by
      simpa using mul_le_mul_of_nonneg_left hl hn0).trans (hs.1.trans hP)
  · nlinarith [mul_nonneg hn0 (pow_nonneg (by linarith [one_le_log_nat n hn]) 4)]

theorem productScale_uniform (n j R d : ℕ) (hn : 3 ≤ n) (hj : j ≤ R)
    (hd : (ComputableParameters.scale n)^j ≤ d ∧
      d ≤ (8*ComputableParameters.scale n)^j) :
    (n : ℝ)^((j : ℝ)*eta) ≤ (d : ℝ) ∧
      (d : ℝ) ≤ phaseOverhead R n * (n : ℝ)^((j : ℝ)*eta) := by
  have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hP : ComputableParameters.scale n ≤ ComputableParameters.scale n ∧
      ComputableParameters.scale n ≤ 8*ComputableParameters.scale n := ⟨le_rfl, by omega⟩
  have hs := factor_bounds n (ComputableParameters.scale n) hn hP
  have hdR : (ComputableParameters.scale n : ℝ)^j ≤ (d : ℝ) ∧
      (d : ℝ) ≤ (8*(ComputableParameters.scale n : ℝ))^j := by exact_mod_cast hd
  have hlo : ((n : ℝ)^eta)^j ≤ (ComputableParameters.scale n : ℝ)^j := by
    gcongr
    exact hs.1
  have h8 : 8*(ComputableParameters.scale n : ℝ) ≤
      8192*((n : ℝ)^eta * (Real.log (n : ℝ))^4) := by
    have hscale := (ComputableParameters.scale_bounds n hn).2
    have hx := Real.rpow_nonneg (Nat.cast_nonneg n) eta
    have hl : 0 ≤ (Real.log (n : ℝ))^4 := by positivity
    nlinarith [mul_nonneg hx hl]
  have hhi : (8*(ComputableParameters.scale n : ℝ))^j ≤
      (8192*((n : ℝ)^eta * (Real.log (n : ℝ))^4))^j := by gcongr
  have he : (n : ℝ)^((j : ℝ)*eta) = ((n : ℝ)^eta)^j := by
    rw [mul_comm, Real.rpow_mul_natCast hn0 eta j]
  have hc : (8192 : ℝ)^j ≤ (8192 : ℝ)^R := pow_le_pow_right₀ (by norm_num) hj
  have hlog : (Real.log (n : ℝ))^(4*j) ≤ (Real.log (n : ℝ))^(4*R) :=
    pow_le_pow_right₀ (one_le_log_nat n hn) (Nat.mul_le_mul_left 4 hj)
  constructor
  · rw [he]
    exact hlo.trans hdR.1
  · calc
      (d : ℝ) ≤ (8*(ComputableParameters.scale n : ℝ))^j := hdR.2
      _ ≤ (8192*((n : ℝ)^eta * (Real.log (n : ℝ))^4))^j := hhi
      _ = (8192 : ℝ)^j * (Real.log (n : ℝ))^(4*j) *
          (n : ℝ)^((j : ℝ)*eta) := by
        rw [he, mul_pow, mul_pow, pow_mul]
        ring
      _ ≤ phaseOverhead R n * (n : ℝ)^((j : ℝ)*eta) := by
        unfold phaseOverhead
        gcongr

theorem actual_list_product_bounds (R n : ℕ) (factors : List ℕ)
    (hn : 3 ≤ n) (hj : factors.length ≤ R)
    (hp : FactorBounds (ComputableParameters.scale n) factors) :
    (n : ℝ)^((factors.length : ℝ)*eta) ≤ (factors.prod : ℝ) ∧
      (factors.prod : ℝ) ≤ phaseOverhead R n *
        (n : ℝ)^((factors.length : ℝ)*eta) := by
  exact productScale_uniform n factors.length R factors.prod hn hj
    (list_product_bounds hp)

theorem actual_folded_bounds (R S n : ℕ) (hn : 3 ≤ n)
    (call : PhaseCall R (ComputableParameters.scale n)) :
    (n : ℝ)^(foldExponent S call.factors.length) ≤ (call.folded S : ℝ) ∧
      (call.folded S : ℝ) ≤ phaseOverhead R n *
        (n : ℝ)^(foldExponent S call.factors.length) := by
  exact productScale_uniform n (min S call.factors.length) R (call.folded S) hn
    ((Nat.min_le_right _ _).trans call.length_le) (call.folded_bounds S)

theorem actual_cyclic_bounds (R S n : ℕ) (hn : 3 ≤ n)
    (call : PhaseCall R (ComputableParameters.scale n)) :
    (n : ℝ)^(ringExponent S call.factors.length) ≤ (call.cyclic S : ℝ) ∧
      (call.cyclic S : ℝ) ≤ phaseOverhead R n *
        (n : ℝ)^(ringExponent S call.factors.length) := by
  exact productScale_uniform n (call.factors.length-S) R (call.cyclic S) hn
    ((Nat.sub_le _ _).trans call.length_le) (call.cyclic_bounds S)

theorem actual_physicalFold_bounds (R S n : ℕ) (hn : 3 ≤ n)
    (call : PhaseCall R (ComputableParameters.scale n)) :
    (n : ℝ)^(foldExponent S call.factors.length) ≤ (physicalFold call S : ℝ) ∧
      (physicalFold call S : ℝ) ≤ 3*phaseOverhead R n *
        (n : ℝ)^(foldExponent S call.factors.length) := by
  have hd := actual_folded_bounds R S n hn call
  have hd0 : 0 ≤ (call.folded S : ℝ) := Nat.cast_nonneg _
  dsimp [physicalFold]
  push_cast
  constructor <;> nlinarith

theorem actual_composite_bounds (R S n : ℕ) (hn : 3 ≤ n)
    (call : PhaseCall R (ComputableParameters.scale n)) :
    (n : ℝ)^((call.factors.length : ℝ)*eta) ≤
        (3*call.folded S*call.cyclic S : ℕ) ∧
      ((3*call.folded S*call.cyclic S : ℕ) : ℝ) ≤
        3*phaseOverhead R n * (n : ℝ)^((call.factors.length : ℝ)*eta) := by
  have hd := actual_list_product_bounds R n call.factors hn call.length_le call.interval
  have hd0 : 0 ≤ (call.factors.prod : ℝ) := Nat.cast_nonneg _
  rw [mul_assoc, call.split]
  simp only [Nat.cast_mul, Nat.cast_ofNat]
  constructor <;> nlinarith



def innerPower (n : ℕ) {R P : ℕ} (call : PhaseCall R P) (S : ℕ) : ℕ :=
  Nat.clog 4 (ComputableParameters.block n*physicalFold call S)

def innerDimension (n : ℕ) {R P : ℕ} (call : PhaseCall R P) (S : ℕ) : ℕ :=
  4^(innerPower n call S)

theorem innerDimension_eq_power (n : ℕ) {R P : ℕ} (call : PhaseCall R P) (S : ℕ) :
    innerDimension n call S = 4^(innerPower n call S) := rfl

theorem actual_inner_bounds (R S n : ℕ) (hn : 3 ≤ n)
    (call : PhaseCall R (ComputableParameters.scale n)) :
    (n:ℝ)^(b+foldExponent S call.factors.length) ≤ (innerDimension n call S:ℝ) ∧
      (innerDimension n call S:ℝ) ≤
        (24*(8192:ℝ)^R)*(Real.log (n:ℝ))^(4*R) *
          (n:ℝ)^(b+foldExponent S call.factors.length) := by
  have hh := ComputableParameters.block_bounds n (by omega)
  have hd := actual_folded_bounds R S n hn call
  have hnpos : 0 < (n:ℝ) := by exact_mod_cast (show 0<n by omega)
  have hhp : 0 < ComputableParameters.block n := by
    have h := (Real.rpow_pos_of_pos hnpos b).trans_le hh.1
    exact_mod_cast h
  have hdp : 0 < call.folded S := by
    have h := (Real.rpow_pos_of_pos hnpos _).trans_le hd.1
    exact_mod_cast h
  have hp := pad4_bounds (ComputableParameters.block n * (3*call.folded S)) (by positivity)
  have hpR : (ComputableParameters.block n:ℝ)*(3*(call.folded S:ℝ)) ≤ (innerDimension n call S:ℝ) ∧
      (innerDimension n call S:ℝ) ≤ 4*((ComputableParameters.block n:ℝ)*(3*(call.folded S:ℝ))) := by
    exact_mod_cast hp
  rw [Real.rpow_add hnpos]
  constructor
  · calc
      (n:ℝ)^b * (n:ℝ)^(foldExponent S call.factors.length) ≤
          (ComputableParameters.block n:ℝ)*(call.folded S:ℝ) := by gcongr; exact hh.1; exact hd.1
      _ ≤ (innerDimension n call S:ℝ) := by nlinarith [hpR.1]
  · calc
      (innerDimension n call S:ℝ) ≤ 4*((ComputableParameters.block n:ℝ)*(3*(call.folded S:ℝ))) := hpR.2
      _ ≤ 4*((2*(n:ℝ)^b)*(3*(phaseOverhead R n*(n:ℝ)^(foldExponent S call.factors.length)))) := by
        gcongr; exact hh.2; exact hd.2
      _ = _ := by unfold phaseOverhead; ring

theorem all_computed_candidate_tiles_fit_real :
    ∀ᶠ n : ℕ in atTop,
      ∀ call : PhaseCall AlignedCertificate.R (ComputableParameters.scale n),
        (Nat.ceil (RealCertificate.c*(innerPower n call AlignedCertificate.S:ℝ))).choose
            (innerPower n call AlignedCertificate.S) *
          4^(Nat.ceil (RealCertificate.c*(innerPower n call AlignedCertificate.S:ℝ)) -
            innerPower n call AlignedCertificate.S) ≤ outerSize call AlignedCertificate.S n := by
  let C : ℝ := 24*(8192:ℝ)^AlignedCertificate.R
  have hfit : ∀ᶠ n : ℕ in atTop, ∀ j : Fin (AlignedCertificate.R+1), ∀ m d : ℕ,
      (4:ℝ)^m ≤ C*(Real.log (n:ℝ))^(4*AlignedCertificate.R)*
        (n:ℝ)^(b+foldExponent AlignedCertificate.S j.val) →
      (n:ℝ)^(foldExponent AlignedCertificate.S j.val) ≤ (d:ℝ) →
      (Nat.ceil (RealCertificate.c*(m:ℝ))).choose m *
        4^(Nat.ceil (RealCertificate.c*(m:ℝ))-m) ≤ n*FoldedCounts.foldWidth d := by
    apply Filter.eventually_all.mpr
    intro j
    exact alignedScalarGridFitsUniformlyEventually
      (foldExponent AlignedCertificate.S j.val) C (4*AlignedCertificate.R)
      (aligned_fold_exponent_range _).1 (aligned_fold_exponent_range _).2 (by dsimp [C]; positivity)
  filter_upwards [hfit, eventually_ge_atTop (3:ℕ)] with n hfitn hn
  intro call
  let j : Fin (AlignedCertificate.R+1) := ⟨call.factors.length, by have h := call.length_le; omega⟩
  apply hfitn j (innerPower n call AlignedCertificate.S) (physicalFold call AlignedCertificate.S)
  · have hD := (actual_inner_bounds AlignedCertificate.R AlignedCertificate.S n hn call).2
    simpa only [C, innerDimension_eq_power, Nat.cast_pow, Nat.cast_ofNat, j] using hD
  · have hd := (actual_folded_bounds AlignedCertificate.R AlignedCertificate.S n hn call).1
    exact hd.trans (by dsimp [physicalFold]; push_cast; nlinarith)


theorem actual_call_exponent_strict (n : ℕ) (call : Call AlignedCertificate.R n) (i : Fin 6) :
    PhaseGeometry.phaseCostExponent
      (foldExponent AlignedCertificate.S call.factors.length)
      (ringExponent AlignedCertificate.S call.factors.length) i < targetExponent :=
  PhaseGeometry.actual_call_exponent_strict call i

theorem actual_outer_bounds (R S n : ℕ) (hn : 3 ≤ n) (call : Call R n)
    (hs : 0 ≤ foldExponent S call.factors.length) :
    (n:ℝ)^(1+foldExponent S call.factors.length/2) ≤ (outerSize call S n:ℝ) ∧
      (outerSize call S n:ℝ) ≤ 4*phaseOverhead R n*
        (n:ℝ)^(1+foldExponent S call.factors.length/2) := by
  have hd := actual_folded_bounds R S n hn call
  have hnpos : 0 < (n:ℝ) := by exact_mod_cast (show 0<n by omega)
  have hdp : 0 < call.folded S := by
    have h := (Real.rpow_pos_of_pos hnpos _).trans_le hd.1
    exact_mod_cast h
  constructor
  · apply PhaseGeometry.foldedOuterLower n (physicalFold call S) _ (by omega)
    exact hd.1.trans (by dsimp [physicalFold]; push_cast; nlinarith)
  · simpa only [outerSize, physicalFold, Nat.cast_mul] using
      PhaseGeometry.foldedOuter_upper n (call.folded S) (phaseOverhead R n) _ hn hdp
        (phaseOverhead_ge_one R n hn) hs hd.2

theorem actual_cyclic_terminal_bound (n : ℕ) (hn : 3 ≤ n)
    (call : Call AlignedCertificate.R n) :
    (call.cyclic AlignedCertificate.S:ℝ) ≤
      phaseOverhead AlignedCertificate.R n*(n:ℝ)^v := by
  have h := (actual_cyclic_bounds AlignedCertificate.R AlignedCertificate.S n hn call).2
  exact h.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1≤n by omega))
      (aligned_ring_exponent_range _ call.length_le).2)
    (by have hH := phaseOverhead_ge_one AlignedCertificate.R n hn; linarith))

theorem scale_ge_three (n : ℕ) (hn : 3 ≤ n) : 3 ≤ ComputableParameters.scale n := by
  have hs : 1 < n.size := Nat.lt_size.mpr (by norm_num; omega)
  have hp : 16 ≤ n.size^4 := by
    have h := Nat.pow_le_pow_left (show 2 ≤ n.size by omega) 4
    norm_num at h
    exact h
  unfold ComputableParameters.scale ComputableParameters.roundedPower
  nlinarith

theorem actual_call_coprime (R S n : ℕ) (hn : 3 ≤ n) (call : Call R n)
    (hnd : call.factors.Nodup) :
    (physicalFold call S).Coprime (call.cyclic S) :=
  PhaseGeometry.actual_call_coprime call S (scale_ge_three n hn) hnd

/-- The actual integer-divided ordinary length used by the program,
with the enlarged candidate interval and computed block size. -/
theorem all_computed_candidate_tiles_fit :
    ∀ᶠ n : ℕ in atTop, ∀ call : Call AlignedCertificate.R n,
      (ComputableParameters.ordinaryLength (innerPower n call AlignedCertificate.S)).choose
          (innerPower n call AlignedCertificate.S) *
        4^(ComputableParameters.ordinaryLength (innerPower n call AlignedCertificate.S) -
          innerPower n call AlignedCertificate.S) ≤ outerSize call AlignedCertificate.S n := by
  filter_upwards [all_computed_candidate_tiles_fit_real] with n hn
  intro call
  simpa only [ComputableParameters.ordinaryLength_eq] using hn call

 theorem logarithmicIndex_bound (m K n : ℕ) (C a : ℝ)
    (hn : 3 ≤ n) (hC : 1 ≤ C)
    (hD : ((4:ℝ)^m) ≤ C * (Real.log (n:ℝ))^K * (n:ℝ)^a) :
    (m:ℝ) ≤ ((Real.log C + (K:ℝ) + a) / Real.log 4) * Real.log (n:ℝ) := by
  have hnpos : 0 < (n:ℝ) := by exact_mod_cast (show 0<n by omega)
  have hl : 1 ≤ Real.log (n:ℝ) := one_le_log_nat n hn
  have hlpos : 0 < Real.log (n:ℝ) := by linarith
  have hCpos : 0 < C := by linarith
  have hlogC : 0 ≤ Real.log C := Real.log_nonneg hC
  have hloglog : Real.log (Real.log (n:ℝ)) ≤ Real.log (n:ℝ) :=
    (Real.log_le_sub_one_of_pos hlpos).trans (by linarith)
  have hh := Real.log_le_log (by positivity : 0 < (4:ℝ)^m) hD
  rw [Real.log_pow, Real.log_mul (by positivity) ((Real.rpow_pos_of_pos hnpos a).ne'),
    Real.log_mul hCpos.ne' (by positivity), Real.log_pow, Real.log_rpow hnpos] at hh
  have h1 : Real.log C ≤ Real.log C * Real.log (n:ℝ) := by
    nlinarith
  have h2 : (K:ℝ)*Real.log (Real.log (n:ℝ)) ≤ (K:ℝ)*Real.log (n:ℝ) :=
    mul_le_mul_of_nonneg_left hloglog (Nat.cast_nonneg K)
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  apply (mul_le_mul_iff_left₀ hlog4).mp
  calc
    (m:ℝ)*Real.log 4 ≤ Real.log C + (K:ℝ)*Real.log (Real.log (n:ℝ)) + a*Real.log (n:ℝ) := hh
    _ ≤ (Real.log C + (K:ℝ) + a)*Real.log (n:ℝ) := by nlinarith
    _ = (((Real.log C + (K:ℝ) + a) / Real.log 4) * Real.log (n:ℝ))*Real.log 4 := by field_simp



theorem foldExponent_bounds (R S n : ℕ) (call : Call R n) :
    0 ≤ foldExponent S call.factors.length ∧
      foldExponent S call.factors.length ≤ (R:ℝ)*eta := by
  have heta := stageRelations.1
  constructor
  · exact mul_nonneg (Nat.cast_nonneg _) heta
  · apply mul_le_mul_of_nonneg_right _ heta
    exact_mod_cast (Nat.min_le_right S call.factors.length).trans call.length_le

noncomputable def indexConstant (R : ℕ) : ℝ :=
  (Real.log (24*(8192:ℝ)^R)+(4*R:ℕ)+b+(R:ℝ)*eta)/Real.log 4

noncomputable def indexMajor (R : ℕ) : ℝ := max (indexConstant R) 0+1

theorem indexMajor_pos (R : ℕ) : 0 < indexMajor R := by
  unfold indexMajor
  have h := le_max_right (indexConstant R) 0
  linarith

theorem actual_innerPower_le_log (R S n : ℕ) (hn : 3 ≤ n) (call : Call R n) :
    (innerPower n call S:ℝ) ≤ indexConstant R*Real.log (n:ℝ) := by
  have hdim := (actual_inner_bounds R S n hn call).2
  have hs := (foldExponent_bounds R S n call).2
  have hpow : (n:ℝ)^(b+foldExponent S call.factors.length) ≤
      (n:ℝ)^(b+(R:ℝ)*eta) :=
    Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast (show 1≤n by omega)) (by linarith)
  have hpos : 0 ≤ (24*(8192:ℝ)^R)*(Real.log (n:ℝ))^(4*R) := by positivity
  have hdim' := hdim.trans (mul_le_mul_of_nonneg_left hpow hpos)
  rw [innerDimension_eq_power, Nat.cast_pow, Nat.cast_ofNat] at hdim'
  have hC : (1:ℝ) ≤ 24*(8192:ℝ)^R := by
    have hp : (1:ℝ) ≤ 8192^R := one_le_pow₀ (by norm_num)
    linarith
  simpa only [indexConstant, add_assoc] using logarithmicIndex_bound _ _ _ _ _ hn hC hdim'

theorem actual_innerPower_add_one_le_log (R S n : ℕ) (hn : 3 ≤ n) (call : Call R n) :
    (innerPower n call S:ℝ)+1 ≤ indexMajor R*Real.log (n:ℝ) := by
  have h := actual_innerPower_le_log R S n hn call
  have hl := one_le_log_nat n hn
  have hm : indexConstant R*Real.log (n:ℝ) ≤
      max (indexConstant R) 0*Real.log (n:ℝ) :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith)
  unfold indexMajor
  nlinarith

theorem ceilLinear_add_one (a : ℝ) (m : ℕ) (ha : 0 ≤ a) :
    (Nat.ceil (a*(m:ℝ)):ℝ)+1 ≤ (a+2)*((m:ℝ)+1) := by
  have h := (Nat.ceil_lt_add_one (mul_nonneg ha (Nat.cast_nonneg m))).le
  nlinarith

theorem actual_roundedLength_le_log (R S n : ℕ) (hn : 3 ≤ n) (call : Call R n) :
    (Nat.ceil (RealCertificate.c*(innerPower n call S:ℝ)):ℝ)+1 ≤
      (RealCertificate.c+2)*indexMajor R*Real.log (n:ℝ) := by
  have hc : 0 ≤ RealCertificate.c := by norm_num [RealCertificate.c]
  calc
    _ ≤ (RealCertificate.c+2)*((innerPower n call S:ℝ)+1) :=
      ceilLinear_add_one _ _ hc
    _ ≤ (RealCertificate.c+2)*(indexMajor R*Real.log (n:ℝ)) :=
      mul_le_mul_of_nonneg_left (actual_innerPower_add_one_le_log R S n hn call) (by positivity)
    _ = _ := by ring

theorem actual_ordinaryLength_le_log (R S n : ℕ) (hn : 3 ≤ n) (call : Call R n) :
    (ComputableParameters.ordinaryLength (innerPower n call S):ℝ)+1 ≤
      (RealCertificate.c+2)*indexMajor R*Real.log (n:ℝ) := by
  simpa only [ComputableParameters.ordinaryLength_eq] using
    actual_roundedLength_le_log R S n hn call

theorem actual_width_le_log (R S n : ℕ) (hn : 3 ≤ n) (call : Call R n) :
    (Nat.ceil (2*RealCertificate.theta*(innerPower n call S:ℝ)):ℝ)+1 ≤
      (2*RealCertificate.theta+2)*indexMajor R*Real.log (n:ℝ) := by
  have ht : 0 ≤ RealCertificate.theta := by norm_num [RealCertificate.theta]
  calc
    _ ≤ (2*RealCertificate.theta+2)*((innerPower n call S:ℝ)+1) :=
      ceilLinear_add_one _ _ (by positivity)
    _ ≤ (2*RealCertificate.theta+2)*(indexMajor R*Real.log (n:ℝ)) :=
      mul_le_mul_of_nonneg_left (actual_innerPower_add_one_le_log R S n hn call) (by positivity)
    _ = _ := by ring

theorem actual_channelLength_le_log (R S n : ℕ) (hn : 3 ≤ n) (call : Call R n) :
    (ComputableParameters.channelLength (innerPower n call S):ℝ)+1 ≤
      (2*RealCertificate.theta+2)*indexMajor R*Real.log (n:ℝ) := by
  simpa only [ComputableParameters.channelLength_eq] using
    actual_width_le_log R S n hn call

theorem actual_twice_innerPower_add_one_le_log (R S n : ℕ) (hn : 3 ≤ n) (call : Call R n) :
    (2*innerPower n call S+1:ℕ) ≤ 2*indexMajor R*Real.log (n:ℝ) := by
  have h := actual_innerPower_add_one_le_log R S n hn call
  push_cast
  linarith

/-- The source-gap threshold holds uniformly over all computed-scale
candidate lists and every location of the physical/cyclic split. -/
theorem actual_innerPower_uniformly_large (R M : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ call : Call R n, ∀ S : ℕ, M ≤ innerPower n call S := by
  have hb : 0 < b := by norm_num [b, AlignedCertificate.b]
  have ht := (tendsto_rpow_atTop hb).comp tendsto_natCast_atTop_atTop
  have hlarge := ht.eventually (eventually_gt_atTop ((4:ℝ)^M))
  filter_upwards [hlarge, eventually_ge_atTop (3:ℕ)] with n hn hn3
  intro call S
  have hD := (actual_inner_bounds R S n hn3 call).1
  have hs := (foldExponent_bounds R S n call).1
  have hpow := Real.rpow_le_rpow_of_exponent_le
    (show (1:ℝ) ≤ n by exact_mod_cast (show 1≤n by omega))
    (show b ≤ b+foldExponent S call.factors.length by linarith)
  rw [innerDimension_eq_power, Nat.cast_pow, Nat.cast_ofNat] at hD
  by_contra hnot
  have hle : innerPower n call S ≤ M := by omega
  have hf : (4:ℝ)^(innerPower n call S) ≤ (4:ℝ)^M :=
    pow_le_pow_right₀ (by norm_num) hle
  change (4:ℝ)^M < (n:ℝ)^b at hn
  exact (not_lt_of_ge (hpow.trans (hD.trans hf))) hn

/-- A list produced under a successful uniform parameter-program result
is a call at exactly its computed interval and fixed factor count. -/
def phaseCallOfProgram (n U : ℕ) (p : CompleteAPSP.Parameters (ComputableParameters.block n) U)
    (hp : ComputableParameters.program n U = some p) (factors : List ℕ)
    (hlen : factors.length ≤ p.k+1) (hvalid : ∀ q ∈ factors, q ∈ p.pool) :
    Call AlignedCertificate.R n where
  factors := factors
  length_le := by
    have hk := (ComputableParameters.program_sound n U p hp).2.2.2.1
    rw [hk] at hlen
    simpa only [ComputableParameters.factorCount, AlignedCertificate.R] using hlen
  valid q hq := by
    apply computedPool_subset_candidates n
    rw [← (ComputableParameters.program_sound n U p hp).1]
    exact hvalid q hq

@[simp] theorem phaseCallOfProgram_factors (n U : ℕ)
    (p : CompleteAPSP.Parameters (ComputableParameters.block n) U)
    (hp : ComputableParameters.program n U = some p) (factors : List ℕ)
    (hlen : factors.length ≤ p.k+1) (hvalid : ∀ q ∈ factors, q ∈ p.pool) :
    (phaseCallOfProgram n U p hp factors hlen hvalid).factors = factors := rfl

/-- This specialization is coupled to the actual successful uniform
program output and its prime lists, not a separately selected scale. -/
theorem all_program_candidate_tiles_fit :
    ∀ᶠ n : ℕ in atTop, ∀ U : ℕ,
      ∀ p : CompleteAPSP.Parameters (ComputableParameters.block n) U,
      ∀ hp : ComputableParameters.program n U = some p, ∀ factors : List ℕ,
      ∀ hlen : factors.length ≤ p.k+1, ∀ hvalid : ∀ q ∈ factors, q ∈ p.pool,
      let call := phaseCallOfProgram n U p hp factors hlen hvalid
      (ComputableParameters.ordinaryLength (innerPower n call AlignedCertificate.S)).choose
          (innerPower n call AlignedCertificate.S) *
        4^(ComputableParameters.ordinaryLength (innerPower n call AlignedCertificate.S) -
          innerPower n call AlignedCertificate.S) ≤ outerSize call AlignedCertificate.S n := by
  filter_upwards [all_computed_candidate_tiles_fit] with n hn
  intro U p hp factors hlen hvalid
  exact hn (phaseCallOfProgram n U p hp factors hlen hvalid)

theorem generic_scale_log_upper (n d K : ℕ) (C a : ℝ)
    (hn : 3 ≤ n) (hC : 0 < C) (hd : 0 < d)
    (hu : (d : ℝ) ≤ C * (Real.log (n : ℝ))^K * (n : ℝ)^a) :
    Real.log (d : ℝ) ≤
      (|Real.log C| + (K : ℝ) + a) * Real.log (n : ℝ) := by
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hl1 := PhaseGeometry.one_le_log_nat n hn
  have hlpos : 0 < Real.log (n : ℝ) := by linarith
  have hxpos : 0 < (n : ℝ)^a := Real.rpow_pos_of_pos hnpos a
  have hlKpos : 0 < (Real.log (n : ℝ))^K := pow_pos hlpos K
  have hlog := Real.log_le_log (by exact_mod_cast hd : (0 : ℝ) < d) hu
  rw [Real.log_mul (mul_pos hC hlKpos).ne' hxpos.ne',
    Real.log_mul hC.ne' hlKpos.ne', Real.log_pow,
    Real.log_rpow hnpos] at hlog
  have hCabs : Real.log C ≤ |Real.log C| := le_abs_self _
  have hCmul : |Real.log C| ≤ |Real.log C| * Real.log (n : ℝ) :=
    le_mul_of_one_le_right (abs_nonneg _) hl1
  have hll := Real.log_le_self hlpos.le
  have hKlog := mul_le_mul_of_nonneg_left hll (Nat.cast_nonneg K : (0 : ℝ) ≤ K)
  calc
    Real.log (d : ℝ) ≤ Real.log C + (K : ℝ) * Real.log (Real.log (n : ℝ)) +
      a * Real.log (n : ℝ) := hlog
    _ ≤ |Real.log C| * Real.log (n : ℝ) + (K : ℝ) * Real.log (n : ℝ) +
      a * Real.log (n : ℝ) := by linarith
    _ = (|Real.log C| + (K : ℝ) + a) * Real.log (n : ℝ) := by ring

noncomputable def outerLogConstant (R : ℕ) : ℝ :=
  (|Real.log (4*(8192:ℝ)^R)|+(4*R:ℕ)+(1+(R:ℝ)*eta/2))/Real.log 2

theorem actual_outer_polynomial_bound (R S n : ℕ) (hn : 3 ≤ n) (call : Call R n) :
    (outerSize call S n:ℝ) ≤
      (4*(8192:ℝ)^R)*(Real.log (n:ℝ))^(4*R)*(n:ℝ)^(1+(R:ℝ)*eta/2) := by
  have hs0 : 0 ≤ foldExponent S call.factors.length :=
    mul_nonneg (Nat.cast_nonneg _) stageRelations.1
  have hsR : foldExponent S call.factors.length ≤ (R:ℝ)*eta := by
    apply mul_le_mul_of_nonneg_right _ stageRelations.1
    exact_mod_cast (Nat.min_le_right S call.factors.length).trans call.length_le
  have h := (ComputedPhaseGeometry.actual_outer_bounds R S n hn call hs0).2
  calc
    _ ≤ 4*ComputedPhaseGeometry.phaseOverhead R n*
        (n:ℝ)^(1+foldExponent S call.factors.length/2) := h
    _ ≤ 4*ComputedPhaseGeometry.phaseOverhead R n*(n:ℝ)^(1+(R:ℝ)*eta/2) := by
      apply mul_le_mul_of_nonneg_left _ (by
        have hH := ComputedPhaseGeometry.phaseOverhead_ge_one R n hn
        linarith)
      apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1≤n by omega))
      linarith
    _ = _ := by unfold ComputedPhaseGeometry.phaseOverhead; ring

theorem actual_outer_pos (R S n : ℕ) (hn : 3 ≤ n) (call : Call R n) :
    0 < outerSize call S n := by
  have hs0 : 0 ≤ foldExponent S call.factors.length :=
    mul_nonneg (Nat.cast_nonneg _) stageRelations.1
  have h := (ComputedPhaseGeometry.actual_outer_bounds R S n hn call hs0).1
  have hnpos : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hp : (0:ℝ)<(outerSize call S n:ℝ) := (Real.rpow_pos_of_pos hnpos _).trans_le h
  exact_mod_cast hp

theorem actual_outer_log2_of_log (R S n : ℕ) (call : Call R n)
    (hlog : Real.log (outerSize call S n:ℝ) ≤
      (|Real.log (4*(8192:ℝ)^R)|+(4*R:ℕ)+(1+(R:ℝ)*eta/2))*Real.log (n:ℝ)) :
    ((outerSize call S n).log2:ℝ) ≤ outerLogConstant R*Real.log (n:ℝ) := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  calc
    ((outerSize call S n).log2:ℝ) ≤ Real.log (outerSize call S n:ℝ)/Real.log 2 := by
      simpa only [Real.logb] using Real.log2_le_logb (outerSize call S n)
    _ ≤ outerLogConstant R*Real.log (n:ℝ) := by
      simpa only [outerLogConstant, div_mul_eq_mul_div] using
        div_le_div_of_nonneg_right hlog h2.le

theorem actual_outer_size_of_log (R S n : ℕ) (hn : 3 ≤ n) (call : Call R n)
    (hlog : Real.log (outerSize call S n:ℝ) ≤
      (|Real.log (4*(8192:ℝ)^R)|+(4*R:ℕ)+(1+(R:ℝ)*eta/2))*Real.log (n:ℝ)) :
    ((outerSize call S n).size:ℝ) ≤ (outerLogConstant R+1)*Real.log (n:ℝ) := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl := PhaseGeometry.one_le_log_nat n hn
  have hdiv : Real.log (outerSize call S n:ℝ)/Real.log 2 ≤
      outerLogConstant R*Real.log (n:ℝ) := by
    simpa only [outerLogConstant, div_mul_eq_mul_div] using
      div_le_div_of_nonneg_right hlog h2.le
  have hs := CertificationParameters.size_le_log (outerSize call S n)
  linarith

theorem actual_outer_log (R S n : ℕ) (hn : 3 ≤ n) (call : Call R n) :
    Real.log (outerSize call S n:ℝ) ≤
      (|Real.log (4*(8192:ℝ)^R)|+(4*R:ℕ)+(1+(R:ℝ)*eta/2))*Real.log (n:ℝ) := by
  exact generic_scale_log_upper n (outerSize call S n) (4*R)
    (4*(8192:ℝ)^R) (1+(R:ℝ)*eta/2) hn (by positivity)
    (actual_outer_pos R S n hn call) (actual_outer_polynomial_bound R S n hn call)

theorem actual_outer_log2 (R S n : ℕ) (hn : 3 ≤ n) (call : Call R n) :
    ((outerSize call S n).log2:ℝ) ≤ outerLogConstant R*Real.log (n:ℝ) := by
  exact actual_outer_log2_of_log R S n call (actual_outer_log R S n hn call)

theorem actual_outer_log2_add_one (R S n : ℕ) (hn : 3 ≤ n) (call : Call R n) :
    ((outerSize call S n).log2:ℝ)+1 ≤ (outerLogConstant R+1)*Real.log (n:ℝ) := by
  have h := actual_outer_log2 R S n hn call
  have hl := PhaseGeometry.one_le_log_nat n hn
  linarith

theorem actual_outer_size (R S n : ℕ) (hn : 3 ≤ n) (call : Call R n) :
    ((outerSize call S n).size:ℝ) ≤ (outerLogConstant R+1)*Real.log (n:ℝ) := by
  exact actual_outer_size_of_log R S n hn call (actual_outer_log R S n hn call)


end ThinMatrix.ComputedPhaseGeometry

#print axioms ThinMatrix.ComputedPhaseGeometry.queryCount_upper
#print axioms ThinMatrix.ComputedPhaseGeometry.actual_candidate_count
#print axioms ThinMatrix.ComputedPhaseGeometry.actual_call_exponent_strict
#print axioms ThinMatrix.ComputedPhaseGeometry.actual_folded_bounds
#print axioms ThinMatrix.ComputedPhaseGeometry.actual_cyclic_bounds
#print axioms ThinMatrix.ComputedPhaseGeometry.actual_inner_bounds
#print axioms ThinMatrix.ComputedPhaseGeometry.actual_outer_bounds
#print axioms ThinMatrix.ComputedPhaseGeometry.actual_call_coprime
#print axioms ThinMatrix.ComputedPhaseGeometry.all_computed_candidate_tiles_fit
#print axioms ThinMatrix.ComputedPhaseGeometry.actual_innerPower_le_log
#print axioms ThinMatrix.ComputedPhaseGeometry.actual_innerPower_uniformly_large
#print axioms ThinMatrix.ComputedPhaseGeometry.all_program_candidate_tiles_fit

#print axioms ThinMatrix.ComputedPhaseGeometry.actual_outer_log2
#print axioms ThinMatrix.ComputedPhaseGeometry.actual_outer_size
