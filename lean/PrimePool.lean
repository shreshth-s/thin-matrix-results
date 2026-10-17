import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

/-!
# Prime candidates in a constant factor interval

The candidate interval is enlarged to `(P,8P)`. This changes only fixed
constants in the reduction. The argument uses mathlib's proved Chebyshev
bounds, rather than a prime number theorem axiom.
-/

namespace ThinMatrix.PrimePool

open Filter Real
open scoped Topology Nat.Prime

def candidates (P : ℕ) : Finset ℕ := Nat.primesLE (8 * P) \ Nat.primesLE P

def available (P : ℕ) (excluded : Finset ℕ) : Finset ℕ := candidates P \ excluded

theorem mem_candidates {P p : ℕ} :
    p ∈ candidates P ↔ Nat.Prime p ∧ P < p ∧ p ≤ 8 * P := by
  simp only [candidates, Finset.mem_sdiff, Nat.mem_primesLE]
  constructor
  · rintro ⟨⟨hp8, hp⟩, hnot⟩
    have hnotle : ¬p ≤ P := fun h => hnot ⟨h, hp⟩
    exact ⟨hp, by omega, hp8⟩
  · rintro ⟨hp, hpP, hp8⟩
    exact ⟨⟨hp8, hp⟩, by omega⟩

theorem candidate_prime {P p : ℕ} (hp : p ∈ candidates P) : Nat.Prime p :=
  (mem_candidates.mp hp).1

theorem candidate_lower {P p : ℕ} (hp : p ∈ candidates P) : P ≤ p :=
  (mem_candidates.mp hp).2.1.le

theorem candidate_upper {P p : ℕ} (hp : p ∈ candidates P) : p < 8 * P := by
  have h := mem_candidates.mp hp
  have hn : ¬Nat.Prime (8 * P) := by
    simp only [Nat.prime_mul_iff]
    norm_num
  have hne : p ≠ 8 * P := by
    intro heq
    exact hn (heq ▸ h.1)
  omega

theorem candidate_card (P : ℕ) :
    (candidates P).card = Nat.primeCounting (8 * P) - Nat.primeCounting P := by
  rw [candidates, Finset.card_sdiff_of_subset (Nat.primesLE_mono (by omega))]
  simp only [Nat.primesLE_card_eq_primeCounting]

private theorem log_four : log (4 : ℝ) = 2 * log 2 := by
  have h := log_pow (2 : ℝ) 2
  norm_num at h
  exact h

private theorem eventually_log_scaled_le :
    ∀ᶠ x : ℝ in atTop, log (8*x+1) ≤ x * log 2 := by
  have hε : 0 < log (2 : ℝ) / 16 := by positivity
  obtain ⟨a, ha⟩ := Filter.eventually_atTop.mp (Real.isLittleO_log_id_atTop.bound hε)
  filter_upwards [eventually_ge_atTop (max 1 a)] with x hx
  have hx1 : 1 ≤ x := le_trans (le_max_left _ _) hx
  have hxa : a ≤ 8*x+1 := by
    have : a ≤ x := le_trans (le_max_right _ _) hx
    linarith
  have hs := ha (8*x+1) hxa
  have hs' : |log (8*x+1)| ≤ log 2 / 16 * (8*x+1) := by
    simpa only [Real.norm_eq_abs, id_eq,
      abs_of_nonneg (show 0 ≤ 8*x+1 by linarith)] using hs
  have hl2 : 0 < log (2 : ℝ) := by positivity
  calc
    log (8*x+1) ≤ |log (8*x+1)| := le_abs_self _
    _ ≤ log 2 / 16 * (8*x+1) := hs'
    _ ≤ x * log 2 := by nlinarith

/-- A genuine eventual lower bound, with an explicit positive constant. -/
theorem eventually_candidate_card_lower :
    ∀ᶠ P : ℕ in atTop,
      (P : ℝ) / (4 * log P) ≤ ((candidates P).card : ℝ) := by
  have hupper := tendsto_natCast_atTop_atTop.eventually
    (Chebyshev.eventually_primeCounting_le (show 0 < log (2 : ℝ) by positivity))
  have herr := tendsto_natCast_atTop_atTop.eventually eventually_log_scaled_le
  filter_upwards [hupper, herr, eventually_ge_atTop 8] with P hupper herr hP
  have hx : (8 : ℝ) ≤ P := by exact_mod_cast hP
  have hxpos : 0 < (P : ℝ) := by linarith
  have hl : 0 < log (P : ℝ) := log_pos (by linarith)
  have hl8 : 0 < log (8 * (P : ℝ)) := log_pos (by linarith)
  have hden : log (8 * (P : ℝ)) ≤ 2 * log P := by
    calc
      log (8 * (P : ℝ)) ≤ log ((P : ℝ)^2) := log_le_log (by positivity) (by nlinarith)
      _ = 2 * log P := by rw [log_pow]; norm_num
  have hlow := Chebyshev.pi_ge (8 * P)
  norm_num only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at hlow
  have hmain : ((7 : ℝ) / 2 * log 2) * P / log P ≤ Nat.primeCounting (8 * P) := by
    apply le_trans _ hlow
    apply (div_le_div_iff₀ hl hl8).2
    have hmul : (7 * (P : ℝ) * log 2) * log P ≤
        (8 * (P : ℝ) * log 2 - log (8 * (P : ℝ)+1)) * log P := by
      nlinarith [mul_nonneg (show 0 ≤ (P : ℝ) * log 2 - log (8 * (P : ℝ)+1) from sub_nonneg.mpr herr) hl.le]
    have hmden := mul_le_mul_of_nonneg_left hden
      (show 0 ≤ ((7 : ℝ)/2 * log 2) * (P : ℝ) by positivity)
    nlinarith
  have hup : (Nat.primeCounting P : ℝ) ≤ (3 * log 2) * P / log P := by
    simpa only [Nat.floor_natCast, log_four, show 2 * log (2 : ℝ) + log 2 = 3 * log 2 by ring] using hupper
  have hmono : Nat.primeCounting P ≤ Nat.primeCounting (8 * P) :=
    Nat.monotone_primeCounting (by omega)
  rw [candidate_card, Nat.cast_sub hmono]
  have hnum : (1 : ℝ) / 2 < log 2 := by linarith [Real.log_two_gt_d9]
  have hgap : (P : ℝ) / (4 * log P) ≤
      ((7 : ℝ)/2 * log 2) * P / log P - (3 * log 2) * P / log P := by
    calc
      (P : ℝ) / (4 * log P) = ((1:ℝ)/4 * P) / log P := by ring
      _ ≤ (log 2 / 2 * P) / log P :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right (by linarith) hxpos.le) hl.le
      _ = _ := by ring
  linarith

/-- The matching upper bound establishes the claimed order `P / log P`. -/
theorem eventually_candidate_card_upper :
    ∀ᶠ P : ℕ in atTop,
      ((candidates P).card : ℝ) ≤ 24 * (P : ℝ) / log P := by
  have ht : Tendsto (fun P : ℕ => 8 * (P : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num : (0 : ℝ) < 8)
  have hupper := ht.eventually
    (Chebyshev.eventually_primeCounting_le (show 0 < log (2 : ℝ) by positivity))
  filter_upwards [hupper, eventually_ge_atTop 2] with P hu hP
  have hx : (2 : ℝ) ≤ P := by exact_mod_cast hP
  have hl : 0 < log (P : ℝ) := log_pos (by linarith)
  have hl8 : 0 < log (8 * (P : ℝ)) := log_pos (by linarith)
  have hlog : log (P : ℝ) ≤ log (8 * (P : ℝ)) :=
    log_le_log (by linarith) (by linarith)
  have hcount : (Nat.primeCounting (8 * P) : ℝ) ≤
      (3 * log 2) * (8 * (P : ℝ)) / log (8 * (P : ℝ)) := by
    simpa only [show 8 * (P : ℝ) = ((8 * P : ℕ) : ℝ) by push_cast; rfl,
      Nat.floor_natCast, log_four,
      show 2 * log (2 : ℝ) + log 2 = 3 * log 2 by ring] using hu
  have hlog2 : log (2 : ℝ) ≤ 1 := by
    have := log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num)
    linarith
  have hnum : (3 * log (2 : ℝ)) * (8 * (P : ℝ)) ≤ 24 * P := by
    nlinarith [mul_nonneg (show 0 ≤ 1 - log (2 : ℝ) by linarith)
      (show 0 ≤ (P : ℝ) by positivity)]
  calc
    ((candidates P).card : ℝ) ≤ (Nat.primeCounting (8 * P) : ℝ) := by
      exact_mod_cast (show (candidates P).card ≤ Nat.primeCounting (8 * P) by
        rw [candidate_card]; omega)
    _ ≤ (3 * log 2) * (8 * (P : ℝ)) / log (8 * (P : ℝ)) := hcount
    _ ≤ (24 * (P : ℝ)) / log (8 * (P : ℝ)) :=
      div_le_div_of_nonneg_right hnum hl8.le
    _ ≤ (24 * (P : ℝ)) / log P :=
      div_le_div_of_nonneg_left (by positivity) hl hlog

private theorem eventually_fixed_le_scale (R : ℕ) :
    ∀ᶠ x : ℝ in atTop, (R : ℝ) ≤ x / (8 * log x) := by
  have hc : 0 < (1 : ℝ) / (8 * ((R : ℝ) + 1)) := by positivity
  filter_upwards [Real.isLittleO_log_id_atTop.bound hc,
    eventually_ge_atTop (2 : ℝ)] with x hx hx2
  have hxp : 0 < x := by linarith
  have hlp : 0 < log x := log_pos (by linarith)
  simp only [Real.norm_eq_abs, id_eq, abs_of_pos hlp, abs_of_pos hxp] at hx
  rw [one_div, inv_mul_eq_div,
    le_div_iff₀ (by positivity : (0 : ℝ) < 8 * ((R : ℝ) + 1))] at hx
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 8 * log x)).2
  nlinarith

/-- Removing any fixed finite set still leaves a prime pool of the required size. -/
theorem eventually_available_card_lower (excluded : Finset ℕ) :
    ∀ᶠ P : ℕ in atTop,
      (P : ℝ) / (8 * log P) ≤ ((available P excluded).card : ℝ) := by
  have hfixed := tendsto_natCast_atTop_atTop.eventually
    (eventually_fixed_le_scale excluded.card)
  filter_upwards [eventually_candidate_card_lower, hfixed] with P hpool hfixed
  have hcard : ((candidates P).card : ℝ) ≤
      ((available P excluded).card : ℝ) + (excluded.card : ℝ) := by
    exact_mod_cast (Finset.card_le_card_sdiff_add_card
      (s := candidates P) (t := excluded))
  have heq : (P : ℝ) / (4 * log P) = 2 * ((P : ℝ) / (8 * log P)) := by ring
  linarith

/-- Uniform in the excluded values: only their fixed cardinality bound matters. -/
theorem eventually_available_card_lower_uniform (R : ℕ) :
    ∀ᶠ P : ℕ in atTop, ∀ excluded : Finset ℕ, excluded.card ≤ R →
      (P : ℝ) / (8 * log P) ≤ ((available P excluded).card : ℝ) := by
  have hfixed := tendsto_natCast_atTop_atTop.eventually
    (eventually_fixed_le_scale R)
  filter_upwards [eventually_candidate_card_lower, hfixed] with P hpool hfixed
  intro excluded hexcluded
  have hcard : ((candidates P).card : ℝ) ≤
      ((available P excluded).card : ℝ) + (excluded.card : ℝ) := by
    exact_mod_cast (Finset.card_le_card_sdiff_add_card
      (s := candidates P) (t := excluded))
  have hex : (excluded.card : ℝ) ≤ R := by exact_mod_cast hexcluded
  have heq : (P : ℝ) / (4 * log P) = 2 * ((P : ℝ) / (8 * log P)) := by ring
  linarith

theorem available_prime {P p : ℕ} {excluded : Finset ℕ}
    (hp : p ∈ available P excluded) : Nat.Prime p :=
  candidate_prime (Finset.mem_sdiff.mp hp).1

theorem available_lower {P p : ℕ} {excluded : Finset ℕ}
    (hp : p ∈ available P excluded) : P ≤ p :=
  candidate_lower (Finset.mem_sdiff.mp hp).1

theorem available_upper {P p : ℕ} {excluded : Finset ℕ}
    (hp : p ∈ available P excluded) : p < 8 * P :=
  candidate_upper (Finset.mem_sdiff.mp hp).1

theorem available_not_excluded {P p : ℕ} {excluded : Finset ℕ}
    (hp : p ∈ available P excluded) : p ∉ excluded :=
  (Finset.mem_sdiff.mp hp).2

/-- The interface used by composite certification, with variable excluded primes. -/
theorem eventually_prime_pool (R : ℕ) :
    ∀ᶠ P : ℕ in atTop, ∀ excluded : Finset ℕ, excluded.card ≤ R →
      ∃ pool : Finset ℕ,
        (∀ p ∈ pool, Nat.Prime p ∧ P ≤ p ∧ p < 8 * P ∧ p ∉ excluded) ∧
        (P : ℝ) / (8 * log P) ≤ (pool.card : ℝ) := by
  filter_upwards [eventually_available_card_lower_uniform R] with P hP
  intro excluded hexcluded
  refine ⟨available P excluded, ?_, hP excluded hexcluded⟩
  intro p hp
  exact ⟨available_prime hp, available_lower hp, available_upper hp,
    available_not_excluded hp⟩

/-- A direct finite trial-division predicate; there is no primality oracle axiom. -/
def trialPrime (n : ℕ) : Prop :=
  2 ≤ n ∧ ∀ d : Fin n, 2 ≤ d.val → ¬d.val ∣ n

instance (n : ℕ) : Decidable (trialPrime n) :=
  inferInstanceAs (Decidable (2 ≤ n ∧ ∀ d : Fin n, 2 ≤ d.val → ¬d.val ∣ n))

theorem trialPrime_iff (n : ℕ) : trialPrime n ↔ Nat.Prime n := by
  rw [Nat.prime_def_lt']
  constructor
  · rintro ⟨hn, hd⟩
    exact ⟨hn, fun d hd2 hdn => hd ⟨d, hdn⟩ hd2⟩
  · rintro ⟨hn, hd⟩
    exact ⟨hn, fun d hd2 => hd d.val hd2 d.isLt⟩

def enumeratedCandidates (P : ℕ) : Finset ℕ :=
  (Finset.range (8 * P)).filter (fun p => P < p ∧ trialPrime p)

theorem enumeratedCandidates_eq (P : ℕ) : enumeratedCandidates P = candidates P := by
  ext p
  simp only [enumeratedCandidates, Finset.mem_filter, Finset.mem_range, trialPrime_iff]
  constructor
  · rintro ⟨hupper, hlower, hprime⟩
    exact mem_candidates.mpr ⟨hprime, hlower, hupper.le⟩
  · intro hp
    exact ⟨candidate_upper hp, (mem_candidates.mp hp).2.1, candidate_prime hp⟩

/-- A superset of every divisor query made by the direct enumeration. -/
def trialDivisionSites (P : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (8 * P)).product (Finset.range (8 * P))

theorem trialDivisionSites_card (P : ℕ) :
    (trialDivisionSites P).card = 64 * P^2 := by
  simp [trialDivisionSites, Finset.card_product]
  ring

theorem divisor_query_mem {P p : ℕ} (hp : p < 8 * P) (d : Fin p) :
    (p, d.val) ∈ trialDivisionSites P := by
  exact Finset.mem_product.mpr
    ⟨Finset.mem_range.mpr hp, Finset.mem_range.mpr (lt_trans d.isLt hp)⟩

/-- The nested trial-division loop has at most a quadratic number of tests. -/
theorem trialDivisionWork_le (P : ℕ) :
    (∑ p ∈ Finset.range (8 * P), p) ≤ 64 * P^2 := by
  calc
    (∑ p ∈ Finset.range (8 * P), p) ≤
        ∑ _p ∈ Finset.range (8 * P), 8 * P :=
      Finset.sum_le_sum (fun p hp => (Finset.mem_range.mp hp).le)
    _ = 64 * P^2 := by simp; ring

/-
`trialDivisionSites_card` is a finite query-count bound, not a formal RAM
semantics theorem. Direct enumeration uses at most 64 P^2 divisibility
tests, plus linear range/filter work and the bit costs of those tests.
Integration must charge this one-time setup additively. This module does
not formalize the complete RAM runtime or its exponent ledger.
-/

end ThinMatrix.PrimePool

#print axioms ThinMatrix.PrimePool.eventually_candidate_card_lower
#print axioms ThinMatrix.PrimePool.eventually_candidate_card_upper
#print axioms ThinMatrix.PrimePool.eventually_available_card_lower
#print axioms ThinMatrix.PrimePool.eventually_available_card_lower_uniform
#print axioms ThinMatrix.PrimePool.eventually_prime_pool
#print axioms ThinMatrix.PrimePool.enumeratedCandidates_eq
#print axioms ThinMatrix.PrimePool.trialDivisionSites_card
#print axioms ThinMatrix.PrimePool.trialDivisionWork_le
