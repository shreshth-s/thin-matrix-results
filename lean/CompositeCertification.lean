import Mathlib

/-!
# Finite composite-incidence certification

This file formalizes the finite counting argument in
`lem:composite-incidence`, independently of the implementation of a count
oracle. Witnesses are labels in an actual finite block and their sums are
integers. Counts retain multiplicities of labels, including false witnesses
inside incidences that also contain genuine zero sums. Candidate primes are
a `Finset`, so the divisor argument uses distinct primes.

The finite prime-pool hypotheses below are explicit: primality, a lower
bound on each prime, and an integer power bound on nonzero sums. Prime
density, a sieve's running time, the folded/cyclic count implementation,
asymptotic bit costs, and the min-plus/APSP transfers are separate interfaces;
they are not asserted by this file. In particular scalar and cyclic calls
must both supply the same exact `modCount` table for their full modulus.

`PrimePool.lean` supplies a pool in `(P,8P)` with eventual cardinality at
least `P/(8 log P)` after a fixed number of exclusions. The changed fixed
constant is deliberate; the finite results here accept any such pool and
do not assume the source's stronger interval-prime estimate. The power
condition `U < P^(lam+1)` replaces a logarithmic floor exactly.
-/

namespace ThinMatrix.CompositeCertification

open Finset

variable {X V Pair : Type*} [DecidableEq Pair]

/-- An incidence's actual block, with one original integer sum per label. -/
structure Instance (X V : Type*) where
  block : X → Finset V
  value : X → V → ℤ

namespace Instance

variable (A : Instance X V)

def trueCount (x : X) : ℕ :=
  ∑ v ∈ A.block x, if A.value x v = 0 then 1 else 0

def falseCount (d : ℕ) (x : X) : ℕ :=
  ∑ v ∈ A.block x, if A.value x v ≠ 0 ∧ (d : ℤ) ∣ A.value x v then 1 else 0

def modCount (d : ℕ) (x : X) : ℕ :=
  ∑ v ∈ A.block x, if (d : ℤ) ∣ A.value x v then 1 else 0

def falseMass (active : Finset X) (d : ℕ) : ℕ :=
  ∑ x ∈ active, A.falseCount d x

def totalCount (active : Finset X) (d : ℕ) : ℕ :=
  ∑ x ∈ active, A.modCount d x

theorem modCount_eq (d : ℕ) (x : X) :
    A.modCount d x = A.trueCount x + A.falseCount d x := by
  unfold modCount trueCount falseCount
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v hv
  by_cases hz : A.value x v = 0
  · simp [hz]
  · by_cases hd : (d : ℤ) ∣ A.value x v <;> simp [hz, hd]

theorem trueCount_le (d : ℕ) (x : X) : A.trueCount x ≤ A.modCount d x := by
  rw [A.modCount_eq]
  omega

theorem count_one (x : X) : A.modCount 1 x = (A.block x).card := by
  simp [modCount]

theorem falseCount_le_block (d : ℕ) (x : X) :
    A.falseCount d x ≤ (A.block x).card := by
  unfold falseCount
  calc
    _ ≤ ∑ _v ∈ A.block x, 1 := Finset.sum_le_sum (fun _ _ => by split <;> omega)
    _ = _ := by simp

theorem falseMass_le (active : Finset X) (d h : ℕ)
    (hblock : ∀ x ∈ active, (A.block x).card ≤ h) :
    A.falseMass active d ≤ h * active.card := by
  calc
    _ ≤ ∑ _x ∈ active, h := Finset.sum_le_sum (fun x hx =>
      (A.falseCount_le_block d x).trans (hblock x hx))
    _ = _ := by simp [mul_comm]

/-- Distinct primes dividing a nonzero integer have product at most its
absolute value. This is proved from Mathlib's prime-factor divisibility. -/
theorem prime_divisor_power_le (pool : Finset ℕ) (P : ℕ) (z : ℤ)
    (hz : z ≠ 0) (hprime : ∀ p ∈ pool, Nat.Prime p)
    (hlower : ∀ p ∈ pool, P ≤ p) :
    P ^ (pool.filter (fun p : ℕ => (p : ℤ) ∣ z)).card ≤ z.natAbs := by
  let divisors := pool.filter (fun p : ℕ => (p : ℤ) ∣ z)
  have hn : z.natAbs ≠ 0 := by simpa using hz
  have hsub : divisors ⊆ z.natAbs.primeFactors := by
    intro p hp
    obtain ⟨hp, hd⟩ := Finset.mem_filter.mp hp
    exact Nat.mem_primeFactors.mpr ⟨hprime p hp, Int.natCast_dvd.mp hd, hn⟩
  have hdvd : (∏ p ∈ divisors, p) ∣ z.natAbs :=
    dvd_trans (Finset.prod_dvd_prod_of_subset divisors z.natAbs.primeFactors id hsub)
      (Nat.prod_primeFactors_dvd z.natAbs)
  calc
    P ^ divisors.card = ∏ _p ∈ divisors, P := by simp
    _ ≤ ∏ p ∈ divisors, p := Finset.prod_le_prod' (fun p hp =>
      hlower p (Finset.mem_filter.mp hp).1)
    _ ≤ z.natAbs := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hdvd

/-- An exact integer replacement for the logarithmic divisor bound. -/
theorem prime_divisor_card_le (pool : Finset ℕ) (P U lam : ℕ) (z : ℤ)
    (hz : z ≠ 0) (hprime : ∀ p ∈ pool, Nat.Prime p)
    (hlower : ∀ p ∈ pool, P ≤ p) (hP : 1 ≤ P)
    (hmag : z.natAbs ≤ U) (hpower : U < P ^ (lam + 1)) :
    (pool.filter (fun p : ℕ => (p : ℤ) ∣ z)).card ≤ lam := by
  by_contra h
  have hc : lam + 1 ≤ (pool.filter (fun p : ℕ => (p : ℤ) ∣ z)).card := by omega
  have hpow := Nat.pow_le_pow_right hP hc
  have hprod := prime_divisor_power_le pool P z hz hprime hlower
  omega

/-- This predicate is a finite divisor bound, subsequently derived from
the proved prime/power theorem rather than assumed as a contraction. -/
def DivisorBound (pool : Finset ℕ) (lam : ℕ) : Prop :=
  ∀ x v, v ∈ A.block x → A.value x v ≠ 0 →
    (pool.filter (fun p : ℕ => (p : ℤ) ∣ A.value x v)).card ≤ lam

theorem divisorBound_of_prime_power (pool : Finset ℕ) (P U lam : ℕ)
    (hprime : ∀ p ∈ pool, Nat.Prime p) (hlower : ∀ p ∈ pool, P ≤ p)
    (hP : 1 ≤ P) (hmag : ∀ x v, v ∈ A.block x → (A.value x v).natAbs ≤ U)
    (hpower : U < P ^ (lam + 1)) : A.DivisorBound pool lam := by
  intro x v hv hz
  exact prime_divisor_card_le pool P U lam _ hz hprime hlower hP (hmag x v hv) hpower

theorem divisorBound_subset {pool small : Finset ℕ} {lam : ℕ}
    (h : A.DivisorBound pool lam) (hs : small ⊆ pool) : A.DivisorBound small lam := by
  intro x v hv hz
  exact (Finset.card_le_card (Finset.filter_subset_filter _ hs)).trans (h x v hv hz)

/-- Averaging counts the same original label at every candidate; no CRT
tuple of unrelated false witnesses is introduced. -/
theorem sum_falseCount_le (pool : Finset ℕ) (lam d : ℕ) (x : X)
    (hdiv : A.DivisorBound pool lam) :
    (∑ p ∈ pool, A.falseCount (d * p) x) ≤ lam * A.falseCount d x := by
  unfold falseCount
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro v hv
  let z := A.value x v
  change (∑ p ∈ pool, if z ≠ 0 ∧ ((d * p : ℕ) : ℤ) ∣ z then 1 else 0) ≤
    lam * (if z ≠ 0 ∧ (d : ℤ) ∣ z then 1 else 0)
  by_cases hz : z = 0
  · simp [z, hz]
  by_cases hd : (d : ℤ) ∣ z
  · rw [if_pos ⟨hz, hd⟩, mul_one]
    calc
      _ ≤ ∑ p ∈ pool, if (p : ℤ) ∣ z then 1 else 0 := by
        apply Finset.sum_le_sum
        intro p hp
        split_ifs with hdp hpz
        · omega
        · exfalso
          exact hpz (dvd_trans (by exact ⟨(d : ℤ), by simp [mul_comm]⟩) hdp.2)
        · omega
        · omega
      _ = (pool.filter (fun p : ℕ => (p : ℤ) ∣ z)).card := by simp
      _ ≤ lam := hdiv x v hv hz
  · have hnone : ∀ p : ℕ, ¬(z ≠ 0 ∧ ((d * p : ℕ) : ℤ) ∣ z) := by
      intro p hdp
      apply hd
      exact dvd_trans (by exact ⟨(p : ℤ), by simp⟩) hdp.2
    rw [if_neg (by exact fun h => hd h.2), mul_zero]
    exact le_of_eq (Finset.sum_eq_zero (fun p hp => if_neg (hnone p)))

theorem sum_falseMass_le (active : Finset X) (pool : Finset ℕ) (lam d : ℕ)
    (hdiv : A.DivisorBound pool lam) :
    (∑ p ∈ pool, A.falseMass active (d * p)) ≤ lam * A.falseMass active d := by
  unfold falseMass
  rw [Finset.sum_comm, Finset.mul_sum]
  exact Finset.sum_le_sum (fun x hx => A.sum_falseCount_le pool lam d x hdiv)

theorem totalCount_eq (active : Finset X) (d : ℕ) :
    A.totalCount active d = (∑ x ∈ active, A.trueCount x) + A.falseMass active d := by
  simp only [totalCount, modCount_eq, Finset.sum_add_distrib, falseMass]

/-- One common candidate minimizes actual count totals over all incidences. -/
noncomputable def greedyPrime (active : Finset X) (pool : Finset ℕ)
    (hne : pool.Nonempty) (d : ℕ) : ℕ :=
  Classical.choose (pool.exists_min_image (fun p => A.totalCount active (d * p)) hne)

theorem greedyPrime_spec (active : Finset X) (pool : Finset ℕ)
    (hne : pool.Nonempty) (d : ℕ) :
    A.greedyPrime active pool hne d ∈ pool ∧
      ∀ p ∈ pool, A.totalCount active (d * A.greedyPrime active pool hne d) ≤
        A.totalCount active (d * p) :=
  Classical.choose_spec (pool.exists_min_image (fun p => A.totalCount active (d * p)) hne)

/-- Greedy contraction is a theorem of the actual tables, not an oracle axiom. -/
theorem greedy_contraction (active : Finset X) (pool : Finset ℕ)
    (hne : pool.Nonempty) (lam d : ℕ) (hdiv : A.DivisorBound pool lam) :
    pool.card * A.falseMass active (d * A.greedyPrime active pool hne d) ≤
      lam * A.falseMass active d := by
  have hmin := (A.greedyPrime_spec active pool hne d).2
  have hfalse : ∀ p ∈ pool,
      A.falseMass active (d * A.greedyPrime active pool hne d) ≤
        A.falseMass active (d * p) := by
    intro p hp
    have hm := hmin p hp
    simp only [A.totalCount_eq] at hm
    omega
  calc
    _ = ∑ _p ∈ pool, A.falseMass active (d * A.greedyPrime active pool hne d) := by
      simp
    _ ≤ ∑ p ∈ pool, A.falseMass active (d * p) := Finset.sum_le_sum hfalse
    _ ≤ _ := A.sum_falseMass_le active pool lam d hdiv

/-- Each incidence takes its own last-round minimum; the earlier prime
selection is common to all incidences. -/
noncomputable def minCount (pool : Finset ℕ) (hne : pool.Nonempty) (d : ℕ) (x : X) : ℕ :=
  (pool.image (fun p => A.modCount (d * p) x)).min' (hne.image _)

theorem minCount_le (pool : Finset ℕ) (hne : pool.Nonempty) (d : ℕ) (x : X)
    {p : ℕ} (hp : p ∈ pool) : A.minCount pool hne d x ≤ A.modCount (d * p) x := by
  exact Finset.min'_le _ _ (Finset.mem_image_of_mem _ hp)

theorem trueCount_le_min (pool : Finset ℕ) (hne : pool.Nonempty) (d : ℕ) (x : X) :
    A.trueCount x ≤ A.minCount pool hne d x := by
  obtain ⟨p, hp, heq⟩ := Finset.mem_image.mp
    (Finset.min'_mem (pool.image (fun p => A.modCount (d * p) x)) (hne.image _))
  unfold minCount
  rw [← heq]
  exact A.trueCount_le (d * p) x

theorem zero_min_sound (pool : Finset ℕ) (hne : pool.Nonempty) (d : ℕ) (x : X)
    (hzero : A.minCount pool hne d x = 0) : A.trueCount x = 0 := by
  have h := A.trueCount_le_min pool hne d x
  omega

theorem minCount_sum_le (pool : Finset ℕ) (hne : pool.Nonempty) (d : ℕ) (x : X) :
    pool.card * A.minCount pool hne d x ≤ ∑ p ∈ pool, A.modCount (d * p) x := by
  calc
    _ = ∑ _p ∈ pool, A.minCount pool hne d x := by simp
    _ ≤ _ := Finset.sum_le_sum (fun p hp => A.minCount_le pool hne d x hp)

/-- The strict affirmative test cannot certify a zero-free block. -/
theorem yes_test_sound (pool : Finset ℕ) (hne : pool.Nonempty) (lam d : ℕ) (x : X)
    (hdiv : A.DivisorBound pool lam)
    (hyes : lam * A.modCount d x < pool.card * A.minCount pool hne d x) :
    0 < A.trueCount x := by
  by_contra hn
  have hz : A.trueCount x = 0 := by omega
  have hc : ∀ e, A.modCount e x = A.falseCount e x := by
    intro e
    simp [A.modCount_eq, hz]
  have hmin := A.minCount_sum_le pool hne d x
  simp only [hc] at hmin hyes
  have havg := A.sum_falseCount_le pool lam d x hdiv
  omega

/-- An uncertified incidence consumes false mass even when it is genuine. -/
theorem uncertified_leak (pool : Finset ℕ) (hne : pool.Nonempty) (lam d : ℕ) (x : X)
    (hM : lam < pool.card) (hpositive : A.minCount pool hne d x ≠ 0)
    (hfail : pool.card * A.minCount pool hne d x ≤ lam * A.modCount d x) :
    pool.card - lam ≤ lam * A.falseCount d x := by
  have hlow := A.trueCount_le_min pool hne d x
  rw [A.modCount_eq] at hfail
  by_cases hz : A.trueCount x = 0
  · simp only [hz, zero_add] at hfail
    have hm : 1 ≤ A.minCount pool hne d x := by omega
    have hm' : pool.card ≤ pool.card * A.minCount pool hne d x := by
      simpa using Nat.mul_le_mul_left pool.card hm
    exact (Nat.sub_le _ _).trans (hm'.trans hfail)
  · have hZ : 1 ≤ A.trueCount x := by omega
    have hsub : pool.card - lam + lam = pool.card := Nat.sub_add_cancel hM.le
    nlinarith

noncomputable def certified (active : Finset X) (pool : Finset ℕ) (hne : pool.Nonempty)
    (lam d : ℕ) : Finset X :=
  active.filter (fun x => lam * A.modCount d x < pool.card * A.minCount pool hne d x)

noncomputable def markedAfter (pair : X → Pair) (marked : Finset Pair)
    (incidences : Finset X) (pool : Finset ℕ) (hne : pool.Nonempty) (lam d : ℕ) : Finset Pair :=
  marked ∪ (A.certified incidences pool hne lam d).image pair

/-- Restart survivors include uncertified true incidences. -/
noncomputable def survivors (pair : X → Pair) (marked : Finset Pair) (active : Finset X)
    (pool : Finset ℕ) (hne : pool.Nonempty) (lam d : ℕ) : Finset X :=
  active.filter (fun x => A.minCount pool hne d x ≠ 0 ∧
    pool.card * A.minCount pool hne d x ≤ lam * A.modCount d x ∧
    pair x ∉ A.markedAfter pair marked active pool hne lam d)

theorem survivor_subset (pair : X → Pair) (marked : Finset Pair) (active : Finset X)
    (pool : Finset ℕ) (hne : pool.Nonempty) (lam d : ℕ) :
    A.survivors pair marked active pool hne lam d ⊆ active := Finset.filter_subset _ _

theorem true_incidence_retained (pair : X → Pair) (marked : Finset Pair)
    (active : Finset X) (pool : Finset ℕ) (hne : pool.Nonempty) (lam d : ℕ)
    {x : X} (hx : x ∈ active) (hz : 0 < A.trueCount x)
    (hunmarked : pair x ∉ A.markedAfter pair marked active pool hne lam d) :
    x ∈ A.survivors pair marked active pool hne lam d := by
  apply Finset.mem_filter.mpr
  refine ⟨hx, ?_, ?_, hunmarked⟩
  · have h := A.trueCount_le_min pool hne d x
    omega
  · by_contra h
    have hcert : x ∈ A.certified active pool hne lam d :=
      Finset.mem_filter.mpr ⟨hx, by omega⟩
    exact hunmarked (Finset.mem_union_right _ (Finset.mem_image_of_mem pair hcert))

theorem survivor_card_leak (pair : X → Pair) (marked : Finset Pair)
    (active : Finset X) (pool : Finset ℕ) (hne : pool.Nonempty) (lam d : ℕ)
    (hM : lam < pool.card) :
    (pool.card - lam) * (A.survivors pair marked active pool hne lam d).card ≤
      lam * A.falseMass active d := by
  let s := A.survivors pair marked active pool hne lam d
  have hs : s ⊆ active := A.survivor_subset pair marked active pool hne lam d
  calc
    _ = ∑ _x ∈ s, (pool.card - lam) := by simp [s, mul_comm]
    _ ≤ ∑ x ∈ s, lam * A.falseCount d x := by
      apply Finset.sum_le_sum
      intro x hx
      obtain ⟨_, hp, hf, _⟩ := Finset.mem_filter.mp hx
      exact A.uncertified_leak pool hne lam d x hM hp hf
    _ ≤ ∑ x ∈ active, lam * A.falseCount d x :=
      Finset.sum_le_sum_of_subset_of_nonneg hs (fun _ _ _ => Nat.zero_le _)
    _ = _ := by simp [falseMass, Finset.mul_sum]

/-- A trace of the specified common-prime algorithm. Each selected prime
is erased before the next round, and every round uses a genuine minimizer. -/
inductive GreedyTrace (active : Finset X) (initial : Finset ℕ) :
    ℕ → ℕ → Finset ℕ → Prop
  | start : GreedyTrace active initial 0 1 initial
  | step {k d available} (previous : GreedyTrace active initial k d available)
      (hne : available.Nonempty) :
      GreedyTrace active initial (k + 1)
        (d * A.greedyPrime active available hne d)
        (available.erase (A.greedyPrime active available hne d))

theorem trace_subset (active : Finset X) (initial : Finset ℕ)
    {k d : ℕ} {available : Finset ℕ}
    (tr : A.GreedyTrace active initial k d available) : available ⊆ initial := by
  induction tr with
  | start => exact Finset.Subset.refl _
  | step previous hne ih => exact (Finset.erase_subset _ _).trans ih

theorem trace_card (active : Finset X) (initial : Finset ℕ)
    {k d : ℕ} {available : Finset ℕ}
    (tr : A.GreedyTrace active initial k d available) : available.card + k = initial.card := by
  induction tr with
  | start => simp
  | @step k d available previous hne ih =>
      have hp := (A.greedyPrime_spec active available hne d).1
      have hc := Finset.card_erase_add_one hp
      omega

/-- The finite algorithm can perform every requested round below pool size. -/
theorem greedyTrace_exists (active : Finset X) (initial : Finset ℕ) (k : ℕ)
    (hk : k ≤ initial.card) : ∃ d available, A.GreedyTrace active initial k d available := by
  induction k with
  | zero => exact ⟨1, initial, GreedyTrace.start⟩
  | succ k ih =>
      obtain ⟨d, available, tr⟩ := ih (by omega)
      have hc := A.trace_card active initial tr
      have hne : available.Nonempty := Finset.card_pos.mp (by omega)
      exact ⟨_, _, GreedyTrace.step tr hne⟩

/-- Integer cross-multiplication avoids any division or logarithm in the
multi-round contraction. `M` is a lower bound on each remaining pool. -/
theorem trace_contraction (active : Finset X) (initial : Finset ℕ)
    {k d : ℕ} {available : Finset ℕ}
    (tr : A.GreedyTrace active initial k d available) (M lam : ℕ)
    (hsize : M + k ≤ initial.card) (hdiv : A.DivisorBound initial lam) :
    M ^ k * A.falseMass active d ≤ lam ^ k * A.falseMass active 1 := by
  induction tr with
  | start => simp
  | @step k d available previous hne ih =>
      have hprev := ih (by omega)
      have hc := A.trace_card active initial previous
      have hm : M ≤ available.card := by omega
      have hb := A.divisorBound_subset hdiv (A.trace_subset active initial previous)
      have hg := A.greedy_contraction active available hne lam d hb
      have hs : M * A.falseMass active (d * A.greedyPrime active available hne d) ≤
          lam * A.falseMass active d :=
        (Nat.mul_le_mul_right _ hm).trans hg
      calc
        _ = M ^ k * (M * A.falseMass active (d * A.greedyPrime active available hne d)) := by
          rw [pow_succ]; ring
        _ ≤ M ^ k * (lam * A.falseMass active d) := Nat.mul_le_mul_left _ hs
        _ = lam * (M ^ k * A.falseMass active d) := by ring
        _ ≤ lam * (lam ^ k * A.falseMass active 1) := Nat.mul_le_mul_left _ hprev
        _ = _ := by rw [pow_succ]; ring

theorem trace_modulus_le (active : Finset X) (initial : Finset ℕ)
    {k d : ℕ} {available : Finset ℕ}
    (tr : A.GreedyTrace active initial k d available) (upper : ℕ)
    (hupper : ∀ p ∈ initial, p ≤ upper) : d ≤ upper ^ k := by
  induction tr with
  | start => simp
  | @step k d available previous hne ih =>
      have hp := (A.greedyPrime_spec active available hne d).1
      have hpu := hupper _ (A.trace_subset active initial previous hp)
      simpa [pow_succ] using Nat.mul_le_mul ih hpu

/-- An unused prime is coprime to the selected modulus. This supplies the
distinct-prime condition needed when a client splits folded and cyclic
factors; it does not assume a field structure for the coefficient ring. -/
theorem trace_coprime_remaining (active : Finset X) (initial : Finset ℕ)
    {k d : ℕ} {available : Finset ℕ}
    (tr : A.GreedyTrace active initial k d available)
    (hprime : ∀ p ∈ initial, Nat.Prime p) :
    ∀ p ∈ available, Nat.Coprime d p := by
  induction tr with
  | start => intro p hp; simp
  | @step k d available previous hne ih =>
      intro p hp
      obtain ⟨hnep, hp⟩ := Finset.mem_erase.mp hp
      have hg := (A.greedyPrime_spec active available hne d).1
      have hgp := hprime _ (A.trace_subset active initial previous hg)
      have hpp := hprime _ (A.trace_subset active initial previous hp)
      exact Nat.coprime_mul_iff_left.mpr ⟨ih p hp,
        (Nat.coprime_primes hgp hpp).mpr hnep.symm⟩

theorem candidate_modulus_le (active : Finset X) (initial : Finset ℕ)
    {k d : ℕ} {available : Finset ℕ}
    (tr : A.GreedyTrace active initial k d available) (upper : ℕ)
    (hupper : ∀ p ∈ initial, p ≤ upper) {p : ℕ} (hp : p ∈ available) :
    d * p ≤ upper ^ (k + 1) := by
  have hd := A.trace_modulus_le active initial tr upper hupper
  have hp' := hupper p (A.trace_subset active initial tr hp)
  simpa [pow_succ] using Nat.mul_le_mul hd hp'

/-- The familiar `a ≤ 1/2` and `h*a^R ≤ 1/4` sufficient conditions,
written with integers and with `R = k+1`. -/
theorem stage_rate_of_quarter (k M lam h : ℕ) (hhalf : 2 * lam ≤ M)
    (hquarter : 4 * h * lam ^ (k + 1) ≤ M ^ (k + 1)) :
    2 * h * lam ^ (k + 1) ≤ (M - lam) * M ^ k := by
  have hgap : M ≤ 2 * (M - lam) := by omega
  have hg := Nat.mul_le_mul_right (M ^ k) hgap
  simp only [pow_succ] at hquarter ⊢
  nlinarith

/-- The explicit finite stage condition implies halving of all survivors,
including genuine incidences that failed the strict affirmative test. -/
theorem stage_halves (pair : X → Pair) (marked : Finset Pair) (active : Finset X)
    (initial : Finset ℕ) {k d : ℕ} {available : Finset ℕ}
    (tr : A.GreedyTrace active initial k d available) (hne : available.Nonempty)
    (M lam h : ℕ) (hM : lam < M) (hsize : M + k ≤ initial.card)
    (hdiv : A.DivisorBound initial lam)
    (hblock : ∀ x ∈ active, (A.block x).card ≤ h)
    (hrate : 2 * h * lam ^ (k + 1) ≤ (M - lam) * M ^ k) :
    2 * (A.survivors pair marked active available hne lam d).card ≤ active.card := by
  let s := (A.survivors pair marked active available hne lam d).card
  have hc := A.trace_card active initial tr
  have hm : M ≤ available.card := by omega
  have hm' : lam < available.card := by omega
  have hl := A.survivor_card_leak pair marked active available hne lam d hm'
  have hl' : (M - lam) * s ≤ lam * A.falseMass active d :=
    (Nat.mul_le_mul_right s (Nat.sub_le_sub_right hm lam)).trans hl
  have ht := A.trace_contraction active initial tr M lam hsize hdiv
  have hb := A.falseMass_le active 1 h hblock
  have ht' := ht.trans (Nat.mul_le_mul_left (lam ^ k) hb)
  have hden : 0 < (M - lam) * M ^ k := by
    exact Nat.mul_pos (Nat.sub_pos_of_lt hM) (pow_pos (by omega) _)
  apply Nat.le_of_mul_le_mul_left (c := (M - lam) * M ^ k) ?_ hden
  calc
    _ = 2 * M ^ k * ((M - lam) * s) := by ring
    _ ≤ 2 * M ^ k * (lam * A.falseMass active d) := Nat.mul_le_mul_left _ hl'
    _ = 2 * lam * (M ^ k * A.falseMass active d) := by ring
    _ ≤ 2 * lam * (lam ^ k * (h * active.card)) := Nat.mul_le_mul_left _ ht'
    _ = (2 * h * lam ^ (k + 1)) * active.card := by rw [pow_succ]; ring
    _ ≤ _ := Nat.mul_le_mul_right active.card hrate

/-- Genuine witnesses are checked against the original signed integer sum. -/
theorem trueCount_pos_iff (x : X) :
    0 < A.trueCount x ↔ ∃ v ∈ A.block x, A.value x v = 0 := by
  have heq : A.trueCount x = ((A.block x).filter (fun v => A.value x v = 0)).card := by
    simp [trueCount]
  rw [heq, Finset.card_pos]
  exact Finset.filter_nonempty_iff

def exactPairs (pair : X → Pair) (initial : Finset X) : Finset Pair :=
  (initial.filter (fun x => 0 < A.trueCount x)).image pair

theorem mem_exactPairs_iff (pair : X → Pair) (initial : Finset X) (q : Pair) :
    q ∈ A.exactPairs pair initial ↔
      ∃ x ∈ initial, pair x = q ∧ ∃ v ∈ A.block x, A.value x v = 0 := by
  simp only [exactPairs, Finset.mem_image, Finset.mem_filter, A.trueCount_pos_iff]
  aesop

/-- The invariant needed across restarts. A true incidence either remains
active or has its pair already soundly certified. -/
def StateInvariant (pair : X → Pair) (initial active : Finset X)
    (marked : Finset Pair) : Prop :=
  active ⊆ initial ∧ marked ⊆ A.exactPairs pair initial ∧
    ∀ x ∈ initial, 0 < A.trueCount x → pair x ∈ marked ∨ x ∈ active

theorem initial_invariant (pair : X → Pair) (initial : Finset X) :
    A.StateInvariant pair initial initial ∅ := by
  exact ⟨Finset.Subset.refl _, Finset.empty_subset _, fun x hx hz => Or.inr hx⟩

theorem stage_invariant (pair : X → Pair) (initial active : Finset X)
    (marked : Finset Pair) (pool : Finset ℕ) (hne : pool.Nonempty) (lam d : ℕ)
    (hinv : A.StateInvariant pair initial active marked) (hdiv : A.DivisorBound pool lam) :
    A.StateInvariant pair initial (A.survivors pair marked active pool hne lam d)
      (A.markedAfter pair marked active pool hne lam d) := by
  obtain ⟨hsub, hsound, hkeep⟩ := hinv
  refine ⟨(A.survivor_subset pair marked active pool hne lam d).trans hsub, ?_, ?_⟩
  · intro q hq
    obtain hq | hq := Finset.mem_union.mp hq
    · exact hsound hq
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hq
      obtain ⟨hx, hyes⟩ := Finset.mem_filter.mp hx
      exact Finset.mem_image_of_mem pair (Finset.mem_filter.mpr
        ⟨hsub hx, A.yes_test_sound pool hne lam d x hdiv hyes⟩)
  · intro x hx hz
    obtain hm | ha := hkeep x hx hz
    · exact Or.inl (Finset.mem_union_left _ hm)
    · by_cases hm : pair x ∈ A.markedAfter pair marked active pool hne lam d
      · exact Or.inl hm
      · exact Or.inr (A.true_incidence_retained pair marked active pool hne lam d ha hz hm)

/-- After any number of valid restarts, scanning each surviving block's
original sums gives exactly all affirmative pairs. -/
theorem final_exact_scan (pair : X → Pair) (initial active : Finset X)
    (marked : Finset Pair) (hinv : A.StateInvariant pair initial active marked) :
    marked ∪ A.exactPairs pair active = A.exactPairs pair initial := by
  obtain ⟨hsub, hsound, hkeep⟩ := hinv
  apply Finset.Subset.antisymm
  · intro q hq
    obtain hq | hq := Finset.mem_union.mp hq
    · exact hsound hq
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hq
      obtain ⟨hx, hz⟩ := Finset.mem_filter.mp hx
      exact Finset.mem_image_of_mem pair (Finset.mem_filter.mpr ⟨hsub hx, hz⟩)
  · intro q hq
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨hx, hz⟩ := Finset.mem_filter.mp hx
    obtain hm | ha := hkeep x hx hz
    · exact Finset.mem_union_left _ hm
    · exact Finset.mem_union_right _ (Finset.mem_image_of_mem pair
        (Finset.mem_filter.mpr ⟨ha, hz⟩))

/-- A complete stage exists under explicit finite numerical conditions.
It starts afresh at modulus one, selects `k` distinct common primes, and
uses the remaining candidates for the final per-incidence tests. -/
theorem certification_stage_exists (pair : X → Pair) (initial active : Finset X)
    (marked : Finset Pair) (pool : Finset ℕ) (k M lam h : ℕ)
    (hinv : A.StateInvariant pair initial active marked)
    (hM : lam < M) (hsize : M + k ≤ pool.card)
    (hdiv : A.DivisorBound pool lam)
    (hblock : ∀ x ∈ initial, (A.block x).card ≤ h)
    (hrate : 2 * h * lam ^ (k + 1) ≤ (M - lam) * M ^ k) :
    ∃ d : ℕ, ∃ available : Finset ℕ, ∃ hne : available.Nonempty,
      A.GreedyTrace active pool k d available ∧
      A.StateInvariant pair initial (A.survivors pair marked active available hne lam d)
        (A.markedAfter pair marked active available hne lam d) ∧
      2 * (A.survivors pair marked active available hne lam d).card ≤ active.card := by
  obtain ⟨d, available, tr⟩ := A.greedyTrace_exists active pool k (by omega)
  have hc := A.trace_card active pool tr
  have hne : available.Nonempty := Finset.card_pos.mp (by omega)
  have hsmall := A.divisorBound_subset hdiv (A.trace_subset active pool tr)
  refine ⟨d, available, hne, tr, A.stage_invariant pair initial active marked available hne
    lam d hinv hsmall, ?_⟩
  exact A.stage_halves pair marked active pool tr hne M lam h hM hsize hdiv
    (fun x hx => hblock x (hinv.1 hx)) hrate

/-- Repeating the fully proved stage gives geometric shrinkage, while the
same prime pool is reused only after restarting the modulus at one. -/
theorem deterministic_restarts (pair : X → Pair) (initial : Finset X)
    (pool : Finset ℕ) (k M lam h stages : ℕ)
    (hM : lam < M) (hsize : M + k ≤ pool.card)
    (hdiv : A.DivisorBound pool lam)
    (hblock : ∀ x ∈ initial, (A.block x).card ≤ h)
    (hrate : 2 * h * lam ^ (k + 1) ≤ (M - lam) * M ^ k) :
    ∃ active marked, A.StateInvariant pair initial active marked ∧
      2 ^ stages * active.card ≤ initial.card ∧
      marked ∪ A.exactPairs pair active = A.exactPairs pair initial := by
  induction stages with
  | zero =>
      refine ⟨initial, ∅, A.initial_invariant pair initial, ?_, ?_⟩
      · simp
      · simp
  | succ stages ih =>
      obtain ⟨active, marked, hinv, hcard, hscan⟩ := ih
      obtain ⟨d, available, hne, tr, hinv', hhalf⟩ :=
        A.certification_stage_exists pair initial active marked pool k M lam h hinv hM
          hsize hdiv hblock hrate
      refine ⟨_, _, hinv', ?_, A.final_exact_scan pair initial _ _ hinv'⟩
      calc
        _ = 2 ^ stages * (2 * (A.survivors pair marked active available hne lam d).card) := by
          rw [pow_succ]; ring
        _ ≤ 2 ^ stages * active.card := Nat.mul_le_mul_left _ hhalf
        _ ≤ _ := hcard

/-- A public entry point derives the divisor assumption from primality and
bounded original integer sums, then runs any number of valid restarts. -/
theorem certification_from_primes (pair : X → Pair) (initial : Finset X)
    (pool : Finset ℕ) (P U k M lam h stages : ℕ)
    (hprime : ∀ p ∈ pool, Nat.Prime p) (hlower : ∀ p ∈ pool, P ≤ p)
    (hP : 1 ≤ P) (hmag : ∀ x v, v ∈ A.block x → (A.value x v).natAbs ≤ U)
    (hpower : U < P ^ (lam + 1))
    (hM : lam < M) (hsize : M + k ≤ pool.card)
    (hblock : ∀ x ∈ initial, (A.block x).card ≤ h)
    (hrate : 2 * h * lam ^ (k + 1) ≤ (M - lam) * M ^ k) :
    ∃ active marked, A.StateInvariant pair initial active marked ∧
      2 ^ stages * active.card ≤ initial.card ∧
      marked ∪ A.exactPairs pair active = A.exactPairs pair initial := by
  exact A.deterministic_restarts pair initial pool k M lam h stages hM hsize
    (A.divisorBound_of_prime_power pool P U lam hprime hlower hP hmag hpower) hblock hrate

/-- Number of original-sum tests in the terminal scan. -/
def scanWork (active : Finset X) : ℕ := ∑ x ∈ active, (A.block x).card

theorem scanWork_le (active : Finset X) (h : ℕ)
    (hblock : ∀ x ∈ active, (A.block x).card ≤ h) :
    A.scanWork active ≤ h * active.card := by
  calc
    _ ≤ ∑ _x ∈ active, h := Finset.sum_le_sum hblock
    _ = _ := by simp [mul_comm]

/-- Converts the restart cardinality certificate into an explicit terminal
scan budget. An asymptotic client supplies its desired number of stages. -/
theorem final_scan_budget (initial active : Finset X) (h stages budget : ℕ)
    (hsub : active ⊆ initial) (hblock : ∀ x ∈ initial, (A.block x).card ≤ h)
    (hcard : 2 ^ stages * active.card ≤ initial.card)
    (hbudget : h * initial.card ≤ 2 ^ stages * budget) : A.scanWork active ≤ budget := by
  apply Nat.le_of_mul_le_mul_left (c := 2 ^ stages) ?_ (pow_pos (by omega) _)
  calc
    _ ≤ 2 ^ stages * (h * active.card) := Nat.mul_le_mul_left _
      (A.scanWork_le active h (fun x hx => hblock x (hsub hx)))
    _ = h * (2 ^ stages * active.card) := by ring
    _ ≤ h * initial.card := Nat.mul_le_mul_left _ hcard
    _ ≤ _ := hbudget

/-- The finite end-to-end statement: all outputs concern original integer
zeros, and the remaining original-sum scan fits the supplied budget. -/
theorem certification_with_budget (pair : X → Pair) (initial : Finset X)
    (pool : Finset ℕ) (P U k M lam h stages budget : ℕ)
    (hprime : ∀ p ∈ pool, Nat.Prime p) (hlower : ∀ p ∈ pool, P ≤ p)
    (hP : 1 ≤ P) (hmag : ∀ x v, v ∈ A.block x → (A.value x v).natAbs ≤ U)
    (hpower : U < P ^ (lam + 1))
    (hM : lam < M) (hsize : M + k ≤ pool.card)
    (hblock : ∀ x ∈ initial, (A.block x).card ≤ h)
    (hrate : 2 * h * lam ^ (k + 1) ≤ (M - lam) * M ^ k)
    (hbudget : h * initial.card ≤ 2 ^ stages * budget) :
    ∃ active marked, A.scanWork active ≤ budget ∧
      ∀ q, q ∈ marked ∪ A.exactPairs pair active ↔
        ∃ x ∈ initial, pair x = q ∧ ∃ v ∈ A.block x, A.value x v = 0 := by
  obtain ⟨active, marked, hinv, hcard, hexact⟩ :=
    A.certification_from_primes pair initial pool P U k M lam h stages hprime hlower hP hmag
      hpower hM hsize hblock hrate
  refine ⟨active, marked, A.final_scan_budget initial active h stages budget hinv.1
    hblock hcard hbudget, ?_⟩
  intro q
  rw [hexact]
  exact A.mem_exactPairs_iff pair initial q

/-- Enumerating every candidate, including the final certification round,
uses at most this many exact-table calls per stage. This is only a finite
call-count bound; no running-time implementation is hidden in it. -/
theorem candidate_calls_le (pool : Finset ℕ) (k : ℕ) :
    (∑ j ∈ Finset.range (k + 1), (pool.card - j)) ≤ (k + 1) * pool.card := by
  calc
    _ ≤ ∑ _j ∈ Finset.range (k + 1), pool.card :=
      Finset.sum_le_sum (fun j hj => Nat.sub_le _ _)
    _ = _ := by simp

end Instance

end ThinMatrix.CompositeCertification

#print axioms ThinMatrix.CompositeCertification.Instance.prime_divisor_card_le
#print axioms ThinMatrix.CompositeCertification.Instance.greedy_contraction
#print axioms ThinMatrix.CompositeCertification.Instance.stage_halves
#print axioms ThinMatrix.CompositeCertification.Instance.trace_coprime_remaining
#print axioms ThinMatrix.CompositeCertification.Instance.stage_rate_of_quarter
#print axioms ThinMatrix.CompositeCertification.Instance.certification_from_primes
#print axioms ThinMatrix.CompositeCertification.Instance.certification_with_budget
#print axioms ThinMatrix.CompositeCertification.Instance.final_exact_scan
#print axioms ThinMatrix.CompositeCertification.Instance.final_scan_budget
