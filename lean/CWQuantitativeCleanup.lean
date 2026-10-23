import CWFilteredHashCounts

set_option autoImplicit false

namespace ThinMatrix.CWQuantitativeCleanup
open scoped BigOperators
open CWBlockWords CWHashFibers CWPrimeHashCounts CWFilteredHashCounts

def allCollisions (n : ℕ) (reference : Word n) :=
  FiniteCollisionCleanup.collisions (fullClass n reference) (wx n) (wy n) (wz n)

variable (M : ℕ) [Fact (Nat.Prime M)]
def filteredCollisions (n : ℕ) (reference : Word n) (B : Finset (ZMod M)) (r : Sample (ZMod M) n) :=
  FiniteCollisionCleanup.collisions (filtered M n reference B r) (wx n) (wy n) (wz n)
def survivors (n : ℕ) (reference : Word n) (B : Finset (ZMod M)) (r : Sample (ZMod M) n) :=
  CWHashedCandidates.kept n reference r.1 r.2.1 r.2.2 B

theorem collision_subset (n : ℕ) (reference : Word n) (B : Finset (ZMod M)) (r : Sample (ZMod M) n) :
    filteredCollisions M n reference B r⊆allCollisions n reference := by
  intro p hp
  obtain ⟨hp,hne,hs⟩ := Finset.mem_filter.mp hp
  obtain ⟨hu,hv⟩ := Finset.mem_product.mp hp
  exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
    ⟨filtered_subset M n reference B r hu,filtered_subset M n reference B r hv⟩,hne,hs⟩

theorem collision_samples_card (hM : 2<M) (n : ℕ) (reference : Word n)
    (B : Finset (ZMod M)) (hB : ThreeAPFree (B : Set (ZMod M)))
    (p : Word n×Word n) (hp : p ∈ allCollisions n reference) :
    Fintype.card {r : Sample (ZMod M) n // p ∈ filteredCollisions M n reference B r}=B.card*M^(n-1) := by
  obtain ⟨hp,hne,hs⟩ := Finset.mem_filter.mp hp
  obtain ⟨hu,hv⟩ := Finset.mem_product.mp hp
  have he (r : Sample (ZMod M) n) : p ∈ filteredCollisions M n reference B r ↔
      p.1 ∈ filtered M n reference B r ∧ p.2 ∈ filtered M n reference B r := by
    simp [filteredCollisions,FiniteCollisionCleanup.collisions,hne,hs]
  rw [Fintype.card_congr (Equiv.subtypeEquivRight he)]
  exact pair_samples_card M hM n reference p.1 p.2 hu hv hne hs B hB

theorem candidate_sum (hM : 2<M) (n : ℕ) (reference : Word n)
    (B : Finset (ZMod M)) (hB : ThreeAPFree (B : Set (ZMod M))) :
    (∑ r : Sample (ZMod M) n,(filtered M n reference B r).card)=
      (fullClass n reference).card*B.card*M^n := by
  rw [FiniteFiberCounting.transpose_card (fullClass n reference) (filtered M n reference B)
    (filtered_subset M n reference B)]
  calc
    _ = ∑ _u ∈ fullClass n reference,B.card*M^n := by
      apply Finset.sum_congr rfl
      intro u hu
      exact candidate_samples_card M hM n reference u hu B hB
    _ = _ := by simp [mul_assoc]

theorem collision_sum (hM : 2<M) (n : ℕ) (reference : Word n)
    (B : Finset (ZMod M)) (hB : ThreeAPFree (B : Set (ZMod M))) :
    (∑ r : Sample (ZMod M) n,(filteredCollisions M n reference B r).card)=
      (allCollisions n reference).card*B.card*M^(n-1) := by
  rw [FiniteFiberCounting.transpose_card (allCollisions n reference) (filteredCollisions M n reference B)
    (collision_subset M n reference B)]
  calc
    _ = ∑ _p ∈ allCollisions n reference,B.card*M^(n-1) := by
      apply Finset.sum_congr rfl
      intro p hp
      exact collision_samples_card M hM n reference B hB p hp
    _ = _ := by simp [mul_assoc]

/-- A quantitative bound on the actual symmetric cleanup, valid also at n=0.
All quantities are cardinalities; no execution-cost claim is made. -/
theorem exists_survivors (hM : 2<M) (n : ℕ) (reference : Word n)
    (B : Finset (ZMod M)) (hB : ThreeAPFree (B : Set (ZMod M))) :
    ∃ r : Sample (ZMod M) n,
      M^(n+2)*(survivors M n reference B r).card+
        (allCollisions n reference).card*B.card*M^(n-1) ≥
        (fullClass n reference).card*B.card*M^n := by
  letI : Nonempty (Sample (ZMod M) n) := Fintype.card_pos_iff.mp (by
    rw [random_space_card]
    exact pow_pos (by omega) _)
  obtain ⟨r,hr⟩ := FiniteFiberCounting.exists_survival
    (fun r : Sample (ZMod M) n => (filtered M n reference B r).card)
    (fun r => (survivors M n reference B r).card)
    (fun r => (filteredCollisions M n reference B r).card)
    (fun r => FiniteCollisionCleanup.retained_card (filtered M n reference B r) (wx n) (wy n) (wz n))
  rw [random_space_card,collision_sum M hM n reference B hB,candidate_sum M hM n reference B hB] at hr
  exact ⟨r,hr⟩

#print axioms collision_subset
#print axioms collision_samples_card
#print axioms candidate_sum
#print axioms collision_sum
#print axioms exists_survivors
end ThinMatrix.CWQuantitativeCleanup
