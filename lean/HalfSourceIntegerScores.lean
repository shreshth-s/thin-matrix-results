import HalfSourceList

set_option autoImplicit false

/-!
# Shared-denominator exact greedy scores

All characters in a conditional score share denominator 2*(A*B)^K.
Numerators are natural numbers; summation never multiplies denominators.
The exponent window is K=64*m^3+1, covering both neighbors of every
character sum during list construction. This file proves score refinement
and preserves the strict comparison (false on a tie). It does not yet claim
a binary execution bound for constructing the entire translation list.
-/
namespace ThinMatrix.HalfSourceIntegerScores
open ThinMatrix.WalshEmbedding ThinMatrix.HalfSourceGreedy ThinMatrix.HalfSourceList
open scoped BigOperators

def A (m : ℕ) : ℕ := 4*m+1
def B (m : ℕ) : ℕ := 4*m
def K (m : ℕ) : ℕ := 64*m^3+1
def denominator (m : ℕ) : ℕ := (A m * B m)^K m

def powerNumerator (m : ℕ) (t : ℤ) : ℕ :=
  A m ^ ((K m:ℤ)+t).toNat * B m ^ ((K m:ℤ)-t).toNat

theorem denominator_pos (m : ℕ) (hm : 0 < m) : 0 < denominator m := by
  unfold denominator A B
  positivity

theorem rationalBase_eq (m : ℕ) (hm : 0 < m) :
    rationalBase m = (A m:ℚ)/(B m:ℚ) := by
  have hm0 : (m:ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
  simp only [rationalBase, A, B, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
  field_simp

theorem powerNumerator_eq (m : ℕ) (hm : 0 < m) (t : ℤ)
    (ht : -(K m:ℤ) ≤ t ∧ t ≤ K m) :
    (powerNumerator m t:ℚ) = rationalBase m ^ t * (denominator m:ℚ) := by
  have ha : (A m:ℚ) ≠ 0 := by unfold A; positivity
  have hb : (B m:ℚ) ≠ 0 := by unfold B; positivity
  have hp : 0 ≤ (K m:ℤ)+t := by omega
  have hn : 0 ≤ (K m:ℤ)-t := by omega
  simp only [powerNumerator, denominator, Nat.cast_mul, Nat.cast_pow, rationalBase_eq m hm]
  rw [← zpow_natCast, ← zpow_natCast, Int.toNat_of_nonneg hp, Int.toNat_of_nonneg hn,
    zpow_add₀ ha, zpow_sub₀ hb, zpow_natCast, zpow_natCast, div_zpow, mul_pow]
  ring

theorem powerNumerator_le (m : ℕ) (t : ℤ)
    (ht : -(K m:ℤ) ≤ t ∧ t ≤ K m) : powerNumerator m t ≤ A m ^ (2*K m) := by
  have he : ((K m:ℤ)+t).toNat + ((K m:ℤ)-t).toNat = 2*K m := by omega
  unfold powerNumerator
  calc
    _ ≤ A m ^ ((K m:ℤ)+t).toNat * A m ^ ((K m:ℤ)-t).toNat := by
      gcongr
      simp [A, B]
    _ = _ := by rw [← pow_add, he]

/-- A coarse polynomial bit envelope, independent of the number of summands. -/
theorem powerNumerator_bits (m : ℕ) (t : ℤ)
    (ht : -(K m:ℤ) ≤ t ∧ t ≤ K m) :
    (powerNumerator m t).size ≤ A m * (2*K m)+1 := by
  apply Nat.size_le.mpr
  have hp := powerNumerator_le m t ht
  have hA : A m ≤ 2^(A m) := (Nat.lt_two_pow_self).le
  have hpow : A m ^ (2*K m) ≤ 2^(A m*(2*K m)) := by
    calc
      _ ≤ (2^(A m))^(2*K m) := Nat.pow_le_pow_left hA _
      _ = _ := (pow_mul _ _ _).symm
  exact lt_of_le_of_lt (hp.trans hpow) (by rw [pow_succ]; have := Nat.two_pow_pos (A m*(2*K m)); omega)

/-- Twice the numerator of the resolved tilted contribution. -/
def resolved (m : ℕ) (s : ℤ) (signBit : Bool) : ℕ :=
  2*(powerNumerator m (s+sign signBit) + powerNumerator m (-(s+sign signBit)))

/-- The four neighboring powers give the unresolved mean contribution. -/
def unresolved (m : ℕ) (s : ℤ) : ℕ :=
  powerNumerator m (s+1) + powerNumerator m (s-1) +
    powerNumerator m (-s+1) + powerNumerator m (-s-1)

theorem resolved_eq (m : ℕ) (hm : 0 < m) (s : ℤ) (hs : |s| ≤ 64*m^3)
    (b : Bool) : (resolved m s b:ℚ) =
      tilt (rationalBase m) (rationalBase m^s) (rationalBase m^(-s)) b *
        (2*denominator m:ℕ) := by
  have hs' := abs_le.mp hs
  have hb : sign b = 1 ∨ sign b = -1 := by cases b <;> simp [sign]
  have ht : -(K m:ℤ) ≤ s+sign b ∧ s+sign b ≤ K m := by
    simp only [K, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow, Nat.cast_one]
    rcases hb with hb | hb <;> omega
  have ht' : -(K m:ℤ) ≤ -(s+sign b) ∧ -(s+sign b) ≤ K m := by omega
  simp only [resolved, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat,
    powerNumerator_eq m hm _ ht, powerNumerator_eq m hm _ ht']
  rw [← add_mul, tilt_powers _ (ne_of_gt (lt_trans (by norm_num) (rationalBase_gt_one m hm)))]
  ring

theorem unresolved_eq (m : ℕ) (hm : 0 < m) (s : ℤ) (hs : |s| ≤ 64*m^3) :
    (unresolved m s:ℚ) =
      (rationalBase m^s+rationalBase m^(-s))*mean (rationalBase m)*(2*denominator m:ℕ) := by
  have hs' := abs_le.mp hs
  have hwin (t : ℤ) (h : t = s+1 ∨ t = s-1 ∨ t = -s+1 ∨ t = -s-1) :
      -(K m:ℤ) ≤ t ∧ t ≤ K m := by
    simp only [K, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow, Nat.cast_one]
    rcases h with h | h | h | h <;> omega
  have hr : rationalBase m ≠ 0 := ne_of_gt (lt_trans (by norm_num) (rationalBase_gt_one m hm))
  simp only [unresolved, Nat.cast_add, powerNumerator_eq m hm _ (hwin _ (Or.inl rfl)),
    powerNumerator_eq m hm _ (hwin _ (Or.inr (Or.inl rfl))),
    powerNumerator_eq m hm _ (hwin _ (Or.inr (Or.inr (Or.inl rfl)))),
    powerNumerator_eq m hm _ (hwin _ (Or.inr (Or.inr (Or.inr rfl)))),
    zpow_add₀ hr, zpow_sub₀ hr, zpow_one, mean, Nat.cast_mul, Nat.cast_ofNat]
  ring

theorem resolved_le (m : ℕ) (s : ℤ) (hs : |s| ≤ 64*m^3) (b : Bool) :
    resolved m s b ≤ 4*A m^(2*K m) := by
  have hs' := abs_le.mp hs
  have hb : sign b = 1 ∨ sign b = -1 := by cases b <;> simp [sign]
  have ht : -(K m:ℤ) ≤ s+sign b ∧ s+sign b ≤ K m := by
    simp only [K, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow, Nat.cast_one]
    rcases hb with hb | hb <;> omega
  have ht' : -(K m:ℤ) ≤ -(s+sign b) ∧ -(s+sign b) ≤ K m := by omega
  have hp := powerNumerator_le m _ ht
  have hn := powerNumerator_le m _ ht'
  unfold resolved
  omega

theorem unresolved_le (m : ℕ) (s : ℤ) (hs : |s| ≤ 64*m^3) :
    unresolved m s ≤ 4*A m^(2*K m) := by
  have hs' := abs_le.mp hs
  have hwin (t : ℤ) (h : t = s+1 ∨ t = s-1 ∨ t = -s+1 ∨ t = -s-1) :
      -(K m:ℤ) ≤ t ∧ t ≤ K m := by
    simp only [K, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow, Nat.cast_one]
    rcases h with h | h | h | h <;> omega
  have h1 := powerNumerator_le m _ (hwin _ (Or.inl rfl))
  have h2 := powerNumerator_le m _ (hwin _ (Or.inr (Or.inl rfl)))
  have h3 := powerNumerator_le m _ (hwin _ (Or.inr (Or.inr (Or.inl rfl))))
  have h4 := powerNumerator_le m _ (hwin _ (Or.inr (Or.inr (Or.inr rfl))))
  unfold unresolved
  omega

variable {C : Type*} [Fintype C]

def score {n : ℕ} (m : ℕ) (sums : C → ℤ) (rows : C → Cube n) (signs : C → Bool) : ℕ :=
  ∑ a, if rows a = zeroBits n then resolved m (sums a) (signs a) else unresolved m (sums a)

theorem score_eq {n : ℕ} (m : ℕ) (hm : 0 < m) (sums : C → ℤ)
    (hs : ∀ a, |sums a| ≤ 64*m^3) (rows : C → Cube n) (signs : C → Bool) :
    (score m sums rows signs:ℚ) =
      expectation (rationalBase m) (fun a => rationalBase m^sums a)
        (fun a => rationalBase m^(-sums a)) rows signs * (2*denominator m:ℕ) := by
  simp only [score, Nat.cast_sum, expectation, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  split_ifs
  · exact resolved_eq m hm (sums a) (hs a) (signs a)
  · exact unresolved_eq m hm (sums a) (hs a)

theorem score_le {n : ℕ} (m : ℕ) (sums : C → ℤ) (hs : ∀ a, |sums a| ≤ 64*m^3)
    (rows : C → Cube n) (signs : C → Bool) :
    score m sums rows signs ≤ Fintype.card C * (4*A m^(2*K m)) := by
  calc
    _ ≤ ∑ _ : C, 4*A m^(2*K m) := by
      apply Finset.sum_le_sum
      intro a _
      split_ifs
      · exact resolved_le m _ (hs a) _
      · exact unresolved_le m _ (hs a)
    _ = _ := by simp

/-- The entire score, and hence every nonnegative partial sum, has polynomial
bit length even though there are exponentially many character rows. -/
theorem score_bits {n : ℕ} (m : ℕ) (sums : C → ℤ) (hs : ∀ a, |sums a| ≤ 64*m^3)
    (hc : Fintype.card C ≤ 2^m) (rows : C → Cube n) (signs : C → Bool) :
    (score m sums rows signs).size ≤ m+2+A m*(2*K m)+1 := by
  have hA : A m ≤ 2^(A m) := (Nat.lt_two_pow_self).le
  have hp : A m^(2*K m) ≤ 2^(A m*(2*K m)) := by
    calc
      _ ≤ (2^(A m))^(2*K m) := Nat.pow_le_pow_left hA _
      _ = _ := (pow_mul _ _ _).symm
  have hb : score m sums rows signs ≤ 2^(m+2+A m*(2*K m)) := by
    calc
      _ ≤ Fintype.card C*(4*A m^(2*K m)) := score_le m sums hs rows signs
      _ ≤ 2^m*(4*2^(A m*(2*K m))) := Nat.mul_le_mul hc (Nat.mul_le_mul_left _ hp)
      _ = _ := by rw [pow_add, pow_add]; ring
  apply Nat.size_le.mpr
  exact lt_of_le_of_lt hb (by rw [pow_succ]; have := Nat.two_pow_pos (m+2+A m*(2*K m)); omega)

/-- Compare two retained natural numerators. Equality selects false. -/
def chosen {n : ℕ} (m : ℕ) (sums : C → ℤ) (rows : C → Cube (n+1))
    (signs : C → Bool) : Bool :=
  let left := score m sums (tails rows) (updateSigns rows signs false)
  let right := score m sums (tails rows) (updateSigns rows signs true)
  decide (right < left)

theorem chosen_eq {n : ℕ} (m : ℕ) (hm : 0 < m) (sums : C → ℤ)
    (hs : ∀ a, |sums a| ≤ 64*m^3) (rows : C → Cube (n+1)) (signs : C → Bool) :
    chosen m sums rows signs = chosenBit (rationalBase m)
      (fun a => rationalBase m^sums a) (fun a => rationalBase m^(-sums a)) rows signs := by
  have hd : (0:ℚ) < (2*denominator m:ℕ) := by exact_mod_cast (by have := denominator_pos m hm; omega : 0 < 2*denominator m)
  unfold chosen chosenBit
  dsimp only
  congr 1
  rw [← Nat.cast_lt (α := ℚ), score_eq m hm sums hs, score_eq m hm sums hs,
    mul_lt_mul_iff_of_pos_right hd]

#print axioms denominator_pos
#print axioms rationalBase_eq
#print axioms powerNumerator_eq
#print axioms powerNumerator_le
#print axioms powerNumerator_bits
#print axioms resolved_eq
#print axioms unresolved_eq
#print axioms resolved_le
#print axioms unresolved_le
#print axioms score_eq
#print axioms score_le
#print axioms score_bits
#print axioms chosen_eq
end ThinMatrix.HalfSourceIntegerScores
