import Mathlib
import CyclicRing
import EncoderCorrectness

/-!
# Coefficient growth and signed integer bit budgets

The bounds apply to the explicitly evaluated integer coefficient operations:
Walsh rows, source weights, local linear circuits, one cyclic leaf product,
high-box addition circuits, low channel/degree/weight sums, degree runs, and
complete exact normalization.  The local circuit interface bounds each row
by four terms of coefficient magnitude at most two; its evaluation theorem
propagates the input bound rather than assuming bounded internal nodes.

These are magnitude and bit-size statements, not a unit-cost assumption for
unbounded integers.  Fast cyclic arithmetic has a separate implementation
and cost obligation.
-/

namespace ThinMatrix.CoefficientBounds

open scoped BigOperators
open CyclicRing

/-- A natural uniform upper bound on every signed cyclic coefficient. -/
def CoeffBound {q : ℕ} (a : Cyclic q) (A : ℕ) : Prop :=
  ∀ k, |a k| ≤ (A : ℤ)

/-- Explicitly evaluated bounded-row integer linear transform. -/
theorem linearCombination_bound {q : ℕ} {ι : Type*}
    (s : Finset ι) (c : ι → ℤ) (a : ι → Cyclic q) (C A : ℕ)
    (hc : ∀ i ∈ s, |c i| ≤ (C : ℤ))
    (ha : ∀ i ∈ s, CoeffBound (a i) A) :
    CoeffBound (linearCombination s c a) (s.card*C*A) := by
  intro k
  have hrow : ∑ i ∈ s, |c i| ≤ (s.card*C : ℕ) := by
    calc
      ∑ i ∈ s, |c i| ≤ ∑ _i ∈ s, (C : ℤ) :=
        Finset.sum_le_sum hc
      _ = (s.card*C : ℕ) := by simp
  simpa only [Nat.cast_mul] using
    linearCombination_abs_le s c a (A : ℤ) (s.card*C : ℕ)
      (Nat.cast_nonneg A) (fun i hi k => ha i hi k) hrow k

/-- Enlarging a natural coefficient budget preserves it. -/
theorem CoeffBound.mono {q A B : ℕ} {a : Cyclic q}
    (h : CoeffBound a A) (hAB : A ≤ B) : CoeffBound a B := by
  intro k
  exact (h k).trans (by exact_mod_cast hAB)

/-- A Walsh row of length at most `2^k` has row weight at most `2^k`. -/
theorem walsh_row_bound {q : ℕ} {ι : Type*}
    (s : Finset ι) (sign : ι → ℤ) (a : ι → Cyclic q) (k A : ℕ)
    (hs : s.card ≤ 2^k) (hsgn : ∀ i ∈ s, |sign i| ≤ 1)
    (ha : ∀ i ∈ s, CoeffBound (a i) A) :
    CoeffBound (linearCombination s sign a) (2^k*A) := by
  have h := linearCombination_bound s sign a 1 A (by simpa using hsgn) ha
  exact h.mono (by simpa using Nat.mul_le_mul_right A hs)

/-- An actual source weight multiplies every coefficient by `2^h`. -/
theorem source_weight_bound {q : ℕ} (a : Cyclic q) (m h A : ℕ)
    (hh : h ≤ m) (ha : CoeffBound a A) :
    CoeffBound (scale ((2 : ℤ)^h) a) (2^m*A) := by
  intro k
  simp only [scale, abs_mul, abs_pow, show |(2 : ℤ)| = 2 by norm_num]
  calc
    (2 : ℤ)^h * |a k| ≤ 2^m*(A : ℤ) := by
      apply mul_le_mul
      · exact pow_le_pow_right₀ (by norm_num) hh
      · exact ha k
      · exact abs_nonneg _
      · positivity
    _ = (2^m*A : ℕ) := by norm_cast

/-- Source formation propagates Walsh and normal-letter weights together. -/
theorem weighted_walsh_source_bound {q : ℕ} {ι : Type*}
    (s : Finset ι) (sign : ι → ℤ) (a : ι → Cyclic q)
    (L m h A : ℕ) (hs : s.card ≤ 2^L) (hh : h ≤ m)
    (hsgn : ∀ i ∈ s, |sign i| ≤ 1)
    (ha : ∀ i ∈ s, CoeffBound (a i) A) :
    CoeffBound (scale ((2 : ℤ)^h) (linearCombination s sign a)) (2^(L+m)*A) := by
  have hw := source_weight_bound (linearCombination s sign a) m h (2^L*A) hh
    (walsh_row_bound s sign a L A hs hsgn ha)
  simpa only [pow_add, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hw

/-- Exactly one cyclic leaf multiplication contributes its full modulus. -/
theorem leaf_product_bound {q A B : ℕ} [NeZero q]
    (a b : Cyclic q) (ha : CoeffBound a A) (hb : CoeffBound b B) :
    CoeffBound (a*b) (q*A*B) := by
  intro k
  simpa only [Nat.cast_mul] using
    mul_abs_le a b (A : ℤ) (B : ℤ) (Nat.cast_nonneg A) (Nat.cast_nonneg B) ha hb k

/-- Finite sums charge all summands, including signs or repeated keys. -/
theorem finite_sum_bound {q : ℕ} {ι : Type*} (s : Finset ι)
    (a : ι → Cyclic q) (A : ℕ) (ha : ∀ i ∈ s, CoeffBound (a i) A) :
    CoeffBound (fun k => ∑ i ∈ s, a i k) (s.card*A) := by
  have h := linearCombination_bound s (fun _ => (1 : ℤ)) a 1 A (by simp) ha
  simpa [CoeffBound, linearCombination] using h

/-- Complete exact integer normalization cannot increase coefficients. -/
theorem decode_bound {q A L : ℕ} (a : Cyclic q) (ha : CoeffBound a A) :
    CoeffBound (decode L a) A := by
  intro k
  change |a k / (4 : ℤ)^L| ≤ (A : ℤ)
  exact (Int.abs_ediv_le_abs _ _).trans (ha k)

end ThinMatrix.CoefficientBounds



namespace ThinMatrix.CoefficientBudget

/-- A deliberately loose elementary power-of-two majorant. -/
theorem nat_le_two_pow (n : ℕ) : n ≤ 2 ^ n := by
  exact (Nat.lt_two_pow_self (n := n)).le

/-- The threshold and interpolation overhead uses only a linear number of bits. -/
theorem threshold_overhead (t m : ℕ) :
    (t + 1) ^ 2 * (2 * m + 1) ≤ 2 ^ (2 * (t + 1) + (2 * m + 1)) := by
  calc
    (t + 1) ^ 2 * (2 * m + 1) ≤ (2 ^ (t + 1)) ^ 2 * 2 ^ (2 * m + 1) :=
      Nat.mul_le_mul (Nat.pow_le_pow_left (nat_le_two_pow (t + 1)) 2)
        (nat_le_two_pow (2 * m + 1))
    _ = _ := by rw [← pow_mul, ← pow_add]; congr 1; omega

/-- Explicit constant in the `O(r)` bit budget. -/
def budgetConstant (cL cm cq cA : ℕ) : ℕ :=
  100 * cL + 106 * cm + cq + 2 * cA + 103

/-- All coefficient magnitudes under the stated size hypotheses fit into a
power of two whose exponent is at most a fixed multiple of `r+1`. -/
theorem full_budget (L m t q A r cL cm cq cA : ℕ)
    (hL : L ≤ cL * r) (hm : m ≤ cm * r)
    (hq : q ≤ 2 ^ (cq * r)) (hA : A ≤ 2 ^ (cA * r)) (ht : t ≤ 2 * m) :
    q * (t + 1) ^ 2 * (2 * m + 1) * 2 ^ (100 * L + 100 * m + 100) * A ^ 2 ≤
      2 ^ (budgetConstant cL cm cq cA * (r + 1)) := by
  calc
    _ = q * ((t + 1) ^ 2 * (2 * m + 1)) *
        2 ^ (100 * L + 100 * m + 100) * A ^ 2 := by ring
    _ ≤ 2 ^ (cq * r) * 2 ^ (2 * (t + 1) + (2 * m + 1)) *
        2 ^ (100 * L + 100 * m + 100) * (2 ^ (cA * r)) ^ 2 := by
      apply Nat.mul_le_mul
      · exact Nat.mul_le_mul (Nat.mul_le_mul hq (threshold_overhead t m)) (le_refl _)
      · exact Nat.pow_le_pow_left hA 2
    _ = 2 ^ (cq * r + (2 * (t + 1) + (2 * m + 1)) +
        (100 * L + 100 * m + 100) + (cA * r) * 2) := by
      rw [← pow_mul, ← pow_add, ← pow_add, ← pow_add]
    _ ≤ _ := by
      apply Nat.pow_le_pow_right (by norm_num)
      dsimp [budgetConstant]
      nlinarith

/-- Magnitude bits together with a sign bit and a zero convention. -/
def signedBitLength (z : ℤ) : ℕ := Nat.log2 z.natAbs + 2

/-- A power-of-two magnitude bound directly gives a bit-length bound. -/
theorem signedBitLength_le_of_natAbs_le_pow (z : ℤ) (b : ℕ)
    (hz : z.natAbs ≤ 2 ^ b) : signedBitLength z ≤ b + 2 := by
  have hlog : Nat.log2 z.natAbs ≤ Nat.log2 (2 ^ b) := by
    simpa only [Nat.log2_eq_log_two] using (Nat.log_mono_right (b := 2) hz)
  rw [Nat.log2_two_pow] at hlog
  exact Nat.add_le_add_right hlog 2

/-- The full coefficient magnitude estimate yields an explicit linear bit
budget, with no real logarithms or rounding assumptions. -/
theorem signedBitLength_full_budget (z : ℤ) (L m t q A r cL cm cq cA : ℕ)
    (hL : L ≤ cL * r) (hm : m ≤ cm * r)
    (hq : q ≤ 2 ^ (cq * r)) (hA : A ≤ 2 ^ (cA * r)) (ht : t ≤ 2 * m)
    (hz : z.natAbs ≤
      q * (t + 1) ^ 2 * (2 * m + 1) * 2 ^ (100 * L + 100 * m + 100) * A ^ 2) :
    signedBitLength z ≤ budgetConstant cL cm cq cA * (r + 1) + 2 := by
  apply signedBitLength_le_of_natAbs_le_pow
  exact hz.trans (full_budget L m t q A r cL cm cq cA hL hm hq hA ht)


end ThinMatrix.CoefficientBudget

namespace ThinMatrix.ChooseBound

theorem choose_le_two_pow (n k : ℕ) : n.choose k ≤ 2 ^ n :=
  Nat.choose_le_two_pow n k

/-- The correction coefficient is bounded uniformly, including all boundary
cases for truncated natural-number subtraction. -/
theorem correction_coefficient_abs_le (m t j : ℕ) :
    |(-1 : ℤ) ^ (t - j - 1) * ((2 * m - j - 1).choose (t - j - 1) : ℤ)| ≤
      (2 : ℤ) ^ (2 * m) := by
  rw [abs_mul, abs_neg_one_pow, one_mul,
    abs_of_nonneg (Nat.cast_nonneg _)]
  have hp : (2 : ℕ) ^ (2 * m - j - 1) ≤ 2 ^ (2 * m) := by
    exact Nat.pow_le_pow_right (by decide : 0 < 2)
      ((Nat.sub_le (2 * m - j) 1).trans (Nat.sub_le (2 * m) j))
  have hn := (choose_le_two_pow (2 * m - j - 1) (t - j - 1)).trans hp
  exact_mod_cast hn


end ThinMatrix.ChooseBound



open scoped BigOperators

namespace ThinMatrix.LinearCircuitBound

open ThinMatrix.EncoderCorrectness ThinMatrix.CyclicRing

theorem abs_sum_mul_le_budget {n : ℕ} (c x : Fin n → ℤ) (A : ℤ)
    (_hA : 0 ≤ A) (hx : ∀ i, |x i| ≤ A) :
    |∑ i, c i * x i| ≤ (∑ i, |c i|) * A := by
  calc
    |∑ i, c i * x i| ≤ ∑ i, |c i * x i| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, |c i| * |x i| := by simp only [abs_mul]
    _ ≤ ∑ i, |c i| * A := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (hx i) (abs_nonneg _)
    _ = (∑ i, |c i|) * A := by rw [Finset.sum_mul]

theorem abs_sum_mul_le_eight {n : ℕ} (c x : Fin n → ℤ) (A : ℤ)
    (hA : 0 ≤ A) (hx : ∀ i, |x i| ≤ A) (hc : (∑ i, |c i|) ≤ 8) :
    |∑ i, c i * x i| ≤ 8 * A := by
  exact (abs_sum_mul_le_budget c x A hA hx).trans
    (mul_le_mul_of_nonneg_right hc hA)

theorem four_children_budget {n : ℕ} (hn : n ≤ 4) (c : Fin n → ℤ)
    (hc : ∀ i, |c i| ≤ 2) : (∑ i, |c i|) ≤ 8 := by
  have hs : (∑ i, |c i|) ≤ ∑ _i : Fin n, (2 : ℤ) :=
    Finset.sum_le_sum (fun i _ => hc i)
  have hnz : (n : ℤ) ≤ 4 := by exact_mod_cast hn
  simpa using hs.trans (by simpa using (show (n : ℤ)*2 ≤ 8 by omega))

theorem five_unit_children_budget {n : ℕ} (hn : n ≤ 5) (c : Fin n → ℤ)
    (hc : ∀ i, |c i| ≤ 1) : (∑ i, |c i|) ≤ 8 := by
  have hs : (∑ i, |c i|) ≤ ∑ _i : Fin n, (1 : ℤ) :=
    Finset.sum_le_sum (fun i _ => hc i)
  have hnz : (n : ℤ) ≤ 5 := by exact_mod_cast hn
  simpa using hs.trans (by simpa using (show (n : ℤ) ≤ 8 by omega))

theorem contractFirst_coefficient_bound {q n : ℕ} [NeZero q]
    (dims : Fin (n+1) → ℕ) (c : Fin (dims 0) → ℤ)
    (input : Coordinates dims → Cyclic q) (A : ℤ)
    (hA : 0 ≤ A) (hc : (∑ a, |c a|) ≤ 8)
    (hinput : ∀ a k, |input a k| ≤ A)
    (rest : Coordinates (fun i : Fin n => dims i.succ)) (k : Fin q) :
    |contractFirst dims (fun a => (c a : Cyclic q)) input rest k| ≤ 8*A := by
  simp only [contractFirst, sum_coeff, intCast_mul_coeff]
  exact abs_sum_mul_le_eight c (fun a => input (Fin.cons a rest) k) A hA
    (fun a => hinput (Fin.cons a rest) k) hc

theorem sweep_coefficient_bound {q : ℕ} [NeZero q] (n : ℕ) :
    ∀ (dims : Fin n → ℕ) (c : (i : Fin n) → Fin (dims i) → ℤ)
      (input : Coordinates dims → Cyclic q) (A : ℤ),
      0 ≤ A → (∀ i, (∑ a, |c i a|) ≤ 8) →
      (∀ a k, |input a k| ≤ A) → ∀ k,
      |sweep n dims (fun i a => (c i a : Cyclic q)) input k| ≤ (8 : ℤ)^n*A := by
  induction n with
  | zero =>
    intro dims c input A hA hc hinput k
    simpa only [sweep, pow_zero, one_mul] using hinput (fun i => Fin.elim0 i) k
  | succ n ih =>
    intro dims c input A hA hc hinput k
    rw [sweep]
    have hnext : 0 ≤ (8 : ℤ)*A := by positivity
    have hbound := ih (fun i => dims i.succ) (fun i => c i.succ)
      (contractFirst dims (fun a => (c 0 a : Cyclic q)) input) (8*A) hnext
      (fun i => hc i.succ)
      (fun rest j => contractFirst_coefficient_bound dims (c 0) input A hA (hc 0) hinput rest j) k
    simpa only [pow_succ, mul_assoc] using hbound

theorem sweep_four_children_bound {q : ℕ} [NeZero q] (n : ℕ)
    (dims : Fin n → ℕ) (c : (i : Fin n) → Fin (dims i) → ℤ)
    (input : Coordinates dims → Cyclic q) (A : ℤ)
    (hA : 0 ≤ A) (hdims : ∀ i, dims i ≤ 4) (hc : ∀ i a, |c i a| ≤ 2)
    (hinput : ∀ a k, |input a k| ≤ A) (k : Fin q) :
    |sweep n dims (fun i a => (c i a : Cyclic q)) input k| ≤ (8 : ℤ)^n*A := by
  exact sweep_coefficient_bound n dims c input A hA
    (fun i => four_children_budget (hdims i) (c i) (hc i)) hinput k

theorem sweep_five_unit_children_bound {q : ℕ} [NeZero q] (n : ℕ)
    (dims : Fin n → ℕ) (c : (i : Fin n) → Fin (dims i) → ℤ)
    (input : Coordinates dims → Cyclic q) (A : ℤ)
    (hA : 0 ≤ A) (hdims : ∀ i, dims i ≤ 5) (hc : ∀ i a, |c i a| ≤ 1)
    (hinput : ∀ a k, |input a k| ≤ A) (k : Fin q) :
    |sweep n dims (fun i a => (c i a : Cyclic q)) input k| ≤ (8 : ℤ)^n*A := by
  exact sweep_coefficient_bound n dims c input A hA
    (fun i => five_unit_children_budget (hdims i) (c i) (hc i)) hinput k

theorem eight_pow_eq_two_pow (n : ℕ) : (8 : ℤ)^n = (2 : ℤ)^(3*n) := by
  calc
    (8 : ℤ)^n = ((2 : ℤ)^3)^n := by norm_num
    _ = (2 : ℤ)^(3*n) := (pow_mul _ _ _).symm

theorem sweep_four_children_bound_two_pow {q : ℕ} [NeZero q] (n : ℕ)
    (dims : Fin n → ℕ) (c : (i : Fin n) → Fin (dims i) → ℤ)
    (input : Coordinates dims → Cyclic q) (A : ℤ)
    (hA : 0 ≤ A) (hdims : ∀ i, dims i ≤ 4) (hc : ∀ i a, |c i a| ≤ 2)
    (hinput : ∀ a k, |input a k| ≤ A) (k : Fin q) :
    |sweep n dims (fun i a => (c i a : Cyclic q)) input k| ≤ (2 : ℤ)^(3*n)*A := by
  simpa only [eight_pow_eq_two_pow] using
    sweep_four_children_bound n dims c input A hA hdims hc hinput k

theorem sweep_two_half_five_unit_bound {q L : ℕ} [NeZero q]
    (dims : Fin (2*L) → ℕ) (c : (i : Fin (2*L)) → Fin (dims i) → ℤ)
    (input : Coordinates dims → Cyclic q) (A : ℤ)
    (hA : 0 ≤ A) (hdims : ∀ i, dims i ≤ 5) (hc : ∀ i a, |c i a| ≤ 1)
    (hinput : ∀ a k, |input a k| ≤ A) (k : Fin q) :
    |sweep (2*L) dims (fun i a => (c i a : Cyclic q)) input k| ≤ (2 : ℤ)^(6*L)*A := by
  simpa only [eight_pow_eq_two_pow, show 3*(2*L)=6*L by omega] using
    sweep_five_unit_children_bound (2*L) dims c input A hA hdims hc hinput k

/-- A finite recursive linear circuit. Child coordinate maps allow shifts
and arbitrary reindexing of a cyclic/auxiliary coefficient grid. The stored
budget concerns local integer coefficients, never an assumed value bound. -/
inductive Expr (ι κ : Type*) : ℕ → Type _
  | input (d : ℕ) (i : ι) : Expr ι κ d
  | node {d : ℕ} (n : ℕ) (c : Fin n → ℤ) (budget : (∑ i, |c i|) ≤ 8)
      (read : Fin n → κ → κ) (children : Fin n → Expr ι κ d) : Expr ι κ (d+1)

def eval {ι κ : Type*} (input : ι → κ → ℤ) : {d : ℕ} → Expr ι κ d → κ → ℤ
  | _, .input _ i, k => input i k
  | _, .node n c _ read children, k =>
      ∑ i : Fin n, c i * eval input (children i) (read i k)

theorem eval_bound {ι κ : Type*} {d : ℕ} (input : ι → κ → ℤ)
    (A : ℤ) (hA : 0 ≤ A) (hinput : ∀ i k, |input i k| ≤ A)
    (e : Expr ι κ d) : ∀ k, |eval input e k| ≤ (8 : ℤ)^d*A := by
  induction e with
  | input d i =>
    intro k
    have hp : (1 : ℤ) ≤ (8 : ℤ)^d := one_le_pow₀ (by norm_num)
    exact (hinput i k).trans (by simpa using mul_le_mul_of_nonneg_right hp hA)
  | @node d n c budget read children ih =>
    intro k
    have hpos : 0 ≤ (8 : ℤ)^d*A := by positivity
    have h := abs_sum_mul_le_eight c
      (fun i => eval input (children i) (read i k)) ((8 : ℤ)^d*A) hpos
      (fun i => ih i (read i k)) budget
    simpa only [eval, pow_succ, mul_assoc, mul_comm, mul_left_comm] using h


end ThinMatrix.LinearCircuitBound

namespace ThinMatrix.CoefficientBounds

open scoped BigOperators
open CyclicRing LinearCircuitBound

/-- A source row records its actual Walsh support, signs, and normal
letter weight.  It has no assumed bound on its output. -/
structure SourceRow (L m : ℕ) where
  support : Finset ℕ
  sign : ℕ → ℤ
  support_le : support.card ≤ 2^L
  sign_le : ∀ i ∈ support, |sign i| ≤ 1
  weight : ℕ
  weight_le : weight ≤ m

/-- Source formation on an arbitrary coefficient grid. -/
def SourceRow.eval {L m : ℕ} {κ : Type*} (r : SourceRow L m)
    (raw : ℕ → κ → ℤ) (k : κ) : ℤ :=
  (2 : ℤ)^r.weight * ∑ i ∈ r.support, r.sign i*raw i k

theorem SourceRow.eval_bound {L m A : ℕ} {κ : Type*} (r : SourceRow L m)
    (raw : ℕ → κ → ℤ) (hraw : ∀ i k, |raw i k| ≤ (A : ℤ)) (k : κ) :
    |r.eval raw k| ≤ (2^(L+m)*A : ℕ) := by
  have h := weighted_walsh_source_bound r.support r.sign
    (fun i (_ : Fin 1) => raw i k) L m r.weight A
    r.support_le r.weight_le r.sign_le (fun i _ _ => hraw i k) (0 : Fin 1)
  exact h

/-- An encoder node is an evaluated finite circuit of depth at most `2L`.
Coefficient-grid reads explicitly permit the one-place shift in `H(z)`. -/
structure EncodedNode (L : ℕ) (κ : Type*) where
  depth : ℕ
  depth_le : depth ≤ 2*L
  circuit : Expr ℕ κ depth

def EncodedNode.eval {L m : ℕ} {κ : Type*} (e : EncodedNode L κ)
    (sources : ℕ → SourceRow L m) (raw : ℕ → κ → ℤ) : κ → ℤ :=
  LinearCircuitBound.eval (fun i k => (sources i).eval raw k) e.circuit

theorem EncodedNode.eval_bound {L m A : ℕ} {κ : Type*} (e : EncodedNode L κ)
    (sources : ℕ → SourceRow L m) (raw : ℕ → κ → ℤ)
    (hraw : ∀ i k, |raw i k| ≤ (A : ℤ)) (k : κ) :
    |e.eval sources raw k| ≤ (2^(7*L+m)*A : ℕ) := by
  have h := LinearCircuitBound.eval_bound
    (fun i k => (sources i).eval raw k) (2^(L+m)*A : ℕ) (by positivity)
    (fun i k => (sources i).eval_bound raw hraw k) e.circuit k
  rw [eight_pow_eq_two_pow] at h
  have hd := e.depth_le
  calc
    |e.eval sources raw k| ≤ (2 : ℤ)^(3*e.depth)*(2^(L+m)*A : ℕ) := h
    _ ≤ (2 : ℤ)^(6*L)*(2^(L+m)*A : ℕ) := by
      apply mul_le_mul_of_nonneg_right
      · exact pow_le_pow_right₀ (by norm_num) (by omega)
      · positivity
    _ = (2^(7*L+m)*A : ℕ) := by
      push_cast
      rw [← mul_assoc, ← pow_add]
      congr 2; omega

/-- A leaf product selects auxiliary degrees and performs one full cyclic
multiplication of two encoder outputs. -/
structure LeafNode (L q : ℕ) where
  left : EncodedNode L (ℤ × Fin q)
  right : EncodedNode L (ℤ × Fin q)
  leftDegree : ℤ
  rightDegree : ℤ

noncomputable def LeafNode.eval {L m q : ℕ} [NeZero q] (e : LeafNode L q)
    (sources : ℕ → SourceRow L m) (raw : ℕ → ℤ × Fin q → ℤ) : Cyclic q :=
  convolution
    (fun k => e.left.eval sources raw (e.leftDegree,k))
    (fun k => e.right.eval sources raw (e.rightDegree,k))

theorem LeafNode.eval_bound {L m q A : ℕ} [NeZero q] (e : LeafNode L q)
    (sources : ℕ → SourceRow L m) (raw : ℕ → ℤ × Fin q → ℤ)
    (hraw : ∀ i k, |raw i k| ≤ (A : ℤ)) :
    CoeffBound (e.eval sources raw) (q*2^(14*L+2*m)*A^2) := by
  have h := leaf_product_bound
    (fun k => e.left.eval sources raw (e.leftDegree,k))
    (fun k => e.right.eval sources raw (e.rightDegree,k))
    (fun k => e.left.eval_bound sources raw hraw _)
    (fun k => e.right.eval_bound sources raw hraw _)
  rw [mul_eq_convolution] at h
  have hb : q*(2^(7*L+m)*A)*(2^(7*L+m)*A) = q*2^(14*L+2*m)*A^2 := by
    rw [show 14*L+2*m=(7*L+m)+(7*L+m) by omega, pow_add]
    ring
  simpa only [CoeffBound, LeafNode.eval, hb] using h

/-- A high-state addition circuit has at most `2L` stages.  Its leaves
are actual encoded cyclic products, and its row budgets are local. -/
structure HighNode (L q : ℕ) where
  leaves : ℕ → LeafNode L q
  depth : ℕ
  depth_le : depth ≤ 2*L
  circuit : Expr ℕ (Fin q) depth

noncomputable def HighNode.eval {L m q : ℕ} [NeZero q] (e : HighNode L q)
    (sources : ℕ → SourceRow L m) (raw : ℕ → ℤ × Fin q → ℤ) : Cyclic q :=
  LinearCircuitBound.eval (fun i k => (e.leaves i).eval sources raw k) e.circuit

theorem HighNode.eval_bound {L m q A : ℕ} [NeZero q] (e : HighNode L q)
    (sources : ℕ → SourceRow L m) (raw : ℕ → ℤ × Fin q → ℤ)
    (hraw : ∀ i k, |raw i k| ≤ (A : ℤ)) :
    CoeffBound (e.eval sources raw) (q*2^(20*L+2*m)*A^2) := by
  intro k
  have h := LinearCircuitBound.eval_bound
    (fun i k => (e.leaves i).eval sources raw k) (q*2^(14*L+2*m)*A^2 : ℕ)
    (by positivity) (fun i k => (e.leaves i).eval_bound sources raw hraw k) e.circuit k
  rw [eight_pow_eq_two_pow] at h
  have hd := e.depth_le
  calc
    |e.eval sources raw k| ≤ (2 : ℤ)^(3*e.depth)*(q*2^(14*L+2*m)*A^2 : ℕ) := h
    _ ≤ (2 : ℤ)^(6*L)*(q*2^(14*L+2*m)*A^2 : ℕ) := by
      apply mul_le_mul_of_nonneg_right
      · exact pow_le_pow_right₀ (by norm_num) (by omega)
      · positivity
    _ = (q*2^(20*L+2*m)*A^2 : ℕ) := by
      push_cast
      rw [show 20*L+2*m=6*L+(14*L+2*m) by omega, pow_add]
      ring

end ThinMatrix.CoefficientBounds

namespace ThinMatrix.CoefficientBounds

open scoped BigOperators
open CyclicRing LinearCircuitBound

/-- Scaling is charged by the absolute integer coefficient. -/
theorem scale_bound {q C A : ℕ} (c : ℤ) (a : Cyclic q)
    (hc : |c| ≤ (C : ℤ)) (ha : CoeffBound a A) :
    CoeffBound (scale c a) (C*A) := by
  intro k
  simp only [scale, abs_mul, Nat.cast_mul]
  exact mul_le_mul hc (ha k) (abs_nonneg _) (Nat.cast_nonneg C)

def a11Weight (m t j : ℕ) : ℤ :=
  (-1 : ℤ)^(t-j-1)*((2*m-j-1).choose (t-j-1) : ℤ)

theorem a11Weight_bound (m t j : ℕ) : |a11Weight m t j| ≤ (2^(2*m) : ℕ) := by
  simpa only [a11Weight, Nat.cast_pow, Nat.cast_ofNat] using
    ChooseBound.correction_coefficient_abs_le m t j

/-- The low stage stores the actual channel keys and degree pairs.  It
performs at most `(t+1)^2` products for each of at most `2^(2m)` keys. -/
structure LowNode (L m t q : ℕ) where
  keys : Finset ℕ
  keys_le : keys.card ≤ 2^(2*m)
  pairs : ℕ → Finset (Fin (t+1) × Fin (t+1))
  leaf : ℕ → Fin (t+1) × Fin (t+1) → LeafNode L q
  degree : ℕ → Fin (t+1) × Fin (t+1) → ℕ

noncomputable def LowNode.eval {L m t q : ℕ} [NeZero q] (e : LowNode L m t q)
    (sources : ℕ → SourceRow L m) (raw : ℕ → ℤ × Fin q → ℤ) : Cyclic q :=
  fun k => ∑ c ∈ e.keys, ∑ p ∈ e.pairs c,
    a11Weight m t (e.degree c p)*(e.leaf c p).eval sources raw k

theorem LowNode.eval_bound {L m t q A : ℕ} [NeZero q] (e : LowNode L m t q)
    (sources : ℕ → SourceRow L m) (raw : ℕ → ℤ × Fin q → ℤ)
    (hraw : ∀ i k, |raw i k| ≤ (A : ℤ)) :
    CoeffBound (e.eval sources raw) (q*(t+1)^2*2^(14*L+6*m)*A^2) := by
  have hweighted (c : ℕ) (p : Fin (t+1) × Fin (t+1)) :=
    scale_bound (a11Weight m t (e.degree c p)) ((e.leaf c p).eval sources raw)
      (a11Weight_bound m t (e.degree c p)) ((e.leaf c p).eval_bound sources raw hraw)
  have hpairs (c : ℕ) :
      (e.pairs c).card ≤ (t+1)^2 := by
    simpa [pow_two] using (e.pairs c).card_le_univ
  have hinner (c : ℕ) : CoeffBound
      (fun k => ∑ p ∈ e.pairs c,
        a11Weight m t (e.degree c p)*(e.leaf c p).eval sources raw k)
      ((t+1)^2*(2^(2*m)*(q*2^(14*L+2*m)*A^2))) := by
    have h := finite_sum_bound (e.pairs c)
      (fun p => scale (a11Weight m t (e.degree c p)) ((e.leaf c p).eval sources raw))
      (2^(2*m)*(q*2^(14*L+2*m)*A^2)) (fun p _ => hweighted c p)
    exact h.mono (Nat.mul_le_mul_right _ (hpairs c))
  have h := finite_sum_bound e.keys
    (fun c k => ∑ p ∈ e.pairs c,
      a11Weight m t (e.degree c p)*(e.leaf c p).eval sources raw k)
    ((t+1)^2*(2^(2*m)*(q*2^(14*L+2*m)*A^2))) (fun c _ => hinner c)
  have h' := h.mono (Nat.mul_le_mul_right _ e.keys_le)
  have hb : 2^(2*m)*((t+1)^2*(2^(2*m)*(q*2^(14*L+2*m)*A^2))) =
      q*(t+1)^2*2^(14*L+6*m)*A^2 := by
    rw [show 14*L+6*m=2*m+(2*m+(14*L+2*m)) by omega]
    simp only [pow_add]
    ring
  simpa only [CoeffBound, LowNode.eval, hb] using h'

/-- An ordinary-labelled high query reads at most `2^(6m)` handles.
The exact count `choose(2m,t)*4^t` implies this when `t≤2m`. -/
structure HighSum (L m q : ℕ) where
  handles : Finset ℕ
  handles_le : handles.card ≤ 2^(6*m)
  node : ℕ → HighNode L q

noncomputable def HighSum.eval {L m q : ℕ} [NeZero q] (e : HighSum L m q)
    (sources : ℕ → SourceRow L m) (raw : ℕ → ℤ × Fin q → ℤ) : Cyclic q :=
  fun k => ∑ i ∈ e.handles, (e.node i).eval sources raw k

theorem HighSum.eval_bound {L m q A : ℕ} [NeZero q] (e : HighSum L m q)
    (sources : ℕ → SourceRow L m) (raw : ℕ → ℤ × Fin q → ℤ)
    (hraw : ∀ i k, |raw i k| ≤ (A : ℤ)) :
    CoeffBound (e.eval sources raw) (q*2^(20*L+8*m)*A^2) := by
  have h := finite_sum_bound e.handles (fun i => (e.node i).eval sources raw)
    (q*2^(20*L+2*m)*A^2) (fun i _ => (e.node i).eval_bound sources raw hraw)
  have h' := h.mono (Nat.mul_le_mul_right _ e.handles_le)
  have hb : 2^(6*m)*(q*2^(20*L+2*m)*A^2) = q*2^(20*L+8*m)*A^2 := by
    rw [show 20*L+8*m=6*m+(20*L+2*m) by omega, pow_add]
    ring
  simpa only [CoeffBound, HighSum.eval, hb] using h'

theorem labelled_high_handles_bound (m t : ℕ) (ht : t ≤ 2*m) :
    (2*m).choose t*4^t ≤ 2^(6*m) := by
  calc
    (2*m).choose t*4^t ≤ 2^(2*m)*(2^2)^t := by
      exact Nat.mul_le_mul (Nat.choose_le_two_pow _ _) (by norm_num)
    _ = 2^(2*m+2*t) := by rw [← pow_mul, ← pow_add]
    _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (by omega)

end ThinMatrix.CoefficientBounds

namespace ThinMatrix.CoefficientBounds

open scoped BigOperators
open CyclicRing LinearCircuitBound

/-- The requested conservative bound, including complete cyclic vectors,
all degree pairs, all degree runs, and both residual terms. -/
def uniformBudget (L m t q A : ℕ) : ℕ :=
  q*(t+1)^2*(2*m+1)*2^(100*L+100*m+100)*A^2

theorem low_add_high_budget (L m t q A : ℕ) :
    q*(t+1)^2*2^(14*L+6*m)*A^2 + q*2^(20*L+8*m)*A^2 ≤
      q*(t+1)^2*2^(20*L+8*m+1)*A^2 := by
  have hl : q*(t+1)^2*2^(14*L+6*m)*A^2 ≤ q*(t+1)^2*2^(20*L+8*m)*A^2 := by
    gcongr <;> omega
  have hh : q*2^(20*L+8*m)*A^2 ≤ q*(t+1)^2*2^(20*L+8*m)*A^2 := by
    have hfactor : 1 ≤ (t+1)^2 := by
      have hp : 0 < (t+1)^2 := by positivity
      omega
    have h := Nat.mul_le_mul_right (q*2^(20*L+8*m)*A^2) hfactor
    simpa only [Nat.one_mul, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h
  calc
    _ ≤ q*(t+1)^2*2^(20*L+8*m)*A^2 + q*(t+1)^2*2^(20*L+8*m)*A^2 :=
      Nat.add_le_add hl hh
    _ = _ := by rw [pow_succ]; ring

/-- One degree run evaluates its complete low-plus-high numerator. -/
structure RunNode (L m t q : ℕ) where
  low : LowNode L m t q
  high : HighSum L m q

noncomputable def RunNode.eval {L m t q : ℕ} [NeZero q] (e : RunNode L m t q)
    (sources : ℕ → SourceRow L m) (raw : ℕ → ℤ × Fin q → ℤ) : Cyclic q :=
  fun k => e.low.eval sources raw k + e.high.eval sources raw k

theorem RunNode.eval_bound {L m t q A : ℕ} [NeZero q] (e : RunNode L m t q)
    (sources : ℕ → SourceRow L m) (raw : ℕ → ℤ × Fin q → ℤ)
    (hraw : ∀ i k, |raw i k| ≤ (A : ℤ)) :
    CoeffBound (e.eval sources raw) (q*(t+1)^2*2^(20*L+8*m+1)*A^2) := by
  intro k
  calc
    |e.eval sources raw k| ≤ |e.low.eval sources raw k|+|e.high.eval sources raw k| := abs_add_le _ _
    _ ≤ (q*(t+1)^2*2^(14*L+6*m)*A^2 : ℕ) + (q*2^(20*L+8*m)*A^2 : ℕ) :=
      add_le_add (e.low.eval_bound sources raw hraw k) (e.high.eval_bound sources raw hraw k)
    _ ≤ (q*(t+1)^2*2^(20*L+8*m+1)*A^2 : ℕ) := by
      exact_mod_cast low_add_high_budget L m t q A

/-- A complete finite coefficient pipeline. The rows and circuit trees
are actual data; no intermediate coefficient-size hypothesis is stored. -/
structure Pipeline (L m t q : ℕ) where
  runs : Finset ℕ
  runs_le : runs.card ≤ 2*m+1
  node : ℕ → RunNode L m t q

noncomputable def Pipeline.numerator {L m t q : ℕ} [NeZero q] (e : Pipeline L m t q)
    (sources : ℕ → SourceRow L m) (raw : ℕ → ℤ × Fin q → ℤ) : Cyclic q :=
  fun k => ∑ i ∈ e.runs, (e.node i).eval sources raw k

theorem Pipeline.numerator_bound {L m t q A : ℕ} [NeZero q] (e : Pipeline L m t q)
    (sources : ℕ → SourceRow L m) (raw : ℕ → ℤ × Fin q → ℤ)
    (hraw : ∀ i k, |raw i k| ≤ (A : ℤ)) :
    CoeffBound (e.numerator sources raw) (uniformBudget L m t q A) := by
  have h := finite_sum_bound e.runs (fun i => (e.node i).eval sources raw)
    (q*(t+1)^2*2^(20*L+8*m+1)*A^2) (fun i _ => (e.node i).eval_bound sources raw hraw)
  have h' := h.mono (Nat.mul_le_mul_right _ e.runs_le)
  have hb : (2*m+1)*(q*(t+1)^2*2^(20*L+8*m+1)*A^2) ≤ uniformBudget L m t q A := by
    unfold uniformBudget
    calc
      _ = q*(t+1)^2*(2*m+1)*2^(20*L+8*m+1)*A^2 := by ring
      _ ≤ _ := by gcongr <;> omega
  have h'' := h'.mono hb
  simpa only [CoeffBound, Pipeline.numerator] using h''

/-- Exact division is applied only after the complete scale identity.
It preserves the bound already proved for the complete numerator. -/
theorem exact_normalization_bound {q A : ℕ} (L : ℕ) (numerator product : Cyclic q)
    (hscale : numerator = scale ((4 : ℤ)^L) product)
    (hnum : CoeffBound numerator A) : CoeffBound product A := by
  rw [← decode_complete L numerator product hscale]
  exact decode_bound numerator hnum

/-- The pipeline's complete normalization has the same uniform budget. -/
theorem Pipeline.decoded_bound {L m t q A : ℕ} [NeZero q] (e : Pipeline L m t q)
    (sources : ℕ → SourceRow L m) (raw : ℕ → ℤ × Fin q → ℤ)
    (hraw : ∀ i k, |raw i k| ≤ (A : ℤ)) :
    CoeffBound (decode L (e.numerator sources raw)) (uniformBudget L m t q A) :=
  decode_bound _ (e.numerator_bound sources raw hraw)

/-- Quadratic intermediate budgets fit into the same final budget. -/
theorem quadratic_le_uniform (L m t q A r : ℕ) (hr : r ≤ 100*L+100*m+100) :
    q*2^r*A^2 ≤ uniformBudget L m t q A := by
  have hf : 1 ≤ (t+1)^2*(2*m+1) := by
    have hp : 0 < (t+1)^2*(2*m+1) := by positivity
    omega
  unfold uniformBudget
  calc
    q*2^r*A^2 ≤ q*2^(100*L+100*m+100)*A^2 := by gcongr; omega
    _ ≤ ((t+1)^2*(2*m+1))*(q*2^(100*L+100*m+100)*A^2) := by
      simpa using Nat.mul_le_mul_right (q*2^(100*L+100*m+100)*A^2) hf
    _ = _ := by ring

/-- Linear intermediate budgets also fit, when `A` includes a unit. -/
theorem linear_le_uniform (L m t q A r : ℕ) (hq : 1 ≤ q) (hA : 1 ≤ A)
    (hr : r ≤ 100*L+100*m+100) : 2^r*A ≤ uniformBudget L m t q A := by
  have ha : A ≤ A^2 := by nlinarith
  have hqa : A ≤ q*A^2 := by
    exact ha.trans (by simpa using Nat.mul_le_mul_right (A^2) hq)
  calc
    2^r*A ≤ 2^r*(q*A^2) := Nat.mul_le_mul_left _ hqa
    _ = q*2^r*A^2 := by ring
    _ ≤ _ := quadratic_le_uniform L m t q A r hr

/-- All source, encoded, leaf, and high-state nodes are bounded uniformly
from the raw inputs.  The quantifiers cover every internal circuit node
because any subtree of permitted depth is another `EncodedNode` or
`HighNode` with the same local row-budget interface. -/
theorem every_stage_node_bound {L m t q A : ℕ} [NeZero q]
    (hA : 1 ≤ A) (sources : ℕ → SourceRow L m)
    (raw : ℕ → ℤ × Fin q → ℤ) (hraw : ∀ i k, |raw i k| ≤ (A : ℤ)) :
    (∀ r : SourceRow L m, ∀ k, |r.eval raw k| ≤ (uniformBudget L m t q A : ℤ)) ∧
    (∀ e : EncodedNode L (ℤ × Fin q), ∀ k,
      |e.eval sources raw k| ≤ (uniformBudget L m t q A : ℤ)) ∧
    (∀ e : LeafNode L q, CoeffBound (e.eval sources raw) (uniformBudget L m t q A)) ∧
    (∀ e : HighNode L q, CoeffBound (e.eval sources raw) (uniformBudget L m t q A)) ∧
    (∀ e : LowNode L m t q, CoeffBound (e.eval sources raw) (uniformBudget L m t q A)) ∧
    (∀ e : HighSum L m q, CoeffBound (e.eval sources raw) (uniformBudget L m t q A)) ∧
    (∀ e : Pipeline L m t q, CoeffBound (e.numerator sources raw) (uniformBudget L m t q A)) := by
  have hq : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hl (r : ℕ) (hr : r ≤ 100*L+100*m+100) := linear_le_uniform L m t q A r hq hA hr
  have hquad (r : ℕ) (hr : r ≤ 100*L+100*m+100) := quadratic_le_uniform L m t q A r hr
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r k
    exact (r.eval_bound raw hraw k).trans (by exact_mod_cast hl (L+m) (by omega))
  · intro e k
    exact (e.eval_bound sources raw hraw k).trans (by exact_mod_cast hl (7*L+m) (by omega))
  · intro e
    exact (e.eval_bound sources raw hraw).mono (hquad (14*L+2*m) (by omega))
  · intro e
    exact (e.eval_bound sources raw hraw).mono (hquad (20*L+2*m) (by omega))
  · intro e
    apply (e.eval_bound sources raw hraw).mono
    unfold uniformBudget
    have hrun : 1 ≤ 2*m+1 := by omega
    calc
      q*(t+1)^2*2^(14*L+6*m)*A^2 ≤ q*(t+1)^2*2^(100*L+100*m+100)*A^2 := by
        apply Nat.mul_le_mul_right (A^2)
        apply Nat.mul_le_mul_left (q*(t+1)^2)
        exact Nat.pow_le_pow_right (by norm_num) (by omega)
      _ ≤ (2*m+1)*(q*(t+1)^2*2^(100*L+100*m+100)*A^2) := by
        simpa using Nat.mul_le_mul_right (q*(t+1)^2*2^(100*L+100*m+100)*A^2) hrun
      _ = _ := by ring
  · intro e
    exact (e.eval_bound sources raw hraw).mono (hquad (20*L+8*m) (by omega))
  · intro e
    exact e.numerator_bound sources raw hraw

/-- The natural magnitude budget yields the stated signed integer bits. -/
theorem coeffBound_signedBitLength {L m t q A : ℕ} (a : Cyclic q)
    (ha : CoeffBound a (uniformBudget L m t q A))
    (r cL cm cq cA : ℕ) (hL : L ≤ cL*r) (hm : m ≤ cm*r)
    (hq : q ≤ 2^(cq*r)) (hA : A ≤ 2^(cA*r)) (ht : t ≤ 2*m) (k : Fin q) :
    CoefficientBudget.signedBitLength (a k) ≤
      CoefficientBudget.budgetConstant cL cm cq cA*(r+1)+2 := by
  apply CoefficientBudget.signedBitLength_full_budget (a k) L m t q A r cL cm cq cA hL hm hq hA ht
  have hz : ((a k).natAbs : ℤ) ≤ (uniformBudget L m t q A : ℤ) := by
    simpa only [Int.natCast_natAbs] using ha k
  exact_mod_cast hz

/-- Every evaluated complete numerator has an explicit linear bit bound
when `L,m,log₂ q,log₂ A` have linear budgets in `r`.  Taking `r` of order
`log₂ n` gives the required logarithmic integer word lengths. -/
theorem Pipeline.signedBitLength_bound {L m t q A : ℕ} [NeZero q]
    (e : Pipeline L m t q) (sources : ℕ → SourceRow L m)
    (raw : ℕ → ℤ × Fin q → ℤ) (hraw : ∀ i k, |raw i k| ≤ (A : ℤ))
    (r cL cm cq cA : ℕ) (hL : L ≤ cL*r) (hm : m ≤ cm*r)
    (hq : q ≤ 2^(cq*r)) (hA : A ≤ 2^(cA*r)) (ht : t ≤ 2*m) (k : Fin q) :
    CoefficientBudget.signedBitLength (e.numerator sources raw k) ≤
      CoefficientBudget.budgetConstant cL cm cq cA*(r+1)+2 :=
  coeffBound_signedBitLength (e.numerator sources raw) (e.numerator_bound sources raw hraw)
    r cL cm cq cA hL hm hq hA ht k

end ThinMatrix.CoefficientBounds

#print axioms ThinMatrix.LinearCircuitBound.sweep_four_children_bound_two_pow
#print axioms ThinMatrix.LinearCircuitBound.eval_bound
#print axioms ThinMatrix.CoefficientBounds.SourceRow.eval_bound
#print axioms ThinMatrix.CoefficientBounds.EncodedNode.eval_bound
#print axioms ThinMatrix.CoefficientBounds.LeafNode.eval_bound
#print axioms ThinMatrix.CoefficientBounds.HighNode.eval_bound
#print axioms ThinMatrix.CoefficientBounds.LowNode.eval_bound
#print axioms ThinMatrix.CoefficientBounds.Pipeline.numerator_bound
#print axioms ThinMatrix.CoefficientBounds.exact_normalization_bound
#print axioms ThinMatrix.CoefficientBounds.every_stage_node_bound
#print axioms ThinMatrix.CoefficientBounds.Pipeline.signedBitLength_bound

namespace ThinMatrix.CoefficientBounds

open scoped BigOperators
open CyclicRing LinearCircuitBound

/-- Actual integer rows of the six normal cache forms, ordered as
`x₁,x₂,p₁,p₂`.  Row four is `H(z)`; its `p₁` read is shifted separately. -/
def normalRowCoefficients : Fin 6 → Fin 4 → ℤ :=
  ![![1,0,1,1], ![1,0,1,0], ![0,1,0,-1], ![0,1,0,0],
    ![-1,-1,1,0], ![0,0,0,1]]

/-- Actual opposite rows, ordered as `s,v,w,0`, including `2s`. -/
def oppositeRowCoefficients : Fin 6 → Fin 4 → ℤ :=
  ![![1,1,0,0], ![1,-1,0,0], ![1,1,-1,0], ![1,-1,1,0],
    ![2,0,0,0], ![0,0,1,0]]

theorem normalRowCoefficients_bound (row : Fin 6) (col : Fin 4) :
    |normalRowCoefficients row col| ≤ 2 := by
  fin_cases row <;> fin_cases col <;> norm_num [normalRowCoefficients]

theorem oppositeRowCoefficients_bound (row : Fin 6) (col : Fin 4) :
    |oppositeRowCoefficients row col| ≤ 2 := by
  fin_cases row <;> fin_cases col <;> norm_num [oppositeRowCoefficients]

theorem normalRow_budget (row : Fin 6) : (∑ col, |normalRowCoefficients row col|) ≤ 8 :=
  four_children_budget (by norm_num) _ (normalRowCoefficients_bound row)

theorem oppositeRow_budget (row : Fin 6) : (∑ col, |oppositeRowCoefficients row col|) ≤ 8 :=
  four_children_budget (by norm_num) _ (oppositeRowCoefficients_bound row)

/-- The formal auxiliary shift occurs exactly at the `p₁` cell of `H`.
Using an integer degree grid permits zero-extension at negative degrees. -/
def normalLocalExpr {ι : Type*} {q d : ℕ} (row : Fin 6)
    (children : Fin 4 → Expr ι (ℤ × Fin q) d) : Expr ι (ℤ × Fin q) (d+1) :=
  .node 4 (normalRowCoefficients row) (normalRow_budget row)
    (fun col k => if row = 4 ∧ col = 2 then (k.1-1,k.2) else k) children

def oppositeLocalExpr {ι κ : Type*} {d : ℕ} (row : Fin 6)
    (children : Fin 4 → Expr ι κ d) : Expr ι κ (d+1) :=
  .node 4 (oppositeRowCoefficients row) (oppositeRow_budget row) (fun _ k => k) children

/-- A genuine five-child high-state addition, with unit coefficients. -/
def highFiveExpr {ι κ : Type*} {d : ℕ}
    (children : Fin 5 → Expr ι κ d) : Expr ι κ (d+1) :=
  .node 5 (fun _ => 1) (five_unit_children_budget (by norm_num) _ (by simp))
    (fun _ k => k) children

/-- Partial local accumulators obey the same row budget. -/
theorem partial_row_budget {n : ℕ} (c : Fin n → ℤ)
    (hc : (∑ i, |c i|) ≤ 8) (s : Finset (Fin n)) :
    (∑ i ∈ s, |c i|) ≤ 8 := by
  exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s)
    (fun i _ _ => abs_nonneg (c i))).trans hc

theorem partial_linear_node_bound {n : ℕ} (c x : Fin n → ℤ)
    (hc : (∑ i, |c i|) ≤ 8) (s : Finset (Fin n)) (A : ℤ)
    (hA : 0 ≤ A) (hx : ∀ i, |x i| ≤ A) :
    |∑ i ∈ s, c i*x i| ≤ 8*A := by
  exact linearCombination_abs_le s c (fun i (_ : Fin 1) => x i) A 8 hA
    (fun i _ _ => hx i) (partial_row_budget c hc s) (0 : Fin 1)

/-- A single run is also a complete pipeline with one run, so its
intermediate accumulator satisfies the same uniform majorant. -/
theorem RunNode.uniform_bound {L m t q A : ℕ} [NeZero q] (e : RunNode L m t q)
    (sources : ℕ → SourceRow L m) (raw : ℕ → ℤ × Fin q → ℤ)
    (hraw : ∀ i k, |raw i k| ≤ (A : ℤ)) :
    CoeffBound (e.eval sources raw) (uniformBudget L m t q A) := by
  let p : Pipeline L m t q :=
    { runs := {0}, runs_le := by simp, node := fun _ => e }
  simpa only [CoeffBound, Pipeline.numerator, p, Finset.sum_singleton] using
    p.numerator_bound sources raw hraw

/-- Complete numerator, each degree run, and its exact decoded output
share the same bound; omitted or partial run supports are covered by
`Pipeline.runs_le` in precisely the same way. -/
theorem every_run_and_decode_bound {L m t q A : ℕ} [NeZero q]
    (sources : ℕ → SourceRow L m) (raw : ℕ → ℤ × Fin q → ℤ)
    (hraw : ∀ i k, |raw i k| ≤ (A : ℤ)) :
    (∀ e : RunNode L m t q, CoeffBound (e.eval sources raw) (uniformBudget L m t q A)) ∧
    (∀ e : Pipeline L m t q, CoeffBound (decode L (e.numerator sources raw)) (uniformBudget L m t q A)) :=
  ⟨fun e => e.uniform_bound sources raw hraw, fun e => e.decoded_bound sources raw hraw⟩

end ThinMatrix.CoefficientBounds

#print axioms ThinMatrix.CoefficientBounds.normalRow_budget
#print axioms ThinMatrix.CoefficientBounds.oppositeRow_budget
#print axioms ThinMatrix.CoefficientBounds.partial_linear_node_bound
#print axioms ThinMatrix.CoefficientBounds.RunNode.uniform_bound
#print axioms ThinMatrix.CoefficientBounds.every_run_and_decode_bound
