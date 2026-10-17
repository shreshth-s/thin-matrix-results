import Mathlib
import CacheBounds

/-!
# Coordinate-by-coordinate source encoding

`sweep` is the actual sequence of local array contractions, rather than a
definition by the desired tensor sum. The correctness theorem proves that
these contractions equal that sum for arbitrary arrays and heterogeneous
local dimensions. Consequently stopping branches of the encoding tree does
not change any retained value.

The finite operation ledger counts the local multiply/add loops and all
coefficient cells at every retained prefix. It charges the complete cyclic
and auxiliary polynomial widths. Translating these scalar operations to a
word-RAM execution additionally requires the coefficient-size bounds and
the implementation of the local fixed-coefficient polynomial forms.
-/

namespace ThinMatrix.EncoderCorrectness

open scoped BigOperators
variable {R : Type*} [CommSemiring R]

abbrev Coordinates {n : ℕ} (dims : Fin n → ℕ) :=
  (i : Fin n) → Fin (dims i)

noncomputable def contractFirst {n : ℕ} (dims : Fin (n+1) → ℕ)
    (form : Fin (dims 0) → R) (input : Coordinates dims → R) :
    Coordinates (fun i : Fin n => dims i.succ) → R :=
  fun rest => ∑ a, form a * input (Fin.cons a rest)

noncomputable def sweep : (n : ℕ) → (dims : Fin n → ℕ) →
    ((i : Fin n) → Fin (dims i) → R) → (Coordinates dims → R) → R
  | 0, _, _, input => input (fun i => Fin.elim0 i)
  | n+1, dims, forms, input =>
    sweep n (fun i => dims i.succ) (fun i => forms i.succ)
      (contractFirst dims (forms 0) input)

noncomputable def tensorSum {n : ℕ} (dims : Fin n → ℕ)
    (forms : (i : Fin n) → Fin (dims i) → R)
    (input : Coordinates dims → R) : R :=
  ∑ a, input a * ∏ i, forms i (a i)

theorem tensorSum_succ {n : ℕ} (dims : Fin (n+1) → ℕ)
    (forms : (i : Fin (n+1)) → Fin (dims i) → R)
    (input : Coordinates dims → R) :
    tensorSum dims forms input =
      tensorSum (fun i : Fin n => dims i.succ) (fun i => forms i.succ)
        (contractFirst dims (forms 0) input) := by
  classical
  unfold tensorSum contractFirst
  rw [← (Fin.consEquiv (fun i => Fin (dims i))).sum_comp
    (fun a => input a * ∏ i, forms i (a i))]
  rw [Fintype.sum_prod_type]
  simp only [Fin.consEquiv, Equiv.coe_fn_mk, Fin.prod_univ_succ,
    Fin.cons_zero, Fin.cons_succ]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro rest _
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem sweep_eq_tensorSum (n : ℕ) (dims : Fin n → ℕ)
    (forms : (i : Fin n) → Fin (dims i) → R)
    (input : Coordinates dims → R) :
    sweep n dims forms input = tensorSum dims forms input := by
  classical
  induction n with
  | zero =>
    simp only [sweep, tensorSum, Fin.prod_univ_zero, mul_one, Fintype.sum_unique]
    congr 1
  | succ n ih =>
    rw [sweep, ih, ← tensorSum_succ]

/-- Pruning changes which branches are evaluated, but the recurrence for a
retained branch is precisely the same `sweep`. No sibling value is needed. -/
theorem retained_branch_correct {n : ℕ} (dims : Fin n → ℕ)
    (forms : Fin n → Fin 6 → (i : Fin n) → Fin (dims i) → R)
    (input : Coordinates dims → R) (word : Fin n → Fin 6) :
    sweep n dims (fun i => forms i (word i) i) input =
      ∑ a, input a * ∏ i, forms i (word i) i (a i) :=
  sweep_eq_tensorSum n dims (fun i => forms i (word i) i) input

open ThinMatrix.CacheBounds

/-- A conservative local loop ledger: six forms, at most four source
coordinates, an addition and scaling per term, plus a coefficient write.
Both complete coefficient widths remain explicit. -/
noncomputable def coefficientLoopCost (L m t q width : ℕ)
    (firstNormal : Bool) : ℕ :=
  ∑ d : Fin (2*L+1),
    Fintype.card (Prefixes L m t d.val) *
      rawVolume L d.val firstNormal * 6 * 9 * q * width

theorem coefficientLoopCost_eq (L m t q width : ℕ) (firstNormal : Bool) :
    coefficientLoopCost L m t q width firstNormal =
      54 * q * width * totalVolume L m t firstNormal := by
  classical
  unfold coefficientLoopCost totalVolume
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d _
  ring

theorem coefficientLoopCost_le (L m t q width : ℕ) (firstNormal : Bool) :
    coefficientLoopCost L m t q width firstNormal ≤
      54 * q * width * (2*L+1) * retainedLeafCount L m t := by
  rw [coefficientLoopCost_eq]
  have h := Nat.mul_le_mul_left (54*q*width)
    (total_volume_le L m t firstNormal)
  simpa only [Nat.mul_assoc] using h

#print axioms sweep_eq_tensorSum
#print axioms retained_branch_correct
#print axioms coefficientLoopCost_le

end ThinMatrix.EncoderCorrectness
