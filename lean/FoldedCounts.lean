import CyclicRing
import Mathlib.Data.Matrix.Mul
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic

/-!
# Folded modular triangle counts with a cyclic factor

This formalizes the finite count identity of `lem:folded-cyclic-factor`.
Weights are arbitrary signed integers.  The entries are the actual residue
indicators times cyclic monomials, and only the designated coefficient is
read.  Zero padding is explicit.  No running-time theorem is asserted here.
-/

namespace ThinMatrix.FoldedCounts

open scoped BigOperators
open Fin.CommRing
open ThinMatrix.CyclicRing

variable {d q : ℕ} [NeZero d] [NeZero q]

/-- The left input entry at residue-folded row coordinate `rho1`. -/
noncomputable def leftEntry (l : ℤ) (rho1 sigma : ZMod d) : Cyclic q :=
  if sigma = (l : ZMod d) + rho1 then monomial (l : Fin q) 1 else 0

/-- The right input entry at residue-folded column coordinate `rho2`. -/
noncomputable def rightEntry (r : ℤ) (d1 : ℕ) (rho2 sigma : ZMod d) : Cyclic q :=
  if sigma = -(r : ZMod d) - (d1 : ZMod d) * rho2 then
    monomial (r : Fin q) 1 else 0

theorem fin_intCast_eq_zero_iff (z : ℤ) :
    (z : Fin q) = 0 ↔ (q : ℤ) ∣ z := by
  rw [← (ZMod.finEquiv q).injective.eq_iff]
  simpa using ZMod.intCast_zmod_eq_zero_iff_dvd z q

theorem designated_exponent_iff (l r t : ℤ) :
    ((-t : ℤ) : Fin q) = (l : Fin q) + (r : Fin q) ↔
      (q : ℤ) ∣ l + r + t := by
  rw [← fin_intCast_eq_zero_iff (q := q)]
  push_cast
  constructor <;> intro h <;> linear_combination -h

omit [NeZero d] in
theorem folded_residue_iff (l r t : ℤ) (d1 : ℕ) (rho1 rho2 : ZMod d)
    (locator : (t : ZMod d) = rho1 + (d1 : ZMod d) * rho2) :
    (l : ZMod d) + rho1 = -(r : ZMod d) - (d1 : ZMod d) * rho2 ↔
      (d : ℤ) ∣ l + r + t := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [locator]
  constructor <;> intro h <;> linear_combination h

/-- Summing the middle residue selects at most one sigma, with no multiplicity d. -/
theorem sigma_sum (l r : ℤ) (d1 : ℕ) (rho1 rho2 : ZMod d) :
    (∑ sigma : ZMod d, leftEntry (q := q) l rho1 sigma *
      rightEntry (q := q) r d1 rho2 sigma) =
    if (l : ZMod d) + rho1 = -(r : ZMod d) - (d1 : ZMod d) * rho2 then
      monomial ((l : Fin q) + (r : Fin q)) 1 else 0 := by
  classical
  simp [leftEntry, rightEntry, monomial_mul, eq_comm]

omit [NeZero d] [NeZero q] in
/-- Coprimality identifies the two modular tests with the product modulus. -/
theorem coprime_divisibility (coprime : d.Coprime q) (z : ℤ) :
    (d : ℤ) ∣ z ∧ (q : ℤ) ∣ z ↔ ((d*q : ℕ) : ℤ) ∣ z := by
  constructor
  · rintro ⟨hd, hq⟩
    simpa only [Nat.cast_mul] using coprime.isCoprime.mul_dvd hd hq
  · intro h
    constructor
    · exact dvd_trans (by exact ⟨(q : ℤ), by simp⟩) h
    · exact dvd_trans (by exact ⟨(d : ℤ), by simp [mul_comm]⟩) h

/-- One original middle vertex contributes one exactly when dq divides its sum. -/
theorem vertex_count (coprime : d.Coprime q) (l r t : ℤ) (d1 : ℕ)
    (rho1 rho2 : ZMod d)
    (locator : (t : ZMod d) = rho1 + (d1 : ZMod d) * rho2) :
    (∑ sigma : ZMod d, leftEntry (q := q) l rho1 sigma *
      rightEntry (q := q) r d1 rho2 sigma) ((-t : ℤ) : Fin q) =
      if ((d*q : ℕ) : ℤ) ∣ l+r+t then 1 else 0 := by
  classical
  rw [sigma_sum]
  by_cases h : (l : ZMod d) + rho1 = -(r : ZMod d) - (d1 : ZMod d) * rho2
  · rw [if_pos h, monomial_coeff]
    have hd := (folded_residue_iff l r t d1 rho1 rho2 locator).mp h
    simp only [designated_exponent_iff, ← coprime_divisibility coprime, hd, true_and]
  · rw [if_neg h, zero_coeff]
    have hd : ¬ (d : ℤ) ∣ l+r+t := by
      intro hh
      exact h ((folded_residue_iff l r t d1 rho1 rho2 locator).mpr hh)
    simp only [← coprime_divisibility coprime, hd, false_and, ↓reduceIte]

section Matrices

variable {A B V : Type*} [Fintype V] [DecidableEq V] {width : ℕ}

/-- Padding is implemented by zero rows in the middle-index dimension. -/
noncomputable def leftMatrix (active : Finset V) (w : A → V → ℤ) :
    Matrix (A × Fin width) (V × ZMod d) (Cyclic q) :=
  fun row middle => if middle.1 ∈ active then
    leftEntry (w row.1 middle.1) (row.2.val : ZMod d) middle.2 else 0

/-- The right matrix has the same middle vertex/residue indices. -/
noncomputable def rightMatrix (w : V → B → ℤ) (d1 : ℕ) :
    Matrix (V × ZMod d) (B × Fin width) (Cyclic q) :=
  fun middle column =>
    rightEntry (w middle.1 column.1) d1 (column.2.val : ZMod d) middle.2

omit [NeZero d] [Fintype V] in
@[simp] theorem absent_left_entry (active : Finset V) (w : A → V → ℤ)
    (row : A × Fin width) (v : V) (sigma : ZMod d) (absent : v ∉ active) :
    leftMatrix (q := q) active w row (v, sigma) = 0 := by
  simp [leftMatrix, absent]

/-- The actual matrix product is one folded residue sum for each active vertex. -/
theorem matrix_product_entry (active : Finset V) (wl : A → V → ℤ)
    (wr : V → B → ℤ) (d1 : ℕ) (a : A) (b : B) (rho1 rho2 : Fin width) :
    (leftMatrix (d := d) (q := q) (width := width) active wl *
      rightMatrix (d := d) (q := q) (width := width) wr d1 :
      Matrix (A × Fin width) (B × Fin width) (Cyclic q))
      (a, rho1) (b, rho2) =
    ∑ v ∈ active, ∑ sigma : ZMod d,
      leftEntry (wl a v) (rho1.val : ZMod d) sigma *
      rightEntry (wr v b) d1 (rho2.val : ZMod d) sigma := by
  classical
  simp [Matrix.mul_apply, Fintype.sum_prod_type, leftMatrix, rightMatrix,
    Finset.sum_ite_irrel]

/-- The selected coefficient counts exactly the original active middle vertices.

There is one coefficient at one row/column position for the entire incidence;
the right side has neither a residue multiplicity nor a sum over q queries.
-/
theorem folded_matrix_count (coprime : d.Coprime q) (active : Finset V)
    (wl : A → V → ℤ) (wr : V → B → ℤ) (wt : A → B → ℤ)
    (d1 : ℕ) (a : A) (b : B) (rho1 rho2 : Fin width)
    (locator : (wt a b : ZMod d) =
      (rho1.val : ZMod d) + (d1 : ZMod d) * (rho2.val : ZMod d)) :
    ((leftMatrix (d := d) (q := q) (width := width) active wl *
      rightMatrix (d := d) (q := q) (width := width) wr d1 :
      Matrix (A × Fin width) (B × Fin width) (Cyclic q))
      (a, rho1) (b, rho2)) ((-wt a b : ℤ) : Fin q) =
    ((active.filter fun v => ((d*q : ℕ) : ℤ) ∣ wl a v + wr v b + wt a b).card : ℤ) := by
  classical
  rw [matrix_product_entry, sum_coeff]
  simp_rw [vertex_count coprime _ _ _ d1 _ _ locator]
  exact Finset.sum_boole _ _

/-- With h padded middle vertices the inner dimension is exactly h*d. -/
theorem middle_dimension (h : ℕ) :
    Fintype.card (Fin h × ZMod d) = h*d := by
  simp

/-- Padding both outer dimensions to width gives n*width rows and columns. -/
theorem outer_dimension (n width : ℕ) :
    Fintype.card (Fin n × Fin width) = n*width := by
  simp

end Matrices

/-- For positive d this is exactly the least integer at least sqrt(d). -/
def foldWidth (d : ℕ) : ℕ := Nat.sqrt (d-1) + 1

omit [NeZero d] [NeZero q] in
theorem foldWidth_pos (d : ℕ) : 0 < foldWidth d := by
  simp [foldWidth]

theorem modulus_fits : d ≤ foldWidth d * foldWidth d := by
  have h := Nat.lt_succ_sqrt (d-1)
  simp only [Nat.succ_eq_add_one] at h
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  dsimp [foldWidth]
  omega

theorem foldWidth_minimal (r : ℕ) (fit : d ≤ r*r) : foldWidth d ≤ r := by
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have h : d-1 < r*r := by omega
  have hs := Nat.sqrt_lt.mpr h
  dsimp [foldWidth]
  omega

/-- The unpadded second residue range is ceil(d / foldWidth(d)). -/
def secondWidth (d : ℕ) : ℕ := (d-1) / foldWidth d + 1

theorem secondWidth_fits : d ≤ foldWidth d * secondWidth d := by
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hmod := Nat.mod_lt (d-1) (foldWidth_pos d)
  have heq := Nat.mod_add_div (d-1) (foldWidth d)
  dsimp [secondWidth]
  rw [Nat.mul_add, Nat.mul_one]
  omega

theorem secondWidth_minimal (r : ℕ) (fit : d ≤ foldWidth d * r) :
    secondWidth d ≤ r := by
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hf : d ≤ r * foldWidth d := by simpa only [Nat.mul_comm] using fit
  have h : d-1 < r * foldWidth d := by omega
  have hdiv := (Nat.div_lt_iff_lt_mul (foldWidth_pos d)).mpr h
  dsimp [secondWidth]
  omega

theorem secondWidth_le : secondWidth d ≤ foldWidth d := by
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hf := modulus_fits (d := d)
  have h : d-1 < foldWidth d * foldWidth d := by omega
  have hdiv := (Nat.div_lt_iff_lt_mul (foldWidth_pos d)).mpr h
  dsimp [secondWidth]
  omega

/-- The low digit of the unique chosen folded residue position. -/
def residueLow (z : ZMod d) : Fin (foldWidth d) :=
  ⟨z.val % foldWidth d, Nat.mod_lt _ (foldWidth_pos d)⟩

/-- The high digit, padded to the same outer width as the low digit. -/
def residueHigh (z : ZMod d) : Fin (foldWidth d) :=
  ⟨z.val / foldWidth d,
    (Nat.div_lt_iff_lt_mul (foldWidth_pos d)).mpr
      ((ZMod.val_lt z).trans_le (modulus_fits (d := d)))⟩

theorem residueHigh_unpadded (z : ZMod d) :
    (residueHigh z).val < secondWidth d := by
  have hz : z.val ≤ d-1 := by have := ZMod.val_lt z; omega
  have h := Nat.div_le_div_right hz (c := foldWidth d)
  exact Nat.lt_succ_of_le h

/-- This is the actual residue locator used for the single requested coefficient. -/
theorem residue_locator (z : ZMod d) :
    z = ((residueLow z).val : ZMod d) +
      (foldWidth d : ZMod d) * ((residueHigh z).val : ZMod d) := by
  change z = (z.val % foldWidth d : ℕ) +
    (foldWidth d : ZMod d) * (z.val / foldWidth d : ℕ)
  rw [← Nat.cast_mul, ← Nat.cast_add, Nat.mod_add_div]
  exact (ZMod.natCast_zmod_val z).symm

/-- The full finite folded embedding, including its computed residue locator. -/
theorem canonical_folded_count {A B V : Type*} [Fintype V] [DecidableEq V]
    (coprime : d.Coprime q) (active : Finset V)
    (wl : A → V → ℤ) (wr : V → B → ℤ) (wt : A → B → ℤ) (a : A) (b : B) :
    ((leftMatrix (d := d) (q := q) active wl * rightMatrix wr (foldWidth d) :
      Matrix (A × Fin (foldWidth d)) (B × Fin (foldWidth d)) (Cyclic q))
      (a, residueLow (wt a b : ZMod d)) (b, residueHigh (wt a b : ZMod d)))
      ((-wt a b : ℤ) : Fin q) =
    ((active.filter fun v => ((d*q : ℕ) : ℤ) ∣ wl a v + wr v b + wt a b).card : ℤ) := by
  apply folded_matrix_count coprime
  exact residue_locator _

omit [NeZero d] in
/-- Both actual padded outer dimensions have the claimed value. -/
theorem folded_outer_dimension (n : ℕ) :
    Fintype.card (Fin n × Fin (foldWidth d)) = n * foldWidth d := by
  simp

end ThinMatrix.FoldedCounts

#print axioms ThinMatrix.FoldedCounts.canonical_folded_count
#print axioms ThinMatrix.FoldedCounts.matrix_product_entry
#print axioms ThinMatrix.FoldedCounts.vertex_count
#print axioms ThinMatrix.FoldedCounts.residue_locator
#print axioms ThinMatrix.FoldedCounts.middle_dimension
#print axioms ThinMatrix.FoldedCounts.folded_outer_dimension
