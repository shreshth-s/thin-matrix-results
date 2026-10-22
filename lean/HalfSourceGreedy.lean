import WalshEmbedding

set_option autoImplicit false

/-!
# Exact rational, bit-by-bit conditional expectation

The score sums once over the character rows and tests whether each remaining
row is zero. It never enumerates completions of the current bit prefix.
`select` evaluates both children once and resolves ties toward false.
This file proves its algebraic contraction. Binary arithmetic costs and the
iteration into the complete small-bias list are separate obligations.
-/

namespace ThinMatrix.HalfSourceGreedy
open ThinMatrix.WalshEmbedding
open scoped BigOperators

variable {A : Type*} [Fintype A]

def tilt (r p q : ℚ) (s : Bool) : ℚ :=
  if s then p/r+q*r else p*r+q/r

def mean (r : ℚ) : ℚ := (r+r⁻¹)/2

def expectation {n : ℕ} (r : ℚ) (p q : A → ℚ)
    (rows : A → Cube n) (signs : A → Bool) : ℚ :=
  ∑ a, if rows a = zeroBits n then tilt r (p a) (q a) (signs a)
       else (p a+q a)*mean r

def tails {n : ℕ} (rows : A → Cube (n+1)) : A → Cube n :=
  fun a => Fin.tail (rows a)

def updateSigns {n : ℕ} (rows : A → Cube (n+1)) (signs : A → Bool)
    (b : Bool) : A → Bool := fun a => Bool.xor (signs a) (rows a 0 && b)

theorem row_zero_iff {n : ℕ} (v : Cube (n+1)) :
    v = zeroBits (n+1) ↔ v 0 = false ∧ Fin.tail v = zeroBits n := by
  constructor
  · intro h
    subst v
    exact ⟨rfl,rfl⟩
  · rintro ⟨h0,ht⟩
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact h0
    · exact congrFun ht j

theorem tilt_balance (r p q : ℚ) (s : Bool) :
    tilt r p q s + tilt r p q (!s) = 2*((p+q)*mean r) := by
  cases s <;> simp only [tilt, Bool.false_eq_true, ↓reduceIte, Bool.not_false,
    Bool.not_true, mean, div_eq_mul_inv] <;> ring

theorem child_balance {n : ℕ} (r : ℚ) (p q : A → ℚ)
    (rows : A → Cube (n+1)) (signs : A → Bool) :
    expectation r p q (tails rows) (updateSigns rows signs false) +
    expectation r p q (tails rows) (updateSigns rows signs true) =
      2*expectation r p q rows signs := by
  unfold expectation
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ht : Fin.tail (rows a) = zeroBits n
  · cases hb : rows a 0
    · have hz := (row_zero_iff (rows a)).mpr ⟨hb,ht⟩
      simp only [tails,updateSigns,hb,Bool.false_and,Bool.xor_false]
      rw [if_pos ht,if_pos hz]
      ring
    · have hz : rows a ≠ zeroBits (n+1) := by
        intro hz
        have := (row_zero_iff (rows a)).mp hz
        simp [hb] at this
      simpa [tails,updateSigns,hb,ht,hz] using tilt_balance r (p a) (q a) (signs a)
  · have hz : rows a ≠ zeroBits (n+1) := by
      intro hz
      exact ht ((row_zero_iff (rows a)).mp hz).2
    simp [tails,ht,hz,two_mul]

def chosenBit {n : ℕ} (r : ℚ) (p q : A → ℚ)
    (rows : A → Cube (n+1)) (signs : A → Bool) : Bool :=
  let e0 := expectation r p q (tails rows) (updateSigns rows signs false)
  let e1 := expectation r p q (tails rows) (updateSigns rows signs true)
  e1 < e0

theorem chosen_le {n : ℕ} (r : ℚ) (p q : A → ℚ)
    (rows : A → Cube (n+1)) (signs : A → Bool) :
    expectation r p q (tails rows) (updateSigns rows signs (chosenBit r p q rows signs)) ≤
      expectation r p q rows signs := by
  have hb := child_balance r p q rows signs
  unfold chosenBit
  dsimp
  by_cases h : expectation r p q (tails rows) (updateSigns rows signs true) <
      expectation r p q (tails rows) (updateSigns rows signs false)
  · simp only [h, decide_true]
    linarith
  · simp only [h, decide_false]
    linarith

def select (r : ℚ) (p q : A → ℚ) :
    (n : ℕ) → (A → Cube n) → (A → Bool) → Cube n
  | 0, _, _ => fun i => Fin.elim0 i
  | n+1, rows, signs =>
      let b := chosenBit r p q rows signs
      Fin.cons b (select r p q n (tails rows) (updateSigns rows signs b))

def terminalSigns {n : ℕ} (rows : A → Cube n) (signs : A → Bool)
    (bits : Cube n) : A → Bool := fun a => Bool.xor (signs a) (dotBits (rows a) bits)

theorem dot_cons {n : ℕ} (a : Cube (n+1)) (b : Bool) (bits : Cube n) :
    dotBits a (Fin.cons b bits) = Bool.xor (a 0 && b) (dotBits (Fin.tail a) bits) := by
  simp [dotBits, List.ofFn_succ, parity, Fin.tail]

omit [Fintype A] in
theorem terminalSigns_cons {n : ℕ} (rows : A → Cube (n+1)) (signs : A → Bool)
    (b : Bool) (bits : Cube n) :
    terminalSigns rows signs (Fin.cons b bits) =
      terminalSigns (tails rows) (updateSigns rows signs b) bits := by
  funext a
  simp only [terminalSigns,dot_cons,updateSigns,tails,Bool.xor_assoc]

theorem select_le (r : ℚ) (p q : A → ℚ) (n : ℕ)
    (rows : A → Cube n) (signs : A → Bool) :
    (∑ a, tilt r (p a) (q a) (terminalSigns rows signs (select r p q n rows signs) a)) ≤
      expectation r p q rows signs := by
  induction n generalizing signs with
  | zero =>
      have hz : ∀ a, rows a = zeroBits 0 := fun _ => Subsingleton.elim _ _
      simp [expectation,hz,terminalSigns,dotBits,parity]
  | succ n ih =>
      rw [select,terminalSigns_cons]
      exact (ih (tails rows) (updateSigns rows signs (chosenBit r p q rows signs))).trans
        (chosen_le r p q rows signs)

theorem expectation_nonzero {n : ℕ} (r : ℚ) (p q : A → ℚ)
    (rows : A → Cube n) (hr : ∀ a, rows a ≠ zeroBits n) (signs : A → Bool) :
    expectation r p q rows signs = (∑ a, (p a + q a))*mean r := by
  simp only [expectation,hr,ite_false,← Finset.sum_mul]

#print axioms row_zero_iff
#print axioms tilt_balance
#print axioms child_balance
#print axioms chosen_le
#print axioms dot_cons
#print axioms terminalSigns_cons
#print axioms select_le
#print axioms expectation_nonzero

end ThinMatrix.HalfSourceGreedy
