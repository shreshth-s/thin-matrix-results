import Mathlib

/-!
Arithmetic on explicit little-endian Boolean lists.

The model charges Boolean gates, reads, writes, and decisions on individual
bits. A processed full-adder/subtractor column has a conservative charge of
12; the terminal case has charge 1. Long division uses one full subtraction
and a fixed charge 8 per input bit. List cons denotes writing one bit, not a
unit-cost shift of an unbounded machine integer. Natural/integer values are
semantic interpretations of the lists; they are not arithmetic primitives in
the list algorithms. No execution bridge to the project's word machine is
asserted by this module.

All `Counted` evaluators below are joint value/counter recursions and store each
recursive child once. The counters are ghost annotations of this bit-serial
instruction model, rather than a charge for executing the counters themselves.
The separate `Steps` functions are proof-only formulas and may recompute
semantic values; executable counted evaluators never call those formulas.
Canonical `ofInt`/`Nat.bits` wrappers specify input/output representation. Their
bounds apply to inputs already supplied as sign-and-magnitude bits and do not
claim a free conversion from an opaque word-machine integer.
-/

namespace ThinMatrix.IntegerArithmetic

def digit (b : Bool) : ℕ := if b then 1 else 0
@[simp] theorem digit_false : digit false = 0 := rfl
@[simp] theorem digit_true : digit true = 1 := rfl
def value : List Bool → ℕ
  | [] => 0
  | b :: bs => digit b + 2 * value bs

theorem digit_le_one (b : Bool) : digit b ≤ 1 := by cases b <;> decide

theorem value_lt (bs : List Bool) : value bs < 2 ^ bs.length := by
  induction bs with
  | nil => simp [value]
  | cons b bs ih =>
    have hb := digit_le_one b
    simp only [value, List.length_cons, pow_succ]
    omega

theorem value_size (bs : List Bool) : (value bs).size ≤ bs.length :=
  Nat.size_le.mpr (value_lt bs)

def fullAdd (a b c : Bool) : Bool × Bool :=
  (Bool.xor (Bool.xor a b) c, (a && b) || (c && (a || b)))

def fullSub (a b c : Bool) : Bool × Bool :=
  (Bool.xor (Bool.xor a b) c, ((!a) && (b || c)) || (b && c))

theorem fullAdd_correct (a b c : Bool) :
    digit (fullAdd a b c).1 + 2 * digit (fullAdd a b c).2 =
      digit a + digit b + digit c := by
  cases a <;> cases b <;> cases c <;> decide

theorem fullSub_correct (a b c : Bool) :
    digit a + 2 * digit (fullSub a b c).2 =
      digit (fullSub a b c).1 + digit b + digit c := by
  cases a <;> cases b <;> cases c <;> decide

def addBits : List Bool → List Bool → Bool → List Bool
  | [], [], c => if c then [true] else []
  | a :: xs, [], c =>
    let p := fullAdd a false c
    p.1 :: addBits xs [] p.2
  | [], b :: ys, c =>
    let p := fullAdd false b c
    p.1 :: addBits [] ys p.2
  | a :: xs, b :: ys, c =>
    let p := fullAdd a b c
    p.1 :: addBits xs ys p.2
  termination_by xs ys _ => xs.length + ys.length
  decreasing_by all_goals (simp_wf <;> omega)

theorem addBits_correct (xs ys : List Bool) (c : Bool) :
    value (addBits xs ys c) = value xs + value ys + digit c := by
  induction xs generalizing ys c with
  | nil =>
    induction ys generalizing c with
    | nil => cases c <;> simp [addBits, value, digit]
    | cons b ys ih =>
      have ht := ih (fullAdd false b c).2
      have hb := fullAdd_correct false b c
      simp only [addBits, value] at *
      simp only [digit_false] at hb
      omega
  | cons a xs ih =>
    cases ys with
    | nil =>
      have ht := ih [] (fullAdd a false c).2
      have hb := fullAdd_correct a false c
      simp only [addBits, value] at *
      simp only [digit_false] at hb
      omega
    | cons b ys =>
      have ht := ih ys (fullAdd a b c).2
      have hb := fullAdd_correct a b c
      simp only [addBits, value] at *
      omega

theorem addBits_length (xs ys : List Bool) (c : Bool) :
    (addBits xs ys c).length ≤ max xs.length ys.length + 1 := by
  induction xs generalizing ys c with
  | nil =>
    induction ys generalizing c with
    | nil => cases c <;> simp [addBits]
    | cons b ys ih =>
      simpa only [addBits, List.length_cons, List.length_nil, zero_max] using
        Nat.succ_le_succ (ih (fullAdd false b c).2)
  | cons a xs ih =>
    cases ys with
    | nil =>
      simpa only [addBits, List.length_cons, List.length_nil, Nat.max_zero] using
        Nat.succ_le_succ (ih [] (fullAdd a false c).2)
    | cons b ys =>
      simpa only [addBits, List.length_cons, max_add_add_right] using
        Nat.succ_le_succ (ih ys (fullAdd a b c).2)

def subBits : List Bool → List Bool → Bool → List Bool × Bool
  | [], [], c => ([], c)
  | a :: xs, [], c =>
    let p := fullSub a false c
    let t := subBits xs [] p.2
    (p.1 :: t.1, t.2)
  | [], b :: ys, c =>
    let p := fullSub false b c
    let t := subBits [] ys p.2
    (p.1 :: t.1, t.2)
  | a :: xs, b :: ys, c =>
    let p := fullSub a b c
    let t := subBits xs ys p.2
    (p.1 :: t.1, t.2)
  termination_by xs ys _ => xs.length + ys.length
  decreasing_by all_goals (simp_wf <;> omega)

theorem subBits_length (xs ys : List Bool) (c : Bool) :
    (subBits xs ys c).1.length = max xs.length ys.length := by
  induction xs generalizing ys c with
  | nil =>
    induction ys generalizing c with
    | nil => simp [subBits]
    | cons b ys ih => simp [subBits, ih]
  | cons a xs ih =>
    cases ys with
    | nil => simp [subBits, ih]
    | cons b ys => simp [subBits, ih, max_add_add_right]

/-- Borrow is recorded with its actual power-of-two place value. -/
theorem subBits_invariant (xs ys : List Bool) (c : Bool) :
    value xs + 2 ^ max xs.length ys.length * digit (subBits xs ys c).2 =
      value (subBits xs ys c).1 + value ys + digit c := by
  induction xs generalizing ys c with
  | nil =>
    induction ys generalizing c with
    | nil => simp [subBits, value]
    | cons b ys ih =>
      have ht := ih (fullSub false b c).2
      have hb := fullSub_correct false b c
      simp only [subBits, value, List.length_nil, List.length_cons, zero_max, pow_succ] at *
      simp only [digit_false] at hb
      nlinarith
  | cons a xs ih =>
    cases ys with
    | nil =>
      have ht := ih [] (fullSub a false c).2
      have hb := fullSub_correct a false c
      simp only [subBits, value, List.length_nil, List.length_cons, Nat.max_zero, pow_succ] at *
      simp only [digit_false] at hb
      nlinarith
    | cons b ys =>
      have ht := ih ys (fullSub a b c).2
      have hb := fullSub_correct a b c
      simp only [subBits, value, List.length_cons, max_add_add_right, pow_succ] at *
      nlinarith

theorem subBits_borrow (xs ys : List Bool) :
    (subBits xs ys false).2 = true ↔ value xs < value ys := by
  have hi := subBits_invariant xs ys false
  have ho := value_lt (subBits xs ys false).1
  rw [subBits_length] at ho
  cases hb : (subBits xs ys false).2 <;> simp [hb] at hi ⊢ <;> omega

theorem subBits_value (xs ys : List Bool) (h : value ys ≤ value xs) :
    value (subBits xs ys false).1 = value xs - value ys := by
  have hi := subBits_invariant xs ys false
  have hb : (subBits xs ys false).2 = false := by
    cases he : (subBits xs ys false).2 with
    | false => rfl
    | true => have := (subBits_borrow xs ys).mp he; omega
  simp only [hb, digit_false, mul_zero, add_zero] at hi
  omega

/-- The concrete full-column loops charge both missing-operand and ordinary columns. -/
def columnSteps : List Bool → List Bool → ℕ
  | [], [] => 1
  | _ :: xs, [] => 12 + columnSteps xs []
  | [], _ :: ys => 12 + columnSteps [] ys
  | _ :: xs, _ :: ys => 12 + columnSteps xs ys
  termination_by xs ys => xs.length + ys.length
  decreasing_by all_goals (simp_wf <;> omega)

theorem columnSteps_eq (xs ys : List Bool) :
    columnSteps xs ys = 12 * max xs.length ys.length + 1 := by
  induction xs generalizing ys with
  | nil =>
    induction ys with
    | nil => simp [columnSteps]
    | cons b ys ih => simp [columnSteps, ih]; omega
  | cons a xs ih =>
    cases ys with
    | nil => simp [columnSteps, ih]; omega
    | cons b ys => simp [columnSteps, ih, max_add_add_right]; omega

def addCounted : List Bool → List Bool → Bool → List Bool × ℕ
  | [], [], c => (if c then [true] else [], 1)
  | a :: xs, [], c =>
    let p := fullAdd a false c
    let tail := addCounted xs [] p.2
    (p.1 :: tail.1, tail.2 + 12)
  | [], b :: ys, c =>
    let p := fullAdd false b c
    let tail := addCounted [] ys p.2
    (p.1 :: tail.1, tail.2 + 12)
  | a :: xs, b :: ys, c =>
    let p := fullAdd a b c
    let tail := addCounted xs ys p.2
    (p.1 :: tail.1, tail.2 + 12)
  termination_by xs ys _ => xs.length + ys.length
  decreasing_by all_goals (simp_wf <;> omega)

theorem addCounted_projections (xs ys : List Bool) (c : Bool) :
    (addCounted xs ys c).1 = addBits xs ys c ∧
      (addCounted xs ys c).2 = columnSteps xs ys := by
  induction xs generalizing ys c with
  | nil =>
    induction ys generalizing c with
    | nil => simp [addCounted, addBits, columnSteps]
    | cons b ys ih => simpa [addCounted, addBits, columnSteps, Nat.add_comm] using ih (fullAdd false b c).2
  | cons a xs ih =>
    cases ys with
    | nil => simpa [addCounted, addBits, columnSteps, Nat.add_comm] using ih [] (fullAdd a false c).2
    | cons b ys => simpa [addCounted, addBits, columnSteps, Nat.add_comm] using ih ys (fullAdd a b c).2

def subCounted : List Bool → List Bool → Bool → (List Bool × Bool) × ℕ
  | [], [], c => (([], c), 1)
  | a :: xs, [], c =>
    let p := fullSub a false c
    let tail := subCounted xs [] p.2
    ((p.1 :: tail.1.1, tail.1.2), tail.2 + 12)
  | [], b :: ys, c =>
    let p := fullSub false b c
    let tail := subCounted [] ys p.2
    ((p.1 :: tail.1.1, tail.1.2), tail.2 + 12)
  | a :: xs, b :: ys, c =>
    let p := fullSub a b c
    let tail := subCounted xs ys p.2
    ((p.1 :: tail.1.1, tail.1.2), tail.2 + 12)
  termination_by xs ys _ => xs.length + ys.length
  decreasing_by all_goals (simp_wf <;> omega)

theorem subCounted_projections (xs ys : List Bool) (c : Bool) :
    (subCounted xs ys c).1 = subBits xs ys c ∧
      (subCounted xs ys c).2 = columnSteps xs ys := by
  induction xs generalizing ys c with
  | nil =>
    induction ys generalizing c with
    | nil => simp [subCounted, subBits, columnSteps]
    | cons b ys ih =>
      obtain ⟨hv, hc⟩ := ih (fullSub false b c).2
      simp [subCounted, subBits, columnSteps, hv, hc, Nat.add_comm]
  | cons a xs ih =>
    cases ys with
    | nil =>
      obtain ⟨hv, hc⟩ := ih [] (fullSub a false c).2
      simp [subCounted, subBits, columnSteps, hv, hc, Nat.add_comm]
    | cons b ys =>
      obtain ⟨hv, hc⟩ := ih ys (fullSub a b c).2
      simp [subCounted, subBits, columnSteps, hv, hc, Nat.add_comm]

def mulBits (xs ys : List Bool) : List Bool :=
  match xs with
  | [] => []
  | b :: bs => addBits (if b then ys else []) (false :: mulBits bs ys) false

theorem mulBits_correct (xs ys : List Bool) : value (mulBits xs ys) = value xs * value ys := by
  induction xs with
  | nil => simp [mulBits, value]
  | cons b bs ih =>
    cases b <;> simp [mulBits, addBits_correct, value, ih] <;> ring

theorem mulBits_length (xs ys : List Bool) :
    (mulBits xs ys).length ≤ 2 * xs.length + ys.length + 1 := by
  induction xs with
  | nil => simp [mulBits]
  | cons b bs ih =>
    have hp : (if b then ys else []).length ≤ ys.length := by cases b <;> simp
    have ha := addBits_length (if b then ys else []) (false :: mulBits bs ys) false
    have hm : max (if b then ys else []).length (false :: mulBits bs ys).length ≤
        2 * bs.length + ys.length + 2 := by
      apply max_le
      · omega
      · simp only [List.length_cons]; omega
    change (addBits (if b then ys else []) (false :: mulBits bs ys) false).length ≤ _
    simp only [List.length_cons]
    omega

def mulSteps (xs ys : List Bool) : ℕ :=
  match xs with
  | [] => 1
  | b :: bs => mulSteps bs ys +
    columnSteps (if b then ys else []) (false :: mulBits bs ys) + 4

def mulCounted (xs ys : List Bool) : List Bool × ℕ :=
  match xs with
  | [] => ([], 1)
  | b :: bs =>
    let child := mulCounted bs ys
    let sum := addCounted (if b then ys else []) (false :: child.1) false
    (sum.1, child.2 + sum.2 + 4)

theorem mulCounted_projections (xs ys : List Bool) :
    (mulCounted xs ys).1 = mulBits xs ys ∧ (mulCounted xs ys).2 = mulSteps xs ys := by
  induction xs with
  | nil => simp [mulCounted, mulBits, mulSteps]
  | cons b bs ih =>
    obtain ⟨hv, hc⟩ := ih
    have ha := addCounted_projections (if b then ys else []) (false :: mulBits bs ys) false
    simp [mulCounted, mulBits, mulSteps, hv, hc, ha.1, ha.2]

theorem mulSteps_bound (xs ys : List Bool) :
    mulSteps xs ys ≤ 40 * (xs.length + 1) * (xs.length + ys.length + 2) := by
  induction xs with
  | nil => simp [mulSteps]; omega
  | cons b bs ih =>
    have hp : (if b then ys else []).length ≤ ys.length := by cases b <;> simp
    have hl := mulBits_length bs ys
    have hm : max (if b then ys else []).length (false :: mulBits bs ys).length ≤
        2 * bs.length + ys.length + 2 := by
      apply max_le
      · omega
      · simp only [List.length_cons]; omega
    have hs := columnSteps_eq (if b then ys else []) (false :: mulBits bs ys)
    simp only [mulSteps, List.length_cons]
    nlinarith

/-- High prefixes are processed first; one subtraction supplies comparison and remainder. -/
def divideBits (divisor : List Bool) : List Bool → List Bool × List Bool
  | [] => ([], [])
  | b :: bs =>
    let previous := divideBits divisor bs
    let shifted := b :: previous.2
    let trial := subBits shifted divisor false
    if trial.2 then (false :: previous.1, shifted)
    else (true :: previous.1, trial.1)

theorem divideBits_correct (divisor input : List Bool) (hD : 0 < value divisor) :
    value input = value (divideBits divisor input).1 * value divisor +
      value (divideBits divisor input).2 ∧
      value (divideBits divisor input).2 < value divisor := by
  induction input with
  | nil => simpa [divideBits, value] using hD
  | cons b bs ih =>
    obtain ⟨hi, hr⟩ := ih
    have hb := digit_le_one b
    have hshift : value (b :: (divideBits divisor bs).2) < 2 * value divisor := by
      simp only [value]
      omega
    simp only [divideBits]
    split_ifs with ht
    · have hlo := (subBits_borrow (b :: (divideBits divisor bs).2) divisor).mp ht
      constructor
      · simp only [value, digit_false]
        nlinarith
      · exact hlo
    · have hbf : (subBits (b :: (divideBits divisor bs).2) divisor false).2 = false := by
        cases he : (subBits (b :: (divideBits divisor bs).2) divisor false).2 <;> simp_all
      have hs := subBits_invariant (b :: (divideBits divisor bs).2) divisor false
      simp only [hbf, digit_false, mul_zero, add_zero, value] at hs hshift
      constructor
      · simp only [value, digit_true]
        nlinarith
      · change value (subBits (b :: (divideBits divisor bs).2) divisor false).1 < value divisor
        omega

theorem divideBits_quotient_length (divisor input : List Bool) :
    (divideBits divisor input).1.length = input.length := by
  induction input with
  | nil => simp [divideBits]
  | cons b bs ih => simp only [divideBits]; split_ifs <;> simp [ih]

theorem divideBits_remainder_length (divisor input : List Bool) :
    (divideBits divisor input).2.length ≤ input.length + divisor.length := by
  induction input with
  | nil => simp [divideBits]
  | cons b bs ih =>
    simp only [divideBits]
    split_ifs
    · simp only [List.length_cons]
      omega
    · rw [subBits_length]
      simp only [List.length_cons]
      apply max_le <;> omega

def divideSteps (divisor : List Bool) : List Bool → ℕ
  | [] => 1
  | b :: bs => divideSteps divisor bs +
    columnSteps (b :: (divideBits divisor bs).2) divisor + 8

def divideCounted (divisor : List Bool) : List Bool → (List Bool × List Bool) × ℕ
  | [] => (([], []), 1)
  | b :: bs =>
    let child := divideCounted divisor bs
    let shifted := b :: child.1.2
    let trial := subCounted shifted divisor false
    (if trial.1.2 then (false :: child.1.1, shifted) else (true :: child.1.1, trial.1.1),
      child.2 + trial.2 + 8)

theorem divideCounted_projections (divisor input : List Bool) :
    (divideCounted divisor input).1 = divideBits divisor input ∧
      (divideCounted divisor input).2 = divideSteps divisor input := by
  induction input with
  | nil => simp [divideCounted, divideBits, divideSteps]
  | cons b bs ih =>
    obtain ⟨hv, hc⟩ := ih
    have hs := subCounted_projections (b :: (divideBits divisor bs).2) divisor false
    simp [divideCounted, divideBits, divideSteps, hv, hc, hs.1, hs.2]

theorem divideSteps_bound (divisor input : List Bool) :
    divideSteps divisor input ≤ 20 * (input.length + 1) *
      (input.length + divisor.length + 1) := by
  induction input with
  | nil => simp [divideSteps]; omega
  | cons b bs ih =>
    have hl := divideBits_remainder_length divisor bs
    have hm : max (b :: (divideBits divisor bs).2).length divisor.length ≤
        bs.length + divisor.length + 1 := by
      simp only [List.length_cons]
      apply max_le <;> omega
    have hs := columnSteps_eq (b :: (divideBits divisor bs).2) divisor
    simp only [divideSteps, List.length_cons]
    nlinarith

theorem divideBits_quotient (divisor input : List Bool) (hD : 0 < value divisor) :
    value (divideBits divisor input).1 = value input / value divisor := by
  obtain ⟨hi, hr⟩ := divideBits_correct divisor input hD
  symm
  apply Nat.div_eq_of_lt_le
  · omega
  · nlinarith

theorem divide_step_width (divisor input : List Bool) (b : Bool) :
    (b :: (divideBits divisor input).2).length ≤ input.length + divisor.length + 1 ∧
      (subBits (b :: (divideBits divisor input).2) divisor false).1.length ≤
        input.length + divisor.length + 1 := by
  have hr := divideBits_remainder_length divisor input
  constructor
  · simp only [List.length_cons]; omega
  · rw [subBits_length]
    simp only [List.length_cons]
    apply max_le <;> omega

theorem value_bits (n : ℕ) : value n.bits = n := by
  induction n using Nat.binaryRec' with
  | zero => simp [value]
  | bit b n h ih =>
    rw [Nat.bits_append_bit n b h]
    simp only [value, ih]
    cases b <;> simp [Nat.bit, Nat.add_comm]

/-- Sign-and-magnitude inputs are explicit bits; negative zero is permitted. -/
structure SignedBits where
  negative : Bool
  magnitude : List Bool
  deriving DecidableEq

def signedValue (x : SignedBits) : ℤ :=
  if x.negative then -(value x.magnitude : ℤ) else (value x.magnitude : ℤ)

theorem signedValue_natAbs (x : SignedBits) : (signedValue x).natAbs = value x.magnitude := by
  cases x with
  | mk negative magnitude => cases negative <;> simp [signedValue]

theorem signedValue_size (x : SignedBits) : (signedValue x).natAbs.size ≤ x.magnitude.length := by
  rw [signedValue_natAbs]
  exact value_size _

theorem subBits_value_int (xs ys : List Bool) (h : value ys ≤ value xs) :
    (value (subBits xs ys false).1 : ℤ) = (value xs : ℤ) - (value ys : ℤ) := by
  rw [subBits_value _ _ h, Nat.cast_sub h]

def signedAdd (x y : SignedBits) : SignedBits :=
  if x.negative = y.negative then
    ⟨x.negative, addBits x.magnitude y.magnitude false⟩
  else
    let trial := subBits x.magnitude y.magnitude false
    if trial.2 then ⟨y.negative, (subBits y.magnitude x.magnitude false).1⟩
    else ⟨x.negative, trial.1⟩

theorem signedAdd_correct (x y : SignedBits) :
    signedValue (signedAdd x y) = signedValue x + signedValue y := by
  cases hx : x.negative <;> cases hy : y.negative
  · simp [signedAdd, signedValue, hx, hy, addBits_correct]
  · simp only [signedAdd, hx, hy, Bool.false_eq_true, if_false]
    split_ifs with hb
    · have hlt := (subBits_borrow x.magnitude y.magnitude).mp hb
      have hv := subBits_value_int y.magnitude x.magnitude hlt.le
      simp [signedValue, hx, hy, hv]
      omega
    · have hge : value y.magnitude ≤ value x.magnitude := by
        by_contra hn
        exact hb ((subBits_borrow _ _).mpr (by omega))
      have hv := subBits_value_int x.magnitude y.magnitude hge
      simp [signedValue, hx, hy, hv]
      omega
  · simp only [signedAdd, hx, hy, Bool.true_eq_false, if_false]
    split_ifs with hb
    · have hlt := (subBits_borrow x.magnitude y.magnitude).mp hb
      have hv := subBits_value_int y.magnitude x.magnitude hlt.le
      simp [signedValue, hx, hy, hv]
      omega
    · have hge : value y.magnitude ≤ value x.magnitude := by
        by_contra hn
        exact hb ((subBits_borrow _ _).mpr (by omega))
      have hv := subBits_value_int x.magnitude y.magnitude hge
      simp [signedValue, hx, hy, hv]
      omega
  · simp [signedAdd, signedValue, hx, hy, addBits_correct]
    omega

/-- This is a ghost formula; executable counted evaluation is joint below. -/
def signedAddSteps (x y : SignedBits) : ℕ :=
  if x.negative = y.negative then columnSteps x.magnitude y.magnitude + 4
  else if (subBits x.magnitude y.magnitude false).2 then
    columnSteps x.magnitude y.magnitude + columnSteps y.magnitude x.magnitude + 8
  else columnSteps x.magnitude y.magnitude + 8

def signedAddCounted (x y : SignedBits) : SignedBits × ℕ :=
  if x.negative = y.negative then
    let sum := addCounted x.magnitude y.magnitude false
    (⟨x.negative, sum.1⟩, sum.2 + 4)
  else
    let trial := subCounted x.magnitude y.magnitude false
    if trial.1.2 then
      let reverse := subCounted y.magnitude x.magnitude false
      (⟨y.negative, reverse.1.1⟩, trial.2 + reverse.2 + 8)
    else (⟨x.negative, trial.1.1⟩, trial.2 + 8)

theorem signedAddCounted_projections (x y : SignedBits) :
    (signedAddCounted x y).1 = signedAdd x y ∧
      (signedAddCounted x y).2 = signedAddSteps x y := by
  have ha := addCounted_projections x.magnitude y.magnitude false
  have hs := subCounted_projections x.magnitude y.magnitude false
  have hr := subCounted_projections y.magnitude x.magnitude false
  simp only [signedAddCounted, signedAdd, signedAddSteps, ha.1, ha.2, hs.1, hs.2, hr.1, hr.2]
  split_ifs <;> exact ⟨rfl, rfl⟩

theorem signedAddSteps_bound (x y : SignedBits) :
    signedAddSteps x y ≤ 30 * (max x.magnitude.length y.magnitude.length + 1) := by
  unfold signedAddSteps
  split_ifs <;> rw [columnSteps_eq]
  · omega
  · rw [columnSteps_eq, max_comm y.magnitude.length x.magnitude.length]
    omega
  · omega

theorem signedAdd_length (x y : SignedBits) :
    (signedAdd x y).magnitude.length ≤ max x.magnitude.length y.magnitude.length + 1 := by
  by_cases hs : x.negative = y.negative
  · simp only [signedAdd, hs, if_true]
    exact addBits_length _ _ _
  · simp only [signedAdd, hs, if_false]
    split_ifs
    · change (subBits y.magnitude x.magnitude false).1.length ≤ _
      rw [subBits_length, max_comm y.magnitude.length x.magnitude.length]
      omega
    · change (subBits x.magnitude y.magnitude false).1.length ≤ _
      rw [subBits_length]
      omega

def signedNeg (x : SignedBits) : SignedBits := ⟨!x.negative, x.magnitude⟩
theorem signedNeg_correct (x : SignedBits) : signedValue (signedNeg x) = -signedValue x := by
  cases hx : x.negative <;> simp [signedNeg, signedValue, hx]

def signedMul (x y : SignedBits) : SignedBits :=
  ⟨Bool.xor x.negative y.negative, mulBits x.magnitude y.magnitude⟩

theorem signedMul_correct (x y : SignedBits) :
    signedValue (signedMul x y) = signedValue x * signedValue y := by
  cases hx : x.negative <;> cases hy : y.negative <;>
    simp [signedValue, signedMul, hx, hy, mulBits_correct]

def signedMulSteps (x y : SignedBits) : ℕ := mulSteps x.magnitude y.magnitude + 4
def signedMulCounted (x y : SignedBits) : SignedBits × ℕ :=
  let child := mulCounted x.magnitude y.magnitude
  (⟨Bool.xor x.negative y.negative, child.1⟩, child.2 + 4)

theorem signedMulCounted_projections (x y : SignedBits) :
    (signedMulCounted x y).1 = signedMul x y ∧
      (signedMulCounted x y).2 = signedMulSteps x y := by
  obtain ⟨hv, hc⟩ := mulCounted_projections x.magnitude y.magnitude
  simp [signedMulCounted, signedMul, signedMulSteps, hv, hc]

theorem signedMulSteps_bound (x y : SignedBits) :
    signedMulSteps x y ≤ 40 * (x.magnitude.length + 1) *
      (x.magnitude.length + y.magnitude.length + 2) + 4 := by
  exact Nat.add_le_add_right (mulSteps_bound _ _) 4

def signedDivide (divisor : List Bool) (x : SignedBits) : SignedBits :=
  ⟨x.negative, (divideBits divisor x.magnitude).1⟩
def signedDivideSteps (divisor : List Bool) (x : SignedBits) : ℕ :=
  divideSteps divisor x.magnitude + 4
def signedDivideCounted (divisor : List Bool) (x : SignedBits) : SignedBits × ℕ :=
  let child := divideCounted divisor x.magnitude
  (⟨x.negative, child.1.1⟩, child.2 + 4)

theorem signedDivideCounted_projections (divisor : List Bool) (x : SignedBits) :
    (signedDivideCounted divisor x).1 = signedDivide divisor x ∧
      (signedDivideCounted divisor x).2 = signedDivideSteps divisor x := by
  obtain ⟨hv, hc⟩ := divideCounted_projections divisor x.magnitude
  simp [signedDivideCounted, signedDivide, signedDivideSteps, hv, hc]

theorem signedDivide_exact (divisor : List Bool) (x : SignedBits) (w : ℤ)
    (hD : 0 < value divisor) (hz : signedValue x = (value divisor : ℤ) * w) :
    signedValue (signedDivide divisor x) = w := by
  have hn : value x.magnitude = value divisor * w.natAbs := by
    have h := congrArg Int.natAbs hz
    simpa only [signedValue_natAbs, Int.natAbs_mul, Int.natAbs_natCast] using h
  have hq : value (divideBits divisor x.magnitude).1 = w.natAbs := by
    rw [divideBits_quotient _ _ hD, hn]
    exact Nat.mul_div_cancel_left _ hD
  have hDi : (0 : ℤ) < value divisor := by exact_mod_cast hD
  cases hx : x.negative with
  | false =>
    have hx0 : 0 ≤ signedValue x := by simp [signedValue, hx]
    have hw : 0 ≤ w := by nlinarith
    simpa [signedValue, signedDivide, hx, hq] using Int.natAbs_of_nonneg hw
  | true =>
    have hx0 : signedValue x ≤ 0 := by simp [signedValue, hx]
    have hw : w ≤ 0 := by nlinarith
    simpa [signedValue, signedDivide, hx, hq] using (Int.eq_neg_natAbs_of_nonpos hw).symm

theorem signedDivideSteps_bound (divisor : List Bool) (x : SignedBits) :
    signedDivideSteps divisor x ≤ 20 * (x.magnitude.length + 1) *
      (x.magnitude.length + divisor.length + 1) + 4 :=
  Nat.add_le_add_right (divideSteps_bound _ _) 4

/-- Canonical representation wrappers are specifications of binary integer input/output. -/
def ofInt (z : ℤ) : SignedBits := ⟨decide (z < 0), z.natAbs.bits⟩

theorem ofInt_correct (z : ℤ) : signedValue (ofInt z) = z := by
  simp only [signedValue, ofInt, value_bits, decide_eq_true_eq]
  split_ifs with hz
  · exact (Int.eq_neg_natAbs_of_nonpos hz.le).symm
  · exact Int.natAbs_of_nonneg (by omega)

theorem ofInt_length (z : ℤ) : (ofInt z).magnitude.length = z.natAbs.size :=
  Nat.size_eq_bits_len _

def signedAddIntCounted (z w : ℤ) : ℤ × ℕ :=
  let result := signedAddCounted (ofInt z) (ofInt w)
  (signedValue result.1, result.2)

theorem signedAddIntCounted_correct (z w : ℤ) : (signedAddIntCounted z w).1 = z + w := by
  rw [signedAddIntCounted, (signedAddCounted_projections _ _).1, signedAdd_correct,
    ofInt_correct, ofInt_correct]

theorem signedAddIntCounted_bound (z w : ℤ) :
    (signedAddIntCounted z w).2 ≤ 30 * (max z.natAbs.size w.natAbs.size + 1) := by
  simpa only [signedAddIntCounted, (signedAddCounted_projections _ _).2, ofInt_length] using
    signedAddSteps_bound (ofInt z) (ofInt w)

theorem signedAddIntCounted_size (z w : ℤ) :
    (signedAddIntCounted z w).1.natAbs.size ≤ max z.natAbs.size w.natAbs.size + 1 := by
  rw [signedAddIntCounted, (signedAddCounted_projections _ _).1]
  refine (signedValue_size _).trans ?_
  simpa only [ofInt_length] using signedAdd_length (ofInt z) (ofInt w)

def signedNegIntCounted (z : ℤ) : ℤ × ℕ := (signedValue (signedNeg (ofInt z)), 1)

theorem signedNegIntCounted_correct (z : ℤ) : (signedNegIntCounted z).1 = -z := by
  simp [signedNegIntCounted, signedNeg_correct, ofInt_correct]

def signedSubIntCounted (z w : ℤ) : ℤ × ℕ :=
  let result := signedAddCounted (ofInt z) (signedNeg (ofInt w))
  (signedValue result.1, result.2 + 1)

theorem signedSubIntCounted_correct (z w : ℤ) : (signedSubIntCounted z w).1 = z - w := by
  rw [signedSubIntCounted, (signedAddCounted_projections _ _).1, signedAdd_correct,
    signedNeg_correct, ofInt_correct, ofInt_correct]
  rfl

theorem signedSubIntCounted_bound (z w : ℤ) :
    (signedSubIntCounted z w).2 ≤ 31 * (max z.natAbs.size w.natAbs.size + 1) := by
  have h := signedAddSteps_bound (ofInt z) (signedNeg (ofInt w))
  simp only [signedNeg, ofInt_length] at h
  simp only [signedSubIntCounted, (signedAddCounted_projections _ _).2, signedNeg]
  omega

def signedMulIntCounted (z w : ℤ) : ℤ × ℕ :=
  let result := signedMulCounted (ofInt z) (ofInt w)
  (signedValue result.1, result.2)

theorem signedMulIntCounted_correct (z w : ℤ) : (signedMulIntCounted z w).1 = z * w := by
  rw [signedMulIntCounted, (signedMulCounted_projections _ _).1, signedMul_correct,
    ofInt_correct, ofInt_correct]

theorem signedMulIntCounted_bound (z w : ℤ) :
    (signedMulIntCounted z w).2 ≤ 40 * (z.natAbs.size + 1) *
      (z.natAbs.size + w.natAbs.size + 2) + 4 := by
  simpa only [signedMulIntCounted, (signedMulCounted_projections _ _).2, ofInt_length] using
    signedMulSteps_bound (ofInt z) (ofInt w)

theorem signedMulIntCounted_size (z w : ℤ) :
    (signedMulIntCounted z w).1.natAbs.size ≤ 2 * z.natAbs.size + w.natAbs.size + 1 := by
  rw [signedMulIntCounted, (signedMulCounted_projections _ _).1]
  refine (signedValue_size _).trans ?_
  simpa only [signedMul, ofInt_length] using mulBits_length (ofInt z).magnitude (ofInt w).magnitude

def binaryExactDiv (D : ℕ) (z : ℤ) : ℤ :=
  signedValue (signedDivide D.bits (ofInt z))
def binaryExactDivCounted (D : ℕ) (z : ℤ) : ℤ × ℕ :=
  let result := signedDivideCounted D.bits (ofInt z)
  (signedValue result.1, result.2)

theorem binaryExactDiv_exact (D : ℕ) (z w : ℤ) (hD : 0 < D) (hz : z = (D : ℤ) * w) :
    binaryExactDiv D z = w := by
  apply signedDivide_exact
  · simpa only [value_bits] using hD
  · simpa only [ofInt_correct, value_bits] using hz

theorem binaryExactDivCounted_exact (D : ℕ) (z w : ℤ) (hD : 0 < D)
    (hz : z = (D : ℤ) * w) : (binaryExactDivCounted D z).1 = w := by
  simpa only [binaryExactDivCounted, (signedDivideCounted_projections _ _).1, binaryExactDiv] using
    binaryExactDiv_exact _ _ _ hD hz

theorem binaryExactDivCounted_bound (D : ℕ) (z : ℤ) :
    (binaryExactDivCounted D z).2 ≤ 20 * (z.natAbs.size + 1) *
      (z.natAbs.size + D.size + 1) + 4 := by
  simpa only [binaryExactDivCounted, (signedDivideCounted_projections _ _).2,
    ofInt_length, Nat.size_eq_bits_len] using
    signedDivideSteps_bound D.bits (ofInt z)

theorem fixedDenominator_bound (D L : ℕ) (z : ℤ) (hsize : z.natAbs.size ≤ L) :
    (binaryExactDivCounted D z).2 ≤ 20 * (L + 1) * (L + D.size + 1) + 4 := by
  have h := binaryExactDivCounted_bound D z
  nlinarith

theorem binaryExactDivCounted_size (D : ℕ) (z : ℤ) :
    (binaryExactDivCounted D z).1.natAbs.size ≤ z.natAbs.size := by
  rw [binaryExactDivCounted, (signedDivideCounted_projections _ _).1]
  exact (signedValue_size _).trans (by
    simp only [signedDivide, divideBits_quotient_length, ofInt_length]
    exact le_rfl)

end ThinMatrix.IntegerArithmetic

#print axioms ThinMatrix.IntegerArithmetic.addBits_correct
#print axioms ThinMatrix.IntegerArithmetic.subBits_invariant
#print axioms ThinMatrix.IntegerArithmetic.subBits_borrow
#print axioms ThinMatrix.IntegerArithmetic.subBits_value
#print axioms ThinMatrix.IntegerArithmetic.addCounted_projections
#print axioms ThinMatrix.IntegerArithmetic.subCounted_projections
#print axioms ThinMatrix.IntegerArithmetic.mulCounted_projections
#print axioms ThinMatrix.IntegerArithmetic.divideCounted_projections
#print axioms ThinMatrix.IntegerArithmetic.mulBits_correct
#print axioms ThinMatrix.IntegerArithmetic.mulSteps_bound
#print axioms ThinMatrix.IntegerArithmetic.divideBits_correct
#print axioms ThinMatrix.IntegerArithmetic.divideSteps_bound
#print axioms ThinMatrix.IntegerArithmetic.divide_step_width
#print axioms ThinMatrix.IntegerArithmetic.signedAddIntCounted_correct
#print axioms ThinMatrix.IntegerArithmetic.signedAddIntCounted_bound
#print axioms ThinMatrix.IntegerArithmetic.signedMulIntCounted_correct
#print axioms ThinMatrix.IntegerArithmetic.signedMulIntCounted_bound
#print axioms ThinMatrix.IntegerArithmetic.binaryExactDivCounted_exact
#print axioms ThinMatrix.IntegerArithmetic.binaryExactDivCounted_bound
#print axioms ThinMatrix.IntegerArithmetic.fixedDenominator_bound
#print axioms ThinMatrix.IntegerArithmetic.binaryExactDivCounted_size
#print axioms ThinMatrix.IntegerArithmetic.signedAddIntCounted_size
#print axioms ThinMatrix.IntegerArithmetic.signedMulIntCounted_size
#print axioms ThinMatrix.IntegerArithmetic.signedSubIntCounted_correct
#print axioms ThinMatrix.IntegerArithmetic.signedSubIntCounted_bound
