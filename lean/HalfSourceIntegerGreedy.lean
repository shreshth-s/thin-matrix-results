import HalfSourceIntegerScores

set_option autoImplicit false

/-!
# Retained integer implementation of the translation list

Precompute both power tables once. Each bit decision uses natural-number
scores over a common denominator. Character sums and selected translations
are materialized in arrays, so
reading state cannot recursively rerun previous selection decisions. Partial
signs retain the already computed Boolean decisions between bits. The
refinement theorem identifies the entire list, including order and repeats,
with the already proved rational list. A complete bit-work bound is separate.
-/
namespace ThinMatrix.HalfSourceIntegerGreedy
open ThinMatrix.WalshEmbedding ThinMatrix.HalfSourceGreedy ThinMatrix.HalfSourceList
open ThinMatrix.HalfSourceIntegerScores
open scoped BigOperators

abbrev Tables := Array ℕ × Array ℕ

def tables (m : ℕ) : Tables :=
  (Array.ofFn (fun i : Fin (2*K m+1) => A m^i.val),
   Array.ofFn (fun i : Fin (2*K m+1) => B m^i.val))

def power (m : ℕ) (ts : Tables) (t : ℤ) : ℕ :=
  ts.1[((K m:ℤ)+t).toNat]?.getD 0 * ts.2[((K m:ℤ)-t).toNat]?.getD 0

theorem power_eq (m : ℕ) (t : ℤ) (ht : -(K m:ℤ) ≤ t ∧ t ≤ K m) :
    power m (tables m) t = powerNumerator m t := by
  have hp : ((K m:ℤ)+t).toNat < 2*K m+1 := by omega
  have hn : ((K m:ℤ)-t).toNat < 2*K m+1 := by omega
  simp [power, tables, powerNumerator, hp, hn]

def resolved (m : ℕ) (ts : Tables) (s : ℤ) (b : Bool) : ℕ :=
  2*(power m ts (s+sign b)+power m ts (-(s+sign b)))

def unresolved (m : ℕ) (ts : Tables) (s : ℤ) : ℕ :=
  power m ts (s+1)+power m ts (s-1)+power m ts (-s+1)+power m ts (-s-1)

theorem resolved_eq (m : ℕ) (s : ℤ) (hs : |s| ≤ 64*m^3) (b : Bool) :
    resolved m (tables m) s b = HalfSourceIntegerScores.resolved m s b := by
  have hs' := abs_le.mp hs
  have hb : sign b = 1 ∨ sign b = -1 := by cases b <;> simp [sign]
  have ht : -(K m:ℤ) ≤ s+sign b ∧ s+sign b ≤ K m := by
    simp only [K, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow, Nat.cast_one]
    rcases hb with hb | hb <;> omega
  have ht' : -(K m:ℤ) ≤ -(s+sign b) ∧ -(s+sign b) ≤ K m := by omega
  simp only [resolved, HalfSourceIntegerScores.resolved, power_eq m _ ht, power_eq m _ ht']

theorem unresolved_eq (m : ℕ) (s : ℤ) (hs : |s| ≤ 64*m^3) :
    unresolved m (tables m) s = HalfSourceIntegerScores.unresolved m s := by
  have hs' := abs_le.mp hs
  have hwin (t : ℤ) (h : t = s+1 ∨ t = s-1 ∨ t = -s+1 ∨ t = -s-1) :
      -(K m:ℤ) ≤ t ∧ t ≤ K m := by
    simp only [K, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow, Nat.cast_one]
    rcases h with h | h | h | h <;> omega
  simp only [unresolved, HalfSourceIntegerScores.unresolved,
    power_eq m _ (hwin _ (Or.inl rfl)), power_eq m _ (hwin _ (Or.inr (Or.inl rfl))),
    power_eq m _ (hwin _ (Or.inr (Or.inr (Or.inl rfl)))),
    power_eq m _ (hwin _ (Or.inr (Or.inr (Or.inr rfl))))]

variable {C : Type*} [Fintype C]

def score {n : ℕ} (m : ℕ) (ts : Tables) (sums : C → ℤ)
    (rows : C → Cube n) (signs : C → Bool) : ℕ :=
  ∑ a, if rows a = zeroBits n then resolved m ts (sums a) (signs a) else unresolved m ts (sums a)

theorem score_eq {n : ℕ} (m : ℕ) (sums : C → ℤ) (hs : ∀ a, |sums a| ≤ 64*m^3)
    (rows : C → Cube n) (signs : C → Bool) :
    score m (tables m) sums rows signs = HalfSourceIntegerScores.score m sums rows signs := by
  unfold score HalfSourceIntegerScores.score
  apply Finset.sum_congr rfl
  intro a _
  split_ifs
  · exact resolved_eq m _ (hs a) _
  · exact unresolved_eq m _ (hs a)

def chosen {n : ℕ} (m : ℕ) (ts : Tables) (sums : C → ℤ)
    (rows : C → Cube (n+1)) (signs : C → Bool) : Bool :=
  let left := score m ts sums (tails rows) (updateSigns rows signs false)
  let right := score m ts sums (tails rows) (updateSigns rows signs true)
  decide (right < left)

theorem chosen_eq {n : ℕ} (m : ℕ) (hm : 0 < m) (sums : C → ℤ)
    (hs : ∀ a, |sums a| ≤ 64*m^3) (rows : C → Cube (n+1)) (signs : C → Bool) :
    chosen m (tables m) sums rows signs = chosenBit (rationalBase m)
      (fun a => rationalBase m^sums a) (fun a => rationalBase m^(-sums a)) rows signs := by
  simp only [chosen, score_eq m sums hs]
  exact HalfSourceIntegerScores.chosen_eq m hm sums hs rows signs

def vectorBits {n : ℕ} (v : Vector Bool n) : Cube n := fun i => v[i.val]

@[simp] theorem vectorBits_ofFn {n : ℕ} (f : Cube n) :
    vectorBits (Vector.ofFn f) = f := by
  funext i
  simp [vectorBits]

/-- Return a stored vector, so evaluating a selected bit cannot rerun earlier
conditional decisions through a partially applied function. -/
def select (m : ℕ) (ts : Tables) (sums : C → ℤ) :
    (n : ℕ) → (C → Cube n) → (C → Bool) → Vector Bool n
  | 0, _, _ => Vector.ofFn (fun i => Fin.elim0 i)
  | n+1, rows, signs =>
      let b := chosen m ts sums rows signs
      let rest := select m ts sums n (tails rows) (updateSigns rows signs b)
      Vector.ofFn (Fin.cons b (vectorBits rest))

theorem select_eq (m : ℕ) (hm : 0 < m) (sums : C → ℤ)
    (hs : ∀ a, |sums a| ≤ 64*m^3) (n : ℕ) (rows : C → Cube n) (signs : C → Bool) :
    vectorBits (select m (tables m) sums n rows signs) = HalfSourceGreedy.select (rationalBase m)
      (fun a => rationalBase m^sums a) (fun a => rationalBase m^(-sums a)) n rows signs := by
  induction n generalizing signs with
  | zero => exact Subsingleton.elim _ _
  | succ n ih =>
    simp only [select, vectorBits_ofFn, HalfSourceGreedy.select, chosen_eq m hm sums hs, ih]

/-- A computable binary enumeration, independent of classical finite choices. -/
def cubeIndex (m : ℕ) : Cube m ≃ Fin (2^m) :=
  (Equiv.arrowCongr (Equiv.refl (Fin m)) finTwoEquiv.symm).trans finFunctionFinEquiv

def storeSums (m : ℕ) (f : Characters m → ℤ) : Vector ℤ (2^m) :=
  Vector.ofFn (fun i => let a := (cubeIndex m).symm i
    if ha : a ≠ zeroBits m then f ⟨a,ha⟩ else 0)

def lookupSums {m : ℕ} (v : Vector ℤ (2^m)) (a : Characters m) : ℤ :=
  v[(cubeIndex m a.val).val]

@[simp] theorem lookup_storeSums (m : ℕ) (f : Characters m → ℤ) (a : Characters m) :
    lookupSums (storeSums m f) a = f a := by
  simp [lookupSums, storeSums, a.property]

structure State (m : ℕ) where
  entries : List (Cube m)
  storedSums : Vector ℤ (2^m)

def State.sums {m : ℕ} (state : State m) : Characters m → ℤ := lookupSums state.storedSums

@[simp] theorem sums_mk {m : ℕ} (entries : List (Cube m)) (f : Characters m → ℤ) :
    (State.mk entries (storeSums m f)).sums = f := by
  funext a
  exact lookup_storeSums m f a

def build (m : ℕ) (ts : Tables) : ℕ → State m
  | 0 => ⟨[], storeSums m (fun _ => 0)⟩
  | j+1 =>
      let prev := build m ts j
      let selected := select m ts prev.sums m (fun a => a.val) (fun _ => false)
      let d := vectorBits selected
      ⟨d :: prev.entries, storeSums m (fun a => prev.sums a+sign (dotBits a.val d))⟩

theorem build_length (m : ℕ) (ts : Tables) (j : ℕ) : (build m ts j).entries.length = j := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [build, List.length_cons, ih]

theorem build_sums (m : ℕ) (ts : Tables) (j : ℕ) (a : Characters m) :
    (build m ts j).sums a = sumSign (build m ts j).entries a.val := by
  induction j with
  | zero => simp [build, sumSign]
  | succ j ih => simp only [build, sums_mk, sumSign_cons, ih]

theorem sumSign_abs_le_length {m : ℕ} (ds : List (Cube m)) (a : Cube m) :
    |sumSign ds a| ≤ ds.length := by
  induction ds with
  | nil => simp [sumSign]
  | cons d ds ih =>
    rw [sumSign_cons]
    have hb : |sign (dotBits a d)| = 1 := by cases dotBits a d <;> norm_num [sign]
    have h := (abs_add_le (sumSign ds a) (sign (dotBits a d))).trans (add_le_add ih (le_of_eq hb))
    simpa using h

theorem build_eq (m : ℕ) (hm : 0 < m) (j : ℕ) (hj : j ≤ 64*m^3) :
    (build m (tables m) j).entries = HalfSourceList.build m (rationalBase m) j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have hj' : j ≤ 64*m^3 := by omega
    have hs (a : Characters m) : |(build m (tables m) j).sums a| ≤ 64*m^3 := by
      rw [build_sums]
      have hb := sumSign_abs_le_length (build m (tables m) j).entries a.val
      rw [build_length] at hb
      exact hb.trans (by exact_mod_cast hj')
    rw [build, HalfSourceList.build]
    dsimp only
    rw [select_eq m hm _ hs]
    have sums_eq : (build m (tables m) j).sums =
        fun a => sumSign (HalfSourceList.build m (rationalBase m) j) a.val := by
      funext a
      rw [build_sums, ih hj']
    rw [sums_eq, ih hj']
    rfl

/-- Both power arrays are materialized once outside the retained list loop. -/
def translations (m : ℕ) : List (Cube m) :=
  let ts := tables m
  (build m ts (64*m^3)).entries

theorem translations_eq (m : ℕ) (hm : 0 < m) :
    translations m = HalfSourceList.translations m := build_eq m hm _ le_rfl

#print axioms power_eq
#print axioms resolved_eq
#print axioms unresolved_eq
#print axioms score_eq
#print axioms chosen_eq
#print axioms vectorBits_ofFn
#print axioms select_eq
#print axioms lookup_storeSums
#print axioms sums_mk
#print axioms build_length
#print axioms build_sums
#print axioms sumSign_abs_le_length
#print axioms build_eq
#print axioms translations_eq
end ThinMatrix.HalfSourceIntegerGreedy
