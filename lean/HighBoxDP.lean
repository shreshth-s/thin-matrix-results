import CacheBounds
import CacheCardinality
import TensorContraction
import HighBoxEntropy

/-!
# Finite balanced high-box dynamic program

This module uses actual six-letter words: four ordinary labels, the private
label four, and the star label five. A box is the sum of arbitrary five-label
leaf values compatible with its fixed positions. Thus the proofs apply to
entangled source arrays, and do not assume a product of local scalar inputs.

The physical order has all stars before all private positions. Its balanced
caps are enforced on the words themselves. Replacing the last star by any
of the five leaf labels stays in the state language and strictly decreases
the number of stars. The finite cardinality bound collapses stars to private
letters and records their cut; it does not posit an entropy bound.
-/

namespace ThinMatrix.HighBoxDP

attribute [local instance] Classical.propDecidable

open scoped BigOperators
open Finset
open ThinMatrix.CacheBounds (Label Word)

abbrev LeafWord (n : ℕ) := Fin n → Fin 5

/-- Fixed ordinary/private positions agree; a star permits all five labels. -/
def Compatible {n : ℕ} (w : Word n) (v : LeafWord n) : Prop :=
  ∀ i, (w i).val < 5 → (v i).val = (w i).val

/-- Set one physical position to an ordinary or private leaf label. -/
def replace {n : ℕ} (w : Word n) (i : Fin n) (a : Fin 5) : Word n :=
  Function.update w i ⟨a.val, by omega⟩

@[simp] theorem replace_same {n : ℕ} (w : Word n) (i : Fin n) (a : Fin 5) :
    replace w i a i = ⟨a.val, by omega⟩ := by simp [replace]

@[simp] theorem replace_other {n : ℕ} (w : Word n) (i j : Fin n) (a : Fin 5)
    (h : j ≠ i) : replace w i a j = w j := by simp [replace, h]

theorem compatible_replace_iff {n : ℕ} (w : Word n) (v : LeafWord n)
    (i : Fin n) (a : Fin 5) (hs : (w i).val = 5) :
    Compatible (replace w i a) v ↔ Compatible w v ∧ v i = a := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro j hj
      have hji : j ≠ i := by intro he; subst j; omega
      simpa [replace, hji] using h j (by simpa [replace, hji] using hj)
    · apply Fin.ext
      simpa [replace] using h i (by simp [replace])
  · rintro ⟨h, ha⟩ j hj
    by_cases hji : j = i
    · subst j; simp [replace, ha]
    · simpa [replace, hji] using h j (by simpa [replace, hji] using hj)

/-- The exact finite box value, for arbitrary already-contracted leaf values. -/
noncomputable def boxValue {n : ℕ} {R : Type*} [AddCommMonoid R]
    (w : Word n) (leaf : LeafWord n → R) : R := by
  classical
  exact ∑ v, if Compatible w v then leaf v else 0

/-- The actual five-child recurrence at any star. -/
theorem boxValue_expand {n : ℕ} {R : Type*} [AddCommMonoid R]
    (w : Word n) (leaf : LeafWord n → R) (i : Fin n) (hs : (w i).val = 5) :
    boxValue w leaf = ∑ a : Fin 5, boxValue (replace w i a) leaf := by
  classical
  unfold boxValue
  calc
    _ = ∑ v : LeafWord n, ∑ a : Fin 5,
        if Compatible (replace w i a) v then leaf v else 0 := by
      apply Finset.sum_congr rfl
      intro v hv
      simp_rw [compatible_replace_iff w v i _ hs]
      by_cases h : Compatible w v <;> simp [h]
    _ = _ := Finset.sum_comm

/-- Number of private-or-star letters in the requested physical region. -/
noncomputable def specialCount {n : ℕ} (w : Word n) (region : Fin n → Prop) : ℕ := by
  classical
  exact (Finset.univ.filter (fun i => region i ∧ 4 ≤ (w i).val)).card

/-- Genuine balanced caps, including the total cap used by high boxes. -/
def Balanced (L m t : ℕ) (w : Word (2*L)) : Prop :=
  specialCount w (fun i => i.val < L) ≤ m ∧
  specialCount w (fun i => L ≤ i.val) ≤ m ∧
  specialCount w (fun _ => True) ≤ 2*m-t

/-- Physical order: every star is before every private position. -/
def Ordered {n : ℕ} (w : Word n) : Prop :=
  ∀ i j, (w i).val = 5 → (w j).val = 4 → i.val < j.val

abbrev States (L m t : ℕ) :=
  {w : Word (2*L) // Balanced L m t w ∧ Ordered w}

abbrev BaseStates (L m t : ℕ) :=
  {w : Word (2*L) // Balanced L m t w ∧ ∀ i, (w i).val ≠ 5}

noncomputable instance statesFintype (L m t : ℕ) : Fintype (States L m t) :=
  Fintype.ofFinite _
noncomputable instance baseStatesFintype (L m t : ℕ) : Fintype (BaseStates L m t) :=
  Fintype.ofFinite _

/-- Replacing a star cannot create any new private-or-star support. -/
theorem specialCount_replace_le {n : ℕ} (w : Word n) (i : Fin n) (a : Fin 5)
    (hs : (w i).val = 5) (region : Fin n → Prop) :
    specialCount (replace w i a) region ≤ specialCount w region := by
  classical
  apply Finset.card_le_card
  intro j hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
  refine ⟨hj.1, ?_⟩
  by_cases he : j = i
  · subst j; omega
  · simpa [replace, he] using hj.2

theorem balanced_replace {L m t : ℕ} (w : Word (2*L)) (h : Balanced L m t w)
    (i : Fin (2*L)) (a : Fin 5) (hs : (w i).val = 5) :
    Balanced L m t (replace w i a) := by
  exact ⟨(specialCount_replace_le w i a hs _).trans h.1,
    (specialCount_replace_le w i a hs _).trans h.2.1,
    (specialCount_replace_le w i a hs _).trans h.2.2⟩

/-- An actual last star in physical order. -/
def IsLastStar {n : ℕ} (w : Word n) (i : Fin n) : Prop :=
  (w i).val = 5 ∧ ∀ j, (w j).val = 5 → j.val ≤ i.val

theorem ordered_replace_last {n : ℕ} (w : Word n) (h : Ordered w)
    (i : Fin n) (hlast : IsLastStar w i) (a : Fin 5) :
    Ordered (replace w i a) := by
  intro j k hj hk
  have hji : j ≠ i := by intro he; subst j; simp [replace] at hj; omega
  have hjs : (w j).val = 5 := by simpa [replace, hji] using hj
  by_cases hki : k = i
  · subst k
    have hle := hlast.2 j hjs
    have hne : j.val ≠ i.val := by intro he; exact hji (Fin.ext he)
    omega
  · exact h j k hjs (by simpa [replace, hki] using hk)

/-- The recurrence's five children are all genuine retained high states. -/
def child {L m t : ℕ} (w : States L m t) (i : Fin (2*L))
    (h : IsLastStar w.val i) (a : Fin 5) : States L m t :=
  ⟨replace w.val i a, balanced_replace _ w.property.1 i a h.1,
    ordered_replace_last _ w.property.2 i h a⟩

noncomputable def starPositions {n : ℕ} (w : Word n) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun i => (w i).val = 5)

noncomputable def starCount {n : ℕ} (w : Word n) : ℕ := (starPositions w).card

@[simp] theorem mem_starPositions {n : ℕ} (w : Word n) (i : Fin n) :
    i ∈ starPositions w ↔ (w i).val = 5 := by
  classical
  simp [starPositions]

theorem starPositions_replace {n : ℕ} (w : Word n) (i : Fin n) (a : Fin 5) :
    starPositions (replace w i a) = (starPositions w).erase i := by
  classical
  ext j
  by_cases he : j = i
  · subst j; simp [replace, starPositions]; omega
  · simp [starPositions, replace, he]

theorem starCount_replace_lt {n : ℕ} (w : Word n) (i : Fin n) (a : Fin 5)
    (hs : (w i).val = 5) : starCount (replace w i a) < starCount w := by
  classical
  unfold starCount
  rw [starPositions_replace]
  exact Finset.card_erase_lt_of_mem (by simpa using hs)

theorem exists_lastStar {n : ℕ} (w : Word n) (h : 0 < starCount w) :
    ∃ i, IsLastStar w i := by
  classical
  have hn : (starPositions w).Nonempty := Finset.card_pos.mp h
  let i := (starPositions w).max' hn
  refine ⟨i, ?_, ?_⟩
  · exact (mem_starPositions w i).mp (Finset.max'_mem _ hn)
  · intro j hj
    exact Fin.le_iff_val_le_val.mp
      (Finset.le_max' _ _ ((mem_starPositions w j).mpr hj))

/-- A star-free box is exactly one actual leaf, with no residual summation. -/
def baseLeaf {n : ℕ} (w : Word n) (h : ∀ i, (w i).val ≠ 5) : LeafWord n :=
  fun i => ⟨(w i).val, by have := (w i).isLt; have := h i; omega⟩

theorem boxValue_base {n : ℕ} {R : Type*} [AddCommMonoid R]
    (w : Word n) (h : ∀ i, (w i).val ≠ 5) (leaf : LeafWord n → R) :
    boxValue w leaf = leaf (baseLeaf w h) := by
  classical
  have hc (v : LeafWord n) : Compatible w v ↔ v = baseLeaf w h := by
    constructor
    · intro hv; funext i; apply Fin.ext
      exact hv i (by have := (w i).isLt; have := h i; omega)
    · intro hv; subst v; intro i hi; rfl
  simp [boxValue, hc]

/-- Erase the star/private distinction, retaining all four ordinary labels. -/
def collapse {n : ℕ} (w : Word n) : Word n :=
  fun i => if (w i).val = 5 then 4 else w i

@[simp] theorem collapse_not_star {n : ℕ} (w : Word n) (i : Fin n) :
    (collapse w i).val ≠ 5 := by
  simp only [collapse]
  split <;> simp_all

@[simp] theorem collapse_special {n : ℕ} (w : Word n) (i : Fin n) :
    4 ≤ (collapse w i).val ↔ 4 ≤ (w i).val := by
  simp only [collapse]
  split <;> simp_all

@[simp] theorem specialCount_collapse {n : ℕ} (w : Word n) (region : Fin n → Prop) :
    specialCount (collapse w) region = specialCount w region := by
  classical
  simp only [specialCount, collapse_special]

theorem balanced_collapse {L m t : ℕ} (w : Word (2*L)) (h : Balanced L m t w) :
    Balanced L m t (collapse w) := by simpa only [Balanced, specialCount_collapse] using h

/-- A physical cut immediately after the last star, or zero if no star exists. -/
noncomputable def starCut {n : ℕ} (w : Word n) : ℕ :=
  (starPositions w).sup (fun i => i.val+1)

theorem starCut_le {n : ℕ} (w : Word n) : starCut w ≤ n := by
  classical
  apply Finset.sup_le
  intro i hi
  have := i.isLt
  omega

theorem star_before_cut {n : ℕ} (w : Word n) (i : Fin n) (h : (w i).val = 5) :
    i.val < starCut w := by
  classical
  have := Finset.le_sup (f := fun j : Fin n => j.val+1)
    ((mem_starPositions w i).mpr h)
  unfold starCut
  omega

theorem cut_before_private {n : ℕ} (w : Word n) (ho : Ordered w)
    (i : Fin n) (h : (w i).val = 4) : starCut w ≤ i.val := by
  classical
  apply Finset.sup_le
  intro j hj
  have := ho j i ((mem_starPositions w j).mp hj) h
  omega

/-- The collapsed word and cut recover every actual star position. -/
theorem star_iff_collapsed_cut {n : ℕ} (w : Word n) (ho : Ordered w) (i : Fin n) :
    (w i).val = 5 ↔ (collapse w i).val = 4 ∧ i.val < starCut w := by
  constructor
  · intro h
    exact ⟨by simp [collapse, h], star_before_cut w i h⟩
  · rintro ⟨hc, hi⟩
    by_contra hn
    have hp : (w i).val = 4 := by simpa [collapse, hn] using hc
    have := cut_before_private w ho i hp
    omega

/-- Genuine high states inject into balanced private bases and a physical cut.
This accounts for the ordering restriction without allocating `6^(2L)` states. -/
noncomputable def stateCode {L m t : ℕ} (w : States L m t) :
    BaseStates L m t × Fin (2*L+1) :=
  (⟨collapse w.val, balanced_collapse _ w.property.1, collapse_not_star _⟩,
    ⟨starCut w.val, by have := starCut_le w.val; omega⟩)

theorem stateCode_injective (L m t : ℕ) :
    Function.Injective (@stateCode L m t) := by
  intro w v he
  have hw : collapse w.val = collapse v.val := congrArg (fun p => p.1.val) he
  have hc : starCut w.val = starCut v.val := congrArg (fun p => p.2.val) he
  apply Subtype.ext
  funext i
  have hs : (w.val i).val = 5 ↔ (v.val i).val = 5 := by
    rw [star_iff_collapsed_cut _ w.property.2,
      star_iff_collapsed_cut _ v.property.2, hw, hc]
  have hi := congrArg (fun u : Word (2*L) => (u i).val) hw
  apply Fin.ext
  by_cases hws : (w.val i).val = 5
  · exact hws.trans (hs.mp hws).symm
  · have hvs : (v.val i).val ≠ 5 := fun hv => hws (hs.mpr hv)
    simpa [collapse, hws, hvs] using hi

/-- Full finite state bound in the original `2L` physical geometry. -/
theorem stateCount_le_baseCount (L m t : ℕ) :
    Fintype.card (States L m t) ≤ (2*L+1) * Fintype.card (BaseStates L m t) := by
  have h := Fintype.card_le_of_injective (@stateCode L m t) (stateCode_injective L m t)
  simpa only [Fintype.card_prod, Fintype.card_fin, Nat.mul_comm] using h

/-- Uniform scalar work charged per stored state: one product and one write
at a leaf; five accumulator additions and one write at a nonleaf. -/
noncomputable def stateWork {L m t : ℕ} (w : States L m t) : ℕ :=
  if starCount w.val = 0 then 2 else 6

noncomputable def preprocessingWork (L m t : ℕ) : ℕ :=
  ∑ w : States L m t, stateWork w

theorem preprocessingWork_le_six_states (L m t : ℕ) :
    preprocessingWork L m t ≤ 6 * Fintype.card (States L m t) := by
  classical
  calc
    _ ≤ ∑ _w : States L m t, 6 := by
      apply Finset.sum_le_sum
      intro w hw
      unfold stateWork
      split <;> omega
    _ = _ := by simp [Nat.mul_comm]

theorem preprocessingWork_le_balanced_bases (L m t : ℕ) :
    preprocessingWork L m t ≤ 6 * (2*L+1) * Fintype.card (BaseStates L m t) := by
  calc
    _ ≤ 6 * Fintype.card (States L m t) := preprocessingWork_le_six_states _ _ _
    _ ≤ _ := by
      simpa only [Nat.mul_assoc] using
        Nat.mul_le_mul_left 6 (stateCount_le_baseCount L m t)

/-- Every coordinate contributes at most one star. -/
theorem starCount_le_length {n : ℕ} (w : Word n) : starCount w ≤ n := by
  classical
  have h := Finset.card_le_card (Finset.filter_subset (fun i => (w i).val = 5)
    (Finset.univ : Finset (Fin n)))
  simpa [starCount, starPositions] using h

theorem noStars_of_count_zero {n : ℕ} (w : Word n) (h : starCount w = 0) :
    ∀ i, (w i).val ≠ 5 := by
  classical
  have he : starPositions w = ∅ := Finset.card_eq_zero.mp h
  intro i hi
  have hm := (mem_starPositions w i).mpr hi
  simp [he] at hm

/-- Choose the last physical star, whose existence is already proved. -/
noncomputable def lastStar {n : ℕ} (w : Word n) (h : starCount w ≠ 0) : Fin n :=
  Classical.choose (exists_lastStar w (Nat.pos_of_ne_zero h))

theorem lastStar_spec {n : ℕ} (w : Word n) (h : starCount w ≠ 0) :
    IsLastStar w (lastStar w h) :=
  Classical.choose_spec (exists_lastStar w (Nat.pos_of_ne_zero h))

/-- One real table update: either form the private-leaf product supplied by
`leaf`, or read the five already-stored children and add them. -/
noncomputable def nodeValue {L m t : ℕ} {R : Type*} [AddCommMonoid R]
    (leaf : LeafWord (2*L) → R) (table : States L m t → R)
    (w : States L m t) : R :=
  if h : starCount w.val = 0 then
    leaf (baseLeaf w.val (noStars_of_count_zero w.val h))
  else ∑ a : Fin 5, table (child w (lastStar w.val h) (lastStar_spec w.val h) a)

/-- The node update reads only children of strictly smaller star count. -/
theorem nodeValue_correct {L m t : ℕ} {R : Type*} [AddCommMonoid R]
    (leaf : LeafWord (2*L) → R) (table : States L m t → R) (w : States L m t)
    (hprev : ∀ v, starCount v.val < starCount w.val →
      table v = boxValue v.val leaf) :
    nodeValue leaf table w = boxValue w.val leaf := by
  classical
  unfold nodeValue
  split_ifs with h
  · exact (boxValue_base w.val (noStars_of_count_zero w.val h) leaf).symm
  · rw [boxValue_expand w.val leaf (lastStar w.val h) (lastStar_spec w.val h).1]
    apply Finset.sum_congr rfl
    intro a ha
    apply hprev
    exact starCount_replace_lt w.val (lastStar w.val h) a (lastStar_spec w.val h).1

/-- Write precisely one star-count layer; all other addresses are unchanged. -/
noncomputable def updateLayer {L m t : ℕ} {R : Type*} [AddCommMonoid R]
    (leaf : LeafWord (2*L) → R) (k : ℕ) (table : States L m t → R) :
    States L m t → R :=
  fun w => if starCount w.val = k then nodeValue leaf table w else table w

@[simp] theorem updateLayer_unchanged {L m t : ℕ} {R : Type*} [AddCommMonoid R]
    (leaf : LeafWord (2*L) → R) (k : ℕ) (table : States L m t → R)
    (w : States L m t) (h : starCount w.val ≠ k) :
    updateLayer leaf k table w = table w := by simp [updateLayer, h]

/-- Bottom-up stored tables. The zero initial function is a logical default;
no node reads a default value, as the correctness invariant below proves. -/
noncomputable def tableAfter {L m t : ℕ} {R : Type*} [AddCommMonoid R]
    (leaf : LeafWord (2*L) → R) : ℕ → States L m t → R
  | 0 => fun _ => 0
  | k+1 => updateLayer leaf k (tableAfter leaf k)

/-- After layer `k-1`, every address of height below `k` stores its exact box. -/
theorem tableAfter_correct_below {L m t : ℕ} {R : Type*} [AddCommMonoid R]
    (leaf : LeafWord (2*L) → R) (k : ℕ) :
    ∀ w : States L m t, starCount w.val < k →
      tableAfter leaf k w = boxValue w.val leaf := by
  induction k with
  | zero => intro w hw; omega
  | succ k ih =>
    intro w hw
    simp only [tableAfter, updateLayer]
    split_ifs with he
    · apply nodeValue_correct
      intro v hv
      apply ih
      omega
    · exact ih w (by omega)

/-- The finite stored DP computes every capped, ordered box correctly. -/
theorem tableAfter_complete {L m t : ℕ} {R : Type*} [AddCommMonoid R]
    (leaf : LeafWord (2*L) → R) (w : States L m t) :
    tableAfter leaf (2*L+1) w = boxValue w.val leaf := by
  apply tableAfter_correct_below
  have := starCount_le_length w.val
  omega

/-- Actual ring operations plus writes of the bottom-up schedule. Each
address belongs to its single genuine star-count layer. -/
noncomputable def scheduledWork (L m t : ℕ) : ℕ :=
  ∑ k : Fin (2*L+1), ∑ w : States L m t,
    if starCount w.val = k.val then stateWork w else 0

theorem scheduledWork_eq (L m t : ℕ) :
    scheduledWork L m t = preprocessingWork L m t := by
  classical
  unfold scheduledWork preprocessingWork
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w hw
  let k : Fin (2*L+1) := ⟨starCount w.val, by have := starCount_le_length w.val; omega⟩
  rw [Finset.sum_eq_single k]
  · simp [k]
  · intro j hj hjk
    have hn : starCount w.val ≠ j.val := by
      intro he
      exact hjk (Fin.ext he.symm)
    simp [hn]
  · simp

theorem scheduledWork_le_six_states (L m t : ℕ) :
    scheduledWork L m t ≤ 6 * Fintype.card (States L m t) := by
  rw [scheduledWork_eq]
  exact preprocessingWork_le_six_states L m t

/-- Table reads are charged separately: two cache operands at a base product,
five child values at a nonleaf. Ring work and reads together are at most
 eleven per state in the conservative zero-initialized-sum convention. -/
noncomputable def stateReads {L m t : ℕ} (w : States L m t) : ℕ :=
  if starCount w.val = 0 then 2 else 5

noncomputable def preprocessingReads (L m t : ℕ) : ℕ :=
  ∑ w : States L m t, stateReads w

theorem preprocessing_with_reads_le (L m t : ℕ) :
    preprocessingWork L m t + preprocessingReads L m t ≤
      11 * Fintype.card (States L m t) := by
  classical
  unfold preprocessingWork preprocessingReads
  rw [← Finset.sum_add_distrib]
  calc
    _ ≤ ∑ _w : States L m t, 11 := by
      apply Finset.sum_le_sum
      intro w hw
      unfold stateWork stateReads
      split <;> simp_all
    _ = _ := by simp [Nat.mul_comm]

/-- The support counts are the same genuine counts used by the cache. -/
theorem specialCount_eq_countPositions {n : ℕ} (w : Word n) (region : Fin n → Prop) :
    specialCount w region = CacheBounds.countPositions w
      (fun i a => region i ∧ CacheBounds.distinguished a) := by
  classical
  simp [specialCount, CacheBounds.countPositions, CacheBounds.distinguished]

/-- Balanced private bases are exactly the actual zero-channel cache words
with the additional total support cap. -/
noncomputable def baseStatesEquivTotalCapped (L m t : ℕ) :
    BaseStates L m t ≃ CacheCardinality.TotalCappedLeaves L m (2*m-t) where
  toFun w := ⟨⟨w.val, by simpa only [← specialCount_eq_countPositions] using w.property.1.1,
    by simpa only [← specialCount_eq_countPositions] using w.property.1.2.1, by
    have hz := (CacheCardinality.no_channels_iff w.val).mpr w.property.2
    omega⟩, by
      simpa [specialCount, CacheBounds.countPositions, CacheBounds.distinguished]
        using w.property.1.2.2⟩
  invFun w := ⟨w.val.val, ⟨by simpa only [specialCount_eq_countPositions] using w.val.property.1,
    by simpa only [specialCount_eq_countPositions] using w.val.property.2.1, by
      simpa [specialCount, CacheBounds.countPositions, CacheBounds.distinguished]
        using w.property⟩,
    (CacheCardinality.no_channels_iff w.val.val).mp (by
      have h := w.val.property.2.2
      omega)⟩
  left_inv w := Subtype.ext rfl
  right_inv w := Subtype.ext (Subtype.ext rfl)

/-- Exact balanced private-base cardinality in the original full grid. -/
theorem baseStates_card (L m t : ℕ) :
    Fintype.card (BaseStates L m t) =
      ∑ j ∈ Finset.range (m+1), ∑ k ∈ Finset.range (m+1),
        if j+k ≤ 2*m-t then L.choose j * L.choose k * 4^(2*L-j-k) else 0 := by
  rw [Fintype.card_congr (baseStatesEquivTotalCapped L m t)]
  exact CacheCardinality.totalCappedLeaves_card L m (2*m-t)

/-- Fully finite actual high-state bound, including the balanced support cap. -/
theorem stateCount_le_balanced_sum (L m t : ℕ) :
    Fintype.card (States L m t) ≤ (2*L+1) *
      (∑ j ∈ Finset.range (m+1), ∑ k ∈ Finset.range (m+1),
        if j+k ≤ 2*m-t then L.choose j * L.choose k * 4^(2*L-j-k) else 0) := by
  simpa only [baseStates_card] using stateCount_le_baseCount L m t

/-- Every completed DP base is present in the actual polynomial cache;
its private factor is obtained from the constant auxiliary coefficient. -/
def baseCacheWord {L m t : ℕ} (w : States L m t) (h : starCount w.val = 0) :
    CacheBounds.Leaves L m t :=
  ⟨w.val, by simpa only [← specialCount_eq_countPositions] using w.property.1.1,
    by simpa only [← specialCount_eq_countPositions] using w.property.1.2.1, by
    have hz := (CacheCardinality.no_channels_iff w.val).mpr
      (noStars_of_count_zero w.val h)
    omega⟩

/-- Two global transformed-source arrays provide the actual base product. -/
def productLeaf {n : ℕ} {R : Type*} [Mul R]
    (left right : LeafWord n → R) (v : LeafWord n) : R := left v * right v

/-- The stored DP is correct when bases are products of two arbitrary global
source transforms. No coordinate independence of those transforms is used. -/
theorem tableAfter_products_complete {L m t : ℕ} {R : Type*} [Semiring R]
    (left right : LeafWord (2*L) → R) (w : States L m t) :
    tableAfter (productLeaf left right) (2*L+1) w =
      ∑ v : LeafWord (2*L), if Compatible w.val v then left v * right v else 0 := by
  exact tableAfter_complete (productLeaf left right) w

/-- Every cyclic coefficient is actually stored at every high-state address. -/
abbrev StoredCoefficients (L m t q : ℕ) := Fin q × States L m t

theorem storedCoefficients_card_le (L m t q : ℕ) :
    Fintype.card (StoredCoefficients L m t q) ≤ q * (2*L+1) *
      Fintype.card (BaseStates L m t) := by
  simpa [StoredCoefficients, Nat.mul_assoc] using
    Nat.mul_le_mul_left q (stateCount_le_baseCount L m t)

/-- Actual ordinary positions of a box mask. Stars and private positions
carry no ordinary assignment coordinate. -/
abbrev MaskOrdinary {n : ℕ} (mask : Fin n → Option Bool) :=
  {i : Fin n // mask i = some true}

noncomputable instance maskOrdinaryFintype {n : ℕ} (mask : Fin n → Option Bool) :
    Fintype (MaskOrdinary mask) := Fintype.ofFinite _

abbrev OrdinaryAssignments {n : ℕ} (mask : Fin n → Option Bool) :=
  MaskOrdinary mask → Fin 4

/-- A labelled queried box, now represented by its actual fixed-word key. -/
def fixedWord {n : ℕ} (mask : Fin n → Option Bool) (a : OrdinaryAssignments mask) :
    Word n := fun i =>
  if h : mask i = some true then ⟨(a ⟨i,h⟩).val, by omega⟩
  else if mask i = some false then 4 else 5

/-- The same full-five compatibility language used by the algebraic partition. -/
def MaskCompatible {n : ℕ} (mask : Fin n → Option Bool) (v : LeafWord n) : Prop :=
  ∀ i, match mask i with
    | none => True
    | some false => v i = 4
    | some true => (v i).val < 4

theorem fixed_compatible_implies_mask {n : ℕ} (mask : Fin n → Option Bool)
    (a : OrdinaryAssignments mask) (v : LeafWord n) (h : Compatible (fixedWord mask a) v) :
    MaskCompatible mask v := by
  intro i
  cases hm : mask i with
  | none => trivial
  | some b =>
    cases b with
    | false =>
      apply Fin.ext
      simpa [fixedWord, hm] using h i (by simp [fixedWord, hm])
    | true =>
      have he := h i (by simp [fixedWord, hm]; omega)
      have ha := (a ⟨i,hm⟩).isLt
      simp only [fixedWord, hm, dite_true, Fin.val_mk] at he
      omega

/-- A compatible full leaf has one unique ordinary-label assignment. -/
def extractOrdinary {n : ℕ} (mask : Fin n → Option Bool) (v : LeafWord n)
    (h : MaskCompatible mask v) : OrdinaryAssignments mask :=
  fun i => ⟨(v i.val).val, by have hi := h i.val; simpa [i.property] using hi⟩

theorem compatible_fixed_iff {n : ℕ} (mask : Fin n → Option Bool)
    (v : LeafWord n) (h : MaskCompatible mask v) (a : OrdinaryAssignments mask) :
    Compatible (fixedWord mask a) v ↔ a = extractOrdinary mask v h := by
  constructor
  · intro hc
    funext i
    apply Fin.ext
    have he := hc i.val (by simp [fixedWord, i.property]; omega)
    simpa [fixedWord, i.property, extractOrdinary] using he.symm
  · intro he
    subst a
    intro i hi
    cases hm : mask i with
    | none => simp [fixedWord, hm] at hi
    | some b =>
      cases b with
      | false =>
        have hv := h i
        simpa [fixedWord, hm] using congrArg Fin.val (show v i = 4 by simpa [hm] using hv)
      | true => simp [fixedWord, hm, extractOrdinary]

/-- Generic partition of arbitrary global leaf values by the ordinary
assignments only. This is a disjoint partition, not a scalar product
factorization; stars remain inside their stored fixed-word box. -/
theorem ordinary_assignment_partition {n : ℕ} {R : Type*} [AddCommMonoid R]
    (mask : Fin n → Option Bool) (leaf : LeafWord n → R) :
    (∑ a : OrdinaryAssignments mask, boxValue (fixedWord mask a) leaf) =
      ∑ v : LeafWord n, if MaskCompatible mask v then leaf v else 0 := by
  classical
  unfold boxValue
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v hv
  by_cases h : MaskCompatible mask v
  · simp_rw [compatible_fixed_iff mask v h]
    simp [h]
  · have hn (a : OrdinaryAssignments mask) : ¬ Compatible (fixedWord mask a) v :=
      fun hc => h (fixed_compatible_implies_mask mask a v hc)
    simp [hn, h]

/-- Identification with the algebraic full-five compatible-label set. -/
theorem maskCompatible_iff_mem {n : ℕ} (mask : Fin n → Option Bool) (v : LeafWord n) :
    MaskCompatible mask v ↔ v ∈ OrderedBoxes.full5CompatibleLabels mask := by
  classical
  simp only [OrderedBoxes.full5CompatibleLabels, Finset.mem_filter,
    Finset.mem_univ, true_and]
  apply forall_congr'
  intro i
  cases hm : mask i with
  | none => simp [OrderedBoxes.full5Allowed]
  | some b =>
    cases b with
    | false => simp [OrderedBoxes.full5Allowed]
    | true =>
      simp only [OrderedBoxes.full5Allowed, Finset.mem_erase, Finset.mem_univ, and_true]
      have hv := (v i).isLt
      constructor
      · intro h he; have := congrArg Fin.val he; simp at this; omega
      · intro h
        have hn : (v i).val ≠ 4 := fun he => h (Fin.ext he)
        omega

/-- Finite algebraic box handles are precisely sums of fixed-word stored boxes. -/
theorem ordinary_assignment_partition_full5 {n : ℕ} {R : Type*} [AddCommMonoid R]
    (mask : Fin n → Option Bool) (leaf : LeafWord n → R) :
    (∑ a : OrdinaryAssignments mask, boxValue (fixedWord mask a) leaf) =
      ∑ v ∈ OrderedBoxes.full5CompatibleLabels mask, leaf v := by
  classical
  rw [ordinary_assignment_partition]
  simp only [OrderedBoxes.full5CompatibleLabels, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro v hv
  have he : MaskCompatible mask v ↔ ∀ i, v i ∈ OrderedBoxes.full5Allowed (mask i) := by
    simpa [OrderedBoxes.full5CompatibleLabels] using maskCompatible_iff_mem mask v
  rw [he]
  split_ifs <;> rfl

/-- Only ordinary positions inside the selected physical query support are
free. Every ordinary label outside that support is fixed by the locator. -/
abbrev SelectedOrdinary {n : ℕ} (mask : Fin n → Option Bool) (q : Finset (Fin n)) :=
  {i : MaskOrdinary mask // i.val ∈ q}

noncomputable instance selectedOrdinaryFintype {n : ℕ}
    (mask : Fin n → Option Bool) (q : Finset (Fin n)) :
    Fintype (SelectedOrdinary mask q) := Fintype.ofFinite _

abbrev SelectedAssignments {n : ℕ} (mask : Fin n → Option Bool) (q : Finset (Fin n)) :=
  SelectedOrdinary mask q → Fin 4

/-- Extend only the queried ordinary choices. Outside labels come directly
from the fixed locator and are not in the free assignment type. -/
def extendAssignment {n : ℕ} (mask : Fin n → Option Bool) (q : Finset (Fin n))
    (outside : Fin n → Fin 4) (a : SelectedAssignments mask q) : OrdinaryAssignments mask :=
  fun i => if h : i.val ∈ q then a ⟨i,h⟩ else outside i.val

def selectedWord {n : ℕ} (mask : Fin n → Option Bool) (q : Finset (Fin n))
    (outside : Fin n → Fin 4) (a : SelectedAssignments mask q) : Word n :=
  fixedWord mask (extendAssignment mask q outside a)

/-- Compatibility includes the actual fixed ordinary outside coordinates. -/
def SelectedCompatible {n : ℕ} (mask : Fin n → Option Bool) (q : Finset (Fin n))
    (outside : Fin n → Fin 4) (v : LeafWord n) : Prop :=
  MaskCompatible mask v ∧ ∀ i, i ∉ q → v i = (outside i).castSucc

theorem selected_compatible_implies {n : ℕ} (mask : Fin n → Option Bool)
    (q : Finset (Fin n)) (outside : Fin n → Fin 4)
    (ho : ∀ i, i ∉ q → mask i = some true)
    (a : SelectedAssignments mask q) (v : LeafWord n)
    (h : Compatible (selectedWord mask q outside a) v) :
    SelectedCompatible mask q outside v := by
  refine ⟨fixed_compatible_implies_mask _ _ _ h, ?_⟩
  intro i hi
  apply Fin.ext
  have hm := ho i hi
  have he := h i (by simp [selectedWord, fixedWord, hm, extendAssignment, hi]; omega)
  simpa [selectedWord, fixedWord, hm, extendAssignment, hi] using he

/-- Restrict the unique ordinary assignment to the genuine free query keys. -/
def extractSelected {n : ℕ} (mask : Fin n → Option Bool) (q : Finset (Fin n))
    (outside : Fin n → Fin 4) (v : LeafWord n) (h : SelectedCompatible mask q outside v) :
    SelectedAssignments mask q := fun i => extractOrdinary mask v h.1 i.val

theorem compatible_selected_iff {n : ℕ} (mask : Fin n → Option Bool)
    (q : Finset (Fin n)) (outside : Fin n → Fin 4) (v : LeafWord n)
    (h : SelectedCompatible mask q outside v) (a : SelectedAssignments mask q) :
    Compatible (selectedWord mask q outside a) v ↔ a = extractSelected mask q outside v h := by
  change Compatible (fixedWord mask (extendAssignment mask q outside a)) v ↔ _
  rw [compatible_fixed_iff mask v h.1]
  constructor
  · intro he
    funext i
    have hh := congrFun he i.val
    simpa [extendAssignment, i.property, extractSelected] using hh
  · intro he
    subst a
    funext i
    by_cases hi : i.val ∈ q
    · simp [extendAssignment, hi, extractSelected]
    · apply Fin.ext
      have hv := congrArg Fin.val (h.2 i.val hi)
      simpa [extendAssignment, hi, extractOrdinary] using hv.symm

/-- Arbitrary global leaves partition over only the ordinary choices in `q`.
All outside labels are held fixed, even for entangled source arrays. -/
theorem selected_assignment_partition {n : ℕ} {R : Type*} [AddCommMonoid R]
    (mask : Fin n → Option Bool) (q : Finset (Fin n)) (outside : Fin n → Fin 4)
    (ho : ∀ i, i ∉ q → mask i = some true) (leaf : LeafWord n → R) :
    (∑ a : SelectedAssignments mask q, boxValue (selectedWord mask q outside a) leaf) =
      ∑ v : LeafWord n, if SelectedCompatible mask q outside v then leaf v else 0 := by
  classical
  unfold boxValue
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v hv
  by_cases h : SelectedCompatible mask q outside v
  · simp_rw [compatible_selected_iff mask q outside v h]
    simp [h]
  · have hn (a : SelectedAssignments mask q) :
        ¬ Compatible (selectedWord mask q outside a) v :=
      fun hc => h (selected_compatible_implies mask q outside ho a v hc)
    simp [hn, h]

/-- Actual ordinary query-key cardinality; there is no outside-label factor. -/
theorem selectedAssignments_card {n : ℕ} (mask : Fin n → Option Bool)
    (q : Finset (Fin n)) :
    Fintype.card (SelectedAssignments mask q) =
      4 ^ (q.filter (fun i => mask i = some true)).card := by
  classical
  let e : SelectedOrdinary mask q ≃ ↥(q.filter (fun i => mask i = some true)) :=
    { toFun := fun i => ⟨i.val.val, by simp [i.property, i.val.property]⟩
      invFun := fun i => ⟨⟨i.val, (Finset.mem_filter.mp i.property).2⟩,
        (Finset.mem_filter.mp i.property).1⟩
      left_inv := fun i => Subtype.ext (Subtype.ext rfl)
      right_inv := fun i => Subtype.ext rfl }
  rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_congr e, Fintype.card_coe]

@[simp] theorem fixedWord_special_iff {n : ℕ} (mask : Fin n → Option Bool)
    (a : OrdinaryAssignments mask) (i : Fin n) :
    4 ≤ (fixedWord mask a i).val ↔ mask i ≠ some true := by
  cases hm : mask i with
  | none => simp [fixedWord, hm]
  | some b => cases b <;> simp [fixedWord, hm]

@[simp] theorem fixedWord_star_iff {n : ℕ} (mask : Fin n → Option Bool)
    (a : OrdinaryAssignments mask) (i : Fin n) :
    (fixedWord mask a i).val = 5 ↔ mask i = none := by
  cases hm : mask i with
  | none => simp [fixedWord, hm]
  | some b =>
    cases b with
    | false => simp [fixedWord, hm]
    | true => simp [fixedWord, hm]; omega

@[simp] theorem fixedWord_private_iff {n : ℕ} (mask : Fin n → Option Bool)
    (a : OrdinaryAssignments mask) (i : Fin n) :
    (fixedWord mask a i).val = 4 ↔ mask i = some false := by
  cases hm : mask i with
  | none => simp [fixedWord, hm]
  | some b =>
    cases b with
    | false => simp [fixedWord, hm]
    | true => simp [fixedWord, hm]; omega

/-- All distinguished support lies in the genuine selected inner positions.
This proves the cap from actual supports, with outside positions fixed ordinary. -/
theorem selectedWord_specialCount {n : ℕ} (mask : Fin n → Option Bool)
    (q : Finset (Fin n)) (outside : Fin n → Fin 4)
    (ho : ∀ i, i ∉ q → mask i = some true) (a : SelectedAssignments mask q)
    (region : Fin n → Prop) :
    specialCount (selectedWord mask q outside a) region =
      (q.filter (fun i => region i ∧ mask i ≠ some true)).card := by
  classical
  unfold specialCount selectedWord
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, fixedWord_special_iff]
  constructor
  · rintro ⟨hr, hm⟩
    have hi : i ∈ q := by
      by_contra hn
      exact hm (ho i hn)
    exact ⟨hi, hr, hm⟩
  · rintro ⟨hi, hr, hm⟩
    exact ⟨hr, hm⟩

/-- The source's actual `m`-per-half inner support and `t` ordinary choices
imply every labelled query box satisfies the stored balanced caps. -/
theorem selectedWord_balanced {L m t : ℕ} (mask : Fin (2*L) → Option Bool)
    (q : Finset (Fin (2*L))) (outside : Fin (2*L) → Fin 4)
    (ho : ∀ i, i ∉ q → mask i = some true)
    (hleft : (q.filter (fun i => i.val < L)).card ≤ m)
    (hright : (q.filter (fun i => L ≤ i.val)).card ≤ m)
    (hq : q.card = 2*m) (ht : (q.filter (fun i => mask i = some true)).card = t)
    (a : SelectedAssignments mask q) : Balanced L m t (selectedWord mask q outside a) := by
  classical
  unfold Balanced
  refine ⟨?_, ?_, ?_⟩
  · rw [selectedWord_specialCount mask q outside ho]
    apply le_trans (Finset.card_le_card ?_) hleft
    intro i hi
    simp only [Finset.mem_filter] at hi ⊢
    exact ⟨hi.1, hi.2.1⟩
  · rw [selectedWord_specialCount mask q outside ho]
    apply le_trans (Finset.card_le_card ?_) hright
    intro i hi
    simp only [Finset.mem_filter] at hi ⊢
    exact ⟨hi.1, hi.2.1⟩
  · rw [selectedWord_specialCount mask q outside ho]
    simp only [true_and]
    have hp : t + (q.filter (fun i => mask i ≠ some true)).card = 2*m := by
      simpa only [ht, hq] using Finset.card_filter_add_card_filter_not
        (s := q) (fun i => mask i = some true)
    omega

/-- Physical mask ordering is inherited by every ordinary labelling. -/
theorem fixedWord_ordered {n : ℕ} (mask : Fin n → Option Bool)
    (horder : ∀ i j, mask i = none → mask j = some false → i.val < j.val)
    (a : OrdinaryAssignments mask) : Ordered (fixedWord mask a) := by
  intro i j hi hj
  exact horder i j ((fixedWord_star_iff mask a i).mp hi)
    ((fixedWord_private_iff mask a j).mp hj)

/-- The actual stored address for a physical queried box. Its outside
ordinary labels are fixed, and only its inner ordinary positions are free. -/
def selectedState {L m t : ℕ} (mask : Fin (2*L) → Option Bool)
    (q : Finset (Fin (2*L))) (outside : Fin (2*L) → Fin 4)
    (ho : ∀ i, i ∉ q → mask i = some true)
    (hleft : (q.filter (fun i => i.val < L)).card ≤ m)
    (hright : (q.filter (fun i => L ≤ i.val)).card ≤ m)
    (hq : q.card = 2*m) (ht : (q.filter (fun i => mask i = some true)).card = t)
    (horder : ∀ i j, mask i = none → mask j = some false → i.val < j.val)
    (a : SelectedAssignments mask q) : States L m t :=
  ⟨selectedWord mask q outside a,
    selectedWord_balanced mask q outside ho hleft hright hq ht a,
    fixedWord_ordered mask horder _⟩

/-- All algebraic high-box contributions are recovered by reads of the
completed stored table, with the actual fixed outside locator. -/
theorem stored_selected_query {L m t : ℕ} {R : Type*} [AddCommMonoid R]
    (mask : Fin (2*L) → Option Bool) (q : Finset (Fin (2*L)))
    (outside : Fin (2*L) → Fin 4) (ho : ∀ i, i ∉ q → mask i = some true)
    (hleft : (q.filter (fun i => i.val < L)).card ≤ m)
    (hright : (q.filter (fun i => L ≤ i.val)).card ≤ m)
    (hq : q.card = 2*m) (ht : (q.filter (fun i => mask i = some true)).card = t)
    (horder : ∀ i j, mask i = none → mask j = some false → i.val < j.val)
    (leaf : LeafWord (2*L) → R) :
    (∑ a : SelectedAssignments mask q,
      tableAfter leaf (2*L+1) (selectedState mask q outside ho hleft hright hq ht horder a)) =
      ∑ v : LeafWord (2*L), if SelectedCompatible mask q outside v then leaf v else 0 := by
  classical
  simp_rw [tableAfter_complete]
  exact selected_assignment_partition mask q outside ho leaf

/-- Exactly `4^t` stored reads for one physical box mask. -/
theorem selected_query_read_count {n t : ℕ} (mask : Fin n → Option Bool)
    (q : Finset (Fin n)) (ht : (q.filter (fun i => mask i = some true)).card = t) :
    Fintype.card (SelectedAssignments mask q) = 4^t := by
  rw [selectedAssignments_card, ht]

/-- The actual finite stored high-state family has the source's box saving
`G`, with explicit polynomial overhead and the original full-grid count. -/
theorem rounded_highState_bound (c theta : ℝ) (m : ℕ)
    (hc : 5 < c) (ht0 : 0 < theta) (ht1 : theta < 1/2) (hm : 0 < m) :
    let L := Nat.ceil (c*(m:ℝ))
    let t := Nat.ceil (2*theta*(m:ℝ))
    (Fintype.card (States L m t) : ℝ) ≤ (2*L+1:ℝ) *
      ((L+1:ℝ)^4 * Real.exp (HighBoxEntropy.roundingConstant c theta) *
        (EntropyBounds.gridCount L m)^2 * ((4:ℝ)^m)^(-HighBoxEntropy.boxSaving c theta)) := by
  let L := Nat.ceil (c*(m:ℝ))
  let t := Nat.ceil (2*theta*(m:ℝ))
  have hf : (Fintype.card (States L m t) : ℝ) ≤ (2*L+1:ℝ) *
      (Fintype.card (CacheCardinality.TotalCappedLeaves L m (2*m-t)) : ℝ) := by
    have h := stateCount_le_baseCount L m t
    rw [Fintype.card_congr (baseStatesEquivTotalCapped L m t)] at h
    exact_mod_cast h
  have hb := HighBoxEntropy.rounded_totalCappedLeaves_polynomial c theta m hc ht0 ht1 hm
  exact hf.trans (mul_le_mul_of_nonneg_left hb (by positivity))

/-- Full high-table ring arithmetic, writes, and explicit operand reads have
an eleven-times-state bound. The complete original-grid entropy saving is
retained; coefficient-width/bit costs are separate ring-cost multipliers. -/
theorem rounded_highPreprocessing_bound (c theta : ℝ) (m : ℕ)
    (hc : 5 < c) (ht0 : 0 < theta) (ht1 : theta < 1/2) (hm : 0 < m) :
    let L := Nat.ceil (c*(m:ℝ))
    let t := Nat.ceil (2*theta*(m:ℝ))
    ((preprocessingWork L m t + preprocessingReads L m t : ℕ) : ℝ) ≤
      11 * ((2*L+1:ℝ) * ((L+1:ℝ)^4 * Real.exp (HighBoxEntropy.roundingConstant c theta) *
        (EntropyBounds.gridCount L m)^2 * ((4:ℝ)^m)^(-HighBoxEntropy.boxSaving c theta))) := by
  let L := Nat.ceil (c*(m:ℝ))
  let t := Nat.ceil (2*theta*(m:ℝ))
  have hf : ((preprocessingWork L m t + preprocessingReads L m t : ℕ) : ℝ) ≤
      11 * (Fintype.card (States L m t) : ℝ) := by
    exact_mod_cast preprocessing_with_reads_le L m t
  exact hf.trans (mul_le_mul_of_nonneg_left
    (rounded_highState_bound c theta m hc ht0 ht1 hm) (by norm_num))

/-- TensorContraction lists masks in reverse physical order. Reversing
its finite index therefore recovers the physical mask used by the table. -/
def reverseMask (ms : List (Option Bool)) : Fin ms.length → Option Bool :=
  fun i => ms[i.rev.val]?.getD none

theorem scan_star_after_private (ms : List (Option Bool))
    (hshape : ∃ bs : List Bool, ∃ r : ℕ, ms = bs.map some ++ List.replicate r none)
    (i j : Fin ms.length) (hi : ms[i.val]?.getD none = none)
    (hj : ms[j.val]?.getD none = some false) : j.val < i.val := by
  rcases hshape with ⟨bs,r,rfl⟩
  rw [List.getElem?_eq_getElem i.isLt] at hi
  rw [List.getElem?_eq_getElem j.isLt] at hj
  simp only [Option.getD_some] at hi hj
  have hs : bs.length ≤ i.val := by
    by_contra hn
    have hlt : i.val < (bs.map some).length := by simp; omega
    rw [List.getElem_append_left hlt, List.getElem_map] at hi
    contradiction
  have hp : j.val < bs.length := by
    by_contra hn
    have hge : (bs.map some).length ≤ j.val := by simp; omega
    rw [List.getElem_append_right hge, List.getElem_replicate] at hj
    contradiction
  omega

/-- The masks produced by the algebraic high partition have exactly the
physical star-before-private order required by the stored-state DP. -/
theorem reverseMask_ordered {t k : ℕ} {ms : List (Option Bool)}
    (hms : ms ∈ OrderedBoxes.orderedBoxMasks t k) :
    ∀ i j, reverseMask ms i = none → reverseMask ms j = some false → i.val < j.val := by
  intro i j hi hj
  have h := scan_star_after_private ms (OrderedBoxes.orderedBoxMasks_shape hms).2.2
    i.rev j.rev hi hj
  have hf : j.rev < i.rev := h
  exact Fin.rev_lt_rev.mp hf

/-- Reversing the physical mask preserves its exact ordinary count. -/
theorem reverseMask_ordinary_count (ms : List (Option Bool)) :
    (Finset.univ.filter (fun i : Fin ms.length => reverseMask ms i = some true)).card =
      ms.count (some true) := by
  classical
  let e : {i : Fin ms.length // reverseMask ms i = some true} ≃
      {i : Fin ms.length // ms[i.val]?.getD none = some true} :=
    { toFun := fun i => ⟨i.val.rev, i.property⟩
      invFun := fun i => ⟨i.val.rev, by simpa [reverseMask] using i.property⟩
      left_inv := fun i => Subtype.ext (Fin.rev_rev i.val)
      right_inv := fun i => Subtype.ext (Fin.rev_rev i.val) }
  have he := Fintype.card_congr e
  simp only [Fintype.card_subtype] at he
  have hn : (Finset.univ.filter (fun i : Fin ms.length => ms[i.val]?.getD none = some true)) =
      OrderedBoxes.ordinaryPositions ms := by
    ext i
    simp [OrderedBoxes.ordinaryPositions]
  rw [hn] at he
  exact he.trans (OrderedBoxes.ordinaryPositions_card ms)

/-- Each generated high mask has exactly the threshold's ordinary choices
in its original, nonclamped inner domain. -/
theorem reverseMask_ordinary_count_of_generated {t k : ℕ} {ms : List (Option Bool)}
    (hms : ms ∈ OrderedBoxes.orderedBoxMasks t k) :
    (Finset.univ.filter (fun i : Fin ms.length => reverseMask ms i = some true)).card = t := by
  rw [reverseMask_ordinary_count, (OrderedBoxes.orderedBoxMasks_shape hms).2.1]

/-- Actual physical inner positions, embedded in increasing physical order. -/
def embeddedSupport {k n : ℕ} (e : Fin k ↪o Fin n) : Finset (Fin n) :=
  Finset.univ.image e

/-- Embed an inner box mask; every outside position is ordinary and fixed. -/
noncomputable def embeddedMask {k n : ℕ} (e : Fin k ↪o Fin n)
    (mask : Fin k → Option Bool) : Fin n → Option Bool := fun i =>
  if h : ∃ j, e j = i then mask (Classical.choose h) else some true

@[simp] theorem embeddedMask_at {k n : ℕ} (e : Fin k ↪o Fin n)
    (mask : Fin k → Option Bool) (j : Fin k) : embeddedMask e mask (e j) = mask j := by
  have h : ∃ a, e a = e j := ⟨j,rfl⟩
  simp only [embeddedMask, dif_pos h]
  congr 1
  exact e.injective (Classical.choose_spec h)

theorem embeddedSupport_card {k n : ℕ} (e : Fin k ↪o Fin n) :
    (embeddedSupport e).card = k := by
  rw [embeddedSupport, Finset.card_image_of_injective _ e.injective]
  simp

theorem embeddedMask_outside {k n : ℕ} (e : Fin k ↪o Fin n)
    (mask : Fin k → Option Bool) (i : Fin n) (hi : i ∉ embeddedSupport e) :
    embeddedMask e mask i = some true := by
  have hn : ¬ ∃ j, e j = i := by simpa [embeddedSupport] using hi
  simp [embeddedMask, hn]

theorem embeddedMask_ordered {k n : ℕ} (e : Fin k ↪o Fin n)
    (mask : Fin k → Option Bool)
    (horder : ∀ i j, mask i = none → mask j = some false → i.val < j.val) :
    ∀ i j, embeddedMask e mask i = none → embeddedMask e mask j = some false →
      i.val < j.val := by
  intro i j hi hj
  have hqi : i ∈ embeddedSupport e := by
    by_contra hn
    rw [embeddedMask_outside e mask i hn] at hi
    contradiction
  have hqj : j ∈ embeddedSupport e := by
    by_contra hn
    rw [embeddedMask_outside e mask j hn] at hj
    contradiction
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hqi
  obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hqj
  rw [embeddedMask_at] at hi hj
  exact e.strictMono (horder a b hi hj)

/-- Embedding an inner mask creates no extra ordinary query choice. -/
theorem embeddedMask_ordinary_count {k n : ℕ} (e : Fin k ↪o Fin n)
    (mask : Fin k → Option Bool) :
    ((embeddedSupport e).filter (fun i => embeddedMask e mask i = some true)).card =
      (Finset.univ.filter (fun i => mask i = some true)).card := by
  classical
  have he : (embeddedSupport e).filter (fun i => embeddedMask e mask i = some true) =
      (Finset.univ.filter (fun i => mask i = some true)).image e := by
    ext i
    constructor
    · intro hi
      obtain ⟨hq,hm⟩ := Finset.mem_filter.mp hi
      obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hq
      apply Finset.mem_image.mpr
      exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa using hm⟩, rfl⟩
    · intro hi
      obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hi
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩,
        by simpa using (Finset.mem_filter.mp hj).2⟩
  rw [he, Finset.card_image_of_injective _ e.injective]

/-- A generated algebraic high mask, embedded in the full original source
geometry, yields a genuine stored physical handle for every ordinary key. -/
noncomputable def physicalState {L m t k : ℕ} (ms : List (Option Bool))
    (hms : ms ∈ OrderedBoxes.orderedBoxMasks t k) (hlen : ms.length = 2*m)
    (e : Fin ms.length ↪o Fin (2*L)) (outside : Fin (2*L) → Fin 4)
    (hleft : ((embeddedSupport e).filter (fun i => i.val < L)).card ≤ m)
    (hright : ((embeddedSupport e).filter (fun i => L ≤ i.val)).card ≤ m)
    (a : SelectedAssignments (embeddedMask e (reverseMask ms)) (embeddedSupport e)) :
    States L m t :=
  selectedState (embeddedMask e (reverseMask ms)) (embeddedSupport e) outside
    (embeddedMask_outside e (reverseMask ms)) hleft hright
    (by rw [embeddedSupport_card, hlen])
    (by rw [embeddedMask_ordinary_count, reverseMask_ordinary_count_of_generated hms])
    (embeddedMask_ordered e (reverseMask ms) (reverseMask_ordered hms)) a

/-- The actual physical high-box handle count is `4^t`, independently of
all outside coordinates and of the size of the physical source geometry. -/
theorem physicalState_key_count {L t k : ℕ} (ms : List (Option Bool))
    (hms : ms ∈ OrderedBoxes.orderedBoxMasks t k)
    (e : Fin ms.length ↪o Fin (2*L)) :
    Fintype.card (SelectedAssignments (embeddedMask e (reverseMask ms)) (embeddedSupport e)) =
      4^t := by
  rw [selectedAssignments_card, embeddedMask_ordinary_count,
    reverseMask_ordinary_count_of_generated hms]

/-- Full physical query correctness for a generated reverse-scan mask. -/
theorem physicalState_query {L m t k : ℕ} {R : Type*} [AddCommMonoid R]
    (ms : List (Option Bool)) (hms : ms ∈ OrderedBoxes.orderedBoxMasks t k)
    (hlen : ms.length = 2*m) (e : Fin ms.length ↪o Fin (2*L))
    (outside : Fin (2*L) → Fin 4)
    (hleft : ((embeddedSupport e).filter (fun i => i.val < L)).card ≤ m)
    (hright : ((embeddedSupport e).filter (fun i => L ≤ i.val)).card ≤ m)
    (leaf : LeafWord (2*L) → R) :
    (∑ a : SelectedAssignments (embeddedMask e (reverseMask ms)) (embeddedSupport e),
      tableAfter leaf (2*L+1) (physicalState ms hms hlen e outside hleft hright a)) =
      ∑ v : LeafWord (2*L),
        if SelectedCompatible (embeddedMask e (reverseMask ms)) (embeddedSupport e) outside v
        then leaf v else 0 := by
  classical
  simp_rw [tableAfter_complete]
  exact selected_assignment_partition _ _ _ (embeddedMask_outside _ _) leaf

/-- Extracting one additive coefficient from each fully stored box recovers
the requested coefficient of the high contribution. Preprocessing stores
all coefficients, while this query performs one coefficient read per key. -/
theorem physicalState_coefficient_query {L m t k : ℕ} {R S : Type*}
    [AddCommMonoid R] [AddCommMonoid S] (coefficient : R →+ S)
    (ms : List (Option Bool)) (hms : ms ∈ OrderedBoxes.orderedBoxMasks t k)
    (hlen : ms.length = 2*m) (e : Fin ms.length ↪o Fin (2*L))
    (outside : Fin (2*L) → Fin 4)
    (hleft : ((embeddedSupport e).filter (fun i => i.val < L)).card ≤ m)
    (hright : ((embeddedSupport e).filter (fun i => L ≤ i.val)).card ≤ m)
    (leaf : LeafWord (2*L) → R) :
    (∑ a : SelectedAssignments (embeddedMask e (reverseMask ms)) (embeddedSupport e),
      coefficient (tableAfter leaf (2*L+1)
        (physicalState ms hms hlen e outside hleft hright a))) =
      coefficient (∑ v : LeafWord (2*L),
        if SelectedCompatible (embeddedMask e (reverseMask ms)) (embeddedSupport e) outside v
        then leaf v else 0) := by
  classical
  rw [← map_sum]
  exact congrArg coefficient (physicalState_query ms hms hlen e outside hleft hright leaf)

/-- The actual free-key count for the whole generated family is exactly
`choose k t * 4^t`. Each member's outside labels remain fixed. -/
theorem physicalQuery_key_count (L k t : ℕ)
    (e : ∀ ms : ↥(OrderedBoxes.orderedBoxMasks t k).toFinset,
      Fin ms.val.length ↪o Fin (2*L)) :
    Fintype.card (Σ ms : ↥(OrderedBoxes.orderedBoxMasks t k).toFinset,
      SelectedAssignments (embeddedMask (e ms) (reverseMask ms.val)) (embeddedSupport (e ms))) =
      k.choose t * 4^t := by
  classical
  rw [Fintype.card_sigma]
  have he (ms : ↥(OrderedBoxes.orderedBoxMasks t k).toFinset) :
      Fintype.card (SelectedAssignments (embeddedMask (e ms) (reverseMask ms.val))
        (embeddedSupport (e ms))) = 4^t :=
    physicalState_key_count ms.val (List.mem_toFinset.mp ms.property) (e ms)
  simp_rw [he]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe,
    List.toFinset_card_of_nodup (OrderedBoxes.orderedBoxMasks_nodup t k),
    OrderedBoxes.orderedBoxMasks_length]
  simp

end ThinMatrix.HighBoxDP

#print axioms ThinMatrix.HighBoxDP.boxValue_expand
#print axioms ThinMatrix.HighBoxDP.ordered_replace_last
#print axioms ThinMatrix.HighBoxDP.starCount_replace_lt
#print axioms ThinMatrix.HighBoxDP.stateCount_le_baseCount
#print axioms ThinMatrix.HighBoxDP.preprocessingWork_le_balanced_bases

#print axioms ThinMatrix.HighBoxDP.tableAfter_complete
#print axioms ThinMatrix.HighBoxDP.scheduledWork_le_six_states
#print axioms ThinMatrix.HighBoxDP.preprocessing_with_reads_le

#print axioms ThinMatrix.HighBoxDP.baseStates_card
#print axioms ThinMatrix.HighBoxDP.stateCount_le_balanced_sum
#print axioms ThinMatrix.HighBoxDP.baseCacheWord
#print axioms ThinMatrix.HighBoxDP.tableAfter_products_complete
#print axioms ThinMatrix.HighBoxDP.storedCoefficients_card_le

#print axioms ThinMatrix.HighBoxDP.ordinary_assignment_partition_full5

#print axioms ThinMatrix.HighBoxDP.selected_assignment_partition
#print axioms ThinMatrix.HighBoxDP.selectedAssignments_card

#print axioms ThinMatrix.HighBoxDP.selectedWord_balanced
#print axioms ThinMatrix.HighBoxDP.stored_selected_query
#print axioms ThinMatrix.HighBoxDP.selected_query_read_count

#print axioms ThinMatrix.HighBoxDP.rounded_highState_bound
#print axioms ThinMatrix.HighBoxDP.rounded_highPreprocessing_bound

#print axioms ThinMatrix.HighBoxDP.reverseMask_ordered
#print axioms ThinMatrix.HighBoxDP.reverseMask_ordinary_count_of_generated

#print axioms ThinMatrix.HighBoxDP.physicalState
#print axioms ThinMatrix.HighBoxDP.physicalState_key_count

#print axioms ThinMatrix.HighBoxDP.physicalState_query
#print axioms ThinMatrix.HighBoxDP.physicalState_coefficient_query
#print axioms ThinMatrix.HighBoxDP.physicalQuery_key_count
