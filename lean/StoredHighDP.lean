import HighBoxDP
import CappedEnumeration

/-!
# Materialized high-box vectors in a six-way array trie

The dictionary below stores vectors in array-backed nodes. Reading a key
traverses its digits; it never searches the state enumeration or recomputes
an earlier dynamic-programming layer. Prefix generation visits six extensions
of retained parents, testing the actual balanced and ordered language.

The execution counters are finite data-structure operations. Compilation to
word RAM and the implementation of the supplied base multiplication are
separate obligations.
-/
namespace ThinMatrix.StoredHighDP

open scoped BigOperators
open CacheBounds HighBoxDP CappedEnumeration

/-- A real array of six child pointers, with an optional stored payload. -/
inductive Trie (A : Type*) where
  | empty
  | node (value : Option A) (children : Array (Trie A))

namespace Trie

def children {A : Type*} : Trie A → Array (Trie A)
  | .empty => #[]
  | .node _ cs => cs

def value {A : Type*} : Trie A → Option A
  | .empty => none
  | .node v _ => v

def child {A : Type*} (t : Trie A) (a : Label) : Trie A :=
  (children t)[a.val]?.getD .empty

def read {A : Type*} : Trie A → List Label → Option A
  | t, [] => value t
  | t, a :: as => read (child t a) as

def write {A : Type*} : Trie A → List Label → A → Trie A
  | t, [], x => .node (some x) (children t)
  | t, a :: as, x =>
      let next := write (child t a) as x
      .node (value t) (Array.ofFn (fun b : Label => if b = a then next else child t b))

@[simp] theorem read_write_same {A : Type*} (t : Trie A) (key : List Label) (x : A) :
    read (write t key x) key = some x := by
  induction key generalizing t with
  | nil => rfl
  | cons a as ih =>
      simpa [write, read, child, children] using ih (child t a)

theorem read_write_other {A : Type*} (t : Trie A) (key other : List Label)
    (x : A) (hne : other ≠ key) : read (write t key x) other = read t other := by
  induction key generalizing t other with
  | nil =>
      cases other with
      | nil => exact False.elim (hne rfl)
      | cons b bs => rfl
  | cons a as ih =>
      cases other with
      | nil => rfl
      | cons b bs =>
          simp only [write, read]
          by_cases hab : b = a
          · subst b
            simp only [child, children, Array.getElem?_ofFn, dif_pos a.isLt, Fin.eta, ite_true, Option.getD_some]
            apply ih
            intro h
            exact hne (by simp [h])
          · simp [child, children, hab]

/-- Read cost counts one child pointer per digit and the terminal payload. -/
def readCounted {A : Type*} : Trie A → List Label → Option A × ℕ
  | t, [] => (value t, 1)
  | t, a :: as =>
      let r := readCounted (child t a) as
      (r.1, r.2 + 1)

/-- A persistent update copies at most six child pointers per visited node.
The payload is a pointer to the newly materialized coefficient vector. -/
def writeCounted {A : Type*} : Trie A → List Label → A → Trie A × ℕ
  | t, [], x => (.node (some x) (children t), 7)
  | t, a :: as, x =>
      let r := writeCounted (child t a) as x
      (.node (value t) (Array.ofFn (fun b : Label => if b = a then r.1 else child t b)), r.2 + 8)

@[simp] theorem readCounted_value {A : Type*} (t : Trie A) (key : List Label) :
    (readCounted t key).1 = read t key := by
  induction key generalizing t with
  | nil => rfl
  | cons a as ih => simp [readCounted, read, ih]

@[simp] theorem readCounted_work {A : Type*} (t : Trie A) (key : List Label) :
    (readCounted t key).2 = key.length + 1 := by
  induction key generalizing t with
  | nil => rfl
  | cons a as ih => simp [readCounted, ih, Nat.add_assoc]

@[simp] theorem writeCounted_value {A : Type*} (t : Trie A) (key : List Label) (x : A) :
    (writeCounted t key x).1 = write t key x := by
  induction key generalizing t with
  | nil => rfl
  | cons a as ih => simp [writeCounted, write, ih]

@[simp] theorem writeCounted_work {A : Type*} (t : Trie A) (key : List Label) (x : A) :
    (writeCounted t key x).2 = 8 * key.length + 7 := by
  induction key generalizing t with
  | nil => rfl
  | cons a as ih => simp [writeCounted, ih]; omega

end Trie

def key {n : ℕ} (w : Word n) : List Label := (List.finRange n).map w

@[simp] theorem key_length {n : ℕ} (w : Word n) : (key w).length = n := by simp [key]

theorem key_injective (n : ℕ) : Function.Injective (@key n) := by
  intro w v h
  funext i
  have he := List.map_inj_left.mp h i (by simp)
  exact he

/-- Computable position tests for the actual high-state language. -/
def highTest (L m t : ℕ) (w : Word (2*L)) : Bool :=
  decide (countBool w (fun i a => decide (i.val < L ∧ 4 ≤ a.val)) ≤ m) &&
  decide (countBool w (fun i a => decide (L ≤ i.val ∧ 4 ≤ a.val)) ≤ m) &&
  decide (countBool w (fun _ a => decide (4 ≤ a.val)) ≤ 2*m-t) &&
  (List.finRange (2*L)).all (fun i =>
    (List.finRange (2*L)).all (fun j =>
      decide ((w i).val = 5 → (w j).val = 4 → i.val < j.val)))

theorem highTest_eq_true (L m t : ℕ) (w : Word (2*L)) :
    highTest L m t w = true ↔ Balanced L m t w ∧ Ordered w := by
  have hc (p : Fin (2*L) → Label → Prop) (dp : ∀ i a, Decidable (p i a)) :
      countBool w (fun i a => @decide (p i a) (dp i a)) = countPositions w p := by
    rw [countBool_eq]
    simp only [decide_eq_true_eq]
  simp only [highTest, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_finRange, true_implies]
  rw [hc (fun i a => i.val < L ∧ 4 ≤ a.val) (fun i a => inferInstance),
    hc (fun i a => L ≤ i.val ∧ 4 ≤ a.val) (fun i a => inferInstance),
    hc (fun _ a => 4 ≤ a.val) (fun i a => inferInstance)]
  simp only [HighBoxDP.Balanced, specialCount, countPositions, Ordered, true_and, and_assoc]

theorem high_zero (L m t : ℕ) :
    Balanced L m t (zeroWord (2*L)) ∧ Ordered (zeroWord (2*L)) := by
  constructor
  · simp [HighBoxDP.Balanced, specialCount, zeroWord]
  · intro i j hi
    simp [zeroWord] at hi

theorem specialCount_trim_le {n : ℕ} (d : ℕ) (w : Word n) (region : Fin n → Prop) :
    specialCount (trimWord d w) region ≤ specialCount w region := by
  classical
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  refine ⟨hi.1, ?_⟩
  by_cases h : i.val < d
  · simpa [trimWord, h] using hi.2
  · simp [trimWord, h] at hi

theorem high_trim {L m t : ℕ} (d : ℕ) (w : Word (2*L))
    (hw : Balanced L m t w ∧ Ordered w) :
    Balanced L m t (trimWord d w) ∧ Ordered (trimWord d w) := by
  refine ⟨⟨(specialCount_trim_le d w _).trans hw.1.1,
    (specialCount_trim_le d w _).trans hw.1.2.1,
    (specialCount_trim_le d w _).trans hw.1.2.2⟩, ?_⟩
  intro i j hi hj
  have hib : i.val < d := by
    by_contra hn
    simp [trimWord, hn] at hi
  have hjb : j.val < d := by
    by_contra hn
    simp [trimWord, hn] at hj
  exact hw.2 i j (by simpa [trimWord, hib] using hi) (by simpa [trimWord, hjb] using hj)

def highChildren (L m t d : ℕ) (hd : d < 2*L) (w : Word (2*L)) : List (Word (2*L)) :=
  ((List.finRange 6).map (put d hd w)).filter (highTest L m t)

def generate (L m t : ℕ) : ℕ → List (Word (2*L))
  | 0 => [zeroWord (2*L)]
  | d+1 => if hd : d < 2*L then
      (generate L m t d).flatMap (highChildren L m t d hd) else []

theorem mem_highChildren (L m t d : ℕ) (hd : d < 2*L) (w v : Word (2*L)) :
    v ∈ highChildren L m t d hd w ↔
      ∃ a : Label, put d hd w a = v ∧ Balanced L m t v ∧ Ordered v := by
  simp only [highChildren, List.mem_filter, List.mem_map, List.mem_finRange,
    true_and, highTest_eq_true]
  aesop

theorem mem_generate (L m t d : ℕ) (hd : d ≤ 2*L) (w : Word (2*L)) :
    w ∈ generate L m t d ↔ IsPrefix d w ∧ Balanced L m t w ∧ Ordered w := by
  induction d generalizing w with
  | zero =>
      simp only [generate, List.mem_singleton]
      constructor
      · intro h; subst w; exact ⟨fun _ _ => rfl, high_zero L m t⟩
      · intro h; funext i; exact h.1 i (Nat.zero_le _)
  | succ d ih =>
      have hlt : d < 2*L := by omega
      rw [generate, dif_pos hlt, List.mem_flatMap]
      constructor
      · rintro ⟨p, hp, hc⟩
        obtain ⟨a, rfl, hv⟩ := (mem_highChildren L m t d hlt p w).mp hc
        exact ⟨put_prefix hlt p a ((ih (by omega) p).mp hp).1, hv⟩
      · rintro ⟨hp, hv⟩
        refine ⟨trimWord d w, (ih (by omega) _).mpr ⟨trim_isPrefix d w, high_trim d w hv⟩, ?_⟩
        exact (mem_highChildren L m t d hlt _ w).mpr
          ⟨w ⟨d,hlt⟩, put_trim hlt w hp, hv⟩

theorem generate_nodup (L m t d : ℕ) (hd : d ≤ 2*L) : (generate L m t d).Nodup := by
  induction d with
  | zero => simp [generate]
  | succ d ih =>
      have hlt : d < 2*L := by omega
      rw [generate, dif_pos hlt]
      apply List.nodup_flatMap.mpr
      refine ⟨fun w _ => ((List.nodup_finRange 6).map (put_label_injective hlt w)).filter _, ?_⟩
      apply (ih (by omega)).imp_of_mem
      intro w v hw hv hne
      apply List.disjoint_left.mpr
      intro z hzw hzv
      obtain ⟨a, ha, _⟩ := (mem_highChildren L m t d hlt w z).mp hzw
      obtain ⟨b, hb, _⟩ := (mem_highChildren L m t d hlt v z).mp hzv
      exact hne (put_pair_injective hlt w v a b
        ((mem_generate L m t d (by omega) w).mp hw).1
        ((mem_generate L m t d (by omega) v).mp hv).1 (ha.trans hb.symm)).1

/-- Every generated prefix is itself a zero-completed genuine state. -/
theorem generate_length_le_states (L m t d : ℕ) (hd : d ≤ 2*L) :
    (generate L m t d).length ≤ Fintype.card (States L m t) := by
  classical
  let f : {w // w ∈ (generate L m t d).toFinset} → States L m t :=
    fun w => ⟨w.val, ((mem_generate L m t d hd w.val).mp (List.mem_toFinset.mp w.property)).2⟩
  have hi : Function.Injective f := by
    intro a b h
    apply Subtype.ext
    exact congrArg (fun x : States L m t => x.val) h
  have hc := Fintype.card_le_of_injective f hi
  rw [Fintype.card_coe, List.toFinset_card_of_nodup (generate_nodup L m t d hd)] at hc
  exact hc

/-- Computable star scan; equal to the logical star set. -/
def stars {n : ℕ} (w : Word n) : Finset (Fin n) :=
  Finset.univ.filter (fun i => (w i).val = 5)

def height {n : ℕ} (w : Word n) : ℕ := (stars w).card

theorem stars_eq {n : ℕ} (w : Word n) : stars w = starPositions w := by
  classical
  ext i
  simp [stars, starPositions]

theorem height_eq {n : ℕ} (w : Word n) : height w = starCount w := by
  rw [height, stars_eq, starCount]

def finalStar {n : ℕ} (w : Word n) (h : height w ≠ 0) : Fin n :=
  (stars w).max' (Finset.card_pos.mp (Nat.pos_of_ne_zero h))

theorem finalStar_spec {n : ℕ} (w : Word n) (h : height w ≠ 0) :
    IsLastStar w (finalStar w h) := by
  have hn := Finset.card_pos.mp (Nat.pos_of_ne_zero h)
  refine ⟨?_, ?_⟩
  · have hm := Finset.max'_mem (stars w) hn
    simpa [stars, finalStar] using hm
  · intro j hj
    have hm : j ∈ stars w := by simp [stars, hj]
    exact Fin.le_iff_val_le_val.mp (Finset.le_max' _ _ hm)

/-- Coefficients are actually materialized in the array underlying `Vector`. -/
abbrev Coefficients (R : Type*) (q : ℕ) := Vector R q

def zeroVector {R : Type*} [Zero R] (q : ℕ) : Coefficients R q := Vector.replicate q 0

def lookup {R : Type*} [Zero R] {q n : ℕ}
    (table : Trie (Coefficients R q)) (w : Word n) : Coefficients R q :=
  (table.read (key w)).getD (zeroVector q)

/-- The five child vectors are read and materialized once, before the
coefficient loop adds their entries. The initial zero addition is charged. -/
def addFive {R : Type*} [AddCommMonoid R] {q : ℕ}
    (children : Vector (Coefficients R q) 5) : Coefficients R q :=
  Vector.ofFn (fun j => ∑ a : Fin 5, (children.get a).get j)

def node {R : Type*} [AddCommMonoid R] {L q : ℕ}
    (base : LeafWord (2*L) → Coefficients R q)
    (table : Trie (Coefficients R q)) (w : Word (2*L)) : Coefficients R q :=
  if h : height w = 0 then
    base (baseLeaf w (noStars_of_count_zero w (by simpa [height_eq] using h)))
  else
    let cs : Vector (Coefficients R q) 5 := Vector.ofFn (fun a =>
      lookup table (replace w (finalStar w h) a))
    addFive cs

/-- Batch updates compute their payloads using one fixed snapshot. The
recursive result is a materialized trie, not a function of state queries. -/
def writeBatch {A : Type*} {n : ℕ} (values : Word n → A) :
    Trie A → List (Word n) → Trie A
  | table, [] => table
  | table, w :: ws => writeBatch values (table.write (key w) (values w)) ws

theorem read_writeBatch {A : Type*} {n : ℕ} (values : Word n → A)
    (table : Trie A) (ws : List (Word n)) (w : Word n) :
    (writeBatch values table ws).read (key w) =
      if w ∈ ws then some (values w) else table.read (key w) := by
  induction ws generalizing table with
  | nil => simp [writeBatch]
  | cons v vs ih =>
      rw [writeBatch, ih]
      by_cases hw : w ∈ vs
      · simp [hw]
      · simp only [hw, if_false, List.mem_cons]
        by_cases hv : w = v
        · subst v; simp
        · rw [Trie.read_write_other table (key v) (key w) (values v)
            (fun h => hv (key_injective n h))]
          simp [hv]

def layerWords (L m t k : ℕ) : List (Word (2*L)) :=
  (generate L m t (2*L)).filter (fun w => decide (height w = k))

theorem mem_layerWords (L m t k : ℕ) (w : Word (2*L)) :
    w ∈ layerWords L m t k ↔ Balanced L m t w ∧ Ordered w ∧ starCount w = k := by
  rw [layerWords, List.mem_filter, mem_generate L m t (2*L) (le_refl _)]
  have hp : IsPrefix (2*L) w := by intro i hi; omega
  simp [hp, height_eq, and_assoc]

def runLayer {R : Type*} [AddCommMonoid R] {L m t q : ℕ}
    (base : LeafWord (2*L) → Coefficients R q) (k : ℕ)
    (table : Trie (Coefficients R q)) : Trie (Coefficients R q) :=
  writeBatch (node base table) table (layerWords L m t k)

def execute {R : Type*} [AddCommMonoid R] {L m t q : ℕ}
    (base : LeafWord (2*L) → Coefficients R q) : ℕ → Trie (Coefficients R q)
  | 0 => .empty
  | k+1 => runLayer (m := m) (t := t) base k (execute (m := m) (t := t) base k)

def logicalLeaf {R : Type*} {L q : ℕ}
    (base : LeafWord (2*L) → Coefficients R q) (j : Fin q) : LeafWord (2*L) → R :=
  fun v => (base v).get j

theorem node_correct {R : Type*} [AddCommMonoid R] {L m t q : ℕ}
    (base : LeafWord (2*L) → Coefficients R q)
    (table : Trie (Coefficients R q)) (w : States L m t)
    (hprev : ∀ v : States L m t, starCount v.val < starCount w.val →
      ∀ j : Fin q, (lookup table v.val).get j = boxValue v.val (logicalLeaf base j))
    (j : Fin q) :
    (node base table w.val).get j = boxValue w.val (logicalLeaf base j) := by
  unfold node
  split_ifs with h
  · exact (boxValue_base w.val (noStars_of_count_zero w.val (by simpa [height_eq] using h))
      (logicalLeaf base j)).symm
  · simp only [addFive, Vector.get_ofFn]
    rw [boxValue_expand w.val (logicalLeaf base j) (finalStar w.val h) (finalStar_spec w.val h).1]
    apply Finset.sum_congr rfl
    intro a ha
    exact hprev (child w (finalStar w.val h) (finalStar_spec w.val h) a)
      (starCount_replace_lt _ _ _ (finalStar_spec w.val h).1) j

theorem runLayer_lookup {R : Type*} [AddCommMonoid R] {L m t q : ℕ}
    (base : LeafWord (2*L) → Coefficients R q) (k : ℕ)
    (table : Trie (Coefficients R q)) (w : States L m t) :
    lookup (runLayer (m := m) (t := t) base k table) w.val =
      if starCount w.val = k then node base table w.val else lookup table w.val := by
  unfold lookup runLayer
  rw [read_writeBatch]
  by_cases h : starCount w.val = k
  · have hm := (mem_layerWords L m t k w.val).mpr ⟨w.property.1, w.property.2, h⟩
    simp [hm, h]
  · have hm : w.val ∉ layerWords L m t k := by
      intro hm
      exact h ((mem_layerWords L m t k w.val).mp hm).2.2
    simp [hm, h]

theorem execute_correct_below {R : Type*} [AddCommMonoid R] {L m t q : ℕ}
    (base : LeafWord (2*L) → Coefficients R q) (k : ℕ) :
    ∀ w : States L m t, starCount w.val < k → ∀ j : Fin q,
    (lookup (execute (m := m) (t := t) base k) w.val).get j =
      boxValue w.val (logicalLeaf base j) := by
  induction k with
  | zero => intro w hw; omega
  | succ k ih =>
      intro w hw j
      rw [execute, runLayer_lookup]
      split_ifs with he
      · apply node_correct base (execute (m := m) (t := t) base k) w
        intro v hv jj
        exact ih v (by omega) jj
      · exact ih w (by omega) j

/-- All complete stored coefficient vectors compute the full box sum. -/
theorem execute_complete {R : Type*} [AddCommMonoid R] {L m t q : ℕ}
    (base : LeafWord (2*L) → Coefficients R q) (w : States L m t) (j : Fin q) :
    (lookup (execute (m := m) (t := t) base (2*L+1)) w.val).get j =
      boxValue w.val (logicalLeaf base j) := by
  apply execute_correct_below
  have := starCount_le_length w.val
  omega

/-- The materialized execution refines the earlier finite logical DP. -/
theorem execute_refines_tableAfter {R : Type*} [AddCommMonoid R] {L m t q : ℕ}
    (base : LeafWord (2*L) → Coefficients R q) (w : States L m t) (j : Fin q) :
    (lookup (execute (m := m) (t := t) base (2*L+1)) w.val).get j =
      tableAfter (logicalLeaf base j) (2*L+1) w := by
  rw [execute_complete, tableAfter_complete]

/-- Base callback returns the vector and the work that actually formed it. -/
abbrev BaseResult (R : Type*) (q : ℕ) := Coefficients R q × ℕ

def nodeCounted {R : Type*} [AddCommMonoid R] {L q : ℕ}
    (base : LeafWord (2*L) → BaseResult R q)
    (table : Trie (Coefficients R q)) (w : Word (2*L)) : BaseResult R q :=
  if h : height w = 0 then
    let r := base (baseLeaf w (noStars_of_count_zero w (by simpa [height_eq] using h)))
    (r.1, r.2 + 2*L)
  else
    let reads : Vector (Option (Coefficients R q) × ℕ) 5 := Vector.ofFn (fun a =>
      let r := Trie.readCounted table (key (replace w (finalStar w h) a))
      (r.1, r.2 + 2*L))
    let cs : Vector (Coefficients R q) 5 := Vector.ofFn (fun a =>
      (reads.get a).1.getD (zeroVector q))
    (addFive cs, (∑ a : Fin 5, (reads.get a).2) + 10*q + 2*(2*L))

theorem nodeCounted_value {R : Type*} [AddCommMonoid R] {L q : ℕ}
    (base : LeafWord (2*L) → BaseResult R q)
    (table : Trie (Coefficients R q)) (w : Word (2*L)) :
    (nodeCounted base table w).1 = node (fun v => (base v).1) table w := by
  unfold nodeCounted node
  split_ifs
  · rfl
  · simp only [Vector.get_ofFn, Trie.readCounted_value, lookup]

theorem nodeCounted_work_le {R : Type*} [AddCommMonoid R] {L q : ℕ}
    (base : LeafWord (2*L) → BaseResult R q) (B : ℕ)
    (hb : ∀ v, (base v).2 ≤ B)
    (table : Trie (Coefficients R q)) (w : Word (2*L)) :
    (nodeCounted base table w).2 ≤ B + 5*(2*L+1) + 10*q + 7*(2*L) := by
  unfold nodeCounted
  split_ifs with h
  · have hbase := hb (baseLeaf w (noStars_of_count_zero w (by simpa [height_eq] using h)))
    dsimp only
    omega
  · simp only [Vector.get_ofFn, Trie.readCounted_work, key_length, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    omega

/-- The same batch loop computes each payload once and uses counted trie
updates. The extra `q` pays for writing the full output vector. -/
def writeBatchCounted {R : Type*} {q n : ℕ}
    (values : Word n → BaseResult R q) :
    Trie (Coefficients R q) → List (Word n) → Trie (Coefficients R q) × ℕ
  | table, [] => (table, 0)
  | table, w :: ws =>
      let x := values w
      let wr := table.writeCounted (key w) x.1
      let rest := writeBatchCounted values wr.1 ws
      (rest.1, x.2 + wr.2 + q + n + rest.2)

theorem writeBatchCounted_value {R : Type*} {q n : ℕ}
    (values : Word n → BaseResult R q) (table : Trie (Coefficients R q))
    (ws : List (Word n)) :
    (writeBatchCounted values table ws).1 =
      writeBatch (fun w => (values w).1) table ws := by
  induction ws generalizing table with
  | nil => rfl
  | cons w ws ih => simp [writeBatchCounted, writeBatch, ih]

theorem writeBatchCounted_work_le {R : Type*} {q n : ℕ}
    (values : Word n → BaseResult R q) (B : ℕ)
    (hb : ∀ w, (values w).2 ≤ B)
    (table : Trie (Coefficients R q)) (ws : List (Word n)) :
    (writeBatchCounted values table ws).2 ≤ ws.length * (B + 8*n + 7 + q + n) := by
  induction ws generalizing table with
  | nil => simp [writeBatchCounted]
  | cons w ws ih =>
      simp only [writeBatchCounted, Trie.writeCounted_work, key_length,
        List.length_cons, Nat.succ_mul]
      have h := ih (table.writeCounted (key w) (values w).1).1
      have := hb w
      nlinarith

/-- Joint enumeration and physical-test counter. Each attempted extension
performs three position scans and a scan of all ordered position pairs;
rejected children are included. -/
structure Generated (L : ℕ) where
  words : List (Word (2*L))
  extensions : ℕ
  tests : ℕ

def generateCounted (L m t : ℕ) : ℕ → Generated L
  | 0 => ⟨[zeroWord (2*L)], 0, 0⟩
  | d+1 =>
      let prev := generateCounted L m t d
      if hd : d < 2*L then
        { words := prev.words.flatMap (highChildren L m t d hd)
          extensions := prev.extensions + 6*prev.words.length
          tests := prev.tests + (3*(2*L)+(2*L)^2)*(6*prev.words.length) }
      else { words := [], extensions := prev.extensions, tests := prev.tests }

theorem generateCounted_words (L m t d : ℕ) :
    (generateCounted L m t d).words = generate L m t d := by
  induction d with
  | zero => rfl
  | succ d ih => simp only [generateCounted, generate]; split <;> simp [ih]

theorem generateCounted_tests (L m t d : ℕ) :
    (generateCounted L m t d).tests =
      (3*(2*L)+(2*L)^2)*(generateCounted L m t d).extensions := by
  induction d with
  | zero => simp [generateCounted]
  | succ d ih =>
      simp only [generateCounted]
      split
      · simp only [ih]; ring
      · exact ih

theorem generateCounted_extensions_le (L m t d : ℕ) (hd : d ≤ 2*L) :
    (generateCounted L m t d).extensions ≤ 6*d*Fintype.card (States L m t) := by
  induction d with
  | zero => simp [generateCounted]
  | succ d ih =>
      have hlt : d < 2*L := by omega
      simp only [generateCounted, dif_pos hlt, generateCounted_words]
      have h := ih (by omega)
      have hlen := generate_length_le_states L m t d (by omega)
      nlinarith

theorem enumeration_tests_le_bases (L m t : ℕ) :
    (generateCounted L m t (2*L)).tests ≤
      (3*(2*L)+(2*L)^2) * (6*(2*L)) * (2*L+1) * Fintype.card (BaseStates L m t) := by
  rw [generateCounted_tests]
  calc
    _ ≤ (3*(2*L)+(2*L)^2) * (6*(2*L)*Fintype.card (States L m t)) :=
      Nat.mul_le_mul_left _ (generateCounted_extensions_le L m t (2*L) (le_refl _))
    _ ≤ _ := by
      have h := Nat.mul_le_mul_left ((3*(2*L)+(2*L)^2)*(6*(2*L)))
        (stateCount_le_baseCount L m t)
      simpa [Nat.mul_assoc] using h

/-- A layer jointly constructs its state list, scans its star counts,
forms each node, and performs every actual trie update. -/
def runLayerCounted {R : Type*} [AddCommMonoid R] {L m t q : ℕ}
    (base : LeafWord (2*L) → BaseResult R q) (k : ℕ)
    (table : Trie (Coefficients R q)) : Trie (Coefficients R q) × ℕ :=
  let gen := generateCounted L m t (2*L)
  let ws := gen.words.filter (fun w => decide (height w = k))
  let batch := writeBatchCounted (nodeCounted base table) table ws
  (batch.1, gen.tests + gen.extensions + (2*L+1)*gen.words.length + batch.2)

theorem runLayerCounted_value {R : Type*} [AddCommMonoid R] {L m t q : ℕ}
    (base : LeafWord (2*L) → BaseResult R q) (k : ℕ)
    (table : Trie (Coefficients R q)) :
    (runLayerCounted (m := m) (t := t) base k table).1 =
      runLayer (m := m) (t := t) (fun v => (base v).1) k table := by
  simp only [runLayerCounted, writeBatchCounted_value, generateCounted_words,
    nodeCounted_value, runLayer, layerWords]

/-- Cost includes physical tests, state-layer scans, key pointer operations,
all coefficient reads/additions/writes, and the supplied base work. -/
def layerFactor (L q B : ℕ) : ℕ :=
  ((3*(2*L)+(2*L)^2)+1)*(6*(2*L)) + (2*L+1) +
    (B + 5*(2*L+1) + 10*q + 7*(2*L) + 8*(2*L) + 7 + q + 2*L)

theorem runLayerCounted_work_le {R : Type*} [AddCommMonoid R] {L m t q : ℕ}
    (base : LeafWord (2*L) → BaseResult R q) (B : ℕ)
    (hb : ∀ v, (base v).2 ≤ B) (k : ℕ)
    (table : Trie (Coefficients R q)) :
    (runLayerCounted (m := m) (t := t) base k table).2 ≤
      layerFactor L q B * Fintype.card (States L m t) := by
  simp only [runLayerCounted, generateCounted_tests, generateCounted_words]
  have he := generateCounted_extensions_le L m t (2*L) (le_refl _)
  have hl := generate_length_le_states L m t (2*L) (le_refl _)
  have hf := List.length_filter_le (fun w : Word (2*L) => decide (height w = k))
    (generate L m t (2*L))
  have hbch := writeBatchCounted_work_le (nodeCounted base table)
    (B + 5*(2*L+1) + 10*q + 7*(2*L)) (nodeCounted_work_le base B hb table) table
    ((generate L m t (2*L)).filter (fun w => decide (height w = k)))
  have hbatch := hbch.trans (Nat.mul_le_mul_right _ (hf.trans hl))
  have htests := Nat.mul_le_mul_left (3*(2*L)+(2*L)^2) he
  have hscan := Nat.mul_le_mul_left (2*L+1) hl
  unfold layerFactor
  nlinarith

def executeCounted {R : Type*} [AddCommMonoid R] {L m t q : ℕ}
    (base : LeafWord (2*L) → BaseResult R q) : ℕ → Trie (Coefficients R q) × ℕ
  | 0 => (.empty, 0)
  | k+1 =>
      let previous := executeCounted (m := m) (t := t) base k
      let next := runLayerCounted (m := m) (t := t) base k previous.1
      (next.1, previous.2 + next.2)

theorem executeCounted_value {R : Type*} [AddCommMonoid R] {L m t q : ℕ}
    (base : LeafWord (2*L) → BaseResult R q) (k : ℕ) :
    (executeCounted (m := m) (t := t) base k).1 =
      execute (m := m) (t := t) (fun v => (base v).1) k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [executeCounted, runLayerCounted_value, ih, execute]

theorem executeCounted_work_le {R : Type*} [AddCommMonoid R] {L m t q : ℕ}
    (base : LeafWord (2*L) → BaseResult R q) (B : ℕ)
    (hb : ∀ v, (base v).2 ≤ B) (k : ℕ) :
    (executeCounted (m := m) (t := t) base k).2 ≤
      k * layerFactor L q B * Fintype.card (States L m t) := by
  induction k with
  | zero => simp [executeCounted]
  | succ k ih =>
      simp only [executeCounted]
      have hn := runLayerCounted_work_le (m := m) (t := t) base B hb k
        (executeCounted (m := m) (t := t) base k).1
      nlinarith

/-- Complete execution work is polynomial in `L`, linear in the base
callback budget and coefficient width, times the actual balanced base count. -/
theorem executeCounted_work_le_bases {R : Type*} [AddCommMonoid R] {L m t q : ℕ}
    (base : LeafWord (2*L) → BaseResult R q) (B : ℕ)
    (hb : ∀ v, (base v).2 ≤ B) :
    (executeCounted (m := m) (t := t) base (2*L+1)).2 ≤
      (2*L+1)^2 * layerFactor L q B * Fintype.card (BaseStates L m t) := by
  calc
    _ ≤ (2*L+1)*layerFactor L q B*Fintype.card (States L m t) :=
      executeCounted_work_le base B hb (2*L+1)
    _ ≤ _ := by
      have h := Nat.mul_le_mul_left ((2*L+1)*layerFactor L q B)
        (stateCount_le_baseCount L m t)
      nlinarith

/-- Correctness and all finite execution counters concern the same returned
materialized table. No recursive DP call occurs during a dictionary lookup. -/
theorem executeCounted_complete {R : Type*} [AddCommMonoid R] {L m t q : ℕ}
    (base : LeafWord (2*L) → BaseResult R q) (w : States L m t) (j : Fin q) :
    (lookup (executeCounted (m := m) (t := t) base (2*L+1)).1 w.val).get j =
      boxValue w.val (logicalLeaf (fun v => (base v).1) j) := by
  rw [executeCounted_value]
  exact execute_complete _ w j

/-- Embed a star-free five-letter leaf as a physical six-letter word. -/
def leafKey {n : ℕ} (v : LeafWord n) : Word n :=
  fun i => ⟨(v i).val, by have := (v i).isLt; omega⟩

@[simp] theorem leafKey_noStars {n : ℕ} (v : LeafWord n) (i : Fin n) :
    (leafKey v i).val ≠ 5 := by have := (v i).isLt; simp only [leafKey]; omega

/-- A compatible leaf never has more private support than its box. -/
theorem compatible_specialCount_le {n : ℕ} (w : Word n) (v : LeafWord n)
    (hc : Compatible w v) (region : Fin n → Prop) :
    specialCount (leafKey v) region ≤ specialCount w region := by
  classical
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  refine ⟨hi.1, ?_⟩
  have hvi : 4 ≤ (v i).val := hi.2
  by_contra hn
  have hlt : (w i).val < 4 := by omega
  have he := hc i (by omega)
  omega

theorem compatible_leaf_balanced {L m t : ℕ} (w : States L m t) (v : LeafWord (2*L))
    (hc : Compatible w.val v) : Balanced L m t (leafKey v) :=
  ⟨(compatible_specialCount_le w.val v hc _).trans w.property.1.1,
    (compatible_specialCount_le w.val v hc _).trans w.property.1.2.1,
    (compatible_specialCount_le w.val v hc _).trans w.property.1.2.2⟩

def guardTests (L : ℕ) : ℕ := 3*(2*L)+(2*L)^2

def guardedBase {R : Type*} [Zero R] {L m t q : ℕ}
    (base : BaseStates L m t → BaseResult R q) (v : LeafWord (2*L)) : BaseResult R q :=
  if h : highTest L m t (leafKey v) = true then
    let r := base ⟨leafKey v, ((highTest_eq_true L m t _).mp h).1, leafKey_noStars v⟩
    (r.1, r.2 + guardTests L)
  else (zeroVector q, q + guardTests L)

/-- The total callback uses only true capped base addresses. No value of a
source transform at an off-cap leaf is required. -/
theorem guardedBase_work_le {R : Type*} [Zero R] {L m t q : ℕ}
    (base : BaseStates L m t → BaseResult R q) (B : ℕ)
    (hb : ∀ v, (base v).2 ≤ B) (hq : q ≤ B) (v : LeafWord (2*L)) :
    (guardedBase base v).2 ≤ B + guardTests L := by
  unfold guardedBase
  split_ifs
  · exact Nat.add_le_add_right (hb _) _
  · exact Nat.add_le_add_right hq _

theorem guardedBase_agrees_on_compatible {R : Type*} [Zero R] {L m t q : ℕ}
    (base : BaseStates L m t → BaseResult R q)
    (global : LeafWord (2*L) → Coefficients R q)
    (hb : ∀ b : BaseStates L m t, (base b).1 = global (baseLeaf b.val b.property.2))
    (w : States L m t) (v : LeafWord (2*L)) (hc : Compatible w.val v) :
    (guardedBase base v).1 = global v := by
  have hbal := compatible_leaf_balanced w v hc
  have ho : Ordered (leafKey v) := by
    intro i j hi
    exact False.elim (leafKey_noStars v i hi)
  have ht := (highTest_eq_true L m t (leafKey v)).mpr ⟨hbal, ho⟩
  rw [guardedBase, dif_pos ht]
  dsimp only
  rw [hb]
  congr 1

/-- The guarded callback computes the complete intended global-leaf box,
although it reads only retained private bases. -/
theorem guarded_execute_complete {R : Type*} [AddCommMonoid R] {L m t q : ℕ}
    (base : BaseStates L m t → BaseResult R q)
    (global : LeafWord (2*L) → Coefficients R q)
    (hb : ∀ b : BaseStates L m t, (base b).1 = global (baseLeaf b.val b.property.2))
    (w : States L m t) (j : Fin q) :
    (lookup (executeCounted (m := m) (t := t) (guardedBase base) (2*L+1)).1 w.val).get j =
      boxValue w.val (logicalLeaf global j) := by
  rw [executeCounted_complete]
  unfold boxValue
  apply Finset.sum_congr rfl
  intro v hv
  by_cases hc : Compatible w.val v
  · simp only [hc, if_true, logicalLeaf]
    rw [guardedBase_agrees_on_compatible base global hb w v hc]
  · simp [hc]

/-- Every completed state address contains a stored vector, independently
of its coefficient values (including all-zero vectors and `q = 0`). -/
theorem execute_stores_below {R : Type*} [AddCommMonoid R] {L m t q : ℕ}
    (base : LeafWord (2*L) → Coefficients R q) (k : ℕ) :
    ∀ w : States L m t, starCount w.val < k →
      ∃ v, (execute (m := m) (t := t) base k).read (key w.val) = some v := by
  induction k with
  | zero => intro w hw; omega
  | succ k ih =>
      intro w hw
      rw [execute, runLayer, read_writeBatch]
      by_cases he : starCount w.val = k
      · have hm := (mem_layerWords L m t k w.val).mpr ⟨w.property.1, w.property.2, he⟩
        simp [hm]
      · have hm : w.val ∉ layerWords L m t k := by
          intro hm
          exact he ((mem_layerWords L m t k w.val).mp hm).2.2
        simp only [hm, if_false]
        exact ih w (by omega)

def readCoefficient {R : Type*} {q n : ℕ}
    (table : Trie (Coefficients R q)) (w : Word n) (j : Fin q) : Option R :=
  (table.read (key w)).map (fun v => v.get j)

/-- One coefficient query reads its key path and one array coefficient.
It does not scan, multiply, or allocate the other `q-1` coefficients. -/
def readCoefficientCounted {R : Type*} {q n : ℕ}
    (table : Trie (Coefficients R q)) (w : Word n) (j : Fin q) : Option R × ℕ :=
  let r := table.readCounted (key w)
  (r.1.map (fun v => v.get j), r.2 + n + 1)

@[simp] theorem readCoefficientCounted_value {R : Type*} {q n : ℕ}
    (table : Trie (Coefficients R q)) (w : Word n) (j : Fin q) :
    (readCoefficientCounted table w j).1 = readCoefficient table w j := by
  simp [readCoefficientCounted, readCoefficient]

@[simp] theorem readCoefficientCounted_work {R : Type*} {q n : ℕ}
    (table : Trie (Coefficients R q)) (w : Word n) (j : Fin q) :
    (readCoefficientCounted table w j).2 = 2*n+2 := by
  simp [readCoefficientCounted]; omega

theorem readCoefficient_execute {R : Type*} [AddCommMonoid R] {L m t q : ℕ}
    (base : LeafWord (2*L) → BaseResult R q) (w : States L m t) (j : Fin q) :
    readCoefficient (executeCounted (m := m) (t := t) base (2*L+1)).1 w.val j =
      some (boxValue w.val (logicalLeaf (fun v => (base v).1) j)) := by
  rw [executeCounted_value]
  obtain ⟨v, hv⟩ := execute_stores_below (m := m) (t := t) (fun v => (base v).1)
    (2*L+1) w (by have := starCount_le_length w.val; omega)
  unfold readCoefficient
  rw [hv]
  simp only [Option.map_some]
  congr 1
  have he := execute_complete (m := m) (t := t) (fun v => (base v).1) w j
  simpa only [lookup, hv, Option.getD_some] using he

/-- The materialized execution retains the source's entropy saving. Every
additional array-trie, enumeration, and coefficient-loop factor is explicit. -/
theorem rounded_executeCounted_work {R : Type*} [AddCommMonoid R]
    (c theta : ℝ) (m q B : ℕ)
    (hc : 5 < c) (ht0 : 0 < theta) (ht1 : theta < 1/2) (hm : 0 < m)
    (base : LeafWord (2*Nat.ceil (c*(m:ℝ))) → BaseResult R q)
    (hb : ∀ v, (base v).2 ≤ B) :
    let L := Nat.ceil (c*(m:ℝ))
    let t := Nat.ceil (2*theta*(m:ℝ))
    ((executeCounted (m := m) (t := t) base (2*L+1)).2 : ℝ) ≤
      (((2*L+1)^2 * layerFactor L q B : ℕ) : ℝ) *
        ((L+1:ℝ)^4 * Real.exp (HighBoxEntropy.roundingConstant c theta) *
          (EntropyBounds.gridCount L m)^2 * ((4:ℝ)^m)^(-HighBoxEntropy.boxSaving c theta)) := by
  let L := Nat.ceil (c*(m:ℝ))
  let t := Nat.ceil (2*theta*(m:ℝ))
  have hfinite : ((executeCounted (m := m) (t := t) base (2*L+1)).2 : ℝ) ≤
      (((2*L+1)^2 * layerFactor L q B : ℕ) : ℝ) *
        (Fintype.card (BaseStates L m t) : ℝ) := by
    exact_mod_cast executeCounted_work_le_bases (m := m) (t := t) base B hb
  have hentropy := HighBoxEntropy.rounded_totalCappedLeaves_polynomial c theta m hc ht0 ht1 hm
  have hcard : Fintype.card (BaseStates L m t) =
      Fintype.card (CacheCardinality.TotalCappedLeaves L m (2*m-t)) :=
    Fintype.card_congr (baseStatesEquivTotalCapped L m t)
  rw [hcard] at hfinite
  exact hfinite.trans (mul_le_mul_of_nonneg_left hentropy (by positivity))

#print axioms Trie.read_write_same
#print axioms Trie.read_write_other
#print axioms generate_length_le_states
#print axioms execute_complete
#print axioms execute_refines_tableAfter
#print axioms enumeration_tests_le_bases
#print axioms executeCounted_work_le_bases
#print axioms executeCounted_complete
#print axioms guarded_execute_complete
#print axioms readCoefficient_execute
#print axioms readCoefficientCounted_work
#print axioms rounded_executeCounted_work

end ThinMatrix.StoredHighDP
