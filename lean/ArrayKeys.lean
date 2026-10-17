import StoredHighDP

/-!
# Materialized physical keys and finite address bounds

The concrete keys are array-backed fixed-length vectors. Their coordinate
reads and updates contain no application of an arbitrary `Word` function.
The forgetful map to `Word` is used only to state refinement theorems.
Direct capped generation operates on vectors and refines the functional
high-state specification. Scan counters count actual bounded array reads
and predicate visits; compilation of these loops to word RAM is separate.
-/
namespace ThinMatrix.ArrayKeys

open CacheBounds HighBoxDP
open scoped BigOperators

abbrev Key (n : ℕ) := Vector Label n

def toWord {n : ℕ} (a : Key n) : Word n := fun i => a.get i

def materialize {n : ℕ} (w : Word n) : Key n := Vector.ofFn w

@[simp] theorem toWord_materialize {n : ℕ} (w : Word n) : toWord (materialize w) = w := by
  funext i
  simp [toWord, materialize]

theorem toWord_injective (n : ℕ) : Function.Injective (@toWord n) := by
  intro a b hab
  apply Vector.ext
  intro i hi
  exact congrFun hab ⟨i,hi⟩

@[simp] theorem materialize_toWord {n : ℕ} (a : Key n) : materialize (toWord a) = a := by
  apply toWord_injective n
  simp

def zero (n : ℕ) : Key n := Vector.replicate n 0

@[simp] theorem toWord_zero (n : ℕ) : toWord (zero n) = CappedEnumeration.zeroWord n := by
  funext i
  simp [toWord, zero, CappedEnumeration.zeroWord]

/-- Array update copies at most `n` coordinates in the persistent case. -/
def put {n : ℕ} (a : Key n) (i : Fin n) (v : Label) : Key n := a.set i.val v i.isLt

@[simp] theorem toWord_put {n : ℕ} (a : Key n) (i : Fin n) (v : Label) :
    toWord (put a i v) = Function.update (toWord a) i v := by
  funext j
  by_cases h : j = i
  · subst j
    rw [Function.update_self]
    change (a.set i.val v i.isLt)[i.val] = v
    exact Vector.getElem_set_self i.isLt
  · have hv : i.val ≠ j.val := by intro he; exact h (Fin.ext he.symm)
    simp only [Function.update_of_ne h]
    change (a.set i.val v i.isLt)[j.val] = a[j.val]
    exact Vector.getElem_set_ne i.isLt j.isLt hv

/-- Forgetting a suffix is one bounded array construction. -/
def forget {n : ℕ} (d : ℕ) (a : Key n) : Key n :=
  Vector.ofFn (fun i => if i.val < d then a.get i else 0)

@[simp] theorem toWord_forget {n : ℕ} (d : ℕ) (a : Key n) :
    toWord (forget d a) = trimWord d (toWord a) := by
  funext i
  simp [toWord, forget, trimWord]

/-- A literal array-coordinate scan. -/
def count {n : ℕ} (a : Key n) (p : Fin n → Label → Bool) : ℕ :=
  ((List.finRange n).filter (fun i => p i (a.get i))).length

@[simp] theorem count_eq {n : ℕ} (a : Key n) (p : Fin n → Label → Bool) :
    count a p = CappedEnumeration.countBool (toWord a) p := rfl

/-- Its counter is accumulated in the same scan recursion. -/
def scan {n : ℕ} (a : Key n) (p : Fin n → Label → Bool) : List (Fin n) → ℕ × ℕ
  | [] => (0,0)
  | i :: is =>
      let r := scan a p is
      (if p i (a.get i) then r.1+1 else r.1, r.2+1)

theorem scan_value {n : ℕ} (a : Key n) (p : Fin n → Label → Bool) (is : List (Fin n)) :
    (scan a p is).1 = (is.filter (fun i => p i (a.get i))).length := by
  induction is with
  | nil => rfl
  | cons i is ih =>
      simp only [scan, List.filter_cons]
      split <;> simp [ih]

@[simp] theorem scan_work {n : ℕ} (a : Key n) (p : Fin n → Label → Bool) (is : List (Fin n)) :
    (scan a p is).2 = is.length := by
  induction is with
  | nil => rfl
  | cons i is ih => simp [scan, ih]

/-- The orderedness test reads two array entries at each ordered pair. -/
def orderScan {n : ℕ} (a : Key n) : List (Fin n × Fin n) → Bool × ℕ
  | [] => (true,0)
  | (i,j) :: is =>
      let r := orderScan a is
      (decide ((a.get i).val = 5 → (a.get j).val = 4 → i.val < j.val) && r.1,
        r.2+2)

def pairs (n : ℕ) : List (Fin n × Fin n) :=
  (List.finRange n).flatMap (fun i => (List.finRange n).map (fun j => (i,j)))

@[simp] theorem pairs_length (n : ℕ) : (pairs n).length = n*n := by
  simp [pairs, List.length_flatMap, List.sum_replicate]

theorem orderScan_value {n : ℕ} (a : Key n) (is : List (Fin n × Fin n)) :
    (orderScan a is).1 = true ↔
      ∀ ij ∈ is, (a.get ij.1).val = 5 → (a.get ij.2).val = 4 → ij.1.val < ij.2.val := by
  induction is with
  | nil => simp [orderScan]
  | cons ij is ih =>
      rcases ij with ⟨i,j⟩
      rw [orderScan, Bool.and_eq_true, decide_eq_true_eq, ih]
      simp only [List.mem_cons]
      aesop

@[simp] theorem orderScan_work {n : ℕ} (a : Key n) (is : List (Fin n × Fin n)) :
    (orderScan a is).2 = 2*is.length := by
  induction is with
  | nil => rfl
  | cons ij is ih => rcases ij with ⟨i,j⟩; simp [orderScan, ih]; omega

/-- All three cap counts and the physical orderedness test are executable
bounded scans over the materialized key. -/
def highTest (L m t : ℕ) (a : Key (2*L)) : Bool × ℕ :=
  let left := scan a (fun i v => decide (i.val < L ∧ 4 ≤ v.val)) (List.finRange (2*L))
  let right := scan a (fun i v => decide (L ≤ i.val ∧ 4 ≤ v.val)) (List.finRange (2*L))
  let total := scan a (fun _ v => decide (4 ≤ v.val)) (List.finRange (2*L))
  let order := orderScan a (pairs (2*L))
  (decide (left.1 ≤ m) && decide (right.1 ≤ m) && decide (total.1 ≤ 2*m-t) && order.1,
    left.2 + right.2 + total.2 + order.2)

theorem highTest_value (L m t : ℕ) (a : Key (2*L)) :
    (highTest L m t a).1 = true ↔ Balanced L m t (toWord a) ∧ Ordered (toWord a) := by
  have hs (p : Fin (2*L) → Label → Bool) :
      (scan a p (List.finRange (2*L))).1 = CappedEnumeration.countBool (toWord a) p := by
    exact scan_value a p _
  have ho : (orderScan a (pairs (2*L))).1 = true ↔ Ordered (toWord a) := by
    rw [orderScan_value]
    simp [pairs, Ordered, toWord]
  simp only [highTest, Bool.and_eq_true, decide_eq_true_eq, hs, ho]
  have hh := StoredHighDP.highTest_eq_true L m t (toWord a)
  simp only [StoredHighDP.highTest, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true, List.mem_finRange, true_implies] at hh
  exact hh

@[simp] theorem highTest_work (L m t : ℕ) (a : Key (2*L)) :
    (highTest L m t a).2 = 3*(2*L)+2*(2*L)^2 := by
  simp [highTest, pow_two]
  omega

/-- Each vector child is copied and tested before it is retained. -/
def children (L m t d : ℕ) (hd : d < 2*L) (a : Key (2*L)) : List (Key (2*L)) :=
  ((List.finRange 6).map (fun v => put a ⟨d,hd⟩ v)).filter (fun v => (highTest L m t v).1)

theorem children_refine (L m t d : ℕ) (hd : d < 2*L) (a : Key (2*L)) :
    (children L m t d hd a).map toWord = StoredHighDP.highChildren L m t d hd (toWord a) := by
  have ht (v : Key (2*L)) : (highTest L m t v).1 = StoredHighDP.highTest L m t (toWord v) := by
    apply Bool.eq_iff_iff.mpr
    rw [highTest_value, StoredHighDP.highTest_eq_true]
  simp only [children, ht]
  change List.map toWord (List.filter (StoredHighDP.highTest L m t ∘ toWord)
    ((List.finRange 6).map (fun v => put a ⟨d,hd⟩ v))) = _
  rw [← List.filter_map, List.map_map]
  simp only [StoredHighDP.highChildren, Function.comp_def, toWord_put]
  rfl

def generate (L m t : ℕ) : ℕ → List (Key (2*L))
  | 0 => [zero (2*L)]
  | d+1 => if hd : d < 2*L then (generate L m t d).flatMap (children L m t d hd) else []

theorem generate_refine (L m t d : ℕ) :
    (generate L m t d).map toWord = StoredHighDP.generate L m t d := by
  induction d with
  | zero => simp [generate, StoredHighDP.generate]
  | succ d ih =>
      simp only [generate, StoredHighDP.generate]
      split
      · rw [List.map_flatMap]
        simp only [children_refine]
        rw [← List.flatMap_map, ih]
      · rfl

@[simp] theorem generate_length (L m t d : ℕ) :
    (generate L m t d).length = (StoredHighDP.generate L m t d).length := by
  rw [← generate_refine L m t d, List.length_map]

theorem generate_nodup (L m t d : ℕ) (hd : d ≤ 2*L) :
    (generate L m t d).Nodup :=
  (List.nodup_map_iff (toWord_injective (2*L))).mp
    (by rw [generate_refine]; exact StoredHighDP.generate_nodup L m t d hd)

theorem mem_generate (L m t d : ℕ) (hd : d ≤ 2*L) (a : Key (2*L)) :
    a ∈ generate L m t d ↔
      IsPrefix d (toWord a) ∧ Balanced L m t (toWord a) ∧ Ordered (toWord a) := by
  rw [← StoredHighDP.mem_generate L m t d hd (toWord a), ← generate_refine]
  exact (List.mem_map_of_injective (toWord_injective (2*L))).symm

/-- The materialized state generator has the same actual capped-family
bound; it does not allocate the Cartesian family of all keys. -/
theorem generate_length_le_bases (L m t d : ℕ) (hd : d ≤ 2*L) :
    (generate L m t d).length ≤ (2*L+1)*Fintype.card (BaseStates L m t) := by
  rw [generate_length]
  exact (StoredHighDP.generate_length_le_states L m t d hd).trans (stateCount_le_baseCount L m t)

/-- Generic materialized generator, also usable by the channel cache and
the five-label HIGH base encoder. -/
def generateKeys {n : ℕ} (alphabet : List Label) (test : Key n → Bool) : ℕ → List (Key n)
  | 0 => [zero n]
  | d+1 => if hd : d < n then
      (generateKeys alphabet test d).flatMap (fun a =>
        (alphabet.map (fun v => put a ⟨d,hd⟩ v)).filter test) else []

/-- Functional words occur only in the denotational specification. -/
def generateWords {n : ℕ} (alphabet : List Label) (test : Word n → Bool) : ℕ → List (Word n)
  | 0 => [CappedEnumeration.zeroWord n]
  | d+1 => if hd : d < n then
      (generateWords alphabet test d).flatMap (fun w =>
        (alphabet.map (fun v => Function.update w ⟨d,hd⟩ v)).filter test) else []

theorem generateKeys_refine {n : ℕ} (alphabet : List Label)
    (test : Key n → Bool) (spec : Word n → Bool)
    (ht : ∀ a, test a = spec (toWord a)) (d : ℕ) :
    (generateKeys alphabet test d).map toWord = generateWords alphabet spec d := by
  induction d with
  | zero => simp [generateKeys, generateWords]
  | succ d ih =>
      simp only [generateKeys, generateWords]
      split
      · rw [List.map_flatMap]
        have hc (a : Key n) :
            ((alphabet.map (fun v => put a ⟨d,by assumption⟩ v)).filter test).map toWord =
              (alphabet.map (fun v => Function.update (toWord a) ⟨d,by assumption⟩ v)).filter spec := by
          have htf : test = spec ∘ toWord := funext ht
          rw [htf]
          change List.map toWord (List.filter (spec ∘ toWord) _) = _
          rw [← List.filter_map, List.map_map]
          simp only [Function.comp_def, toWord_put]
        simp only [hc]
        simpa only [List.flatMap_map] using congrArg
          (List.flatMap (fun w => (alphabet.map (fun v => Function.update w ⟨d,by assumption⟩ v)).filter spec)) ih
      · rfl

/-- Computable channel-cache caps on materialized keys. -/
def cacheTest (L m t : ℕ) (a : Key (2*L)) : Bool × ℕ :=
  let left := scan a (fun i v => decide (i.val < L ∧ 4 ≤ v.val)) (List.finRange (2*L))
  let right := scan a (fun i v => decide (L ≤ i.val ∧ 4 ≤ v.val)) (List.finRange (2*L))
  let channel := scan a (fun _ v => decide (v.val = 5)) (List.finRange (2*L))
  (decide (left.1 ≤ m) && decide (right.1 ≤ m) && decide (channel.1 ≤ t),
    left.2+right.2+channel.2)

theorem cacheTest_refine (L m t : ℕ) (a : Key (2*L)) :
    (cacheTest L m t a).1 = CappedEnumeration.capTest L m t (toWord a) := by
  simp only [cacheTest, scan_value, CappedEnumeration.capTest, CappedEnumeration.countBool, toWord]
  rfl

@[simp] theorem cacheTest_work (L m t : ℕ) (a : Key (2*L)) :
    (cacheTest L m t a).2 = 3*(2*L) := by simp [cacheTest]; omega

def cacheGenerate (L m t : ℕ) : ℕ → List (Key (2*L)) :=
  generateKeys (List.finRange 6) (fun a => (cacheTest L m t a).1)

theorem cacheGenerate_refine (L m t d : ℕ) :
    (cacheGenerate L m t d).map toWord = CappedEnumeration.generate L m t d := by
  rw [cacheGenerate, generateKeys_refine _ _ _ (cacheTest_refine L m t)]
  induction d with
  | zero => rfl
  | succ d ih =>
      simp only [generateWords, CappedEnumeration.generate]
      split
      · rw [ih]
        rfl
      · rfl

/-- HIGH bases have the balanced total cap and no star letters. -/
def baseTest (L m t : ℕ) (a : Key (2*L)) : Bool × ℕ :=
  let left := scan a (fun i v => decide (i.val < L ∧ 4 ≤ v.val)) (List.finRange (2*L))
  let right := scan a (fun i v => decide (L ≤ i.val ∧ 4 ≤ v.val)) (List.finRange (2*L))
  let total := scan a (fun _ v => decide (4 ≤ v.val)) (List.finRange (2*L))
  let stars := scan a (fun _ v => decide (v.val = 5)) (List.finRange (2*L))
  (decide (left.1 ≤ m) && decide (right.1 ≤ m) && decide (total.1 ≤ 2*m-t) && decide (stars.1 = 0),
    left.2+right.2+total.2+stars.2)

theorem baseTest_value (L m t : ℕ) (a : Key (2*L)) :
    (baseTest L m t a).1 = true ↔
      Balanced L m t (toWord a) ∧ ∀ i, (toWord a i).val ≠ 5 := by
  have hs (p : Fin (2*L) → Label → Bool) :
      (scan a p (List.finRange (2*L))).1 = CappedEnumeration.countBool (toWord a) p :=
    scan_value a p _
  have hstar : CappedEnumeration.countBool (toWord a) (fun _ v => decide (v.val = 5)) =
      starCount (toWord a) := by
    rw [CappedEnumeration.countBool_eq]
    simp [countPositions, starCount, starPositions]
  have hnostar : starCount (toWord a) = 0 ↔ ∀ i, (toWord a i).val ≠ 5 := by
    constructor
    · exact noStars_of_count_zero _
    · intro h
      simp [starCount, starPositions, h]
  simp only [baseTest, Bool.and_eq_true, decide_eq_true_eq, hs, hstar, hnostar]
  have hc (p : Fin (2*L) → Label → Prop) (dp : ∀ i v, Decidable (p i v)) :
      CappedEnumeration.countBool (toWord a) (fun i v => @decide (p i v) (dp i v)) =
        countPositions (toWord a) p := by
    rw [CappedEnumeration.countBool_eq]
    simp only [decide_eq_true_eq]
  rw [hc (fun i v => i.val < L ∧ 4 ≤ v.val) (fun i v => inferInstance),
    hc (fun i v => L ≤ i.val ∧ 4 ≤ v.val) (fun i v => inferInstance),
    hc (fun _ v => 4 ≤ v.val) (fun i v => inferInstance)]
  simp only [HighBoxDP.Balanced, specialCount, countPositions, true_and, and_assoc]

@[simp] theorem baseTest_work (L m t : ℕ) (a : Key (2*L)) :
    (baseTest L m t a).2 = 4*(2*L) := by simp [baseTest]; omega

def baseGenerate (L m t : ℕ) : ℕ → List (Key (2*L)) :=
  generateKeys ((List.finRange 5).map Fin.castSucc) (fun a => (baseTest L m t a).1)

/-- Direct array traversal supplies trie keys without evaluating a Word. -/
def digits {n : ℕ} (a : Key n) : List Label := a.toList

@[simp] theorem digits_length {n : ℕ} (a : Key n) : (digits a).length = n := by simp [digits]

theorem digits_refine {n : ℕ} (a : Key n) : digits a = StoredHighDP.key (toWord a) := by
  calc
    digits a = (Vector.ofFn (toWord a)).toList :=
      congrArg Vector.toList (materialize_toWord a).symm
    _ = List.ofFn (toWord a) := Vector.toList_ofFn
    _ = StoredHighDP.key (toWord a) := List.ofFn_eq_map

def read {A : Type*} {n : ℕ} (table : StoredHighDP.Trie A) (a : Key n) : Option A × ℕ :=
  let r := table.readCounted (digits a)
  (r.1, r.2+n)

@[simp] theorem read_value {A : Type*} {n : ℕ} (table : StoredHighDP.Trie A) (a : Key n) :
    (read table a).1 = table.read (StoredHighDP.key (toWord a)) := by
  simp [read, digits_refine]

@[simp] theorem read_work {A : Type*} {n : ℕ} (table : StoredHighDP.Trie A) (a : Key n) :
    (read table a).2 = 2*n+1 := by simp [read]; omega

def write {A : Type*} {n : ℕ} (table : StoredHighDP.Trie A) (a : Key n) (value : A) :
    StoredHighDP.Trie A × ℕ :=
  let r := table.writeCounted (digits a) value
  (r.1, r.2+n)

@[simp] theorem write_value {A : Type*} {n : ℕ} (table : StoredHighDP.Trie A) (a : Key n) (value : A) :
    (write table a value).1 = table.write (StoredHighDP.key (toWord a)) value := by
  simp [write, digits_refine]

@[simp] theorem write_work {A : Type*} {n : ℕ} (table : StoredHighDP.Trie A) (a : Key n) (value : A) :
    (write table a value).2 = 9*n+7 := by simp [write]; omega

/-- An explicit radix-six address code, computed by a linear digit loop. -/
def pack : List Label → ℕ
  | [] => 0
  | a :: as => a.val + 6*pack as

theorem pack_lt (as : List Label) : pack as < 6^as.length := by
  induction as with
  | nil => simp [pack]
  | cons a as ih =>
      simp only [pack, List.length_cons, pow_succ]
      have := a.isLt
      nlinarith

def address {n : ℕ} (a : Key n) : ℕ := pack (digits a)

theorem address_lt {n : ℕ} (a : Key n) : address a < 6^n := by
  simpa only [address, digits_length] using pack_lt (digits a)

theorem six_pow_le_two (n : ℕ) : 6^n ≤ 2^(3*n) := by
  calc
    6^n ≤ 8^n := Nat.pow_le_pow_left (show 6 ≤ 8 by omega) n
    _ = _ := by rw [show (8:ℕ)=2^3 by norm_num, ← pow_mul]

theorem address_bits {n : ℕ} (a : Key n) : Nat.log2 (address a+1) ≤ 3*n := by
  have h := (address_lt a).trans_le (six_pow_le_two n)
  have hlog : Nat.log2 (address a+1) ≤ Nat.log2 (2^(3*n)) := by
    simpa only [Nat.log2_eq_log_two] using
      (Nat.log_mono_right (b := 2) (show address a+1 ≤ 2^(3*n) by omega))
  simpa only [Nat.log2_two_pow] using hlog

/-- Every polynomial-size trie/allocation address has a logarithmic word
budget when physical length and coefficient width have logarithmic budgets. -/
theorem storage_address_bits (n q p r cn cq : ℕ)
    (hn : n ≤ cn*(r+1)) (hq : q ≤ 2^(cq*(r+1))) :
    Nat.log2 ((n+1)^p * 6^n * q + 1) ≤ (p*(cn+1)+3*cn+cq+1)*(r+1) := by
  have hn2 : n+1 ≤ 2^(n+1) := (Nat.lt_two_pow_self (n := n+1)).le
  have hpow : (n+1)^p ≤ 2^(p*(n+1)) := by
    calc
      (n+1)^p ≤ (2^(n+1))^p := Nat.pow_le_pow_left hn2 p
      _ = _ := by rw [← pow_mul, Nat.mul_comm (n+1) p]
  have hsize : (n+1)^p * 6^n * q ≤ 2^(p*(n+1)+3*n+cq*(r+1)) := by
    calc
      _ ≤ 2^(p*(n+1))*2^(3*n)*2^(cq*(r+1)) :=
        Nat.mul_le_mul (Nat.mul_le_mul hpow (six_pow_le_two n)) hq
      _ = _ := by rw [pow_add, pow_add]
  have he : p*(n+1)+3*n+cq*(r+1)+1 ≤ (p*(cn+1)+3*cn+cq+1)*(r+1) := by
    nlinarith
  have hsize2 : (n+1)^p*6^n*q+1 ≤ 2^((p*(cn+1)+3*cn+cq+1)*(r+1)) := by
    have hp : 0 < 2^(p*(n+1)+3*n+cq*(r+1)) := by positivity
    calc
      _ ≤ 2^(p*(n+1)+3*n+cq*(r+1))+1 := Nat.add_le_add_right hsize 1
      _ ≤ 2^(p*(n+1)+3*n+cq*(r+1)+1) := by rw [pow_succ]; omega
      _ ≤ _ := Nat.pow_le_pow_right (by omega) he
  have hl := Nat.log_mono_right (b := 2) hsize2
  simpa only [← Nat.log2_eq_log_two, Nat.log2_two_pow] using hl

/-- Test and copy a candidate exactly once. Rejected copies and tests remain
in the work counter. Copies cost at most `n` pointer-sized coordinates. -/
def childrenCounted {n : ℕ} (test : Key n → Bool × ℕ) (a : Key n)
    (i : Fin n) : List Label → List (Key n) × ℕ
  | [] => ([],0)
  | v :: vs =>
      let child := put a i v
      let checked := test child
      let rest := childrenCounted test a i vs
      (if checked.1 then child :: rest.1 else rest.1,
        n + checked.2 + 1 + rest.2)

theorem childrenCounted_value {n : ℕ} (test : Key n → Bool × ℕ) (a : Key n)
    (i : Fin n) (alphabet : List Label) :
    (childrenCounted test a i alphabet).1 =
      (alphabet.map (fun v => put a i v)).filter (fun v => (test v).1) := by
  induction alphabet with
  | nil => rfl
  | cons v vs ih =>
      simp only [childrenCounted, List.map_cons, List.filter_cons, ih]

theorem childrenCounted_work_le {n : ℕ} (test : Key n → Bool × ℕ) (B : ℕ)
    (ht : ∀ a, (test a).2 ≤ B) (a : Key n) (i : Fin n) (alphabet : List Label) :
    (childrenCounted test a i alphabet).2 ≤ alphabet.length*(n+B+1) := by
  induction alphabet with
  | nil => simp [childrenCounted]
  | cons v vs ih =>
      simp only [childrenCounted, List.length_cons, Nat.succ_mul]
      have := ht (put a i v)
      omega

structure Generated (n : ℕ) where
  keys : List (Key n)
  work : ℕ

/-- Joint array-key enumeration and test/copy counter. The previous layer
and every tested child are bound once before the next layer is assembled. -/
def generateCounted {n : ℕ} (alphabet : List Label) (test : Key n → Bool × ℕ) : ℕ → Generated n
  | 0 => ⟨[zero n], n⟩
  | d+1 =>
      let previous := generateCounted alphabet test d
      if hd : d < n then
        let branches := previous.keys.map (fun a => childrenCounted test a ⟨d,hd⟩ alphabet)
        { keys := branches.flatMap Prod.fst
          work := previous.work + (branches.map Prod.snd).sum }
      else { keys := [], work := previous.work }

theorem generateCounted_keys {n : ℕ} (alphabet : List Label) (test : Key n → Bool × ℕ) (d : ℕ) :
    (generateCounted alphabet test d).keys = generateKeys alphabet (fun a => (test a).1) d := by
  induction d with
  | zero => rfl
  | succ d ih =>
      simp only [generateCounted, generateKeys]
      split
      · simp only [List.flatMap_map, childrenCounted_value, ih]
      · rfl

theorem list_sum_le_bound {A : Type*} (as : List A) (f : A → ℕ) (B : ℕ)
    (h : ∀ a ∈ as, f a ≤ B) : (as.map f).sum ≤ as.length*B := by
  induction as with
  | nil => simp
  | cons a as ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
      have ha := h a (by simp)
      have hs := ih (fun b hb => h b (by simp [hb]))
      omega

theorem generateCounted_work_le {n : ℕ} (alphabet : List Label)
    (test : Key n → Bool × ℕ) (B S : ℕ) (ht : ∀ a, (test a).2 ≤ B)
    (hlen : ∀ d ≤ n, (generateKeys alphabet (fun a => (test a).1) d).length ≤ S)
    (d : ℕ) (hd : d ≤ n) :
    (generateCounted alphabet test d).work ≤ n+d*(alphabet.length*(n+B+1))*S := by
  induction d with
  | zero => simp [generateCounted]
  | succ d ih =>
      have hlt : d < n := by omega
      simp only [generateCounted, dif_pos hlt, List.map_map, Function.comp_def]
      have hs := list_sum_le_bound (generateCounted alphabet test d).keys
        (fun a => (childrenCounted test a ⟨d,hlt⟩ alphabet).2)
        (alphabet.length*(n+B+1)) (fun a _ => childrenCounted_work_le test B ht a ⟨d,hlt⟩ alphabet)
      rw [generateCounted_keys] at hs
      have hs2 := hs.trans (Nat.mul_le_mul_right _ (hlen d (by omega)))
      have hi := ih (by omega)
      rw [generateCounted_keys]
      nlinarith

theorem high_generateKeys_eq (L m t d : ℕ) :
    generateKeys (List.finRange 6) (fun a => (highTest L m t a).1) d = generate L m t d := by
  induction d with
  | zero => rfl
  | succ d ih =>
      simp only [generateKeys, generate]
      split
      · rw [ih]; rfl
      · rfl

/-- All materialized key copies and actual pair/cap scans are bounded by a
polynomial in physical length times the real balanced HIGH base count. -/
theorem high_generation_work_le (L m t : ℕ) :
    (generateCounted (List.finRange 6) (highTest L m t) (2*L)).work ≤
      2*L+(2*L)*(6*(2*L+(3*(2*L)+2*(2*L)^2)+1))*
        ((2*L+1)*Fintype.card (BaseStates L m t)) := by
  apply generateCounted_work_le (List.finRange 6) (highTest L m t)
    (3*(2*L)+2*(2*L)^2) ((2*L+1)*Fintype.card (BaseStates L m t))
  · intro a; simp
  · intro d hd
    rw [high_generateKeys_eq]
    exact generate_length_le_bases L m t d hd
  · rfl

/-- Materialize a physical query key from stored ordinary labels and two
stored bit masks. Each coordinate uses at most three reads and one write. -/
def queryKey {n : ℕ} (ordinary : Vector (Fin 4) n)
    (distinguished channel : Vector Bool n) : Key n :=
  Vector.ofFn (fun i => if channel.get i then 5 else
    if distinguished.get i then 4 else ⟨(ordinary.get i).val, by have := (ordinary.get i).isLt; omega⟩)

theorem queryKey_refine {n : ℕ} (ordinary : Vector (Fin 4) n)
    (distinguished channel : Vector Bool n) (i : Fin n) :
    toWord (queryKey ordinary distinguished channel) i =
      if channel.get i then 5 else if distinguished.get i then 4 else
        ⟨(ordinary.get i).val, by have := (ordinary.get i).isLt; omega⟩ := by
  simp [toWord, queryKey]

def queryKeyCounted {n : ℕ} (ordinary : Vector (Fin 4) n)
    (distinguished channel : Vector Bool n) : Key n × ℕ :=
  (queryKey ordinary distinguished channel, 4*n)

@[simp] theorem queryKey_work {n : ℕ} (ordinary : Vector (Fin 4) n)
    (distinguished channel : Vector Bool n) :
    (queryKeyCounted ordinary distinguished channel).2 = 4*n := rfl

/-- A batch whose key metadata remains materialized vectors. -/
def writeBatchKeys {A : Type*} {n : ℕ} (values : Key n → A) :
    StoredHighDP.Trie A → List (Key n) → StoredHighDP.Trie A
  | table, [] => table
  | table, a :: as => writeBatchKeys values (write table a (values a)).1 as

theorem writeBatchKeys_refine {A : Type*} {n : ℕ}
    (values : Key n → A) (spec : Word n → A)
    (hv : ∀ a, values a = spec (toWord a))
    (table : StoredHighDP.Trie A) (as : List (Key n)) :
    writeBatchKeys values table as = StoredHighDP.writeBatch spec table (as.map toWord) := by
  induction as generalizing table with
  | nil => rfl
  | cons a as ih =>
      simp only [writeBatchKeys, write_value, hv, List.map_cons, StoredHighDP.writeBatch, ih]

/-- Node semantics receive a known array-backed key. The only function
coordinate read in `StoredHighDP.node` is therefore a direct array read. -/
def highRunLayer {R : Type*} [AddCommMonoid R] {L m t q : ℕ}
    (base : LeafWord (2*L) → StoredHighDP.Coefficients R q) (k : ℕ)
    (table : StoredHighDP.Trie (StoredHighDP.Coefficients R q)) :
    StoredHighDP.Trie (StoredHighDP.Coefficients R q) :=
  let states := (generate L m t (2*L)).filter (fun a => decide (StoredHighDP.height (toWord a) = k))
  writeBatchKeys (fun a => StoredHighDP.node base table (toWord a)) table states

theorem highRunLayer_refine {R : Type*} [AddCommMonoid R] {L m t q : ℕ}
    (base : LeafWord (2*L) → StoredHighDP.Coefficients R q) (k : ℕ)
    (table : StoredHighDP.Trie (StoredHighDP.Coefficients R q)) :
    highRunLayer (m := m) (t := t) base k table = StoredHighDP.runLayer (m := m) (t := t) base k table := by
  unfold highRunLayer
  rw [writeBatchKeys_refine _ (StoredHighDP.node base table) (fun _ => rfl)]
  have hf : ((generate L m t (2*L)).filter
      (fun a => decide (StoredHighDP.height (toWord a) = k))).map toWord =
      StoredHighDP.layerWords L m t k := by
    change List.map toWord (List.filter
      ((fun w => decide (StoredHighDP.height w = k)) ∘ toWord) _) = _
    rw [← List.filter_map, generate_refine]
    rfl
  rw [hf]
  rfl

def highExecute {R : Type*} [AddCommMonoid R] {L m t q : ℕ}
    (base : LeafWord (2*L) → StoredHighDP.Coefficients R q) :
    ℕ → StoredHighDP.Trie (StoredHighDP.Coefficients R q)
  | 0 => .empty
  | k+1 => highRunLayer (m := m) (t := t) base k (highExecute (m := m) (t := t) base k)

theorem highExecute_refine {R : Type*} [AddCommMonoid R] {L m t q : ℕ}
    (base : LeafWord (2*L) → StoredHighDP.Coefficients R q) (k : ℕ) :
    highExecute (m := m) (t := t) base k = StoredHighDP.execute (m := m) (t := t) base k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [highExecute, highRunLayer_refine, ih, StoredHighDP.execute]

/-- The complete HIGH table is computed with array metadata throughout the
actual enumeration and execution, while retaining the proved box semantics. -/
theorem highExecute_complete {R : Type*} [AddCommMonoid R] {L m t q : ℕ}
    (base : LeafWord (2*L) → StoredHighDP.Coefficients R q) (w : States L m t) (j : Fin q) :
    (StoredHighDP.lookup (highExecute (m := m) (t := t) base (2*L+1)) w.val).get j =
      boxValue w.val (StoredHighDP.logicalLeaf base j) := by
  rw [highExecute_refine]
  exact StoredHighDP.execute_complete base w j

/-- Joint batch value/work loop on actual vector metadata. -/
def writeBatchKeysCounted {R : Type*} {n q : ℕ}
    (values : Key n → StoredHighDP.BaseResult R q) :
    StoredHighDP.Trie (StoredHighDP.Coefficients R q) → List (Key n) →
      StoredHighDP.Trie (StoredHighDP.Coefficients R q) × ℕ
  | table, [] => (table,0)
  | table, a :: as =>
      let value := values a
      let written := write table a value.1
      let rest := writeBatchKeysCounted values written.1 as
      (rest.1, value.2+written.2+q+rest.2)

theorem writeBatchKeysCounted_value {R : Type*} {n q : ℕ}
    (values : Key n → StoredHighDP.BaseResult R q)
    (table : StoredHighDP.Trie (StoredHighDP.Coefficients R q)) (as : List (Key n)) :
    (writeBatchKeysCounted values table as).1 = writeBatchKeys (fun a => (values a).1) table as := by
  induction as generalizing table with
  | nil => rfl
  | cons a as ih => simp only [writeBatchKeysCounted, writeBatchKeys, ih]

theorem writeBatchKeysCounted_work {R : Type*} {n q : ℕ}
    (values : Key n → StoredHighDP.BaseResult R q) (B : ℕ)
    (hv : ∀ a, (values a).2 ≤ B)
    (table : StoredHighDP.Trie (StoredHighDP.Coefficients R q)) (as : List (Key n)) :
    (writeBatchKeysCounted values table as).2 ≤ as.length*(B+9*n+7+q) := by
  induction as generalizing table with
  | nil => simp [writeBatchKeysCounted]
  | cons a as ih =>
      simp only [writeBatchKeysCounted, write_work, List.length_cons, Nat.succ_mul]
      have hi := ih (write table a (values a).1).1
      have hvv := hv a
      nlinarith

def highRunLayerCounted {R : Type*} [AddCommMonoid R] {L m t q : ℕ}
    (base : LeafWord (2*L) → StoredHighDP.BaseResult R q) (k : ℕ)
    (table : StoredHighDP.Trie (StoredHighDP.Coefficients R q)) :
    StoredHighDP.Trie (StoredHighDP.Coefficients R q) × ℕ :=
  let generated := generateCounted (List.finRange 6) (highTest L m t) (2*L)
  let states := generated.keys.filter (fun a => decide (StoredHighDP.height (toWord a) = k))
  let batch := writeBatchKeysCounted
    (fun a => StoredHighDP.nodeCounted base table (toWord a)) table states
  (batch.1, generated.work + (2*L+1)*generated.keys.length + batch.2)

theorem highRunLayerCounted_value {R : Type*} [AddCommMonoid R] {L m t q : ℕ}
    (base : LeafWord (2*L) → StoredHighDP.BaseResult R q) (k : ℕ)
    (table : StoredHighDP.Trie (StoredHighDP.Coefficients R q)) :
    (highRunLayerCounted (m := m) (t := t) base k table).1 =
      highRunLayer (m := m) (t := t) (fun v => (base v).1) k table := by
  simp only [highRunLayerCounted, writeBatchKeysCounted_value, StoredHighDP.nodeCounted_value,
    generateCounted_keys, high_generateKeys_eq, highRunLayer]

def highLayerFactor (L q B : ℕ) : ℕ :=
  2*L + (2*L)*(6*(2*L+(3*(2*L)+2*(2*L)^2)+1)) + (2*L+1) +
    (B+5*(2*L+1)+10*q+7*(2*L)+9*(2*L)+7+q)

theorem highRunLayerCounted_work {R : Type*} [AddCommMonoid R] {L m t q : ℕ}
    (base : LeafWord (2*L) → StoredHighDP.BaseResult R q) (B : ℕ)
    (hb : ∀ v, (base v).2 ≤ B) (k : ℕ)
    (table : StoredHighDP.Trie (StoredHighDP.Coefficients R q)) :
    (highRunLayerCounted (m := m) (t := t) base k table).2 ≤
      highLayerFactor L q B * Fintype.card (States L m t) := by
  have hlen (d : ℕ) (hd : d ≤ 2*L) :
      (generateKeys (List.finRange 6) (fun a => (highTest L m t a).1) d).length ≤
        Fintype.card (States L m t) := by
    rw [high_generateKeys_eq, generate_length]
    exact StoredHighDP.generate_length_le_states L m t d hd
  have hg := generateCounted_work_le (List.finRange 6) (highTest L m t)
    (3*(2*L)+2*(2*L)^2) (Fintype.card (States L m t)) (fun _ => by simp) hlen (2*L) (le_refl _)
  have hl := hlen (2*L) (le_refl _)
  have hf := List.length_filter_le
    (fun a : Key (2*L) => decide (StoredHighDP.height (toWord a) = k))
    (generateCounted (List.finRange 6) (highTest L m t) (2*L)).keys
  have hbatch := writeBatchKeysCounted_work
    (fun a => StoredHighDP.nodeCounted base table (toWord a))
    (B+5*(2*L+1)+10*q+7*(2*L))
    (fun a => StoredHighDP.nodeCounted_work_le base B hb table (toWord a)) table
    ((generateCounted (List.finRange 6) (highTest L m t) (2*L)).keys.filter
      (fun a => decide (StoredHighDP.height (toWord a) = k)))
  rw [generateCounted_keys] at hf hbatch
  have hbatch2 := hbatch.trans (Nat.mul_le_mul_right _ (hf.trans hl))
  have hc : 1 ≤ Fintype.card (States L m t) := by
    exact (Fintype.card_pos_iff.mpr
      ⟨⟨CappedEnumeration.zeroWord (2*L), StoredHighDP.high_zero L m t⟩⟩)
  have hroot := Nat.mul_le_mul_left (2*L) hc
  have hscan := Nat.mul_le_mul_left (2*L+1) hl
  simp only [highRunLayerCounted, generateCounted_keys]
  unfold highLayerFactor
  simp only [List.length_finRange] at hg
  nlinarith

def highExecuteCounted {R : Type*} [AddCommMonoid R] {L m t q : ℕ}
    (base : LeafWord (2*L) → StoredHighDP.BaseResult R q) :
    ℕ → StoredHighDP.Trie (StoredHighDP.Coefficients R q) × ℕ
  | 0 => (.empty,0)
  | k+1 =>
      let previous := highExecuteCounted (m := m) (t := t) base k
      let next := highRunLayerCounted (m := m) (t := t) base k previous.1
      (next.1, previous.2+next.2)

theorem highExecuteCounted_value {R : Type*} [AddCommMonoid R] {L m t q : ℕ}
    (base : LeafWord (2*L) → StoredHighDP.BaseResult R q) (k : ℕ) :
    (highExecuteCounted (m := m) (t := t) base k).1 =
      highExecute (m := m) (t := t) (fun v => (base v).1) k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [highExecuteCounted, highRunLayerCounted_value, ih, highExecute]

theorem highExecuteCounted_work {R : Type*} [AddCommMonoid R] {L m t q : ℕ}
    (base : LeafWord (2*L) → StoredHighDP.BaseResult R q) (B : ℕ)
    (hb : ∀ v, (base v).2 ≤ B) (k : ℕ) :
    (highExecuteCounted (m := m) (t := t) base k).2 ≤
      k*highLayerFactor L q B*Fintype.card (States L m t) := by
  induction k with
  | zero => simp [highExecuteCounted]
  | succ k ih =>
      simp only [highExecuteCounted]
      have hn := highRunLayerCounted_work (m := m) (t := t) base B hb k
        (highExecuteCounted (m := m) (t := t) base k).1
      nlinarith

/-- Concrete array-key HIGH computation has exactly the same entropy
family and only polynomial physical-length overhead. -/
theorem highExecuteCounted_work_le_bases {R : Type*} [AddCommMonoid R] {L m t q : ℕ}
    (base : LeafWord (2*L) → StoredHighDP.BaseResult R q) (B : ℕ)
    (hb : ∀ v, (base v).2 ≤ B) :
    (highExecuteCounted (m := m) (t := t) base (2*L+1)).2 ≤
      (2*L+1)^2*highLayerFactor L q B*Fintype.card (BaseStates L m t) := by
  calc
    _ ≤ (2*L+1)*highLayerFactor L q B*Fintype.card (States L m t) := highExecuteCounted_work base B hb _
    _ ≤ _ := by
      have h := Nat.mul_le_mul_left ((2*L+1)*highLayerFactor L q B) (stateCount_le_baseCount L m t)
      nlinarith

/-- Selected coefficient reads use a materialized key and one array index. -/
def readSelected {R : Type*} {n q : ℕ}
    (table : StoredHighDP.Trie (StoredHighDP.Coefficients R q)) (a : Key n) (j : Fin q) :
    Option R × ℕ :=
  let value := read table a
  (value.1.map (fun v => v.get j), value.2+1)

@[simp] theorem readSelected_work {R : Type*} {n q : ℕ}
    (table : StoredHighDP.Trie (StoredHighDP.Coefficients R q)) (a : Key n) (j : Fin q) :
    (readSelected table a j).2 = 2*n+2 := by simp [readSelected]

@[simp] theorem readSelected_value {R : Type*} {n q : ℕ}
    (table : StoredHighDP.Trie (StoredHighDP.Coefficients R q)) (a : Key n) (j : Fin q) :
    (readSelected table a j).1 = StoredHighDP.readCoefficient table (toWord a) j := by
  simp [readSelected, StoredHighDP.readCoefficient]

theorem highExecuteCounted_complete {R : Type*} [AddCommMonoid R] {L m t q : ℕ}
    (base : LeafWord (2*L) → StoredHighDP.BaseResult R q) (a : Key (2*L))
    (ha : Balanced L m t (toWord a) ∧ Ordered (toWord a)) (j : Fin q) :
    (readSelected (highExecuteCounted (m := m) (t := t) base (2*L+1)).1 a j).1 =
      some (boxValue (toWord a) (StoredHighDP.logicalLeaf (fun v => (base v).1) j)) := by
  rw [readSelected_value, highExecuteCounted_value, highExecute_refine]
  have h := StoredHighDP.readCoefficient_execute base (⟨toWord a,ha⟩ : States L m t) j
  rw [StoredHighDP.executeCounted_value] at h
  exact h

/-- Concrete array-key execution preserves the rounded source-grid saving. -/
theorem rounded_highExecuteCounted_work {R : Type*} [AddCommMonoid R]
    (c theta : ℝ) (m q B : ℕ)
    (hc : 5 < c) (ht0 : 0 < theta) (ht1 : theta < 1/2) (hm : 0 < m)
    (base : LeafWord (2*Nat.ceil (c*(m:ℝ))) → StoredHighDP.BaseResult R q)
    (hb : ∀ v, (base v).2 ≤ B) :
    let L := Nat.ceil (c*(m:ℝ))
    let t := Nat.ceil (2*theta*(m:ℝ))
    ((highExecuteCounted (m := m) (t := t) base (2*L+1)).2 : ℝ) ≤
      (((2*L+1)^2*highLayerFactor L q B : ℕ) : ℝ) *
        ((L+1:ℝ)^4 * Real.exp (HighBoxEntropy.roundingConstant c theta) *
          (EntropyBounds.gridCount L m)^2 * ((4:ℝ)^m)^(-HighBoxEntropy.boxSaving c theta)) := by
  let L := Nat.ceil (c*(m:ℝ))
  let t := Nat.ceil (2*theta*(m:ℝ))
  have hfinite : ((highExecuteCounted (m := m) (t := t) base (2*L+1)).2 : ℝ) ≤
      (((2*L+1)^2*highLayerFactor L q B : ℕ) : ℝ) *
        (Fintype.card (BaseStates L m t) : ℝ) := by
    exact_mod_cast highExecuteCounted_work_le_bases (m := m) (t := t) base B hb
  have hentropy := HighBoxEntropy.rounded_totalCappedLeaves_polynomial c theta m hc ht0 ht1 hm
  have hcard : Fintype.card (BaseStates L m t) =
      Fintype.card (CacheCardinality.TotalCappedLeaves L m (2*m-t)) :=
    Fintype.card_congr (baseStatesEquivTotalCapped L m t)
  rw [hcard] at hfinite
  exact hfinite.trans (mul_le_mul_of_nonneg_left hentropy (by positivity))

/-- A base encoder with any equivalent Boolean test can use the generic
materialized Fin5 generator without importing its functional implementation. -/
theorem baseGenerate_refine {L m t : ℕ} (spec : Word (2*L) → Bool)
    (hspec : ∀ w, spec w = true ↔ Balanced L m t w ∧ ∀ i, (w i).val ≠ 5) (d : ℕ) :
    (baseGenerate L m t d).map toWord =
      generateWords ((List.finRange 5).map Fin.castSucc) spec d := by
  unfold baseGenerate
  apply generateKeys_refine
  intro a
  apply Bool.eq_iff_iff.mpr
  rw [baseTest_value, hspec]

#print axioms generate_refine
#print axioms highTest_value
#print axioms highTest_work
#print axioms generate_length_le_bases
#print axioms generateKeys_refine
#print axioms cacheGenerate_refine
#print axioms baseTest_value
#print axioms read_work
#print axioms write_work
#print axioms address_bits
#print axioms storage_address_bits
#print axioms generateCounted_work_le
#print axioms high_generation_work_le
#print axioms queryKey_refine
#print axioms highExecute_complete
#print axioms highExecuteCounted_work_le_bases
#print axioms highExecuteCounted_complete
#print axioms rounded_highExecuteCounted_work
#print axioms baseGenerate_refine

end ThinMatrix.ArrayKeys
