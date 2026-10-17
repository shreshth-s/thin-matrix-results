import HighBoxDP
import ArrayKeys
import Mathlib.Data.List.NodupEquivFin

/-!
# Direct materialized ordinary keys for generated HIGH masks

Ordinary choices are enumerated by a four-way vector recursion. A physical
key fixes every outside coordinate, writes private and star labels directly,
and reads only the free ordinary digits. SelectedAssignments and its finite
universe occur only in refinement proofs, never in the key program.
-/
namespace ThinMatrix.HighQueryKeys
open CacheBounds HighBoxDP
open scoped BigOperators

abbrev Digits (t : ℕ) := Vector (Fin 4) t
abbrev Mask (n : ℕ) := Vector (Option Bool) n
abbrev Support (n : ℕ) := Vector Bool n

def maskAt {n : ℕ} (mask : Mask n) : Fin n → Option Bool := mask.get

def supportSet {n : ℕ} (support : Support n) : Finset (Fin n) :=
  Finset.univ.filter (fun i => support.get i = true)

def prepend {t : ℕ} (digit : Fin 4) (tail : Digits t) : Digits (t+1) :=
  Vector.ofFn (Fin.cons digit tail.get)

@[simp] theorem prepend_get_zero {t : ℕ} (digit : Fin 4) (tail : Digits t) :
    (prepend digit tail).get 0 = digit := by simp [prepend]

@[simp] theorem prepend_get_succ {t : ℕ} (digit : Fin 4) (tail : Digits t) (i : Fin t) :
    (prepend digit tail).get i.succ = tail.get i := by simp [prepend]

theorem prepend_injective (t : ℕ) :
    Function.Injective (fun p : Fin 4 × Digits t => prepend p.1 p.2) := by
  intro x y h
  apply Prod.ext
  · simpa only [prepend_get_zero] using congrArg (fun v : Digits (t+1) => v.get 0) h
  · apply Vector.ext
    intro i hi
    have hh := congrArg (fun v : Digits (t+1) => v.get (Fin.succ ⟨i,hi⟩)) h
    have hh' : x.2.get ⟨i,hi⟩ = y.2.get ⟨i,hi⟩ := by
      simpa only [prepend_get_succ] using hh
    simpa [Vector.get] using hh'

def digitVectors : (t : ℕ) → List (Digits t)
  | 0 => [#v[]]
  | t+1 => ((List.finRange 4) ×ˢ (digitVectors t)).map (fun p => prepend p.1 p.2)

@[simp] theorem digitVectors_length (t : ℕ) : (digitVectors t).length = 4^t := by
  induction t with
  | zero => simp [digitVectors]
  | succ t ih =>
    simp only [digitVectors,List.length_map,List.length_product,List.length_finRange,ih]
    rw [pow_succ]
    omega

theorem digitVectors_nodup (t : ℕ) : (digitVectors t).Nodup := by
  induction t with
  | zero => simp [digitVectors]
  | succ t ih =>
    exact List.Nodup.map (prepend_injective t) ((List.nodup_finRange 4).product ih)

def tail {t : ℕ} (v : Digits (t+1)) : Digits t :=
  Vector.ofFn (fun i => v.get i.succ)

theorem prepend_head_tail {t : ℕ} (v : Digits (t+1)) :
    prepend (v.get 0) (tail v) = v := by
  apply Vector.ext
  intro i hi
  change (prepend (v.get 0) (tail v)).get ⟨i,hi⟩ = v.get ⟨i,hi⟩
  refine Fin.cases ?_ (fun j => ?_) (⟨i,hi⟩ : Fin (t+1))
  · exact prepend_get_zero _ _
  · simp [tail]

theorem mem_digitVectors {t : ℕ} (v : Digits t) : v ∈ digitVectors t := by
  induction t with
  | zero => simp [digitVectors,Vector.eq_empty]
  | succ t ih =>
    apply List.mem_map.mpr
    refine ⟨(v.get 0,tail v),List.mem_product.mpr ⟨List.mem_finRange _,ih _⟩,?_⟩
    exact prepend_head_tail v

instance digitsFintype (t : ℕ) : Fintype (Digits t) where
  elems := (digitVectors t).toFinset
  complete v := List.mem_toFinset.mpr (mem_digitVectors v)

theorem digitVectors_toFinset (t : ℕ) : (digitVectors t).toFinset = Finset.univ := by
  ext v
  simp [mem_digitVectors]

theorem digitVectors_sum {A : Type*} [AddCommMonoid A] (t : ℕ) (f : Digits t → A) :
    ((digitVectors t).map f).sum = ∑ v, f v := by
  rw [← List.sum_toFinset f (digitVectors_nodup t),digitVectors_toFinset]


/-- A bounded scan in increasing physical order. -/
def freePositions {n : ℕ} (mask : Mask n) (support : Support n) : List (Fin n) :=
  (List.finRange n).filter (fun i => support.get i && decide (mask.get i = some true))

@[simp] theorem mem_freePositions {n : ℕ} (mask : Mask n) (support : Support n) (i : Fin n) :
    i ∈ freePositions mask support ↔ support.get i = true ∧ mask.get i = some true := by
  simp [freePositions,Bool.and_eq_true]

theorem freePositions_nodup {n : ℕ} (mask : Mask n) (support : Support n) :
    (freePositions mask support).Nodup := (List.nodup_finRange n).filter _

theorem freePositions_length {n : ℕ} (mask : Mask n) (support : Support n) :
    (freePositions mask support).length =
      ((supportSet support).filter (fun i => maskAt mask i = some true)).card := by
  have he : (freePositions mask support).toFinset =
      (supportSet support).filter (fun i => maskAt mask i = some true) := by
    ext i
    simp [supportSet,maskAt]
  rw [←he,List.toFinset_card_of_nodup (freePositions_nodup mask support)]

/-- The rank-to-free-position bijection uses an actual ordered list and
its bounded index search. Its proof fields erase. -/
def positionEquiv {n : ℕ} (mask : Mask n) (support : Support n) :
    Fin (freePositions mask support).length ≃ SelectedOrdinary (maskAt mask) (supportSet support) :=
  (List.Nodup.getEquiv (freePositions mask support) (freePositions_nodup mask support)).trans
  { toFun := fun i => ⟨⟨i.val,(mem_freePositions mask support i.val).mp i.property |>.2⟩,
      by simpa [supportSet] using ((mem_freePositions mask support i.val).mp i.property).1⟩
    invFun := fun i => ⟨i.val.val,(mem_freePositions mask support i.val.val).mpr
      ⟨by simpa [supportSet] using i.property,i.val.property⟩⟩
    left_inv := fun i => Subtype.ext rfl
    right_inv := fun i => Subtype.ext (Subtype.ext rfl) }

@[simp] theorem positionEquiv_symm_val {n : ℕ} (mask : Mask n) (support : Support n)
    (i : SelectedOrdinary (maskAt mask) (supportSet support)) :
    ((positionEquiv mask support).symm i).val =
      (freePositions mask support).idxOf i.val.val := rfl

/-- Digit assignment is a proof denotation of the same bounded list rank. -/
def digitAssignment {n : ℕ} (mask : Mask n) (support : Support n)
    (digits : Digits (freePositions mask support).length) :
    SelectedAssignments (maskAt mask) (supportSet support) :=
  fun i => digits.get ((positionEquiv mask support).symm i)

/-- Literal array key formation; outside ordinary values are never free.
The free-position list is shared by every coordinate of this key. -/
def makeKey {n : ℕ} (mask : Mask n) (support : Support n)
    (outside : Vector (Fin 4) n) (digits : Digits (freePositions mask support).length) :
    ArrayKeys.Key n :=
  let positions := freePositions mask support
  Vector.ofFn fun i =>
    if hm : mask.get i = some true then
      if hs : support.get i = true then
        let rank : Fin positions.length := ⟨positions.idxOf i,
          List.idxOf_lt_length_of_mem ((mem_freePositions mask support i).mpr ⟨hs,hm⟩)⟩
        (digits.get rank).castSucc.castSucc
      else (outside.get i).castSucc.castSucc
    else if mask.get i = some false then 4 else 5

/-- Every materialized key is exactly the corresponding selected box word. -/
theorem makeKey_refines {n : ℕ} (mask : Mask n) (support : Support n)
    (outside : Vector (Fin 4) n) (digits : Digits (freePositions mask support).length) :
    ArrayKeys.toWord (makeKey mask support outside digits) =
      selectedWord (maskAt mask) (supportSet support) outside.get
        (digitAssignment mask support digits) := by
  funext i
  simp only [makeKey,ArrayKeys.toWord,Vector.get_ofFn,selectedWord,fixedWord,maskAt,
    extendAssignment,digitAssignment]
  by_cases hm : mask.get i = some true
  · simp only [hm,dite_true]
    by_cases hs : support.get i = true
    · have hi : i ∈ supportSet support := by simp [supportSet,hs]
      simp only [hs,dite_true,hi]
      congr 1
    · have hi : i ∉ supportSet support := by simp [supportSet,hs]
      simp only [hs,dite_false,hi]
      rfl
  · simp only [hm,dite_false]
    rfl

/-- Materialized digit vectors and selected assignments are bijective. -/
def assignmentEquiv {n : ℕ} (mask : Mask n) (support : Support n) :
    Digits (freePositions mask support).length ≃
      SelectedAssignments (maskAt mask) (supportSet support) where
  toFun := digitAssignment mask support
  invFun a := Vector.ofFn (fun j => a (positionEquiv mask support j))
  left_inv digits := by
    apply Vector.ext
    intro j hj
    simp only [digitAssignment,Vector.getElem_ofFn,Equiv.symm_apply_apply]
    rfl
  right_inv a := by
    funext i
    simp [digitAssignment]


/-- Materialized physical embedding coordinates, formed once per query. -/
def locations {k n : ℕ} (e : Fin k ↪o Fin n) : Vector (Fin n) k := Vector.ofFn e

def embeddedMaskArray {k n : ℕ} (loc : Vector (Fin n) k) (tags : Mask k) : Mask n :=
  Vector.ofFn fun i =>
    let j := loc.toList.idxOf i
    if h : j < k then tags.get ⟨j,h⟩ else some true

def embeddedSupportArray {k n : ℕ} (loc : Vector (Fin n) k) : Support n :=
  Vector.ofFn fun i => decide (i ∈ loc.toList)

theorem locations_nodup {k n : ℕ} (e : Fin k ↪o Fin n) : (locations e).toList.Nodup := by
  rw [locations,Vector.toList_ofFn]
  exact List.nodup_ofFn_ofInjective e.injective

@[simp] theorem locations_get {k n : ℕ} (e : Fin k ↪o Fin n) (j : Fin k) :
    (locations e).get j = e j := by simp [locations]

@[simp] theorem locations_mem {k n : ℕ} (e : Fin k ↪o Fin n) (i : Fin n) :
    i ∈ (locations e).toList ↔ ∃ j, e j = i := by
  simp [locations,Vector.toList_ofFn,List.mem_ofFn]

theorem locations_idxOf {k n : ℕ} (e : Fin k ↪o Fin n) (j : Fin k) :
    (locations e).toList.idxOf (e j) = j.val := by
  have hh := List.get_idxOf (locations_nodup e) (⟨j.val,by simp⟩ : Fin (locations e).toList.length)
  simpa [locations,Vector.toList_ofFn] using hh

@[simp] theorem embeddedMaskArray_at {k n : ℕ} (e : Fin k ↪o Fin n)
    (tags : Mask k) (j : Fin k) :
    (embeddedMaskArray (locations e) tags).get (e j) = tags.get j := by
  simp [embeddedMaskArray,locations_idxOf,j.isLt]

theorem embeddedMaskArray_refines {k n : ℕ} (e : Fin k ↪o Fin n) (tags : Mask k) :
    maskAt (embeddedMaskArray (locations e) tags) = embeddedMask e tags.get := by
  funext i
  by_cases hi : ∃ j, e j = i
  · obtain ⟨j,rfl⟩ := hi
    simp [maskAt]
  · have hnot : i ∉ (locations e).toList := (locations_mem e i).not.mpr hi
    have hj : ¬ (locations e).toList.idxOf i < k := by
      simpa using (List.idxOf_lt_length_iff.not.mpr hnot)
    simp [maskAt,embeddedMaskArray,hj,embeddedMask,hi]

theorem embeddedSupportArray_refines {k n : ℕ} (e : Fin k ↪o Fin n) :
    supportSet (embeddedSupportArray (locations e)) = embeddedSupport e := by
  ext i
  simp only [supportSet,Finset.mem_filter,Finset.mem_univ,true_and,embeddedSupportArray,
    Vector.get_ofFn,decide_eq_true_eq,locations_mem,embeddedSupport,Finset.mem_image]

/-- Reverse the algebraic mask into physical order by a bounded list read
per position. This vector is shared by all its 4^t ordinary digit choices. -/
def reversedMaskArray (ms : List (Option Bool)) : Mask ms.length := Vector.ofFn (reverseMask ms)

@[simp] theorem reversedMaskArray_get (ms : List (Option Bool)) :
    (reversedMaskArray ms).get = reverseMask ms := by funext i; simp [reversedMaskArray]

/-- Actual physical mask/support arrays. Their construction scans at most
n*k coordinates and does not enumerate ordinary assignments. -/
def physicalMask {n : ℕ} (ms : List (Option Bool)) (e : Fin ms.length ↪o Fin n) : Mask n :=
  embeddedMaskArray (locations e) (reversedMaskArray ms)

def physicalSupport {k n : ℕ} (e : Fin k ↪o Fin n) : Support n := embeddedSupportArray (locations e)

@[simp] theorem physicalMask_refines {n : ℕ} (ms : List (Option Bool)) (e : Fin ms.length ↪o Fin n) :
    maskAt (physicalMask ms e) = embeddedMask e (reverseMask ms) := by
  rw [physicalMask,embeddedMaskArray_refines,reversedMaskArray_get]

@[simp] theorem physicalSupport_refines {k n : ℕ} (e : Fin k ↪o Fin n) :
    supportSet (physicalSupport e) = embeddedSupport e := embeddedSupportArray_refines e

/-- Generated masks have exactly t free ordinary positions in the actual
physical locator. The enumeration therefore allocates exactly t digits. -/
theorem physical_free_length {n t k : ℕ} (ms : List (Option Bool))
    (hms : ms ∈ OrderedBoxes.orderedBoxMasks t k) (e : Fin ms.length ↪o Fin n) :
    (freePositions (physicalMask ms e) (physicalSupport e)).length = t := by
  rw [freePositions_length,physicalMask_refines,physicalSupport_refines,
    embeddedMask_ordinary_count,reverseMask_ordinary_count_of_generated hms]

/-- Direct four-way ordinary digit stream mapped to materialized physical
keys, with every outside coordinate fixed by the locator. -/
def keys {n : ℕ} (mask : Mask n) (support : Support n) (outside : Vector (Fin 4) n) :
    List (ArrayKeys.Key n) :=
  (digitVectors (freePositions mask support).length).map (makeKey mask support outside)

@[simp] theorem keys_length {n : ℕ} (mask : Mask n) (support : Support n)
    (outside : Vector (Fin 4) n) :
    (keys mask support outside).length = 4^(freePositions mask support).length := by simp [keys]

/-- Complete selected-assignment contraction through actual integer-array
keys. No enumeration of the SelectedAssignments finite universe is run. -/
theorem keys_sum {n : ℕ} {A : Type*} [AddCommMonoid A]
    (mask : Mask n) (support : Support n) (outside : Vector (Fin 4) n)
    (f : ArrayKeys.Key n → A) :
    ((keys mask support outside).map f).sum =
      ∑ a : SelectedAssignments (maskAt mask) (supportSet support),
        f (ArrayKeys.materialize (selectedWord (maskAt mask) (supportSet support) outside.get a)) := by
  simp only [keys,List.map_map,Function.comp_def]
  rw [digitVectors_sum]
  have he (d : Digits (freePositions mask support).length) :
      makeKey mask support outside d = ArrayKeys.materialize
        (selectedWord (maskAt mask) (supportSet support) outside.get (digitAssignment mask support d)) := by
    rw [←makeKey_refines,ArrayKeys.materialize_toWord]
  simp_rw [he]
  exact (assignmentEquiv mask support).sum_comp
    (fun a => f (ArrayKeys.materialize (selectedWord (maskAt mask) (supportSet support) outside.get a)))

def physicalKeys {n : ℕ} (ms : List (Option Bool)) (e : Fin ms.length ↪o Fin n)
    (outside : Vector (Fin 4) n) : List (ArrayKeys.Key n) :=
  let mask := physicalMask ms e
  let support := physicalSupport e
  keys mask support outside

@[simp] theorem physicalKeys_length {n t k : ℕ} (ms : List (Option Bool))
    (hms : ms ∈ OrderedBoxes.orderedBoxMasks t k) (e : Fin ms.length ↪o Fin n)
    (outside : Vector (Fin 4) n) :
    (physicalKeys ms e outside).length = 4^t := by
  rw [physicalKeys,keys_length,physical_free_length ms hms e]

/-- The production key list has exactly the same weighted box contraction
as the backend's mathematical selected-assignment sum, for arbitrary f. -/
theorem physicalKeys_sum {n : ℕ} {A : Type*} [AddCommMonoid A]
    (ms : List (Option Bool)) (e : Fin ms.length ↪o Fin n)
    (outside : Vector (Fin 4) n) (f : ArrayKeys.Key n → A) :
    ((physicalKeys ms e outside).map f).sum =
      ∑ a : SelectedAssignments (embeddedMask e (reverseMask ms)) (embeddedSupport e),
        f (ArrayKeys.materialize (selectedWord (embeddedMask e (reverseMask ms))
          (embeddedSupport e) outside.get a)) := by
  rw [←physicalMask_refines ms e,←physicalSupport_refines e]
  exact keys_sum (physicalMask ms e) (physicalSupport e) outside f


abbrev Masks := List (List (Option Bool))

/-- The infeasible guard precedes recursion; both recursive outputs are stored once.
The overhead charges guard/matches, list maps, prefix cells, and append visits. -/
def generateMasks : ℕ → ℕ → Masks × ℕ
  | t, 0 => if 0 < t then ([],2) else ([[]],4)
  | t, k+1 =>
      if k+1 < t then ([],2) else
        match t with
        | 0 => ([List.replicate (k+1) none],4*(k+2))
        | t+1 =>
            let left := generateMasks (t+1) k
            let right := generateMasks t k
            (left.1.map (some false :: ·) ++ right.1.map (some true :: ·),
              left.2 + right.2 + 8*(k+2)*(left.1.length+right.1.length+1))

theorem original_empty_of_lt {t k : ℕ} (h : k < t) : OrderedBoxes.orderedBoxMasks t k = [] := by
  apply List.length_eq_zero_iff.mp
  rw [OrderedBoxes.orderedBoxMasks_length,Nat.choose_eq_zero_of_lt h]

theorem generateMasks_value (t k : ℕ) : (generateMasks t k).1 = OrderedBoxes.orderedBoxMasks t k := by
  induction k generalizing t with
  | zero => cases t <;> simp [generateMasks,OrderedBoxes.orderedBoxMasks]
  | succ k ih =>
    by_cases h : k+1 < t
    · simp only [generateMasks,if_pos h]
      exact (original_empty_of_lt h).symm
    · cases t with
      | zero => simp [generateMasks,OrderedBoxes.orderedBoxMasks]
      | succ t =>
        simp only [generateMasks,if_neg h,OrderedBoxes.orderedBoxMasks,ih]

theorem generateMasks_length (t k : ℕ) : (generateMasks t k).1.length = k.choose t := by
  rw [generateMasks_value,OrderedBoxes.orderedBoxMasks_length]

theorem generateMasks_work_small (t k : ℕ) :
    (generateMasks t k).2 ≤ 32*(k+1)^2*(k.choose t)+2 := by
  induction k generalizing t with
  | zero => cases t <;> simp [generateMasks]
  | succ k ih =>
    by_cases h : k+1 < t
    · simp only [generateMasks,if_pos h]
      omega
    · have ht : t ≤ k+1 := by omega
      cases t with
      | zero =>
        simp only [generateMasks,not_lt_zero,if_false,Nat.choose_zero_right]
        nlinarith
      | succ t =>
        have hC : 1 ≤ k.choose (t+1) + k.choose t := by
          have hp := Nat.choose_pos ht
          rw [Nat.choose_succ_succ] at hp
          change 0 < k.choose t + k.choose (t+1) at hp
          omega
        have hleft := ih (t+1)
        have hright := ih t
        simp only [generateMasks,if_neg h]
        rw [generateMasks_length,generateMasks_length,Nat.choose_succ_succ]
        change (generateMasks (t+1) k).2 + (generateMasks t k).2 +
          8*(k+2)*(k.choose (t+1)+k.choose t+1) ≤
            32*(k+2)^2*(k.choose t+k.choose (t+1))+2
        have hnonneg : 0 ≤ k * (k.choose (t+1)+k.choose t) := Nat.zero_le _
        nlinarith

theorem generateMasks_work_le (t k : ℕ) :
    (generateMasks t k).2 ≤ 64*(k+1)^3*(k.choose t+1) := by
  have hpow : (k+1)^2 ≤ (k+1)^3 :=
    Nat.pow_le_pow_right (by omega : 0 < k+1) (by omega : 2 ≤ 3)
  have hp' : 0 < (k+1)^3 := by positivity
  have hp : 1 ≤ (k+1)^3 := by omega
  calc
    (generateMasks t k).2 ≤ 32*(k+1)^2*(k.choose t)+2 := generateMasks_work_small t k
    _ ≤ 32*(k+1)^3*(k.choose t)+2 :=
      Nat.add_le_add_right (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 32 hpow)) 2
    _ ≤ 32*(k+1)^3*(k.choose t)+32*(k+1)^3 := by omega
    _ = 32*(k+1)^3*(k.choose t+1) := by ring
    _ ≤ 64*(k+1)^3*(k.choose t+1) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega : 32 ≤ 64))


/-- Reindexing proof is erased; no membership test or list search occurs. -/
def reindex {k n : ℕ} (ms : List (Option Bool)) (hlen : ms.length = k)
    (e : Fin k ↪o Fin n) : Fin ms.length ↪o Fin n :=
  (Fin.castOrderIso hlen).toOrderEmbedding.trans e

/-- Attach already known generator membership; no decidable membership
search is used by this conversion. -/
def attachMasks (t k : ℕ) (masks : Masks) (h : masks = OrderedBoxes.orderedBoxMasks t k) :
    List {ms // ms ∈ OrderedBoxes.orderedBoxMasks t k} :=
  masks.attach.map (fun ms => ⟨ms.val,h ▸ ms.property⟩)

@[simp] theorem attachMasks_values (t k : ℕ) (masks : Masks)
    (h : masks = OrderedBoxes.orderedBoxMasks t k) :
    (attachMasks t k masks h).map Subtype.val = masks := by
  simp [attachMasks,List.map_map,Function.comp_def]

/-- The pruned mask program, carrying proof fields erased at runtime. -/
def generatedMasks (t k : ℕ) : List {ms // ms ∈ OrderedBoxes.orderedBoxMasks t k} :=
  let result := generateMasks t k
  attachMasks t k result.1 (generateMasks_value t k)

@[simp] theorem generatedMasks_values (t k : ℕ) :
    (generatedMasks t k).map Subtype.val = OrderedBoxes.orderedBoxMasks t k := by
  unfold generatedMasks
  rw [attachMasks_values,generateMasks_value]

@[simp] theorem generatedMasks_length (t k : ℕ) : (generatedMasks t k).length = k.choose t := by
  have h := congrArg List.length (generatedMasks_values t k)
  simpa only [List.length_map,OrderedBoxes.orderedBoxMasks_length] using h

/-- Production masks carry their generator membership proof. That proof
is used only for cardinality/correctness, with no runtime whole-list guard. -/
def generatedKeys (t k n : ℕ) (e : Fin k ↪o Fin n) (outside : Vector (Fin 4) n) :
    List (ArrayKeys.Key n) :=
  (generatedMasks t k).flatMap fun ms =>
    physicalKeys ms.val (reindex ms.val (OrderedBoxes.orderedBoxMasks_shape ms.property).1 e) outside

theorem generatedKeys_length (t k n : ℕ) (e : Fin k ↪o Fin n) (outside : Vector (Fin 4) n) :
    (generatedKeys t k n e outside).length = k.choose t*4^t := by
  unfold generatedKeys
  rw [List.length_flatMap]
  have hm : List.map (fun ms : {ms // ms ∈ OrderedBoxes.orderedBoxMasks t k} =>
      (physicalKeys ms.val (reindex ms.val (OrderedBoxes.orderedBoxMasks_shape ms.property).1 e) outside).length)
      (generatedMasks t k) =
      List.map (fun _ => 4^t) (generatedMasks t k) := by
    apply List.map_congr_left
    intro ms _
    exact physicalKeys_length ms.val ms.property _ outside
  rw [hm]
  simp

/-- Arbitrary weights of physical stored handles are preserved, including
all coefficients and independent formal source/target weights. -/
theorem physicalState_sum {L m t k : ℕ} {A : Type*} [AddCommMonoid A]
    (ms : List (Option Bool)) (hms : ms ∈ OrderedBoxes.orderedBoxMasks t k)
    (hlen : ms.length = 2*m) (e : Fin ms.length ↪o Fin (2*L))
    (outside : Vector (Fin 4) (2*L))
    (hleft : ((embeddedSupport e).filter (fun i => i.val < L)).card ≤ m)
    (hright : ((embeddedSupport e).filter (fun i => L ≤ i.val)).card ≤ m)
    (f : ArrayKeys.Key (2*L) → A) :
    ((physicalKeys ms e outside).map f).sum =
      ∑ a : SelectedAssignments (embeddedMask e (reverseMask ms)) (embeddedSupport e),
        f (ArrayKeys.materialize (physicalState ms hms hlen e outside.get hleft hright a).val) := by
  exact physicalKeys_sum ms e outside f

/-- Work-counted four-way generation shares its stored recursive result.
The counter pays product/map visits and copying every t+1-vector. -/
structure DigitResult (t : ℕ) where
  values : List (Digits t)
  work : ℕ

def generateDigits : (t : ℕ) → DigitResult t
  | 0 => ⟨[#v[]],1⟩
  | t+1 =>
      let child := generateDigits t
      let pairs := (List.finRange 4) ×ˢ child.values
      ⟨pairs.map (fun p => prepend p.1 p.2),
        child.work+8*(t+2)*pairs.length+8⟩

@[simp] theorem generateDigits_values (t : ℕ) : (generateDigits t).values = digitVectors t := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [generateDigits,digitVectors,ih]

theorem generateDigits_work_le (t : ℕ) : (generateDigits t).work ≤ 16*(t+1)^2*4^t := by
  induction t with
  | zero => norm_num [generateDigits]
  | succ t ih =>
      have hp : 1 ≤ 4^t := Nat.one_le_pow t 4 (by omega)
      simp only [generateDigits,List.length_product,List.length_finRange,generateDigits_values,
        digitVectors_length,pow_succ]
      nlinarith


/-- Literal bounded rank search with its comparison/loop counter. -/
def rankCounted {α : Type*} [DecidableEq α] (x : α) : List α → ℕ × ℕ
  | [] => (0,1)
  | y::ys => if x=y then (0,2) else
      let child := rankCounted x ys
      (child.1+1,child.2+2)

@[simp] theorem rankCounted_value {α : Type*} [DecidableEq α] (x : α) (xs : List α) :
    (rankCounted x xs).1 = xs.idxOf x := by
  induction xs with
  | nil => simp [rankCounted]
  | cons y ys ih =>
      by_cases h:x=y
      · simp [rankCounted,h]
      · simp [rankCounted,h,Ne.symm h,ih]

theorem rankCounted_work {α : Type*} [DecidableEq α] (x : α) (xs : List α) :
    (rankCounted x xs).2 ≤ 2*xs.length+1 := by
  induction xs with
  | nil => simp [rankCounted]
  | cons y ys ih => by_cases h:x=y <;> simp [rankCounted,h] <;> omega

/-- One physical coordinate: no unbounded assignment or mask-list search. -/
def cellCounted {n : ℕ} (mask : Mask n) (support : Support n)
    (outside : Vector (Fin 4) n) (positions : List (Fin n))
    (hp : positions = freePositions mask support) (digits : Digits positions.length)
    (i : Fin n) : Label × ℕ :=
  if hm : mask.get i = some true then
    if hs : support.get i = true then
      let rank := rankCounted i positions
      let hr : rank.1 < positions.length := by
        rw [rankCounted_value,hp]
        exact List.idxOf_lt_length_of_mem ((mem_freePositions mask support i).mpr ⟨hs,hm⟩)
      ((digits.get ⟨rank.1,hr⟩).castSucc.castSucc,rank.2+6)
    else ((outside.get i).castSucc.castSucc,6)
  else if mask.get i = some false then (4,5) else (5,5)

theorem cellCounted_work {n : ℕ} (mask : Mask n) (support : Support n)
    (outside : Vector (Fin 4) n) (positions : List (Fin n))
    (hp : positions = freePositions mask support) (digits : Digits positions.length) (i : Fin n) :
    (cellCounted mask support outside positions hp digits i).2 ≤ 2*positions.length+8 := by
  unfold cellCounted
  split
  · split
    · change (rankCounted i positions).2+6 ≤ _
      have h := rankCounted_work i positions
      omega
    · omega
  · split <;> omega

/-- Both value and cost read the same stored coordinate results. This
avoids recomputing a key or its rank searches when collecting the counter. -/
def makeKeyCounted {n : ℕ} (mask : Mask n) (support : Support n)
    (outside : Vector (Fin 4) n) (digits : Digits (freePositions mask support).length) :
    ArrayKeys.Key n × ℕ :=
  let positions := freePositions mask support
  let cells := Vector.ofFn (cellCounted mask support outside positions rfl digits)
  (cells.map Prod.fst,6*n+(cells.toList.map Prod.snd).sum)

theorem makeKeyCounted_value {n : ℕ} (mask : Mask n) (support : Support n)
    (outside : Vector (Fin 4) n) (digits : Digits (freePositions mask support).length) :
    (makeKeyCounted mask support outside digits).1 = makeKey mask support outside digits := by
  apply Vector.ext
  intro j hj
  simp only [makeKeyCounted,Vector.getElem_map,Vector.getElem_ofFn,makeKey]
  unfold cellCounted
  split
  · split
    · simp only [rankCounted_value]
    · rfl
  · split <;> rfl

theorem makeKeyCounted_work_le {n : ℕ} (mask : Mask n) (support : Support n)
    (outside : Vector (Fin 4) n) (digits : Digits (freePositions mask support).length) :
    (makeKeyCounted mask support outside digits).2 ≤ n*(2*n+14) := by
  have hl : (freePositions mask support).length ≤ n := by
    simpa only [freePositions,List.length_finRange] using
      List.length_filter_le (fun i : Fin n => support.get i && decide (mask.get i = some true)) (List.finRange n)
  let cells := Vector.ofFn (cellCounted mask support outside (freePositions mask support) rfl digits)
  have hs : (cells.toList.map Prod.snd).sum ≤ n*(2*n+8) := by
    have h := List.sum_le_card_nsmul (cells.toList.map Prod.snd) (2*n+8) (by
      intro x hx
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hx
      have ha' : ∃ i, a = cellCounted mask support outside (freePositions mask support) rfl digits i := by
        simpa [cells,Vector.toList_ofFn,List.mem_ofFn,eq_comm] using ha
      obtain ⟨i,rfl⟩ := ha'
      exact (cellCounted_work mask support outside _ rfl digits i).trans (by omega))
    simpa [cells] using h
  change 6*n+(cells.toList.map Prod.snd).sum ≤ _
  nlinarith


/-- All retained digit vectors are stored once and their key/counter pairs
are consumed once. Counter collection never reruns key construction. -/
def keysCounted {n : ℕ} (mask : Mask n) (support : Support n) (outside : Vector (Fin 4) n) :
    List (ArrayKeys.Key n) × ℕ :=
  let digits := generateDigits (freePositions mask support).length
  let rows := digits.values.map (makeKeyCounted mask support outside)
  (rows.map Prod.fst,digits.work+(rows.map Prod.snd).sum+8*rows.length)

@[simp] theorem keysCounted_value {n : ℕ} (mask : Mask n) (support : Support n)
    (outside : Vector (Fin 4) n) :
    (keysCounted mask support outside).1 = keys mask support outside := by
  simp only [keysCounted,generateDigits_values,keys,List.map_map,Function.comp_def,makeKeyCounted_value]

def keyFactor (n : ℕ) : ℕ := 16*(n+1)^2+n*(2*n+14)+8

theorem keysCounted_work_le {n : ℕ} (mask : Mask n) (support : Support n)
    (outside : Vector (Fin 4) n) :
    (keysCounted mask support outside).2 ≤
      keyFactor n * 4^(freePositions mask support).length := by
  have hl : (freePositions mask support).length ≤ n := by
    simpa only [freePositions,List.length_finRange] using
      List.length_filter_le (fun i : Fin n => support.get i && decide (mask.get i = some true)) (List.finRange n)
  let rows := (generateDigits (freePositions mask support).length).values.map
    (makeKeyCounted mask support outside)
  have hlen : rows.length = 4^(freePositions mask support).length := by
    simp [rows]
  have hsum : (rows.map Prod.snd).sum ≤ rows.length*(n*(2*n+14)) := by
    have h := List.sum_le_card_nsmul (rows.map Prod.snd) (n*(2*n+14)) (by
      intro x hx
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hx
      obtain ⟨d,_,rfl⟩ := List.mem_map.mp ha
      exact makeKeyCounted_work_le mask support outside d)
    simpa only [List.length_map,smul_eq_mul] using h
  have hd := generateDigits_work_le (freePositions mask support).length
  have hpoly : 16*((freePositions mask support).length+1)^2 ≤ 16*(n+1)^2 := by gcongr
  change (generateDigits (freePositions mask support).length).work+
    (rows.map Prod.snd).sum+8*rows.length ≤ _
  calc
    _ ≤ 16*(n+1)^2*4^(freePositions mask support).length+
        rows.length*(n*(2*n+14))+8*rows.length := by
      exact Nat.add_le_add_right (Nat.add_le_add (hd.trans (Nat.mul_le_mul_right _ hpoly)) hsum) _
    _ = _ := by rw [hlen]; unfold keyFactor; ring

/-- Polynomial mask/support-array formation allowance. Reversing a mask,
copying embedding coordinates, and every bounded physical index search are
included. It counts finite coordinate/loop sites, not free machine division. -/
def physicalFormationWork (n k : ℕ) : ℕ := 16*(n+k+1)^2


/-- A single stored rank result supplies both physical tag and support bit.
The list conversion and every comparison are included in its counter. -/
def physicalCell {k n : ℕ} (loc : Vector (Fin n) k) (tags : Mask k) (i : Fin n) :
    (Option Bool × Bool) × ℕ :=
  let rank := rankCounted i loc.toList
  if h : rank.1 < k then ((tags.get ⟨rank.1,h⟩,true),rank.2+k+8)
  else ((some true,false),rank.2+k+8)

theorem physicalCell_tag {k n : ℕ} (loc : Vector (Fin n) k) (tags : Mask k) (i : Fin n) :
    (physicalCell loc tags i).1.1 = (embeddedMaskArray loc tags).get i := by
  simp only [physicalCell,embeddedMaskArray,Vector.get_ofFn,rankCounted_value]
  split <;> rfl

theorem physicalCell_support {k n : ℕ} (loc : Vector (Fin n) k) (tags : Mask k) (i : Fin n) :
    (physicalCell loc tags i).1.2 = (embeddedSupportArray loc).get i := by
  have hi : loc.toList.idxOf i < k ↔ i ∈ loc.toList := by
    simpa only [Vector.length_toList] using (List.idxOf_lt_length_iff (a := i) (l := loc.toList))
  simp only [physicalCell,embeddedSupportArray,Vector.get_ofFn,rankCounted_value]
  split
  · rename_i h
    simp [hi.mp h]
  · rename_i h
    simp [mt hi.mpr h]

theorem physicalCell_work {k n : ℕ} (loc : Vector (Fin n) k) (tags : Mask k) (i : Fin n) :
    (physicalCell loc tags i).2 ≤ 3*k+9 := by
  have h := rankCounted_work i loc.toList
  simp only [Vector.length_toList] at h
  dsimp only [physicalCell]
  split <;> change (rankCounted i loc.toList).2+k+8 ≤ _ <;> omega

structure PhysicalArrays (n : ℕ) where
  mask : Mask n
  support : Support n
  work : ℕ

/-- Both array payloads are projected from the same stored cell results. -/
def arraysCounted {k n : ℕ} (loc : Vector (Fin n) k) (tags : Mask k) : PhysicalArrays n :=
  let cells := Vector.ofFn (physicalCell loc tags)
  ⟨cells.map (fun c => c.1.1),cells.map (fun c => c.1.2),
    6*n+(cells.toList.map Prod.snd).sum⟩

@[simp] theorem arraysCounted_mask {k n : ℕ} (loc : Vector (Fin n) k) (tags : Mask k) :
    (arraysCounted loc tags).mask = embeddedMaskArray loc tags := by
  apply Vector.ext
  intro j hj
  simpa [arraysCounted,Vector.get] using physicalCell_tag loc tags ⟨j,hj⟩

@[simp] theorem arraysCounted_support {k n : ℕ} (loc : Vector (Fin n) k) (tags : Mask k) :
    (arraysCounted loc tags).support = embeddedSupportArray loc := by
  apply Vector.ext
  intro j hj
  simpa [arraysCounted,Vector.get] using physicalCell_support loc tags ⟨j,hj⟩

theorem arraysCounted_work_le {k n : ℕ} (loc : Vector (Fin n) k) (tags : Mask k) :
    (arraysCounted loc tags).work ≤ n*(3*k+15) := by
  let cells := Vector.ofFn (physicalCell loc tags)
  have hsum : (cells.toList.map Prod.snd).sum ≤ n*(3*k+9) := by
    have h := List.sum_le_card_nsmul (cells.toList.map Prod.snd) (3*k+9) (by
      intro x hx
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hx
      have ha' : ∃ i, a = physicalCell loc tags i := by
        simpa [cells,Vector.toList_ofFn,List.mem_ofFn,eq_comm] using ha
      obtain ⟨i,rfl⟩ := ha'
      exact physicalCell_work loc tags i)
    simpa [cells] using h
  change 6*n+(cells.toList.map Prod.snd).sum ≤ _
  nlinarith

/-- Copying the embedding and reversing its list mask are also paid.
The k(k+4) term permits a length-k linked-list read for each reverse entry. -/
theorem physicalFormationWork_le (n k : ℕ) :
    k*(k+4)+n*(3*k+15) ≤ physicalFormationWork n k := by
  unfold physicalFormationWork
  nlinarith

/-- The physical arrays are shared across the whole 4^t digit stream. -/
def physicalKeysCounted {n : ℕ} (ms : List (Option Bool)) (e : Fin ms.length ↪o Fin n)
    (outside : Vector (Fin 4) n) : List (ArrayKeys.Key n) × ℕ :=
  let arrays := arraysCounted (locations e) (reversedMaskArray ms)
  let result := keysCounted arrays.mask arrays.support outside
  (result.1,ms.length*(ms.length+4)+arrays.work+result.2)

@[simp] theorem physicalKeysCounted_value {n : ℕ} (ms : List (Option Bool))
    (e : Fin ms.length ↪o Fin n) (outside : Vector (Fin 4) n) :
    (physicalKeysCounted ms e outside).1 = physicalKeys ms e outside := by
  simp only [physicalKeysCounted,keysCounted_value,arraysCounted_mask,arraysCounted_support,
    physicalKeys,physicalMask,physicalSupport]

theorem physicalKeysCounted_work_le {n t k : ℕ} (ms : List (Option Bool))
    (hms : ms ∈ OrderedBoxes.orderedBoxMasks t k) (e : Fin ms.length ↪o Fin n)
    (outside : Vector (Fin 4) n) :
    (physicalKeysCounted ms e outside).2 ≤
      (physicalFormationWork n k+keyFactor n)*4^t := by
  have h := keysCounted_work_le (physicalMask ms e) (physicalSupport e) outside
  rw [physical_free_length ms hms e] at h
  have ha := arraysCounted_work_le (locations e) (reversedMaskArray ms)
  have hf := physicalFormationWork_le n ms.length
  have hlen := (OrderedBoxes.orderedBoxMasks_shape hms).1
  have hp : 1 ≤ 4^t := Nat.one_le_pow t 4 (by omega)
  have hw : physicalFormationWork n ms.length = physicalFormationWork n k := congrArg (physicalFormationWork n) hlen
  simp only [physicalKeysCounted,arraysCounted_mask,arraysCounted_support]
  change ms.length*(ms.length+4)+_+(keysCounted (physicalMask ms e) (physicalSupport e) outside).2 ≤ _
  rw [hw] at hf
  nlinarith


/-- End-to-end key enumeration uses the pruned stored mask result once,
then the stored key/counter rows once. Membership proofs erase. -/
def generatedKeysCounted (t k n : ℕ) (e : Fin k ↪o Fin n) (outside : Vector (Fin 4) n) :
    List (ArrayKeys.Key n) × ℕ :=
  let masks := generateMasks t k
  let typed := attachMasks t k masks.1 (generateMasks_value t k)
  let rows := typed.map (fun ms => physicalKeysCounted ms.val
    (reindex ms.val (OrderedBoxes.orderedBoxMasks_shape ms.property).1 e) outside)
  let output := rows.flatMap Prod.fst
  (output,masks.2+(rows.map Prod.snd).sum+8*rows.length+2*output.length)

@[simp] theorem generatedKeysCounted_value (t k n : ℕ) (e : Fin k ↪o Fin n)
    (outside : Vector (Fin 4) n) :
    (generatedKeysCounted t k n e outside).1 = generatedKeys t k n e outside := by
  simp only [generatedKeysCounted,generatedKeys,generatedMasks,List.flatMap_map,
    physicalKeysCounted_value]

def queryKeyFactor (n k : ℕ) : ℕ := 32*(k+1)^2+physicalFormationWork n k+keyFactor n+12

/-- Fully formed ordinary keys, with direct pruned mask construction,
all digit copies, rank searches and physical key arrays paid. -/
theorem generatedKeysCounted_work_le (t k n : ℕ) (ht : t ≤ k) (e : Fin k ↪o Fin n)
    (outside : Vector (Fin 4) n) :
    (generatedKeysCounted t k n e outside).2 ≤ queryKeyFactor n k*(k.choose t)*4^t := by
  let typed := generatedMasks t k
  let rows := typed.map (fun ms => physicalKeysCounted ms.val
    (reindex ms.val (OrderedBoxes.orderedBoxMasks_shape ms.property).1 e) outside)
  have hlen : rows.length = k.choose t := by simp [rows,typed]
  have hsum : (rows.map Prod.snd).sum ≤
      rows.length*((physicalFormationWork n k+keyFactor n)*4^t) := by
    have h := List.sum_le_card_nsmul (rows.map Prod.snd)
      ((physicalFormationWork n k+keyFactor n)*4^t) (by
        intro x hx
        obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hx
        obtain ⟨ms,_,rfl⟩ := List.mem_map.mp ha
        exact physicalKeysCounted_work_le ms.val ms.property _ outside)
    simpa only [List.length_map,smul_eq_mul] using h
  have hm := generateMasks_work_small t k
  have hC : 1 ≤ k.choose t := Nat.choose_pos ht
  have hP : 1 ≤ 4^t := Nat.one_le_pow t 4 (by omega)
  have hcp : 1 ≤ k.choose t*4^t := by simpa using Nat.mul_le_mul hC hP
  have hscale : 32*(k+1)^2*(k.choose t) ≤ 32*(k+1)^2*(k.choose t)*4^t := by
    exact Nat.le_mul_of_pos_right _ hP
  have htwo : 2 ≤ 2*(k.choose t)*4^t := by nlinarith
  have hloop : 8*(k.choose t) ≤ 8*(k.choose t)*4^t := by
    exact Nat.le_mul_of_pos_right _ hP
  have hkeys : (rows.flatMap Prod.fst).length = k.choose t*4^t := by
    change (generatedKeysCounted t k n e outside).1.length = _
    rw [generatedKeysCounted_value,generatedKeys_length]
  change (generateMasks t k).2+(rows.map Prod.snd).sum+8*rows.length+
    2*(rows.flatMap Prod.fst).length ≤ _
  rw [hlen] at hsum ⊢
  rw [hkeys]
  calc
    _ ≤ (32*(k+1)^2*(k.choose t)+2) +
        (k.choose t)*((physicalFormationWork n k+keyFactor n)*4^t)+8*(k.choose t)+2*(k.choose t*4^t) := by omega
    _ ≤ 32*(k+1)^2*(k.choose t)*4^t+2*(k.choose t)*4^t+
        (k.choose t)*((physicalFormationWork n k+keyFactor n)*4^t)+8*(k.choose t)*4^t+2*(k.choose t*4^t) := by omega
    _ = _ := by unfold queryKeyFactor; ring

/- Executable audits of the actual materialized producer, including the
boundary where pruning prevents empty exponential recursion. -/
#eval let result := generatedKeysCounted 2 4 4 (OrderIso.refl (Fin 4)).toOrderEmbedding (Vector.replicate 4 0)
  (result.1.length,result.2)
#eval ((generateMasks 4 4).1.length,(generateMasks 4 4).2)
#eval ((generateMasks 10 4).1.length,(generateMasks 10 4).2)

#print axioms digitVectors_nodup
#print axioms digitVectors_sum
#print axioms makeKey_refines
#print axioms assignmentEquiv
#print axioms physicalKeys_length
#print axioms physicalKeys_sum
#print axioms physicalState_sum
#print axioms generateMasks_value
#print axioms generateMasks_work_small
#print axioms generatedKeys_length
#print axioms generateDigits_work_le
#print axioms rankCounted_value
#print axioms makeKeyCounted_value
#print axioms makeKeyCounted_work_le
#print axioms arraysCounted_work_le
#print axioms physicalKeysCounted_value
#print axioms physicalKeysCounted_work_le
#print axioms generatedKeysCounted_value
#print axioms generatedKeysCounted_work_le

end ThinMatrix.HighQueryKeys
