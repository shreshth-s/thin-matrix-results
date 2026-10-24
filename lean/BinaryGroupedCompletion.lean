import BinaryGroupedPreparation

set_option autoImplicit false

/-! Elementary completion over retained binary cells. Every requested row
contains all coefficient slots. Partial-sum widths follow from the actual
number of stored terms and original input magnitude; they are not premises
of the eventual prepared-program contract. Boolean/indexed-control charges
are kept distinct from the binary arithmetic circuit counter. -/
namespace ThinMatrix.BinaryGroupedCompletion
open BinaryCell BinaryGroupedCoordinates BinaryGroupedPreparation GroupedPreparation
open scoped BigOperators

def addVectors {C : ℕ} (a b : Vector Cell C) : Run (Vector Cell C) :=
  tabulate a (fun c => let out := add (a.get c) (b.get c); ⟨out.value,out.bitSteps,8⟩)

theorem addVectors_view {C : ℕ} (a b : Vector Cell C) (c : Fin C) :
    view ((addVectors a b).value.get c) = view (a.get c)+view (b.get c) := by
  simp only [addVectors,tabulate_get,add_view]

theorem addVectors_bits {C W : ℕ} (a b : Vector Cell C)
    (ha : ∀ c, (view (a.get c)).natAbs.size ≤ W)
    (hb : ∀ c, (view (b.get c)).natAbs.size ≤ W) :
    (addVectors a b).bitSteps ≤ C*BackendScalarBits.backendScalarUnit W :=
  tabulate_bits a _ (fun c => add_price W _ _ (ha c) (hb c))

theorem addVectors_control {C : ℕ} (a b : Vector Cell C) :
    (addVectors a b).control ≤ 40*C+8 := by
  have h := tabulate_control a (fun c => let out := add (a.get c) (b.get c); ⟨out.value,out.bitSteps,8⟩) (fun _ => le_refl 8)
  simpa only [addVectors,show 8+32=40 by decide,Nat.mul_comm] using h

def sumRows {C : ℕ} : List (Bool × Vector Cell C) → Run (Vector Cell C)
  | [] => ⟨Vector.replicate C zero,0,3*C+2⟩
  | (b,v)::xs =>
      let rest := sumRows xs
      if b then
        let next := addVectors v rest.value
        ⟨next.value,rest.bitSteps+next.bitSteps,rest.control+next.control+8⟩
      else ⟨rest.value,rest.bitSteps,rest.control+8⟩

private def sumRowsStep {C : ℕ} (row : Bool × Vector Cell C) (rest : Run (Vector Cell C)) : Run (Vector Cell C) :=
  if row.1 then
    let next := addVectors row.2 rest.value
    ⟨next.value,rest.bitSteps+next.bitSteps,rest.control+next.control+8⟩
  else ⟨rest.value,rest.bitSteps,rest.control+8⟩

private def sumRowsTail {C : ℕ} (rows : List (Bool × Vector Cell C)) : Run (Vector Cell C) :=
  rows.reverse.foldl (fun rest row => sumRowsStep row rest) ⟨Vector.replicate C zero,0,3*C+2⟩

private theorem sumRows_foldr {C : ℕ} (rows : List (Bool × Vector Cell C)) :
    rows.foldr sumRowsStep ⟨Vector.replicate C zero,0,3*C+2⟩=sumRows rows := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
      rw [List.foldr_cons,ih]
      rcases row with ⟨b,v⟩
      rfl

@[csimp] theorem sumRows_eq_tail : @sumRows=@sumRowsTail := by
  funext C rows
  rw [←sumRows_foldr]
  exact (List.foldr_eq_foldl_reverse ..)


theorem sumRows_view {C : ℕ} (xs : List (Bool × Vector Cell C)) (c : Fin C) :
    view ((sumRows xs).value.get c) = (xs.map (fun x => if x.1 then view (x.2.get c) else 0)).sum := by
  induction xs with
  | nil => simp [sumRows]
  | cons x xs ih => rcases x with ⟨b,v⟩; cases b <;> simp [sumRows,addVectors_view,ih]

theorem sumRows_abs {C : ℕ} (A : ℕ) (xs : List (Bool × Vector Cell C))
    (hx : ∀ x ∈ xs, ∀ c, (view (x.2.get c)).natAbs ≤ A) (c : Fin C) :
    (view ((sumRows xs).value.get c)).natAbs ≤ xs.length*A := by
  induction xs with
  | nil => simp [sumRows]
  | cons x xs ih =>
    rcases x with ⟨b,v⟩
    have ht := ih (fun y hy => hx y (List.mem_cons_of_mem _ hy))
    have hh := hx (b,v) (by simp) c
    cases b
    · simp only [sumRows,Bool.false_eq_true,↓reduceIte,List.length_cons]
      nlinarith
    · simp only [sumRows,↓reduceIte,addVectors_view,List.length_cons]
      have hm := (Int.natAbs_add_le _ _).trans (Nat.add_le_add hh ht)
      nlinarith

theorem sumRows_bits {C : ℕ} (A N W : ℕ) (xs : List (Bool × Vector Cell C))
    (hlen : xs.length ≤ N) (hW : (N*A).size ≤ W)
    (hx : ∀ x ∈ xs, ∀ c, (view (x.2.get c)).natAbs ≤ A) :
    (sumRows xs).bitSteps ≤ xs.length*(C*BackendScalarBits.backendScalarUnit W) := by
  induction xs with
  | nil => simp [sumRows]
  | cons x xs ih =>
    rcases x with ⟨b,v⟩
    simp only [List.length_cons] at hlen
    have hh (c : Fin C) : (view (v.get c)).natAbs.size ≤ W :=
      (Nat.size_le_size ((hx (b,v) (by simp) c).trans (Nat.le_mul_of_pos_left A (by omega)))).trans hW
    have hr (c : Fin C) : (view ((sumRows xs).value.get c)).natAbs.size ≤ W :=
      (Nat.size_le_size ((sumRows_abs A xs (fun y hy => hx y (List.mem_cons_of_mem _ hy)) c).trans
        (Nat.mul_le_mul_right A (by omega)))).trans hW
    have ht := ih (by omega) (fun y hy => hx y (List.mem_cons_of_mem _ hy))
    have hc := addVectors_bits v (sumRows xs).value hh hr
    cases b <;> simp only [sumRows,Bool.false_eq_true,↓reduceIte,List.length_cons] <;> nlinarith

theorem sumRows_control {C : ℕ} (xs : List (Bool × Vector Cell C)) :
    (sumRows xs).control ≤ xs.length*(40*C+16)+3*C+2 := by
  induction xs with
  | nil => simp [sumRows]
  | cons x xs ih =>
    rcases x with ⟨b,v⟩
    have h := addVectors_control v (sumRows xs).value
    cases b <;> simp only [sumRows,Bool.false_eq_true,↓reduceIte,List.length_cons] <;> nlinarith

/-- Use the actual retained data length for runtime enumeration. -/
def runRow {S C : ℕ} (mask : Vector Bool S) (data : Vector (Vector Cell C) S) : Run (Vector Cell C) :=
  let pairs := ofStoredFn data (fun j => (mask.get j,data.get j))
  let out := sumRows pairs.toList
  ⟨out.value,out.bitSteps,out.control+8*data.toArray.size+2⟩

theorem runRow_view {S C : ℕ} (mask : Vector Bool S) (data : Vector (Vector Cell C) S) (c : Fin C) :
    view ((runRow mask data).value.get c) = ∑ j, if mask.get j then view ((data.get j).get c) else 0 := by
  simp only [runRow,ofStoredFn_eq,sumRows_view,Vector.toList_ofFn,List.map_ofFn,List.sum_ofFn,Function.comp_apply]

theorem runRow_abs {S C : ℕ} (A : ℕ) (mask : Vector Bool S) (data : Vector (Vector Cell C) S)
    (h : ∀ j c, (view ((data.get j).get c)).natAbs ≤ A) (c : Fin C) :
    (view ((runRow mask data).value.get c)).natAbs ≤ S*A := by
  apply (sumRows_abs A _ ?_ c).trans (by simp)
  intro x hx
  simp only [ofStoredFn_eq,Vector.toList_ofFn,List.mem_ofFn] at hx
  obtain ⟨j,rfl⟩ := hx
  exact h j

theorem runRow_bits {S C : ℕ} (A W : ℕ) (mask : Vector Bool S) (data : Vector (Vector Cell C) S)
    (hW : (S*A).size ≤ W) (h : ∀ j c, (view ((data.get j).get c)).natAbs ≤ A) :
    (runRow mask data).bitSteps ≤ S*(C*BackendScalarBits.backendScalarUnit W) := by
  apply (sumRows_bits A S W _ (by simp) hW ?_).trans (by simp)
  intro x hx
  simp only [ofStoredFn_eq,Vector.toList_ofFn,List.mem_ofFn] at hx
  obtain ⟨j,rfl⟩ := hx
  exact h j

theorem runRow_control {S C : ℕ} (mask : Vector Bool S) (data : Vector (Vector Cell C) S) :
    (runRow mask data).control ≤ S*(40*C+24)+3*C+4 := by
  have h := sumRows_control (ofStoredFn data (fun j => (mask.get j,data.get j))).toList
  simp only [Vector.length_toList] at h
  simp only [runRow,Vector.size_toArray]
  nlinarith

def runMatrix {S C : ℕ} (masks : Array (Vector Bool S)) (data : Vector (Vector Cell C) S) :
    Run (Array (Vector Cell C)) := mapArray (fun mask => runRow mask data) masks

@[simp] theorem runMatrix_size {S C : ℕ} (masks : Array (Vector Bool S)) (data : Vector (Vector Cell C) S) :
    (runMatrix masks data).value.size = masks.size := by simp [runMatrix]

theorem runMatrix_get {S C : ℕ} (masks : Array (Vector Bool S)) (data : Vector (Vector Cell C) S)
    (i : ℕ) (hi : i < masks.size) (c : Fin C) :
    view (((runMatrix masks data).value[i]'(by simpa using hi)).get c) =
      ∑ j, if masks[i].get j then view ((data.get j).get c) else 0 := by
  exact (congrArg (fun v : Vector Cell C => view (v.get c))
    (BinaryGroupedPreparation.mapArray_get (fun mask => runRow mask data) masks i hi)).trans
    (runRow_view masks[i] data c)

theorem runMatrix_bits {S C : ℕ} (A W : ℕ) (masks : Array (Vector Bool S)) (data : Vector (Vector Cell C) S)
    (hW : (S*A).size ≤ W) (h : ∀ j c, (view ((data.get j).get c)).natAbs ≤ A) :
    (runMatrix masks data).bitSteps ≤ masks.size*(S*(C*BackendScalarBits.backendScalarUnit W)) :=
  mapArray_bits _ _ (fun mask _ => runRow_bits A W mask data hW h)

theorem runMatrix_control {S C : ℕ} (masks : Array (Vector Bool S)) (data : Vector (Vector Cell C) S) :
    (runMatrix masks data).control ≤ masks.size*(S*(40*C+24)+3*C+36)+8 := by
  have h := mapArray_control (fun mask => runRow mask data) masks (fun mask _ => runRow_control mask data)
  simpa only [runMatrix,Nat.add_assoc,show 4+32=36 by decide] using h

theorem count_le_power (n r : ℕ) : CappedSubsetList.count n r ≤ 2^n := by
  rw [← CappedSubsetList.generate_length,← List.toFinset_card_of_nodup (CappedSubsetList.generate_nodup n r)]
  calc
    _ ≤ (Finset.univ : Finset (Finset (Fin n))).card := Finset.card_le_card (Finset.subset_univ _)
    _ = _ := by simp

theorem capped_width (n r A : ℕ) : (CappedSubsetList.count n r*A).size ≤ n+A.size := by
  have h := BinaryWalshBounds.natAbs_size_of_le_power_mul ((CappedSubsetList.count n r*A : ℕ) : ℤ) n A
    (by simpa only [Int.natAbs_natCast] using Nat.mul_le_mul_right A (count_le_power n r))
  simpa only [Int.natAbs_natCast] using h

#print axioms addVectors_view
#print axioms addVectors_bits
#print axioms addVectors_control
#print axioms sumRows_view
#print axioms sumRows_abs
#print axioms sumRows_bits
#print axioms sumRows_control
#print axioms runRow_view
#print axioms runRow_abs
#print axioms runRow_bits
#print axioms runRow_control
#print axioms runMatrix_size
#print axioms runMatrix_get
#print axioms runMatrix_bits
#print axioms runMatrix_control
#print axioms count_le_power
#print axioms capped_width
end ThinMatrix.BinaryGroupedCompletion
