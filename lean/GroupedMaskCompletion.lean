import CroppedGroupedSuffix

set_option autoImplicit false

/-!
# Retained selector matrices and complete coefficient-vector outputs

This is an exact, elementary completion program on stored matrices. It
produces every coefficient in every requested output row. Its scalar/read/
write counter describes the stated indexed-array model, not bit complexity
or the missing fast rectangular multiplication algorithm. Selector formation
and source-group formation have separate storage identities below. The
annotations charge at most eight sites per added coefficient (operand reads,
addition, result write and index/control), eight per visited row, and sixteen
per retained result for the surrounding map/projection/fold traversals. Ring
addition is one scalar action here; no binary scalar price is asserted.
-/
namespace ThinMatrix.GroupedMaskCompletion
open scoped BigOperators
variable {R : Type} [CommRing R]

def sumRows {C : ℕ} : List (Bool × Vector R C) → Vector R C × ℕ
  | [] => (Vector.replicate C 0,3*C+2)
  | (b,v)::xs =>
      let rest := sumRows xs
      if b then
        (Vector.ofFn (fun c => v.get c+rest.1.get c),rest.2+8*C+8)
      else (rest.1,rest.2+8)

theorem sumRows_value {C : ℕ} (xs : List (Bool × Vector R C)) (c : Fin C) :
    (sumRows xs).1.get c = (xs.map (fun x => if x.1 then x.2.get c else 0)).sum := by
  induction xs with
  | nil => simp [sumRows]
  | cons x xs ih =>
    rcases x with ⟨b,v⟩
    cases b <;> simp [sumRows,ih]

theorem sumRows_work {C : ℕ} (xs : List (Bool × Vector R C)) :
    (sumRows xs).2 ≤ xs.length*(8*C+8)+3*C+2 := by
  induction xs with
  | nil => simp [sumRows]
  | cons x xs ih =>
    rcases x with ⟨b,v⟩
    cases b <;> simp only [sumRows,Bool.false_eq_true,↓reduceIte,List.length_cons] <;> nlinarith

/-- Read both retained operands once per pair, then sum complete vectors. -/
def runRow {S C : ℕ} (mask : Vector Bool S) (data : Vector (Vector R C) S) : Vector R C × ℕ :=
  let pairs := Vector.ofFn (fun j => (mask.get j,data.get j))
  let out := sumRows pairs.toList
  (out.1,out.2+8*S+2)

theorem runRow_value {S C : ℕ} (mask : Vector Bool S) (data : Vector (Vector R C) S) (c : Fin C) :
    (runRow mask data).1.get c = ∑ j, if mask.get j then (data.get j).get c else 0 := by
  simp only [runRow,sumRows_value,Vector.toList_ofFn,List.map_ofFn,List.sum_ofFn,Function.comp_apply]

theorem runRow_work {S C : ℕ} (mask : Vector Bool S) (data : Vector (Vector R C) S) :
    (runRow mask data).2 ≤ S*(8*C+16)+3*C+4 := by
  have h := sumRows_work (Vector.ofFn (fun j => (mask.get j,data.get j))).toList
  simp only [Vector.length_toList] at h
  dsimp only [runRow]
  nlinarith

structure Execution (C : ℕ) (R : Type*) where
  outputs : Array (Vector R C)
  work : ℕ

/-- Each row result and its counter are retained before projecting outputs. -/
def runMatrix {S C : ℕ} (selectors : Array (Vector Bool S)) (data : Vector (Vector R C) S) : Execution C R :=
  let computed := selectors.map (fun mask => runRow mask data)
  ⟨computed.map Prod.fst,computed.foldl (fun w row => w+row.2) 0+16*selectors.size+4⟩

@[simp] theorem runMatrix_size {S C : ℕ}
    (selectors : Array (Vector Bool S)) (data : Vector (Vector R C) S) :
    (runMatrix selectors data).outputs.size = selectors.size := by simp [runMatrix]

theorem runMatrix_get {S C : ℕ} (selectors : Array (Vector Bool S))
    (data : Vector (Vector R C) S) (i : ℕ) (hi : i < selectors.size) (c : Fin C) :
    ((runMatrix selectors data).outputs[i]'(by simpa using hi)).get c =
      ∑ j, if selectors[i].get j then (data.get j).get c else 0 := by
  simp only [runMatrix,Array.getElem_map,runRow_value]

theorem runMatrix_work {S C : ℕ} (selectors : Array (Vector Bool S))
    (data : Vector (Vector R C) S) :
    (runMatrix selectors data).work ≤ selectors.size*(S*(8*C+16)+3*C+20)+4 := by
  have h := BinaryArrayCosts.array_fold_cost_bound
    (selectors.map (fun mask => runRow mask data)) Prod.snd (S*(8*C+16)+3*C+4) (by
      intro row hrow
      obtain ⟨mask,_,rfl⟩ := Array.mem_map.mp hrow
      exact runRow_work mask data)
  simp only [Array.size_map] at h
  dsimp only [runMatrix]
  simp only [Array.size_map]
  nlinarith

/-- Output writes are represented by full vectors, including every batch,
cyclic slot, and formal coefficient. No coefficient-only output is used. -/
theorem output_cells {S B q F : ℕ} (selectors : Array (Vector Bool S))
    (data : Vector (Vector R (B*q*F)) S) :
    ((runMatrix selectors data).outputs.toList.map (fun row => row.toList.length)).sum =
      selectors.size*(B*q*F) := by
  simp [Vector.length_toList,runMatrix,Function.comp_def]

#print axioms sumRows_value
#print axioms sumRows_work
#print axioms runRow_value
#print axioms runRow_work
#print axioms runMatrix_size
#print axioms runMatrix_get
#print axioms runMatrix_work
#print axioms output_cells
end ThinMatrix.GroupedMaskCompletion
