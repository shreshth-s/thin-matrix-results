import BinaryCell
import ArrayKeys
import HighQueryKeys
import ThinMatrixBackend
import BitArraySimulation

/-!
# Stored binary HIGH tables

Every coefficient payload is a canonical signed-bit cell. Runtime updates
read five stored child vectors and add their binary cells; integer views
appear only in refinement and resource proofs. The persistent array trie
and counted key generator are the same concrete dictionaries used by the
native finite table specification.
-/
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

namespace ThinMatrix.BinaryHighTable.Projection
open StoredHighDP CacheBounds

def TrieRel {A B : Type*} (f : A → B) (t : Trie A) (s : Trie B) : Prop :=
  ∀ key, s.read key = (t.read key).map f

@[simp] theorem read_empty {A : Type*} (key : List Label) :
    (Trie.empty : Trie A).read key = none := by
  induction key with
  | nil => rfl
  | cons a key ih => simpa [Trie.read,Trie.child,Trie.children] using ih

theorem empty {A B : Type*} (f : A → B) : TrieRel f .empty .empty := by
  intro key
  simp

theorem refl {A : Type*} (t : Trie A) : TrieRel id t t := by
  intro key
  simp

theorem comp {A B C : Type*} {f : A → B} {g : B → C}
    {t : Trie A} {s : Trie B} {u : Trie C} (hf : TrieRel f t s) (hg : TrieRel g s u) :
    TrieRel (g ∘ f) t u := by
  intro key
  rw [hg key,hf key,Option.map_map]

theorem write {A B : Type*} {f : A → B} {t : Trie A} {s : Trie B}
    (h : TrieRel f t s) (key : List Label) (x : A) :
    TrieRel f (t.write key x) (s.write key (f x)) := by
  intro other
  by_cases he : other=key
  · subst other
    simp
  · rw [Trie.read_write_other s key other (f x) he,
      Trie.read_write_other t key other x he]
    exact h other

theorem write_of_eq {A B : Type*} {f : A → B} {t : Trie A} {s : Trie B}
    (h : TrieRel f t s) (key : List Label) (x : A) (y : B) (hy : y=f x) :
    TrieRel f (t.write key x) (s.write key y) := by
  subst y
  exact write h key x

theorem readCounted {A B : Type*} {f : A → B} {t : Trie A} {s : Trie B}
    (h : TrieRel f t s) (key : List Label) :
    (s.readCounted key).1 = ((t.readCounted key).1).map f := by
  simpa only [Trie.readCounted_value] using h key

theorem readCounted_work {A B : Type*} (t : Trie A) (s : Trie B) (key : List Label) :
    (s.readCounted key).2 = (t.readCounted key).2 := by simp

theorem writeCounted {A B : Type*} {f : A → B} {t : Trie A} {s : Trie B}
    (h : TrieRel f t s) (key : List Label) (x : A) :
    TrieRel f (t.writeCounted key x).1 (s.writeCounted key (f x)).1 := by
  simpa only [Trie.writeCounted_value] using write h key x

theorem writeCounted_work {A B : Type*} (t : Trie A) (s : Trie B)
    (key : List Label) (x : A) (y : B) :
    (s.writeCounted key y).2 = (t.writeCounted key x).2 := by simp

/-- Defaulted lookup also projects, provided the default is projected. -/
theorem read_getD {A B : Type*} {f : A → B} {t : Trie A} {s : Trie B}
    (h : TrieRel f t s) (key : List Label) (default : A) :
    (s.read key).getD (f default) = f ((t.read key).getD default) := by
  rw [h key]
  cases t.read key <;> rfl

theorem array_read {A B : Type*} {n : ℕ} {f : A → B} {t : Trie A} {s : Trie B}
    (h : TrieRel f t s) (key : ArrayKeys.Key n) :
    (ArrayKeys.read s key).1 = ((ArrayKeys.read t key).1).map f := by
  simpa only [ArrayKeys.read_value] using h (StoredHighDP.key (ArrayKeys.toWord key))

theorem array_read_work {A B : Type*} {n : ℕ} (t : Trie A) (s : Trie B)
    (key : ArrayKeys.Key n) : (ArrayKeys.read s key).2 = (ArrayKeys.read t key).2 := by simp

theorem array_write {A B : Type*} {n : ℕ} {f : A → B} {t : Trie A} {s : Trie B}
    (h : TrieRel f t s) (key : ArrayKeys.Key n) (x : A) :
    TrieRel f (ArrayKeys.write t key x).1 (ArrayKeys.write s key (f x)).1 := by
  simpa only [ArrayKeys.write_value] using write h (StoredHighDP.key (ArrayKeys.toWord key)) x

theorem array_write_work {A B : Type*} {n : ℕ} (t : Trie A) (s : Trie B)
    (key : ArrayKeys.Key n) (x : A) (y : B) :
    (ArrayKeys.write s key y).2 = (ArrayKeys.write t key x).2 := by simp

theorem word_writeBatch {A B : Type*} {n : ℕ} {f : A → B}
    (values : Word n → A) {t : Trie A} {s : Trie B} (h : TrieRel f t s)
    (keys : List (Word n)) :
    TrieRel f (StoredHighDP.writeBatch values t keys)
      (StoredHighDP.writeBatch (fun key => f (values key)) s keys) := by
  induction keys generalizing t s with
  | nil => exact h
  | cons key keys ih =>
      exact ih (write h (StoredHighDP.key key) (values key))


theorem array_writeBatch {A B : Type*} {n : ℕ} {f : A → B}
    (values : ArrayKeys.Key n → A) {t : Trie A} {s : Trie B} (h : TrieRel f t s)
    (keys : List (ArrayKeys.Key n)) :
    TrieRel f (ArrayKeys.writeBatchKeys values t keys)
      (ArrayKeys.writeBatchKeys (fun key => f (values key)) s keys) := by
  induction keys generalizing t s with
  | nil => exact h
  | cons key keys ih =>
      exact ih (array_write h key (values key))

theorem array_writeBatch_of_eq {A B : Type*} {n : ℕ} {f : A → B}
    (values : ArrayKeys.Key n → A) (out : ArrayKeys.Key n → B)
    {t : Trie A} {s : Trie B} (h : TrieRel f t s)
    (hv : ∀ key, out key=f (values key)) (keys : List (ArrayKeys.Key n)) :
    TrieRel f (ArrayKeys.writeBatchKeys values t keys) (ArrayKeys.writeBatchKeys out s keys) := by
  have he : out=fun key => f (values key) := funext hv
  rw [he]
  exact array_writeBatch values h keys

/-- Vector-valued lookup specialization used by stored polynomial tables. -/
theorem lookup_vector {A B : Type*} [Zero A] [Zero B] {q n : ℕ} (f : A → B)
    (hf : f 0=0) {t : Trie (Vector A q)} {s : Trie (Vector B q)}
    (h : TrieRel (fun v : Vector A q => v.map f) t s) (key : Word n) :
    StoredHighDP.lookup s key = (StoredHighDP.lookup t key).map f := by
  have hz : (StoredHighDP.zeroVector (R:=A) q).map f = StoredHighDP.zeroVector (R:=B) q := by
    apply Vector.ext
    intro i hi
    simp [StoredHighDP.zeroVector,hf]
  change (s.read (StoredHighDP.key key)).getD (StoredHighDP.zeroVector q) =
    ((t.read (StoredHighDP.key key)).getD (StoredHighDP.zeroVector q)).map f
  rw [← hz]
  exact read_getD h (StoredHighDP.key key) (StoredHighDP.zeroVector q)

end ThinMatrix.BinaryHighTable.Projection

namespace ThinMatrix.BinaryHighTable.Bounds
open StoredHighDP CacheBounds

abbrev BV (q : ℕ) := Vector BinaryArrayFFT.Integer q

def VectorBound {q : ℕ} (A : ℕ) (v : BV q) : Prop :=
  ∀ j, (v.get j).view.natAbs ≤ A

def TableBound {q : ℕ} (A : ℕ) (t : Trie (BV q)) : Prop :=
  ∀ key v, t.read key = some v → VectorBound A v

def zeroVector (q : ℕ) : BV q := Vector.replicate q BinaryArrayFFT.zeroInteger

def lookup {q : ℕ} (t : Trie (BV q)) (key : List Label) : BV q :=
  (t.read key).getD (zeroVector q)

@[simp] theorem read_empty {A : Type*} (key : List Label) :
    (Trie.empty : Trie A).read key = none := Projection.read_empty key

theorem vector_mono {q A B : ℕ} {v : BV q} (h : VectorBound A v) (hAB : A ≤ B) :
    VectorBound B v := fun j => (h j).trans hAB

theorem empty (q A : ℕ) : TableBound A (Trie.empty : Trie (BV q)) := by
  intro key v hv
  rw [read_empty] at hv
  contradiction

theorem table_mono {q A B : ℕ} {t : Trie (BV q)} (h : TableBound A t) (hAB : A ≤ B) :
    TableBound B t := fun key v hv => vector_mono (h key v hv) hAB

theorem write {q A : ℕ} {t : Trie (BV q)} (h : TableBound A t)
    (key : List Label) (x : BV q) (hx : VectorBound A x) :
    TableBound A (t.write key x) := by
  intro other v hv
  by_cases he : other=key
  · subst other
    rw [Trie.read_write_same] at hv
    cases hv
    exact hx
  · rw [Trie.read_write_other t key other x he] at hv
    exact h other v hv

theorem writeCounted {q A : ℕ} {t : Trie (BV q)} (h : TableBound A t)
    (key : List Label) (x : BV q) (hx : VectorBound A x) :
    TableBound A (t.writeCounted key x).1 := by
  simpa only [Trie.writeCounted_value] using write h key x hx

theorem zeroVector_bound (q A : ℕ) : VectorBound A (zeroVector q) := by
  intro j
  simp [zeroVector,BinaryArrayFFT.zeroInteger_view]

theorem option_getD_bound {q A : ℕ} (o : Option (BV q))
    (h : ∀ v, o=some v → VectorBound A v) (default : BV q) (hd : VectorBound A default) :
    VectorBound A (o.getD default) := by
  cases o with
  | none => exact hd
  | some v => exact h v rfl

theorem lookup_bound {q A : ℕ} {t : Trie (BV q)} (h : TableBound A t) (key : List Label) :
    VectorBound A (lookup t key) :=
  option_getD_bound (t.read key) (h key) _ (zeroVector_bound q A)

theorem array_read_bound {q n A : ℕ} {t : Trie (BV q)} (h : TableBound A t)
    (key : ArrayKeys.Key n) :
    VectorBound A ((ArrayKeys.read t key).1.getD (zeroVector q)) := by
  rw [ArrayKeys.read_value]
  exact lookup_bound h _

theorem array_write_bound {q n A : ℕ} {t : Trie (BV q)} (h : TableBound A t)
    (key : ArrayKeys.Key n) (x : BV q) (hx : VectorBound A x) :
    TableBound A (ArrayKeys.write t key x).1 := by
  simpa only [ArrayKeys.write_value] using write h (StoredHighDP.key (ArrayKeys.toWord key)) x hx

/-- A batch may reuse one fixed snapshot to compute its already bounded
new vectors. Only the written vector values enter this storage invariant. -/
theorem array_writeBatch_bound {q n A : ℕ} (values : ArrayKeys.Key n → BV q)
    {t : Trie (BV q)} (h : TableBound A t) (keys : List (ArrayKeys.Key n))
    (hv : ∀ key ∈ keys, VectorBound A (values key)) :
    TableBound A (ArrayKeys.writeBatchKeys values t keys) := by
  induction keys generalizing t with
  | nil => exact h
  | cons key keys ih =>
      apply ih (array_write_bound h key (values key) (hv key (by simp)))
      intro a ha
      exact hv a (by simp [ha])

theorem array_writeBatchCounted_bound {q n A : ℕ}
    (values : ArrayKeys.Key n → StoredHighDP.BaseResult BinaryArrayFFT.Integer q)
    {t : Trie (BV q)} (h : TableBound A t) (keys : List (ArrayKeys.Key n))
    (hv : ∀ key ∈ keys, VectorBound A (values key).1) :
    TableBound A (ArrayKeys.writeBatchKeysCounted values t keys).1 := by
  rw [ArrayKeys.writeBatchKeysCounted_value]
  exact array_writeBatch_bound (fun key => (values key).1) h keys hv

/-- Exact monotonicity of natural binary size; no extra guard unit is needed. -/
theorem natAbs_size_le {A : ℕ} {z : ℤ} (h : z.natAbs ≤ A) : z.natAbs.size ≤ A.size :=
  Nat.size_le_size h

theorem vector_size_bound {q A : ℕ} {v : BV q} (h : VectorBound A v) (j : Fin q) :
    (v.get j).view.natAbs.size ≤ A.size := natAbs_size_le (h j)

theorem table_read_size_bound {q A : ℕ} {t : Trie (BV q)} (h : TableBound A t)
    (key : List Label) (v : BV q) (hv : t.read key=some v) (j : Fin q) :
    (v.get j).view.natAbs.size ≤ A.size := vector_size_bound (h key v hv) j

theorem lookup_size_bound {q A : ℕ} {t : Trie (BV q)} (h : TableBound A t)
    (key : List Label) (j : Fin q) :
    ((lookup t key).get j).view.natAbs.size ≤ A.size := vector_size_bound (lookup_bound h key) j

end ThinMatrix.BinaryHighTable.Bounds

namespace ThinMatrix.BinaryHighTable
open scoped BigOperators
open CacheBounds HighBoxDP StoredHighDP

abbrev Cell := BinaryArrayFFT.Integer
abbrev Coefficients (q : ℕ) := Vector Cell q
abbrev Table (q : ℕ) := Trie (Coefficients q)
abbrev Base (L q : ℕ) := LeafWord (2*L) → Coefficients q × ℕ

def vectorView {q : ℕ} (v : Coefficients q) : Vector ℤ q := v.map BinaryCell.view

@[simp] theorem vectorView_get {q : ℕ} (v : Coefficients q) (j : Fin q) :
    (vectorView v).get j = (v.get j).view := by simp [vectorView,BinaryCell.view]

@[simp] theorem vectorView_zero (q : ℕ) : vectorView (BinaryCell.vectorZero q) = StoredHighDP.zeroVector q := by
  apply Vector.ext
  intro j hj
  simp [vectorView,BinaryCell.vectorZero,StoredHighDP.zeroVector]

@[simp] theorem vectorAdd_get_view {q : ℕ} (a b : Coefficients q) (j : Fin q) :
    ((BinaryCell.vectorAdd a b).value.get j).view = (a.get j).view+(b.get j).view :=
  BinaryCell.vectorAdd_view a b j

def sumVectors {q : ℕ} : List (Coefficients q) → BinaryCell.Result (Coefficients q)
  | [] => ⟨BinaryCell.vectorZero q,q⟩
  | v::vs =>
      let tail := sumVectors vs
      let next := BinaryCell.vectorAdd v tail.value
      ⟨next.value,tail.bitSteps+next.bitSteps+3*q⟩

theorem sumVectors_view {q : ℕ} (vs : List (Coefficients q)) (j : Fin q) :
    ((sumVectors vs).value.get j).view = (vs.map (fun v => (v.get j).view)).sum := by
  induction vs with
  | nil => simp [sumVectors,BinaryCell.vectorZero,BinaryCell.zero]
  | cons v vs ih =>
      simp only [sumVectors,vectorAdd_get_view,List.map_cons,List.sum_cons,ih]

lemma vectorAdd_price {q : ℕ} (W : ℕ) (a b : Coefficients q)
    (ha : ∀ j, (a.get j).view.natAbs.size ≤ W) (hb : ∀ j, (b.get j).view.natAbs.size ≤ W) :
    (BinaryCell.vectorAdd a b).bitSteps ≤ q*BackendScalarBits.backendScalarUnit W := by
  let rows := Vector.ofFn (fun i => BinaryCell.add (a.get i) (b.get i))
  have hh := List.sum_le_card_nsmul (rows.toList.map (fun r => r.bitSteps))
    (BackendScalarBits.backendScalarUnit W) (by
      intro x hx
      obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hx
      have hv' : ∃ j, v=BinaryCell.add (a.get j) (b.get j) := by
        simpa only [rows,Vector.toList_ofFn,List.mem_ofFn,eq_comm] using hv
      obtain ⟨j,rfl⟩ := hv'
      exact BinaryCell.add_price W _ _ (ha j) (hb j))
  simpa only [BinaryCell.vectorAdd,List.length_map,Vector.length_toList,smul_eq_mul,rows] using hh

def VectorBound {q : ℕ} (A : ℕ) (v : Coefficients q) : Prop := ∀ j, (v.get j).view.natAbs ≤ A

theorem sumVectors_bound {q : ℕ} (A : ℕ) (vs : List (Coefficients q))
    (hv : ∀ v∈vs, VectorBound A v) : VectorBound (vs.length*A) (sumVectors vs).value := by
  intro j
  induction vs with
  | nil => simp [sumVectors,BinaryCell.vectorZero,BinaryCell.zero]
  | cons v vs ih =>
      have htail := ih (fun x hx => hv x (List.mem_cons_of_mem v hx))
      have hhead := hv v (by simp) j
      simp only [sumVectors,vectorAdd_get_view,List.length_cons,Nat.succ_mul]
      simpa only [Nat.add_comm] using (Int.natAbs_add_le _ _).trans (Nat.add_le_add hhead htail)

def arithmeticUnit (W : ℕ) : ℕ := BackendScalarBits.backendScalarUnit W+8

theorem arithmeticUnit_pos (W : ℕ) : 1 ≤ arithmeticUnit W := by unfold arithmeticUnit; omega

theorem sumVectors_price_width {q : ℕ} (W A : ℕ) (vs : List (Coefficients q))
    (hlen : vs.length ≤ 5) (hv : ∀ v∈vs, VectorBound A v) (hW : (5*A).size ≤ W) :
    (sumVectors vs).bitSteps ≤ vs.length*q*(BackendScalarBits.backendScalarUnit W+3)+q := by
  induction vs with
  | nil => simp [sumVectors]
  | cons v vs ih =>
      simp only [List.length_cons] at hlen
      have htail := ih (by omega)
        (fun x hx => hv x (List.mem_cons_of_mem v hx))
      have htb := sumVectors_bound A vs (fun x hx => hv x (List.mem_cons_of_mem v hx))
      have hleft : ∀ j, (v.get j).view.natAbs.size ≤ W := by
        intro j
        exact (Nat.size_le_size ((hv v (by simp) j).trans (by omega : A ≤ 5*A))).trans hW
      have hright : ∀ j, ((sumVectors vs).value.get j).view.natAbs.size ≤ W := by
        intro j
        exact (Nat.size_le_size ((htb j).trans (Nat.mul_le_mul_right A (by omega)))).trans hW
      have hadd := vectorAdd_price W v (sumVectors vs).value hleft hright
      simp only [sumVectors,List.length_cons]
      nlinarith

structure Result (α : Type*) where
  value : α
  work : ℕ
  sites : ℕ
  baseWork : ℕ

def nativeBase {L q : ℕ} (base : Base L q) : LeafWord (2*L) → StoredHighDP.BaseResult ℤ q :=
  fun v => (vectorView (base v).1,0)

/-- Five child handles are stored before the binary coefficient loop. -/
def node {L q : ℕ} (base : Base L q) (table : Table q) (a : ArrayKeys.Key (2*L)) : Result (Coefficients q) :=
  let w := ArrayKeys.toWord a
  if h : StoredHighDP.height w = 0 then
    let leaf := baseLeaf w (noStars_of_count_zero w (by simpa [StoredHighDP.height_eq] using h))
    let value := base leaf
    ⟨value.1,value.2+2*L,2*L,value.2⟩
  else
    let position := finalStar w h
    let reads := Vector.ofFn (fun j : Fin 5 =>
      let child := ArrayKeys.put a position ⟨j.val,by omega⟩
      let result := ArrayKeys.read table child
      (result.1,result.2+2*L))
    let children := Vector.ofFn (fun j : Fin 5 => (reads.get j).1.getD (BinaryCell.vectorZero q))
    let value := sumVectors children.toList
    ⟨value.value,(∑ j : Fin 5, (reads.get j).2)+value.bitSteps+4*L+5*q+5,
      5*(4*L+1)+10*q+4*L,0⟩

lemma put_replace {n : ℕ} (a : ArrayKeys.Key n) (i : Fin n) (j : Fin 5) :
    ArrayKeys.toWord (ArrayKeys.put a i ⟨j.val,by omega⟩) = replace (ArrayKeys.toWord a) i j := by
  rw [ArrayKeys.toWord_put]
  rfl

lemma node_refines {L q : ℕ} (base : Base L q) (binary : Table q)
    (native : Trie (Vector ℤ q)) (h : Projection.TrieRel vectorView binary native)
    (a : ArrayKeys.Key (2*L)) :
    vectorView (node base binary a).value = StoredHighDP.node (fun v => vectorView (base v).1) native (ArrayKeys.toWord a) := by
  unfold node StoredHighDP.node
  dsimp only
  split_ifs with hz
  · rfl
  · apply Vector.ext
    intro i hi
    let j : Fin q := ⟨i,hi⟩
    change (vectorView (sumVectors _).value).get j = _
    rw [vectorView_get,sumVectors_view]
    simp only [Vector.toList_ofFn,List.map_ofFn,List.sum_ofFn,Vector.get_ofFn]
    unfold StoredHighDP.addFive
    simp only [Vector.getElem_ofFn,Vector.get_ofFn,Function.comp_def]
    change (∑ a : Fin 5, (_ : ℤ)) = ∑ a : Fin 5, (_ : ℤ)
    apply Finset.sum_congr rfl
    intro b _
    have hr := Projection.read_getD h
      (StoredHighDP.key (replace (ArrayKeys.toWord a) (finalStar (ArrayKeys.toWord a) hz) b))
      (BinaryCell.vectorZero q)
    rw [vectorView_zero] at hr
    have hh := congrArg (fun v : Vector ℤ q => v.get j) hr
    simpa only [StoredHighDP.lookup,ArrayKeys.read_value,put_replace,vectorView_get] using hh.symm

lemma node_sites {L q : ℕ} (base : Base L q) (binary : Table q)
    (native : Trie (Vector ℤ q)) (a : ArrayKeys.Key (2*L)) :
    (node base binary a).sites = (StoredHighDP.nodeCounted (nativeBase base) native (ArrayKeys.toWord a)).2 := by
  unfold node StoredHighDP.nodeCounted
  dsimp only
  split_ifs
  · simp [nativeBase]
  · simp only [Vector.get_ofFn,Trie.readCounted_work,key_length,Finset.sum_const,
      Finset.card_univ,Fintype.card_fin,smul_eq_mul]
    omega


lemma node_bound {L q : ℕ} (base : Base L q) (table : Table q) (A : ℕ)
    (hb : ∀ v, VectorBound A (base v).1) (ht : Bounds.TableBound A table)
    (a : ArrayKeys.Key (2*L)) : VectorBound (5*A) (node base table a).value := by
  unfold node
  dsimp only
  split_ifs with hz
  · exact Bounds.vector_mono (hb _) (by omega)
  · apply Bounds.vector_mono (sumVectors_bound A _ ?_) (by simp)
    intro v hv
    have hv' : ∃ j : Fin 5, v=(ArrayKeys.read table (ArrayKeys.put a (finalStar (ArrayKeys.toWord a) hz) ⟨j.val,by omega⟩)).1.getD
        (BinaryCell.vectorZero q) := by
      simpa only [Vector.toList_ofFn,List.mem_ofFn,Vector.get_ofFn,eq_comm] using hv
    obtain ⟨j,rfl⟩ := hv'
    exact Bounds.array_read_bound ht _

lemma node_work {L q : ℕ} (base : Base L q) (table : Table q) (A W : ℕ)
    (_hb : ∀ v, VectorBound A (base v).1) (ht : Bounds.TableBound A table)
    (hW : (5*A).size ≤ W) (a : ArrayKeys.Key (2*L)) :
    (node base table a).work ≤ (node base table a).sites*arithmeticUnit W+(node base table a).baseWork := by
  have hunit := arithmeticUnit_pos W
  unfold node
  dsimp only
  split_ifs with hz
  · nlinarith
  · let children : Vector (Coefficients q) 5 := Vector.ofFn (fun j =>
      (ArrayKeys.read table (ArrayKeys.put a (finalStar (ArrayKeys.toWord a) hz) ⟨j.val,by omega⟩)).1.getD
        (BinaryCell.vectorZero q))
    have hc : ∀ v∈children.toList, VectorBound A v := by
      intro v hv
      have hv' : ∃ j : Fin 5, v=(ArrayKeys.read table (ArrayKeys.put a (finalStar (ArrayKeys.toWord a) hz)
          ⟨j.val,by omega⟩)).1.getD (BinaryCell.vectorZero q) := by
        simpa only [children,Vector.toList_ofFn,List.mem_ofFn,Vector.get_ofFn,eq_comm] using hv
      obtain ⟨j,rfl⟩ := hv'
      exact Bounds.array_read_bound ht _
    have hs := sumVectors_price_width W A children.toList (by simp) hc hW
    simp only [Vector.length_toList] at hs
    simp only [Vector.get_ofFn,ArrayKeys.read_work,Finset.sum_const,Finset.card_univ,
      Fintype.card_fin,smul_eq_mul]
    change 5*(2*(2*L)+1+2*L)+(sumVectors children.toList).bitSteps+4*L+5*q+5 ≤ _
    unfold arithmeticUnit
    nlinarith

/-- Payload and all counters are retained together; callbacks see the
fixed previous-layer snapshot, never the evolving dictionary. -/
def writeBatch {n q : ℕ} (values : ArrayKeys.Key n → Result (Coefficients q)) :
    Table q → List (ArrayKeys.Key n) → Result (Table q)
  | table, [] => ⟨table,0,0,0⟩
  | table, a::as =>
      let value := values a
      let written := ArrayKeys.write table a value.value
      let rest := writeBatch values written.1 as
      ⟨rest.value,value.work+written.2+q+rest.work,
        value.sites+written.2+q+rest.sites,value.baseWork+rest.baseWork⟩

lemma writeBatch_refines {n q : ℕ} (values : ArrayKeys.Key n → Result (Coefficients q))
    (nativeValues : ArrayKeys.Key n → StoredHighDP.BaseResult ℤ q)
    (binary : Table q) (native : Trie (Vector ℤ q))
    (ht : Projection.TrieRel vectorView binary native)
    (hv : ∀ a, vectorView (values a).value = (nativeValues a).1)
    (as : List (ArrayKeys.Key n)) :
    Projection.TrieRel vectorView (writeBatch values binary as).value
      (ArrayKeys.writeBatchKeysCounted nativeValues native as).1 := by
  induction as generalizing binary native with
  | nil => exact ht
  | cons a as ih =>
      simp only [writeBatch,ArrayKeys.writeBatchKeysCounted]
      apply ih
      have hh := Projection.array_write ht a (values a).value
      rw [hv a] at hh
      exact hh

lemma writeBatch_sites {n q : ℕ} (values : ArrayKeys.Key n → Result (Coefficients q))
    (nativeValues : ArrayKeys.Key n → StoredHighDP.BaseResult ℤ q)
    (binary : Table q) (native : Trie (Vector ℤ q))
    (hv : ∀ a, (values a).sites = (nativeValues a).2)
    (as : List (ArrayKeys.Key n)) :
    (writeBatch values binary as).sites = (ArrayKeys.writeBatchKeysCounted nativeValues native as).2 := by
  induction as generalizing binary native with
  | nil => rfl
  | cons a as ih =>
      simp only [writeBatch,ArrayKeys.writeBatchKeysCounted,ArrayKeys.write_work,hv]
      rw [ih (ArrayKeys.write binary a (values a).value).1 (ArrayKeys.write native a (nativeValues a).1).1]

lemma writeBatch_work {n q : ℕ} (values : ArrayKeys.Key n → Result (Coefficients q))
    (table : Table q) (as : List (ArrayKeys.Key n)) (U : ℕ) (hU : 1 ≤ U)
    (hv : ∀ a∈as, (values a).work ≤ (values a).sites*U+(values a).baseWork) :
    (writeBatch values table as).work ≤ (writeBatch values table as).sites*U+
      (writeBatch values table as).baseWork := by
  induction as generalizing table with
  | nil => simp [writeBatch]
  | cons a as ih =>
      have hrest := ih (ArrayKeys.write table a (values a).value).1
        (fun x hx => hv x (List.mem_cons_of_mem a hx))
      have hhead := hv a (by simp)
      have hmetadata : (ArrayKeys.write table a (values a).value).2+q ≤
          ((ArrayKeys.write table a (values a).value).2+q)*U := Nat.le_mul_of_pos_right _ hU
      simp only [writeBatch]
      nlinarith

lemma writeBatch_bound {n q : ℕ} (values : ArrayKeys.Key n → Result (Coefficients q))
    (table : Table q) (as : List (ArrayKeys.Key n)) (A : ℕ)
    (ht : Bounds.TableBound A table) (hv : ∀ a∈as, VectorBound A (values a).value) :
    Bounds.TableBound A (writeBatch values table as).value := by
  induction as generalizing table with
  | nil => exact ht
  | cons a as ih =>
      apply ih (ArrayKeys.write table a (values a).value).1
        (Bounds.array_write_bound ht a (values a).value (hv a (by simp)))
      intro x hx
      exact hv x (List.mem_cons_of_mem a hx)

/-- The same six-way balanced/ordered generator is retained explicitly. -/
def runLayer {L m t q : ℕ} (base : Base L q) (k : ℕ) (table : Table q) : Result (Table q) :=
  let generated := ArrayKeys.generateCounted (List.finRange 6) (ArrayKeys.highTest L m t) (2*L)
  let states := generated.keys.filter (fun a => decide (height (ArrayKeys.toWord a) = k))
  let batch := writeBatch (node base table) table states
  ⟨batch.value,generated.work+(2*L+1)*generated.keys.length+batch.work,
    generated.work+(2*L+1)*generated.keys.length+batch.sites,batch.baseWork⟩

lemma runLayer_refines {L m t q : ℕ} (base : Base L q) (k : ℕ)
    (binary : Table q) (native : Trie (Vector ℤ q)) (ht : Projection.TrieRel vectorView binary native) :
    Projection.TrieRel vectorView (runLayer (m := m) (t := t) base k binary).value
      (ArrayKeys.highRunLayerCounted (m := m) (t := t) (nativeBase base) k native).1 := by
  unfold runLayer ArrayKeys.highRunLayerCounted
  dsimp only
  apply writeBatch_refines _ _ _ _ ht
  intro a
  rw [StoredHighDP.nodeCounted_value]
  exact node_refines base binary native ht a

lemma runLayer_sites {L m t q : ℕ} (base : Base L q) (k : ℕ)
    (binary : Table q) (native : Trie (Vector ℤ q)) :
    (runLayer (m := m) (t := t) base k binary).sites =
      (ArrayKeys.highRunLayerCounted (m := m) (t := t) (nativeBase base) k native).2 := by
  unfold runLayer ArrayKeys.highRunLayerCounted
  dsimp only
  rw [writeBatch_sites _ _ _ _ (fun a => node_sites base binary native a)]

lemma runLayer_work {L m t q : ℕ} (base : Base L q) (k : ℕ) (table : Table q) (A W : ℕ)
    (hb : ∀ v, VectorBound A (base v).1) (ht : Bounds.TableBound A table) (hW : (5*A).size ≤ W) :
    (runLayer (m := m) (t := t) base k table).work ≤
      (runLayer (m := m) (t := t) base k table).sites*arithmeticUnit W+
        (runLayer (m := m) (t := t) base k table).baseWork := by
  have hh := writeBatch_work (node base table) table
    ((ArrayKeys.generateCounted (List.finRange 6) (ArrayKeys.highTest L m t) (2*L)).keys.filter
      (fun a => decide (height (ArrayKeys.toWord a) = k))) (arithmeticUnit W)
    (arithmeticUnit_pos W) (fun a _ => node_work base table A W hb ht hW a)
  have hu := arithmeticUnit_pos W
  have hm := Nat.le_mul_of_pos_right
    ((ArrayKeys.generateCounted (List.finRange 6) (ArrayKeys.highTest L m t) (2*L)).work+
      (2*L+1)*(ArrayKeys.generateCounted (List.finRange 6) (ArrayKeys.highTest L m t) (2*L)).keys.length) hu
  unfold runLayer
  dsimp only
  nlinarith

lemma runLayer_bound {L m t q : ℕ} (base : Base L q) (k : ℕ) (table : Table q) (A : ℕ)
    (hb : ∀ v, VectorBound A (base v).1) (ht : Bounds.TableBound A table) :
    Bounds.TableBound (5*A) (runLayer (m := m) (t := t) base k table).value := by
  unfold runLayer
  dsimp only
  apply writeBatch_bound
  · exact Bounds.table_mono ht (by omega)
  · intro a _
    exact node_bound base table A hb ht a


/-- Layers keep the previous persistent snapshot and its counters once. -/
def execute {L m t q : ℕ} (base : Base L q) : ℕ → Result (Table q)
  | 0 => ⟨.empty,0,0,0⟩
  | k+1 =>
      let previous := execute (m := m) (t := t) base k
      let next := runLayer (m := m) (t := t) base k previous.value
      ⟨next.value,previous.work+next.work,previous.sites+next.sites,previous.baseWork+next.baseWork⟩

lemma execute_refines {L m t q : ℕ} (base : Base L q) (k : ℕ) :
    Projection.TrieRel vectorView (execute (m := m) (t := t) base k).value
      (ArrayKeys.highExecuteCounted (m := m) (t := t) (nativeBase base) k).1 := by
  induction k with
  | zero => exact Projection.empty _
  | succ k ih =>
      simp only [execute,ArrayKeys.highExecuteCounted]
      exact runLayer_refines base k _ _ ih

lemma execute_sites {L m t q : ℕ} (base : Base L q) (k : ℕ) :
    (execute (m := m) (t := t) base k).sites =
      (ArrayKeys.highExecuteCounted (m := m) (t := t) (nativeBase base) k).2 := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [execute,ArrayKeys.highExecuteCounted]
      rw [ih,runLayer_sites base k _ (ArrayKeys.highExecuteCounted (m := m) (t := t) (nativeBase base) k).1]

lemma execute_bound {L m t q : ℕ} (base : Base L q) (A : ℕ)
    (hb : ∀ v, VectorBound A (base v).1) (k : ℕ) :
    Bounds.TableBound (5^k*A) (execute (m := m) (t := t) base k).value := by
  induction k with
  | zero => exact Bounds.empty _ _
  | succ k ih =>
      have ha : A ≤ 5^k*A := Nat.le_mul_of_pos_left _ (Nat.one_le_pow k 5 (by omega))
      have hbase : ∀ v, VectorBound (5^k*A) (base v).1 := fun v => Bounds.vector_mono (hb v) ha
      have hn := runLayer_bound (m := m) (t := t) base k _ (5^k*A) hbase ih
      simpa only [execute,pow_succ,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using hn

/-- Every arithmetic operand has a proved width determined by the actual
base magnitude and number of stored layers. No unit-cost integer arithmetic
or new integer encoding occurs in this comparison. -/
lemma execute_work {L m t q : ℕ} (base : Base L q) (A K : ℕ)
    (hb : ∀ v, VectorBound A (base v).1) :
    (execute (m := m) (t := t) base K).work ≤
      (execute (m := m) (t := t) base K).sites*arithmeticUnit (5^K*A).size+
        (execute (m := m) (t := t) base K).baseWork := by
  have hh (k : ℕ) (hk : k ≤ K) :
      (execute (m := m) (t := t) base k).work ≤
        (execute (m := m) (t := t) base k).sites*arithmeticUnit (5^K*A).size+
          (execute (m := m) (t := t) base k).baseWork := by
    induction k with
    | zero => simp [execute]
    | succ k ih =>
        have hprev := ih (by omega)
        have ht := execute_bound (m := m) (t := t) base A hb k
        have ha : A ≤ 5^k*A := Nat.le_mul_of_pos_left _ (Nat.one_le_pow k 5 (by omega))
        have hbase : ∀ v, VectorBound (5^k*A) (base v).1 := fun v => Bounds.vector_mono (hb v) ha
        have hmag : 5*(5^k*A) ≤ 5^K*A := by
          have hp := Nat.mul_le_mul_right A (Nat.pow_le_pow_right (by omega : 1 ≤ 5) hk)
          simpa only [pow_succ,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using hp
        have hnext := runLayer_work (m := m) (t := t) base k _ (5^k*A) (5^K*A).size
          hbase ht (Nat.size_le_size hmag)
        simp only [execute]
        nlinarith
  exact hh K le_rfl

/-- The returned site counter is exactly the existing full-coefficient DP
counter with the separately retained base-call costs set to zero. -/
lemma execute_sites_le_bases {L m t q : ℕ} (base : Base L q) :
    (execute (m := m) (t := t) base (2*L+1)).sites ≤
      (2*L+1)^2*ArrayKeys.highLayerFactor L q 0*Fintype.card (BaseStates L m t) := by
  rw [execute_sites]
  exact ArrayKeys.highExecuteCounted_work_le_bases (nativeBase base) 0 (fun _ => le_rfl)

def lookup {n q : ℕ} (table : Table q) (a : ArrayKeys.Key n) : Coefficients q :=
  (ArrayKeys.read table a).1.getD (BinaryCell.vectorZero q)

lemma lookup_view {n q : ℕ} (binary : Table q) (native : Trie (Vector ℤ q))
    (ht : Projection.TrieRel vectorView binary native) (a : ArrayKeys.Key n) :
    vectorView (lookup binary a) = StoredHighDP.lookup native (ArrayKeys.toWord a) := by
  have hh := Projection.read_getD ht (StoredHighDP.key (ArrayKeys.toWord a)) (BinaryCell.vectorZero q)
  rw [vectorView_zero] at hh
  simpa only [lookup,ArrayKeys.read_value,StoredHighDP.lookup] using hh.symm

/-- Arbitrary selected targets read one stored binary coefficient; all q
coefficients were formed and retained in the table. -/
lemma execute_complete {L m t q : ℕ} (base : Base L q) (w : States L m t) (j : Fin q) :
    ((lookup (execute (m := m) (t := t) base (2*L+1)).value (ArrayKeys.materialize w.val)).get j).view =
      boxValue w.val (fun v => ((base v).1.get j).view) := by
  have hh := lookup_view _ _ (execute_refines (m := m) (t := t) base (2*L+1)) (ArrayKeys.materialize w.val)
  have hc := congrArg (fun v : Vector ℤ q => v.get j) hh
  rw [vectorView_get,ArrayKeys.toWord_materialize,ArrayKeys.highExecuteCounted_value,
    ArrayKeys.highExecute_refine,StoredHighDP.execute_complete] at hc
  change _ = boxValue w.val (fun v => (vectorView (base v).1).get j) at hc
  simpa only [vectorView_get] using hc

lemma node_baseWork_le {L q : ℕ} (base : Base L q) (table : Table q) (B : ℕ)
    (hb : ∀ v, (base v).2 ≤ B) (a : ArrayKeys.Key (2*L)) : (node base table a).baseWork ≤ B := by
  unfold node
  dsimp only
  split_ifs
  · exact hb _
  · exact Nat.zero_le _

lemma writeBatch_baseWork {n q : ℕ} (values : ArrayKeys.Key n → Result (Coefficients q))
    (table : Table q) (as : List (ArrayKeys.Key n)) (B : ℕ) (hb : ∀ a∈as, (values a).baseWork ≤ B) :
    (writeBatch values table as).baseWork ≤ as.length*B := by
  induction as generalizing table with
  | nil => simp [writeBatch]
  | cons a as ih =>
      have hrest := ih (ArrayKeys.write table a (values a).value).1
        (fun x hx => hb x (List.mem_cons_of_mem a hx))
      have hhead := hb a (by simp)
      simp only [writeBatch,List.length_cons,Nat.succ_mul]
      omega

lemma runLayer_baseWork {L m t q : ℕ} (base : Base L q) (k : ℕ) (table : Table q) (B : ℕ)
    (hb : ∀ v, (base v).2 ≤ B) :
    (runLayer (m := m) (t := t) base k table).baseWork ≤ Fintype.card (States L m t)*B := by
  have hh := writeBatch_baseWork (node base table) table
    ((ArrayKeys.generateCounted (List.finRange 6) (ArrayKeys.highTest L m t) (2*L)).keys.filter
      (fun a => decide (height (ArrayKeys.toWord a) = k))) B
    (fun a _ => node_baseWork_le base table B hb a)
  have hlen : (ArrayKeys.generateCounted (List.finRange 6) (ArrayKeys.highTest L m t) (2*L)).keys.length ≤
      Fintype.card (States L m t) := by
    rw [ArrayKeys.generateCounted_keys,ArrayKeys.high_generateKeys_eq,ArrayKeys.generate_length]
    exact StoredHighDP.generate_length_le_states L m t _ le_rfl
  have hf := List.length_filter_le (fun a : ArrayKeys.Key (2*L) => decide (height (ArrayKeys.toWord a) = k))
    (ArrayKeys.generateCounted (List.finRange 6) (ArrayKeys.highTest L m t) (2*L)).keys
  exact hh.trans (Nat.mul_le_mul_right B (hf.trans hlen))

lemma execute_baseWork {L m t q : ℕ} (base : Base L q) (B : ℕ) (hb : ∀ v, (base v).2 ≤ B) (k : ℕ) :
    (execute (m := m) (t := t) base k).baseWork ≤ k*Fintype.card (States L m t)*B := by
  induction k with
  | zero => simp [execute]
  | succ k ih =>
      have hn := runLayer_baseWork (m := m) (t := t) base k (execute (m := m) (t := t) base k).value B hb
      simp only [execute]
      nlinarith

lemma execute_baseWork_le_bases {L m t q : ℕ} (base : Base L q) (B : ℕ) (hb : ∀ v, (base v).2 ≤ B) :
    (execute (m := m) (t := t) base (2*L+1)).baseWork ≤
      (2*L+1)^2*Fintype.card (BaseStates L m t)*B := by
  have hh := execute_baseWork (m := m) (t := t) base B hb (2*L+1)
  have hc := Nat.mul_le_mul_right B (Nat.mul_le_mul_left (2*L+1) (stateCount_le_baseCount L m t))
  nlinarith


lemma multiplication_size (q A : ℕ) (a b : Array Cell) :
    (BinaryArrayFFT.multiplication q A a b).value.size = q := by
  simp only [BinaryArrayFFT.multiplication,BinaryArrayFFT.cyclic,BinaryArrayFFT.tabulate_value,Array.size_ofFn]

/-- This full-vector primitive consumes binary operands directly. There is
no integer-view conversion, serializer, or native multiplication in its path. -/
def fullProduct {q : ℕ} (A : ℕ) (a b : Coefficients q) : Coefficients q × ℕ :=
  let result := BinaryArrayFFT.multiplication q A a.toArray b.toArray
  (⟨result.value,multiplication_size q A a.toArray b.toArray⟩,
    result.bitSteps+result.arrayActions+2*q)

lemma vector_getD {q : ℕ} (v : Coefficients q) (j : Fin q) :
    v.toArray.getD j.val BinaryArrayFFT.zeroInteger = v.get j := by
  simp [Array.getD,j.isLt,Vector.get]

lemma fullProduct_correct {q : ℕ} [NeZero q] (A : ℕ) (hA : 1 ≤ A) (a b : Coefficients q)
    (ha : VectorBound A a) (hb : VectorBound A b) (j : Fin q) :
    ((fullProduct A a b).1.get j).view =
      CyclicRing.convolution (fun i => (a.get i).view) (fun i => (b.get i).view) j := by
  have ha' : ∀ i : Fin q, (a.toArray.getD i.val BinaryArrayFFT.zeroInteger).view.natAbs ≤ A := by
    intro i; rw [vector_getD]; exact ha i
  have hb' : ∀ i : Fin q, (b.toArray.getD i.val BinaryArrayFFT.zeroInteger).view.natAbs ≤ A := by
    intro i; rw [vector_getD]; exact hb i
  have hh := BinaryArrayFFT.multiplication_correct q A hA a.toArray b.toArray ha' hb' j
  have hread := vector_getD (fullProduct A a b).1 j
  change (BinaryArrayFFT.multiplication q A a.toArray b.toArray).value.getD j.val BinaryArrayFFT.zeroInteger =
    (fullProduct A a b).1.get j at hread
  rw [hread] at hh
  have hleft : ArrayFFT.asCyclic q (BinaryArrayFFT.viewIntegers a.toArray) = (fun i => (a.get i).view) := by
    funext i
    simp only [ArrayFFT.asCyclic,BinaryArrayFFT.viewIntegers_getD,vector_getD]
  have hright : ArrayFFT.asCyclic q (BinaryArrayFFT.viewIntegers b.toArray) = (fun i => (b.get i).view) := by
    funext i
    simp only [ArrayFFT.asCyclic,BinaryArrayFFT.viewIntegers_getD,vector_getD]
  rw [hleft,hright] at hh
  exact hh

lemma fullProduct_bound {q : ℕ} [NeZero q] (A : ℕ) (hA : 1 ≤ A) (a b : Coefficients q)
    (ha : VectorBound A a) (hb : VectorBound A b) :
    VectorBound (q*A^2) (fullProduct A a b).1 := by
  intro j
  rw [fullProduct_correct A hA a b ha hb j]
  unfold CyclicRing.convolution
  calc
    _ ≤ ∑ i : Fin q, ((a.get i).view*(b.get (j-i)).view).natAbs := Int.natAbs_sum_le _ _
    _ ≤ ∑ _i : Fin q, A*A := by
      apply Finset.sum_le_sum
      intro i _
      rw [Int.natAbs_mul]
      exact Nat.mul_le_mul (ha i) (hb (j-i))
    _ = q*A^2 := by simp [pow_two]

def fftWorkBound (q A : ℕ) : ℕ :=
  295147905179352825856*(q.log2+3)*q*(q.log2+A.log2+102)^10

lemma fullProduct_work {q : ℕ} [NeZero q] (A : ℕ) (hA : 1 ≤ A) (a b : Coefficients q)
    (ha : VectorBound A a) (hb : VectorBound A b) :
    (fullProduct A a b).2 ≤ fftWorkBound q A := by
  have ha' : ∀ i : Fin q, (a.toArray.getD i.val BinaryArrayFFT.zeroInteger).view.natAbs ≤ A := by
    intro i; rw [vector_getD]; exact ha i
  have hb' : ∀ i : Fin q, (b.toArray.getD i.val BinaryArrayFFT.zeroInteger).view.natAbs ≤ A := by
    intro i; rw [vector_getD]; exact hb i
  have hh := BinaryArrayFFT.multiplication_totalSteps_bound q A a.toArray b.toArray hA ha' hb'
  have hp : 1 ≤ (q.log2+A.log2+102)^10 := Nat.one_le_pow _ _ (by omega)
  have hf : 2*q ≤ 147573952589676412928*(q.log2+3)*q*(q.log2+A.log2+102)^10 := by
    have hfirst := Nat.mul_le_mul_right q (show 2 ≤ 147573952589676412928*(q.log2+3) by omega)
    exact hfirst.trans (Nat.le_mul_of_pos_right _ hp)
  unfold fullProduct fftWorkBound
  dsimp only
  nlinarith

/-- Source operands are read from the retained binary dictionaries. The
metadata key, default vector, and complete vector handle are charged. -/
def readBase {L m t q : ℕ} (table : Table q) (w : BaseStates L m t) : Coefficients q × ℕ :=
  let key := ArrayKeys.materialize w.val
  let result := ArrayKeys.read table key
  (result.1.getD (BinaryCell.vectorZero q),result.2+2*L+q)

lemma readBase_work {L m t q : ℕ} (table : Table q) (w : BaseStates L m t) :
    (readBase table w).2 = 6*L+q+1 := by simp [readBase]; omega

lemma readBase_projection {L m t q : ℕ} (binary : Table q) (native : Trie (Vector ℤ q))
    (ht : Projection.TrieRel vectorView binary native) (w : BaseStates L m t) :
    vectorView (readBase binary w).1 = StoredHighDP.lookup native w.val := by
  exact (lookup_view binary native ht (ArrayKeys.materialize w.val)).trans (by rw [ArrayKeys.toWord_materialize])

def fftBase {L m t q : ℕ} (A : ℕ) (left right : Table q) (w : BaseStates L m t) : Coefficients q × ℕ :=
  let a := readBase left w
  let b := readBase right w
  let product := fullProduct A a.1 b.1
  (product.1,a.2+b.2+product.2)

lemma fftBase_correct {L m t q : ℕ} [NeZero q] (A : ℕ) (hA : 1 ≤ A)
    (left right : Table q) (w : BaseStates L m t)
    (ha : VectorBound A (readBase left w).1) (hb : VectorBound A (readBase right w).1) (j : Fin q) :
    ((fftBase A left right w).1.get j).view =
      CyclicRing.convolution (fun i => ((readBase left w).1.get i).view)
        (fun i => ((readBase right w).1.get i).view) j :=
  fullProduct_correct A hA _ _ ha hb j

lemma fftBase_bound {L m t q : ℕ} [NeZero q] (A : ℕ) (hA : 1 ≤ A)
    (left right : Table q) (w : BaseStates L m t)
    (ha : VectorBound A (readBase left w).1) (hb : VectorBound A (readBase right w).1) :
    VectorBound (q*A^2) (fftBase A left right w).1 := fullProduct_bound A hA _ _ ha hb

lemma fftBase_work {L m t q : ℕ} [NeZero q] (A : ℕ) (hA : 1 ≤ A)
    (left right : Table q) (w : BaseStates L m t)
    (ha : VectorBound A (readBase left w).1) (hb : VectorBound A (readBase right w).1) :
    (fftBase A left right w).2 ≤ fftWorkBound q A+2*(6*L+q+1) := by
  have hh := fullProduct_work A hA _ _ ha hb
  simpa only [fftBase,readBase_work,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc,two_mul] using
    Nat.add_le_add_left hh ((readBase left w).2+(readBase right w).2)

/-- Only actual balanced star-free source operands reach the FFT. -/
def guardedBase {L m t q : ℕ} (base : BaseStates L m t → Coefficients q × ℕ) : Base L q :=
  fun v => if h : StoredHighDP.highTest L m t (StoredHighDP.leafKey v) = true then
    let b : BaseStates L m t := ⟨StoredHighDP.leafKey v,
      ((StoredHighDP.highTest_eq_true L m t _).mp h).1,StoredHighDP.leafKey_noStars v⟩
    let result := base b
    (result.1,result.2+StoredHighDP.guardTests L)
  else (BinaryCell.vectorZero q,q+StoredHighDP.guardTests L)

lemma guardedBase_bound {L m t q : ℕ} (base : BaseStates L m t → Coefficients q × ℕ)
    (A : ℕ) (hb : ∀ v, VectorBound A (base v).1) (v : LeafWord (2*L)) :
    VectorBound A (guardedBase base v).1 := by
  unfold guardedBase
  split_ifs
  · exact hb _
  · exact Bounds.zeroVector_bound q A

lemma guardedBase_work {L m t q : ℕ} (base : BaseStates L m t → Coefficients q × ℕ)
    (B : ℕ) (hb : ∀ v, (base v).2 ≤ B) (v : LeafWord (2*L)) :
    (guardedBase base v).2 ≤ B+q+StoredHighDP.guardTests L := by
  unfold guardedBase
  split_ifs with h
  · have hh := hb ⟨StoredHighDP.leafKey v,
      ((StoredHighDP.highTest_eq_true L m t _).mp h).1,StoredHighDP.leafKey_noStars v⟩
    dsimp only
    omega
  · omega

lemma guardedBase_view {L m t q : ℕ} (base : BaseStates L m t → Coefficients q × ℕ)
    (v : LeafWord (2*L)) :
    vectorView (guardedBase base v).1 =
      (StoredHighDP.guardedBase (fun b => (vectorView (base b).1,0)) v).1 := by
  unfold guardedBase StoredHighDP.guardedBase
  split_ifs
  · rfl
  · exact vectorView_zero _

lemma guarded_execute_complete {L m t q : ℕ} (base : BaseStates L m t → Coefficients q × ℕ)
    (global : LeafWord (2*L) → Vector ℤ q)
    (hb : ∀ b, vectorView (base b).1 = global (baseLeaf b.val b.property.2))
    (w : States L m t) (j : Fin q) :
    ((lookup (execute (m := m) (t := t) (guardedBase base) (2*L+1)).value
      (ArrayKeys.materialize w.val)).get j).view = boxValue w.val (StoredHighDP.logicalLeaf global j) := by
  rw [execute_complete]
  unfold boxValue
  apply Finset.sum_congr rfl
  intro v _
  by_cases hc : Compatible w.val v
  · rw [if_pos hc,if_pos hc]
    have hh := StoredHighDP.guardedBase_agrees_on_compatible
      (fun b => (vectorView (base b).1,0)) global hb w v hc
    rw [←guardedBase_view] at hh
    have hj := congrArg (fun x : Vector ℤ q => x.get j) hh
    rw [vectorView_get] at hj
    exact hj
  · rw [if_neg hc,if_neg hc]

/-- Complete actual binary HIGH program: capped source reads, full FFT
products, and the stored five-child table layers. -/
def prepare {L m t q : ℕ} (A : ℕ) (left right : Table q) : Result (Table q) :=
  execute (L := L) (m := m) (t := t)
    (guardedBase (L := L) (m := m) (t := t) (fftBase (L := L) (m := m) (t := t) A left right)) (2*L+1)

def baseBudget (L q A : ℕ) : ℕ := fftWorkBound q A+2*(6*L+q+1)+q+StoredHighDP.guardTests L

noncomputable def preparationBudget (L m t q A : ℕ) : ℕ :=
  (2*L+1)^2*Fintype.card (BaseStates L m t)*
    (ArrayKeys.highLayerFactor L q 0*arithmeticUnit (5^(2*L+1)*(q*A^2)).size+baseBudget L q A)

lemma prepare_work {L m t q : ℕ} [NeZero q] (A : ℕ) (hA : 1 ≤ A) (left right : Table q)
    (ha : ∀ w : BaseStates L m t, VectorBound A (readBase left w).1)
    (hb : ∀ w : BaseStates L m t, VectorBound A (readBase right w).1) :
    (prepare (L := L) (m := m) (t := t) A left right).work ≤ preparationBudget L m t q A := by
  let base : Base L q := guardedBase (L := L) (m := m) (t := t) (fftBase (L := L) (m := m) (t := t) A left right)
  have hmag : ∀ v, VectorBound (q*A^2) (base v).1 :=
    guardedBase_bound _ _ (fun w => fftBase_bound A hA left right w (ha w) (hb w))
  have hprice : ∀ v, (base v).2 ≤ baseBudget L q A :=
    guardedBase_work _ _ (fun w => fftBase_work A hA left right w (ha w) (hb w))
  have hh := execute_work (m := m) (t := t) base (q*A^2) (2*L+1) hmag
  have hs := execute_sites_le_bases (m := m) (t := t) base
  have hf := execute_baseWork_le_bases (m := m) (t := t) base (baseBudget L q A) hprice
  have hu := Nat.mul_le_mul_right (arithmeticUnit (5^(2*L+1)*(q*A^2)).size) hs
  change (execute (m := m) (t := t) base (2*L+1)).work ≤ _
  unfold preparationBudget
  nlinarith


lemma prepare_bound {L m t q : ℕ} [NeZero q] (A : ℕ) (hA : 1 ≤ A) (left right : Table q)
    (ha : ∀ w : BaseStates L m t, VectorBound A (readBase left w).1)
    (hb : ∀ w : BaseStates L m t, VectorBound A (readBase right w).1) :
    Bounds.TableBound (5^(2*L+1)*(q*A^2)) (prepare (L := L) (m := m) (t := t) A left right).value := by
  apply execute_bound
  exact guardedBase_bound _ _ (fun w => fftBase_bound A hA left right w (ha w) (hb w))

/-- Joint lowering compares the real bit counter to the exact native DP
sites and the retained sum of the actual FFT/read callback counters. -/
lemma prepare_joint_work {L m t q : ℕ} [NeZero q] (A : ℕ) (hA : 1 ≤ A) (left right : Table q)
    (ha : ∀ w : BaseStates L m t, VectorBound A (readBase left w).1)
    (hb : ∀ w : BaseStates L m t, VectorBound A (readBase right w).1) :
    (prepare (L := L) (m := m) (t := t) A left right).work ≤
      (prepare (L := L) (m := m) (t := t) A left right).sites*
        arithmeticUnit (5^(2*L+1)*(q*A^2)).size+
      (prepare (L := L) (m := m) (t := t) A left right).baseWork := by
  apply execute_work
  exact guardedBase_bound _ _ (fun w => fftBase_bound A hA left right w (ha w) (hb w))

/-- Source-table refinement is stated on the actual capped binary reads.
It determines every global box through the proved compatibility support,
rather than assuming the completed table equals an output product. -/
lemma prepare_source_complete {L m t q : ℕ} [NeZero q] (A : ℕ) (hA : 1 ≤ A)
    (left right : Table q) (leftGlobal rightGlobal : LeafWord (2*L) → Vector ℤ q)
    (ha : ∀ w : BaseStates L m t, VectorBound A (readBase left w).1)
    (hb : ∀ w : BaseStates L m t, VectorBound A (readBase right w).1)
    (hl : ∀ b : BaseStates L m t, vectorView (readBase left b).1 = leftGlobal (baseLeaf b.val b.property.2))
    (hr : ∀ b : BaseStates L m t, vectorView (readBase right b).1 = rightGlobal (baseLeaf b.val b.property.2))
    (w : States L m t) (j : Fin q) :
    ((lookup (prepare (L := L) (m := m) (t := t) A left right).value
      (ArrayKeys.materialize w.val)).get j).view =
      boxValue w.val (fun v => CyclicRing.convolution (leftGlobal v).get (rightGlobal v).get j) := by
  let global : LeafWord (2*L) → Vector ℤ q := fun v => Vector.ofFn (fun r =>
    CyclicRing.convolution (leftGlobal v).get (rightGlobal v).get r)
  have hg (b : BaseStates L m t) : vectorView (fftBase A left right b).1 =
      global (baseLeaf b.val b.property.2) := by
    apply Vector.ext
    intro r hq
    let index : Fin q := ⟨r,hq⟩
    change (vectorView (fftBase A left right b).1).get index = (global _).get index
    rw [vectorView_get,fftBase_correct A hA left right b (ha b) (hb b)]
    have hleft : (fun i => ((readBase left b).1.get i).view) =
        (leftGlobal (baseLeaf b.val b.property.2)).get := by
      funext i
      have hh := congrArg (fun v : Vector ℤ q => v.get i) (hl b)
      rw [vectorView_get] at hh
      exact hh
    have hright : (fun i => ((readBase right b).1.get i).view) =
        (rightGlobal (baseLeaf b.val b.property.2)).get := by
      funext i
      have hh := congrArg (fun v : Vector ℤ q => v.get i) (hr b)
      rw [vectorView_get] at hh
      exact hh
    rw [hleft,hright]
    exact (Vector.get_ofFn _ _).symm
  have hh := guarded_execute_complete (fftBase A left right) global hg w j
  have hglobal : StoredHighDP.logicalLeaf global j =
      fun v => CyclicRing.convolution (leftGlobal v).get (rightGlobal v).get j := by
    funext v
    exact Vector.get_ofFn _ _
  rw [hglobal] at hh
  exact hh

/-- A selected scalar read retains its binary cell and pointer/index work. -/
def readSelected {n q : ℕ} (table : Table q) (a : ArrayKeys.Key n) (j : Fin q) : Option Cell × ℕ :=
  ArrayKeys.readSelected table a j

lemma readSelected_work {n q : ℕ} (table : Table q) (a : ArrayKeys.Key n) (j : Fin q) :
    (readSelected table a j).2 = 2*n+2 := by simp [readSelected]

lemma readSelected_projection {n q : ℕ} (binary : Table q) (native : Trie (Vector ℤ q))
    (ht : Projection.TrieRel vectorView binary native) (a : ArrayKeys.Key n) (j : Fin q) :
    (ArrayKeys.readSelected native a j).1 = ((readSelected binary a j).1).map BinaryCell.view := by
  unfold readSelected ArrayKeys.readSelected
  simp only [Projection.array_read ht,Option.map_map,Function.comp_def]
  apply congrArg (fun f => ((ArrayKeys.read binary a).1).map f)
  funext v
  exact vectorView_get v j


/-- The scalar HIGH sum uses binary addition on the retained cells. -/
def sumCells : List Cell → ToomCook.Counted Cell
  | [] => ⟨BinaryCell.zero,1⟩
  | x::xs =>
      let tail := sumCells xs
      let next := BinaryCell.add x tail.value
      ⟨next.value,tail.operations+next.bitSteps+2⟩

@[simp] lemma cellAdd_view (a b : Cell) : (BinaryCell.add a b).value.view = a.view+b.view := BinaryCell.add_view _ _

lemma sumCells_view (xs : List Cell) :
    (sumCells xs).value.view = (xs.map (fun x => x.view)).sum := by
  induction xs with
  | nil => simp [sumCells,BinaryCell.zero]
  | cons x xs ih => simp only [sumCells,cellAdd_view,List.map_cons,List.sum_cons,ih]

lemma sumCells_bound (A : ℕ) (xs : List Cell) (hx : ∀ x∈xs, x.view.natAbs ≤ A) :
    (sumCells xs).value.view.natAbs ≤ xs.length*A := by
  induction xs with
  | nil => simp [sumCells,BinaryCell.zero]
  | cons x xs ih =>
      have ht := ih (fun y hy => hx y (List.mem_cons_of_mem x hy))
      have hh := hx x (by simp)
      simp only [sumCells,cellAdd_view,List.length_cons]
      have hm := (Int.natAbs_add_le _ _).trans (Nat.add_le_add hh ht)
      nlinarith

lemma sumCells_price_width (A N W : ℕ) (xs : List Cell)
    (hlen : xs.length ≤ N) (hW : (N*A).size ≤ W) (hx : ∀ x∈xs, x.view.natAbs ≤ A) :
    (sumCells xs).operations ≤ xs.length*(BackendScalarBits.backendScalarUnit W+2)+1 := by
  induction xs with
  | nil => simp [sumCells]
  | cons x xs ih =>
      simp only [List.length_cons] at hlen
      have ht := ih (by omega) (fun y hy => hx y (List.mem_cons_of_mem x hy))
      have htail := sumCells_bound A xs (fun y hy => hx y (List.mem_cons_of_mem x hy))
      have hh : x.view.natAbs.size ≤ W :=
        (Nat.size_le_size ((hx x (by simp)).trans (Nat.le_mul_of_pos_left A (by omega)))).trans hW
      have hr : (sumCells xs).value.view.natAbs.size ≤ W :=
        (Nat.size_le_size (htail.trans (Nat.mul_le_mul_right A (by omega)))).trans hW
      have hc := BinaryCell.add_price W x (sumCells xs).value hh hr
      simp only [sumCells,List.length_cons]
      nlinarith

def readCell {n q : ℕ} (table : Table q) (key : ArrayKeys.Key n) (target : Fin q) : ToomCook.Counted Cell :=
  let read := readSelected table key target
  ⟨read.1.getD BinaryCell.zero,read.2+1⟩

lemma readCell_work {n q : ℕ} (table : Table q) (key : ArrayKeys.Key n) (target : Fin q) :
    (readCell table key target).operations = 2*n+3 := by simp [readCell,readSelected_work]

lemma readCell_lookup {n q : ℕ} (table : Table q) (key : ArrayKeys.Key n) (target : Fin q) :
    (readCell table key target).value = (lookup table key).get target := by
  unfold readCell readSelected ArrayKeys.readSelected lookup
  dsimp only
  cases h : (ArrayKeys.read table key).1 <;> simp [BinaryCell.vectorZero]

def query {L k q : ℕ} (t : ℕ) (embedding : Fin k ↪o Fin (2*L))
    (outside : Vector (Fin 4) (2*L)) (table : Table q) (target : Fin q) : ToomCook.Counted Cell :=
  let stored := ThinMatrixBackend.materializeEmbedding embedding
  let keys := HighQueryKeys.generatedKeysCounted t k (2*L) stored outside
  let reads := keys.1.map (fun key => readCell table key target)
  let result := sumCells (reads.map (fun r => r.value))
  ⟨result.value,k+keys.2+(reads.map (fun r => r.operations)).sum+result.operations+2*reads.length⟩

lemma query_keysum {L k q : ℕ} (t : ℕ) (embedding : Fin k ↪o Fin (2*L))
    (outside : Vector (Fin 4) (2*L)) (table : Table q) (target : Fin q) :
    (query t embedding outside table target).value.view =
      ((HighQueryKeys.generatedKeys t k (2*L) embedding outside).map
        (fun key => (readCell table key target).value.view)).sum := by
  simp only [query,sumCells_view,List.map_map,Function.comp_def,
    HighQueryKeys.generatedKeysCounted_value,ThinMatrixBackend.materializeEmbedding_eq]

def queryUnit (L k W : ℕ) : ℕ :=
  HighQueryKeys.queryKeyFactor (2*L) k+BackendScalarBits.backendScalarUnit W+4*L+k+8

lemma query_bound {L k q : ℕ} (t A : ℕ) (embedding : Fin k ↪o Fin (2*L))
    (outside : Vector (Fin 4) (2*L)) (table : Table q) (target : Fin q)
    (ht : Bounds.TableBound A table) :
    (query t embedding outside table target).value.view.natAbs ≤ (k.choose t*4^t)*A := by
  have hh := sumCells_bound A
    (((HighQueryKeys.generatedKeysCounted t k (2*L)
      (ThinMatrixBackend.materializeEmbedding embedding) outside).1.map
        (fun key => readCell table key target)).map (fun r => r.value)) (by
      intro x hx
      obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hx
      obtain ⟨key,_,rfl⟩ := List.mem_map.mp hr
      rw [readCell_lookup]
      exact Bounds.array_read_bound ht key target)
  simpa only [query,List.length_map,HighQueryKeys.generatedKeysCounted_value,
    HighQueryKeys.generatedKeys_length] using hh

lemma query_work {L k q : ℕ} (t A : ℕ) (embedding : Fin k ↪o Fin (2*L))
    (outside : Vector (Fin 4) (2*L)) (table : Table q) (target : Fin q)
    (ht : t ≤ k) (hbound : Bounds.TableBound A table) :
    (query t embedding outside table target).operations ≤
      (k.choose t*4^t)*queryUnit L k ((k.choose t*4^t)*A).size := by
  let keys := HighQueryKeys.generatedKeysCounted t k (2*L)
    (ThinMatrixBackend.materializeEmbedding embedding) outside
  let reads := keys.1.map (fun key => readCell table key target)
  have hlen : reads.length = k.choose t*4^t := by
    simp only [reads,keys,List.length_map,HighQueryKeys.generatedKeysCounted_value,HighQueryKeys.generatedKeys_length]
  have hs := sumCells_price_width A (k.choose t*4^t) ((k.choose t*4^t)*A).size
    (reads.map (fun r => r.value)) (by rw [List.length_map,hlen]) le_rfl (by
      intro x hx
      obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hx
      obtain ⟨key,_,rfl⟩ := List.mem_map.mp hr
      rw [readCell_lookup]
      exact Bounds.array_read_bound hbound key target)
  have hk := HighQueryKeys.generatedKeysCounted_work_le t k (2*L) ht
    (ThinMatrixBackend.materializeEmbedding embedding) outside
  have hread : (reads.map (fun r => r.operations)).sum = reads.length*(4*L+3) := by
    simp only [reads,List.map_map,Function.comp_def,readCell_work,List.map_const',List.sum_const_nat,List.length_map]
    ring
  have hm : 1 ≤ k.choose t*4^t := Nat.mul_le_mul (Nat.choose_pos ht) (Nat.one_le_pow _ _ (by omega))
  have hcontrol : k+1 ≤ (k+1)*(k.choose t*4^t) := Nat.le_mul_of_pos_right _ hm
  change k+keys.2+(reads.map (fun r => r.operations)).sum+(sumCells (reads.map (fun r => r.value))).operations+
    2*reads.length ≤ _
  rw [hread,hlen]
  simp only [List.length_map,hlen] at hs
  unfold queryUnit
  nlinarith

lemma native_queryBox_keys {L m t k q : ℕ} [NeZero q] (hk : k=2*m)
    (e : Fin k ↪o Fin (2*L)) (outside : Vector (Fin 4) (2*L))
    (hleft : ((embeddedSupport e).filter (fun i => i.val < L)).card ≤ m)
    (hright : ((embeddedSupport e).filter (fun i => L ≤ i.val)).card ≤ m)
    (prepared : ThinMatrixBackend.PreparedHigh L m t q) (ms : List (Option Bool))
    (hms : ms∈OrderedBoxes.orderedBoxMasks t k) (target : Fin q) :
    (ThinMatrixBackend.queryHighBox hk e outside.get hleft hright prepared ms target).1 =
      ((HighQueryKeys.physicalKeys ms
        (HighQueryKeys.reindex ms (OrderedBoxes.orderedBoxMasks_shape hms).1 e) outside).map
          (fun key => (ArrayKeys.readSelected prepared.table key target).1.getD 0)).sum := by
  rw [←ThinMatrixBackend.queryHighBoxGenerated_refines hk e outside.get hleft hright prepared ms hms target]
  simp only [ThinMatrixBackend.queryHighBoxGenerated,HighQueryKeys.physicalKeysCounted_value,
    List.map_map,Function.comp_def,ThinMatrixBackend.queryHighKey]
  have hout : Vector.ofFn outside.get = outside := by
    apply Vector.ext; intro i hi; exact Vector.get_ofFn _ _
  rw [hout]
  rfl

lemma sum_flatMap {α β : Type*} [AddCommMonoid β] (xs : List α) (f : α → List β) :
    (xs.flatMap f).sum = (xs.map (fun x => (f x).sum)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs _ih => simp [List.flatMap,Function.comp_def]

lemma native_queryHigh_keys {L m t k q : ℕ} [NeZero q] (hk : k=2*m)
    (e : Fin k ↪o Fin (2*L)) (outside : Vector (Fin 4) (2*L))
    (hleft : ((embeddedSupport e).filter (fun i => i.val < L)).card ≤ m)
    (hright : ((embeddedSupport e).filter (fun i => L ≤ i.val)).card ≤ m)
    (prepared : ThinMatrixBackend.PreparedHigh L m t q) (target : Fin q) :
    (ThinMatrixBackend.queryHigh hk e outside.get hleft hright prepared target).1 =
      ((HighQueryKeys.generatedKeys t k (2*L) e outside).map
        (fun key => (ArrayKeys.readSelected prepared.table key target).1.getD 0)).sum := by
  rw [ThinMatrixBackend.queryHigh_refines]
  unfold HighQueryKeys.generatedKeys
  rw [List.map_flatMap,sum_flatMap]
  simp only [List.map_map,Function.comp_def]
  have hmaps : ((HighQueryKeys.generatedMasks t k).map Subtype.val).map
      (fun ms => (ThinMatrixBackend.queryHighBox hk e outside.get hleft hright prepared ms target).1) =
      (HighQueryKeys.generatedMasks t k).map (fun ms =>
        ((HighQueryKeys.physicalKeys ms.val
          (HighQueryKeys.reindex ms.val (OrderedBoxes.orderedBoxMasks_shape ms.property).1 e) outside).map
          (fun key => (ArrayKeys.readSelected prepared.table key target).1.getD 0)).sum) := by
    simp only [List.map_map,Function.comp_def]
    apply List.map_congr_left
    intro ms _
    exact native_queryBox_keys hk e outside hleft hright prepared ms.val ms.property target
  rw [HighQueryKeys.generatedMasks_values] at hmaps
  exact congrArg List.sum hmaps

lemma query_native_refines {L m t k q : ℕ} [NeZero q] (hk : k=2*m)
    (e : Fin k ↪o Fin (2*L)) (outside : Vector (Fin 4) (2*L))
    (hleft : ((embeddedSupport e).filter (fun i => i.val < L)).card ≤ m)
    (hright : ((embeddedSupport e).filter (fun i => L ≤ i.val)).card ≤ m)
    (binary : Table q) (native : ThinMatrixBackend.PreparedHigh L m t q) (target : Fin q)
    (hmatch : ∀ w : States L m t, ((lookup binary (ArrayKeys.materialize w.val)).get target).view =
      (StoredHighDP.lookup native.table w.val).get target) :
    (query t e outside binary target).value.view =
      (ThinMatrixBackend.queryHigh hk e outside.get hleft hright native target).1 := by
  rw [query_keysum,native_queryHigh_keys hk e outside hleft hright native target]
  unfold HighQueryKeys.generatedKeys
  rw [List.map_flatMap,sum_flatMap,List.map_flatMap,sum_flatMap]
  congr 1
  apply List.map_congr_left
  intro ms _
  let hlen := (OrderedBoxes.orderedBoxMasks_shape ms.property).1
  let e' := HighQueryKeys.reindex ms.val hlen e
  have hl : ((embeddedSupport e').filter (fun i => i.val < L)).card ≤ m := by
    change ((embeddedSupport (CompleteThinProduct.reindexEmbedding ms.val hlen e)).filter
      (fun i => i.val < L)).card ≤ m
    simpa only [CompleteThinProduct.reindexEmbedding_support] using hleft
  have hr : ((embeddedSupport e').filter (fun i => L ≤ i.val)).card ≤ m := by
    change ((embeddedSupport (CompleteThinProduct.reindexEmbedding ms.val hlen e)).filter
      (fun i => L ≤ i.val)).card ≤ m
    simpa only [CompleteThinProduct.reindexEmbedding_support] using hright
  rw [HighQueryKeys.physicalState_sum ms.val ms.property (hlen.trans hk) e' outside hl hr,
    HighQueryKeys.physicalState_sum ms.val ms.property (hlen.trans hk) e' outside hl hr]
  apply Finset.sum_congr rfl
  intro a _
  rw [readCell_lookup]
  have hh := hmatch (physicalState ms.val ms.property (hlen.trans hk) e' outside.get hl hr a)
  have hv := ThinMatrixBackend.queryHighState_value native
    (physicalState ms.val ms.property (hlen.trans hk) e' outside.get hl hr a) target
  exact hh.trans hv.symm


/-- A correctly prepared table is consumed through its physical box
coefficients only; the query does not reconstruct any native table. -/
lemma query_boxes {L m t k q : ℕ} (hk : k=2*m)
    (e : Fin k ↪o Fin (2*L)) (outside : Vector (Fin 4) (2*L))
    (hleft : ((embeddedSupport e).filter (fun i => i.val < L)).card ≤ m)
    (hright : ((embeddedSupport e).filter (fun i => L ≤ i.val)).card ≤ m)
    (binary : Table q) (target : Fin q) (global : LeafWord (2*L) → ℤ)
    (hbox : ∀ w : States L m t, ((lookup binary (ArrayKeys.materialize w.val)).get target).view = boxValue w.val global) :
    (query t e outside binary target).value.view =
      CompleteThinProduct.storedHigh (t := t) hk e outside.get hleft hright global := by
  rw [query_keysum]
  unfold HighQueryKeys.generatedKeys CompleteThinProduct.storedHigh
  rw [List.map_flatMap,sum_flatMap]
  conv_rhs => rw [←HighQueryKeys.generatedMasks_values t k]
  simp only [List.map_map,Function.comp_def]
  congr 1
  apply List.map_congr_left
  intro ms _
  let hlen := (OrderedBoxes.orderedBoxMasks_shape ms.property).1
  let e' := HighQueryKeys.reindex ms.val hlen e
  have hl : ((embeddedSupport e').filter (fun i => i.val < L)).card ≤ m := by
    change ((embeddedSupport (CompleteThinProduct.reindexEmbedding ms.val hlen e)).filter
      (fun i => i.val < L)).card ≤ m
    simpa only [CompleteThinProduct.reindexEmbedding_support] using hleft
  have hr : ((embeddedSupport e').filter (fun i => L ≤ i.val)).card ≤ m := by
    change ((embeddedSupport (CompleteThinProduct.reindexEmbedding ms.val hlen e)).filter
      (fun i => L ≤ i.val)).card ≤ m
    simpa only [CompleteThinProduct.reindexEmbedding_support] using hright
  rw [HighQueryKeys.physicalState_sum ms.val ms.property (hlen.trans hk) e' outside hl hr]
  unfold CompleteThinProduct.storedBox
  rw [dif_pos ms.property]
  simp only [HighBoxDP.tableAfter_complete]
  apply Finset.sum_congr rfl
  intro a _
  rw [readCell_lookup]
  exact hbox (physicalState ms.val ms.property (hlen.trans hk) e' outside.get hl hr a)

lemma query_prepared_work {L m t k q : ℕ} [NeZero q] (A : ℕ) (hA : 1 ≤ A)
    (left right : Table q) (e : Fin k ↪o Fin (2*L)) (outside : Vector (Fin 4) (2*L)) (target : Fin q)
    (ht : t ≤ k)
    (ha : ∀ w : BaseStates L m t, VectorBound A (readBase left w).1)
    (hb : ∀ w : BaseStates L m t, VectorBound A (readBase right w).1) :
    (query t e outside (prepare (L := L) (m := m) (t := t) A left right).value target).operations ≤
      (k.choose t*4^t)*queryUnit L k ((k.choose t*4^t)*(5^(2*L+1)*(q*A^2))).size :=
  query_work t _ e outside _ target ht (prepare_bound A hA left right ha hb)


end ThinMatrix.BinaryHighTable

#print axioms ThinMatrix.BinaryHighTable.node_refines
#print axioms ThinMatrix.BinaryHighTable.execute_refines
#print axioms ThinMatrix.BinaryHighTable.execute_sites
#print axioms ThinMatrix.BinaryHighTable.execute_bound
#print axioms ThinMatrix.BinaryHighTable.execute_work
#print axioms ThinMatrix.BinaryHighTable.execute_sites_le_bases
#print axioms ThinMatrix.BinaryHighTable.execute_complete
#print axioms ThinMatrix.BinaryHighTable.fullProduct_correct
#print axioms ThinMatrix.BinaryHighTable.fullProduct_work
#print axioms ThinMatrix.BinaryHighTable.guarded_execute_complete
#print axioms ThinMatrix.BinaryHighTable.prepare_work
#print axioms ThinMatrix.BinaryHighTable.prepare_joint_work
#print axioms ThinMatrix.BinaryHighTable.prepare_source_complete
#print axioms ThinMatrix.BinaryHighTable.readSelected_projection

#print axioms ThinMatrix.BinaryHighTable.query_keysum
#print axioms ThinMatrix.BinaryHighTable.query_bound
#print axioms ThinMatrix.BinaryHighTable.query_work
#print axioms ThinMatrix.BinaryHighTable.query_native_refines
#print axioms ThinMatrix.BinaryHighTable.query_boxes
#print axioms ThinMatrix.BinaryHighTable.query_prepared_work
