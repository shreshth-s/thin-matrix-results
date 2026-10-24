import BinaryGroupedPreparation

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! Stable request routing by retained Boolean keys. One trie is initialized,
then each original list occurrence is inserted once. Leaf order and duplicate
payloads are preserved. Indexed-control costs include copying key tails and
the rebuilt path; no linear scan over all groups is performed per request.
Binary addressing and the graph-specific key construction are separate. -/
namespace ThinMatrix.BooleanRequestRouter
open BinaryGroupedCoordinates

variable {A : Type}

abbrev Key (n : ℕ) := Vector Bool n

def Tree (A : Type) : ℕ → Type
  | 0 => List A
  | n+1 => Tree A n × Tree A n

def tail {n : ℕ} (key : Key (n+1)) : Key n := Vector.ofFn (fun i => key.get i.succ)

theorem key_eq_iff {n : ℕ} (key query : Key (n+1)) :
    key=query ↔ key.get 0=query.get 0 ∧ tail key=tail query := by
  constructor
  · rintro rfl; exact ⟨rfl,rfl⟩
  · rintro ⟨hh,ht⟩
    apply Vector.ext
    intro i hi
    cases i with
    | zero => exact hh
    | succ i =>
      have h := congrArg (fun v : Key n => v.get ⟨i,by omega⟩) ht
      simpa only [tail,Vector.get_ofFn,Vector.get_eq_getElem,Vector.getElem_ofFn,Fin.val_succ] using h

def bucket : {n : ℕ} → Tree A n → Key n → List A
  | 0,tree,_ => tree
  | _+1,tree,key => bucket (if key.get 0 then tree.2 else tree.1) (tail key)

def read : {n : ℕ} → Tree A n → Key n → Run (List A)
  | 0,tree,_ => ⟨tree,0,4⟩
  | n+1,tree,key =>
      let out := read (if key.get 0 then tree.2 else tree.1) (tail key)
      ⟨out.value,out.bitSteps,out.control+8*n+16⟩

theorem read_value {n : ℕ} (tree : Tree A n) (key : Key n) : (read tree key).value=bucket tree key := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih _ _

theorem read_bits {n : ℕ} (tree : Tree A n) (key : Key n) : (read tree key).bitSteps=0 := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih _ _

theorem read_control {n : ℕ} (tree : Tree A n) (key : Key n) :
    (read tree key).control≤16*(n+1)^2 := by
  induction n with
  | zero => simp [read]
  | succ n ih =>
    have hh := ih (if key.get 0 then tree.2 else tree.1) (tail key)
    simp only [read]
    nlinarith

def empty : (n : ℕ) → Run (Tree A n)
  | 0 => ⟨[],0,4⟩
  | n+1 =>
      let left := empty n
      let right := empty n
      ⟨(left.value,right.value),left.bitSteps+right.bitSteps,left.control+right.control+8⟩

theorem empty_bucket (n : ℕ) (key : Key n) : bucket (empty (A:=A) n).value key=[] := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [empty,bucket]; split <;> exact ih _

theorem empty_bits (n : ℕ) : (empty (A:=A) n).bitSteps=0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [empty,ih,zero_add]

theorem empty_control (n : ℕ) : (empty (A:=A) n).control≤12*2^n := by
  have h : (empty (A:=A) n).control+8=12*2^n := by
    induction n with
    | zero => rfl
    | succ n ih => simp only [empty,pow_succ];omega
  omega

def insert : {n : ℕ} → Tree A n → Key n → A → Run (Tree A n)
  | 0,tree,_,a => ⟨a::tree,0,8⟩
  | n+1,tree,key,a =>
      if key.get 0 then
        let child := insert tree.2 (tail key) a
        ⟨(tree.1,child.value),child.bitSteps,child.control+8*n+24⟩
      else
        let child := insert tree.1 (tail key) a
        ⟨(child.value,tree.2),child.bitSteps,child.control+8*n+24⟩

theorem insert_bucket {n : ℕ} (tree : Tree A n) (key query : Key n) (a : A) :
    bucket (insert tree key a).value query=if key=query then a::bucket tree query else bucket tree query := by
  induction n with
  | zero =>
    have h : key=query := Vector.ext (fun i hi => by omega)
    simp only [insert,bucket,h,ite_true]
  | succ n ih =>
    cases hk : key.get 0 <;> cases hq : query.get 0 <;>
      simp [insert,bucket,hk,hq,ih,key_eq_iff]

theorem insert_bits {n : ℕ} (tree : Tree A n) (key : Key n) (a : A) :
    (insert tree key a).bitSteps=0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [insert]; split <;> exact ih _ _

theorem insert_control {n : ℕ} (tree : Tree A n) (key : Key n) (a : A) :
    (insert tree key a).control≤16*(n+1)^2 := by
  induction n with
  | zero => simp [insert]
  | succ n ih =>
    simp only [insert]
    split
    · have h := ih tree.2 (tail key); dsimp only; nlinarith
    · have h := ih tree.1 (tail key); dsimp only; nlinarith

def items : {n : ℕ} → Tree A n → ℕ
  | 0,tree => tree.length
  | _+1,tree => items tree.1+items tree.2

theorem empty_items (n : ℕ) : items (empty (A:=A) n).value=0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [empty,items,ih,zero_add]

theorem insert_items {n : ℕ} (tree : Tree A n) (key : Key n) (a : A) :
    items (insert tree key a).value=items tree+1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [insert]; split <;> simp only [items,ih] <;> omega

/-- Tail-first insertion preserves the original order within each leaf. -/
def fill {n : ℕ} (tree : Tree A n) : List (Key n × A) → Run (Tree A n)
  | [] => ⟨tree,0,4⟩
  | row::rows =>
      let rest := fill tree rows
      let out := insert rest.value row.1 row.2
      ⟨out.value,rest.bitSteps+out.bitSteps,rest.control+out.control+12⟩

def selected {n : ℕ} (rows : List (Key n × A)) (query : Key n) : List A :=
  rows.filterMap (fun row => if row.1=query then some row.2 else none)

theorem fill_bucket {n : ℕ} (tree : Tree A n) (rows : List (Key n × A)) (query : Key n) :
    bucket (fill tree rows).value query=selected rows query++bucket tree query := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
    simp only [fill,insert_bucket,ih,selected,List.filterMap_cons]
    split <;> simp_all

theorem fill_bits {n : ℕ} (tree : Tree A n) (rows : List (Key n × A)) :
    (fill tree rows).bitSteps=0 := by
  induction rows with
  | nil => rfl
  | cons row rows ih => simp only [fill,insert_bits,ih,zero_add]

theorem fill_control {n : ℕ} (tree : Tree A n) (rows : List (Key n × A)) :
    (fill tree rows).control≤rows.length*(16*(n+1)^2+12)+4 := by
  induction rows with
  | nil => simp [fill]
  | cons row rows ih =>
    have hh := insert_control (fill tree rows).value row.1 row.2
    simp only [fill,List.length_cons]
    nlinarith

theorem fill_items {n : ℕ} (tree : Tree A n) (rows : List (Key n × A)) :
    items (fill tree rows).value=items tree+rows.length := by
  induction rows with
  | nil => simp [fill]
  | cons row rows ih => simp [fill,insert_items,ih,Nat.add_assoc]

def build {n : ℕ} (rows : List (Key n × A)) : Run (Tree A n) :=
  let initial := empty n
  let out := fill initial.value rows
  ⟨out.value,initial.bitSteps+out.bitSteps,initial.control+out.control+8⟩

theorem build_bucket {n : ℕ} (rows : List (Key n × A)) (query : Key n) :
    bucket (build rows).value query=selected rows query := by
  simp only [build,fill_bucket,empty_bucket,List.append_nil]

theorem build_items {n : ℕ} (rows : List (Key n × A)) : items (build rows).value=rows.length := by
  simp only [build,fill_items,empty_items,zero_add]

theorem build_cost {n : ℕ} (rows : List (Key n × A)) :
    (build rows).bitSteps=0 ∧
    (build rows).control≤12*2^n+rows.length*(16*(n+1)^2+12)+12 := by
  refine ⟨by simp only [build,empty_bits,fill_bits,zero_add],?_⟩
  have he := empty_control (A:=A) n
  have hf := fill_control (empty (A:=A) n).value rows
  simp only [build]
  omega

#print axioms key_eq_iff
#print axioms read_value
#print axioms read_bits
#print axioms read_control
#print axioms empty_bucket
#print axioms empty_bits
#print axioms empty_control
#print axioms insert_bucket
#print axioms insert_bits
#print axioms insert_control
#print axioms empty_items
#print axioms insert_items
#print axioms fill_bucket
#print axioms fill_bits
#print axioms fill_control
#print axioms fill_items
#print axioms build_bucket
#print axioms build_items
#print axioms build_cost
end ThinMatrix.BooleanRequestRouter
