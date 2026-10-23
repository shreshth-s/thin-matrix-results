import StoredGroupedCompletion

set_option autoImplicit false

/-!
# Retained capped Boolean keys with complete enumeration annotations

The recursion only visits admissible prefixes. It retains concrete Boolean
vectors, charges their copies and every map/append traversal, and includes
root and recursion control. These are bounded-register/Boolean actions;
no constant-time claim for Lean's native evaluator is made.
-/
namespace ThinMatrix.CappedBitPreparation
open scoped BigOperators
abbrev Key (n : ℕ) := Vector Bool n

def prepend {n : ℕ} (b : Bool) (v : Key n) : Key (n+1) :=
  Vector.ofFn (Fin.cases b v.get)

def tail {n : ℕ} (v : Key (n+1)) : Key n := Vector.ofFn (fun i => v.get i.succ)

@[simp] theorem prepend_zero {n : ℕ} (b : Bool) (v : Key n) :
    (prepend b v).get 0 = b := by simp [prepend]
@[simp] theorem prepend_succ {n : ℕ} (b : Bool) (v : Key n) (i : Fin n) :
    (prepend b v).get i.succ = v.get i := by simp [prepend]
@[simp] theorem tail_prepend {n : ℕ} (b : Bool) (v : Key n) : tail (prepend b v) = v := by
  ext i hi
  simp [tail,prepend,Vector.get]

theorem prepend_tail {n : ℕ} (v : Key (n+1)) : prepend (v.get 0) (tail v) = v := by
  apply Vector.ext
  intro i hi
  change (prepend (v.get 0) (tail v)).get ⟨i,hi⟩ = v.get ⟨i,hi⟩
  generalize hk : (⟨i,hi⟩ : Fin (n+1)) = k
  exact Fin.cases (by simp) (fun j => by simp [tail]) k

@[simp] theorem prepend_eq {n : ℕ} (b c : Bool) (v w : Key n) :
    prepend b v = prepend c w ↔ b=c ∧ v=w := by
  constructor
  · intro h
    exact ⟨by simpa using congrArg (fun x : Key (n+1) => x.get 0) h,
      by simpa using congrArg tail h⟩
  · rintro ⟨rfl,rfl⟩
    rfl

theorem prepend_injective {n : ℕ} (b : Bool) : Function.Injective (@prepend n b) := by
  intro v w h
  exact (prepend_eq b b v w).mp h |>.2

def ones {n : ℕ} (v : Key n) : ℕ := (v.toList.map (fun b => if b then 1 else 0)).sum

theorem toList_prepend {n : ℕ} (b : Bool) (v : Key n) :
    (prepend b v).toList = b::v.toList := by
  have hv : Vector.ofFn v.get = v := by ext i hi; simp only [Vector.getElem_ofFn]; rfl
  simp only [prepend,Vector.toList_ofFn,List.ofFn_succ,Fin.cases_zero,Fin.cases_succ]
  rw [← Vector.toList_ofFn,hv]

@[simp] theorem ones_prepend {n : ℕ} (b : Bool) (v : Key n) :
    ones (prepend b v) = (if b then 1 else 0)+ones v := by simp [ones,toList_prepend]

def support {n : ℕ} (v : Key n) : Finset (Fin n) := Finset.univ.filter (fun i => v.get i)

@[simp] theorem mem_support {n : ℕ} (v : Key n) (i : Fin n) : i ∈ support v ↔ v.get i = true := by
  simp [support]

theorem support_card {n : ℕ} (v : Key n) : (support v).card = ones v := by
  simp only [support,Finset.card_eq_sum_ones,Finset.sum_filter]
  simpa only [ones] using StoredGroupedCompletion.vector_sum v
    (fun b => if b then (1:ℕ) else 0)

theorem support_injective {n : ℕ} : Function.Injective (@support n) := by
  intro v w h
  apply Vector.ext
  intro i hi
  have hm := Finset.ext_iff.mp h ⟨i,hi⟩
  simp only [mem_support] at hm
  exact Bool.eq_iff_iff.mpr hm

def fromSupport {n : ℕ} (J : Finset (Fin n)) : Key n := Vector.ofFn (fun i => decide (i ∈ J))
@[simp] theorem support_fromSupport {n : ℕ} (J : Finset (Fin n)) : support (fromSupport J) = J := by
  ext i
  simp [fromSupport]

def generate : (n : ℕ) → ℕ → List (Key n)
  | 0,_ => [Vector.replicate 0 false]
  | n+1,r => (generate n r).map (prepend false) ++
      (if r=0 then [] else (generate n (r-1)).map (prepend true))

theorem mem_generate (n r : ℕ) (v : Key n) : v ∈ generate n r ↔ ones v ≤ r := by
  induction n generalizing r with
  | zero =>
    have hv : v = Vector.replicate 0 false := by ext i hi; omega
    simp [generate,hv,ones]
  | succ n ih =>
    have hv := prepend_tail v
    rw [← hv]
    cases hb : v.get 0 <;>
      simp only [generate,List.mem_append,List.mem_map,prepend_eq,ones_prepend]
    · by_cases hr : r=0 <;> simp [hr,ih]
    · by_cases hr : r=0 <;> simp [hr,ih]
      omega

theorem generate_nodup (n r : ℕ) : (generate n r).Nodup := by
  induction n generalizing r with
  | zero => simp [generate]
  | succ n ih =>
    simp only [generate]
    by_cases hr : r=0
    · simp only [if_pos hr,List.append_nil]
      exact (ih r).map (prepend_injective false)
    · rw [if_neg hr]
      apply List.nodup_append.mpr
      refine ⟨(ih r).map (prepend_injective false),(ih (r-1)).map (prepend_injective true),?_⟩
      intro z hz z' hz' he
      obtain ⟨v,_,rfl⟩ := List.mem_map.mp hz
      obtain ⟨w,_,rfl⟩ := List.mem_map.mp hz'
      have := (prepend_eq false true v w).mp he
      simp at this

theorem generated_supports (n r : ℕ) :
    ((generate n r).map support).toFinset = Finset.univ.filter (fun J : Finset (Fin n) => J.card ≤ r) := by
  ext J
  simp only [List.mem_toFinset,List.mem_map,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨v,hv,rfl⟩
    rw [support_card]
    exact (mem_generate n r v).mp hv
  · intro hJ
    refine ⟨fromSupport J,?_,support_fromSupport J⟩
    rw [mem_generate,← support_card,support_fromSupport]
    exact hJ

theorem generate_length (n r : ℕ) : (generate n r).length = CappedSubsetList.count n r := by
  have h := generated_supports n r
  have hc := congrArg Finset.card h
  rw [List.toFinset_card_of_nodup ((generate_nodup n r).map support_injective),List.length_map,
    ← CappedSubsetList.generate_toFinset,List.toFinset_card_of_nodup (CappedSubsetList.generate_nodup n r),
    CappedSubsetList.generate_length] at hc
  exact hc

structure Generated (n : ℕ) where
  keys : List (Key n)
  work : ℕ

/-- Each child vector is materialized. The allowance includes both mapped
lists, concatenation, retained result projection and recursion control. -/
def execute : (n : ℕ) → ℕ → Generated n
  | 0,_ => ⟨[Vector.replicate 0 false],10⟩
  | n+1,r =>
    let lo := execute n r
    if r=0 then
      ⟨lo.keys.map (prepend false),lo.work+(8*(n+1)+16)*lo.keys.length+16⟩
    else
      let hi := execute n (r-1)
      ⟨lo.keys.map (prepend false) ++ hi.keys.map (prepend true),
        lo.work+hi.work+(8*(n+1)+16)*(lo.keys.length+hi.keys.length)+16⟩

@[simp] theorem execute_keys (n r : ℕ) : (execute n r).keys = generate n r := by
  induction n generalizing r with
  | zero => rfl
  | succ n ih => simp only [execute,generate]; split <;> simp [*]

theorem work_le_length (n r : ℕ) :
    (execute n r).work ≤ (n+1)*(8*n+32)*(generate n r).length := by
  induction n generalizing r with
  | zero => simp [execute,generate]
  | succ n ih =>
    have hlo := ih r
    have hpos : 0 < (generate n r).length := by
      rw [generate_length]
      exact CappedSubsetList.count_pos n r
    by_cases hr : r=0
    · simp only [execute,generate,if_pos hr,List.append_nil,List.length_map,execute_keys]
      nlinarith
    · have hhi := ih (r-1)
      simp only [execute,generate,if_neg hr,List.length_append,List.length_map,execute_keys]
      nlinarith

theorem work_bound (n r : ℕ) :
    (execute n r).work ≤ (n+1)*(8*n+32)*CappedSubsetList.count n r := by
  simpa only [generate_length] using work_le_length n r

#print axioms prepend_zero
#print axioms prepend_succ
#print axioms tail_prepend
#print axioms toList_prepend
#print axioms prepend_injective
#print axioms mem_support
#print axioms prepend_tail
#print axioms prepend_eq
#print axioms ones_prepend
#print axioms support_card
#print axioms support_injective
#print axioms support_fromSupport
#print axioms mem_generate
#print axioms generate_nodup
#print axioms generated_supports
#print axioms generate_length
#print axioms execute_keys
#print axioms work_le_length
#print axioms work_bound
end ThinMatrix.CappedBitPreparation
