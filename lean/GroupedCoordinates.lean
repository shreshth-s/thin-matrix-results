import CappedBitPreparation

set_option autoImplicit false

/-! Linear retained scans for signed ternary addresses and subset selectors.
Address arithmetic is in the bounded-register model; coefficient arithmetic
is priced separately. No powers or function-equivalence evaluation execute
inside the scans. -/
namespace ThinMatrix.GroupedCoordinates
open CappedBitPreparation CroppedGroupedSuffix
open scoped BigOperators

structure Coordinate where
  index : ℕ
  negative : Bool
  work : ℕ

def digit (p k : Bool) : ℕ := if k then 2 else if p then 1 else 0

def scan : List (Bool × Bool) → Coordinate
  | [] => ⟨0,false,2⟩
  | (p,k)::xs =>
      let rest := scan xs
      ⟨digit p k+3*rest.index,Bool.xor (p && k) rest.negative,rest.work+12⟩

theorem scan_work (xs : List (Bool × Bool)) : (scan xs).work = 12*xs.length+2 := by
  induction xs with
  | nil => rfl
  | cons x xs ih => rcases x with ⟨p,k⟩; simp only [scan,ih,List.length_cons]; omega

theorem scan_index_lt (xs : List (Bool × Bool)) : (scan xs).index < 3^xs.length := by
  induction xs with
  | nil => simp [scan]
  | cons x xs ih =>
    rcases x with ⟨p,k⟩
    have hd : digit p k ≤ 2 := by cases p <;> cases k <;> decide
    simp only [scan,List.length_cons,pow_succ]
    nlinarith

theorem scan_index (n : ℕ) (p k : Fin n → Bool) :
    (scan (List.ofFn (fun i => (p i,k i)))).index = ∑ i, digit (p i) (k i)*3^i.val := by
  induction n with
  | zero => simp [scan]
  | succ n ih =>
    simp only [List.ofFn_succ,scan,ih,Fin.sum_univ_succ,Fin.val_zero,pow_zero,mul_one,
      Fin.val_succ,pow_succ]
    rw [Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring

theorem sign_xor {R : Type*} [CommRing R] (a b : Bool) :
    sign (R := R) (Bool.xor a b) = sign a*sign b := by cases a <;> cases b <;> simp [sign]

theorem scan_sign {R : Type*} [CommRing R] (n : ℕ) (p k : Fin n → Bool) :
    sign (R := R) (scan (List.ofFn (fun i => (p i,k i)))).negative =
      ∏ i, if k i then sign (p i) else 1 := by
  induction n with
  | zero => simp [scan,sign]
  | succ n ih =>
    simp only [List.ofFn_succ,scan,sign_xor,ih,Fin.prod_univ_succ]
    congr 1
    cases hp : p 0 <;> cases hk : k 0 <;> simp [sign]

def coordinates {n : ℕ} (p k : Key n) : Coordinate :=
  let out := scan (List.ofFn (fun i => (p.get i,k.get i)))
  ⟨out.index,out.negative,out.work+16*n+6⟩

theorem coordinates_index {n : ℕ} (p k : Key n) :
    (coordinates p k).index = (StoredGroupedCompletion.rawIndex n (word p.get (support k))).val := by
  rw [StoredGroupedCompletion.rawIndex,finFunctionFinEquiv_apply]
  simp only [coordinates,scan_index]
  apply Finset.sum_congr rfl
  intro i _
  cases hp : p.get i <;> cases hk : k.get i <;> simp [digit,word,pairLetter,hp,hk]

theorem coordinates_lt {n : ℕ} (p k : Key n) : (coordinates p k).index < 3^n := by
  rw [coordinates_index]
  exact (StoredGroupedCompletion.rawIndex n (word p.get (support k))).isLt

theorem coordinates_sign {R : Type*} [CommRing R] {n : ℕ} (p k : Key n) :
    sign (R := R) (coordinates p k).negative = signed p.get (support k) := by
  simp only [coordinates,scan_sign,signed,support,Finset.prod_filter]

theorem coordinates_work {n : ℕ} (p k : Key n) : (coordinates p k).work = 28*n+8 := by
  simp only [coordinates,scan_work,List.length_ofFn]
  omega

def subsetScan : List (Bool × Bool) → Bool × ℕ
  | [] => (true,2)
  | (k,a)::xs =>
      let rest := subsetScan xs
      ((!k || a) && rest.1,rest.2+10)

theorem subsetScan_value (xs : List (Bool × Bool)) :
    (subsetScan xs).1 = true ↔ ∀ x ∈ xs, x.1 = true → x.2 = true := by
  induction xs with
  | nil => simp [subsetScan]
  | cons x xs ih =>
    rcases x with ⟨k,a⟩
    cases k <;> cases a <;> simp [subsetScan,ih]

theorem subsetScan_work (xs : List (Bool × Bool)) : (subsetScan xs).2 = 10*xs.length+2 := by
  induction xs with
  | nil => rfl
  | cons x xs ih => rcases x with ⟨k,a⟩; simp only [subsetScan,ih,List.length_cons]; omega

def subset {n : ℕ} (k a : Key n) : Bool × ℕ :=
  let out := subsetScan (List.ofFn (fun i => (k.get i,a.get i)))
  (out.1,out.2+16*n+6)

theorem subset_correct {n : ℕ} (k a : Key n) : (subset k a).1 = decide (support k ⊆ support a) := by
  apply Bool.eq_iff_iff.mpr
  simp only [subset,subsetScan_value,decide_eq_true_eq,Finset.subset_iff,mem_support]
  constructor
  · intro h i hi
    exact h (k.get i,a.get i) (List.mem_ofFn.mpr ⟨i,rfl⟩) hi
  · intro h x hx
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
    exact fun hi => h hi

theorem subset_work {n : ℕ} (k a : Key n) : (subset k a).2 = 26*n+8 := by
  simp only [subset,subsetScan_work,List.length_ofFn]
  omega

#print axioms scan_work
#print axioms scan_index_lt
#print axioms scan_index
#print axioms sign_xor
#print axioms scan_sign
#print axioms coordinates_index
#print axioms coordinates_lt
#print axioms coordinates_sign
#print axioms coordinates_work
#print axioms subsetScan_value
#print axioms subsetScan_work
#print axioms subset_correct
#print axioms subset_work
end ThinMatrix.GroupedCoordinates
