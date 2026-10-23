import CyclicLightWindow
import GroupedPreparation

set_option autoImplicit false

/-! Retained first-window selection. Counts, modular addresses, and traversal
charges use bounded natural registers and indexed arrays. They are explicit
control work, not a binary-machine implementation or Lean evaluator timing. -/
namespace ThinMatrix.WindowSelection
open GroupedPreparation (Counted)
open CyclicLightWindow
open scoped BigOperators

def countScan : List Bool → Counted ℕ
  | [] => ⟨0,1⟩
  | b::bs => let tail := countScan bs
             ⟨(if b then 1 else 0)+tail.value,tail.work+4⟩

theorem countScan_value (bs : List Bool) :
    (countScan bs).value = (bs.map fun b => if b then 1 else 0).sum := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [countScan,ih]

theorem countScan_work (bs : List Bool) : (countScan bs).work = 4*bs.length+1 := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp only [countScan,ih,List.length_cons]; omega

theorem countScan_vector {k : ℕ} (b : Vector Bool k) :
    (countScan b.toList).value = count b.get := by
  rw [countScan_value,←StoredGroupedCompletion.vector_sum]
  rfl

def window {k : ℕ} [NeZero k] (ell : ℕ) (b : Vector Bool k) (s : Fin k) : Vector Bool ell :=
  Vector.ofFn fun j => b.get (s+Fin.ofNat k j.val)

def evaluate {k : ℕ} [NeZero k] (ell : ℕ) (b : Vector Bool k) (s : Fin k) : ℕ × ℕ :=
  let stored := window ell b s
  let total := countScan stored.toList
  (total.value,total.work+10*ell+2)

theorem evaluate_value {k : ℕ} [NeZero k] (ell : ℕ) (b : Vector Bool k) (s : Fin k) :
    (evaluate ell b s).1 = weight ell b.get s := by
  simp only [evaluate,countScan_vector,count,window,Vector.get_ofFn]
  rfl

theorem evaluate_work {k : ℕ} [NeZero k] (ell : ℕ) (b : Vector Bool k) (s : Fin k) :
    (evaluate ell b s).2 = 14*ell+3 := by
  simp only [evaluate,countScan_work,Vector.length_toList]
  omega

def choose {k : ℕ} [NeZero k] (ell r : ℕ) (b : Vector Bool k) : Counted (Option (Fin k)) :=
  let total := countScan b.toList
  if total.value≤r then
    let found := HalfSourceScan.run (r*ell/k) (evaluate ell b)
    ⟨found.1,total.work+found.2+2*k+8⟩
  else ⟨none,total.work+2*k+8⟩

theorem choose_value {k : ℕ} [NeZero k] (ell r : ℕ) (b : Vector Bool k) :
    (choose ell r b).value = if h : count b.get≤r then some (first ell r b.get h) else none := by
  simp only [choose,countScan_vector]
  split
  · have h := HalfSourceScan.run_eq_first (m:=2*(r*ell/k)) (weight ell b.get) (evaluate ell b)
      (evaluate_value ell b) (by simpa using exists_light ell r b.get ‹count b.get≤r›)
    simpa [first] using h
  · rfl

def budget (k ell : ℕ) : ℕ := k*(14*ell+7)+6*k+12

theorem choose_work {k : ℕ} [NeZero k] (ell r : ℕ) (b : Vector Bool k) :
    (choose ell r b).work ≤ budget k ell := by
  have h := HalfSourceScan.run_work (r*ell/k) (evaluate ell b) (14*ell+3)
    (fun s => le_of_eq (evaluate_work ell b s))
  rw [show 14*ell+3+4=14*ell+7 by omega] at h
  simp only [choose,countScan_work,Vector.length_toList,budget]
  split <;> dsimp only <;> omega

theorem choose_none_iff {k : ℕ} [NeZero k] (ell r : ℕ) (b : Vector Bool k) :
    (choose ell r b).value=none ↔ r<count b.get := by
  rw [choose_value]
  split <;> simp_all

theorem choose_valid {k : ℕ} [NeZero k] (ell r : ℕ) (b : Vector Bool k) (s : Fin k)
    (h : (choose ell r b).value=some s) :
    count b.get≤r ∧ weight ell b.get s≤r*ell/k ∧
      ∀ j<s, r*ell/k<weight ell b.get j := by
  rw [choose_value] at h
  split at h
  · have hs := Option.some.inj h
    subst s
    exact ⟨‹count b.get≤r›,first_valid _ _ _ _,fun j hj => first_minimal _ _ _ _ j hj⟩
  · contradiction

/-- Native base-three decoding retains every prefix vector and prices its
copy. There is no runtime inverse-equivalence call or exponentiation. -/
def decode : (n : ℕ) → ℕ → Counted (Vector (Fin 3) n)
  | 0, _ => ⟨Vector.ofFn Fin.elim0,2⟩
  | n+1, a =>
      let rest := decode n (a/3)
      ⟨Vector.ofFn (Fin.cases ⟨a%3,Nat.mod_lt _ (by decide)⟩ rest.value.get),
        rest.work+6*(n+1)+10⟩

theorem decode_get (n a : ℕ) (j : Fin n) : ((decode n a).value.get j).val = a/3^j.val%3 := by
  induction n generalizing a with
  | zero => exact j.elim0
  | succ n ih =>
    refine Fin.cases ?_ (fun i => ?_) j
    · simp [decode]
    · simp only [decode,Vector.get_ofFn,Fin.cases_succ,ih,Fin.val_succ,pow_succ',Nat.div_div_eq_div_mul]

theorem decode_index (n : ℕ) (i : Fin (3^n)) :
    (decode n i.val).value.get = (StoredGroupedCompletion.rawIndex n).symm i := by
  funext j
  apply Fin.ext
  exact decode_get n i.val j

theorem decode_work (n a : ℕ) : (decode n a).work ≤ n*(6*n+16)+2 := by
  induction n generalizing a with
  | zero => simp [decode]
  | succ n ih =>
    have h := ih (a/3)
    simp only [decode]
    nlinarith

#print axioms countScan_value
#print axioms countScan_work
#print axioms countScan_vector
#print axioms evaluate_value
#print axioms evaluate_work
#print axioms choose_value
#print axioms choose_work
#print axioms choose_none_iff
#print axioms choose_valid
#print axioms decode_get
#print axioms decode_index
#print axioms decode_work
end ThinMatrix.WindowSelection
