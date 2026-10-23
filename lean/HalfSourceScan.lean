import HalfSourceSelector

set_option autoImplicit false

/-!
# Retained first-valid scan

Each tested index and recursive suffix is evaluated once. The callback returns
its own work count. The scan adds one control charge per test and a terminal
charge; its bound does not silently give the callback free work. `run` receives
a stored list and stored rows. Their construction and binary representation
are separate obligations.
-/

namespace ThinMatrix.HalfSourceScan
open ThinMatrix.WalshEmbedding ThinMatrix.HalfSourceCoverage ThinMatrix.HalfSourceList

variable {A : Type*}

/-- The candidate occurrences are scanned in their given order, including duplicates. -/
def scan (test : A → Bool × ℕ) : List A → Option A × ℕ
  | [] => (none, 1)
  | a :: as =>
      let tested := test a
      if tested.1 then (some a, tested.2+1)
      else let rest := scan test as; (rest.1, tested.2+1+rest.2)

theorem scan_value (test : A → Bool × ℕ) (as : List A) :
    (scan test as).1 = as.find? (fun a => (test a).1) := by
  induction as with
  | nil => rfl
  | cons a as ih => cases ht : (test a).1 <;> simp [scan, ih, ht]

theorem scan_work (test : A → Bool × ℕ) (as : List A) (C : ℕ)
    (ht : ∀ a ∈ as, (test a).2 ≤ C) :
    (scan test as).2 ≤ as.length*(C+1)+1 := by
  induction as with
  | nil => simp [scan]
  | cons a as ih =>
    have ha := ht a (by simp)
    have hr := ih (fun b hb => ht b (by simp [hb]))
    simp only [scan]
    split
    · simp only [List.length_cons, Nat.succ_mul]
      omega
    · simp only [List.length_cons, Nat.succ_mul]
      omega

def run {J : ℕ} (cap : ℕ) (evaluate : Fin J → ℕ × ℕ) : Option (Fin J) × ℕ :=
  let result := scan (fun j => let tested := evaluate j; (decide (tested.1 ≤ cap), tested.2+1))
    (List.ofFn (fun j : Fin J => j))
  (result.1, result.2+2*J+1)

theorem run_eq_first {m J : ℕ} (weight : Fin J → ℕ) (evaluate : Fin J → ℕ × ℕ)
    (he : ∀ j, (evaluate j).1 = weight j) (hv : ∃ j, weight j ≤ m/2) :
    (run (m/2) evaluate).1 = some (firstIndex weight hv) := by
  rw [run, scan_value, List.find?_ofFn_eq_some]
  refine ⟨?_, firstIndex weight hv, rfl, ?_⟩
  · simp only [he, decide_eq_true_eq]
    exact firstIndex_valid weight hv
  · intro j hj
    simp only [he, decide_eq_true_eq, not_le]
    exact firstIndex_minimal weight hv j hj

/-- Include generation and storage of the J candidate indices. -/
theorem run_work {J : ℕ} (cap : ℕ) (evaluate : Fin J → ℕ × ℕ) (C : ℕ)
    (he : ∀ j, (evaluate j).2 ≤ C) :
    (run cap evaluate).2 ≤ J*(C+4)+2 := by
  have hb := scan_work (fun j => (decide ((evaluate j).1 ≤ cap), (evaluate j).2+1))
    (List.ofFn (fun j : Fin J => j)) (C+1) (fun j _ => Nat.add_le_add_right (he j) 1)
  simp only [List.length_ofFn] at hb
  unfold run
  dsimp only
  nlinarith

/-- Exact rational-selector refinement for a precomputed translation list.
The callback bound is explicit; it is not a cost claim for constructing the list. -/
theorem translations_run_eq (m : ℕ) (hm : 0 < m) (rows : Fin m → Cube m)
    (hr : ∀ i, rows i ≠ zeroBits m)
    (h : Cube m) (evaluate : Fin (translations m).length → ℕ × ℕ)
    (he : ∀ j, (evaluate j).1 = ones (rowMap rows (xorBits h ((translations m).get j)))) :
    (run (m/2) evaluate).1 = some (HalfSourceSelector.pick m hm rows hr h) :=
  run_eq_first _ evaluate he (translations_half_coverage m hm rows hr h)

#print axioms scan_value
#print axioms scan_work
#print axioms run_eq_first
#print axioms run_work
#print axioms translations_run_eq
end ThinMatrix.HalfSourceScan
