import HalfSourceScan

set_option autoImplicit false

/-!
# Stored-row weight tests and retained selector work

This is an indexed Boolean/register evaluator. Each column iteration charges
six read/gate/control operations; the row loop charges four more operations,
including a bounded natural-counter increment. The input to `run` is a stored
translation list and stored inverse rows. Cube indexing denotes a bounded
indexed read. This does not price the construction of either input, nor claim
that Lean's function closures or unbounded Nat arithmetic have unit bit cost.
-/
namespace ThinMatrix.HalfSourceMaskWork
open ThinMatrix.WalshEmbedding ThinMatrix.HalfSourceCoverage ThinMatrix.HalfSourceList
open scoped BigOperators

def dotRun : (m : ℕ) → Cube m → Cube m → Bool × ℕ
  | 0, _, _ => (false, 1)
  | m+1, a, b =>
      let head := a 0 && b 0
      let tail := dotRun m (Fin.tail a) (Fin.tail b)
      (Bool.xor head tail.1, tail.2+6)

theorem dotRun_value (m : ℕ) (a b : Cube m) : (dotRun m a b).1 = dotBits a b := by
  induction m with
  | zero => simp [dotRun, dotBits, parity]
  | succ m ih => simp only [dotRun, ih, dotBits, List.ofFn_succ, parity, Fin.tail]

theorem dotRun_work (m : ℕ) (a b : Cube m) : (dotRun m a b).2 = 6*m+1 := by
  induction m with
  | zero => rfl
  | succ m ih => simp only [dotRun, ih]; omega

def rowsRun {m : ℕ} : (n : ℕ) → (Fin n → Cube m) → Cube m → ℕ × ℕ
  | 0, _, _ => (0, 1)
  | n+1, rows, v =>
      let bit := dotRun m (rows 0) v
      let rest := rowsRun n (Fin.tail rows) v
      ((if bit.1 then rest.1+1 else rest.1), bit.2+rest.2+4)

theorem rowsRun_value {m : ℕ} (n : ℕ) (rows : Fin n → Cube m) (v : Cube m) :
    (rowsRun n rows v).1 = ∑ i, if dotBits (rows i) v then 1 else 0 := by
  induction n with
  | zero => simp [rowsRun]
  | succ n ih =>
    rw [rowsRun]
    dsimp only
    rw [dotRun_value, ih, Fin.sum_univ_succ]
    have ht : (∑ i : Fin n, if dotBits (Fin.tail rows i) v then 1 else 0 : ℕ) =
        ∑ i : Fin n, if dotBits (rows i.succ) v then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      rfl
    rw [ht]
    split_ifs <;> omega

theorem rowsRun_work {m : ℕ} (n : ℕ) (rows : Fin n → Cube m) (v : Cube m) :
    (rowsRun n rows v).2 = n*(6*m+5)+1 := by
  induction n with
  | zero => simp [rowsRun]
  | succ n ih => simp only [rowsRun, dotRun_work, ih, Nat.succ_mul]; omega

/-- Evaluate one stored translation. The xor vector is materialized once and
charged for all m entries before the matrix-vector scan. -/
def evaluate {m : ℕ} (rows : Fin m → Cube m) (h d : Cube m) : ℕ × ℕ :=
  let shifted := List.ofFn (fun i => Bool.xor (h i) (d i))
  let v : Cube m := fun i => shifted[i.val]'(by simp [shifted])
  let result := rowsRun m rows v
  (result.1, result.2+4*m)

theorem evaluate_value {m : ℕ} (rows : Fin m → Cube m) (h d : Cube m) :
    (evaluate rows h d).1 = ones (rowMap rows (xorBits h d)) := by
  simp only [evaluate, List.getElem_ofFn, rowsRun_value]
  simp only [ones, rowMap, Finset.card_eq_sum_ones, Finset.sum_filter]
  rfl

theorem evaluate_work {m : ℕ} (rows : Fin m → Cube m) (h d : Cube m) :
    (evaluate rows h d).2 = m*(6*m+5)+1+4*m := by
  simp only [evaluate, rowsRun_work]

/-- The retained scan, including every tested weight computation and comparison. -/
def run {m : ℕ} (rows : Fin m → Cube m) (h : Cube m) (ds : List (Cube m)) :
    Option (Fin ds.length) × ℕ :=
  HalfSourceScan.run (m/2) (fun j => evaluate rows h (ds.get j))

theorem run_refines_pick (m : ℕ) (hm : 0 < m) (rows : Fin m → Cube m)
    (hr : ∀ i, rows i ≠ zeroBits m) (h : Cube m) :
    (run rows h (translations m)).1 = some (HalfSourceSelector.pick m hm rows hr h) :=
  HalfSourceScan.translations_run_eq m hm rows hr h _ (fun _ => evaluate_value _ _ _)

theorem run_work {m : ℕ} (rows : Fin m → Cube m) (h : Cube m) (ds : List (Cube m)) :
    (run rows h ds).2 ≤ ds.length*(m*(6*m+5)+4*m+5)+2 := by
  have he := HalfSourceScan.run_work (m/2) (fun j => evaluate rows h (ds.get j))
    (m*(6*m+5)+1+4*m) (fun j => le_of_eq (evaluate_work rows h (ds.get j)))
  unfold run
  convert he using 1
  ring

theorem translations_work (m : ℕ) (rows : Fin m → Cube m) (h : Cube m) :
    (run rows h (translations m)).2 ≤ 64*m^3*(m*(6*m+5)+4*m+5)+2 := by
  simpa only [translations_length] using run_work rows h (translations m)

#print axioms dotRun_value
#print axioms dotRun_work
#print axioms rowsRun_value
#print axioms rowsRun_work
#print axioms evaluate_value
#print axioms evaluate_work
#print axioms run_refines_pick
#print axioms run_work
#print axioms translations_work
end ThinMatrix.HalfSourceMaskWork
