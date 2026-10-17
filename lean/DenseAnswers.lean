import Mathlib

/-!+# Dense all-pairs Boolean answer storage

Initialize n² Boolean cells once, then write true once for each returned pair.
The unordered fold is executable on the underlying list; commuting writes
prove it independent of that list's order. There is no finite-set membership
scan at output lookup. The counter measures RAM array-cell writes, including
initialization, rather than the runtime of a persistent Lean array library.
-/

namespace ThinMatrix.DenseAnswers

abbrev Pair (n : ℕ) := Fin n × Fin n
abbrev Output (n : ℕ) := Vector Bool (n*n) × ℕ

def address {n : ℕ} (p : Pair n) : Fin (n*n) := finProdFinEquiv p

theorem address_injective (n : ℕ) : Function.Injective (@address n) :=
  finProdFinEquiv.injective

def mark {n : ℕ} (p : Pair n) (out : Output n) : Output n :=
  (out.1.set (address p).val true (address p).isLt, out.2+1)

instance mark_leftCommutative (n : ℕ) : LeftCommutative (@mark n) := by
  constructor
  intro p q out
  apply Prod.ext
  · dsimp [mark]
    by_cases he : (address p).val = (address q).val
    · simp only [he, Vector.set_set]
    · exact Vector.set_comm true true (Ne.symm he)
  · simp only [mark]

def initial (n : ℕ) : Output n := (Vector.replicate (n*n) false, n*n)

def fromMultiset {n : ℕ} (answers : Multiset (Pair n)) : Output n :=
  answers.foldr mark (initial n)

def build {n : ℕ} (answers : Finset (Pair n)) : Output n :=
  fromMultiset answers.val

def read {n : ℕ} (out : Output n) (p : Pair n) : Bool :=
  out.1[(address p).val]

theorem read_mark {n : ℕ} (out : Output n) (p q : Pair n) :
    read (mark p out) q = if p = q then true else read out q := by
  simp only [read, mark, Vector.getElem_set]
  have he : (address p).val = (address q).val ↔ p=q := by
    constructor
    · intro h
      exact address_injective n (Fin.ext h)
    · intro h
      exact congrArg (fun r => (address r).val) h
  simp only [he]

theorem fromMultiset_correct {n : ℕ} (answers : Multiset (Pair n)) (p : Pair n) :
    read (fromMultiset answers) p = true ↔ p ∈ answers := by
  induction answers using Multiset.induction_on with
  | empty => simp [fromMultiset, initial, read]
  | cons q rest ih =>
    rw [fromMultiset, Multiset.foldr_cons]
    change read (mark q (fromMultiset rest)) p = true ↔ p ∈ q ::ₘ rest
    rw [read_mark]
    by_cases he : q=p
    · subst q; simp
    · simp [he, Ne.symm he, ih]

theorem build_correct {n : ℕ} (answers : Finset (Pair n)) (p : Pair n) :
    read (build answers) p = true ↔ p ∈ answers :=
  fromMultiset_correct answers.val p

theorem fromMultiset_writes {n : ℕ} (answers : Multiset (Pair n)) :
    (fromMultiset answers).2 = n*n + answers.card := by
  induction answers using Multiset.induction_on with
  | empty => simp [fromMultiset, initial]
  | cons p rest ih =>
    simp only [fromMultiset, Multiset.foldr_cons, mark, Multiset.card_cons]
    change (fromMultiset rest).2+1 = n*n+(rest.card+1)
    rw [ih]
    omega

theorem build_writes {n : ℕ} (answers : Finset (Pair n)) :
    (build answers).2 = n*n+answers.card := fromMultiset_writes answers.val

theorem build_writes_le {n : ℕ} (answers : Finset (Pair n)) :
    (build answers).2 ≤ 2*n*n := by
  rw [build_writes]
  have hc := Finset.card_le_univ answers
  simp only [Fintype.card_prod, Fintype.card_fin] at hc
  nlinarith

#print axioms build_correct
#print axioms build_writes
#print axioms build_writes_le

end ThinMatrix.DenseAnswers
