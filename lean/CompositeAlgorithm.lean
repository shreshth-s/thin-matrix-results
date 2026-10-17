import CompositeCertification

/-!
# An instrumented deterministic composite-count program

The program below calls an exact modular-count oracle on every unused
candidate, caches the returned tables, and minimizes totals of `C`, never
totals of the unobservable `F` or `Z`. Lists of primes are sorted, and
`List.argmin` breaks ties by the first list entry. The final round takes
separate minima for each incidence. Each restart begins at modulus one.

The resource counters count actual oracle invocations and explicit finite
table/selector/incident visits. They are a semantic resource interface,
not a word-RAM cost model for Lean's finite-set implementation.

`CompositeCertification.GreedyTrace` hardcodes a `Classical.choose` tie
rule. This module's `OracleTrace` instead records the actual computable
minimum and proves contraction from the same previously proved averaging
lemma. Equality of these different tie rules is neither needed nor assumed.
-/

namespace ThinMatrix.CompositeAlgorithm

open Finset
open CompositeCertification

variable {X V Pair : Type*} [DecidableEq Pair]

structure CountOracle (X : Type*) where
  table : ℕ → Finset X → X → ℕ

def CountOracle.Correct (O : CountOracle X) (A : Instance X V) : Prop :=
  ∀ d active x, x ∈ active → O.table d active x = A.modCount d x

structure Call (X : Type*) where
  modulus : ℕ
  active : Finset X

abbrev Row (X : Type*) := ℕ × (X → ℕ)

def evaluate (O : CountOracle X) (active : Finset X) (d : ℕ) (pool : Finset ℕ) :
    List (Row X) :=
  (pool.sort (· ≤ ·)).map (fun p => (p, O.table (d * p) active))

def tableTotal (active : Finset X) (row : Row X) : ℕ := ∑ x ∈ active, row.2 x

/-- Cache each score once before the argmin scan. In particular comparisons
do not repeatedly rescan entire count tables. -/
def pick (rows : List (Row X)) (score : Row X → ℕ) : Row X :=
  (((rows.map (fun row => (score row, row))).argmin Prod.fst).getD
    (0, (0, fun _ => 0))).2

theorem pick_spec (rows : List (Row X)) (score : Row X → ℕ) (hne : rows ≠ []) :
    pick rows score ∈ rows ∧ ∀ row ∈ rows, score (pick rows score) ≤ score row := by
  cases harg : (rows.map (fun row => (score row, row))).argmin Prod.fst with
  | none =>
      have hnil := List.argmin_eq_none.mp harg
      have hl := congrArg List.length hnil
      simp only [List.length_map, List.length_nil] at hl
      exact False.elim (hne (List.length_eq_zero_iff.mp hl))
  | some scored =>
      have hm : scored ∈ (rows.map (fun row => (score row, row))).argmin Prod.fst := by
        simp [harg]
      obtain ⟨row, hr, heq⟩ := List.mem_map.mp (List.argmin_mem hm)
      subst scored
      simp only [pick, harg, Option.getD_some]
      refine ⟨hr, ?_⟩
      intro r hrow
      have hle := List.le_of_mem_argmin
        (List.mem_map.mpr ⟨r, hrow, rfl⟩) hm
      exact hle

theorem evaluate_length (O : CountOracle X) (active : Finset X) (d : ℕ) (pool : Finset ℕ) :
    (evaluate O active d pool).length = pool.card := by simp [evaluate]

theorem evaluate_nonempty (O : CountOracle X) (active : Finset X) (d : ℕ)
    (pool : Finset ℕ) (hne : pool.Nonempty) : evaluate O active d pool ≠ [] := by
  have hl := evaluate_length O active d pool
  have hp := Finset.card_pos.mpr hne
  intro heq
  simp [heq] at hl
  omega

theorem mem_evaluate (O : CountOracle X) (active : Finset X) (d : ℕ) (pool : Finset ℕ)
    (row : Row X) : row ∈ evaluate O active d pool ↔
      ∃ p ∈ pool, row = (p, O.table (d * p) active) := by
  simp only [evaluate, List.mem_map, Finset.mem_sort]
  aesop

theorem total_correct (O : CountOracle X) (A : Instance X V) (hO : O.Correct A)
    (active : Finset X) (d p : ℕ) :
    tableTotal active (p, O.table (d * p) active) = A.totalCount active (d * p) := by
  exact Finset.sum_congr rfl (fun x hx => hO _ _ _ hx)

theorem selected_spec (O : CountOracle X) (A : Instance X V) (hO : O.Correct A)
    (active : Finset X) (d : ℕ) (pool : Finset ℕ) (hne : pool.Nonempty) :
    let row := pick (evaluate O active d pool) (tableTotal active)
    row.1 ∈ pool ∧ (∀ x ∈ active, row.2 x = A.modCount (d * row.1) x) ∧
      ∀ p ∈ pool, A.totalCount active (d * row.1) ≤ A.totalCount active (d * p) := by
  dsimp only
  have hs := pick_spec (evaluate O active d pool) (tableTotal active)
    (evaluate_nonempty O active d pool hne)
  obtain ⟨p, hp, heq⟩ := (mem_evaluate O active d pool _).mp hs.1
  rw [heq]
  refine ⟨hp, fun x hx => hO _ _ _ hx, ?_⟩
  intro q hq
  have hmin := hs.2 (q, O.table (d * q) active)
    ((mem_evaluate O active d pool _).mpr ⟨q, hq, rfl⟩)
  rw [heq, total_correct O A hO, total_correct O A hO] at hmin
  exact hmin

structure GreedyResult (X : Type*) where
  modulus : ℕ
  available : Finset ℕ
  base : X → ℕ
  calls : List (Call X)
  bookkeeping : ℕ

/-- One call per candidate; the selected returned table is retained as the
next base table, so the program makes no extra base-modulus oracle call. -/
def greedy (O : CountOracle X) (active : Finset X) :
    ℕ → ℕ → Finset ℕ → (X → ℕ) → GreedyResult X
  | 0, d, pool, base => ⟨d, pool, base, [], 0⟩
  | n + 1, d, pool, _base =>
      let rows := evaluate O active d pool
      let row := pick rows (tableTotal active)
      let tail := greedy O active n (d * row.1) (pool.erase row.1) row.2
      { tail with
        calls := (pool.sort (· ≤ ·)).map (fun p => ⟨d * p, active⟩) ++ tail.calls
        -- Three visits per cell cover score reading/caching and selection;
        -- four per prime cover comparisons, row selection, and erasure.
        bookkeeping := 3 * pool.card * active.card + 4 * pool.card + tail.bookkeeping }

/-- A trace with the actual executable tie rule replaced only by its
proved minimum specification; no contraction is part of this definition. -/
inductive OracleTrace (A : Instance X V) (active : Finset X)
    (initial : Finset ℕ) (startModulus : ℕ) : ℕ → ℕ → Finset ℕ → Prop
  | start : OracleTrace A active initial startModulus 0 startModulus initial
  | step {n d pool p} (previous : OracleTrace A active initial startModulus n d pool)
      (hp : p ∈ pool)
      (hmin : ∀ q ∈ pool, A.totalCount active (d * p) ≤ A.totalCount active (d * q)) :
      OracleTrace A active initial startModulus (n + 1) (d * p) (pool.erase p)

theorem trace_subset (A : Instance X V) (active : Finset X) (initial : Finset ℕ)
    (d0 : ℕ) {n d : ℕ} {pool : Finset ℕ}
    (tr : OracleTrace A active initial d0 n d pool) : pool ⊆ initial := by
  induction tr with
  | start => exact Finset.Subset.refl _
  | step previous hp hmin ih => exact (Finset.erase_subset _ _).trans ih

theorem trace_card (A : Instance X V) (active : Finset X) (initial : Finset ℕ)
    (d0 : ℕ) {n d : ℕ} {pool : Finset ℕ}
    (tr : OracleTrace A active initial d0 n d pool) : pool.card + n = initial.card := by
  induction tr with
  | start => simp
  | step previous hp hmin ih =>
      have hc := Finset.card_erase_add_one hp
      omega

theorem minimizing_contraction (A : Instance X V) (active : Finset X)
    (pool : Finset ℕ) (lam d p : ℕ) (hdiv : A.DivisorBound pool lam)
    (hmin : ∀ q ∈ pool, A.totalCount active (d * p) ≤ A.totalCount active (d * q)) :
    pool.card * A.falseMass active (d * p) ≤ lam * A.falseMass active d := by
  have hf : ∀ q ∈ pool, A.falseMass active (d * p) ≤ A.falseMass active (d * q) := by
    intro q hq
    have hm := hmin q hq
    simp only [A.totalCount_eq] at hm
    omega
  calc
    _ = ∑ _q ∈ pool, A.falseMass active (d * p) := by simp
    _ ≤ ∑ q ∈ pool, A.falseMass active (d * q) := Finset.sum_le_sum hf
    _ ≤ _ := A.sum_falseMass_le active pool lam d hdiv

theorem trace_append (A : Instance X V) (active : Finset X) (initial : Finset ℕ)
    (d0 : ℕ) {n d m e : ℕ} {pool last : Finset ℕ}
    (first : OracleTrace A active initial d0 n d pool)
    (second : OracleTrace A active pool d m e last) :
    OracleTrace A active initial d0 (n + m) e last := by
  induction second with
  | start => simpa using first
  | step previous hp hmin ih =>
      simpa [Nat.add_assoc] using OracleTrace.step ih hp hmin

theorem greedy_correct (O : CountOracle X) (A : Instance X V) (hO : O.Correct A)
    (active : Finset X) (n d : ℕ) (pool : Finset ℕ) (base : X → ℕ)
    (hn : n ≤ pool.card) (hbase : ∀ x ∈ active, base x = A.modCount d x) :
    let out := greedy O active n d pool base
    OracleTrace A active pool d n out.modulus out.available ∧
      ∀ x ∈ active, out.base x = A.modCount out.modulus x := by
  induction n generalizing d pool base with
  | zero => exact ⟨OracleTrace.start, hbase⟩
  | succ n ih =>
      have hne : pool.Nonempty := Finset.card_pos.mp (by omega)
      let row := pick (evaluate O active d pool) (tableTotal active)
      have hs := selected_spec O A hO active d pool hne
      change row.1 ∈ pool ∧ (∀ x ∈ active, row.2 x = A.modCount (d * row.1) x) ∧
        (∀ p ∈ pool, A.totalCount active (d * row.1) ≤ A.totalCount active (d * p)) at hs
      have hc := Finset.card_erase_add_one hs.1
      have ht := ih (d * row.1) (pool.erase row.1) row.2 (by omega) hs.2.1
      have hhead : OracleTrace A active pool d 1 (d * row.1) (pool.erase row.1) :=
        OracleTrace.step OracleTrace.start hs.1 hs.2.2
      refine ⟨?_, ht.2⟩
      simpa [greedy, row, Nat.add_comm] using trace_append A active pool d hhead ht.1

theorem greedy_subset (O : CountOracle X) (active : Finset X) (n d : ℕ)
    (pool : Finset ℕ) (base : X → ℕ) :
    (greedy O active n d pool base).available ⊆ pool := by
  induction n generalizing d pool base with
  | zero => exact Finset.Subset.refl _
  | succ n ih => exact (ih _ _ _).trans (Finset.erase_subset _ _)

theorem greedy_calls_bound (O : CountOracle X) (active : Finset X) (n d : ℕ)
    (pool : Finset ℕ) (base : X → ℕ) :
    (greedy O active n d pool base).calls.length ≤ n * pool.card := by
  induction n generalizing d pool base with
  | zero => simp [greedy]
  | succ n ih =>
      simp only [greedy, List.length_append, List.length_map, Finset.length_sort]
      have ht := ih (d * (pick (evaluate O active d pool) (tableTotal active)).1)
        (pool.erase (pick (evaluate O active d pool) (tableTotal active)).1)
        (pick (evaluate O active d pool) (tableTotal active)).2
      have he : (pool.erase (pick (evaluate O active d pool) (tableTotal active)).1).card ≤
          pool.card := Finset.card_le_card (Finset.erase_subset _ _)
      have hm := Nat.mul_le_mul_left n he
      nlinarith

theorem greedy_bookkeeping_bound (O : CountOracle X) (active : Finset X) (n d : ℕ)
    (pool : Finset ℕ) (base : X → ℕ) :
    (greedy O active n d pool base).bookkeeping ≤
      n * (3 * pool.card * active.card + 4 * pool.card) := by
  induction n generalizing d pool base with
  | zero => simp [greedy]
  | succ n ih =>
      simp only [greedy]
      have ht := ih (d * (pick (evaluate O active d pool) (tableTotal active)).1)
        (pool.erase (pick (evaluate O active d pool) (tableTotal active)).1)
        (pick (evaluate O active d pool) (tableTotal active)).2
      have he : (pool.erase (pick (evaluate O active d pool) (tableTotal active)).1).card ≤
          pool.card := Finset.card_le_card (Finset.erase_subset _ _)
      have hcell := Nat.mul_le_mul_right active.card he
      have hunit := Nat.mul_le_mul_left 2 he
      have hm := Nat.mul_le_mul_left n (Nat.add_le_add hcell hunit)
      nlinarith

def batchMinimum (rows : List (Row X)) (x : X) : ℕ := (pick rows (fun row => row.2 x)).2 x

theorem batchMinimum_eq (O : CountOracle X) (A : Instance X V) (hO : O.Correct A)
    (active : Finset X) (d : ℕ) (pool : Finset ℕ) (hne : pool.Nonempty)
    {x : X} (hx : x ∈ active) :
    batchMinimum (evaluate O active d pool) x = A.minCount pool hne d x := by
  let rows := evaluate O active d pool
  let row := pick rows (fun row => row.2 x)
  have hs := pick_spec rows (fun row => row.2 x) (evaluate_nonempty O active d pool hne)
  obtain ⟨p, hp, heq⟩ := (mem_evaluate O active d pool _).mp hs.1
  have hvalue : row.2 x = A.modCount (d * p) x := by
    change (pick rows (fun row => row.2 x)).2 x = _
    rw [heq]
    exact hO _ _ _ hx
  apply le_antisymm
  · apply Finset.le_min'
    intro v hv
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hv
    have hm := hs.2 (q, O.table (d * q) active)
      ((mem_evaluate O active d pool _).mpr ⟨q, hq, rfl⟩)
    exact hm.trans_eq (hO _ _ _ hx)
  · change A.minCount pool hne d x ≤ row.2 x
    rw [hvalue]
    exact A.minCount_le pool hne d x hp

structure StageResult (X Pair : Type*) where
  active : Finset X
  marked : Finset Pair
  calls : List (Call X)
  bookkeeping : ℕ

/-- Both final filters read the already returned candidate tables. Original
integer values are absent from the certification tests. -/
def stage (O : CountOracle X) (A : Instance X V) (pair : X → Pair)
    (lam k : ℕ) (pool : Finset ℕ) (active : Finset X) (marked : Finset Pair) :
    StageResult X Pair :=
  let selected := greedy O active k 1 pool (fun x => (A.block x).card)
  let rows := evaluate O active selected.modulus selected.available
  let mu := batchMinimum rows
  let yes := active.filter (fun x => lam * selected.base x < selected.available.card * mu x)
  let marked' := marked ∪ yes.image pair
  let active' := active.filter (fun x => mu x ≠ 0 ∧
    selected.available.card * mu x ≤ lam * selected.base x ∧ pair x ∉ marked')
  { active := active'
    marked := marked'
    calls := selected.calls ++ (selected.available.sort (· ≤ ·)).map
      (fun p => ⟨selected.modulus * p, active⟩)
    -- Score reads, candidate comparisons/erasure, per-pair minimum reads,
    -- score caches/comparisons, and final predicate/image/member visits
    -- are charged conservatively. `mu` is evaluated at most three times
    -- per incidence by these two predicates, not assumed memoized.
    bookkeeping := selected.bookkeeping + 12 * selected.available.card * active.card +
      12 * active.card + 4 * selected.available.card }

theorem stage_semantics (O : CountOracle X) (A : Instance X V) (hO : O.Correct A)
    (pair : X → Pair) (lam k : ℕ) (pool : Finset ℕ) (active : Finset X)
    (marked : Finset Pair) (hk : k ≤ pool.card)
    (hne : (greedy O active k 1 pool (fun x => (A.block x).card)).available.Nonempty) :
    let selected := greedy O active k 1 pool (fun x => (A.block x).card)
    (stage O A pair lam k pool active marked).marked =
      A.markedAfter pair marked active selected.available hne lam selected.modulus ∧
    (stage O A pair lam k pool active marked).active =
      A.survivors pair marked active selected.available hne lam selected.modulus := by
  let selected := greedy O active k 1 pool (fun x => (A.block x).card)
  have hg := greedy_correct O A hO active k 1 pool (fun x => (A.block x).card) hk
    (fun x hx => (A.count_one x).symm)
  have hb : ∀ x ∈ active, selected.base x = A.modCount selected.modulus x := hg.2
  have hm : ∀ x ∈ active,
      batchMinimum (evaluate O active selected.modulus selected.available) x =
        A.minCount selected.available hne selected.modulus x :=
    fun x hx => batchMinimum_eq O A hO active selected.modulus selected.available hne hx
  have hy : active.filter (fun x => lam * selected.base x < selected.available.card *
      batchMinimum (evaluate O active selected.modulus selected.available) x) =
      A.certified active selected.available hne lam selected.modulus := by
    ext x
    simp only [Instance.certified, Finset.mem_filter]
    constructor
    · rintro ⟨hx, htest⟩
      exact ⟨hx, by simpa only [hb x hx, hm x hx] using htest⟩
    · rintro ⟨hx, htest⟩
      exact ⟨hx, by simpa only [hb x hx, hm x hx] using htest⟩
  have hmark : (stage O A pair lam k pool active marked).marked =
      A.markedAfter pair marked active selected.available hne lam selected.modulus := by
    change marked ∪ _ = marked ∪ _
    rw [hy]
  refine ⟨hmark, ?_⟩
  dsimp only [selected] at hb hm hmark
  change active.filter (fun x => batchMinimum _ x ≠ 0 ∧ _ ∧
    pair x ∉ (stage O A pair lam k pool active marked).marked) = _
  ext x
  simp only [Instance.survivors, Finset.mem_filter]
  rw [hmark]
  constructor
  · rintro ⟨hx, hp, hf, hn⟩
    exact ⟨hx, by simpa only [hm x hx] using hp,
      by simpa only [hb x hx, hm x hx] using hf, hn⟩
  · rintro ⟨hx, hp, hf, hn⟩
    exact ⟨hx, by simpa only [hm x hx] using hp,
      by simpa only [hb x hx, hm x hx] using hf, hn⟩

theorem trace_contraction (A : Instance X V) (active : Finset X) (initial : Finset ℕ)
    (d0 : ℕ) {n d : ℕ} {pool : Finset ℕ}
    (tr : OracleTrace A active initial d0 n d pool) (M lam : ℕ)
    (hsize : M + n ≤ initial.card) (hdiv : A.DivisorBound initial lam) :
    M ^ n * A.falseMass active d ≤ lam ^ n * A.falseMass active d0 := by
  induction tr with
  | start => simp
  | @step n d pool p previous hp hmin ih =>
      have hprev := ih (by omega)
      have hc := trace_card A active initial d0 previous
      have hm : M ≤ pool.card := by omega
      have hb := A.divisorBound_subset hdiv (trace_subset A active initial d0 previous)
      have hg := minimizing_contraction A active pool lam d p hb hmin
      have hs : M * A.falseMass active (d * p) ≤ lam * A.falseMass active d :=
        (Nat.mul_le_mul_right _ hm).trans hg
      calc
        _ = M ^ n * (M * A.falseMass active (d * p)) := by rw [pow_succ]; ring
        _ ≤ M ^ n * (lam * A.falseMass active d) := Nat.mul_le_mul_left _ hs
        _ = lam * (M ^ n * A.falseMass active d) := by ring
        _ ≤ lam * (lam ^ n * A.falseMass active d0) := Nat.mul_le_mul_left _ hprev
        _ = _ := by rw [pow_succ]; ring

theorem trace_halves (A : Instance X V) (pair : X → Pair) (marked : Finset Pair)
    (active : Finset X) (initial : Finset ℕ) {k d : ℕ} {available : Finset ℕ}
    (tr : OracleTrace A active initial 1 k d available) (hne : available.Nonempty)
    (M lam h : ℕ) (hM : lam < M) (hsize : M + k ≤ initial.card)
    (hdiv : A.DivisorBound initial lam)
    (hblock : ∀ x ∈ active, (A.block x).card ≤ h)
    (hrate : 2 * h * lam ^ (k + 1) ≤ (M - lam) * M ^ k) :
    2 * (A.survivors pair marked active available hne lam d).card ≤ active.card := by
  let s := (A.survivors pair marked active available hne lam d).card
  have hc := trace_card A active initial 1 tr
  have hm : M ≤ available.card := by omega
  have hm' : lam < available.card := by omega
  have hl := A.survivor_card_leak pair marked active available hne lam d hm'
  have hl' : (M - lam) * s ≤ lam * A.falseMass active d :=
    (Nat.mul_le_mul_right s (Nat.sub_le_sub_right hm lam)).trans hl
  have ht := trace_contraction A active initial 1 tr M lam hsize hdiv
  have hb := A.falseMass_le active 1 h hblock
  have ht' := ht.trans (Nat.mul_le_mul_left (lam ^ k) hb)
  have hden : 0 < (M - lam) * M ^ k :=
    Nat.mul_pos (Nat.sub_pos_of_lt hM) (pow_pos (by omega) _)
  apply Nat.le_of_mul_le_mul_left (c := (M - lam) * M ^ k) ?_ hden
  calc
    _ = 2 * M ^ k * ((M - lam) * s) := by ring
    _ ≤ 2 * M ^ k * (lam * A.falseMass active d) := Nat.mul_le_mul_left _ hl'
    _ = 2 * lam * (M ^ k * A.falseMass active d) := by ring
    _ ≤ 2 * lam * (lam ^ k * (h * active.card)) := Nat.mul_le_mul_left _ ht'
    _ = (2 * h * lam ^ (k + 1)) * active.card := by rw [pow_succ]; ring
    _ ≤ _ := Nat.mul_le_mul_right active.card hrate

/-- The implemented stage satisfies the old semantic invariant and halves
its actual active list; halving is derived, not a round assumption. -/
theorem stage_correct (O : CountOracle X) (A : Instance X V) (hO : O.Correct A)
    (pair : X → Pair) (initial active : Finset X) (marked : Finset Pair)
    (pool : Finset ℕ) (k M lam h : ℕ)
    (hinv : A.StateInvariant pair initial active marked)
    (hM : lam < M) (hsize : M + k ≤ pool.card) (hdiv : A.DivisorBound pool lam)
    (hblock : ∀ x ∈ initial, (A.block x).card ≤ h)
    (hrate : 2 * h * lam ^ (k + 1) ≤ (M - lam) * M ^ k) :
    let out := stage O A pair lam k pool active marked
    A.StateInvariant pair initial out.active out.marked ∧ 2 * out.active.card ≤ active.card := by
  let selected := greedy O active k 1 pool (fun x => (A.block x).card)
  have hk : k ≤ pool.card := by omega
  have hg := greedy_correct O A hO active k 1 pool (fun x => (A.block x).card) hk
    (fun x hx => (A.count_one x).symm)
  have hc := trace_card A active pool 1 hg.1
  have hne : selected.available.Nonempty := by
    apply Finset.card_pos.mp
    dsimp only [selected]
    omega
  have heq := stage_semantics O A hO pair lam k pool active marked hk hne
  dsimp only at heq ⊢
  rw [heq.1, heq.2]
  have hsmall := A.divisorBound_subset hdiv (trace_subset A active pool 1 hg.1)
  exact ⟨A.stage_invariant pair initial active marked selected.available hne lam selected.modulus
      hinv hsmall,
    trace_halves A pair marked active pool hg.1 hne M lam h hM hsize hdiv
      (fun x hx => hblock x (hinv.1 hx)) hrate⟩

theorem stage_subset (O : CountOracle X) (A : Instance X V) (pair : X → Pair)
    (lam k : ℕ) (pool : Finset ℕ) (active : Finset X) (marked : Finset Pair) :
    (stage O A pair lam k pool active marked).active ⊆ active := Finset.filter_subset _ _

theorem stage_calls_bound (O : CountOracle X) (A : Instance X V) (pair : X → Pair)
    (lam k : ℕ) (pool : Finset ℕ) (active : Finset X) (marked : Finset Pair) :
    (stage O A pair lam k pool active marked).calls.length ≤ (k + 1) * pool.card := by
  have hg := greedy_calls_bound O active k 1 pool (fun x => (A.block x).card)
  have hs := greedy_subset O active k 1 pool (fun x => (A.block x).card)
  have hc := Finset.card_le_card hs
  simp only [stage, List.length_append, List.length_map, Finset.length_sort]
  nlinarith

theorem stage_bookkeeping_bound (O : CountOracle X) (A : Instance X V) (pair : X → Pair)
    (lam k : ℕ) (pool : Finset ℕ) (active : Finset X) (marked : Finset Pair) :
    (stage O A pair lam k pool active marked).bookkeeping ≤
      16 * (k + 1) * (pool.card + 1) * (active.card + 1) := by
  have hg := greedy_bookkeeping_bound O active k 1 pool (fun x => (A.block x).card)
  have hs := greedy_subset O active k 1 pool (fun x => (A.block x).card)
  have hc := Finset.card_le_card hs
  have hcell := Nat.mul_le_mul_right active.card hc
  let B := 12 * pool.card * active.card + 12 * active.card + 4 * pool.card
  have hterm : 3 * pool.card * active.card + 4 * pool.card ≤ B := by
    dsimp [B]
    nlinarith [Nat.zero_le (pool.card * active.card)]
  have hfinal : 12 * (greedy O active k 1 pool (fun x => (A.block x).card)).available.card *
      active.card + 12 * active.card +
      4 * (greedy O active k 1 pool (fun x => (A.block x).card)).available.card ≤ B := by
    dsimp [B]
    nlinarith
  have hlarge : B ≤ 16 * (pool.card + 1) * (active.card + 1) := by
    dsimp [B]
    nlinarith [Nat.zero_le (pool.card * active.card)]
  calc
    _ ≤ k * B + B := by
      have ht := hg.trans (Nat.mul_le_mul_left k hterm)
      simp only [stage]
      omega
    _ = (k + 1) * B := by ring
    _ ≤ (k + 1) * (16 * (pool.card + 1) * (active.card + 1)) :=
      Nat.mul_le_mul_left _ hlarge
    _ = _ := by ring

/-- Stages really restart with the original prime pool and modulus one.
The returned value and resource trace are accumulated by the same recursion. -/
def restarts (O : CountOracle X) (A : Instance X V) (pair : X → Pair)
    (lam k : ℕ) (pool : Finset ℕ) : ℕ → Finset X → Finset Pair → StageResult X Pair
  | 0, active, marked => ⟨active, marked, [], 0⟩
  | n + 1, active, marked =>
      let one := stage O A pair lam k pool active marked
      let tail := restarts O A pair lam k pool n one.active one.marked
      { tail with
        calls := one.calls ++ tail.calls
        bookkeeping := one.bookkeeping + tail.bookkeeping }

theorem restarts_subset (O : CountOracle X) (A : Instance X V) (pair : X → Pair)
    (lam k : ℕ) (pool : Finset ℕ) (n : ℕ) (active : Finset X) (marked : Finset Pair) :
    (restarts O A pair lam k pool n active marked).active ⊆ active := by
  induction n generalizing active marked with
  | zero => exact Finset.Subset.refl _
  | succ n ih => exact (ih _ _).trans (stage_subset O A pair lam k pool active marked)

theorem restarts_correct (O : CountOracle X) (A : Instance X V) (hO : O.Correct A)
    (pair : X → Pair) (initial active : Finset X) (marked : Finset Pair)
    (pool : Finset ℕ) (k M lam h n : ℕ)
    (hinv : A.StateInvariant pair initial active marked)
    (hM : lam < M) (hsize : M + k ≤ pool.card) (hdiv : A.DivisorBound pool lam)
    (hblock : ∀ x ∈ initial, (A.block x).card ≤ h)
    (hrate : 2 * h * lam ^ (k + 1) ≤ (M - lam) * M ^ k) :
    let out := restarts O A pair lam k pool n active marked
    A.StateInvariant pair initial out.active out.marked ∧
      2 ^ n * out.active.card ≤ active.card := by
  induction n generalizing active marked with
  | zero => exact ⟨hinv, by simp [restarts]⟩
  | succ n ih =>
      have hs := stage_correct O A hO pair initial active marked pool k M lam h
        hinv hM hsize hdiv hblock hrate
      let one := stage O A pair lam k pool active marked
      have ht := ih one.active one.marked hs.1
      refine ⟨ht.1, ?_⟩
      change 2 ^ (n + 1) * (restarts O A pair lam k pool n one.active one.marked).active.card ≤ _
      calc
        _ = 2 * (2 ^ n * (restarts O A pair lam k pool n one.active one.marked).active.card) := by
          rw [pow_succ]; ring
        _ ≤ 2 * one.active.card := Nat.mul_le_mul_left _ ht.2
        _ ≤ _ := hs.2

theorem restarts_calls_bound (O : CountOracle X) (A : Instance X V) (pair : X → Pair)
    (lam k : ℕ) (pool : Finset ℕ) (n : ℕ) (active : Finset X) (marked : Finset Pair) :
    (restarts O A pair lam k pool n active marked).calls.length ≤ n * (k + 1) * pool.card := by
  induction n generalizing active marked with
  | zero => simp [restarts]
  | succ n ih =>
      let one := stage O A pair lam k pool active marked
      have hs := stage_calls_bound O A pair lam k pool active marked
      have ht := ih one.active one.marked
      change (one.calls ++ (restarts O A pair lam k pool n one.active one.marked).calls).length ≤ _
      rw [List.length_append]
      nlinarith

theorem restarts_bookkeeping_bound (O : CountOracle X) (A : Instance X V) (pair : X → Pair)
    (lam k : ℕ) (pool : Finset ℕ) (n : ℕ) (active : Finset X) (marked : Finset Pair) :
    (restarts O A pair lam k pool n active marked).bookkeeping ≤
      16 * n * (k + 1) * (pool.card + 1) * (active.card + 1) := by
  induction n generalizing active marked with
  | zero => simp [restarts]
  | succ n ih =>
      let one := stage O A pair lam k pool active marked
      have hs := stage_bookkeeping_bound O A pair lam k pool active marked
      have ht := ih one.active one.marked
      have hc := Finset.card_le_card (stage_subset O A pair lam k pool active marked)
      have ht' := ht.trans (Nat.mul_le_mul_left (16 * n * (k + 1) * (pool.card + 1))
        (Nat.add_le_add_right hc 1))
      change one.bookkeeping + (restarts O A pair lam k pool n one.active one.marked).bookkeeping ≤ _
      calc
        _ ≤ 16 * (k + 1) * (pool.card + 1) * (active.card + 1) +
            16 * n * (k + 1) * (pool.card + 1) * (active.card + 1) := Nat.add_le_add hs ht'
        _ = _ := by ring

theorem greedy_call_active (O : CountOracle X) (active : Finset X) (n d : ℕ)
    (pool : Finset ℕ) (base : X → ℕ) :
    ∀ c ∈ (greedy O active n d pool base).calls, c.active = active := by
  induction n generalizing d pool base with
  | zero => simp [greedy]
  | succ n ih =>
      intro c hc
      simp only [greedy, List.mem_append, List.mem_map, Finset.mem_sort] at hc
      obtain ⟨p, hp, rfl⟩ | hc := hc
      · rfl
      · exact ih _ _ _ c hc

theorem stage_call_active (O : CountOracle X) (A : Instance X V) (pair : X → Pair)
    (lam k : ℕ) (pool : Finset ℕ) (active : Finset X) (marked : Finset Pair) :
    ∀ c ∈ (stage O A pair lam k pool active marked).calls, c.active = active := by
  intro c hc
  simp only [stage, List.mem_append, List.mem_map, Finset.mem_sort] at hc
  obtain hc | ⟨p, hp, rfl⟩ := hc
  · exact greedy_call_active O active k 1 pool (fun x => (A.block x).card) c hc
  · rfl

theorem restarts_call_subset (O : CountOracle X) (A : Instance X V) (pair : X → Pair)
    (lam k : ℕ) (pool : Finset ℕ) (n : ℕ) (active : Finset X) (marked : Finset Pair) :
    ∀ c ∈ (restarts O A pair lam k pool n active marked).calls, c.active ⊆ active := by
  induction n generalizing active marked with
  | zero => simp [restarts]
  | succ n ih =>
      intro c hc
      simp only [restarts, List.mem_append] at hc
      obtain hc | hc := hc
      · rw [stage_call_active O A pair lam k pool active marked c hc]
      · exact (ih _ _ c hc).trans (stage_subset O A pair lam k pool active marked)

/-- Exact number of returned table cells across the recorded oracle calls. -/
def tableCells (calls : List (Call X)) : ℕ := (calls.map (fun c => c.active.card)).sum

theorem tableCells_le (calls : List (Call X)) (bound : ℕ)
    (h : ∀ c ∈ calls, c.active.card ≤ bound) : tableCells calls ≤ calls.length * bound := by
  induction calls with
  | nil => simp [tableCells]
  | cons c calls ih =>
      have hh := h c (by simp)
      have ht := ih (fun c hc => h c (by simp [hc]))
      dsimp only [tableCells] at ht
      simp only [tableCells, List.map_cons, List.sum_cons, List.length_cons]
      nlinarith

theorem restarts_tableCells_bound (O : CountOracle X) (A : Instance X V) (pair : X → Pair)
    (lam k : ℕ) (pool : Finset ℕ) (n : ℕ) (active : Finset X) (marked : Finset Pair) :
    tableCells (restarts O A pair lam k pool n active marked).calls ≤
      n * (k + 1) * pool.card * active.card := by
  have ht := tableCells_le (restarts O A pair lam k pool n active marked).calls active.card
    (fun c hc => Finset.card_le_card (restarts_call_subset O A pair lam k pool n active marked c hc))
  exact ht.trans (Nat.mul_le_mul_right _ (restarts_calls_bound O A pair lam k pool n active marked))

def finalScan (A : Instance X V) (pair : X → Pair) (active : Finset X)
    (marked : Finset Pair) : Finset Pair :=
  marked ∪ (active.filter (fun x =>
    0 < ((A.block x).filter (fun v => A.value x v = 0)).card)).image pair

theorem finalScan_eq (A : Instance X V) (pair : X → Pair) (active : Finset X)
    (marked : Finset Pair) : finalScan A pair active marked = marked ∪ A.exactPairs pair active := by
  have hzero : ∀ x, ((A.block x).filter (fun v => A.value x v = 0)).card = A.trueCount x := by
    intro x
    simp [Instance.trueCount]
  simp only [finalScan, hzero, Instance.exactPairs]

structure Result (X Pair : Type*) where
  answers : Finset Pair
  active : Finset X
  calls : List (Call X)
  bookkeeping : ℕ
  originalSumTests : ℕ

/-- The final scan examines only original integer sums. It adds no modular
oracle calls; its original-sum tests are recorded separately. -/
def solve (O : CountOracle X) (A : Instance X V) (pair : X → Pair)
    (lam k stages : ℕ) (pool : Finset ℕ) (initial : Finset X) : Result X Pair :=
  let out := restarts O A pair lam k pool stages initial ∅
  { answers := finalScan A pair out.active out.marked
    active := out.active
    calls := out.calls
    bookkeeping := out.bookkeeping
    originalSumTests := A.scanWork out.active }

/-- Correctness and the call/cell/bookkeeping/scan bounds concern one and
the same returned program value and its recorded resource trace. -/
theorem solve_correct_and_resources (O : CountOracle X) (A : Instance X V)
    (hO : O.Correct A) (pair : X → Pair) (initial : Finset X)
    (pool : Finset ℕ) (k M lam h stages budget : ℕ)
    (hM : lam < M) (hsize : M + k ≤ pool.card) (hdiv : A.DivisorBound pool lam)
    (hblock : ∀ x ∈ initial, (A.block x).card ≤ h)
    (hrate : 2 * h * lam ^ (k + 1) ≤ (M - lam) * M ^ k)
    (hbudget : h * initial.card ≤ 2 ^ stages * budget) :
    let out := solve O A pair lam k stages pool initial
    (∀ q, q ∈ out.answers ↔
      ∃ x ∈ initial, pair x = q ∧ ∃ v ∈ A.block x, A.value x v = 0) ∧
    out.calls.length ≤ stages * (k + 1) * pool.card ∧
    tableCells out.calls ≤ stages * (k + 1) * pool.card * initial.card ∧
    out.bookkeeping ≤ 16 * stages * (k + 1) * (pool.card + 1) * (initial.card + 1) ∧
    out.originalSumTests ≤ budget := by
  have hs := restarts_correct O A hO pair initial initial ∅ pool k M lam h stages
    (A.initial_invariant pair initial) hM hsize hdiv hblock hrate
  let state := restarts O A pair lam k pool stages initial ∅
  have heq := A.final_exact_scan pair initial state.active state.marked hs.1
  refine ⟨?_, restarts_calls_bound O A pair lam k pool stages initial ∅,
    restarts_tableCells_bound O A pair lam k pool stages initial ∅,
    restarts_bookkeeping_bound O A pair lam k pool stages initial ∅, ?_⟩
  · intro q
    change q ∈ finalScan A pair state.active state.marked ↔ _
    rw [finalScan_eq, heq]
    exact A.mem_exactPairs_iff pair initial q
  · exact A.final_scan_budget initial state.active h stages budget hs.1.1 hblock hs.2 hbudget

theorem trace_modulus_le (A : Instance X V) (active : Finset X) (initial : Finset ℕ)
    {n d : ℕ} {pool : Finset ℕ} (tr : OracleTrace A active initial 1 n d pool)
    (upper : ℕ) (hu : ∀ p ∈ initial, p ≤ upper) : d ≤ upper ^ n := by
  induction tr with
  | start => simp
  | step previous hp hmin ih =>
      have hpu := hu _ (trace_subset A active initial 1 previous hp)
      simpa [pow_succ] using Nat.mul_le_mul ih hpu

theorem trace_coprime_remaining (A : Instance X V) (active : Finset X) (initial : Finset ℕ)
    {n d : ℕ} {pool : Finset ℕ} (tr : OracleTrace A active initial 1 n d pool)
    (hprime : ∀ p ∈ initial, Nat.Prime p) : ∀ p ∈ pool, Nat.Coprime d p := by
  induction tr with
  | start => intro p hp; simp
  | step previous hp hmin ih =>
      intro p hp'
      obtain ⟨hnep, hp'⟩ := Finset.mem_erase.mp hp'
      have hsel := hprime _ (trace_subset A active initial 1 previous hp)
      have hrem := hprime _ (trace_subset A active initial 1 previous hp')
      exact Nat.coprime_mul_iff_left.mpr ⟨ih p hp', (Nat.coprime_primes hsel hrem).mpr hnep.symm⟩

/-- Every recorded greedy call has a bounded actual modulus. The one spare
factor accommodates the final, unselected certification prime. -/
theorem greedy_call_modulus_bound (O : CountOracle X) (active : Finset X) (n d : ℕ)
    (pool : Finset ℕ) (base : X → ℕ) (upper : ℕ) (hu1 : 1 ≤ upper)
    (hu : ∀ p ∈ pool, p ≤ upper) :
    ∀ c ∈ (greedy O active n d pool base).calls, c.modulus ≤ d * upper ^ (n + 1) := by
  induction n generalizing d pool base with
  | zero => simp [greedy]
  | succ n ih =>
      intro c hc
      simp only [greedy, List.mem_append, List.mem_map, Finset.mem_sort] at hc
      let row := pick (evaluate O active d pool) (tableTotal active)
      have hpick : row.1 ≤ upper := by
        by_cases hne : pool.Nonempty
        · have hs := pick_spec (evaluate O active d pool) (tableTotal active)
            (evaluate_nonempty O active d pool hne)
          obtain ⟨p, hp, heq⟩ := (mem_evaluate O active d pool _).mp hs.1
          change (pick (evaluate O active d pool) (tableTotal active)).1 ≤ _
          rw [heq]
          exact hu p hp
        · have he : pool = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
          simp [row, pick, evaluate, he]
      obtain ⟨p, hp, rfl⟩ | hc := hc
      · have hpow : upper ≤ upper ^ (n + 1 + 1) := by
          simpa using Nat.pow_le_pow_right hu1 (show 1 ≤ n + 1 + 1 by omega)
        exact Nat.mul_le_mul_left d ((hu p hp).trans hpow)
      · have ht := ih (d * row.1) (pool.erase row.1) row.2
          (fun p hp => hu p (Finset.mem_of_mem_erase hp)) c hc
        calc
          _ ≤ (d * row.1) * upper ^ (n + 1) := ht
          _ ≤ (d * upper) * upper ^ (n + 1) :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hpick)
          _ = _ := by rw [pow_succ]; ring

theorem stage_call_modulus_bound (O : CountOracle X) (A : Instance X V) (hO : O.Correct A)
    (pair : X → Pair) (lam k : ℕ) (pool : Finset ℕ) (active : Finset X)
    (marked : Finset Pair) (hk : k ≤ pool.card) (upper : ℕ) (hu1 : 1 ≤ upper)
    (hu : ∀ p ∈ pool, p ≤ upper) :
    ∀ c ∈ (stage O A pair lam k pool active marked).calls, c.modulus ≤ upper ^ (k + 1) := by
  intro c hc
  let selected := greedy O active k 1 pool (fun x => (A.block x).card)
  have ht := greedy_correct O A hO active k 1 pool (fun x => (A.block x).card) hk
    (fun x hx => (A.count_one x).symm)
  have hd := trace_modulus_le A active pool ht.1 upper hu
  have hs := trace_subset A active pool 1 ht.1
  simp only [stage, List.mem_append, List.mem_map, Finset.mem_sort] at hc
  obtain hc | ⟨p, hp, rfl⟩ := hc
  · simpa using greedy_call_modulus_bound O active k 1 pool (fun x => (A.block x).card)
      upper hu1 hu c hc
  · have hp' := hu p (hs hp)
    simpa [pow_succ] using Nat.mul_le_mul hd hp'

theorem restarts_call_modulus_bound (O : CountOracle X) (A : Instance X V) (hO : O.Correct A)
    (pair : X → Pair) (lam k : ℕ) (pool : Finset ℕ) (stages : ℕ) (active : Finset X)
    (marked : Finset Pair) (hk : k ≤ pool.card) (upper : ℕ) (hu1 : 1 ≤ upper)
    (hu : ∀ p ∈ pool, p ≤ upper) :
    ∀ c ∈ (restarts O A pair lam k pool stages active marked).calls,
      c.modulus ≤ upper ^ (k + 1) := by
  induction stages generalizing active marked with
  | zero => simp [restarts]
  | succ stages ih =>
      intro c hc
      simp only [restarts, List.mem_append] at hc
      obtain hc | hc := hc
      · exact stage_call_modulus_bound O A hO pair lam k pool active marked hk upper hu1 hu c hc
      · exact ih _ _ c hc

/-- A client may assign its proved encoding/count/extraction cost to each
recorded call. The bound is tied to this program trace, not a separate
existence theorem about some successful sequence of moduli. -/
def oracleWork (cost : Call X → ℕ) (calls : List (Call X)) : ℕ := (calls.map cost).sum

theorem oracleWork_le (cost : Call X → ℕ) (calls : List (Call X)) (Gamma : ℕ)
    (hcost : ∀ c ∈ calls, cost c ≤ Gamma) : oracleWork cost calls ≤ calls.length * Gamma := by
  induction calls with
  | nil => simp [oracleWork]
  | cons c calls ih =>
      have hh := hcost c (by simp)
      have ht := ih (fun c hc => hcost c (by simp [hc]))
      dsimp only [oracleWork] at ht
      simp only [oracleWork, List.map_cons, List.sum_cons, List.length_cons]
      nlinarith

theorem solve_oracleWork_bound (O : CountOracle X) (A : Instance X V) (pair : X → Pair)
    (lam k stages : ℕ) (pool : Finset ℕ) (initial : Finset X)
    (cost : Call X → ℕ) (Gamma : ℕ)
    (hcost : ∀ c ∈ (solve O A pair lam k stages pool initial).calls, cost c ≤ Gamma) :
    oracleWork cost (solve O A pair lam k stages pool initial).calls ≤
      stages * (k + 1) * pool.card * Gamma := by
  have hb := oracleWork_le cost _ Gamma hcost
  exact hb.trans (Nat.mul_le_mul_right Gamma
    (restarts_calls_bound O A pair lam k pool stages initial ∅))

/-- A small definitional execution audit with different false witnesses at
different primes, a genuine incidence, and a negative original sum. -/
private def auditInstance : Instance (Fin 3) (Fin 2) where
  block := fun _ => Finset.univ
  value := fun x v => if x = 0 then (if v = 0 then 0 else 101 * 103)
    else if x = 1 then (if v = 0 then 101 else 103)
    else if v = 0 then -107 else 109

private def auditOracle : CountOracle (Fin 3) where
  table := fun d _ x => auditInstance.modCount d x

private def auditPool : Finset ℕ := {101, 103, 107, 109, 113}

#eval (solve auditOracle auditInstance id 1 1 1 auditPool Finset.univ).answers
#eval (solve auditOracle auditInstance id 1 1 1 auditPool Finset.univ).calls.length

end ThinMatrix.CompositeAlgorithm

#print axioms ThinMatrix.CompositeAlgorithm.greedy_correct
#print axioms ThinMatrix.CompositeAlgorithm.stage_correct
#print axioms ThinMatrix.CompositeAlgorithm.solve_correct_and_resources
#print axioms ThinMatrix.CompositeAlgorithm.restarts_call_modulus_bound
#print axioms ThinMatrix.CompositeAlgorithm.solve_oracleWork_bound
