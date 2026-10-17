import CompositeAlgorithm
import PhaseGeometry

/-!
# Factor histories of the actual composite oracle program

The additional trace records the already selected factors and the candidate
being tested. It follows the same sorted candidate tables and cached argmin
as `CompositeAlgorithm`; erasing the annotation recovers its returned
program value and complete ordered call list. No new oracle call is added.
-/
namespace ThinMatrix.CompositePhaseTrace

open CompositeAlgorithm CompositeCertification
open Finset

variable {X V Pair : Type*} [DecidableEq Pair]

/-- One recorded invocation, before the fixed signed-window factor three. -/
structure FactorCall (X : Type*) where
  selected : List ℕ
  candidate : ℕ
  active : Finset X

def FactorCall.factors (c : FactorCall X) : List ℕ := c.selected ++ [c.candidate]

def FactorCall.erase (c : FactorCall X) : Call X :=
  ⟨c.selected.prod * c.candidate, c.active⟩

theorem FactorCall.erase_modulus (c : FactorCall X) :
    c.erase.modulus = c.factors.prod := by simp [erase, factors]

structure FactorGreedyResult (X : Type*) where
  selected : List ℕ
  available : Finset ℕ
  base : X → ℕ
  calls : List (FactorCall X)
  bookkeeping : ℕ

def FactorGreedyResult.erase (out : FactorGreedyResult X) : GreedyResult X :=
  ⟨out.selected.prod, out.available, out.base, out.calls.map FactorCall.erase,
    out.bookkeeping⟩

/-- The row and its cached table are selected exactly once, as in `greedy`. -/
def factorGreedy (O : CountOracle X) (active : Finset X) :
    ℕ → List ℕ → Finset ℕ → (X → ℕ) → FactorGreedyResult X
  | 0, selected, pool, base => ⟨selected, pool, base, [], 0⟩
  | n+1, selected, pool, _base =>
      let rows := evaluate O active selected.prod pool
      let row := pick rows (tableTotal active)
      let tail := factorGreedy O active n (selected ++ [row.1]) (pool.erase row.1) row.2
      { tail with
        calls := (pool.sort (· ≤ ·)).map (fun p => ⟨selected, p, active⟩) ++ tail.calls
        bookkeeping := 3*pool.card*active.card + 4*pool.card + tail.bookkeeping }

/-- The annotation preserves every returned table, call order, and counter. -/
theorem factorGreedy_erases (O : CountOracle X) (active : Finset X) (n : ℕ)
    (selected : List ℕ) (pool : Finset ℕ) (base : X → ℕ) :
    (factorGreedy O active n selected pool base).erase =
      greedy O active n selected.prod pool base := by
  induction n generalizing selected pool base with
  | zero => rfl
  | succ n ih =>
      simp only [factorGreedy, greedy, FactorGreedyResult.erase, List.map_append,
        List.map_map]
      have ht := ih (selected ++ [(pick (evaluate O active selected.prod pool)
        (tableTotal active)).1])
        (pool.erase (pick (evaluate O active selected.prod pool) (tableTotal active)).1)
        (pick (evaluate O active selected.prod pool) (tableTotal active)).2
      cases he : factorGreedy O active n
        (selected ++ [(pick (evaluate O active selected.prod pool) (tableTotal active)).1])
        (pool.erase (pick (evaluate O active selected.prod pool) (tableTotal active)).1)
        (pick (evaluate O active selected.prod pool) (tableTotal active)).2
      simp only [he, FactorGreedyResult.erase, List.prod_append, List.prod_singleton] at ht
      rw [← ht]
      rfl

theorem factorGreedy_calls_valid (O : CountOracle X) (active : Finset X)
    (n : ℕ) (selected : List ℕ) (pool initial : Finset ℕ) (base : X → ℕ)
    (hnodup : selected.Nodup) (hsel : ∀ p ∈ selected, p ∈ initial)
    (hpool : pool ⊆ initial) (hdis : ∀ p ∈ pool, p ∉ selected)
    (hn : n ≤ pool.card) :
    ∀ c ∈ (factorGreedy O active n selected pool base).calls,
      c.factors.Nodup ∧ (∀ p ∈ c.factors, p ∈ initial) ∧
        selected.length ≤ c.selected.length ∧ c.selected.length < selected.length+n := by
  induction n generalizing selected pool base with
  | zero => simp [factorGreedy]
  | succ n ih =>
      have hne : pool.Nonempty := Finset.card_pos.mp (by omega)
      let row := pick (evaluate O active selected.prod pool) (tableTotal active)
      have hm := (pick_spec (evaluate O active selected.prod pool) (tableTotal active)
        (evaluate_nonempty O active selected.prod pool hne)).1
      obtain ⟨p, hp, heq⟩ := (mem_evaluate O active selected.prod pool _).mp hm
      have hrow : row.1 ∈ pool := by change (pick _ _).1 ∈ pool; rw [heq]; exact hp
      have hrownot := hdis row.1 hrow
      have hnewnodup : (selected ++ [row.1]).Nodup := by
        simpa only [List.concat_eq_append] using List.Nodup.concat hrownot hnodup
      have hnewmem : ∀ p ∈ selected ++ [row.1], p ∈ initial := by
        intro p hp
        rcases List.mem_append.mp hp with hp | hp
        · exact hsel p hp
        · have hp' := List.mem_singleton.mp hp
          simpa [hp'] using hpool hrow
      have hnewpool : pool.erase row.1 ⊆ initial :=
        (Finset.erase_subset _ _).trans hpool
      have hnewdis : ∀ p ∈ pool.erase row.1, p ∉ selected ++ [row.1] := by
        intro p hp
        have hp' := Finset.mem_erase.mp hp
        simpa only [List.mem_append, List.mem_singleton, not_or] using
          ⟨hdis p hp'.2, hp'.1⟩
      have hcard := Finset.card_erase_add_one hrow
      have ht := ih (selected ++ [row.1]) (pool.erase row.1) row.2
        hnewnodup hnewmem hnewpool hnewdis (by omega)
      intro c hc
      simp only [factorGreedy, List.mem_append, List.mem_map, Finset.mem_sort] at hc
      obtain ⟨p, hp, rfl⟩ | hc := hc
      · refine ⟨?_, ?_, le_rfl, ?_⟩
        · change (selected ++ [p]).Nodup
          simpa only [List.concat_eq_append] using List.Nodup.concat (hdis p hp) hnodup
        · intro q hq
          rcases List.mem_append.mp hq with hq | hq
          · exact hsel q hq
          · have hq' := List.mem_singleton.mp hq
            simpa [hq'] using hpool hp
        · change selected.length < selected.length + (n+1)
          omega
      · obtain ⟨hnd, hmem, hlo, hhi⟩ := ht c hc
        refine ⟨hnd, hmem, ?_, ?_⟩
        · simp only [List.length_append, List.length_singleton] at hlo
          omega
        · simp only [List.length_append, List.length_singleton] at hhi
          omega


/-- The minimum selector selects a member of every nonempty pool, without
requiring oracle correctness. -/
theorem factor_selected_prime_mem (O : CountOracle X) (active : Finset X) (d : ℕ)
    (pool : Finset ℕ) (hne : pool.Nonempty) :
    (pick (evaluate O active d pool) (tableTotal active)).1 ∈ pool := by
  have hs := pick_spec (evaluate O active d pool) (tableTotal active)
    (evaluate_nonempty O active d pool hne)
  obtain ⟨p, hp, heq⟩ := (mem_evaluate O active d pool _).mp hs.1
  simpa only [heq] using hp

/-- Every recursive step appends exactly one selected factor, regardless of
pool size or oracle behavior. -/
theorem factorGreedy_selected_length (O : CountOracle X) (active : Finset X)
    (n : ℕ) (selected : List ℕ) (pool : Finset ℕ) (base : X → ℕ) :
    (factorGreedy O active n selected pool base).selected.length = selected.length + n := by
  induction n generalizing selected pool base with
  | zero => simp only [factorGreedy, Nat.add_zero]
  | succ n ih =>
      simp only [factorGreedy, ih, List.length_append, List.length_singleton]
      omega

/-- All final-state factor invariants hold for the actual annotated greedy
program. Distinctness comes from erasure, rather than any oracle property. -/
theorem factorGreedy_final_invariants (O : CountOracle X) (active : Finset X)
    (n : ℕ) (selected : List ℕ) (pool initial : Finset ℕ) (base : X → ℕ)
    (hselected : selected.Nodup)
    (hselected_mem : ∀ p ∈ selected, p ∈ initial)
    (hpool : pool ⊆ initial)
    (hdisjoint : ∀ p ∈ pool, p ∉ selected)
    (hn : n ≤ pool.card) :
    let out := factorGreedy O active n selected pool base
    out.selected.Nodup ∧ out.selected.length = selected.length + n ∧
      (∀ p ∈ out.selected, p ∈ initial) ∧
      (∀ p ∈ out.available, p ∉ out.selected) := by
  induction n generalizing selected pool base with
  | zero => exact ⟨hselected, by simp only [factorGreedy, Nat.add_zero],
      hselected_mem, hdisjoint⟩
  | succ n ih =>
      let row := pick (evaluate O active selected.prod pool) (tableTotal active)
      have hrow : row.1 ∈ pool :=
        factor_selected_prime_mem O active selected.prod pool
          (Finset.card_pos.mp (by omega))
      have hrow_not : row.1 ∉ selected := hdisjoint row.1 hrow
      have hc := Finset.card_erase_add_one hrow
      have hn' : n ≤ (pool.erase row.1).card := by omega
      have hselected' : (selected ++ [row.1]).Nodup := by
        simpa only [List.concat_eq_append] using List.Nodup.concat hrow_not hselected
      have hselected_mem' : ∀ p ∈ selected ++ [row.1], p ∈ initial := by
        intro p hp
        rcases List.mem_append.mp hp with hp | hp
        · exact hselected_mem p hp
        · have heq := List.mem_singleton.mp hp
          simpa only [heq] using hpool hrow
      have hpool' : pool.erase row.1 ⊆ initial :=
        (Finset.erase_subset _ _).trans hpool
      have hdisjoint' : ∀ p ∈ pool.erase row.1, p ∉ selected ++ [row.1] := by
        intro p hp hmem
        have he := Finset.mem_erase.mp hp
        rcases List.mem_append.mp hmem with hs | hs
        · exact hdisjoint p he.2 hs
        · exact he.1 (List.mem_singleton.mp hs)
      have ht := ih (selected ++ [row.1]) (pool.erase row.1) row.2
        hselected' hselected_mem' hpool' hdisjoint' hn'
      simpa only [factorGreedy, row, List.length_append, List.length_singleton,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ht


structure FactorStageResult (X Pair : Type*) where
  active : Finset X
  marked : Finset Pair
  calls : List (FactorCall X)
  bookkeeping : ℕ

def FactorStageResult.erase (out : FactorStageResult X Pair) : StageResult X Pair :=
  ⟨out.active, out.marked, out.calls.map FactorCall.erase, out.bookkeeping⟩

/-- Final certification tests each unused prime against the selected prefix. -/
def factorStage (O : CountOracle X) (A : Instance X V) (pair : X → Pair)
    (lam k : ℕ) (pool : Finset ℕ) (active : Finset X) (marked : Finset Pair) :
    FactorStageResult X Pair :=
  let selected := factorGreedy O active k [] pool (fun x => (A.block x).card)
  let rows := evaluate O active selected.selected.prod selected.available
  let mu := batchMinimum rows
  let yes := active.filter (fun x => lam * selected.base x < selected.available.card * mu x)
  let marked' := marked ∪ yes.image pair
  let active' := active.filter (fun x => mu x ≠ 0 ∧
    selected.available.card * mu x ≤ lam * selected.base x ∧ pair x ∉ marked')
  { active := active'
    marked := marked'
    calls := selected.calls ++ (selected.available.sort (· ≤ ·)).map
      (fun p => ⟨selected.selected, p, active⟩)
    bookkeeping := selected.bookkeeping + 12*selected.available.card*active.card +
      12*active.card + 4*selected.available.card }

theorem factorStage_erases (O : CountOracle X) (A : Instance X V) (pair : X → Pair)
    (lam k : ℕ) (pool : Finset ℕ) (active : Finset X) (marked : Finset Pair) :
    (factorStage O A pair lam k pool active marked).erase =
      stage O A pair lam k pool active marked := by
  have hg : (factorGreedy O active k [] pool (fun x => (A.block x).card)).erase =
      greedy O active k 1 pool (fun x => (A.block x).card) :=
    factorGreedy_erases O active k [] pool (fun x => (A.block x).card)
  unfold factorStage stage
  rw [← hg]
  simp only [FactorStageResult.erase, FactorGreedyResult.erase, List.map_append, List.map_map]
  rfl

/-- One log entry for each restart, including its exact active input. -/
structure RestartLog (X Pair : Type*) where
  input : Finset X
  marked : Finset Pair
  output : FactorStageResult X Pair

structure FactorRestartResult (X Pair : Type*) where
  state : FactorStageResult X Pair
  logs : List (RestartLog X Pair)

/-- Restarts retain their original pool and reset the selected list to empty. -/
def factorRestarts (O : CountOracle X) (A : Instance X V) (pair : X → Pair)
    (lam k : ℕ) (pool : Finset ℕ) :
    ℕ → Finset X → Finset Pair → FactorRestartResult X Pair
  | 0, active, marked => ⟨⟨active, marked, [], 0⟩, []⟩
  | n+1, active, marked =>
      let one := factorStage O A pair lam k pool active marked
      let tail := factorRestarts O A pair lam k pool n one.active one.marked
      { state := { tail.state with
          calls := one.calls ++ tail.state.calls
          bookkeeping := one.bookkeeping + tail.state.bookkeeping }
        logs := ⟨active, marked, one⟩ :: tail.logs }

theorem factorRestarts_erases (O : CountOracle X) (A : Instance X V) (pair : X → Pair)
    (lam k : ℕ) (pool : Finset ℕ) (n : ℕ) (active : Finset X) (marked : Finset Pair) :
    (factorRestarts O A pair lam k pool n active marked).state.erase =
      restarts O A pair lam k pool n active marked := by
  induction n generalizing active marked with
  | zero => rfl
  | succ n ih =>
      have hs := factorStage_erases O A pair lam k pool active marked
      have ht := ih (factorStage O A pair lam k pool active marked).active
        (factorStage O A pair lam k pool active marked).marked
      unfold factorRestarts restarts
      rw [← hs]
      dsimp only [FactorStageResult.erase]
      rw [← ht]
      simp only [FactorStageResult.erase, List.map_append]

theorem factorRestarts_logs_length (O : CountOracle X) (A : Instance X V)
    (pair : X → Pair) (lam k : ℕ) (pool : Finset ℕ) (n : ℕ)
    (active : Finset X) (marked : Finset Pair) :
    (factorRestarts O A pair lam k pool n active marked).logs.length = n := by
  induction n generalizing active marked with
  | zero => rfl
  | succ n ih => simp only [factorRestarts, List.length_cons, ih]

/-- The entire stage includes k greedy rounds and one final candidate batch. -/
theorem factorStage_calls_valid (O : CountOracle X) (A : Instance X V)
    (pair : X → Pair) (lam k : ℕ) (pool : Finset ℕ) (active : Finset X)
    (marked : Finset Pair) (hk : k ≤ pool.card) :
    ∀ c ∈ (factorStage O A pair lam k pool active marked).calls,
      c.factors.Nodup ∧ (∀ p ∈ c.factors, p ∈ pool) ∧ c.selected.length < k+1 := by
  let out := factorGreedy O active k [] pool (fun x => (A.block x).card)
  have hg := factorGreedy_calls_valid O active k [] pool pool
    (fun x => (A.block x).card) (by simp) (by simp) (Finset.Subset.refl _)
    (by simp) hk
  have hf := factorGreedy_final_invariants O active k [] pool pool
    (fun x => (A.block x).card) (by simp) (by simp) (Finset.Subset.refl _)
    (by simp) hk
  have he := factorGreedy_erases O active k [] pool (fun x => (A.block x).card)
  simp only [List.prod_nil] at he
  have hp : out.available ⊆ pool := by
    have h := greedy_subset O active k 1 pool (fun x => (A.block x).card)
    rw [← he] at h
    exact h
  intro c hc
  simp only [factorStage, List.mem_append, List.mem_map, Finset.mem_sort] at hc
  obtain hc | ⟨p, hp', rfl⟩ := hc
  · obtain ⟨hnd, hmem, _, hlen⟩ := hg c hc
    simp only [List.length_nil, Nat.zero_add] at hlen
    exact ⟨hnd, hmem, by omega⟩
  · refine ⟨?_, ?_, ?_⟩
    · change (out.selected ++ [p]).Nodup
      simpa only [List.concat_eq_append] using List.Nodup.concat (hf.2.2.2 p hp') hf.1
    · intro q hq
      rcases List.mem_append.mp hq with hq | hq
      · exact hf.2.2.1 q hq
      · have hqp := List.mem_singleton.mp hq
        simpa only [hqp] using hp hp'
    · change out.selected.length < k+1
      have hl : out.selected.length = k := by simpa using hf.2.1
      omega

/-- Every restart has its own actual factor history, from the empty prefix. -/
theorem factorRestarts_calls_valid (O : CountOracle X) (A : Instance X V)
    (pair : X → Pair) (lam k : ℕ) (pool : Finset ℕ) (n : ℕ)
    (active : Finset X) (marked : Finset Pair) (hk : k ≤ pool.card) :
    ∀ c ∈ (factorRestarts O A pair lam k pool n active marked).state.calls,
      c.factors.Nodup ∧ (∀ p ∈ c.factors, p ∈ pool) ∧ c.selected.length < k+1 := by
  induction n generalizing active marked with
  | zero => simp [factorRestarts]
  | succ n ih =>
      intro c hc
      simp only [factorRestarts, List.mem_append] at hc
      rcases hc with hc | hc
      · exact factorStage_calls_valid O A pair lam k pool active marked hk c hc
      · exact ih _ _ c hc

/-- The call list is partitioned in order into the recorded restart batches. -/
theorem factorRestarts_calls_eq_logs (O : CountOracle X) (A : Instance X V)
    (pair : X → Pair) (lam k : ℕ) (pool : Finset ℕ) (n : ℕ)
    (active : Finset X) (marked : Finset Pair) :
    (factorRestarts O A pair lam k pool n active marked).state.calls =
      (factorRestarts O A pair lam k pool n active marked).logs.flatMap
        (fun log => log.output.calls) := by
  induction n generalizing active marked with
  | zero => rfl
  | succ n ih => simp only [factorRestarts, List.flatMap_cons, ih]

theorem factorRestarts_logs_actual (O : CountOracle X) (A : Instance X V)
    (pair : X → Pair) (lam k : ℕ) (pool : Finset ℕ) (n : ℕ)
    (active : Finset X) (marked : Finset Pair) :
    ∀ log ∈ (factorRestarts O A pair lam k pool n active marked).logs,
      log.output = factorStage O A pair lam k pool log.input log.marked := by
  induction n generalizing active marked with
  | zero => simp [factorRestarts]
  | succ n ih =>
      intro log hlog
      simp only [factorRestarts, List.mem_cons] at hlog
      rcases hlog with rfl | hlog
      · rfl
      · exact ih _ _ log hlog

/-- An actual recorded call supplies a phase value directly, without choosing
an unrelated factorization or assuming a modulus shape. -/
def FactorCall.toPhaseCall (c : FactorCall X) (R P : ℕ)
    (hlen : c.selected.length < R)
    (hpool : ∀ p ∈ c.factors, p ∈ PrimePool.candidates P) : PhaseGeometry.PhaseCall R P where
  factors := c.factors
  length_le := by simp only [factors, List.length_append, List.length_singleton]; omega
  valid := hpool

theorem FactorCall.toPhaseCall_product (c : FactorCall X) (R P : ℕ)
    (hlen : c.selected.length < R)
    (hpool : ∀ p ∈ c.factors, p ∈ PrimePool.candidates P) :
    (c.toPhaseCall R P hlen hpool).factors.prod = c.erase.modulus :=
  c.erase_modulus.symm

/-- The factor three enters once, after the exact scalar/cyclic prime split. -/
theorem FactorCall.physical_product (c : FactorCall X) (R P S : ℕ)
    (hlen : c.selected.length < R)
    (hpool : ∀ p ∈ c.factors, p ∈ PrimePool.candidates P) :
    PhaseGeometry.physicalFold (c.toPhaseCall R P hlen hpool) S *
      (c.toPhaseCall R P hlen hpool).cyclic S = 3*c.erase.modulus := by
  rw [PhaseGeometry.physicalFold, Nat.mul_assoc,
    PhaseGeometry.PhaseCall.split, c.toPhaseCall_product]

/-- Direct phase annotation of a member of the actual restart trace. -/
def recordedPhaseCall (O : CountOracle X) (A : Instance X V) (pair : X → Pair)
    (lam k R P : ℕ) (pool : Finset ℕ) (n : ℕ) (active : Finset X)
    (marked : Finset Pair) (hk : k ≤ pool.card) (hR : k+1 ≤ R)
    (hpool : pool ⊆ PrimePool.candidates P) (c : FactorCall X)
    (hc : c ∈ (factorRestarts O A pair lam k pool n active marked).state.calls) :
    PhaseGeometry.PhaseCall R P :=
  let hv := factorRestarts_calls_valid O A pair lam k pool n active marked hk c hc
  c.toPhaseCall R P (hv.2.2.trans_le hR) (fun p hp => hpool (hv.2.1 p hp))

theorem recordedPhaseCall_correct (O : CountOracle X) (A : Instance X V)
    (pair : X → Pair) (lam k R P : ℕ) (pool : Finset ℕ) (n : ℕ)
    (active : Finset X) (marked : Finset Pair) (hk : k ≤ pool.card) (hR : k+1 ≤ R)
    (hpool : pool ⊆ PrimePool.candidates P) (c : FactorCall X)
    (hc : c ∈ (factorRestarts O A pair lam k pool n active marked).state.calls) :
    let call := recordedPhaseCall O A pair lam k R P pool n active marked hk hR hpool c hc
    call.factors = c.selected ++ [c.candidate] ∧ call.factors.Nodup ∧
      call.factors.prod = c.erase.modulus ∧ c.candidate ∉ c.selected := by
  have hv := factorRestarts_calls_valid O A pair lam k pool n active marked hk c hc
  refine ⟨rfl, hv.1, c.erase_modulus.symm, ?_⟩
  have hcat : (c.selected.concat c.candidate).Nodup := by
    simpa only [List.concat_eq_append, FactorCall.factors] using hv.1
  exact ((List.nodup_concat c.selected c.candidate).mp hcat).1

/-- Every original recorded invocation is the erasure of its chronological
selected-prefix/candidate annotation. Oracle correctness is not needed here. -/
theorem actual_restarts_call_history (O : CountOracle X) (A : Instance X V)
    (pair : X → Pair) (lam k : ℕ) (pool : Finset ℕ) (n : ℕ)
    (active : Finset X) (marked : Finset Pair) (hk : k ≤ pool.card)
    (c : Call X) (hc : c ∈ (restarts O A pair lam k pool n active marked).calls) :
    ∃ annotated ∈ (factorRestarts O A pair lam k pool n active marked).state.calls,
      annotated.erase = c ∧ annotated.factors.Nodup ∧
      (∀ p ∈ annotated.factors, p ∈ pool) ∧ annotated.selected.length < k+1 := by
  have he := congrArg StageResult.calls
    (factorRestarts_erases O A pair lam k pool n active marked)
  change List.map FactorCall.erase _ = _ at he
  rw [← he] at hc
  obtain ⟨annotated, ha, heq⟩ := List.mem_map.mp hc
  obtain ⟨hnd, hmem, hlen⟩ :=
    factorRestarts_calls_valid O A pair lam k pool n active marked hk annotated ha
  exact ⟨annotated, ha, heq, hnd, hmem, hlen⟩

/-- The phase witness is built from the actual call's retained factor history. -/
theorem actual_restarts_call_phase (O : CountOracle X) (A : Instance X V)
    (pair : X → Pair) (lam k R P : ℕ) (pool : Finset ℕ) (n : ℕ)
    (active : Finset X) (marked : Finset Pair) (hk : k ≤ pool.card) (hR : k+1 ≤ R)
    (hpool : pool ⊆ PrimePool.candidates P) (c : Call X)
    (hc : c ∈ (restarts O A pair lam k pool n active marked).calls) :
    ∃ call : PhaseGeometry.PhaseCall R P,
      call.factors.Nodup ∧ call.factors.prod = c.modulus := by
  obtain ⟨annotated, ha, heq, _, _, _⟩ :=
    actual_restarts_call_history O A pair lam k pool n active marked hk c hc
  let call := recordedPhaseCall O A pair lam k R P pool n active marked hk hR hpool annotated ha
  have hv := recordedPhaseCall_correct O A pair lam k R P pool n active marked
    hk hR hpool annotated ha
  exact ⟨call, hv.2.1, by rw [hv.2.2.1, heq]⟩

/-- Candidate counts and returned-table cell counts are exactly the already
instrumented program's quantities, even after all restart annotations. -/
theorem factorRestarts_resources (O : CountOracle X) (A : Instance X V)
    (pair : X → Pair) (lam k : ℕ) (pool : Finset ℕ) (n : ℕ)
    (active : Finset X) (marked : Finset Pair) :
    let out := (factorRestarts O A pair lam k pool n active marked).state
    out.calls.length ≤ n*(k+1)*pool.card ∧
      tableCells (out.calls.map FactorCall.erase) ≤ n*(k+1)*pool.card*active.card ∧
      out.bookkeeping ≤ 16*n*(k+1)*(pool.card+1)*(active.card+1) := by
  have he := factorRestarts_erases O A pair lam k pool n active marked
  have hc := congrArg StageResult.calls he
  have hl := congrArg List.length hc
  simp only [FactorStageResult.erase, List.length_map] at hl
  have hb := congrArg StageResult.bookkeeping he
  change (factorRestarts O A pair lam k pool n active marked).state.bookkeeping = _ at hb
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · rw [hl]
    exact restarts_calls_bound O A pair lam k pool n active marked
  · change tableCells (factorRestarts O A pair lam k pool n active marked).state.erase.calls ≤ _
    rw [he]
    exact restarts_tableCells_bound O A pair lam k pool n active marked
  · rw [hb]
    exact restarts_bookkeeping_bound O A pair lam k pool n active marked

/-- All candidates in all rounds and restarts retain the n^eta charge. -/
theorem actual_restarts_candidate_charge (O : CountOracle X) (A : Instance X V)
    (pair : X → Pair) (lam k stages n logPower : ℕ) (pool : Finset ℕ)
    (active : Finset X) (marked : Finset Pair) (hn : 3 ≤ n)
    (hpool : pool ⊆ PrimePool.candidates (PhaseGeometry.primeScale n AsymptoticCosts.eta logPower)) :
    ((restarts O A pair lam k pool stages active marked).calls.length : ℝ) ≤
      (stages:ℝ)*(k+1)*16*(Real.log (n:ℝ))^logPower*(n:ℝ)^AsymptoticCosts.eta := by
  have hcpool : (pool.card:ℝ) ≤
      ((PrimePool.candidates (PhaseGeometry.primeScale n AsymptoticCosts.eta logPower)).card:ℝ) := by
    exact_mod_cast Finset.card_le_card hpool
  have hc : (pool.card:ℝ) ≤
      16*(Real.log (n:ℝ))^logPower*(n:ℝ)^AsymptoticCosts.eta :=
    hcpool.trans (PhaseGeometry.actual_candidate_count n logPower hn)
  have hb : ((restarts O A pair lam k pool stages active marked).calls.length : ℝ) ≤
      (stages:ℝ)*(k+1)*(pool.card:ℝ) := by
    exact_mod_cast restarts_calls_bound O A pair lam k pool stages active marked
  calc
    _ ≤ (stages:ℝ)*(k+1)*(pool.card:ℝ) := hb
    _ ≤ (stages:ℝ)*(k+1)*(16*(Real.log (n:ℝ))^logPower*(n:ℝ)^AsymptoticCosts.eta) :=
      mul_le_mul_of_nonneg_left hc (by positivity)
    _ = _ := by ring

/-- The signed-window physical modulus and the coprime cyclic factor belong
to each actual original call, including the final R-factor batch. -/
theorem actual_restarts_call_full_phase (O : CountOracle X) (A : Instance X V)
    (pair : X → Pair) (lam k P : ℕ) (pool : Finset ℕ) (stages : ℕ)
    (active : Finset X) (marked : Finset Pair) (hk : k ≤ pool.card)
    (hR : k+1 ≤ AlignedCertificate.R) (hP : 3 ≤ P)
    (hpool : pool ⊆ PrimePool.candidates P) (c : Call X)
    (hc : c ∈ (restarts O A pair lam k pool stages active marked).calls) :
    ∃ call : PhaseGeometry.PhaseCall AlignedCertificate.R P,
      call.factors.Nodup ∧ call.factors.prod = c.modulus ∧
      PhaseGeometry.physicalFold call AlignedCertificate.S * call.cyclic AlignedCertificate.S =
        3*c.modulus ∧
      (PhaseGeometry.physicalFold call AlignedCertificate.S).Coprime
        (call.cyclic AlignedCertificate.S) ∧
      ∀ i : Fin 6, PhaseGeometry.phaseCostExponent
        (PhaseGeometry.foldExponent AlignedCertificate.S call.factors.length)
        (PhaseGeometry.ringExponent AlignedCertificate.S call.factors.length) i <
          AsymptoticCosts.targetExponent := by
  obtain ⟨call, hnd, hprod⟩ := actual_restarts_call_phase O A pair lam k
    AlignedCertificate.R P pool stages active marked hk hR hpool c hc
  refine ⟨call, hnd, hprod, ?_, PhaseGeometry.actual_call_coprime call
    AlignedCertificate.S hP hnd, PhaseGeometry.actual_call_exponent_strict call⟩
  rw [PhaseGeometry.physicalFold, Nat.mul_assoc, PhaseGeometry.PhaseCall.split, hprod]

/-- One eventual threshold fits every original recorded call, simultaneously
for all oracle contents, candidate subsets, rounds, and restart inputs. -/
theorem actual_restarts_tiles_fit_eventually (logPower : ℕ) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ∀ (O : CountOracle X) (A : Instance X V) (pair : X → Pair)
        (lam k stages : ℕ) (pool : Finset ℕ) (active : Finset X) (marked : Finset Pair),
        k ≤ pool.card → k+1 ≤ AlignedCertificate.R →
        pool ⊆ PrimePool.candidates (PhaseGeometry.primeScale n AsymptoticCosts.eta logPower) →
        ∀ c ∈ (restarts O A pair lam k pool stages active marked).calls,
          ∃ call : PhaseGeometry.PhaseCall AlignedCertificate.R
              (PhaseGeometry.primeScale n AsymptoticCosts.eta logPower),
            call.factors.Nodup ∧ call.factors.prod = c.modulus ∧
              (Nat.ceil (RealCertificate.c*(PhaseGeometry.innerPower n call AlignedCertificate.S:ℝ))).choose
                  (PhaseGeometry.innerPower n call AlignedCertificate.S) *
                4^(Nat.ceil (RealCertificate.c*(PhaseGeometry.innerPower n call AlignedCertificate.S:ℝ)) -
                  PhaseGeometry.innerPower n call AlignedCertificate.S) ≤
                PhaseGeometry.outerSize call AlignedCertificate.S n := by
  filter_upwards [PhaseGeometry.all_actual_candidate_tiles_fit logPower] with n hn
  intro O A pair lam k stages pool active marked hk hR hpool c hc
  obtain ⟨call, hnd, hprod⟩ := actual_restarts_call_phase O A pair lam k
    AlignedCertificate.R (PhaseGeometry.primeScale n AsymptoticCosts.eta logPower)
    pool stages active marked hk hR hpool c hc
  exact ⟨call, hnd, hprod, hn call⟩

/-- `solve` adds only an original-sum scan after these same annotated calls. -/
theorem actual_solve_call_phase (O : CountOracle X) (A : Instance X V)
    (pair : X → Pair) (lam k R P stages : ℕ) (pool : Finset ℕ) (initial : Finset X)
    (hk : k ≤ pool.card) (hR : k+1 ≤ R) (hpool : pool ⊆ PrimePool.candidates P)
    (c : Call X) (hc : c ∈ (solve O A pair lam k stages pool initial).calls) :
    ∃ call : PhaseGeometry.PhaseCall R P,
      call.factors.Nodup ∧ call.factors.prod = c.modulus :=
  actual_restarts_call_phase O A pair lam k R P pool stages initial ∅ hk hR hpool c hc

#print axioms factorGreedy_erases
#print axioms factorGreedy_final_invariants
#print axioms factorStage_erases
#print axioms factorRestarts_erases
#print axioms factorRestarts_calls_valid
#print axioms factorRestarts_calls_eq_logs
#print axioms recordedPhaseCall_correct
#print axioms actual_restarts_call_history
#print axioms actual_restarts_call_phase
#print axioms factorRestarts_resources
#print axioms actual_restarts_candidate_charge
#print axioms actual_restarts_call_full_phase
#print axioms actual_restarts_tiles_fit_eventually
#print axioms actual_solve_call_phase

end ThinMatrix.CompositePhaseTrace
