import CompositeAlgorithm

/-!
# Dense array passes for composite certification

Incidences, output pairs, candidate rows, and their scores have fixed dense
addresses. The executable definitions below use array-backed vectors and
bounded list scans; `decode` and all finite sets occur only in specifications.
In particular, marking is one incidence scan followed by a separate survivor
scan. It does not rescan all incidences separately for every output pair.

The visit counters in this file are not a claim about the running time of
Lean's persistent array implementation. The actual Light store-loop proof
is in the separate machine package. Compiling all the remaining passes and
the complete oracle/controller composition is still required for a RAM
running-time theorem.
-/

namespace ThinMatrix.ArrayCompositeAlgorithm

open CompositeCertification CompositeAlgorithm
open scoped BigOperators

abbrev Flags (n : ℕ) := Vector Bool n
abbrev Counts (n : ℕ) := Vector ℕ n
abbrev Owners (I Q : ℕ) := Vector (Fin Q) I
abbrev Tables (P I : ℕ) := Vector (Counts I) P

/-- Ghost interpretation; this function is not called by any array pass. -/
def decode {n : ℕ} (flags : Flags n) : Finset (Fin n) :=
  Finset.univ.filter (fun i => flags.get i = true)

@[simp] theorem mem_decode {n : ℕ} (flags : Flags n) (i : Fin n) :
    i ∈ decode flags ↔ flags.get i = true := by simp [decode]

def put {n : ℕ} (flags : Flags n) (i : Fin n) (b : Bool) : Flags n :=
  flags.set i.val b i.isLt

@[simp] theorem get_put {n : ℕ} (flags : Flags n) (i j : Fin n) (b : Bool) :
    (put flags i b).get j = if j = i then b else flags.get j := by
  by_cases h : j = i
  · subst j
    change (flags.set i.val b i.isLt)[i.val] = if i = i then b else flags[i.val]
    rw [if_pos rfl]
    exact Vector.getElem_set_self i.isLt
  · have hv : i.val ≠ j.val := by intro he; exact h (Fin.ext he.symm)
    simp only [if_neg h]
    exact Vector.getElem_set_ne i.isLt j.isLt hv

/-- One bounded scan; inactive positions still occupy their original slots. -/
def scoreScan {I : ℕ} (active : Flags I) (row : Counts I) :
    List (Fin I) → ℕ × ℕ
  | [] => (0, 0)
  | i :: is =>
      let tail := scoreScan active row is
      ((if active.get i then row.get i else 0) + tail.1, tail.2 + 1)

def score {I : ℕ} (active : Flags I) (row : Counts I) : ℕ :=
  (scoreScan active row (List.finRange I)).1

theorem scoreScan_value {I : ℕ} (active : Flags I) (row : Counts I)
    (is : List (Fin I)) :
    (scoreScan active row is).1 =
      (is.map (fun i => if active.get i then row.get i else 0)).sum := by
  induction is with
  | nil => rfl
  | cons i is ih => simp [scoreScan, ih]

@[simp] theorem scoreScan_visits {I : ℕ} (active : Flags I) (row : Counts I)
    (is : List (Fin I)) : (scoreScan active row is).2 = is.length := by
  induction is with
  | nil => rfl
  | cons i is ih => simp [scoreScan, ih]

theorem score_eq {I : ℕ} (active : Flags I) (row : Counts I) :
    score active row = ∑ i ∈ decode active, row.get i := by
  rw [score, scoreScan_value]
  rw [← List.sum_toFinset _ (List.nodup_finRange I)]
  simp only [List.toFinset_finRange]
  rw [decode, Finset.sum_filter]

/-- Cached scalar scores: the argmin comparator reads two scores, not two rows. -/
def scores {P I : ℕ} (active : Flags I) (rows : Tables P I) : Counts P :=
  Vector.ofFn (fun p => score active (rows.get p))

@[simp] theorem get_scores {P I : ℕ} (active : Flags I) (rows : Tables P I)
    (p : Fin P) : (scores active rows).get p = score active (rows.get p) := by
  simp [scores]

/-- A minimum scan with an explicit empty result; minima are never initialized
to zero. Ties choose the earlier index in the dense scan. -/
def best {P : ℕ} (values : Counts P) : List (Fin P) → Option (Fin P)
  | [] => none
  | p :: ps =>
      match best values ps with
      | none => some p
      | some q => some (if values.get p ≤ values.get q then p else q)

theorem best_none_iff {P : ℕ} (values : Counts P) (ps : List (Fin P)) :
    best values ps = none ↔ ps = [] := by
  cases ps with
  | nil => simp [best]
  | cons p ps => cases h : best values ps <;> simp [best, h]

theorem best_spec {P : ℕ} (values : Counts P) (ps : List (Fin P))
    {p : Fin P} (hp : best values ps = some p) :
    p ∈ ps ∧ ∀ q ∈ ps, values.get p ≤ values.get q := by
  induction ps generalizing p with
  | nil => simp [best] at hp
  | cons q qs ih =>
      cases htail : best values qs with
      | none =>
          have hn : qs = [] := (best_none_iff values qs).mp htail
          subst qs
          simp [best] at hp
          subst p
          simp
      | some r =>
          have hr := ih htail
          by_cases hqr : values.get q ≤ values.get r
          · simp [best, htail, hqr] at hp
            subst p
            refine ⟨by simp, ?_⟩
            intro s hs
            rcases List.mem_cons.mp hs with rfl | hs
            · exact le_rfl
            · exact hqr.trans (hr.2 s hs)
          · simp [best, htail, hqr] at hp
            subst p
            refine ⟨by simp [hr.1], ?_⟩
            intro s hs
            rcases List.mem_cons.mp hs with rfl | hs
            · omega
            · exact hr.2 s hs

def indices {P : ℕ} (remaining : Flags P) : List (Fin P) :=
  (List.finRange P).filter (fun p => remaining.get p)

@[simp] theorem mem_indices {P : ℕ} (remaining : Flags P) (p : Fin P) :
    p ∈ indices remaining ↔ remaining.get p = true := by simp [indices]

def choose {P : ℕ} (remaining : Flags P) (values : Counts P) : Option (Fin P) :=
  best values (indices remaining)

theorem choose_spec {P : ℕ} (remaining : Flags P) (values : Counts P)
    {p : Fin P} (hp : choose remaining values = some p) :
    remaining.get p = true ∧
      ∀ q, remaining.get q = true → values.get p ≤ values.get q := by
  have hs := best_spec values (indices remaining) hp
  exact ⟨(mem_indices remaining p).mp hs.1,
    fun q hq => hs.2 q ((mem_indices remaining q).mpr hq)⟩

theorem choose_exists {P : ℕ} (remaining : Flags P) (values : Counts P)
    (hne : (decode remaining).Nonempty) : ∃ p, choose remaining values = some p := by
  cases h : choose remaining values with
  | some p => exact ⟨p, rfl⟩
  | none =>
      have hempty : indices remaining = [] := (best_none_iff values _).mp h
      obtain ⟨p, hp⟩ := hne
      have := (mem_indices remaining p).mpr ((mem_decode remaining p).mp hp)
      simp [hempty] at this

/-- Both dimensions are materialized. There is no implicit function-valued
row or recomputation when the row is later selected as the base table. -/
structure Oracle (I : ℕ) where
  table : List ℕ → ℕ → Flags I → Counts I

def Oracle.Correct {I : ℕ} {V : Type*} (O : Oracle I)
    (A : Instance (Fin I) V) : Prop :=
  ∀ selected candidate active i, active.get i = true →
    (O.table selected candidate active).get i = A.modCount (selected.prod * candidate) i

def evaluate {P I : ℕ} (O : Oracle I) (active : Flags I)
    (primes : Counts P) (remaining : Flags P) (_d : ℕ) (selected : List ℕ) : Tables P I :=
  Vector.ofFn (fun p => if remaining.get p then O.table selected (primes.get p) active
    else Vector.replicate I 0)

@[simp] theorem get_evaluate {P I : ℕ} (O : Oracle I) (active : Flags I)
    (primes : Counts P) (remaining : Flags P) (d : ℕ) (selected : List ℕ) (p : Fin P)
    (hp : remaining.get p = true) :
    (evaluate O active primes remaining d selected).get p = O.table selected (primes.get p) active := by
  simp [evaluate, hp]

/-- Ghost prime pool; it is absent from oracle calls and all dense passes. -/
def pool {P : ℕ} (primes : Counts P) (remaining : Flags P) : Finset ℕ :=
  (decode remaining).image (fun p => primes.get p)

theorem choose_minimizes {P I : ℕ} {V : Type*} (O : Oracle I)
    (A : Instance (Fin I) V) (hO : O.Correct A) (active : Flags I)
    (primes : Counts P) (remaining : Flags P) (d : ℕ) (selected : List ℕ)
    (hd : selected.prod = d) {p : Fin P}
    (hp : choose remaining (scores active (evaluate O active primes remaining d selected)) = some p) :
    primes.get p ∈ pool primes remaining ∧
      ∀ q ∈ pool primes remaining,
        A.totalCount (decode active) (d * primes.get p) ≤
          A.totalCount (decode active) (d * q) := by
  have hs := choose_spec remaining _ hp
  have hscore (q : Fin P) (hq : remaining.get q = true) :
      (scores active (evaluate O active primes remaining d selected)).get q =
        A.totalCount (decode active) (d * primes.get q) := by
    rw [get_scores, get_evaluate _ _ _ _ _ _ _ hq, score_eq]
    exact Finset.sum_congr rfl (fun i hi => by
      simpa only [hd] using hO selected (primes.get q) active i ((mem_decode _ _).mp hi))
  refine ⟨Finset.mem_image.mpr ⟨p, (mem_decode _ _).mpr hs.1, rfl⟩, ?_⟩
  intro q hq
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hq
  simpa only [hscore p hs.1, hscore j ((mem_decode _ _).mp hj)] using
    hs.2 j ((mem_decode _ _).mp hj)

theorem pool_card {P : ℕ} (primes : Counts P) (remaining : Flags P)
    (hinj : Function.Injective primes.get) :
    (pool primes remaining).card = (decode remaining).card := by
  exact Finset.card_image_of_injective _ hinj

theorem pool_nonempty_iff {P : ℕ} (primes : Counts P) (remaining : Flags P) :
    (pool primes remaining).Nonempty ↔ (decode remaining).Nonempty := by
  exact Finset.image_nonempty

theorem decode_put_false {P : ℕ} (remaining : Flags P) (p : Fin P) :
    decode (put remaining p false) = (decode remaining).erase p := by
  ext q
  by_cases h : q = p <;> simp [get_put, h]

theorem pool_put_false {P : ℕ} (primes : Counts P) (remaining : Flags P)
    (hinj : Function.Injective primes.get) (p : Fin P) :
    pool primes (put remaining p false) = (pool primes remaining).erase (primes.get p) := by
  rw [pool, decode_put_false, Finset.image_erase hinj]
  rfl

/-- Physical candidate histories accompany every oracle call. Removed
candidates do not invoke the oracle, so factors cannot accidentally repeat. -/
structure FactorCall (I : ℕ) where
  selected : List ℕ
  candidate : ℕ
  active : Flags I

def FactorCall.modulus {I : ℕ} (call : FactorCall I) : ℕ :=
  call.selected.prod * call.candidate

def batchCalls {P I : ℕ} (primes : Counts P) (remaining : Flags P)
    (active : Flags I) (selected : List ℕ) : List (FactorCall I) :=
  (indices remaining).map (fun p => ⟨selected, primes.get p, active⟩)

theorem batchCalls_length_le {P I : ℕ} (primes : Counts P) (remaining : Flags P)
    (active : Flags I) (selected : List ℕ) :
    (batchCalls primes remaining active selected).length ≤ P := by
  simpa [batchCalls, indices] using List.length_filter_le (fun p => remaining.get p) (List.finRange P)

structure GreedyResult (P I : ℕ) where
  modulus : ℕ
  remaining : Flags P
  base : Counts I
  selected : List ℕ
  calls : List (FactorCall I)

/-- The incidence mask is fixed through every round of a common-prime
selection. Each round constructs the full cache, constructs its scores once,
selects one cached row, and preserves that row as the next base. -/
def greedy {P I : ℕ} (O : Oracle I) (active : Flags I) (primes : Counts P) :
    ℕ → ℕ → Flags P → Counts I → List ℕ → GreedyResult P I
  | 0, d, remaining, base, selected => ⟨d, remaining, base, selected, []⟩
  | k + 1, d, remaining, base, selected =>
      let rows := evaluate O active primes remaining d selected
      let scalarScores := scores active rows
      match choose remaining scalarScores with
      | none => ⟨d, remaining, base, selected, []⟩
      | some p =>
          let tail := greedy O active primes k (d * primes.get p)
            (put remaining p false) (rows.get p) (selected ++ [primes.get p])
          { tail with calls := batchCalls primes remaining active selected ++ tail.calls }

theorem greedy_correct {P I : ℕ} {V : Type*} (O : Oracle I)
    (A : Instance (Fin I) V) (hO : O.Correct A) (active : Flags I)
    (primes : Counts P) (hinj : Function.Injective primes.get)
    (k d : ℕ) (remaining : Flags P) (base : Counts I) (selected : List ℕ)
    (hd : selected.prod = d) (hk : k ≤ (pool primes remaining).card)
    (hbase : ∀ i, active.get i = true → base.get i = A.modCount d i) :
    let out := greedy O active primes k d remaining base selected
    OracleTrace A (decode active) (pool primes remaining) d k out.modulus
        (pool primes out.remaining) ∧
      ∀ i, active.get i = true → out.base.get i = A.modCount out.modulus i := by
  induction k generalizing d remaining base selected with
  | zero => exact ⟨OracleTrace.start, hbase⟩
  | succ k ih =>
      have hne : (decode remaining).Nonempty := by
        apply (pool_nonempty_iff primes remaining).mp
        exact Finset.card_pos.mp (by omega)
      obtain ⟨p, hp⟩ := choose_exists remaining
        (scores active (evaluate O active primes remaining d selected)) hne
      have hs := choose_minimizes O A hO active primes remaining d selected hd hp
      have hs' := choose_spec remaining _ hp
      have hnext : k ≤ (pool primes (put remaining p false)).card := by
        rw [pool_put_false primes remaining hinj p]
        have hc := Finset.card_erase_add_one hs.1
        omega
      have hb : ∀ i, active.get i = true →
          ((evaluate O active primes remaining d selected).get p).get i =
            A.modCount (d * primes.get p) i := by
        intro i hi
        rw [get_evaluate O active primes remaining d selected p hs'.1]
        simpa only [hd] using hO selected (primes.get p) active i hi
      have ht := ih (d * primes.get p) (put remaining p false)
        ((evaluate O active primes remaining d selected).get p) (selected ++ [primes.get p]) (by simp [hd]) hnext hb
      have first : OracleTrace A (decode active) (pool primes remaining) d 1
          (d * primes.get p) (pool primes (put remaining p false)) := by
        rw [pool_put_false primes remaining hinj p]
        exact OracleTrace.step OracleTrace.start hs.1 hs.2
      have tr := trace_append A (decode active) (pool primes remaining) d first ht.1
      simp only [greedy, hp]
      exact ⟨by simpa [Nat.add_comm] using tr, ht.2⟩

theorem greedy_calls_bound {P I : ℕ} (O : Oracle I) (active : Flags I)
    (primes : Counts P) (k d : ℕ) (remaining : Flags P) (base : Counts I)
    (selected : List ℕ) :
    (greedy O active primes k d remaining base selected).calls.length ≤ k * P := by
  induction k generalizing d remaining base selected with
  | zero => simp [greedy]
  | succ k ih =>
      simp only [greedy]
      split
      · simp
      · rename_i p hp
        have hb := batchCalls_length_le primes remaining active selected
        have ht := ih (d * primes.get p) (put remaining p false)
          ((evaluate O active primes remaining d selected).get p) (selected ++ [primes.get p])
        simp only [List.length_append]
        nlinarith

theorem greedy_factor_product {P I : ℕ} (O : Oracle I) (active : Flags I)
    (primes : Counts P) (k d : ℕ) (remaining : Flags P) (base : Counts I)
    (selected : List ℕ) (hd : selected.prod = d) :
    let out := greedy O active primes k d remaining base selected
    out.selected.prod = out.modulus ∧
      ∀ call ∈ out.calls, call.active = active := by
  induction k generalizing d remaining base selected with
  | zero => exact ⟨hd, by simp [greedy]⟩
  | succ k ih =>
      simp only [greedy]
      split
      · exact ⟨hd, by simp⟩
      · rename_i p hp
        have ht := ih (d * primes.get p) (put remaining p false)
          ((evaluate O active primes remaining d selected).get p) (selected ++ [primes.get p])
          (by simp [hd])
        refine ⟨ht.1, ?_⟩
        intro call hc
        rcases List.mem_append.mp hc with hc | hc
        · obtain ⟨q, _, rfl⟩ := List.mem_map.mp hc
          rfl
        · exact ht.2 call hc

theorem nodup_append_one {α : Type*} [DecidableEq α] (xs : List α) (x : α)
    (hx : xs.Nodup) (hnot : x ∉ xs) : (xs ++ [x]).Nodup := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
      have ha := List.nodup_cons.mp hx
      have hn : x ∉ xs := fun h => hnot (by simp [h])
      simp only [List.cons_append, List.nodup_cons, List.mem_append, List.mem_singleton]
      exact ⟨fun h => h.elim ha.1 (fun he => hnot (by simp [he])), ih ha.2 hn⟩

/-- Every backend call receives distinct physical prime factors; this is
proved from candidate erasure, not stipulated as an oracle assumption. -/
theorem greedy_factors_distinct {P I : ℕ} (O : Oracle I) (active : Flags I)
    (primes : Counts P) (hinj : Function.Injective primes.get) (k d : ℕ)
    (remaining : Flags P) (base : Counts I) (selected : List ℕ)
    (hnd : selected.Nodup)
    (hsep : ∀ p, remaining.get p = true → primes.get p ∉ selected) :
    let out := greedy O active primes k d remaining base selected
    out.selected.Nodup ∧
      (∀ p, out.remaining.get p = true → primes.get p ∉ out.selected) ∧
      ∀ call ∈ out.calls, (call.selected ++ [call.candidate]).Nodup ∧
        call.selected.length < selected.length + k := by
  induction k generalizing d remaining base selected with
  | zero => exact ⟨hnd, hsep, by simp [greedy]⟩
  | succ k ih =>
      simp only [greedy]
      split
      · exact ⟨hnd, hsep, by simp⟩
      · rename_i p hp
        have hs := choose_spec remaining _ hp
        have hnew : (selected ++ [primes.get p]).Nodup :=
          nodup_append_one selected _ hnd (hsep p hs.1)
        have hsep' : ∀ q, (put remaining p false).get q = true →
            primes.get q ∉ selected ++ [primes.get p] := by
          intro q hq
          by_cases hqp : q = p
          · simp [get_put, hqp] at hq
          · have hqold : remaining.get q = true := by simpa [get_put, hqp] using hq
            simp only [List.mem_append, List.mem_singleton, not_or]
            exact ⟨hsep q hqold, fun he => hqp (hinj he)⟩
        have ht := ih (d * primes.get p) (put remaining p false)
          ((evaluate O active primes remaining d selected).get p) (selected ++ [primes.get p]) hnew hsep'
        refine ⟨ht.1, ht.2.1, ?_⟩
        intro call hc
        rcases List.mem_append.mp hc with hc | hc
        · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hc
          have hq' := (mem_indices remaining q).mp hq
          exact ⟨nodup_append_one selected _ hnd (hsep q hq'), by simp⟩
        · have hc' := ht.2.2 call hc
          exact ⟨hc'.1, by simpa [List.length_append, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hc'.2⟩

theorem greedy_factor_budget {P I : ℕ} (O : Oracle I) (active : Flags I)
    (primes : Counts P) (hinj : Function.Injective primes.get) (k d : ℕ)
    (remaining : Flags P) (base : Counts I) (selected : List ℕ) :
    let out := greedy O active primes k d remaining base selected
    out.selected.length + (pool primes out.remaining).card =
      selected.length + (pool primes remaining).card := by
  induction k generalizing d remaining base selected with
  | zero => rfl
  | succ k ih =>
      simp only [greedy]
      split
      · rfl
      · rename_i p hp
        have hs := choose_spec remaining _ hp
        have hmem : primes.get p ∈ pool primes remaining :=
          Finset.mem_image.mpr ⟨p, (mem_decode _ _).mpr hs.1, rfl⟩
        have ht := ih (d * primes.get p) (put remaining p false)
          ((evaluate O active primes remaining d selected).get p) (selected ++ [primes.get p])
        rw [pool_put_false primes remaining hinj p] at ht
        have hc := Finset.card_erase_add_one hmem
        simp only [List.length_append, List.length_singleton] at ht
        dsimp only
        omega

theorem greedy_selected_length {P I : ℕ} {V : Type*} (O : Oracle I)
    (A : Instance (Fin I) V) (hO : O.Correct A) (active : Flags I)
    (primes : Counts P) (hinj : Function.Injective primes.get)
    (k d : ℕ) (remaining : Flags P) (base : Counts I) (selected : List ℕ)
    (hd : selected.prod = d) (hk : k ≤ (pool primes remaining).card)
    (hbase : ∀ i, active.get i = true → base.get i = A.modCount d i) :
    (greedy O active primes k d remaining base selected).selected.length = selected.length + k := by
  have hg := greedy_correct O A hO active primes hinj k d remaining base selected hd hk hbase
  have hc := trace_card A (decode active) (pool primes remaining) d hg.1
  have hb := greedy_factor_budget O active primes hinj k d remaining base selected
  omega

theorem greedy_factors_property {P I : ℕ} (O : Oracle I) (active : Flags I)
    (primes : Counts P) (property : ℕ → Prop) (hprimes : ∀ p, property (primes.get p))
    (k d : ℕ) (remaining : Flags P) (base : Counts I) (selected : List ℕ)
    (hsel : ∀ p ∈ selected, property p) :
    let out := greedy O active primes k d remaining base selected
    (∀ p ∈ out.selected, property p) ∧
      ∀ call ∈ out.calls, ∀ p ∈ call.selected ++ [call.candidate], property p := by
  induction k generalizing d remaining base selected with
  | zero => exact ⟨hsel, by simp [greedy]⟩
  | succ k ih =>
      simp only [greedy]
      split
      · exact ⟨hsel, by simp⟩
      · rename_i p hp
        have hnew : ∀ q ∈ selected ++ [primes.get p], property q := by
          intro q hq
          rcases List.mem_append.mp hq with hq | hq
          · exact hsel q hq
          · have : q = primes.get p := by simpa using hq
            subst q
            exact hprimes p
        have ht := ih (d * primes.get p) (put remaining p false)
          ((evaluate O active primes remaining d selected).get p) (selected ++ [primes.get p]) hnew
        refine ⟨ht.1, ?_⟩
        intro call hc q hq
        rcases List.mem_append.mp hc with hc | hc
        · obtain ⟨j, _, rfl⟩ := List.mem_map.mp hc
          rcases List.mem_append.mp hq with hq | hq
          · exact hsel q hq
          · have : q = primes.get j := by simpa using hq
            subst q
            exact hprimes j
        · exact ht.2 call hc q hq

def column {P I : ℕ} (rows : Tables P I) (i : Fin I) : Counts P :=
  Vector.ofFn (fun p => (rows.get p).get i)

@[simp] theorem get_column {P I : ℕ} (rows : Tables P I) (i : Fin I) (p : Fin P) :
    (column rows i).get p = (rows.get p).get i := by simp [column]

def minima {P I : ℕ} (rows : Tables P I) (remaining : Flags P) : Counts I :=
  let eligible := indices remaining
  Vector.ofFn (fun i =>
    match best (column rows i) eligible with
    | none => 0
    | some p => (rows.get p).get i)

theorem minima_correct {P I : ℕ} {V : Type*} (O : Oracle I)
    (A : Instance (Fin I) V) (hO : O.Correct A) (active : Flags I)
    (primes : Counts P) (remaining : Flags P) (d : ℕ) (selected : List ℕ)
    (hd : selected.prod = d) (hne : (pool primes remaining).Nonempty) (i : Fin I) (hi : active.get i = true) :
    (minima (evaluate O active primes remaining d selected) remaining).get i =
      A.minCount (pool primes remaining) hne d i := by
  obtain ⟨p, hp⟩ := choose_exists remaining
    (column (evaluate O active primes remaining d selected) i)
    ((pool_nonempty_iff primes remaining).mp hne)
  have hs := choose_spec remaining _ hp
  have hrow (q : Fin P) (hq : remaining.get q = true) :
      ((evaluate O active primes remaining d selected).get q).get i =
        A.modCount (d * primes.get q) i := by
    rw [get_evaluate O active primes remaining d selected q hq]
    simpa only [hd] using hO selected (primes.get q) active i hi
  have hvalue : (minima (evaluate O active primes remaining d selected) remaining).get i =
      A.modCount (d * primes.get p) i := by
    have hp' : best (column (evaluate O active primes remaining d selected) i)
        (indices remaining) = some p := hp
    simpa [minima, hp'] using hrow p hs.1
  rw [hvalue]
  apply Nat.le_antisymm
  · obtain ⟨q, hq, hqval⟩ := Finset.mem_image.mp
      (Finset.min'_mem ((pool primes remaining).image (fun q => A.modCount (d * q) i))
        (hne.image _))
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hq
    have hj' := (mem_decode _ _).mp hj
    have hle := hs.2 j hj'
    simp only [get_column] at hle
    rw [hrow p hs.1, hrow j hj'] at hle
    change A.modCount (d * primes.get p) i ≤
      ((pool primes remaining).image (fun q => A.modCount (d * q) i)).min' _
    rw [← hqval]
    exact hle
  · exact A.minCount_le _ hne d i (Finset.mem_image.mpr
      ⟨p, (mem_decode _ _).mpr hs.1, rfl⟩)

/-- A literal scatter pass over incidences. Pair lookup is an array read;
each affirmative incidence performs one Boolean write. -/
def markScan {I Q : ℕ} (owner : Owners I Q) (yes : Flags I) :
    Flags Q → List (Fin I) → Flags Q
  | marked, [] => marked
  | marked, i :: is =>
      markScan owner yes (if yes.get i then put marked (owner.get i) true else marked) is

theorem markScan_get {I Q : ℕ} (owner : Owners I Q) (yes : Flags I)
    (marked : Flags Q) (is : List (Fin I)) (q : Fin Q) :
    (markScan owner yes marked is).get q = true ↔
      marked.get q = true ∨ ∃ i ∈ is, yes.get i = true ∧ owner.get i = q := by
  induction is generalizing marked with
  | nil => simp [markScan]
  | cons i is ih =>
      rw [markScan, ih]
      cases hy : yes.get i with
      | false => simp [hy]
      | true =>
          simp only [if_true, get_put]
          by_cases hq : q = owner.get i
          · simp [hq, hy]
          · have hq' : owner.get i ≠ q := Ne.symm hq
            simp [hq, hq']

def mark {I Q : ℕ} (owner : Owners I Q) (yes : Flags I) (marked : Flags Q) : Flags Q :=
  markScan owner yes marked (List.finRange I)

@[simp] theorem mark_get {I Q : ℕ} (owner : Owners I Q) (yes : Flags I)
    (marked : Flags Q) (q : Fin Q) :
    (mark owner yes marked).get q = true ↔
      marked.get q = true ∨ ∃ i, yes.get i = true ∧ owner.get i = q := by
  simp [mark, markScan_get]

def affirmative {I : ℕ} (active : Flags I) (base minima : Counts I) (lam m : ℕ) : Flags I :=
  Vector.ofFn (fun i => active.get i && decide (lam * base.get i < m * minima.get i))

@[simp] theorem affirmative_get {I : ℕ} (active : Flags I) (base minima : Counts I)
    (lam m : ℕ) (i : Fin I) :
    (affirmative active base minima lam m).get i = true ↔
      active.get i = true ∧ lam * base.get i < m * minima.get i := by
  simp [affirmative]

/-- This pass runs only after *all* affirmative pair writes have finished. -/
def retain {I Q : ℕ} (owner : Owners I Q) (active : Flags I)
    (pairMarks : Flags Q) (base minima : Counts I) (lam m : ℕ) : Flags I :=
  Vector.ofFn (fun i => active.get i && decide (minima.get i ≠ 0) &&
    decide (m * minima.get i ≤ lam * base.get i) && !(pairMarks.get (owner.get i)))

@[simp] theorem retain_get {I Q : ℕ} (owner : Owners I Q) (active : Flags I)
    (pairMarks : Flags Q) (base minima : Counts I) (lam m : ℕ) (i : Fin I) :
    (retain owner active pairMarks base minima lam m).get i = true ↔
      active.get i = true ∧ minima.get i ≠ 0 ∧
        m * minima.get i ≤ lam * base.get i ∧ pairMarks.get (owner.get i) ≠ true := by
  simp [retain, and_assoc]

structure Result (I Q : ℕ) where
  active : Flags I
  marked : Flags Q

def finish {I Q : ℕ} (owner : Owners I Q) (active : Flags I) (marked : Flags Q)
    (base minima : Counts I) (lam m : ℕ) : Result I Q :=
  let yes := affirmative active base minima lam m
  let marked' := mark owner yes marked
  ⟨retain owner active marked' base minima lam m, marked'⟩

/-- The threshold uses the *current* pool size `m`; the two dense passes
refine the original exact certification semantics. -/
theorem finish_semantics {I Q : ℕ} {V : Type*} (A : Instance (Fin I) V)
    (owner : Owners I Q) (active : Flags I) (marked : Flags Q)
    (base minima : Counts I) (available : Finset ℕ) (hne : available.Nonempty)
    (lam d : ℕ)
    (hbase : ∀ i, active.get i = true → base.get i = A.modCount d i)
    (hmin : ∀ i, active.get i = true → minima.get i = A.minCount available hne d i) :
    decode (finish owner active marked base minima lam available.card).marked =
        A.markedAfter owner.get (decode marked) (decode active) available hne lam d ∧
    decode (finish owner active marked base minima lam available.card).active =
        A.survivors owner.get (decode marked) (decode active) available hne lam d := by
  have hmarked : decode (finish owner active marked base minima lam available.card).marked =
      A.markedAfter owner.get (decode marked) (decode active) available hne lam d := by
    ext q
    simp only [mem_decode, finish, mark_get, affirmative_get, Instance.markedAfter,
      Instance.certified, Finset.mem_union, Finset.mem_image, Finset.mem_filter, mem_decode]
    constructor
    · rintro (hq | ⟨i, ⟨hi, hy⟩, hp⟩)
      · exact Or.inl hq
      · exact Or.inr ⟨i, ⟨hi, by simpa [hbase i hi, hmin i hi] using hy⟩, hp⟩
    · rintro (hq | ⟨i, ⟨hi, hy⟩, hp⟩)
      · exact Or.inl hq
      · exact Or.inr ⟨i, ⟨hi, by simpa [hbase i hi, hmin i hi] using hy⟩, hp⟩
  refine ⟨hmarked, ?_⟩
  ext i
  have hmark :
      (mark owner (affirmative active base minima lam available.card) marked).get (owner.get i) = true ↔
        owner.get i ∈ A.markedAfter owner.get (decode marked) (decode active) available hne lam d := by
    have hm := (mem_decode (finish owner active marked base minima lam available.card).marked
      (owner.get i)).symm
    rw [hmarked] at hm
    exact hm
  simp only [mem_decode, finish, retain_get, Instance.survivors, Finset.mem_filter, mem_decode]
  constructor
  · rintro ⟨hi, hz, hf, hm⟩
    exact ⟨hi, by simpa [hmin i hi] using hz,
      by simpa [hbase i hi, hmin i hi] using hf, fun h => hm (hmark.mpr h)⟩
  · rintro ⟨hi, hz, hf, hm⟩
    exact ⟨hi, by simpa [hmin i hi] using hz,
      by simpa [hbase i hi, hmin i hi] using hf, fun h => hm (hmark.mp h)⟩

theorem finish_correct {I Q : ℕ} {V : Type*} (A : Instance (Fin I) V)
    (owner : Owners I Q) (initial : Finset (Fin I)) (active : Flags I) (marked : Flags Q)
    (base minima : Counts I) (initialPool available : Finset ℕ) (hne : available.Nonempty)
    (k M lam h d : ℕ)
    (hinv : A.StateInvariant owner.get initial (decode active) (decode marked))
    (tr : OracleTrace A (decode active) initialPool 1 k d available)
    (hbase : ∀ i, active.get i = true → base.get i = A.modCount d i)
    (hmin : ∀ i, active.get i = true → minima.get i = A.minCount available hne d i)
    (hM : lam < M) (hsize : M + k ≤ initialPool.card)
    (hdiv : A.DivisorBound initialPool lam)
    (hblock : ∀ i ∈ initial, (A.block i).card ≤ h)
    (hrate : 2 * h * lam ^ (k + 1) ≤ (M - lam) * M ^ k) :
    let out := finish owner active marked base minima lam available.card
    A.StateInvariant owner.get initial (decode out.active) (decode out.marked) ∧
      2 * (decode out.active).card ≤ (decode active).card := by
  have hs := finish_semantics A owner active marked base minima available hne lam d hbase hmin
  dsimp only
  rw [hs.1, hs.2]
  exact ⟨A.stage_invariant owner.get initial (decode active) (decode marked) available hne lam d
      hinv (A.divisorBound_subset hdiv (trace_subset A (decode active) initialPool 1 tr)),
    trace_halves A owner.get (decode marked) (decode active) initialPool tr hne M lam h hM hsize
      hdiv (fun i hi => hblock i (hinv.1 hi)) hrate⟩

/-- Executable current candidate count: a dense Boolean scan. -/
def population {P : ℕ} (remaining : Flags P) : ℕ := (indices remaining).length

theorem population_eq {P : ℕ} (remaining : Flags P) :
    population remaining = (decode remaining).card := by
  have hset : (indices remaining).toFinset = decode remaining := by
    ext p
    simp
  have hnd : (indices remaining).Nodup :=
    (List.nodup_finRange P).filter (fun p => remaining.get p)
  rw [population, ← hset]
  exact (List.toFinset_card_of_nodup hnd).symm

structure StageResult (P I Q : ℕ) where
  active : Flags I
  marked : Flags Q
  selected : List ℕ
  calls : List (FactorCall I)

/-- One complete dense stage. Initial block sizes are supplied as materialized
input data. The stage calls no finite-set operation. -/
def stage {P I Q : ℕ} (O : Oracle I) (owner : Owners I Q) (primes : Counts P)
    (active : Flags I) (marked : Flags Q) (blockSizes : Counts I)
    (remaining : Flags P) (k lam : ℕ) : StageResult P I Q :=
  let chosen := greedy O active primes k 1 remaining blockSizes []
  let rows := evaluate O active primes chosen.remaining chosen.modulus chosen.selected
  let mu := minima rows chosen.remaining
  let out := finish owner active marked chosen.base mu lam (population chosen.remaining)
  ⟨out.active, out.marked, chosen.selected,
    chosen.calls ++ batchCalls primes chosen.remaining active chosen.selected⟩

theorem stage_correct {P I Q : ℕ} {V : Type*} (O : Oracle I)
    (A : Instance (Fin I) V) (hO : O.Correct A) (owner : Owners I Q)
    (primes : Counts P) (hinj : Function.Injective primes.get)
    (initial : Finset (Fin I)) (active : Flags I) (marked : Flags Q)
    (blockSizes : Counts I) (remaining : Flags P) (k M lam h : ℕ)
    (hinv : A.StateInvariant owner.get initial (decode active) (decode marked))
    (hbase : ∀ i, active.get i = true → blockSizes.get i = (A.block i).card)
    (hM : lam < M) (hsize : M + k ≤ (pool primes remaining).card)
    (hdiv : A.DivisorBound (pool primes remaining) lam)
    (hblock : ∀ i ∈ initial, (A.block i).card ≤ h)
    (hrate : 2 * h * lam ^ (k + 1) ≤ (M - lam) * M ^ k) :
    let out := stage O owner primes active marked blockSizes remaining k lam
    A.StateInvariant owner.get initial (decode out.active) (decode out.marked) ∧
      2 * (decode out.active).card ≤ (decode active).card := by
  let chosen := greedy O active primes k 1 remaining blockSizes []
  have hg := greedy_correct O A hO active primes hinj k 1 remaining blockSizes []
    rfl (by omega) (fun i hi => (hbase i hi).trans (A.count_one i).symm)
  have hc := trace_card A (decode active) (pool primes remaining) 1 hg.1
  have hne : (pool primes chosen.remaining).Nonempty := by
    exact Finset.card_pos.mp (by dsimp [chosen]; omega)
  have hf := greedy_factor_product O active primes k 1 remaining blockSizes [] rfl
  have hm := minima_correct O A hO active primes chosen.remaining chosen.modulus chosen.selected hf.1 hne
  have hs := finish_correct A owner initial active marked chosen.base
    (minima (evaluate O active primes chosen.remaining chosen.modulus chosen.selected) chosen.remaining)
    (pool primes remaining) (pool primes chosen.remaining) hne k M lam h chosen.modulus
    hinv hg.1 hg.2 hm hM hsize hdiv hblock hrate
  have hpop : population chosen.remaining = (pool primes chosen.remaining).card := by
    rw [population_eq, pool_card primes chosen.remaining hinj]
  simpa only [stage, chosen, hpop] using hs

theorem stage_calls_bound {P I Q : ℕ} (O : Oracle I) (owner : Owners I Q)
    (primes : Counts P) (active : Flags I) (marked : Flags Q) (blockSizes : Counts I)
    (remaining : Flags P) (k lam : ℕ) :
    (stage O owner primes active marked blockSizes remaining k lam).calls.length ≤ (k + 1) * P := by
  have hg := greedy_calls_bound O active primes k 1 remaining blockSizes []
  have hb := batchCalls_length_le primes
    (greedy O active primes k 1 remaining blockSizes []).remaining active
    (greedy O active primes k 1 remaining blockSizes []).selected
  simp only [stage, List.length_append]
  nlinarith

theorem stage_factors_distinct {P I Q : ℕ} (O : Oracle I) (owner : Owners I Q)
    (primes : Counts P) (hinj : Function.Injective primes.get)
    (active : Flags I) (marked : Flags Q) (blockSizes : Counts I)
    (remaining : Flags P) (k lam : ℕ) :
    ∀ call ∈ (stage O owner primes active marked blockSizes remaining k lam).calls,
      (call.selected ++ [call.candidate]).Nodup := by
  have hg := greedy_factors_distinct O active primes hinj k 1 remaining blockSizes []
    (by simp) (by simp)
  intro call hc
  rcases List.mem_append.mp hc with hc | hc
  · exact (hg.2.2 call hc).1
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hc
    exact nodup_append_one _ _ hg.1 (hg.2.1 p ((mem_indices _ _).mp hp))

theorem stage_factors_property {P I Q : ℕ} (O : Oracle I) (owner : Owners I Q)
    (primes : Counts P) (property : ℕ → Prop) (hprimes : ∀ p, property (primes.get p))
    (active : Flags I) (marked : Flags Q) (blockSizes : Counts I)
    (remaining : Flags P) (k lam : ℕ) :
    ∀ call ∈ (stage O owner primes active marked blockSizes remaining k lam).calls,
      ∀ p ∈ call.selected ++ [call.candidate], property p := by
  have hg := greedy_factors_property O active primes property hprimes k 1 remaining blockSizes [] (by simp)
  intro call hc p hp
  rcases List.mem_append.mp hc with hc | hc
  · exact hg.2 call hc p hp
  · obtain ⟨j, _, rfl⟩ := List.mem_map.mp hc
    rcases List.mem_append.mp hp with hp | hp
    · exact hg.1 p hp
    · have : p = primes.get j := by simpa using hp
      subst p
      exact hprimes j

/-- Each restart resets the prime mask and modulus, while retaining the
dense incidence mask and already certified pair flags. -/
def restarts {P I Q : ℕ} (O : Oracle I) (owner : Owners I Q) (primes : Counts P)
    (blockSizes : Counts I) (remaining : Flags P) (k lam : ℕ) :
    ℕ → Flags I → Flags Q → StageResult P I Q
  | 0, active, marked => ⟨active, marked, [], []⟩
  | n + 1, active, marked =>
      let one := stage O owner primes active marked blockSizes remaining k lam
      let tail := restarts O owner primes blockSizes remaining k lam n one.active one.marked
      { tail with calls := one.calls ++ tail.calls }

theorem restarts_correct {P I Q : ℕ} {V : Type*} (O : Oracle I)
    (A : Instance (Fin I) V) (hO : O.Correct A) (owner : Owners I Q)
    (primes : Counts P) (hinj : Function.Injective primes.get)
    (initial : Finset (Fin I)) (active : Flags I) (marked : Flags Q)
    (blockSizes : Counts I) (remaining : Flags P) (k M lam h n : ℕ)
    (hinv : A.StateInvariant owner.get initial (decode active) (decode marked))
    (hbase : ∀ i ∈ initial, blockSizes.get i = (A.block i).card)
    (hM : lam < M) (hsize : M + k ≤ (pool primes remaining).card)
    (hdiv : A.DivisorBound (pool primes remaining) lam)
    (hblock : ∀ i ∈ initial, (A.block i).card ≤ h)
    (hrate : 2 * h * lam ^ (k + 1) ≤ (M - lam) * M ^ k) :
    let out := restarts O owner primes blockSizes remaining k lam n active marked
    A.StateInvariant owner.get initial (decode out.active) (decode out.marked) ∧
      2 ^ n * (decode out.active).card ≤ (decode active).card := by
  induction n generalizing active marked with
  | zero => exact ⟨hinv, by simp [restarts]⟩
  | succ n ih =>
      have hs := stage_correct O A hO owner primes hinj initial active marked blockSizes remaining
        k M lam h hinv (fun i hi => hbase i (hinv.1 ((mem_decode _ _).mpr hi)))
        hM hsize hdiv hblock hrate
      let one := stage O owner primes active marked blockSizes remaining k lam
      have ht := ih one.active one.marked hs.1
      refine ⟨ht.1, ?_⟩
      change 2 ^ (n + 1) *
        (decode (restarts O owner primes blockSizes remaining k lam n one.active one.marked).active).card ≤ _
      calc
        _ = 2 * (2 ^ n *
            (decode (restarts O owner primes blockSizes remaining k lam n one.active one.marked).active).card) := by
          rw [pow_succ]; ring
        _ ≤ 2 * (decode one.active).card := Nat.mul_le_mul_left _ ht.2
        _ ≤ _ := hs.2

theorem restarts_calls_bound {P I Q : ℕ} (O : Oracle I) (owner : Owners I Q)
    (primes : Counts P) (blockSizes : Counts I) (remaining : Flags P)
    (k lam n : ℕ) (active : Flags I) (marked : Flags Q) :
    (restarts O owner primes blockSizes remaining k lam n active marked).calls.length ≤
      n * (k + 1) * P := by
  induction n generalizing active marked with
  | zero => simp [restarts]
  | succ n ih =>
      let one := stage O owner primes active marked blockSizes remaining k lam
      have hs := stage_calls_bound O owner primes active marked blockSizes remaining k lam
      have ht := ih one.active one.marked
      change (one.calls ++
        (restarts O owner primes blockSizes remaining k lam n one.active one.marked).calls).length ≤ _
      rw [List.length_append]
      nlinarith

theorem restarts_factors_distinct {P I Q : ℕ} (O : Oracle I) (owner : Owners I Q)
    (primes : Counts P) (hinj : Function.Injective primes.get) (blockSizes : Counts I)
    (remaining : Flags P) (k lam n : ℕ) (active : Flags I) (marked : Flags Q) :
    ∀ call ∈ (restarts O owner primes blockSizes remaining k lam n active marked).calls,
      (call.selected ++ [call.candidate]).Nodup := by
  induction n generalizing active marked with
  | zero => simp [restarts]
  | succ n ih =>
      let one := stage O owner primes active marked blockSizes remaining k lam
      intro call hc
      rcases List.mem_append.mp hc with hc | hc
      · exact stage_factors_distinct O owner primes hinj active marked blockSizes remaining k lam call hc
      · exact ih one.active one.marked call hc

theorem restarts_factors_property {P I Q : ℕ} (O : Oracle I) (owner : Owners I Q)
    (primes : Counts P) (property : ℕ → Prop) (hprimes : ∀ p, property (primes.get p))
    (blockSizes : Counts I) (remaining : Flags P) (k lam n : ℕ)
    (active : Flags I) (marked : Flags Q) :
    ∀ call ∈ (restarts O owner primes blockSizes remaining k lam n active marked).calls,
      ∀ p ∈ call.selected ++ [call.candidate], property p := by
  induction n generalizing active marked with
  | zero => simp [restarts]
  | succ n ih =>
      let one := stage O owner primes active marked blockSizes remaining k lam
      intro call hc
      rcases List.mem_append.mp hc with hc | hc
      · exact stage_factors_property O owner primes property hprimes active marked blockSizes remaining k lam call hc
      · exact ih one.active one.marked call hc

/-- At termination the dense arrays support the same exact final original-sum
scan theorem. This statement does not treat `trueCount` as executable code. -/
theorem final_scan_of_invariant {I Q : ℕ} {V : Type*} (A : Instance (Fin I) V)
    (owner : Owners I Q) (initial : Finset (Fin I)) (active : Flags I) (marked : Flags Q)
    (hinv : A.StateInvariant owner.get initial (decode active) (decode marked)) :
    decode marked ∪ A.exactPairs owner.get (decode active) = A.exactPairs owner.get initial :=
  A.final_exact_scan owner.get initial (decode active) (decode marked) hinv

/-- Dense row-major address, with every candidate row charged. -/
def cell {P I : ℕ} (p : Fin P) (i : Fin I) : ℕ := p.val * I + i.val

theorem cell_lt {P I : ℕ} (p : Fin P) (i : Fin I) : cell p i < P * I := by
  unfold cell
  calc
    p.val * I + i.val < p.val * I + I := Nat.add_lt_add_left i.isLt _
    _ = (p.val + 1) * I := by ring
    _ ≤ P * I := Nat.mul_le_mul_right I (by omega)

def storage (P I Q k : ℕ) : ℕ := P * I + 3 * P + 7 * I + Q + k

/- `storage` charges the full count table, scalar scores, primes, remaining
flags, active/YES/owner/base/minimum/block-size/next-active vectors, pair marks,
and the selected-factor history. It excludes oracle-private memory,
which the backend must add. No space or work bound uses active.card in
place of the original dense incidence dimension I. -/

end ThinMatrix.ArrayCompositeAlgorithm

#print axioms ThinMatrix.ArrayCompositeAlgorithm.choose_minimizes
#print axioms ThinMatrix.ArrayCompositeAlgorithm.greedy_correct
#print axioms ThinMatrix.ArrayCompositeAlgorithm.greedy_calls_bound
#print axioms ThinMatrix.ArrayCompositeAlgorithm.greedy_factor_product
#print axioms ThinMatrix.ArrayCompositeAlgorithm.greedy_factors_distinct
#print axioms ThinMatrix.ArrayCompositeAlgorithm.greedy_selected_length
#print axioms ThinMatrix.ArrayCompositeAlgorithm.greedy_factors_property
#print axioms ThinMatrix.ArrayCompositeAlgorithm.minima_correct
#print axioms ThinMatrix.ArrayCompositeAlgorithm.stage_correct
#print axioms ThinMatrix.ArrayCompositeAlgorithm.stage_calls_bound
#print axioms ThinMatrix.ArrayCompositeAlgorithm.stage_factors_distinct
#print axioms ThinMatrix.ArrayCompositeAlgorithm.stage_factors_property
#print axioms ThinMatrix.ArrayCompositeAlgorithm.restarts_correct
#print axioms ThinMatrix.ArrayCompositeAlgorithm.restarts_calls_bound
#print axioms ThinMatrix.ArrayCompositeAlgorithm.restarts_factors_distinct
#print axioms ThinMatrix.ArrayCompositeAlgorithm.restarts_factors_property
#print axioms ThinMatrix.ArrayCompositeAlgorithm.final_scan_of_invariant
#print axioms ThinMatrix.ArrayCompositeAlgorithm.markScan_get
#print axioms ThinMatrix.ArrayCompositeAlgorithm.finish_semantics
#print axioms ThinMatrix.ArrayCompositeAlgorithm.finish_correct
#print axioms ThinMatrix.ArrayCompositeAlgorithm.cell_lt
