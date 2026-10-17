import ArrayCompositeAlgorithm

/-!
# Composite selection with retained backend results

Each remaining candidate is evaluated once into an array slot holding its
materialized count vector, actual producer payload, and returned work counter.
Score formation, selection, row preservation, and work summation all read
that same slot. No definition reruns the oracle to recover a resource bound.

The erasure theorems relate this joint producer to `ArrayCompositeAlgorithm`.
Returned backend work is summed exactly, without claiming it is RAM time:
the concrete backend must prove what its counter measures. The separate
controller visit counter describes dense scans and is not a word-RAM theorem
for Lean's persistent arrays.
-/

namespace ThinMatrix.CountedArrayComposite

open CompositeCertification CompositeAlgorithm

structure Table (I : ℕ) (Payload : Type*) where
  counts : ArrayCompositeAlgorithm.Counts I
  payload : Payload
  work : ℕ

structure Oracle (I : ℕ) (Payload : Type*) where
  table : List ℕ → ℕ → ArrayCompositeAlgorithm.Flags I → Table I Payload

def Oracle.erase {I : ℕ} {Payload : Type*} (O : Oracle I Payload) : ArrayCompositeAlgorithm.Oracle I :=
  ⟨fun selected candidate active => (O.table selected candidate active).counts⟩

def Oracle.Correct {I : ℕ} {Payload V : Type*} (O : Oracle I Payload)
    (inst : Instance (Fin I) V) : Prop := O.erase.Correct inst

/-- The producer proves the meaning of its returned counter separately. -/
def Oracle.WorkMatches {I : ℕ} {Payload : Type*} (O : Oracle I Payload)
    (measure : Payload → ℕ) : Prop :=
  ∀ selected candidate active,
    (O.table selected candidate active).work = measure (O.table selected candidate active).payload

structure Call (I : ℕ) (Payload : Type*) where
  factors : ArrayCompositeAlgorithm.FactorCall I
  result : Table I Payload

def eraseCalls {I : ℕ} {Payload : Type*} (calls : List (Call I Payload)) :
    List (ArrayCompositeAlgorithm.FactorCall I) := calls.map Call.factors

def workSum {I : ℕ} {Payload : Type*} (calls : List (Call I Payload)) : ℕ :=
  (calls.map (fun call => call.result.work)).sum

@[simp] theorem eraseCalls_append {I : ℕ} {Payload : Type*}
    (xs ys : List (Call I Payload)) :
    eraseCalls (xs ++ ys) = eraseCalls xs ++ eraseCalls ys := by simp [eraseCalls]

@[simp] theorem workSum_append {I : ℕ} {Payload : Type*}
    (xs ys : List (Call I Payload)) : workSum (xs ++ ys) = workSum xs + workSum ys := by
  simp [workSum]

abbrev Cache (P I : ℕ) (Payload : Type*) := Vector (Option (Table I Payload)) P

/-- The only producer invocation in a batch. Inactive candidate slots are
`none`, so no arbitrary dummy payload or repeated prime call is required. -/
def evaluateOnce {P I : ℕ} {Payload : Type*} (O : Oracle I Payload)
    (active : ArrayCompositeAlgorithm.Flags I) (primes : ArrayCompositeAlgorithm.Counts P) (remaining : ArrayCompositeAlgorithm.Flags P)
    (selected : List ℕ) : Cache P I Payload :=
  Vector.ofFn (fun p => if remaining.get p then
    some (O.table selected (primes.get p) active) else none)

@[simp] theorem get_evaluateOnce {P I : ℕ} {Payload : Type*} (O : Oracle I Payload)
    (active : ArrayCompositeAlgorithm.Flags I) (primes : ArrayCompositeAlgorithm.Counts P) (remaining : ArrayCompositeAlgorithm.Flags P)
    (selected : List ℕ) (p : Fin P) :
    (evaluateOnce O active primes remaining selected).get p =
      if remaining.get p then some (O.table selected (primes.get p) active) else none := by
  simp [evaluateOnce]

/-- This creates only a vector of references to already returned count rows. -/
def Cache.rows {P I : ℕ} {Payload : Type*} (cache : Cache P I Payload) : ArrayCompositeAlgorithm.Tables P I :=
  Vector.ofFn (fun p => match cache.get p with
    | none => Vector.replicate I 0
    | some result => result.counts)

theorem evaluateOnce_rows {P I : ℕ} {Payload : Type*} (O : Oracle I Payload)
    (active : ArrayCompositeAlgorithm.Flags I) (primes : ArrayCompositeAlgorithm.Counts P) (remaining : ArrayCompositeAlgorithm.Flags P)
    (d : ℕ) (selected : List ℕ) :
    (evaluateOnce O active primes remaining selected).rows =
      ArrayCompositeAlgorithm.evaluate O.erase active primes remaining d selected := by
  apply Vector.ext
  intro p hp
  simp only [Cache.rows, ArrayCompositeAlgorithm.evaluate]
  simp [get_evaluateOnce, Oracle.erase]
  split <;> simp_all

def Cache.callsFrom {P I : ℕ} {Payload : Type*} (cache : Cache P I Payload)
    (active : ArrayCompositeAlgorithm.Flags I) (primes : ArrayCompositeAlgorithm.Counts P) (selected : List ℕ) :
    List (Fin P) → List (Call I Payload)
  | [] => []
  | p :: ps =>
      match cache.get p with
      | none => cache.callsFrom active primes selected ps
      | some result => ⟨⟨selected, primes.get p, active⟩, result⟩ ::
          cache.callsFrom active primes selected ps

def Cache.calls {P I : ℕ} {Payload : Type*} (cache : Cache P I Payload)
    (active : ArrayCompositeAlgorithm.Flags I) (primes : ArrayCompositeAlgorithm.Counts P) (selected : List ℕ) : List (Call I Payload) :=
  cache.callsFrom active primes selected (List.finRange P)

theorem evaluateOnce_callsFrom {P I : ℕ} {Payload : Type*} (O : Oracle I Payload)
    (active : ArrayCompositeAlgorithm.Flags I) (primes : ArrayCompositeAlgorithm.Counts P) (remaining : ArrayCompositeAlgorithm.Flags P)
    (selected : List ℕ) (ps : List (Fin P)) :
    eraseCalls ((evaluateOnce O active primes remaining selected).callsFrom active primes selected ps) =
      (ps.filter (fun p => remaining.get p)).map (fun p => ⟨selected, primes.get p, active⟩) := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
      simp only [Cache.callsFrom, get_evaluateOnce]
      simp only [eraseCalls] at ih
      cases h : remaining.get p <;> simp [h, eraseCalls, ih]

@[simp] theorem evaluateOnce_calls {P I : ℕ} {Payload : Type*} (O : Oracle I Payload)
    (active : ArrayCompositeAlgorithm.Flags I) (primes : ArrayCompositeAlgorithm.Counts P) (remaining : ArrayCompositeAlgorithm.Flags P)
    (selected : List ℕ) :
    eraseCalls ((evaluateOnce O active primes remaining selected).calls active primes selected) =
      ArrayCompositeAlgorithm.batchCalls primes remaining active selected := by
  exact evaluateOnce_callsFrom O active primes remaining selected (List.finRange P)

/-- Every retained result is literally the producer return for the recorded
factor call. This theorem is a specification, not a second execution. -/
theorem evaluateOnce_call_result {P I : ℕ} {Payload : Type*} (O : Oracle I Payload)
    (active : ArrayCompositeAlgorithm.Flags I) (primes : ArrayCompositeAlgorithm.Counts P) (remaining : ArrayCompositeAlgorithm.Flags P)
    (selected : List ℕ) (ps : List (Fin P)) (call : Call I Payload)
    (hc : call ∈ (evaluateOnce O active primes remaining selected).callsFrom active primes selected ps) :
    call.result = O.table call.factors.selected call.factors.candidate call.factors.active := by
  induction ps with
  | nil => simp [Cache.callsFrom] at hc
  | cons p ps ih =>
      simp only [Cache.callsFrom, get_evaluateOnce] at hc
      cases h : remaining.get p <;> simp only [h] at hc
      · exact ih hc
      · rcases List.mem_cons.mp hc with rfl | hc
        · rfl
        · exact ih hc

/-- Thus the empty-selection branch cannot discard any actual producer call. -/
theorem choose_none_no_calls {P I : ℕ} {Payload : Type*} (O : Oracle I Payload)
    (active : ArrayCompositeAlgorithm.Flags I) (primes : ArrayCompositeAlgorithm.Counts P)
    (remaining : ArrayCompositeAlgorithm.Flags P) (selected : List ℕ)
    (values : ArrayCompositeAlgorithm.Counts P) (hn : ArrayCompositeAlgorithm.choose remaining values = none) :
    (evaluateOnce O active primes remaining selected).calls active primes selected = [] := by
  have hfalse : ∀ p, remaining.get p = false := by
    intro p
    cases h : remaining.get p with
    | false => rfl
    | true =>
        have hne : (ArrayCompositeAlgorithm.decode remaining).Nonempty :=
          ⟨p, (ArrayCompositeAlgorithm.mem_decode _ _).mpr h⟩
        obtain ⟨q, hq⟩ := ArrayCompositeAlgorithm.choose_exists remaining values hne
        rw [hn] at hq
        contradiction
  have hlist (ps : List (Fin P)) :
      (evaluateOnce O active primes remaining selected).callsFrom active primes selected ps = [] := by
    induction ps with
    | nil => rfl
    | cons p ps ih => simp [Cache.callsFrom, get_evaluateOnce, hfalse p, ih]
  exact hlist _

/-- Bounded indexed visits, kept separate from the returned backend counter.
The `I` term includes preservation/copy of a selected base row before cache
reuse. A RAM implementation must still prove the corresponding loop costs. -/
def batchVisits (P I : ℕ) : ℕ := P * I + 6 * P + I

structure GreedyResult (P I : ℕ) (Payload : Type*) where
  modulus : ℕ
  remaining : ArrayCompositeAlgorithm.Flags P
  base : ArrayCompositeAlgorithm.Counts I
  selected : List ℕ
  calls : List (Call I Payload)
  backendWork : ℕ
  controllerVisits : ℕ

def GreedyResult.erase {P I : ℕ} {Payload : Type*} (out : GreedyResult P I Payload) :
    ArrayCompositeAlgorithm.GreedyResult P I :=
  ⟨out.modulus, out.remaining, out.base, out.selected, eraseCalls out.calls⟩

def greedy {P I : ℕ} {Payload : Type*} (O : Oracle I Payload)
    (active : ArrayCompositeAlgorithm.Flags I) (primes : ArrayCompositeAlgorithm.Counts P) :
    ℕ → ℕ → ArrayCompositeAlgorithm.Flags P → ArrayCompositeAlgorithm.Counts I → List ℕ → GreedyResult P I Payload
  | 0, d, remaining, base, selected => ⟨d, remaining, base, selected, [], 0, 0⟩
  | k + 1, d, remaining, base, selected =>
      let cache := evaluateOnce O active primes remaining selected
      let rows := cache.rows
      let scalarScores := ArrayCompositeAlgorithm.scores active rows
      match ArrayCompositeAlgorithm.choose remaining scalarScores with
      | none => ⟨d, remaining, base, selected, [], 0, batchVisits P I⟩
      | some p =>
          let calls := cache.calls active primes selected
          let tail := greedy O active primes k (d * primes.get p)
            (ArrayCompositeAlgorithm.put remaining p false) (rows.get p) (selected ++ [primes.get p])
          { tail with
            calls := calls ++ tail.calls
            backendWork := workSum calls + tail.backendWork
            controllerVisits := batchVisits P I + tail.controllerVisits }

theorem greedy_erases {P I : ℕ} {Payload : Type*} (O : Oracle I Payload)
    (active : ArrayCompositeAlgorithm.Flags I) (primes : ArrayCompositeAlgorithm.Counts P) (k d : ℕ)
    (remaining : ArrayCompositeAlgorithm.Flags P) (base : ArrayCompositeAlgorithm.Counts I) (selected : List ℕ) :
    (greedy O active primes k d remaining base selected).erase =
      ArrayCompositeAlgorithm.greedy O.erase active primes k d remaining base selected := by
  induction k generalizing d remaining base selected with
  | zero => rfl
  | succ k ih =>
      simp only [greedy, ArrayCompositeAlgorithm.greedy, evaluateOnce_rows O active primes remaining d selected]
      split
      · rename_i hp
        rw [hp]
        rfl
      · rename_i p hp
        rw [hp]
        have ht := ih (d * primes.get p) (ArrayCompositeAlgorithm.put remaining p false)
          ((ArrayCompositeAlgorithm.evaluate O.erase active primes remaining d selected).get p) (selected ++ [primes.get p])
        have hf := congrArg ArrayCompositeAlgorithm.GreedyResult.modulus ht
        have hr := congrArg ArrayCompositeAlgorithm.GreedyResult.remaining ht
        have hb := congrArg ArrayCompositeAlgorithm.GreedyResult.base ht
        have hs := congrArg ArrayCompositeAlgorithm.GreedyResult.selected ht
        have hc := congrArg ArrayCompositeAlgorithm.GreedyResult.calls ht
        simp only [GreedyResult.erase, eraseCalls_append, evaluateOnce_calls] at hf hr hb hs hc ⊢
        rw [hf, hr, hb, hs, hc]

theorem greedy_backendWork {P I : ℕ} {Payload : Type*} (O : Oracle I Payload)
    (active : ArrayCompositeAlgorithm.Flags I) (primes : ArrayCompositeAlgorithm.Counts P) (k d : ℕ)
    (remaining : ArrayCompositeAlgorithm.Flags P) (base : ArrayCompositeAlgorithm.Counts I) (selected : List ℕ) :
    (greedy O active primes k d remaining base selected).backendWork =
      workSum (greedy O active primes k d remaining base selected).calls := by
  induction k generalizing d remaining base selected with
  | zero => rfl
  | succ k ih =>
      simp only [greedy]
      split
      · rfl
      · rw [workSum_append, ih]

theorem greedy_retained_results {P I : ℕ} {Payload : Type*} (O : Oracle I Payload)
    (active : ArrayCompositeAlgorithm.Flags I) (primes : ArrayCompositeAlgorithm.Counts P)
    (k d : ℕ) (remaining : ArrayCompositeAlgorithm.Flags P) (base : ArrayCompositeAlgorithm.Counts I)
    (selected : List ℕ) :
    ∀ call ∈ (greedy O active primes k d remaining base selected).calls,
      call.result = O.table call.factors.selected call.factors.candidate call.factors.active := by
  induction k generalizing d remaining base selected with
  | zero => simp [greedy]
  | succ k ih =>
      simp only [greedy]
      split
      · simp
      · rename_i p hp
        intro call hc
        rcases List.mem_append.mp hc with hc | hc
        · exact evaluateOnce_call_result O active primes remaining selected (List.finRange P) call hc
        · exact ih _ _ _ _ call hc

theorem greedy_visits_bound {P I : ℕ} {Payload : Type*} (O : Oracle I Payload)
    (active : ArrayCompositeAlgorithm.Flags I) (primes : ArrayCompositeAlgorithm.Counts P) (k d : ℕ)
    (remaining : ArrayCompositeAlgorithm.Flags P) (base : ArrayCompositeAlgorithm.Counts I) (selected : List ℕ) :
    (greedy O active primes k d remaining base selected).controllerVisits ≤ k * batchVisits P I := by
  induction k generalizing d remaining base selected with
  | zero => simp [greedy]
  | succ k ih =>
      simp only [greedy]
      split
      · dsimp only
        nlinarith
      · rename_i p hp
        have ht := ih (d * primes.get p) (ArrayCompositeAlgorithm.put remaining p false)
          (((evaluateOnce O active primes remaining selected).rows).get p) (selected ++ [primes.get p])
        dsimp only
        nlinarith

structure StageResult (P I Q : ℕ) (Payload : Type*) where
  active : ArrayCompositeAlgorithm.Flags I
  marked : ArrayCompositeAlgorithm.Flags Q
  selected : List ℕ
  calls : List (Call I Payload)
  backendWork : ℕ
  controllerVisits : ℕ

def StageResult.erase {P I Q : ℕ} {Payload : Type*} (out : StageResult P I Q Payload) :
    ArrayCompositeAlgorithm.StageResult P I Q := ⟨out.active, out.marked, out.selected, eraseCalls out.calls⟩

def finalVisits (P I : ℕ) : ℕ := 2 * P * I + 5 * I + 4 * P

def stage {P I Q : ℕ} {Payload : Type*} (O : Oracle I Payload) (owner : ArrayCompositeAlgorithm.Owners I Q)
    (primes : ArrayCompositeAlgorithm.Counts P) (active : ArrayCompositeAlgorithm.Flags I) (marked : ArrayCompositeAlgorithm.Flags Q)
    (blockSizes : ArrayCompositeAlgorithm.Counts I) (remaining : ArrayCompositeAlgorithm.Flags P) (k lam : ℕ) : StageResult P I Q Payload :=
  let chosen := greedy O active primes k 1 remaining blockSizes []
  let cache := evaluateOnce O active primes chosen.remaining chosen.selected
  let rows := cache.rows
  let mu := ArrayCompositeAlgorithm.minima rows chosen.remaining
  let out := ArrayCompositeAlgorithm.finish owner active marked chosen.base mu lam (ArrayCompositeAlgorithm.population chosen.remaining)
  let calls := cache.calls active primes chosen.selected
  ⟨out.active, out.marked, chosen.selected, chosen.calls ++ calls,
    chosen.backendWork + workSum calls,
    chosen.controllerVisits + finalVisits P I⟩

theorem stage_erases {P I Q : ℕ} {Payload : Type*} (O : Oracle I Payload)
    (owner : ArrayCompositeAlgorithm.Owners I Q) (primes : ArrayCompositeAlgorithm.Counts P) (active : ArrayCompositeAlgorithm.Flags I) (marked : ArrayCompositeAlgorithm.Flags Q)
    (blockSizes : ArrayCompositeAlgorithm.Counts I) (remaining : ArrayCompositeAlgorithm.Flags P) (k lam : ℕ) :
    (stage O owner primes active marked blockSizes remaining k lam).erase =
      ArrayCompositeAlgorithm.stage O.erase owner primes active marked blockSizes remaining k lam := by
  have hg := greedy_erases O active primes k 1 remaining blockSizes []
  have hf := congrArg ArrayCompositeAlgorithm.GreedyResult.modulus hg
  have hr := congrArg ArrayCompositeAlgorithm.GreedyResult.remaining hg
  have hb := congrArg ArrayCompositeAlgorithm.GreedyResult.base hg
  have hs := congrArg ArrayCompositeAlgorithm.GreedyResult.selected hg
  have hc := congrArg ArrayCompositeAlgorithm.GreedyResult.calls hg
  simp only [GreedyResult.erase] at hf hr hb hs hc
  simp only [stage, StageResult.erase, ArrayCompositeAlgorithm.stage, eraseCalls_append, evaluateOnce_calls]
  rw [evaluateOnce_rows O active primes
    (greedy O active primes k 1 remaining blockSizes []).remaining
    (greedy O active primes k 1 remaining blockSizes []).modulus
    (greedy O active primes k 1 remaining blockSizes []).selected]
  rw [hf, hr, hb, hs, hc]

theorem stage_backendWork {P I Q : ℕ} {Payload : Type*} (O : Oracle I Payload)
    (owner : ArrayCompositeAlgorithm.Owners I Q) (primes : ArrayCompositeAlgorithm.Counts P) (active : ArrayCompositeAlgorithm.Flags I) (marked : ArrayCompositeAlgorithm.Flags Q)
    (blockSizes : ArrayCompositeAlgorithm.Counts I) (remaining : ArrayCompositeAlgorithm.Flags P) (k lam : ℕ) :
    (stage O owner primes active marked blockSizes remaining k lam).backendWork =
      workSum (stage O owner primes active marked blockSizes remaining k lam).calls := by
  simp only [stage, workSum_append, greedy_backendWork]

theorem stage_retained_results {P I Q : ℕ} {Payload : Type*} (O : Oracle I Payload)
    (owner : ArrayCompositeAlgorithm.Owners I Q) (primes : ArrayCompositeAlgorithm.Counts P)
    (active : ArrayCompositeAlgorithm.Flags I) (marked : ArrayCompositeAlgorithm.Flags Q)
    (blockSizes : ArrayCompositeAlgorithm.Counts I) (remaining : ArrayCompositeAlgorithm.Flags P) (k lam : ℕ) :
    ∀ call ∈ (stage O owner primes active marked blockSizes remaining k lam).calls,
      call.result = O.table call.factors.selected call.factors.candidate call.factors.active := by
  intro call hc
  rcases List.mem_append.mp hc with hc | hc
  · exact greedy_retained_results O active primes k 1 remaining blockSizes [] call hc
  · exact evaluateOnce_call_result O active primes
      (greedy O active primes k 1 remaining blockSizes []).remaining
      (greedy O active primes k 1 remaining blockSizes []).selected (List.finRange P) call hc

theorem stage_visits_bound {P I Q : ℕ} {Payload : Type*} (O : Oracle I Payload)
    (owner : ArrayCompositeAlgorithm.Owners I Q) (primes : ArrayCompositeAlgorithm.Counts P) (active : ArrayCompositeAlgorithm.Flags I) (marked : ArrayCompositeAlgorithm.Flags Q)
    (blockSizes : ArrayCompositeAlgorithm.Counts I) (remaining : ArrayCompositeAlgorithm.Flags P) (k lam : ℕ) :
    (stage O owner primes active marked blockSizes remaining k lam).controllerVisits ≤
      k * batchVisits P I + finalVisits P I := by
  exact Nat.add_le_add_right (greedy_visits_bound O active primes k 1 remaining blockSizes []) _

def restarts {P I Q : ℕ} {Payload : Type*} (O : Oracle I Payload)
    (owner : ArrayCompositeAlgorithm.Owners I Q) (primes : ArrayCompositeAlgorithm.Counts P) (blockSizes : ArrayCompositeAlgorithm.Counts I)
    (remaining : ArrayCompositeAlgorithm.Flags P) (k lam : ℕ) : ℕ → ArrayCompositeAlgorithm.Flags I → ArrayCompositeAlgorithm.Flags Q → StageResult P I Q Payload
  | 0, active, marked => ⟨active, marked, [], [], 0, 0⟩
  | n + 1, active, marked =>
      let one := stage O owner primes active marked blockSizes remaining k lam
      let tail := restarts O owner primes blockSizes remaining k lam n one.active one.marked
      { tail with
        calls := one.calls ++ tail.calls
        backendWork := one.backendWork + tail.backendWork
        controllerVisits := one.controllerVisits + tail.controllerVisits }

theorem restarts_erases {P I Q : ℕ} {Payload : Type*} (O : Oracle I Payload)
    (owner : ArrayCompositeAlgorithm.Owners I Q) (primes : ArrayCompositeAlgorithm.Counts P) (blockSizes : ArrayCompositeAlgorithm.Counts I)
    (remaining : ArrayCompositeAlgorithm.Flags P) (k lam n : ℕ) (active : ArrayCompositeAlgorithm.Flags I) (marked : ArrayCompositeAlgorithm.Flags Q) :
    (restarts O owner primes blockSizes remaining k lam n active marked).erase =
      ArrayCompositeAlgorithm.restarts O.erase owner primes blockSizes remaining k lam n active marked := by
  induction n generalizing active marked with
  | zero => rfl
  | succ n ih =>
      have hs := stage_erases O owner primes active marked blockSizes remaining k lam
      have ha := congrArg ArrayCompositeAlgorithm.StageResult.active hs
      have hm := congrArg ArrayCompositeAlgorithm.StageResult.marked hs
      have hc := congrArg ArrayCompositeAlgorithm.StageResult.calls hs
      simp only [StageResult.erase] at ha hm hc
      simp only [restarts, ArrayCompositeAlgorithm.restarts]
      have ht := ih (stage O owner primes active marked blockSizes remaining k lam).active
        (stage O owner primes active marked blockSizes remaining k lam).marked
      simp only [StageResult.erase, eraseCalls_append] at ht ⊢
      rw [ha, hm] at ht
      have hta := congrArg ArrayCompositeAlgorithm.StageResult.active ht
      have htm := congrArg ArrayCompositeAlgorithm.StageResult.marked ht
      have hts := congrArg ArrayCompositeAlgorithm.StageResult.selected ht
      have htc := congrArg ArrayCompositeAlgorithm.StageResult.calls ht
      simp only at hta htm hts htc
      rw [ha, hm]
      rw [hta, htm, hts, htc, hc]

theorem restarts_backendWork {P I Q : ℕ} {Payload : Type*} (O : Oracle I Payload)
    (owner : ArrayCompositeAlgorithm.Owners I Q) (primes : ArrayCompositeAlgorithm.Counts P) (blockSizes : ArrayCompositeAlgorithm.Counts I)
    (remaining : ArrayCompositeAlgorithm.Flags P) (k lam n : ℕ) (active : ArrayCompositeAlgorithm.Flags I) (marked : ArrayCompositeAlgorithm.Flags Q) :
    (restarts O owner primes blockSizes remaining k lam n active marked).backendWork =
      workSum (restarts O owner primes blockSizes remaining k lam n active marked).calls := by
  induction n generalizing active marked with
  | zero => rfl
  | succ n ih => simp only [restarts, workSum_append, stage_backendWork, ih]

theorem restarts_retained_results {P I Q : ℕ} {Payload : Type*} (O : Oracle I Payload)
    (owner : ArrayCompositeAlgorithm.Owners I Q) (primes : ArrayCompositeAlgorithm.Counts P)
    (blockSizes : ArrayCompositeAlgorithm.Counts I) (remaining : ArrayCompositeAlgorithm.Flags P)
    (k lam n : ℕ) (active : ArrayCompositeAlgorithm.Flags I) (marked : ArrayCompositeAlgorithm.Flags Q) :
    ∀ call ∈ (restarts O owner primes blockSizes remaining k lam n active marked).calls,
      call.result = O.table call.factors.selected call.factors.candidate call.factors.active := by
  induction n generalizing active marked with
  | zero => simp [restarts]
  | succ n ih =>
      intro call hc
      rcases List.mem_append.mp hc with hc | hc
      · exact stage_retained_results O owner primes active marked blockSizes remaining k lam call hc
      · exact ih _ _ call hc

theorem restarts_work_measure {P I Q : ℕ} {Payload : Type*} (O : Oracle I Payload)
    (measure : Payload → ℕ) (hmeasure : O.WorkMatches measure)
    (owner : ArrayCompositeAlgorithm.Owners I Q) (primes : ArrayCompositeAlgorithm.Counts P)
    (blockSizes : ArrayCompositeAlgorithm.Counts I) (remaining : ArrayCompositeAlgorithm.Flags P)
    (k lam n : ℕ) (active : ArrayCompositeAlgorithm.Flags I) (marked : ArrayCompositeAlgorithm.Flags Q) :
    (restarts O owner primes blockSizes remaining k lam n active marked).backendWork =
      ((restarts O owner primes blockSizes remaining k lam n active marked).calls.map
        (fun call => measure call.result.payload)).sum := by
  rw [restarts_backendWork, workSum]
  congr 1
  apply List.map_congr_left
  intro call hc
  rw [restarts_retained_results O owner primes blockSizes remaining k lam n active marked call hc]
  exact hmeasure _ _ _

theorem restarts_visits_bound {P I Q : ℕ} {Payload : Type*} (O : Oracle I Payload)
    (owner : ArrayCompositeAlgorithm.Owners I Q) (primes : ArrayCompositeAlgorithm.Counts P) (blockSizes : ArrayCompositeAlgorithm.Counts I)
    (remaining : ArrayCompositeAlgorithm.Flags P) (k lam n : ℕ) (active : ArrayCompositeAlgorithm.Flags I) (marked : ArrayCompositeAlgorithm.Flags Q) :
    (restarts O owner primes blockSizes remaining k lam n active marked).controllerVisits ≤
      n * (k * batchVisits P I + finalVisits P I) := by
  induction n generalizing active marked with
  | zero => simp [restarts]
  | succ n ih =>
      let one := stage O owner primes active marked blockSizes remaining k lam
      have hs := stage_visits_bound O owner primes active marked blockSizes remaining k lam
      have ht := ih one.active one.marked
      change one.controllerVisits +
        (restarts O owner primes blockSizes remaining k lam n one.active one.marked).controllerVisits ≤ _
      nlinarith

/-- A purely structural bound, including the empty-pool failure branch. -/
theorem array_greedy_history_lengths {P I : ℕ} (O : ArrayCompositeAlgorithm.Oracle I)
    (active : ArrayCompositeAlgorithm.Flags I) (primes : ArrayCompositeAlgorithm.Counts P)
    (k d : ℕ) (remaining : ArrayCompositeAlgorithm.Flags P) (base : ArrayCompositeAlgorithm.Counts I)
    (selected : List ℕ) :
    let out := ArrayCompositeAlgorithm.greedy O active primes k d remaining base selected
    out.selected.length ≤ selected.length + k ∧
      ∀ call ∈ out.calls, call.selected.length < selected.length + k := by
  induction k generalizing d remaining base selected with
  | zero => exact ⟨by simp [ArrayCompositeAlgorithm.greedy], by simp [ArrayCompositeAlgorithm.greedy]⟩
  | succ k ih =>
      simp only [ArrayCompositeAlgorithm.greedy]
      split
      · exact ⟨by simp, by simp⟩
      · rename_i p hp
        have ht := ih (d * primes.get p) (ArrayCompositeAlgorithm.put remaining p false)
          ((ArrayCompositeAlgorithm.evaluate O active primes remaining d selected).get p)
          (selected ++ [primes.get p])
        refine ⟨?_, ?_⟩
        · dsimp only
          simpa [List.length_append, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ht.1
        · intro call hc
          rcases List.mem_append.mp hc with hc | hc
          · obtain ⟨q, _, rfl⟩ := List.mem_map.mp hc
            simp
          · have hl := ht.2 call hc
            simpa [List.length_append, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hl

theorem array_stage_factors_length_le {P I Q : ℕ} (O : ArrayCompositeAlgorithm.Oracle I)
    (owner : ArrayCompositeAlgorithm.Owners I Q) (primes : ArrayCompositeAlgorithm.Counts P)
    (active : ArrayCompositeAlgorithm.Flags I) (marked : ArrayCompositeAlgorithm.Flags Q)
    (blockSizes : ArrayCompositeAlgorithm.Counts I) (remaining : ArrayCompositeAlgorithm.Flags P) (k lam : ℕ) :
    ∀ call ∈ (ArrayCompositeAlgorithm.stage O owner primes active marked blockSizes remaining k lam).calls,
      call.selected.length + 1 ≤ k + 1 := by
  have hg := array_greedy_history_lengths O active primes k 1 remaining blockSizes []
  simp only [List.length_nil, zero_add] at hg
  intro call hc
  rcases List.mem_append.mp hc with hc | hc
  · have hl := hg.2 call hc
    omega
  · obtain ⟨p, _, rfl⟩ := List.mem_map.mp hc
    exact Nat.add_le_add_right hg.1 1

theorem array_restarts_factors_length_le {P I Q : ℕ} (O : ArrayCompositeAlgorithm.Oracle I)
    (owner : ArrayCompositeAlgorithm.Owners I Q) (primes : ArrayCompositeAlgorithm.Counts P)
    (blockSizes : ArrayCompositeAlgorithm.Counts I) (remaining : ArrayCompositeAlgorithm.Flags P)
    (k lam n : ℕ) (active : ArrayCompositeAlgorithm.Flags I) (marked : ArrayCompositeAlgorithm.Flags Q) :
    ∀ call ∈ (ArrayCompositeAlgorithm.restarts O owner primes blockSizes remaining k lam n active marked).calls,
      call.selected.length + 1 ≤ k + 1 := by
  induction n generalizing active marked with
  | zero => simp [ArrayCompositeAlgorithm.restarts]
  | succ n ih =>
      intro call hc
      rcases List.mem_append.mp hc with hc | hc
      · exact array_stage_factors_length_le O owner primes active marked blockSizes remaining k lam call hc
      · exact ih _ _ call hc

theorem restarts_factors_length_le {P I Q : ℕ} {Payload : Type*} (O : Oracle I Payload)
    (owner : ArrayCompositeAlgorithm.Owners I Q) (primes : ArrayCompositeAlgorithm.Counts P)
    (blockSizes : ArrayCompositeAlgorithm.Counts I) (remaining : ArrayCompositeAlgorithm.Flags P)
    (k lam n : ℕ) (active : ArrayCompositeAlgorithm.Flags I) (marked : ArrayCompositeAlgorithm.Flags Q) :
    ∀ call ∈ (restarts O owner primes blockSizes remaining k lam n active marked).calls,
      call.factors.selected.length + 1 ≤ k + 1 := by
  have he := congrArg ArrayCompositeAlgorithm.StageResult.calls
    (restarts_erases O owner primes blockSizes remaining k lam n active marked)
  simp only [StageResult.erase] at he
  intro call hc
  have hmem : call.factors ∈
      (ArrayCompositeAlgorithm.restarts O.erase owner primes blockSizes remaining k lam n active marked).calls := by
    rw [← he]
    exact List.mem_map.mpr ⟨call, hc, rfl⟩
  exact array_restarts_factors_length_le O.erase owner primes blockSizes remaining k lam n active marked _ hmem

theorem restarts_calls_bound {P I Q : ℕ} {Payload : Type*} (O : Oracle I Payload)
    (owner : ArrayCompositeAlgorithm.Owners I Q) (primes : ArrayCompositeAlgorithm.Counts P)
    (blockSizes : ArrayCompositeAlgorithm.Counts I) (remaining : ArrayCompositeAlgorithm.Flags P)
    (k lam n : ℕ) (active : ArrayCompositeAlgorithm.Flags I) (marked : ArrayCompositeAlgorithm.Flags Q) :
    (restarts O owner primes blockSizes remaining k lam n active marked).calls.length ≤ n * (k + 1) * P := by
  have he := congrArg ArrayCompositeAlgorithm.StageResult.calls
    (restarts_erases O owner primes blockSizes remaining k lam n active marked)
  have hl := congrArg List.length he
  simp only [StageResult.erase, eraseCalls, List.length_map] at hl
  rw [hl]
  exact ArrayCompositeAlgorithm.restarts_calls_bound O.erase owner primes blockSizes remaining k lam n active marked

theorem restarts_factors_distinct {P I Q : ℕ} {Payload : Type*} (O : Oracle I Payload)
    (owner : ArrayCompositeAlgorithm.Owners I Q) (primes : ArrayCompositeAlgorithm.Counts P)
    (hinj : Function.Injective primes.get) (blockSizes : ArrayCompositeAlgorithm.Counts I)
    (remaining : ArrayCompositeAlgorithm.Flags P) (k lam n : ℕ)
    (active : ArrayCompositeAlgorithm.Flags I) (marked : ArrayCompositeAlgorithm.Flags Q) :
    ∀ call ∈ (restarts O owner primes blockSizes remaining k lam n active marked).calls,
      (call.factors.selected ++ [call.factors.candidate]).Nodup := by
  have he := congrArg ArrayCompositeAlgorithm.StageResult.calls
    (restarts_erases O owner primes blockSizes remaining k lam n active marked)
  simp only [StageResult.erase] at he
  intro call hc
  apply ArrayCompositeAlgorithm.restarts_factors_distinct O.erase owner primes hinj blockSizes remaining k lam n active marked
  rw [← he]
  exact List.mem_map.mpr ⟨call, hc, rfl⟩

theorem restarts_factors_property {P I Q : ℕ} {Payload : Type*} (O : Oracle I Payload)
    (owner : ArrayCompositeAlgorithm.Owners I Q) (primes : ArrayCompositeAlgorithm.Counts P)
    (property : ℕ → Prop) (hprimes : ∀ p, property (primes.get p))
    (blockSizes : ArrayCompositeAlgorithm.Counts I) (remaining : ArrayCompositeAlgorithm.Flags P)
    (k lam n : ℕ) (active : ArrayCompositeAlgorithm.Flags I) (marked : ArrayCompositeAlgorithm.Flags Q) :
    ∀ call ∈ (restarts O owner primes blockSizes remaining k lam n active marked).calls,
      ∀ p ∈ call.factors.selected ++ [call.factors.candidate], property p := by
  have he := congrArg ArrayCompositeAlgorithm.StageResult.calls
    (restarts_erases O owner primes blockSizes remaining k lam n active marked)
  simp only [StageResult.erase] at he
  intro call hc
  apply ArrayCompositeAlgorithm.restarts_factors_property O.erase owner primes property hprimes blockSizes remaining k lam n active marked
  rw [← he]
  exact List.mem_map.mpr ⟨call, hc, rfl⟩

end ThinMatrix.CountedArrayComposite

#print axioms ThinMatrix.CountedArrayComposite.evaluateOnce_rows
#print axioms ThinMatrix.CountedArrayComposite.evaluateOnce_call_result
#print axioms ThinMatrix.CountedArrayComposite.greedy_erases
#print axioms ThinMatrix.CountedArrayComposite.greedy_backendWork
#print axioms ThinMatrix.CountedArrayComposite.stage_erases
#print axioms ThinMatrix.CountedArrayComposite.stage_backendWork
#print axioms ThinMatrix.CountedArrayComposite.restarts_erases
#print axioms ThinMatrix.CountedArrayComposite.restarts_backendWork
#print axioms ThinMatrix.CountedArrayComposite.restarts_visits_bound
#print axioms ThinMatrix.CountedArrayComposite.choose_none_no_calls
#print axioms ThinMatrix.CountedArrayComposite.restarts_retained_results
#print axioms ThinMatrix.CountedArrayComposite.restarts_work_measure
#print axioms ThinMatrix.CountedArrayComposite.array_restarts_factors_length_le
#print axioms ThinMatrix.CountedArrayComposite.restarts_factors_length_le
#print axioms ThinMatrix.CountedArrayComposite.restarts_calls_bound
#print axioms ThinMatrix.CountedArrayComposite.restarts_factors_distinct
#print axioms ThinMatrix.CountedArrayComposite.restarts_factors_property
