import CountedArrayComposite
import IntegerNormalization

/-!
# Operational dense composite controller

These joint evaluators execute bounded vector/list loops and retain both their
values and their scalar/indexed-array instruction counters. A backend table
producer is invoked once at each eligible slot. Its payload and returned work
are shared by the score, selection, row, call-history, and work-sum passes.
Backend production is excluded from the controller counter.

An indexed read/write is one operation in this finite array IR. This does not
assert the runtime of Lean persistent arrays or a Light machine compilation.
Arithmetic sites are later priced by a uniform bounded-bit primitive unit.
-/

namespace ThinMatrix.DenseControllerExecution
open ArrayCompositeAlgorithm
open scoped BigOperators

structure Result (α : Type*) where
  value : α
  sites : ℕ

/-- One execution per scalar score; the recursive result is shared. -/
def scoreScan {I : ℕ} (active : Flags I) (row : Counts I) :
    List (Fin I) → Result ℕ
  | [] => ⟨0, 1⟩
  | i :: is =>
    let tail := scoreScan active row is
    let flag := active.get i
    let entry := if flag then row.get i else 0
    ⟨entry + tail.value, tail.sites + 6⟩

theorem scoreScan_value {I : ℕ} (active : Flags I) (row : Counts I)
    (is : List (Fin I)) :
    (scoreScan active row is).value = (ArrayCompositeAlgorithm.scoreScan active row is).1 := by
  induction is with
  | nil => rfl
  | cons i is ih => simp [scoreScan, ArrayCompositeAlgorithm.scoreScan, ih]

theorem scoreScan_sites {I : ℕ} (active : Flags I) (row : Counts I)
    (is : List (Fin I)) :
    (scoreScan active row is).sites = 6 * is.length + 1 := by
  induction is with
  | nil => rfl
  | cons i is ih => simp [scoreScan, ih]; omega

/-- The bounded index list is generated once, and its construction is charged. -/
def score {I : ℕ} (active : Flags I) (row : Counts I) : Result ℕ :=
  let out := scoreScan active row (List.finRange I)
  ⟨out.value, out.sites + 4 * I + 1⟩

theorem score_value {I : ℕ} (active : Flags I) (row : Counts I) :
    (score active row).value = ArrayCompositeAlgorithm.score active row := by
  simp [score, ArrayCompositeAlgorithm.score, scoreScan_value]

theorem score_sites {I : ℕ} (active : Flags I) (row : Counts I) :
    (score active row).sites = 10 * I + 2 := by
  simp [score, scoreScan_sites]; omega

/-- The per-cell computations have already executed into a stored vector.
This scan reads their counters and charges its own bounded traversal. -/
def scanSites {n : ℕ} {α : Type*} (stored : Vector (Result α) n) : List (Fin n) → ℕ
  | [] => 1
  | i :: is => (stored.get i).sites + scanSites stored is + 6

theorem scanSites_le {n B : ℕ} {α : Type*} (stored : Vector (Result α) n)
    (h : ∀ i, (stored.get i).sites   ≤   B) (is : List (Fin n)) :
    scanSites stored is   ≤   (B + 6) * is.length + 1 := by
  induction is with
  | nil => simp [scanSites]
  | cons i is ih =>
    have hi := h i
    simp only [scanSites, List.length_cons]
    nlinarith

/-- `f` is invoked once per output position by the first eager vector build.
The two subsequent passes only read this stored vector. -/
def tabulate {n : ℕ} {α : Type*} (f : Fin n → Result α) : Result (Vector α n) :=
  let stored := Vector.ofFn f
  let values := stored.map Result.value
  let total := scanSites stored (List.finRange n)
  ⟨values, total + 7 * n + 1⟩

theorem tabulate_value {n : ℕ} {α : Type*} (f : Fin n → Result α) :
    (tabulate f).value = Vector.ofFn (fun i => (f i).value) := by
  apply Vector.ext
  intro i hi
  simp [tabulate]

theorem tabulate_sites_le {n B : ℕ} {α : Type*} (f : Fin n → Result α)
    (h : ∀ i, (f i).sites   ≤   B) :
    (tabulate f).sites   ≤   n * (B + 13) + 2 := by
  have hs := scanSites_le (Vector.ofFn f) (by simpa using h) (List.finRange n)
  simp only [List.length_finRange] at hs
  change scanSites (Vector.ofFn f) (List.finRange n) + 7*n+1   ≤   _
  nlinarith

/-- Scores are fully stored before any argmin scan. -/
def scores {P I : ℕ} (active : Flags I) (rows : Tables P I) : Result (Counts P) :=
  tabulate (fun p =>
    let row := rows.get p
    let out := score active row
    ⟨out.value, out.sites + 1⟩)

theorem scores_value {P I : ℕ} (active : Flags I) (rows : Tables P I) :
    (scores active rows).value = ArrayCompositeAlgorithm.scores active rows := by
  rw [scores, tabulate_value]
  apply Vector.ext
  intro i hi
  simp [ArrayCompositeAlgorithm.scores, score_value]

theorem scores_sites_le {P I : ℕ} (active : Flags I) (rows : Tables P I) :
    (scores active rows).sites   ≤   P * (10*I+16) + 2 := by
  apply tabulate_sites_le
  intro p
  simp [score_sites]

/-- An actual filter loop; eligibility is read once per index. -/
def filterIndices {P : ℕ} (remaining : Flags P) : List (Fin P) → Result (List (Fin P))
  | [] => ⟨[], 1⟩
  | p :: ps =>
    let tail := filterIndices remaining ps
    let keep := remaining.get p
    ⟨if keep then p :: tail.value else tail.value, tail.sites + 4⟩

theorem filterIndices_value {P : ℕ} (remaining : Flags P) (ps : List (Fin P)) :
    (filterIndices remaining ps).value = ps.filter (fun p => remaining.get p) := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simp only [filterIndices, List.filter_cons]
    cases remaining.get p <;> simp [ih]

theorem filterIndices_sites {P : ℕ} (remaining : Flags P) (ps : List (Fin P)) :
    (filterIndices remaining ps).sites = 4*ps.length+1 := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [filterIndices, ih]; omega

def indices {P : ℕ} (remaining : Flags P) : Result (List (Fin P)) :=
  let out := filterIndices remaining (List.finRange P)
  ⟨out.value, out.sites + 4*P+1⟩

theorem indices_value {P : ℕ} (remaining : Flags P) :
    (indices remaining).value = ArrayCompositeAlgorithm.indices remaining := by
  simp [indices, ArrayCompositeAlgorithm.indices, filterIndices_value]

theorem indices_sites {P : ℕ} (remaining : Flags P) :
    (indices remaining).sites = 8*P+2 := by
  simp [indices, filterIndices_sites]; omega

theorem indices_length_le {P : ℕ} (remaining : Flags P) :
    (indices remaining).value.length   ≤   P := by
  rw [indices_value]
  simpa [ArrayCompositeAlgorithm.indices] using
    List.length_filter_le (fun p => remaining.get p) (List.finRange P)

/-- First-tie argmin over cached scalar values, sharing the recursive result. -/
def best {P : ℕ} (values : Counts P) : List (Fin P) → Result (Option (Fin P))
  | [] => ⟨none, 1⟩
  | p :: ps =>
    let tail := best values ps
    match tail.value with
    | none => ⟨some p, tail.sites + 6⟩
    | some q =>
      let vp := values.get p
      let vq := values.get q
      ⟨some (if vp   ≤   vq then p else q), tail.sites + 6⟩

theorem best_value {P : ℕ} (values : Counts P) (ps : List (Fin P)) :
    (best values ps).value = ArrayCompositeAlgorithm.best values ps := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simp only [best, ArrayCompositeAlgorithm.best]
    rw [← ih]
    cases (best values ps).value <;> rfl

theorem best_sites {P : ℕ} (values : Counts P) (ps : List (Fin P)) :
    (best values ps).sites = 6*ps.length+1 := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simp only [best, List.length_cons]
    cases (best values ps).value <;> simp [ih] <;> omega

def choose {P : ℕ} (remaining : Flags P) (values : Counts P) : Result (Option (Fin P)) :=
  let eligible := indices remaining
  let minimum := best values eligible.value
  ⟨minimum.value, eligible.sites + minimum.sites + 1⟩

theorem choose_value {P : ℕ} (remaining : Flags P) (values : Counts P) :
    (choose remaining values).value = ArrayCompositeAlgorithm.choose remaining values := by
  simp [choose, ArrayCompositeAlgorithm.choose, best_value, indices_value]

theorem choose_sites_le {P : ℕ} (remaining : Flags P) (values : Counts P) :
    (choose remaining values).sites   ≤   14*P+4 := by
  have hl := indices_length_le remaining
  simp only [choose, indices_sites, best_sites]
  omega



open CountedArrayComposite (Oracle Table Cache Call)

/-- Output slots are materialized; only this pass invokes the producer. -/
def evaluateOnce {P I : ℕ} {Payload : Type*} (O : Oracle I Payload)
    (active : Flags I) (primes : Counts P) (remaining : Flags P)
    (selected : List ℕ) : Result (Cache P I Payload) :=
  tabulate (fun p =>
    let eligible := remaining.get p
    if eligible then
      let prime := primes.get p
      let produced := O.table selected prime active
      ⟨some produced, 5⟩
    else ⟨none, 3⟩)

theorem evaluateOnce_value {P I : ℕ} {Payload : Type*} (O : Oracle I Payload)
    (active : Flags I) (primes : Counts P) (remaining : Flags P) (selected : List ℕ) :
    (evaluateOnce O active primes remaining selected).value =
      CountedArrayComposite.evaluateOnce O active primes remaining selected := by
  rw [evaluateOnce, tabulate_value]
  unfold CountedArrayComposite.evaluateOnce
  congr 1
  funext p
  cases remaining.get p <;> simp

theorem evaluateOnce_sites_le {P I : ℕ} {Payload : Type*} (O : Oracle I Payload)
    (active : Flags I) (primes : Counts P) (remaining : Flags P) (selected : List ℕ) :
    (evaluateOnce O active primes remaining selected).sites   ≤   18*P+2 := by
  have h := tabulate_sites_le (B:=5) (fun p : Fin P =>
    if remaining.get p then ⟨some (O.table selected (primes.get p) active),5⟩
    else (⟨none,3⟩ : Result (Option (Table I Payload)))) (by intro p; split <;> simp)
  simpa [evaluateOnce,Nat.mul_comm] using h

/-- Empty rows are explicitly zero-filled; successful rows retain a reference
into the actual producer slot. -/
def cacheRows {P I : ℕ} {Payload : Type*} (cache : Cache P I Payload) :
    Result (Tables P I) :=
  tabulate (fun p => match cache.get p with
    | none => ⟨Vector.replicate I 0, I+3⟩
    | some result => ⟨result.counts, 3⟩)

theorem cacheRows_value {P I : ℕ} {Payload : Type*} (cache : Cache P I Payload) :
    (cacheRows cache).value = cache.rows := by
  rw [cacheRows, tabulate_value]
  unfold CountedArrayComposite.Cache.rows
  congr 1
  funext p
  cases cache.get p <;> rfl

theorem cacheRows_sites_le {P I : ℕ} {Payload : Type*} (cache : Cache P I Payload) :
    (cacheRows cache).sites   ≤   P*(I+16)+2 := by
  apply tabulate_sites_le
  intro p
  split <;> simp

/-- The retained call stores the table payload already in the cache. -/
def cacheCallsFrom {P I : ℕ} {Payload : Type*} (cache : Cache P I Payload)
    (active : Flags I) (primes : Counts P) (selected : List ℕ) :
    List (Fin P) → Result (List (Call I Payload))
  | [] => ⟨[],1⟩
  | p::ps =>
    let tail := cacheCallsFrom cache active primes selected ps
    match cache.get p with
    | none => ⟨tail.value,tail.sites+5⟩
    | some table =>
      let prime := primes.get p
      ⟨⟨⟨selected,prime,active⟩,table⟩::tail.value,tail.sites+5⟩

theorem cacheCallsFrom_value {P I : ℕ} {Payload : Type*} (cache : Cache P I Payload)
    (active : Flags I) (primes : Counts P) (selected : List ℕ) (ps : List (Fin P)) :
    (cacheCallsFrom cache active primes selected ps).value =
      cache.callsFrom active primes selected ps := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simp only [cacheCallsFrom, CountedArrayComposite.Cache.callsFrom]
    cases cache.get p <;> simp [ih]

theorem cacheCallsFrom_sites {P I : ℕ} {Payload : Type*} (cache : Cache P I Payload)
    (active : Flags I) (primes : Counts P) (selected : List ℕ) (ps : List (Fin P)) :
    (cacheCallsFrom cache active primes selected ps).sites = 5*ps.length+1 := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simp only [cacheCallsFrom]
    cases cache.get p <;> simp [ih] <;> omega

theorem cacheCallsFrom_length_le {P I : ℕ} {Payload : Type*} (cache : Cache P I Payload)
    (active : Flags I) (primes : Counts P) (selected : List ℕ) (ps : List (Fin P)) :
    (cacheCallsFrom cache active primes selected ps).value.length   ≤   ps.length := by
  induction ps with
  | nil => simp [cacheCallsFrom]
  | cons p ps ih =>
    simp only [cacheCallsFrom]
    cases cache.get p <;> simp <;> omega

def cacheCalls {P I : ℕ} {Payload : Type*} (cache : Cache P I Payload)
    (active : Flags I) (primes : Counts P) (selected : List ℕ) : Result (List (Call I Payload)) :=
  let out := cacheCallsFrom cache active primes selected (List.finRange P)
  ⟨out.value,out.sites+4*P+1⟩

theorem cacheCalls_value {P I : ℕ} {Payload : Type*} (cache : Cache P I Payload)
    (active : Flags I) (primes : Counts P) (selected : List ℕ) :
    (cacheCalls cache active primes selected).value = cache.calls active primes selected := by
  simp [cacheCalls,cacheCallsFrom_value,CountedArrayComposite.Cache.calls]

theorem cacheCalls_sites {P I : ℕ} {Payload : Type*} (cache : Cache P I Payload)
    (active : Flags I) (primes : Counts P) (selected : List ℕ) :
    (cacheCalls cache active primes selected).sites = 9*P+2 := by
  simp [cacheCalls,cacheCallsFrom_sites];omega

theorem cacheCalls_length_le {P I : ℕ} {Payload : Type*} (cache : Cache P I Payload)
    (active : Flags I) (primes : Counts P) (selected : List ℕ) :
    (cacheCalls cache active primes selected).value.length   ≤   P := by
  exact (cacheCallsFrom_length_le cache active primes selected (List.finRange P)).trans_eq
    (List.length_finRange)

/-- Traverses only the retained prefix; the tail list is shared. -/
def append {α : Type*} : List α → List α → Result (List α)
  | [],ys => ⟨ys,1⟩
  | x::xs,ys =>
    let tail := append xs ys
    ⟨x::tail.value,tail.sites+3⟩

theorem append_value {α : Type*} (xs ys : List α) :
    (append xs ys).value = xs++ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [append,ih]

theorem append_sites {α : Type*} (xs ys : List α) :
    (append xs ys).sites = 3*xs.length+1 := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [append,ih];omega

/-- The work fields are read from retained results; no backend is invoked. -/
def sumWork {I : ℕ} {Payload : Type*} : List (Call I Payload) → Result ℕ
  | [] => ⟨0,1⟩
  | call::calls =>
    let tail := sumWork calls
    let work := call.result.work
    ⟨work+tail.value,tail.sites+4⟩

theorem sumWork_value {I : ℕ} {Payload : Type*} (calls : List (Call I Payload)) :
    (sumWork calls).value = CountedArrayComposite.workSum calls := by
  induction calls with
  | nil => rfl
  | cons call calls ih => simp [sumWork,CountedArrayComposite.workSum,ih]

theorem sumWork_sites {I : ℕ} {Payload : Type*} (calls : List (Call I Payload)) :
    (sumWork calls).sites = 4*calls.length+1 := by
  induction calls with
  | nil => rfl
  | cons call calls ih => simp [sumWork,ih];omega

/-- One indexed write in the array IR. -/
def put {n : ℕ} (flags : Flags n) (i : Fin n) (b : Bool) : Result (Flags n) :=
  ⟨flags.set i.val b i.isLt,2⟩

theorem put_value {n : ℕ} (flags : Flags n) (i : Fin n) (b : Bool) :
    (put flags i b).value = ArrayCompositeAlgorithm.put flags i b := rfl

/-- Preserve a selected count row before the table storage is reused. -/
def copyRow {I : ℕ} (row : Counts I) : Result (Counts I) :=
  tabulate (fun i => ⟨row.get i,1⟩)

theorem copyRow_value {I : ℕ} (row : Counts I) : (copyRow row).value=row := by
  rw [copyRow,tabulate_value]
  apply Vector.ext
  intro i hi
  simp only [Vector.getElem_ofFn]
  rfl

theorem copyRow_sites_le {I : ℕ} (row : Counts I) :
    (copyRow row).sites  ≤  14*I+2 := by
  simpa [copyRow,Nat.mul_comm] using
    (tabulate_sites_le (B:=1) (fun i => (⟨row.get i,1⟩ : Result ℕ)) (by intro i; rfl))

/-- Products and the strict comparison are evaluated before the flag write. -/
def affirmative {I : ℕ} (active : Flags I) (base mu : Counts I) (lam m : ℕ) :
    Result (Flags I) :=
  tabulate (fun i =>
    let a := active.get i
    let b := base.get i
    let v := mu.get i
    let lhs := lam*b
    let rhs := m*v
    let test := decide (lhs < rhs)
    ⟨a && test,8⟩)

theorem affirmative_value {I : ℕ} (active : Flags I) (base mu : Counts I) (lam m : ℕ) :
    (affirmative active base mu lam m).value =
      ArrayCompositeAlgorithm.affirmative active base mu lam m := by
  rw [affirmative,tabulate_value]
  rfl

theorem affirmative_sites_le {I : ℕ} (active : Flags I) (base mu : Counts I) (lam m : ℕ) :
    (affirmative active base mu lam m).sites  ≤  21*I+2 := by
  simpa [affirmative,Nat.mul_comm] using
    (tabulate_sites_le (B:=8) (fun i=>
      (⟨active.get i && decide (lam*base.get i < m*mu.get i),8⟩ : Result Bool))
      (by intro i;rfl))

/-- Marking is an actual sequential indexed-write pass. -/
def markScan {I Q : ℕ} (owner : Owners I Q) (yes : Flags I) :
    Flags Q → List (Fin I) → Result (Flags Q)
  | marked,[] => ⟨marked,1⟩
  | marked,i::is =>
    let flag := yes.get i
    let updated := if flag then put marked (owner.get i) true else ⟨marked,2⟩
    let tail := markScan owner yes updated.value is
    ⟨tail.value,updated.sites+tail.sites+5⟩

theorem markScan_value {I Q : ℕ} (owner : Owners I Q) (yes : Flags I)
    (marked : Flags Q) (is : List (Fin I)) :
    (markScan owner yes marked is).value = ArrayCompositeAlgorithm.markScan owner yes marked is := by
  induction is generalizing marked with
  | nil => rfl
  | cons i is ih =>
    simp only [markScan,ArrayCompositeAlgorithm.markScan]
    cases h : yes.get i <;> simp [put_value,ih]

theorem markScan_sites {I Q : ℕ} (owner : Owners I Q) (yes : Flags I)
    (marked : Flags Q) (is : List (Fin I)) :
    (markScan owner yes marked is).sites = 7*is.length+1 := by
  induction is generalizing marked with
  | nil => rfl
  | cons i is ih =>
    simp only [markScan]
    cases h : yes.get i <;> simp [put,ih] <;> omega

def mark {I Q : ℕ} (owner : Owners I Q) (yes : Flags I) (marked : Flags Q) :
    Result (Flags Q) :=
  let out := markScan owner yes marked (List.finRange I)
  ⟨out.value,out.sites+4*I+1⟩

theorem mark_value {I Q : ℕ} (owner : Owners I Q) (yes : Flags I) (marked : Flags Q) :
    (mark owner yes marked).value=ArrayCompositeAlgorithm.mark owner yes marked := by
  simp [mark,ArrayCompositeAlgorithm.mark,markScan_value]

theorem mark_sites {I Q : ℕ} (owner : Owners I Q) (yes : Flags I) (marked : Flags Q) :
    (mark owner yes marked).sites=11*I+2 := by
  simp [mark,markScan_sites];omega

/-- All pair marks exist before the survivor pass starts. -/
def retain {I Q : ℕ} (owner : Owners I Q) (active : Flags I) (marked : Flags Q)
    (base mu : Counts I) (lam m : ℕ) : Result (Flags I) :=
  tabulate (fun i =>
    let a := active.get i
    let v := mu.get i
    let b := base.get i
    let q := owner.get i
    let solved := marked.get q
    let lhs := m*v
    let rhs := lam*b
    let positive := decide (v≠0)
    let bounded := decide (lhs  ≤  rhs)
    ⟨a && positive && bounded && !solved,14⟩)

theorem retain_value {I Q : ℕ} (owner : Owners I Q) (active : Flags I) (marked : Flags Q)
    (base mu : Counts I) (lam m : ℕ) :
    (retain owner active marked base mu lam m).value =
      ArrayCompositeAlgorithm.retain owner active marked base mu lam m := by
  rw [retain,tabulate_value]
  rfl

theorem retain_sites_le {I Q : ℕ} (owner : Owners I Q) (active : Flags I) (marked : Flags Q)
    (base mu : Counts I) (lam m : ℕ) :
    (retain owner active marked base mu lam m).sites  ≤  27*I+2 := by
  have h := tabulate_sites_le (B:=14)
    (fun i => (⟨active.get i && decide (mu.get i≠0) &&
      decide (m*mu.get i  ≤  lam*base.get i) && !(marked.get (owner.get i)),14⟩ : Result Bool))
    (by intro i; rfl)
  simpa [retain,Nat.mul_comm] using h

def finish {I Q : ℕ} (owner : Owners I Q) (active : Flags I) (marked : Flags Q)
    (base mu : Counts I) (lam m : ℕ) : Result (ArrayCompositeAlgorithm.Result I Q) :=
  let yes := affirmative active base mu lam m
  let marks := mark owner yes.value marked
  let survivors := retain owner active marks.value base mu lam m
  ⟨⟨survivors.value,marks.value⟩,yes.sites+marks.sites+survivors.sites+3⟩

theorem finish_value {I Q : ℕ} (owner : Owners I Q) (active : Flags I) (marked : Flags Q)
    (base mu : Counts I) (lam m : ℕ) :
    (finish owner active marked base mu lam m).value =
      ArrayCompositeAlgorithm.finish owner active marked base mu lam m := by
  simp [finish,ArrayCompositeAlgorithm.finish,affirmative_value,mark_value,retain_value]

theorem finish_sites_le {I Q : ℕ} (owner : Owners I Q) (active : Flags I) (marked : Flags Q)
    (base mu : Counts I) (lam m : ℕ) :
    (finish owner active marked base mu lam m).sites  ≤  59*I+9 := by
  have h₁:=affirmative_sites_le active base mu lam m
  have h₂:=mark_sites owner (affirmative active base mu lam m).value marked
  have h₃:=retain_sites_le owner active
    (mark owner (affirmative active base mu lam m).value marked).value base mu lam m
  dsimp only [finish]
  omega

/-- Read each stored row and scalar once; eager tabulation materializes the
joint results and counts its projection, writes, and counter scan. -/
def columnExec {P I : ℕ} (rows : Tables P I) (i : Fin I) : Result (Counts P) :=
  tabulate (fun p =>
    let row := rows.get p
    let entry := row.get i
    ⟨entry,2⟩)

@[simp] theorem columnExec_value {P I : ℕ} (rows : Tables P I) (i : Fin I) :
    (columnExec rows i).value = ArrayCompositeAlgorithm.column rows i := by
  rw [columnExec, tabulate_value]
  rfl

theorem columnExec_sites {P I : ℕ} (rows : Tables P I) (i : Fin I) :
    (columnExec rows i).sites   ≤   15*P+2 := by
  have h := tabulate_sites_le (n := P) (B := 2)
    (fun p : Fin P => (⟨(rows.get p).get i,2⟩ : Result ℕ)) (by intro p; rfl)
  simpa only [columnExec, Nat.mul_comm] using h

/-- Form one actual column, scan cached scalars, then read the chosen scalar. -/
def minimumCell {P I : ℕ} (rows : Tables P I) (eligible : List (Fin P)) (i : Fin I) : Result ℕ :=
  let values := columnExec rows i
  let chosen := best values.value eligible
  ⟨match chosen.value with | none => 0 | some p => values.value.get p,
    values.sites+chosen.sites+3⟩

theorem minimumCell_value {P I : ℕ} (rows : Tables P I) (eligible : List (Fin P)) (i : Fin I) :
    (minimumCell rows eligible i).value =
      match ArrayCompositeAlgorithm.best (ArrayCompositeAlgorithm.column rows i) eligible with
      | none => 0 | some p => (rows.get p).get i := by
  simp [minimumCell, best_value]

theorem minimumCell_sites {P I : ℕ} (rows : Tables P I) (eligible : List (Fin P))
    (he : eligible.length   ≤   P) (i : Fin I) :
    (minimumCell rows eligible i).sites   ≤   21*P+6 := by
  have hb := best_sites (columnExec rows i).value eligible
  have hc := columnExec_sites rows i
  simp only [minimumCell]
  nlinarith

/-- Generate eligibility once. All per-incidence column/minimum executions
are stored before their values and scalar-array counters are projected. -/
def minimaExec {P I : ℕ} (rows : Tables P I) (remaining : Flags P) : Result (Counts I) :=
  let eligible := indices remaining
  let output := tabulate (minimumCell rows eligible.value)
  ⟨output.value,eligible.sites+output.sites+1⟩

@[simp] theorem minimaExec_value {P I : ℕ} (rows : Tables P I) (remaining : Flags P) :
    (minimaExec rows remaining).value = ArrayCompositeAlgorithm.minima rows remaining := by
  simp only [minimaExec, tabulate_value, ArrayCompositeAlgorithm.minima]
  congr 1
  funext i
  rw [minimumCell_value, indices_value]
  rfl

theorem minimaExec_sites {P I : ℕ} (rows : Tables P I) (remaining : Flags P) :
    (minimaExec rows remaining).sites   ≤   64*(P*I+P+I+1) := by
  have ho := tabulate_sites_le (minimumCell rows (indices remaining).value)
    (fun i => minimumCell_sites rows _ (indices_length_le remaining) i)
  have hi := indices_sites remaining
  simp only [minimaExec]
  nlinarith

/-- Joint list-length traversal; eligibility is not regenerated. -/
def lengthExec {A : Type*} : List A → Result ℕ
  | [] => ⟨0,1⟩
  | _::xs => let tail := lengthExec xs; ⟨tail.value+1,tail.sites+3⟩

@[simp] theorem lengthExec_value {A : Type*} (xs : List A) : (lengthExec xs).value = xs.length := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp [lengthExec, ih]

@[simp] theorem lengthExec_sites {A : Type*} (xs : List A) : (lengthExec xs).sites = 3*xs.length+1 := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp [lengthExec, ih]; omega

def populationExec {P : ℕ} (remaining : Flags P) : Result ℕ :=
  let eligible := indices remaining
  let count := lengthExec eligible.value
  ⟨count.value,eligible.sites+count.sites+1⟩

@[simp] theorem populationExec_value {P : ℕ} (remaining : Flags P) :
    (populationExec remaining).value = ArrayCompositeAlgorithm.population remaining := by
  simp [populationExec, ArrayCompositeAlgorithm.population, indices_value]

theorem populationExec_sites {P : ℕ} (remaining : Flags P) :
    (populationExec remaining).sites   ≤   16*(P+1) := by
  have hl := indices_length_le remaining
  simp only [populationExec, lengthExec_sites, indices_sites]
  omega


/-- One greedy loop body. Producer returns are stored before every controller
pass, and the selected row is copied before the next loop body. -/
def greedyExec {P I : ℕ} {Payload : Type*} (O : Oracle I Payload)
    (active : Flags I) (primes : Counts P) :
    ℕ → ℕ → Flags P → Counts I → List ℕ → Result (CountedArrayComposite.GreedyResult P I Payload)
  | 0,d,remaining,base,selected => ⟨⟨d,remaining,base,selected,[],0,0⟩,1⟩
  | k+1,d,remaining,base,selected =>
    let cache := evaluateOnce O active primes remaining selected
    let rows := cacheRows cache.value
    let values := scores active rows.value
    let chosen := choose remaining values.value
    let batchSites := cache.sites+rows.sites+values.sites+chosen.sites+4
    match chosen.value with
    | none => ⟨⟨d,remaining,base,selected,[],0,CountedArrayComposite.batchVisits P I⟩,
        batchSites+1⟩
    | some p =>
      let calls := cacheCalls cache.value active primes selected
      let prime := primes.get p
      let remaining' := put remaining p false
      let base' := copyRow (rows.value.get p)
      let selected' := append selected [prime]
      let tail := greedyExec O active primes k (d*prime) remaining'.value base'.value selected'.value
      let history := append calls.value tail.value.calls
      let work := sumWork calls.value
      ⟨{ tail.value with
         calls := history.value
         backendWork := work.value+tail.value.backendWork
         controllerVisits := CountedArrayComposite.batchVisits P I+tail.value.controllerVisits },
       batchSites+calls.sites+remaining'.sites+base'.sites+selected'.sites+
         tail.sites+history.sites+work.sites+12⟩

theorem greedyExec_value {P I : ℕ} {Payload : Type*} (O : Oracle I Payload)
    (active : Flags I) (primes : Counts P) (k d : ℕ) (remaining : Flags P)
    (base : Counts I) (selected : List ℕ) :
    (greedyExec O active primes k d remaining base selected).value =
      CountedArrayComposite.greedy O active primes k d remaining base selected := by
  induction k generalizing d remaining base selected with
  | zero => rfl
  | succ k ih =>
    simp only [greedyExec,CountedArrayComposite.greedy,evaluateOnce_value,cacheRows_value,
      scores_value,choose_value,put_value,copyRow_value,append_value,sumWork_value,ih]
    split
    · rename_i h
      rw [h]
    · rename_i p h
      rw [h]
      simp only [cacheCalls_value]

/-- Counts the chosen prefix, not the potentially much larger accumulated tail. -/
theorem greedyExec_calls_length {P I : ℕ} {Payload : Type*} (O : Oracle I Payload)
    (active : Flags I) (primes : Counts P) (k d : ℕ) (remaining : Flags P)
    (base : Counts I) (selected : List ℕ) :
    (greedyExec O active primes k d remaining base selected).value.calls.length  ≤  k*P := by
  rw [greedyExec_value]
  have he := CountedArrayComposite.greedy_erases O active primes k d remaining base selected
  have hl := congrArg (fun out=>out.calls.length) he
  simp only [CountedArrayComposite.GreedyResult.erase,CountedArrayComposite.eraseCalls,
    List.length_map] at hl
  rw [hl]
  exact ArrayCompositeAlgorithm.greedy_calls_bound O.erase active primes k d remaining base selected

theorem greedyExec_selected_length {P I : ℕ} {Payload : Type*} (O : Oracle I Payload)
    (active : Flags I) (primes : Counts P) (k d : ℕ) (remaining : Flags P)
    (base : Counts I) (selected : List ℕ) :
    (greedyExec O active primes k d remaining base selected).value.selected.length  ≤  selected.length+k := by
  rw [greedyExec_value]
  have he := CountedArrayComposite.greedy_erases O active primes k d remaining base selected
  have hl := congrArg (fun out=>out.selected.length) he
  simp only [CountedArrayComposite.GreedyResult.erase] at hl
  rw [hl]
  exact (CountedArrayComposite.array_greedy_history_lengths O.erase active primes k d
    remaining base selected).1

/-- The integer `R` bounds the selected-prefix length plus all remaining rounds. -/
def denseSize (P I : ℕ) : ℕ := P*I+P+I+1

def roundUnit (P I R : ℕ) : ℕ := 256*(R+1)*denseSize P I

theorem greedyExec_sites_le {P I R : ℕ} {Payload : Type*} (O : Oracle I Payload)
    (active : Flags I) (primes : Counts P) (k d : ℕ) (remaining : Flags P)
    (base : Counts I) (selected : List ℕ) (hR : selected.length+k  ≤  R) :
    (greedyExec O active primes k d remaining base selected).sites  ≤  k*roundUnit P I R+1 := by
  induction k generalizing d remaining base selected with
  | zero => simp [greedyExec]
  | succ k ih =>
    have hsize : 1  ≤  denseSize P I := by simp [denseSize]
    have hmul : R  ≤  R*denseSize P I := by nlinarith
    have hunit : 256*(denseSize P I+R)  ≤  roundUnit P I R := by
      dsimp [roundUnit]
      nlinarith
    have hsel : selected.length  ≤  R := by omega
    have hc := evaluateOnce_sites_le O active primes remaining selected
    have hr := cacheRows_sites_le (evaluateOnce O active primes remaining selected).value
    have hs := scores_sites_le active (cacheRows (evaluateOnce O active primes remaining selected).value).value
    have hq := choose_sites_le remaining
      (scores active (cacheRows (evaluateOnce O active primes remaining selected).value).value).value
    simp only [greedyExec]
    split
    · dsimp only
      dsimp [denseSize] at hunit
      nlinarith
    · rename_i p hp
      have hcalls := cacheCalls_sites (evaluateOnce O active primes remaining selected).value active primes selected
      have hlen := cacheCalls_length_le (evaluateOnce O active primes remaining selected).value active primes selected
      have hb := copyRow_sites_le
        ((cacheRows (evaluateOnce O active primes remaining selected).value).value.get p)
      have ht := ih (d*primes.get p) (put remaining p false).value
        (copyRow ((cacheRows (evaluateOnce O active primes remaining selected).value).value.get p)).value
        (append selected [primes.get p]).value (by
          simp only [append_value,List.length_append,List.length_singleton]
          omega)
      simp only [put,append_sites,sumWork_sites]
      dsimp [denseSize] at hunit
      have hlocal :
          (evaluateOnce O active primes remaining selected).sites+
          (cacheRows (evaluateOnce O active primes remaining selected).value).sites+
          (scores active (cacheRows (evaluateOnce O active primes remaining selected).value).value).sites+
          (choose remaining (scores active (cacheRows (evaluateOnce O active primes remaining selected).value).value).value).sites+
          4+(cacheCalls (evaluateOnce O active primes remaining selected).value active primes selected).sites+
          2+(copyRow ((cacheRows (evaluateOnce O active primes remaining selected).value).value.get p)).sites+
          (3*selected.length+1)+
          (3*(cacheCalls (evaluateOnce O active primes remaining selected).value active primes selected).value.length+1)+
          (4*(cacheCalls (evaluateOnce O active primes remaining selected).value active primes selected).value.length+1)+12
           ≤  roundUnit P I R := by
        ring_nf at hr hs hunit ⊢
        omega
      simp only [put] at ht
      simp only [Nat.add_mul,Nat.one_mul]
      omega

/-- The final batch, minima, certification, and pair/survivor writes are
jointly executed after the greedy prefix. -/
def stageExec {P I Q : ℕ} {Payload : Type*} (O : Oracle I Payload) (owner : Owners I Q)
    (primes : Counts P) (active : Flags I) (marked : Flags Q) (blockSizes : Counts I)
    (remaining : Flags P) (k lam : ℕ) : Result (CountedArrayComposite.StageResult P I Q Payload) :=
  let chosen := greedyExec O active primes k 1 remaining blockSizes []
  let cache := evaluateOnce O active primes chosen.value.remaining chosen.value.selected
  let rows := cacheRows cache.value
  let mu := minimaExec rows.value chosen.value.remaining
  let population := populationExec chosen.value.remaining
  let out := finish owner active marked chosen.value.base mu.value lam population.value
  let calls := cacheCalls cache.value active primes chosen.value.selected
  let history := append chosen.value.calls calls.value
  let work := sumWork calls.value
  ⟨⟨out.value.active,out.value.marked,chosen.value.selected,history.value,
      chosen.value.backendWork+work.value,
      chosen.value.controllerVisits+CountedArrayComposite.finalVisits P I⟩,
    chosen.sites+cache.sites+rows.sites+mu.sites+population.sites+out.sites+
      calls.sites+history.sites+work.sites+12⟩

theorem stageExec_value {P I Q : ℕ} {Payload : Type*} (O : Oracle I Payload) (owner : Owners I Q)
    (primes : Counts P) (active : Flags I) (marked : Flags Q) (blockSizes : Counts I)
    (remaining : Flags P) (k lam : ℕ) :
    (stageExec O owner primes active marked blockSizes remaining k lam).value =
      CountedArrayComposite.stage O owner primes active marked blockSizes remaining k lam := by
  simp only [stageExec,CountedArrayComposite.stage,greedyExec_value,evaluateOnce_value,
    cacheRows_value,minimaExec_value,populationExec_value,finish_value,cacheCalls_value,
    append_value,sumWork_value]

theorem stageExec_calls_length {P I Q : ℕ} {Payload : Type*} (O : Oracle I Payload) (owner : Owners I Q)
    (primes : Counts P) (active : Flags I) (marked : Flags Q) (blockSizes : Counts I)
    (remaining : Flags P) (k lam : ℕ) :
    (stageExec O owner primes active marked blockSizes remaining k lam).value.calls.length  ≤  (k+1)*P := by
  rw [stageExec_value]
  have he := CountedArrayComposite.stage_erases O owner primes active marked blockSizes remaining k lam
  have hl := congrArg (fun out=>out.calls.length) he
  simp only [CountedArrayComposite.StageResult.erase,CountedArrayComposite.eraseCalls,List.length_map] at hl
  rw [hl]
  exact ArrayCompositeAlgorithm.stage_calls_bound O.erase owner primes active marked blockSizes remaining k lam

theorem stageExec_sites_le {P I Q : ℕ} {Payload : Type*} (O : Oracle I Payload) (owner : Owners I Q)
    (primes : Counts P) (active : Flags I) (marked : Flags Q) (blockSizes : Counts I)
    (remaining : Flags P) (k lam : ℕ) :
    (stageExec O owner primes active marked blockSizes remaining k lam).sites  ≤
      (k+1)*roundUnit P I k+1 := by
  let chosen := greedyExec O active primes k 1 remaining blockSizes []
  let cache := evaluateOnce O active primes chosen.value.remaining chosen.value.selected
  let rows := cacheRows cache.value
  have hg := greedyExec_sites_le (R:=k) O active primes k 1 remaining blockSizes [] (by simp)
  have hc := evaluateOnce_sites_le O active primes chosen.value.remaining chosen.value.selected
  have hr := cacheRows_sites_le cache.value
  have hm := minimaExec_sites rows.value chosen.value.remaining
  have hp := populationExec_sites chosen.value.remaining
  have hf := finish_sites_le owner active marked chosen.value.base
    (minimaExec rows.value chosen.value.remaining).value lam (populationExec chosen.value.remaining).value
  have hcalls := cacheCalls_sites cache.value active primes chosen.value.selected
  have hlen := cacheCalls_length_le cache.value active primes chosen.value.selected
  have hhist := greedyExec_calls_length O active primes k 1 remaining blockSizes []
  have hsize : P  ≤  denseSize P I := by simp [denseSize];omega
  have hk : k*P  ≤  k*denseSize P I := Nat.mul_le_mul_left k hsize
  change chosen.sites ≤ _ at hg
  change chosen.value.calls.length ≤ _ at hhist
  change chosen.sites+cache.sites+rows.sites+
    (minimaExec rows.value chosen.value.remaining).sites+
    (populationExec chosen.value.remaining).sites+
    (finish owner active marked chosen.value.base (minimaExec rows.value chosen.value.remaining).value
      lam (populationExec chosen.value.remaining).value).sites+
    (cacheCalls cache.value active primes chosen.value.selected).sites+
    (append chosen.value.calls (cacheCalls cache.value active primes chosen.value.selected).value).sites+
    (sumWork (cacheCalls cache.value active primes chosen.value.selected).value).sites+12  ≤  _
  rw [append_sites,sumWork_sites]
  have hu : roundUnit P I k=256*(k+1)*denseSize P I := rfl
  dsimp [denseSize] at hm hsize hk hu
  nlinarith

/-- Restart calls retain all actual payloads. Appending a stage traverses
only that stage's bounded call prefix, never the accumulated tail. -/
def restartsExec {P I Q : ℕ} {Payload : Type*} (O : Oracle I Payload) (owner : Owners I Q)
    (primes : Counts P) (blockSizes : Counts I) (remaining : Flags P) (k lam : ℕ) :
    ℕ → Flags I → Flags Q → Result (CountedArrayComposite.StageResult P I Q Payload)
  | 0,active,marked => ⟨⟨active,marked,[],[],0,0⟩,1⟩
  | n+1,active,marked =>
    let one := stageExec O owner primes active marked blockSizes remaining k lam
    let tail := restartsExec O owner primes blockSizes remaining k lam n one.value.active one.value.marked
    let history := append one.value.calls tail.value.calls
    ⟨{tail.value with
       calls := history.value
       backendWork := one.value.backendWork+tail.value.backendWork
       controllerVisits := one.value.controllerVisits+tail.value.controllerVisits},
      one.sites+tail.sites+history.sites+5⟩

theorem restartsExec_value {P I Q : ℕ} {Payload : Type*} (O : Oracle I Payload) (owner : Owners I Q)
    (primes : Counts P) (blockSizes : Counts I) (remaining : Flags P) (k lam n : ℕ)
    (active : Flags I) (marked : Flags Q) :
    (restartsExec O owner primes blockSizes remaining k lam n active marked).value =
      CountedArrayComposite.restarts O owner primes blockSizes remaining k lam n active marked := by
  induction n generalizing active marked with
  | zero => rfl
  | succ n ih =>
    simp only [restartsExec,CountedArrayComposite.restarts,stageExec_value,append_value,ih]

/-- Explicit work valid also for zero dimensions; the added one accounts for
loop/control returns rather than hiding them in a zero scan allowance. -/
theorem restartsExec_sites_le {P I Q : ℕ} {Payload : Type*} (O : Oracle I Payload) (owner : Owners I Q)
    (primes : Counts P) (blockSizes : Counts I) (remaining : Flags P) (k lam n : ℕ)
    (active : Flags I) (marked : Flags Q) :
    (restartsExec O owner primes blockSizes remaining k lam n active marked).sites  ≤
      n*((k+2)*roundUnit P I k)+1 := by
  induction n generalizing active marked with
  | zero => simp [restartsExec]
  | succ n ih =>
    let one := stageExec O owner primes active marked blockSizes remaining k lam
    have hs := stageExec_sites_le O owner primes active marked blockSizes remaining k lam
    have hl := stageExec_calls_length O owner primes active marked blockSizes remaining k lam
    have ht := ih one.value.active one.value.marked
    change one.sites ≤ _ at hs
    change one.value.calls.length ≤ _ at hl
    have hsize : P+1  ≤  denseSize P I := by simp [denseSize];omega
    have hk := Nat.mul_le_mul_left (k+1) hsize
    change one.sites+
      (restartsExec O owner primes blockSizes remaining k lam n one.value.active one.value.marked).sites+
      (append one.value.calls
        (restartsExec O owner primes blockSizes remaining k lam n one.value.active one.value.marked).value.calls).sites+5  ≤  _
    rw [append_sites]
    have hu : roundUnit P I k=256*(k+1)*denseSize P I := rfl
    nlinarith

/-- Every restart contains its final dense pass, independently of which
selection branch was taken. -/
theorem restarts_visits_lower {P I Q : ℕ} {Payload : Type*} (O : Oracle I Payload)
    (owner : Owners I Q) (primes : Counts P) (blockSizes : Counts I) (remaining : Flags P)
    (k lam n : ℕ) (active : Flags I) (marked : Flags Q) :
    n*CountedArrayComposite.finalVisits P I  ≤
      (CountedArrayComposite.restarts O owner primes blockSizes remaining k lam n active marked).controllerVisits := by
  induction n generalizing active marked with
  | zero => simp [CountedArrayComposite.restarts]
  | succ n ih =>
    have ht := ih
      (CountedArrayComposite.stage O owner primes active marked blockSizes remaining k lam).active
      (CountedArrayComposite.stage O owner primes active marked blockSizes remaining k lam).marked
    simp only [CountedArrayComposite.restarts,CountedArrayComposite.stage]
    simp only [CountedArrayComposite.stage] at ht
    simp only [Nat.add_mul,Nat.one_mul]
    omega

/-- The previously declared visit allowance now bounds the counter of the
actual joint loops. Positivity excludes hiding return/control work in a zero
scan allowance; the zero-dimensional bound is `restartsExec_sites_le`. -/
theorem restartsExec_sites_by_visits {P I Q : ℕ} {Payload : Type*} (O : Oracle I Payload)
    (owner : Owners I Q) (primes : Counts P) (blockSizes : Counts I) (remaining : Flags P)
    (k lam n : ℕ) (active : Flags I) (marked : Flags Q) (hP : 0<P) :
    (restartsExec O owner primes blockSizes remaining k lam n active marked).sites  ≤
      256*(k+1)*(k+2)*
        (restartsExec O owner primes blockSizes remaining k lam n active marked).value.controllerVisits+1 := by
  have hv := restarts_visits_lower O owner primes blockSizes remaining k lam n active marked
  have hd : denseSize P I ≤ CountedArrayComposite.finalVisits P I := by
    dsimp [denseSize,CountedArrayComposite.finalVisits]
    ring_nf
    omega
  have hn : n*denseSize P I ≤
      (restartsExec O owner primes blockSizes remaining k lam n active marked).value.controllerVisits := by
    rw [restartsExec_value]
    exact (Nat.mul_le_mul_left n hd).trans hv
  calc
    _  ≤  n*((k+2)*roundUnit P I k)+1 := restartsExec_sites_le O owner primes blockSizes remaining k lam n active marked
    _ = 256*(k+1)*(k+2)*(n*denseSize P I)+1 := by dsimp [roundUnit];ring
    _  ≤  _ := Nat.add_le_add_right (Nat.mul_le_mul_left _ hn) 1

/-- The original count-table semantics and producer-return association are
inherited from exact erasure of the operational execution. -/
theorem restartsExec_retained_results {P I Q : ℕ} {Payload : Type*} (O : Oracle I Payload)
    (owner : Owners I Q) (primes : Counts P) (blockSizes : Counts I) (remaining : Flags P)
    (k lam n : ℕ) (active : Flags I) (marked : Flags Q) :
    ∀ call∈(restartsExec O owner primes blockSizes remaining k lam n active marked).value.calls,
      call.result=O.table call.factors.selected call.factors.candidate call.factors.active := by
  rw [restartsExec_value]
  exact CountedArrayComposite.restarts_retained_results O owner primes blockSizes remaining k lam n active marked

theorem restartsExec_backendWork {P I Q : ℕ} {Payload : Type*} (O : Oracle I Payload)
    (owner : Owners I Q) (primes : Counts P) (blockSizes : Counts I) (remaining : Flags P)
    (k lam n : ℕ) (active : Flags I) (marked : Flags Q) :
    (restartsExec O owner primes blockSizes remaining k lam n active marked).value.backendWork =
      CountedArrayComposite.workSum
        (restartsExec O owner primes blockSizes remaining k lam n active marked).value.calls := by
  rw [restartsExec_value]
  exact CountedArrayComposite.restarts_backendWork O owner primes blockSizes remaining k lam n active marked

/-- Explicit dense flag initialFlagsrs, charged separately from controller
passes. Owner/primes/block-size arrays are supplied by the reduction setup. -/
def initialFlags (P I Q : ℕ) : Result (Flags P × Flags I × Flags Q) :=
  let remaining := tabulate (fun _ : Fin P => (⟨true,1⟩ : Result Bool))
  let active := tabulate (fun _ : Fin I => (⟨true,1⟩ : Result Bool))
  let marked := tabulate (fun _ : Fin Q => (⟨false,1⟩ : Result Bool))
  ⟨(remaining.value,active.value,marked.value),remaining.sites+active.sites+marked.sites+3⟩

theorem initialFlags_value (P I Q : ℕ) : (initialFlags P I Q).value =
    (Vector.replicate P true,Vector.replicate I true,Vector.replicate Q false) := by
  have hc {n : ℕ} (b : Bool) : Vector.ofFn (fun _ : Fin n => b)=Vector.replicate n b := by
    apply Vector.ext
    intro i hi
    simp
  simp only [initialFlags,tabulate_value,hc]

theorem initialFlags_sites_le (P I Q : ℕ) : (initialFlags P I Q).sites ≤ 14*(P+I+Q)+9 := by
  have hp := tabulate_sites_le (B:=1) (fun _ : Fin P => (⟨true,1⟩ : Result Bool)) (by intro i;rfl)
  have hi := tabulate_sites_le (B:=1) (fun _ : Fin I => (⟨true,1⟩ : Result Bool)) (by intro i;rfl)
  have hq := tabulate_sites_le (B:=1) (fun _ : Fin Q => (⟨false,1⟩ : Result Bool)) (by intro i;rfl)
  dsimp [initialFlags]
  omega

theorem initialFlags_sites_incidence {P I Q : ℕ} (hQ : Q ≤ I) :
    (initialFlags P I Q).sites ≤ 14*(P+2*I)+9 := by
  have h:=initialFlags_sites_le P I Q
  omega

/-- Uniform price in the bounded-bit array/scalar model. `B` bounds maintained
scalar magnitudes, and `A` bounds address/index words. Counter annotations are
ghost data. No conversion from opaque arbitrary integers is assumed free. -/
def bitUnit (B A : ℕ) : ℕ := 256*(B+A+2)^2

/-- The actual normalized add implementation fits the uniform scalar price. -/
theorem normalizedAdd_bitUnit {B A : ℕ} (x y : IntegerArithmetic.SignedBits)
    (hx : x.magnitude.length ≤ B) (hy : y.magnitude.length ≤ B) :
    (IntegerArithmetic.normalizedAddCounted x y).2 ≤ bitUnit B A := by
  have h:=IntegerArithmetic.normalizedAddCounted_steps x y
  have hm : max x.magnitude.length y.magnitude.length ≤ B := max_le hx hy
  have hu : 256*(B+1)^2 ≤ bitUnit B A := by
    exact Nat.mul_le_mul_left 256 (Nat.pow_le_pow_left (by omega : B+1 ≤ B+A+2) 2)
  have hb : (IntegerArithmetic.normalizedAddCounted x y).2 ≤ 256*(B+1)^2 := by
    nlinarith
  exact hb.trans hu

/-- Products in score certification and modulus accumulation are genuinely
multi-bit arithmetic, even when their semantic type is `Nat`. -/
theorem normalizedMul_bitUnit {B A : ℕ} (x y : IntegerArithmetic.SignedBits)
    (hx : x.magnitude.length ≤ B) (hy : y.magnitude.length ≤ B) :
    (IntegerArithmetic.normalizedMulCounted x y).2 ≤ bitUnit B A := by
  have h:=IntegerArithmetic.normalizedMulCounted_steps x y
  have hp:=Nat.mul_le_mul
    (Nat.add_le_add_right hx 1) (by omega : x.magnitude.length+y.magnitude.length+2 ≤ 2*B+2)
  have hu : 256*(B+1)^2 ≤ bitUnit B A := by
    exact Nat.mul_le_mul_left 256 (Nat.pow_le_pow_left (by omega : B+1 ≤ B+A+2) 2)
  have hb : (IntegerArithmetic.normalizedMulCounted x y).2 ≤ 256*(B+1)^2 := by
    nlinarith
  exact hb.trans hu

/-- Strict and non-strict natural comparisons use the explicit borrow chain;
reversing its operands and negating the final bit gives ` ≤ `. -/
theorem borrow_bitUnit {B A : ℕ} (xs ys : List Bool)
    (hx : xs.length ≤ B) (hy : ys.length ≤ B) :
    (IntegerArithmetic.subCounted xs ys false).2 ≤ bitUnit B A := by
  rw [(IntegerArithmetic.subCounted_projections xs ys false).2,
    IntegerArithmetic.columnSteps_eq]
  have hm : max xs.length ys.length ≤ B := max_le hx hy
  have hu : 256*(B+1)^2 ≤ bitUnit B A := by
    exact Nat.mul_le_mul_left 256 (Nat.pow_le_pow_left (by omega : B+1 ≤ B+A+2) 2)
  have hb : 12*max xs.length ys.length+1 ≤ 256*(B+1)^2 := by nlinarith
  exact hb.trans hu

/-- Indexed reads/writes and bounded index updates also fit this price. A
read or write copies at most one `B`-bit cell and one `A`-bit address. -/
theorem array_bitUnit (B A : ℕ) : B+A+1 ≤ bitUnit B A := by
  dsimp [bitUnit]
  nlinarith

/-- The finite array/scalar execution can be priced without changing its
value or repeating its backend. The maintained-register magnitude hypotheses
are established separately; the actual loop count is `out.sites`. -/
def pricedSites {α : Type*} (B A : ℕ) (out : Result α) : ℕ := bitUnit B A*out.sites

theorem restartsExec_priced_bound {P I Q B A : ℕ} {Payload : Type*} (O : Oracle I Payload)
    (owner : Owners I Q) (primes : Counts P) (blockSizes : Counts I) (remaining : Flags P)
    (k lam n : ℕ) (active : Flags I) (marked : Flags Q) (hP : 0<P) :
    pricedSites B A (restartsExec O owner primes blockSizes remaining k lam n active marked)  ≤
      bitUnit B A*(256*(k+1)*(k+2)*
        (restartsExec O owner primes blockSizes remaining k lam n active marked).value.controllerVisits+1) :=
  Nat.mul_le_mul_left _ (restartsExec_sites_by_visits O owner primes blockSizes remaining k lam n active marked hP)

abbrev CountsBound {I : ℕ} (counts : Counts I) (X : ℕ) : Prop :=
  ∀ i, counts.get i  ≤  X

abbrev TablesBound {P I : ℕ} (rows : Tables P I) (X : ℕ) : Prop :=
  ∀ p, CountsBound (rows.get p) X

theorem column_bound {P I X : ℕ} (rows : Tables P I)
    (hrows : TablesBound rows X) (i : Fin I) :
    CountsBound (column rows i) X := by
  intro p
  simpa only [get_column] using hrows p i

theorem minima_bound {P I X : ℕ} (rows : Tables P I) (remaining : Flags P)
    (hrows : TablesBound rows X) : CountsBound (minima rows remaining) X := by
  intro i
  simp only [minima, Vector.get_ofFn]
  split
  · exact Nat.zero_le X
  · rename_i p hp
    exact hrows p i

theorem evaluate_bound {P I X : ℕ} (O : ArrayCompositeAlgorithm.Oracle I)
    (hO : ∀ selected candidate active, CountsBound (O.table selected candidate active) X)
    (active : Flags I) (primes : Counts P) (remaining : Flags P)
    (d : ℕ) (selected : List ℕ) :
    TablesBound (evaluate O active primes remaining d selected) X := by
  intro p i
  simp only [evaluate, Vector.get_ofFn]
  cases hp : remaining.get p with
  | false => simp only [Bool.false_eq_true, if_false, Vector.get_replicate]; exact Nat.zero_le X
  | true => simp only [if_true]; exact hO selected (primes.get p) active i

theorem greedy_base_bound {P I X : ℕ} (O : ArrayCompositeAlgorithm.Oracle I)
    (hO : ∀ selected candidate active, CountsBound (O.table selected candidate active) X)
    (active : Flags I) (primes : Counts P) (k d : ℕ)
    (remaining : Flags P) (base : Counts I) (selected : List ℕ)
    (hbase : CountsBound base X) :
    CountsBound (ArrayCompositeAlgorithm.greedy O active primes k d remaining base selected).base X := by
  induction k generalizing d remaining base selected with
  | zero => exact hbase
  | succ k ih =>
      simp only [ArrayCompositeAlgorithm.greedy]
      split
      · exact hbase
      · rename_i p hp
        exact ih _ _ _ _ (evaluate_bound O hO active primes remaining d selected p)

theorem greedy_modulus_bound {P I pmax : ℕ} (O : ArrayCompositeAlgorithm.Oracle I)
    (active : Flags I) (primes : Counts P) (hprimes : CountsBound primes pmax)
    (hpmax : 1  ≤  pmax) (k d : ℕ)
    (remaining : Flags P) (base : Counts I) (selected : List ℕ) :
    (ArrayCompositeAlgorithm.greedy O active primes k d remaining base selected).modulus  ≤
      d * pmax^k := by
  induction k generalizing d remaining base selected with
  | zero => simp only [ArrayCompositeAlgorithm.greedy, pow_zero, Nat.mul_one, le_refl]
  | succ k ih =>
      simp only [ArrayCompositeAlgorithm.greedy]
      split
      · exact Nat.le_mul_of_pos_right d (Nat.one_le_pow _ _ hpmax)
      · rename_i p hp
        have ht := ih (d * primes.get p) (ArrayCompositeAlgorithm.put remaining p false)
          ((evaluate O active primes remaining d selected).get p) (selected ++ [primes.get p])
        calc
          _  ≤  (d * primes.get p) * pmax^k := ht
          _  ≤  (d * pmax) * pmax^k := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left d (hprimes p))
          _ = d * pmax^(k+1) := by rw [pow_succ]; ring

theorem counted_greedy_base_bound {P I X : ℕ} {Payload : Type*}
    (O : CountedArrayComposite.Oracle I Payload)
    (hO : ∀ selected candidate active,
      CountsBound (O.table selected candidate active).counts X)
    (active : Flags I) (primes : Counts P) (k d : ℕ)
    (remaining : Flags P) (base : Counts I) (selected : List ℕ)
    (hbase : CountsBound base X) :
    CountsBound (CountedArrayComposite.greedy O active primes k d remaining base selected).base X := by
  have he := congrArg ArrayCompositeAlgorithm.GreedyResult.base
    (CountedArrayComposite.greedy_erases O active primes k d remaining base selected)
  simp only [CountedArrayComposite.GreedyResult.erase] at he
  rw [he]
  exact greedy_base_bound O.erase hO active primes k d remaining base selected hbase

theorem counted_greedy_modulus_bound {P I pmax : ℕ} {Payload : Type*}
    (O : CountedArrayComposite.Oracle I Payload)
    (active : Flags I) (primes : Counts P) (hprimes : CountsBound primes pmax)
    (hpmax : 1  ≤  pmax) (k d : ℕ)
    (remaining : Flags P) (base : Counts I) (selected : List ℕ) :
    (CountedArrayComposite.greedy O active primes k d remaining base selected).modulus  ≤
      d * pmax^k := by
  have he := congrArg ArrayCompositeAlgorithm.GreedyResult.modulus
    (CountedArrayComposite.greedy_erases O active primes k d remaining base selected)
  simp only [CountedArrayComposite.GreedyResult.erase] at he
  rw [he]
  exact greedy_modulus_bound O.erase active primes hprimes hpmax k d remaining base selected


/-- Includes every partial sum, not merely the final scalar score. -/
theorem scoreScan_bound {I X : ℕ} (active : Flags I) (row : Counts I)
    (hrow : CountsBound row X) (is : List (Fin I)) :
    (scoreScan active row is).value ≤ is.length*X := by
  induction is with
  | nil => simp [scoreScan]
  | cons i is ih =>
    have hi:=hrow i
    simp only [scoreScan,List.length_cons]
    cases active.get i <;> simp only [Bool.false_eq_true,if_false,if_true]
    all_goals nlinarith

theorem scores_bound {P I X : ℕ} (active : Flags I) (rows : Tables P I)
    (hrows : TablesBound rows X) : CountsBound (scores active rows).value (I*X) := by
  intro p
  simp only [scores,tabulate_value]
  simpa only [Vector.get_ofFn,score,List.length_finRange] using
    scoreScan_bound active (rows.get p) (hrows p) (List.finRange I)

theorem population_bound {P : ℕ} (remaining : Flags P) :
    (populationExec remaining).value ≤ P := by
  simp only [populationExec,lengthExec_value]
  exact indices_length_le remaining

/-- The two products in certification and survivor tests have explicit
magnitude bounds, independently of the Boolean short-circuit behavior. -/
theorem certification_products_bound {I X L M : ℕ} (base mu : Counts I)
    (hb : CountsBound base X) (hm : CountsBound mu X) {lam m : ℕ}
    (hl : lam ≤ L) (hp : m ≤ M) (i : Fin I) :
    lam*base.get i ≤ L*X ∧ m*mu.get i ≤ M*X :=
  ⟨Nat.mul_le_mul hl (hb i),Nat.mul_le_mul hp (hm i)⟩

theorem sumWork_bound {I W : ℕ} {Payload : Type*} (calls : List (Call I Payload))
    (hW : ∀call∈calls,call.result.work ≤ W) :
    (sumWork calls).value ≤ calls.length*W := by
  induction calls with
  | nil => simp [sumWork]
  | cons call calls ih =>
    have hc:=hW call (by simp)
    have ht:=ih (by intro c hm;exact hW c (by simp [hm]))
    simp only [sumWork,List.length_cons]
    nlinarith

/-- Accumulated backend metadata work is bounded from the actual retained
producer returns, with no second evaluation of any producer. -/
theorem restartsExec_backendWork_bound {P I Q W : ℕ} {Payload : Type*} (O : Oracle I Payload)
    (hW : ∀ selected candidate active,(O.table selected candidate active).work ≤ W)
    (owner : Owners I Q) (primes : Counts P) (blockSizes : Counts I) (remaining : Flags P)
    (k lam n : ℕ) (active : Flags I) (marked : Flags Q) :
    (restartsExec O owner primes blockSizes remaining k lam n active marked).value.backendWork ≤
      n*(k+1)*P*W := by
  let out:=restartsExec O owner primes blockSizes remaining k lam n active marked
  have hw : ∀call∈out.value.calls,call.result.work ≤ W := by
    intro call hc
    have hr:=restartsExec_retained_results O owner primes blockSizes remaining k lam n active marked call hc
    rw [hr]
    exact hW _ _ _
  have hs:=sumWork_bound out.value.calls hw
  have hl : out.value.calls.length ≤ n*(k+1)*P := by
    dsimp only [out]
    rw [restartsExec_value]
    exact CountedArrayComposite.restarts_calls_bound O owner primes blockSizes remaining k lam n active marked
  rw [sumWork_value,←restartsExec_backendWork O owner primes blockSizes remaining k lam n active marked] at hs
  exact hs.trans (Nat.mul_le_mul_right W hl)

/-- A concrete cap for scalar registers and list/index metadata. The exponent
`k+1` allows the temporary multiplication preceding a modulus update. This is
an input-derived number; it is not an assumed total-runtime bound. -/
def controllerCap (P I Q k lam n X W pmax : ℕ) : ℕ :=
  X+I*X+lam*X+P*X+pmax^(k+1)+n*(k+1)*P*(W+1)+P+I+Q+k+lam+n+pmax+1

/-- Magnitude-to-bit-width pricing for a maintained canonical register. -/
theorem scalar_size_of_cap {P I Q k lam n X W pmax x : ℕ}
    (hx : x ≤ controllerCap P I Q k lam n X W pmax) :
    x.size ≤ (controllerCap P I Q k lam n X W pmax).size := Nat.size_le_size hx

/-- Every explicitly charged scalar category is dominated by the same cap. -/
theorem controllerCap_components (P I Q k lam n X W pmax : ℕ) :
    X ≤ controllerCap P I Q k lam n X W pmax ∧
    I*X ≤ controllerCap P I Q k lam n X W pmax ∧
    lam*X ≤ controllerCap P I Q k lam n X W pmax ∧
    P*X ≤ controllerCap P I Q k lam n X W pmax ∧
    pmax^(k+1) ≤ controllerCap P I Q k lam n X W pmax ∧
    n*(k+1)*P*W ≤ controllerCap P I Q k lam n X W pmax ∧
    n*(k+1)*P ≤ controllerCap P I Q k lam n X W pmax ∧
    P+I+Q+k+lam+n+pmax+1 ≤ controllerCap P I Q k lam n X W pmax := by
  have hw := Nat.mul_le_mul_left (n*(k+1)*P) (Nat.le_succ W)
  have hl := Nat.mul_le_mul_left (n*(k+1)*P) (by omega : 1 ≤ W+1)
  simp only [Nat.succ_eq_add_one] at hw
  dsimp [controllerCap]
  omega

/-- Actual per-stage score/minimum/product/modulus values have the concrete
input-derived cap. The same statement applies to every restart active mask. -/
theorem stage_registers_bound {P I Q X W pmax : ℕ} {Payload : Type*}
    (O : Oracle I Payload)
    (hO : ∀ selected candidate active,CountsBound (O.table selected candidate active).counts X)
    (_owner : Owners I Q) (primes : Counts P) (hprimes : CountsBound primes pmax)
    (hpmax : 1 ≤ pmax) (active : Flags I) (_marked : Flags Q) (blockSizes : Counts I)
    (hbase : CountsBound blockSizes X) (remaining : Flags P) (k lam n : ℕ) :
    let chosen := greedyExec O active primes k 1 remaining blockSizes []
    let cache := evaluateOnce O active primes chosen.value.remaining chosen.value.selected
    let rows := cacheRows cache.value
    let mu := minimaExec rows.value chosen.value.remaining
    let m := populationExec chosen.value.remaining
    let cap := controllerCap P I Q k lam n X W pmax
    CountsBound (scores active rows.value).value cap ∧
    CountsBound chosen.value.base cap ∧ CountsBound mu.value cap ∧
    (∀ i,lam*chosen.value.base.get i ≤ cap ∧ m.value*mu.value.get i ≤ cap) ∧
    chosen.value.modulus ≤ cap := by
  dsimp only
  let chosen := greedyExec O active primes k 1 remaining blockSizes []
  let cache := evaluateOnce O active primes chosen.value.remaining chosen.value.selected
  let rows := cacheRows cache.value
  have hc:=controllerCap_components P I Q k lam n X W pmax
  have hb : CountsBound chosen.value.base X := by
    dsimp only [chosen]
    rw [greedyExec_value]
    exact counted_greedy_base_bound O hO active primes k 1 remaining blockSizes [] hbase
  have hr : TablesBound rows.value X := by
    dsimp only [rows,cache]
    rw [cacheRows_value,evaluateOnce_value,CountedArrayComposite.evaluateOnce_rows O active primes
      chosen.value.remaining 1 chosen.value.selected]
    exact evaluate_bound O.erase hO active primes chosen.value.remaining 1 chosen.value.selected
  have hm : CountsBound (minimaExec rows.value chosen.value.remaining).value X := by
    rw [minimaExec_value]
    exact minima_bound rows.value chosen.value.remaining hr
  have hs:=scores_bound active rows.value hr
  have hp:=population_bound chosen.value.remaining
  have hd : chosen.value.modulus ≤ pmax^k := by
    dsimp only [chosen]
    rw [greedyExec_value]
    simpa only [Nat.one_mul] using
      counted_greedy_modulus_bound O active primes hprimes hpmax k 1 remaining blockSizes []
  have hpow : pmax^k ≤ pmax^(k+1) := by
    rw [pow_succ]
    exact Nat.le_mul_of_pos_right _ hpmax
  refine ⟨?_,?_,?_,?_,hd.trans (hpow.trans hc.2.2.2.2.1)⟩
  · intro p
    exact (hs p).trans hc.2.1
  · intro i
    exact (hb i).trans hc.1
  · intro i
    exact (hm i).trans hc.1
  · intro i
    have ht:=certification_products_bound chosen.value.base
      (minimaExec rows.value chosen.value.remaining).value hb hm (le_refl lam) hp i
    exact ⟨ht.1.trans hc.2.2.1,ht.2.trans hc.2.2.2.1⟩

/-- The backend work accumulator and call-list indices obey the same cap. -/
theorem restarts_metadata_bound {P I Q X W pmax : ℕ} {Payload : Type*} (O : Oracle I Payload)
    (hW : ∀ selected candidate active,(O.table selected candidate active).work ≤ W)
    (owner : Owners I Q) (primes : Counts P) (blockSizes : Counts I) (remaining : Flags P)
    (k lam n : ℕ) (active : Flags I) (marked : Flags Q) :
    let out:=restartsExec O owner primes blockSizes remaining k lam n active marked
    out.value.backendWork ≤ controllerCap P I Q k lam n X W pmax ∧
    out.value.calls.length ≤ controllerCap P I Q k lam n X W pmax := by
  have hc:=controllerCap_components P I Q k lam n X W pmax
  refine ⟨(restartsExec_backendWork_bound O hW owner primes blockSizes remaining k lam n active marked).trans hc.2.2.2.2.2.1,?_⟩
  rw [restartsExec_value]
  exact (CountedArrayComposite.restarts_calls_bound O owner primes blockSizes remaining k lam n active marked).trans
    hc.2.2.2.2.2.2.1

/-- A temporary modulus product has the advertised cap before storage. -/
theorem modulus_temporary_bound {k pmax d p : ℕ} (hd : d ≤ pmax^k) (hp : p ≤ pmax) :
    d*p ≤ pmax^(k+1) := by
  calc
    d*p ≤ pmax^k*pmax := Nat.mul_le_mul hd hp
    _ = pmax^(k+1) := (pow_succ pmax k).symm

/-- Canonical maintained registers have exactly the semantic size. This is a
representation invariant, rather than a free conversion performed per site. -/
theorem maintained_nat_length (x : ℕ) :
    (IntegerArithmetic.ofInt (x : ℤ)).magnitude.length=x.size := by
  simp [IntegerArithmetic.ofInt_length]

theorem borrow_value (xs ys : List Bool) :
    (IntegerArithmetic.subCounted xs ys false).1.2=true ↔
      IntegerArithmetic.value xs<IntegerArithmetic.value ys := by
  rw [(IntegerArithmetic.subCounted_projections xs ys false).1]
  exact IntegerArithmetic.subBits_borrow xs ys

/-- Every partial score of a bounded scan admits the same maintained width. -/
theorem partial_score_bits {P I Q k lam n X W pmax : ℕ} (active : Flags I) (row : Counts I)
    (hrow : CountsBound row X) (is : List (Fin I)) (hlen : is.length ≤ I) :
    (scoreScan active row is).value.size ≤ (controllerCap P I Q k lam n X W pmax).size := by
  have hs:=scoreScan_bound active row hrow is
  have hc:=(controllerCap_components P I Q k lam n X W pmax).2.1
  exact scalar_size_of_cap (hs.trans ((Nat.mul_le_mul_right X hlen).trans hc))

/-- The bit-priced controller retains actual execution sites and literal
backend results; its upper ledger is a proved consequence, not its definition. -/
theorem controller_execution_contract {P I Q : ℕ} {Payload : Type*} (O : Oracle I Payload)
    (owner : Owners I Q) (primes : Counts P) (blockSizes : Counts I) (remaining : Flags P)
    (k lam n B A : ℕ) (active : Flags I) (marked : Flags Q) (hP : 0<P) :
    let out:=restartsExec O owner primes blockSizes remaining k lam n active marked
    out.value=CountedArrayComposite.restarts O owner primes blockSizes remaining k lam n active marked ∧
    out.value.backendWork=CountedArrayComposite.workSum out.value.calls ∧
    (∀call∈out.value.calls,call.result=O.table call.factors.selected call.factors.candidate call.factors.active) ∧
    out.sites ≤ 256*(k+1)*(k+2)*out.value.controllerVisits+1 ∧
    pricedSites B A out ≤ bitUnit B A*(256*(k+1)*(k+2)*out.value.controllerVisits+1) :=
  ⟨restartsExec_value O owner primes blockSizes remaining k lam n active marked,
   restartsExec_backendWork O owner primes blockSizes remaining k lam n active marked,
   restartsExec_retained_results O owner primes blockSizes remaining k lam n active marked,
   restartsExec_sites_by_visits O owner primes blockSizes remaining k lam n active marked hP,
   restartsExec_priced_bound O owner primes blockSizes remaining k lam n active marked hP⟩

/-- Small execution check uses a literal retained table payload. -/
def exampleOracle : Oracle 2 ℕ :=
  ⟨fun selected prime _=>
    ⟨Vector.ofFn (fun i=>prime+i.val+selected.length),prime,7⟩⟩

def exampleExecution : Result (CountedArrayComposite.StageResult 3 2 1 ℕ) :=
  restartsExec exampleOracle (Vector.replicate 2 (0 : Fin 1))
    (Vector.ofFn (fun p : Fin 3 => p.val+2)) (Vector.replicate 2 4)
    (Vector.replicate 3 true) 1 1 2 (Vector.replicate 2 true) (Vector.replicate 1 false)

#eval (exampleExecution.sites,exampleExecution.value.calls.length,
  exampleExecution.value.backendWork,exampleExecution.value.controllerVisits,
  exampleExecution.value.active.toList,exampleExecution.value.marked.toList)

#print axioms evaluateOnce_value
#print axioms cacheCalls_value
#print axioms scoreScan_value
#print axioms scores_value
#print axioms choose_value
#print axioms minimaExec_value
#print axioms finish_value
#print axioms greedyExec_value
#print axioms greedyExec_sites_le
#print axioms stageExec_value
#print axioms stageExec_sites_le
#print axioms restartsExec_value
#print axioms restartsExec_sites_le
#print axioms restartsExec_sites_by_visits
#print axioms restartsExec_backendWork
#print axioms restartsExec_retained_results
#print axioms normalizedMul_bitUnit
#print axioms borrow_value
#print axioms controllerCap_components
#print axioms stage_registers_bound
#print axioms restarts_metadata_bound
#print axioms controller_execution_contract

end ThinMatrix.DenseControllerExecution
