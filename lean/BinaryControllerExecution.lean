import BinaryCell
import DenseControllerExecution

/-!
# Whole binary composite controller

Counts, score accumulators, minima, pool counts, threshold products, and moduli
are maintained canonical BinaryCell values. The executable definitions never
call the Nat/Int views; those occur only in projections and proof fields.
Each eligible table is produced once and its original payload is retained.

The joint bit counter is the sum of actual binary arithmetic/borrow circuits.
Public bounded loop, prime-label, flag, pointer and address control operations
use a separately priced finite indexed-array IR. Resource counters are ghost
annotations. This is a data-lowering theorem, not a full Light compilation or
a runtime theorem for Lean persistent arrays.
-/

namespace ThinMatrix.BinaryControllerExecution

open ArrayCompositeAlgorithm hiding Counts
open scoped BigOperators

/-- Runtime scalar data contains maintained canonical bits and an erased sign proof. -/
def NatCell := {a : BinaryCell.Cell // 0 ≤ BinaryCell.view a}

def NatCell.cell (a : NatCell) : BinaryCell.Cell := a.val
theorem NatCell.nonnegative (a : NatCell) : 0 ≤ BinaryCell.view a.cell := a.property

/-- Semantic projection; no runtime operation decodes a stored cell. -/
def nview (a : NatCell) : ℕ := (BinaryCell.view a.cell).toNat

@[simp] theorem nview_cast (a : NatCell) : (nview a : ℤ) = BinaryCell.view a.cell :=
  Int.toNat_of_nonneg a.nonnegative

@[simp] theorem magnitude_value (a : NatCell) :
    IntegerArithmetic.value a.cell.bits.magnitude = nview a := by
  rw [← IntegerArithmetic.signedValue_natAbs]
  change (BinaryCell.view a.cell).natAbs = _
  rw [← nview_cast a, Int.natAbs_natCast]

@[simp] theorem magnitude_length (a : NatCell) : a.cell.bits.magnitude.length = (nview a).size := by
  rw [BinaryCell.canonical, ← nview_cast a, Int.natAbs_natCast]

structure Result (α : Type*) where
  value : α
  bitSteps : ℕ
  controlSites : ℕ
  arithSites : ℕ

/-- Literal constant materialization. -/
def zero : NatCell := ⟨BinaryCell.zero, by simp⟩
def one : NatCell := ⟨⟨⟨false,[true]⟩,rfl⟩,by decide⟩
@[simp] theorem zero_nview : nview zero = 0 := rfl
@[simp] theorem one_nview : nview one = 1 := rfl

def add (a b : NatCell) : Result NatCell :=
  let out := BinaryCell.add a.cell b.cell
  ⟨⟨out.value,by simpa only [out,BinaryCell.add_view] using add_nonneg a.nonnegative b.nonnegative⟩,out.bitSteps,1,1⟩

def mul (a b : NatCell) : Result NatCell :=
  let out := BinaryCell.mul a.cell b.cell
  ⟨⟨out.value,by simpa only [out,BinaryCell.mul_view] using mul_nonneg a.nonnegative b.nonnegative⟩,out.bitSteps,1,1⟩

def copy (a : NatCell) : Result NatCell :=
  let out := BinaryCell.copy a.cell
  ⟨⟨out.value,by simpa only [out,BinaryCell.copy_view] using a.nonnegative⟩,out.bitSteps,1,1⟩

@[simp] theorem add_nview (a b : NatCell) : nview (add a b).value = nview a+nview b := by
  apply Int.ofNat_inj.mp
  simp [add, NatCell.cell, Nat.cast_add]

@[simp] theorem mul_nview (a b : NatCell) : nview (mul a b).value = nview a*nview b := by
  apply Int.ofNat_inj.mp
  simp [mul, NatCell.cell, Nat.cast_mul]

@[simp] theorem copy_nview (a : NatCell) : nview (copy a).value = nview a := by
  apply Int.ofNat_inj.mp
  simp [copy, NatCell.cell]

/-- Strict comparison consumes the maintained unsigned magnitudes through the
actual subtraction-and-borrow circuit. The erased sign proof justifies it. -/
def lt (a b : NatCell) : Result Bool :=
  let out := BackendScalarBits.unsignedLessCounted a.cell.bits.magnitude b.cell.bits.magnitude
  ⟨out.1,out.2,1,1⟩

def le (a b : NatCell) : Result Bool :=
  let out := lt b a
  ⟨!out.value,out.bitSteps,out.controlSites+1,out.arithSites⟩

@[simp] theorem lt_value (a b : NatCell) : (lt a b).value = decide (nview a<nview b) := by
  apply Bool.eq_iff_iff.mpr
  simp [lt, BackendScalarBits.unsignedLess_correct]

@[simp] theorem le_value (a b : NatCell) : (le a b).value = decide (nview a≤nview b) := by
  simp only [le,lt_value]
  by_cases h : nview a≤nview b <;> simp [h,show (nview b<nview a) ↔ ¬ nview a≤nview b by omega]

abbrev unit := BackendScalarBits.backendScalarUnit

theorem add_price (B : ℕ) (a b : NatCell) (ha : (nview a).size≤B) (hb : (nview b).size≤B) :
    (add a b).bitSteps ≤ unit B := by
  apply BinaryCell.add_price B <;> simpa only [← nview_cast,Int.natAbs_natCast]

theorem mul_price (B : ℕ) (a b : NatCell) (ha : (nview a).size≤B) (hb : (nview b).size≤B) :
    (mul a b).bitSteps ≤ unit B := by
  apply BinaryCell.mul_price B <;> simpa only [← nview_cast,Int.natAbs_natCast]

theorem copy_price (B : ℕ) (a : NatCell) (ha : (nview a).size≤B) :
    (copy a).bitSteps ≤ unit B := by
  apply BinaryCell.copy_price B
  simpa only [← nview_cast,Int.natAbs_natCast]

theorem lt_price (B : ℕ) (a b : NatCell) (ha : (nview a).size≤B) (hb : (nview b).size≤B) :
    (lt a b).bitSteps ≤ unit B := by
  have h := BackendScalarBits.unsignedLess_price B a.cell.bits.magnitude b.cell.bits.magnitude
    (by simpa using ha) (by simpa using hb)
  exact h.trans (by unfold unit BackendScalarBits.backendScalarUnit; omega)

theorem le_price (B : ℕ) (a b : NatCell) (ha : (nview a).size≤B) (hb : (nview b).size≤B) :
    (le a b).bitSteps ≤ unit B := lt_price B b a hb ha

abbrev Counts (I : ℕ) := Vector NatCell I
abbrev CellCounts := Counts
abbrev CellTables (P I : ℕ) := Vector (CellCounts I) P

def projectCounts {I : ℕ} (row : CellCounts I) : ArrayCompositeAlgorithm.Counts I := row.map nview
abbrev countsView := @projectCounts
def tablesView {P I : ℕ} (rows : CellTables P I) : Tables P I := rows.map countsView
@[simp] theorem countsView_get {I : ℕ} (row : CellCounts I) (i : Fin I) :
    (countsView row).get i = nview (row.get i) := by simp [countsView,projectCounts]
@[simp] theorem tablesView_get {P I : ℕ} (rows : CellTables P I) (p : Fin P) :
    (tablesView rows).get p = countsView (rows.get p) := by simp [tablesView]

/-- Recursive results are shared; each nonempty iteration executes one binary add. -/
def scoreScan {I : ℕ} (active : Flags I) (row : CellCounts I) : List (Fin I) → Result NatCell
  | [] => ⟨zero,0,1,0⟩
  | i::is =>
    let tail := scoreScan active row is
    let flag := active.get i
    let entry := if flag then row.get i else zero
    let out := add entry tail.value
    ⟨out.value,tail.bitSteps+out.bitSteps,tail.controlSites+6,tail.arithSites+1⟩

theorem scoreScan_value {I : ℕ} (active : Flags I) (row : CellCounts I) (is : List (Fin I)) :
    nview (scoreScan active row is).value = (DenseControllerExecution.scoreScan active (countsView row) is).value := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    simp only [scoreScan, DenseControllerExecution.scoreScan,add_nview]
    rw [ih]
    cases active.get i <;> simp

theorem scoreScan_control {I : ℕ} (active : Flags I) (row : CellCounts I) (is : List (Fin I)) :
    (scoreScan active row is).controlSites = (DenseControllerExecution.scoreScan active (countsView row) is).sites := by
  induction is with
  | nil => rfl
  | cons i is ih => simp [scoreScan,DenseControllerExecution.scoreScan,ih]

theorem scoreScan_arith {I : ℕ} (active : Flags I) (row : CellCounts I) (is : List (Fin I)) :
    (scoreScan active row is).arithSites = is.length := by
  induction is with
  | nil => rfl
  | cons i is ih => simp [scoreScan,ih]

theorem scoreScan_bound {I X : ℕ} (active : Flags I) (row : CellCounts I)
    (hrow : ∀ i, nview (row.get i)≤X) (is : List (Fin I)) :
    nview (scoreScan active row is).value ≤ is.length*X := by
  induction is with
  | nil => simp [scoreScan]
  | cons i is ih =>
    simp only [scoreScan,add_nview,List.length_cons]
    have he : nview (if active.get i then row.get i else zero)≤X := by
      cases active.get i <;> simp [hrow]
    nlinarith

theorem scoreScan_price {I X B : ℕ} (active : Flags I) (row : CellCounts I)
    (hrow : ∀ i, nview (row.get i)≤X) (hX : X.size≤B) (is : List (Fin I))
    (hsize : (is.length*X).size≤B) :
    (scoreScan active row is).bitSteps ≤ unit B*(scoreScan active row is).arithSites := by
  induction is with
  | nil => simp [scoreScan]
  | cons i is ih =>
    have hlen : is.length*X≤(i::is).length*X := Nat.mul_le_mul_right X (by simp)
    have hs := (Nat.size_le_size hlen).trans hsize
    have ht := ih hs
    have he : (nview (if active.get i then row.get i else zero)).size≤B := by
      cases hflag : active.get i
      · simp
      · exact (Nat.size_le_size (hrow i)).trans hX
    have ha := add_price B (if active.get i then row.get i else zero) (scoreScan active row is).value he
      ((Nat.size_le_size (scoreScan_bound active row hrow is)).trans hs)
    simp only [scoreScan]
    nlinarith

def score {I : ℕ} (active : Flags I) (row : CellCounts I) : Result NatCell :=
  let out := scoreScan active row (List.finRange I)
  ⟨out.value,out.bitSteps,out.controlSites+4*I+1,out.arithSites⟩

theorem score_value {I : ℕ} (active : Flags I) (row : CellCounts I) :
    nview (score active row).value = (DenseControllerExecution.score active (countsView row)).value :=
  scoreScan_value active row _

theorem score_control {I : ℕ} (active : Flags I) (row : CellCounts I) :
    (score active row).controlSites = (DenseControllerExecution.score active (countsView row)).sites := by
  simp [score,DenseControllerExecution.score,scoreScan_control]

theorem score_arith {I : ℕ} (active : Flags I) (row : CellCounts I) :
    (score active row).arithSites = I := by simp [score,scoreScan_arith]

theorem score_bound {I X : ℕ} (active : Flags I) (row : CellCounts I)
    (hrow : ∀ i, nview (row.get i)≤X) : nview (score active row).value≤I*X := by
  simpa [score] using scoreScan_bound active row hrow (List.finRange I)

theorem score_price {I X B : ℕ} (active : Flags I) (row : CellCounts I)
    (hrow : ∀ i, nview (row.get i)≤X) (hX : X.size≤B) (hsize : (I*X).size≤B) :
    (score active row).bitSteps ≤ unit B*(score active row).arithSites := by
  exact scoreScan_price active row hrow hX _ (by simpa using hsize)

/-- Stored per-slot results are scanned jointly; no scalar producer runs again. -/
def scanTotals {n : ℕ} {α : Type*} (stored : Vector (Result α) n) :
    List (Fin n) → Result Unit
  | [] => ⟨(),0,1,0⟩
  | i::is =>
    let tail := scanTotals stored is
    let row := stored.get i
    ⟨(),row.bitSteps+tail.bitSteps,row.controlSites+tail.controlSites+6,
      row.arithSites+tail.arithSites⟩

theorem scanTotals_price {n B : ℕ} {α : Type*} (stored : Vector (Result α) n)
    (h : ∀ i, (stored.get i).bitSteps≤unit B*(stored.get i).arithSites) (is : List (Fin n)) :
    (scanTotals stored is).bitSteps≤unit B*(scanTotals stored is).arithSites := by
  induction is with
  | nil => simp [scanTotals]
  | cons i is ih =>
    have hi := h i
    simp only [scanTotals]
    nlinarith

theorem scanTotals_control_le {n C : ℕ} {α : Type*} (stored : Vector (Result α) n)
    (h : ∀ i, (stored.get i).controlSites≤C) (is : List (Fin n)) :
    (scanTotals stored is).controlSites≤(C+6)*is.length+1 := by
  induction is with
  | nil => simp [scanTotals]
  | cons i is ih =>
    have hi := h i
    simp only [scanTotals,List.length_cons]
    nlinarith

theorem scanTotals_arith_le {n C : ℕ} {α : Type*} (stored : Vector (Result α) n)
    (h : ∀ i, (stored.get i).arithSites≤C) (is : List (Fin n)) :
    (scanTotals stored is).arithSites≤C*is.length := by
  induction is with
  | nil => simp [scanTotals]
  | cons i is ih =>
    have hi := h i
    simp only [scanTotals,List.length_cons]
    nlinarith

/-- Eagerly execute `f` once per slot and then materialize values/counters from
those stored joint results. -/
def tabulate {n : ℕ} {α : Type*} (f : Fin n → Result α) : Result (Vector α n) :=
  let stored := Vector.ofFn f
  let values := stored.map Result.value
  let total := scanTotals stored (List.finRange n)
  ⟨values,total.bitSteps,total.controlSites+7*n+1,total.arithSites⟩

theorem tabulate_value {n : ℕ} {α : Type*} (f : Fin n → Result α) :
    (tabulate f).value = Vector.ofFn (fun i => (f i).value) := by
  apply Vector.ext
  intro i hi
  simp [tabulate]

theorem tabulate_price {n B : ℕ} {α : Type*} (f : Fin n → Result α)
    (h : ∀ i, (f i).bitSteps≤unit B*(f i).arithSites) :
    (tabulate f).bitSteps≤unit B*(tabulate f).arithSites := by
  apply scanTotals_price
  intro i
  simpa using h i

theorem tabulate_control_le {n C : ℕ} {α : Type*} (f : Fin n → Result α)
    (h : ∀ i, (f i).controlSites≤C) :
    (tabulate f).controlSites≤n*(C+13)+2 := by
  have hs := scanTotals_control_le (Vector.ofFn f) (by simpa using h) (List.finRange n)
  simp only [List.length_finRange] at hs
  change (scanTotals (Vector.ofFn f) (List.finRange n)).controlSites+7*n+1≤_
  nlinarith

theorem tabulate_arith_le {n C : ℕ} {α : Type*} (f : Fin n → Result α)
    (h : ∀ i, (f i).arithSites≤C) :
    (tabulate f).arithSites≤n*C := by
  have hs := scanTotals_arith_le (Vector.ofFn f) (by simpa using h) (List.finRange n)
  simpa [tabulate,Nat.mul_comm] using hs

def scores {P I : ℕ} (active : Flags I) (rows : CellTables P I) : Result (Counts P) :=
  tabulate (fun p =>
    let out := score active (rows.get p)
    ⟨out.value,out.bitSteps,out.controlSites+1,out.arithSites⟩)

theorem scores_value {P I : ℕ} (active : Flags I) (rows : CellTables P I) :
    projectCounts (scores active rows).value =
      (DenseControllerExecution.scores active (tablesView rows)).value := by
  rw [scores,tabulate_value,DenseControllerExecution.scores,DenseControllerExecution.tabulate_value]
  apply Vector.ext
  intro i hi
  simp [projectCounts,score_value]

theorem scores_control_le {P I : ℕ} (active : Flags I) (rows : CellTables P I) :
    (scores active rows).controlSites≤P*(10*I+16)+2 := by
  apply tabulate_control_le
  intro p
  simp [score_control,DenseControllerExecution.score_sites]

theorem scores_arith_le {P I : ℕ} (active : Flags I) (rows : CellTables P I) :
    (scores active rows).arithSites≤P*I := by
  apply tabulate_arith_le
  intro p
  simp [score_arith]

theorem scores_price {P I X B : ℕ} (active : Flags I) (rows : CellTables P I)
    (hrows : ∀ p i, nview ((rows.get p).get i)≤X) (hX : X.size≤B) (hIX : (I*X).size≤B) :
    (scores active rows).bitSteps≤unit B*(scores active rows).arithSites := by
  apply tabulate_price
  intro p
  exact score_price active (rows.get p) (hrows p) hX hIX

theorem scores_bound {P I X : ℕ} (active : Flags I) (rows : CellTables P I)
    (hrows : ∀ p i, nview ((rows.get p).get i)≤X) (p : Fin P) :
    nview ((scores active rows).value.get p)≤I*X := by
  simpa [scores,tabulate] using score_bound active (rows.get p) (hrows p)

def filterIndices {P : ℕ} (remaining : Flags P) : List (Fin P) → Result (List (Fin P))
  | [] => ⟨[],0,1,0⟩
  | p::ps =>
    let tail := filterIndices remaining ps
    let keep := remaining.get p
    ⟨if keep then p::tail.value else tail.value,tail.bitSteps,tail.controlSites+4,tail.arithSites⟩

theorem filterIndices_value {P : ℕ} (remaining : Flags P) (ps : List (Fin P)) :
    (filterIndices remaining ps).value = (DenseControllerExecution.filterIndices remaining ps).value := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [filterIndices,DenseControllerExecution.filterIndices,ih]

theorem filterIndices_control {P : ℕ} (remaining : Flags P) (ps : List (Fin P)) :
    (filterIndices remaining ps).controlSites = (DenseControllerExecution.filterIndices remaining ps).sites := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [filterIndices,DenseControllerExecution.filterIndices,ih]

theorem filterIndices_bitSteps {P : ℕ} (remaining : Flags P) (ps : List (Fin P)) :
    (filterIndices remaining ps).bitSteps = 0 := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [filterIndices,ih]

theorem filterIndices_arith {P : ℕ} (remaining : Flags P) (ps : List (Fin P)) :
    (filterIndices remaining ps).arithSites = 0 := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [filterIndices,ih]

def indices {P : ℕ} (remaining : Flags P) : Result (List (Fin P)) :=
  let out := filterIndices remaining (List.finRange P)
  ⟨out.value,out.bitSteps,out.controlSites+4*P+1,out.arithSites⟩

theorem indices_value {P : ℕ} (remaining : Flags P) :
    (indices remaining).value = (DenseControllerExecution.indices remaining).value :=
  filterIndices_value remaining _

theorem indices_control {P : ℕ} (remaining : Flags P) :
    (indices remaining).controlSites = (DenseControllerExecution.indices remaining).sites := by
  simp [indices,DenseControllerExecution.indices,filterIndices_control]

@[simp] theorem indices_bitSteps {P : ℕ} (remaining : Flags P) :
    (indices remaining).bitSteps = 0 := filterIndices_bitSteps remaining _
@[simp] theorem indices_arith {P : ℕ} (remaining : Flags P) :
    (indices remaining).arithSites = 0 := filterIndices_arith remaining _

theorem indices_length_le {P : ℕ} (remaining : Flags P) :
    (indices remaining).value.length≤P := by
  rw [indices_value]
  exact DenseControllerExecution.indices_length_le remaining

/-- Reverse recursive argmin preserves the source's first-index tie rule. -/
def best {P : ℕ} (values : Counts P) : List (Fin P) → Result (Option (Fin P))
  | [] => ⟨none,0,1,0⟩
  | p::ps =>
    let tail := best values ps
    match tail.value with
    | none => ⟨some p,tail.bitSteps,tail.controlSites+6,tail.arithSites⟩
    | some q =>
      let cmp := le (values.get p) (values.get q)
      ⟨some (if cmp.value then p else q),tail.bitSteps+cmp.bitSteps,
        tail.controlSites+6,tail.arithSites+1⟩

theorem best_value {P : ℕ} (values : Counts P) (ps : List (Fin P)) :
    (best values ps).value = (DenseControllerExecution.best (projectCounts values) ps).value := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simp only [best,DenseControllerExecution.best]
    rw [← ih]
    cases (best values ps).value with
    | none => rfl
    | some q => simp [le_value]

theorem best_control {P : ℕ} (values : Counts P) (ps : List (Fin P)) :
    (best values ps).controlSites = 6*ps.length+1 := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simp only [best,List.length_cons]
    cases (best values ps).value <;> simp [ih] <;> omega

theorem best_arith_le {P : ℕ} (values : Counts P) (ps : List (Fin P)) :
    (best values ps).arithSites≤ps.length := by
  induction ps with
  | nil => simp [best]
  | cons p ps ih =>
    simp only [best,List.length_cons]
    cases (best values ps).value <;> simp <;> omega

theorem best_price {P B : ℕ} (values : Counts P) (hvalues : ∀ p, (nview (values.get p)).size≤B)
    (ps : List (Fin P)) : (best values ps).bitSteps≤unit B*(best values ps).arithSites := by
  induction ps with
  | nil => simp [best]
  | cons p ps ih =>
    simp only [best]
    cases htail : (best values ps).value with
    | none => exact ih
    | some q =>
      have hp := le_price B (values.get p) (values.get q) (hvalues p) (hvalues q)
      nlinarith

def choose {P : ℕ} (remaining : Flags P) (values : Counts P) : Result (Option (Fin P)) :=
  let eligible := indices remaining
  let minimum := best values eligible.value
  ⟨minimum.value,eligible.bitSteps+minimum.bitSteps,
    eligible.controlSites+minimum.controlSites+1,eligible.arithSites+minimum.arithSites⟩

theorem choose_value {P : ℕ} (remaining : Flags P) (values : Counts P) :
    (choose remaining values).value = (DenseControllerExecution.choose remaining (projectCounts values)).value := by
  simp [choose,DenseControllerExecution.choose,best_value,indices_value]

theorem choose_control_le {P : ℕ} (remaining : Flags P) (values : Counts P) :
    (choose remaining values).controlSites≤14*P+4 := by
  have hl := indices_length_le remaining
  simp only [choose,indices_control,DenseControllerExecution.indices_sites,best_control]
  omega

theorem choose_arith_le {P : ℕ} (remaining : Flags P) (values : Counts P) :
    (choose remaining values).arithSites≤P := by
  have ha := best_arith_le values (indices remaining).value
  have hl := indices_length_le remaining
  simp only [choose,indices_arith,zero_add]
  omega

theorem choose_price {P B : ℕ} (remaining : Flags P) (values : Counts P)
    (hvalues : ∀ p, (nview (values.get p)).size≤B) :
    (choose remaining values).bitSteps≤unit B*(choose remaining values).arithSites := by
  simpa [choose] using best_price values hvalues (indices remaining).value

theorem scores_project {P I : ℕ} (active : Flags I) (rows : CellTables P I) :
    projectCounts (scores active rows).value = ArrayCompositeAlgorithm.scores active (tablesView rows) := by
  rw [scores_value,DenseControllerExecution.scores_value]

theorem choose_project {P : ℕ} (remaining : Flags P) (values : Counts P) :
    (choose remaining values).value = ArrayCompositeAlgorithm.choose remaining (projectCounts values) := by
  rw [choose_value,DenseControllerExecution.choose_value]

theorem choose_price_of_bound {P Z B : ℕ} (remaining : Flags P) (values : Counts P)
    (hvalues : ∀ p, nview (values.get p)≤Z) (hZ : Z.size≤B) :
    (choose remaining values).bitSteps≤unit B*(choose remaining values).arithSites :=
  choose_price remaining values (fun p => (Nat.size_le_size (hvalues p)).trans hZ)

theorem best_project {P : ℕ} (values : Counts P) (ps : List (Fin P)) :
    (best values ps).value = ArrayCompositeAlgorithm.best (projectCounts values) ps := by
  rw [best_value,DenseControllerExecution.best_value]

theorem scanTotals_zero_bits {n : ℕ} {α : Type*} (stored : Vector (Result α) n)
    (h : ∀ i, (stored.get i).bitSteps=0) (is : List (Fin n)) :
    (scanTotals stored is).bitSteps=0 := by
  induction is with
  | nil => rfl
  | cons i is ih => simp [scanTotals,h,ih]

theorem tabulate_zero_bits {n : ℕ} {α : Type*} (f : Fin n → Result α)
    (h : ∀ i, (f i).bitSteps=0) : (tabulate f).bitSteps=0 := by
  apply scanTotals_zero_bits
  intro i
  simpa using h i

/-- Materialize references to each cell in one physical column. -/
def column {P I : ℕ} (rows : CellTables P I) (i : Fin I) : Result (Counts P) :=
  tabulate (fun p => ⟨(rows.get p).get i,0,2,0⟩)

@[simp] theorem column_get {P I : ℕ} (rows : CellTables P I) (i : Fin I) (p : Fin P) :
    (column rows i).value.get p = (rows.get p).get i := by simp [column,tabulate]

theorem column_project {P I : ℕ} (rows : CellTables P I) (i : Fin I) :
    projectCounts (column rows i).value = ArrayCompositeAlgorithm.column (tablesView rows) i := by
  apply Vector.ext
  intro p hp
  simp [projectCounts,column,tabulate,ArrayCompositeAlgorithm.column]

@[simp] theorem column_bits {P I : ℕ} (rows : CellTables P I) (i : Fin I) :
    (column rows i).bitSteps=0 := tabulate_zero_bits _ (by intro p; rfl)

@[simp] theorem column_arith {P I : ℕ} (rows : CellTables P I) (i : Fin I) :
    (column rows i).arithSites=0 := by
  apply Nat.eq_zero_of_le_zero
  have h := tabulate_arith_le (n:=P) (C:=0) (fun p => (⟨(rows.get p).get i,0,2,0⟩ : Result NatCell))
    (by intro p; rfl)
  simpa [column] using h

theorem column_control_le {P I : ℕ} (rows : CellTables P I) (i : Fin I) :
    (column rows i).controlSites≤15*P+2 := by
  have h := tabulate_control_le (n:=P) (C:=2) (fun p => (⟨(rows.get p).get i,0,2,0⟩ : Result NatCell))
    (by intro p; rfl)
  simpa [column,Nat.mul_comm] using h

/-- The chosen answer retains a stored binary cell; no semantic decode occurs. -/
def minimumCell {P I : ℕ} (rows : CellTables P I) (eligible : List (Fin P)) (i : Fin I) : Result NatCell :=
  let values := column rows i
  let chosen := best values.value eligible
  ⟨match chosen.value with | none => zero | some p => values.value.get p,
    values.bitSteps+chosen.bitSteps,values.controlSites+chosen.controlSites+3,
    values.arithSites+chosen.arithSites⟩

theorem minimumCell_project {P I : ℕ} (rows : CellTables P I) (eligible : List (Fin P)) (i : Fin I) :
    nview (minimumCell rows eligible i).value =
      match ArrayCompositeAlgorithm.best (ArrayCompositeAlgorithm.column (tablesView rows) i) eligible with
      | none => 0 | some p => nview ((rows.get p).get i) := by
  simp only [minimumCell,best_project,column_project]
  cases ArrayCompositeAlgorithm.best (ArrayCompositeAlgorithm.column (tablesView rows) i) eligible <;> simp

theorem minimumCell_control_le {P I : ℕ} (rows : CellTables P I) (eligible : List (Fin P))
    (he : eligible.length≤P) (i : Fin I) : (minimumCell rows eligible i).controlSites≤21*P+6 := by
  have hc := column_control_le rows i
  have hb := best_control (column rows i).value eligible
  simp only [minimumCell]
  omega

theorem minimumCell_arith_le {P I : ℕ} (rows : CellTables P I) (eligible : List (Fin P))
    (he : eligible.length≤P) (i : Fin I) : (minimumCell rows eligible i).arithSites≤P := by
  have hb := best_arith_le (column rows i).value eligible
  simpa only [minimumCell,column_arith,zero_add] using hb.trans he

theorem minimumCell_price {P I X B : ℕ} (rows : CellTables P I) (eligible : List (Fin P))
    (hrows : ∀ p i, nview ((rows.get p).get i)≤X) (hX : X.size≤B) (i : Fin I) :
    (minimumCell rows eligible i).bitSteps≤unit B*(minimumCell rows eligible i).arithSites := by
  have hb := best_price (column rows i).value
    (fun p => by simpa using (Nat.size_le_size (hrows p i)).trans hX) eligible
  simpa only [minimumCell,column_bits,column_arith,zero_add] using hb

theorem minimumCell_bound {P I X : ℕ} (rows : CellTables P I) (eligible : List (Fin P))
    (hrows : ∀ p i, nview ((rows.get p).get i)≤X) (i : Fin I) :
    nview (minimumCell rows eligible i).value≤X := by
  simp only [minimumCell]
  cases (best (column rows i).value eligible).value with
  | none => simp
  | some p => simpa using hrows p i

/-- Eligibility is generated once, followed by eager joint column/minimum passes. -/
def minima {P I : ℕ} (rows : CellTables P I) (remaining : Flags P) : Result (Counts I) :=
  let eligible := indices remaining
  let output := tabulate (minimumCell rows eligible.value)
  ⟨output.value,eligible.bitSteps+output.bitSteps,eligible.controlSites+output.controlSites+1,
    eligible.arithSites+output.arithSites⟩

theorem minima_project {P I : ℕ} (rows : CellTables P I) (remaining : Flags P) :
    projectCounts (minima rows remaining).value = ArrayCompositeAlgorithm.minima (tablesView rows) remaining := by
  change projectCounts (tabulate (minimumCell rows (indices remaining).value)).value = _
  rw [tabulate_value]
  apply Vector.ext
  intro i hi
  simp only [projectCounts,Vector.getElem_map,Vector.getElem_ofFn,minimumCell_project,
    ArrayCompositeAlgorithm.minima,indices_value,DenseControllerExecution.indices_value]
  cases ArrayCompositeAlgorithm.best (ArrayCompositeAlgorithm.column (tablesView rows) ⟨i,hi⟩)
    (ArrayCompositeAlgorithm.indices remaining) <;> simp

theorem minima_control_le {P I : ℕ} (rows : CellTables P I) (remaining : Flags P) :
    (minima rows remaining).controlSites≤64*(P*I+P+I+1) := by
  have ho := tabulate_control_le (minimumCell rows (indices remaining).value)
    (fun i => minimumCell_control_le rows _ (indices_length_le remaining) i)
  simp only [minima,indices_control,DenseControllerExecution.indices_sites]
  nlinarith

theorem minima_arith_le {P I : ℕ} (rows : CellTables P I) (remaining : Flags P) :
    (minima rows remaining).arithSites≤P*I := by
  have ho := tabulate_arith_le (minimumCell rows (indices remaining).value)
    (fun i => minimumCell_arith_le rows _ (indices_length_le remaining) i)
  simpa only [minima,indices_arith,zero_add,Nat.mul_comm] using ho

theorem minima_price {P I X B : ℕ} (rows : CellTables P I) (remaining : Flags P)
    (hrows : ∀ p i, nview ((rows.get p).get i)≤X) (hX : X.size≤B) :
    (minima rows remaining).bitSteps≤unit B*(minima rows remaining).arithSites := by
  have ho := tabulate_price (minimumCell rows (indices remaining).value)
    (fun i => minimumCell_price rows _ hrows hX i)
  simpa only [minima,indices_bitSteps,indices_arith,zero_add] using ho

theorem minima_bound {P I X : ℕ} (rows : CellTables P I) (remaining : Flags P)
    (hrows : ∀ p i, nview ((rows.get p).get i)≤X) (i : Fin I) :
    nview ((minima rows remaining).value.get i)≤X := by
  simpa [minima,tabulate] using minimumCell_bound rows (indices remaining).value hrows i

theorem scanTotals_arith_le_control {n : ℕ} {α : Type*} (stored : Vector (Result α) n)
    (h : ∀ i, (stored.get i).arithSites≤(stored.get i).controlSites) (is : List (Fin n)) :
    (scanTotals stored is).arithSites≤(scanTotals stored is).controlSites := by
  induction is with
  | nil => simp [scanTotals]
  | cons i is ih =>
    have hi := h i
    simp only [scanTotals]
    omega

theorem tabulate_arith_le_control {n : ℕ} {α : Type*} (f : Fin n → Result α)
    (h : ∀ i, (f i).arithSites≤(f i).controlSites) :
    (tabulate f).arithSites≤(tabulate f).controlSites := by
  have hs := scanTotals_arith_le_control (Vector.ofFn f) (by simpa using h) (List.finRange n)
  simp only [tabulate]
  omega

theorem score_arith_le_control {I : ℕ} (active : Flags I) (row : Counts I) :
    (score active row).arithSites≤(score active row).controlSites := by
  rw [score_arith,score_control,DenseControllerExecution.score_sites]
  omega

theorem scores_arith_le_control {P I : ℕ} (active : Flags I) (rows : CellTables P I) :
    (scores active rows).arithSites≤(scores active rows).controlSites := by
  apply tabulate_arith_le_control
  intro p
  have h := score_arith_le_control active (rows.get p)
  simp only
  omega

theorem best_arith_le_control {P : ℕ} (values : Counts P) (ps : List (Fin P)) :
    (best values ps).arithSites≤(best values ps).controlSites := by
  have h := best_arith_le values ps
  rw [best_control]
  omega

theorem choose_arith_le_control {P : ℕ} (remaining : Flags P) (values : Counts P) :
    (choose remaining values).arithSites≤(choose remaining values).controlSites := by
  have h := best_arith_le_control values (indices remaining).value
  simp only [choose,indices_arith,zero_add]
  omega

theorem minimumCell_arith_le_control {P I : ℕ} (rows : CellTables P I)
    (eligible : List (Fin P)) (i : Fin I) :
    (minimumCell rows eligible i).arithSites≤(minimumCell rows eligible i).controlSites := by
  have h := best_arith_le_control (column rows i).value eligible
  simp only [minimumCell,column_arith,zero_add]
  omega

theorem minima_arith_le_control {P I : ℕ} (rows : CellTables P I) (remaining : Flags P) :
    (minima rows remaining).arithSites≤(minima rows remaining).controlSites := by
  have h := tabulate_arith_le_control (minimumCell rows (indices remaining).value)
    (fun i => minimumCell_arith_le_control rows _ i)
  simp only [minima,indices_arith,zero_add]
  omega




open ArrayCompositeAlgorithm
open scoped BigOperators
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

/-- Each eligible position increments a maintained binary scalar by the literal one. -/
def populationScan {P : ℕ} (remaining : Flags P) : List (Fin P) → Result NatCell
  | [] => ⟨zero,0,1,0⟩
  | p::ps =>
    let tail := populationScan remaining ps
    if remaining.get p then
      let out := add one tail.value
      ⟨out.value,tail.bitSteps+out.bitSteps,tail.controlSites+5,tail.arithSites+1⟩
    else ⟨tail.value,tail.bitSteps,tail.controlSites+5,tail.arithSites⟩

theorem populationScan_project {P : ℕ} (remaining : Flags P) (ps : List (Fin P)) :
    nview (populationScan remaining ps).value =
      (ps.filter (fun p => remaining.get p)).length := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    cases h : remaining.get p <;> simp [populationScan,h,ih,Nat.add_comm]

theorem populationScan_control {P : ℕ} (remaining : Flags P) (ps : List (Fin P)) :
    (populationScan remaining ps).controlSites = 5*ps.length+1 := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    cases h : remaining.get p <;> simp [populationScan,h,ih] <;> omega

theorem populationScan_arith {P : ℕ} (remaining : Flags P) (ps : List (Fin P)) :
    (populationScan remaining ps).arithSites =
      (ps.filter (fun p => remaining.get p)).length := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    cases h : remaining.get p <;> simp [populationScan,h,ih]

theorem populationScan_bound {P : ℕ} (remaining : Flags P) (ps : List (Fin P)) :
    nview (populationScan remaining ps).value ≤ ps.length := by
  rw [populationScan_project]
  exact List.length_filter_le _ _

theorem populationScan_price {P B : ℕ} (remaining : Flags P) (ps : List (Fin P))
    (hone : 1≤B) (hsize : ps.length.size≤B) :
    (populationScan remaining ps).bitSteps ≤ unit B*(populationScan remaining ps).arithSites := by
  induction ps with
  | nil => simp [populationScan]
  | cons p ps ih =>
    have htail : ps.length.size≤B := (Nat.size_le_size (by simp : ps.length≤(p::ps).length)).trans hsize
    have ht := ih htail
    have ha := add_price B one (populationScan remaining ps).value
      (by simpa using hone) ((Nat.size_le_size (populationScan_bound remaining ps)).trans htail)
    cases h : remaining.get p
    · simpa only [populationScan,h,Bool.false_eq_true,if_false] using ht
    · simp only [populationScan,h,if_true]
      nlinarith

def population {P : ℕ} (remaining : Flags P) : Result NatCell :=
  let out := populationScan remaining (List.finRange P)
  ⟨out.value,out.bitSteps,out.controlSites+4*P+1,out.arithSites⟩

theorem population_project {P : ℕ} (remaining : Flags P) :
    nview (population remaining).value = ArrayCompositeAlgorithm.population remaining := by
  simp [population,populationScan_project,ArrayCompositeAlgorithm.population,ArrayCompositeAlgorithm.indices]

theorem population_control {P : ℕ} (remaining : Flags P) :
    (population remaining).controlSites = 9*P+2 := by
  simp [population,populationScan_control]; omega

theorem population_arith_le {P : ℕ} (remaining : Flags P) :
    (population remaining).arithSites ≤ P := by
  simpa [population,populationScan_arith] using
    List.length_filter_le (fun p => remaining.get p) (List.finRange P)

theorem population_bound {P : ℕ} (remaining : Flags P) :
    nview (population remaining).value ≤ P := by
  simpa [population] using populationScan_bound remaining (List.finRange P)

theorem population_price {P B : ℕ} (remaining : Flags P) (hone : 1≤B) (hsize : P.size≤B) :
    (population remaining).bitSteps ≤ unit B*(population remaining).arithSites := by
  exact populationScan_price remaining _ hone (by simpa using hsize)

/-- Width obligations for the input cells and the two transient products.
This certificate is erased; the execution below never consults it. -/
structure FinishFits {I : ℕ} (B : ℕ) (base minima : Counts I) (lam m : NatCell) : Prop where
  baseWidth : ∀ i, (nview (base.get i)).size≤B
  minimaWidth : ∀ i, (nview (minima.get i)).size≤B
  lamWidth : (nview lam).size≤B
  poolWidth : (nview m).size≤B
  left : ∀ i, (nview lam*nview (base.get i)).size≤B
  right : ∀ i, (nview m*nview (minima.get i)).size≤B

/-- A value cap also bounds every transient product used by finish. -/
theorem finishFits_of_cap {I X B : ℕ} (base minima : Counts I) (lam m : NatCell)
    (hX : 1≤X) (hsize : (X*X).size≤B)
    (hbase : ∀ i, nview (base.get i)≤X) (hmin : ∀ i, nview (minima.get i)≤X)
    (hlam : nview lam≤X) (hm : nview m≤X) : FinishFits B base minima lam m := by
  have hsq : X≤X*X := by nlinarith
  have hc : X.size≤B := (Nat.size_le_size hsq).trans hsize
  exact ⟨fun i => (Nat.size_le_size (hbase i)).trans hc,
    fun i => (Nat.size_le_size (hmin i)).trans hc,
    (Nat.size_le_size hlam).trans hc,(Nat.size_le_size hm).trans hc,
    fun i => (Nat.size_le_size (Nat.mul_le_mul hlam (hbase i))).trans hsize,
    fun i => (Nat.size_le_size (Nat.mul_le_mul hm (hmin i))).trans hsize⟩

/-- The two products and strict comparison all consume stored binary cells. -/
def affirmativeCell (active : Bool) (base minima lam m : NatCell) : Result Bool :=
  let left := mul lam base
  let right := mul m minima
  let test := lt left.value right.value
  ⟨active && test.value,left.bitSteps+right.bitSteps+test.bitSteps,8,3⟩

theorem affirmativeCell_project (active : Bool) (base minima lam m : NatCell) :
    (affirmativeCell active base minima lam m).value =
      (active && decide (nview lam*nview base<nview m*nview minima)) := by
  simp only [affirmativeCell,lt_value,mul_nview]

theorem affirmativeCell_price {B : ℕ} (active : Bool) (base minima lam m : NatCell)
    (hbase : (nview base).size≤B) (hmin : (nview minima).size≤B)
    (hlam : (nview lam).size≤B) (hm : (nview m).size≤B)
    (hl : (nview lam*nview base).size≤B) (hr : (nview m*nview minima).size≤B) :
    (affirmativeCell active base minima lam m).bitSteps ≤
      unit B*(affirmativeCell active base minima lam m).arithSites := by
  have ha := mul_price B lam base hlam hbase
  have hb := mul_price B m minima hm hmin
  have ht := lt_price B (mul lam base).value (mul m minima).value
    (by simpa using hl) (by simpa using hr)
  simp only [affirmativeCell]
  omega

def affirmative {I : ℕ} (active : Flags I) (base minima : Counts I) (lam m : NatCell) :
    Result (Flags I) :=
  tabulate (fun i => affirmativeCell (active.get i) (base.get i) (minima.get i) lam m)

theorem affirmative_project {I : ℕ} (active : Flags I) (base minima : Counts I) (lam m : NatCell) :
    (affirmative active base minima lam m).value =
      ArrayCompositeAlgorithm.affirmative active (projectCounts base) (projectCounts minima) (nview lam) (nview m) := by
  rw [affirmative,tabulate_value]
  apply Vector.ext
  intro i hi
  simp [ArrayCompositeAlgorithm.affirmative,affirmativeCell_project,projectCounts]

theorem affirmative_control {I : ℕ} (active : Flags I) (base minima : Counts I) (lam m : NatCell) :
    (affirmative active base minima lam m).controlSites ≤ 21*I+2 := by
  have h := tabulate_control_le (C:=8)
    (fun i => affirmativeCell (active.get i) (base.get i) (minima.get i) lam m)
    (by intro i; rfl)
  simpa [affirmative,Nat.mul_comm] using h

theorem affirmative_arith {I : ℕ} (active : Flags I) (base minima : Counts I) (lam m : NatCell) :
    (affirmative active base minima lam m).arithSites ≤ 3*I := by
  have h := tabulate_arith_le (C:=3)
    (fun i => affirmativeCell (active.get i) (base.get i) (minima.get i) lam m)
    (by intro i; rfl)
  simpa [affirmative,Nat.mul_comm] using h

theorem affirmative_price {I B : ℕ} (active : Flags I) (base minima : Counts I) (lam m : NatCell)
    (hfit : FinishFits B base minima lam m) :
    (affirmative active base minima lam m).bitSteps ≤ unit B*(affirmative active base minima lam m).arithSites := by
  apply tabulate_price
  intro i
  exact affirmativeCell_price _ _ _ _ _ (hfit.baseWidth i) (hfit.minimaWidth i)
    hfit.lamWidth hfit.poolWidth (hfit.left i) (hfit.right i)

/-- The zero and order tests execute through subtraction-and-borrow circuits. -/
def retainCell (active pairMarked : Bool) (base minima lam m : NatCell) : Result Bool :=
  let left := mul m minima
  let right := mul lam base
  let order := le left.value right.value
  let nonzero := lt zero minima
  ⟨active && nonzero.value && order.value && !pairMarked,
    left.bitSteps+right.bitSteps+order.bitSteps+nonzero.bitSteps,14,4⟩

theorem retainCell_project (active pairMarked : Bool) (base minima lam m : NatCell) :
    (retainCell active pairMarked base minima lam m).value =
      (active && decide (nview minima≠0) &&
        decide (nview m*nview minima≤nview lam*nview base) && !pairMarked) := by
  simp only [retainCell,le_value,lt_value,mul_nview,zero_nview]
  simp only [Nat.pos_iff_ne_zero]

theorem retainCell_price {B : ℕ} (active pairMarked : Bool) (base minima lam m : NatCell)
    (hbase : (nview base).size≤B) (hmin : (nview minima).size≤B)
    (hlam : (nview lam).size≤B) (hm : (nview m).size≤B)
    (hl : (nview lam*nview base).size≤B) (hr : (nview m*nview minima).size≤B) :
    (retainCell active pairMarked base minima lam m).bitSteps ≤
      unit B*(retainCell active pairMarked base minima lam m).arithSites := by
  have ha := mul_price B m minima hm hmin
  have hb := mul_price B lam base hlam hbase
  have ht := le_price B (mul m minima).value (mul lam base).value
    (by simpa using hr) (by simpa using hl)
  have hz := lt_price B zero minima (by simp) hmin
  simp only [retainCell]
  omega

def retain {I Q : ℕ} (owner : Owners I Q) (active : Flags I) (pairMarks : Flags Q)
    (base minima : Counts I) (lam m : NatCell) : Result (Flags I) :=
  tabulate (fun i => retainCell (active.get i) (pairMarks.get (owner.get i))
    (base.get i) (minima.get i) lam m)

theorem retain_project {I Q : ℕ} (owner : Owners I Q) (active : Flags I) (pairMarks : Flags Q)
    (base minima : Counts I) (lam m : NatCell) :
    (retain owner active pairMarks base minima lam m).value =
      ArrayCompositeAlgorithm.retain owner active pairMarks (projectCounts base) (projectCounts minima) (nview lam) (nview m) := by
  rw [retain,tabulate_value]
  apply Vector.ext
  intro i hi
  simp [ArrayCompositeAlgorithm.retain,retainCell_project,projectCounts]

theorem retain_control {I Q : ℕ} (owner : Owners I Q) (active : Flags I) (pairMarks : Flags Q)
    (base minima : Counts I) (lam m : NatCell) :
    (retain owner active pairMarks base minima lam m).controlSites ≤ 27*I+2 := by
  have h := tabulate_control_le (C:=14)
    (fun i => retainCell (active.get i) (pairMarks.get (owner.get i)) (base.get i) (minima.get i) lam m)
    (by intro i; rfl)
  simpa [retain,Nat.mul_comm] using h

theorem retain_arith {I Q : ℕ} (owner : Owners I Q) (active : Flags I) (pairMarks : Flags Q)
    (base minima : Counts I) (lam m : NatCell) :
    (retain owner active pairMarks base minima lam m).arithSites ≤ 4*I := by
  have h := tabulate_arith_le (C:=4)
    (fun i => retainCell (active.get i) (pairMarks.get (owner.get i)) (base.get i) (minima.get i) lam m)
    (by intro i; rfl)
  simpa [retain,Nat.mul_comm] using h

theorem retain_price {I Q B : ℕ} (owner : Owners I Q) (active : Flags I) (pairMarks : Flags Q)
    (base minima : Counts I) (lam m : NatCell) (hfit : FinishFits B base minima lam m) :
    (retain owner active pairMarks base minima lam m).bitSteps ≤
      unit B*(retain owner active pairMarks base minima lam m).arithSites := by
  apply tabulate_price
  intro i
  exact retainCell_price _ _ _ _ _ _ (hfit.baseWidth i) (hfit.minimaWidth i)
    hfit.lamWidth hfit.poolWidth (hfit.left i) (hfit.right i)

/-- An affirmative cell performs one indexed Boolean write; all writes finish
before the separate survivor pass begins. -/
def markScan {I Q : ℕ} (owner : Owners I Q) (yes : Flags I) :
    Flags Q → List (Fin I) → Result (Flags Q)
  | marked,[] => ⟨marked,0,1,0⟩
  | marked,i::is =>
    let flag := yes.get i
    let updated := if flag then ArrayCompositeAlgorithm.put marked (owner.get i) true else marked
    let tail := markScan owner yes updated is
    ⟨tail.value,tail.bitSteps,tail.controlSites+5,tail.arithSites⟩

theorem markScan_project {I Q : ℕ} (owner : Owners I Q) (yes : Flags I)
    (marked : Flags Q) (is : List (Fin I)) :
    (markScan owner yes marked is).value = ArrayCompositeAlgorithm.markScan owner yes marked is := by
  induction is generalizing marked with
  | nil => rfl
  | cons i is ih => simp only [markScan,ArrayCompositeAlgorithm.markScan]; exact ih _

theorem markScan_control {I Q : ℕ} (owner : Owners I Q) (yes : Flags I)
    (marked : Flags Q) (is : List (Fin I)) :
    (markScan owner yes marked is).controlSites = 5*is.length+1 := by
  induction is generalizing marked with
  | nil => rfl
  | cons i is ih => simp [markScan,ih]; omega

theorem markScan_bitSteps {I Q : ℕ} (owner : Owners I Q) (yes : Flags I)
    (marked : Flags Q) (is : List (Fin I)) :
    (markScan owner yes marked is).bitSteps = 0 := by
  induction is generalizing marked with
  | nil => rfl
  | cons i is ih => simp [markScan,ih]

theorem markScan_arith {I Q : ℕ} (owner : Owners I Q) (yes : Flags I)
    (marked : Flags Q) (is : List (Fin I)) :
    (markScan owner yes marked is).arithSites = 0 := by
  induction is generalizing marked with
  | nil => rfl
  | cons i is ih => simp [markScan,ih]

def mark {I Q : ℕ} (owner : Owners I Q) (yes : Flags I) (marked : Flags Q) : Result (Flags Q) :=
  let out := markScan owner yes marked (List.finRange I)
  ⟨out.value,out.bitSteps,out.controlSites+4*I+1,out.arithSites⟩

theorem mark_project {I Q : ℕ} (owner : Owners I Q) (yes : Flags I) (marked : Flags Q) :
    (mark owner yes marked).value = ArrayCompositeAlgorithm.mark owner yes marked := by
  exact markScan_project owner yes marked _

theorem mark_control {I Q : ℕ} (owner : Owners I Q) (yes : Flags I) (marked : Flags Q) :
    (mark owner yes marked).controlSites = 9*I+2 := by
  simp [mark,markScan_control]; omega

theorem mark_bitSteps {I Q : ℕ} (owner : Owners I Q) (yes : Flags I) (marked : Flags Q) :
    (mark owner yes marked).bitSteps = 0 := markScan_bitSteps owner yes marked _

theorem mark_arith {I Q : ℕ} (owner : Owners I Q) (yes : Flags I) (marked : Flags Q) :
    (mark owner yes marked).arithSites = 0 := markScan_arith owner yes marked _

/-- All affirmative cells are stored, their flags are scattered sequentially,
and only then is the survivor vector produced. -/
def finish {I Q : ℕ} (owner : Owners I Q) (active : Flags I) (marked : Flags Q)
    (base minima : Counts I) (lam m : NatCell) : Result (ArrayCompositeAlgorithm.Result I Q) :=
  let yes := affirmative active base minima lam m
  let marked' := mark owner yes.value marked
  let kept := retain owner active marked'.value base minima lam m
  ⟨⟨kept.value,marked'.value⟩,yes.bitSteps+marked'.bitSteps+kept.bitSteps,
    yes.controlSites+marked'.controlSites+kept.controlSites+4,
    yes.arithSites+marked'.arithSites+kept.arithSites⟩

theorem finish_project {I Q : ℕ} (owner : Owners I Q) (active : Flags I) (marked : Flags Q)
    (base minima : Counts I) (lam m : NatCell) :
    (finish owner active marked base minima lam m).value =
      ArrayCompositeAlgorithm.finish owner active marked (projectCounts base) (projectCounts minima) (nview lam) (nview m) := by
  simp [finish,ArrayCompositeAlgorithm.finish,affirmative_project,mark_project,retain_project]

theorem finish_control {I Q : ℕ} (owner : Owners I Q) (active : Flags I) (marked : Flags Q)
    (base minima : Counts I) (lam m : NatCell) :
    (finish owner active marked base minima lam m).controlSites ≤ 57*I+10 := by
  have ha := affirmative_control active base minima lam m
  have hm := mark_control owner (affirmative active base minima lam m).value marked
  have hr := retain_control owner active (mark owner (affirmative active base minima lam m).value marked).value base minima lam m
  simp only [finish]
  omega

theorem finish_arith {I Q : ℕ} (owner : Owners I Q) (active : Flags I) (marked : Flags Q)
    (base minima : Counts I) (lam m : NatCell) :
    (finish owner active marked base minima lam m).arithSites ≤ 7*I := by
  have ha := affirmative_arith active base minima lam m
  have hm := mark_arith owner (affirmative active base minima lam m).value marked
  have hr := retain_arith owner active (mark owner (affirmative active base minima lam m).value marked).value base minima lam m
  simp only [finish]
  omega

theorem finish_price {I Q B : ℕ} (owner : Owners I Q) (active : Flags I) (marked : Flags Q)
    (base minima : Counts I) (lam m : NatCell) (hfit : FinishFits B base minima lam m) :
    (finish owner active marked base minima lam m).bitSteps ≤
      unit B*(finish owner active marked base minima lam m).arithSites := by
  have ha := affirmative_price active base minima lam m hfit
  have hm := mark_bitSteps owner (affirmative active base minima lam m).value marked
  have hr := retain_price owner active (mark owner (affirmative active base minima lam m).value marked).value base minima lam m hfit
  have hma := mark_arith owner (affirmative active base minima lam m).value marked
  simp only [finish,hm,hma,Nat.mul_add]
  omega

/-- A single linear control/primitive-site allowance for the actual finish loops. -/
theorem finish_sites_le {I Q : ℕ} (owner : Owners I Q) (active : Flags I) (marked : Flags Q)
    (base minima : Counts I) (lam m : NatCell) :
    (finish owner active marked base minima lam m).controlSites+
      (finish owner active marked base minima lam m).arithSites ≤ 64*I+10 := by
  have hc := finish_control owner active marked base minima lam m
  have ha := finish_arith owner active marked base minima lam m
  omega

/-- The current pool is counted once and that same maintained binary scalar
is used in both final certification passes. -/
theorem population_finish_sites_le {P I Q : ℕ} (remaining : Flags P)
    (owner : Owners I Q) (active : Flags I) (marked : Flags Q)
    (base minima : Counts I) (lam : NatCell) :
    (population remaining).controlSites+(population remaining).arithSites+
      (finish owner active marked base minima lam (population remaining).value).controlSites+
      (finish owner active marked base minima lam (population remaining).value).arithSites ≤
        64*(P+I+1) := by
  have hp := population_control remaining
  have hpa := population_arith_le remaining
  have hf := finish_sites_le owner active marked base minima lam (population remaining).value
  omega

theorem finish_price_of_cap {I Q X B : ℕ} (owner : Owners I Q) (active : Flags I) (marked : Flags Q)
    (base minima : Counts I) (lam m : NatCell)
    (hX : 1≤X) (hsize : (X*X).size≤B)
    (hbase : ∀ i, nview (base.get i)≤X) (hmin : ∀ i, nview (minima.get i)≤X)
    (hlam : nview lam≤X) (hm : nview m≤X) :
    (finish owner active marked base minima lam m).bitSteps ≤
      unit B*(finish owner active marked base minima lam m).arithSites := by
  exact finish_price owner active marked base minima lam m
    (finishFits_of_cap base minima lam m hX hsize hbase hmin hlam hm)

#eval let out := population (Vector.ofFn (fun i : Fin 3 => decide (i.val ≠ 1)))
  (nview out.value,out.bitSteps,out.controlSites,out.arithSites)





open ArrayCompositeAlgorithm (Flags Owners)

/-- The public prime label is bounded control data; arithmetic uses its stored
canonical binary cell. Its equality proof is erased. -/
structure Prime where
  control : ℕ
  cell : NatCell
  same : nview cell=control

abbrev Primes (P : ℕ)  :=  Vector Prime P

def projectPrimes {P : ℕ} (primes : Primes P) : ArrayCompositeAlgorithm.Counts P  :=
  primes.map Prime.control

structure Table (I : ℕ) (Payload : Type*) where
  counts : Counts I
  payload : Payload
  work : ℕ

structure Oracle (I : ℕ) (Payload : Type*) where
  table : List ℕ → ℕ → Flags I → Table I Payload

def Table.project {I : ℕ} {Payload : Type*} (table : Table I Payload) :
    CountedArrayComposite.Table I Payload  :=  ⟨projectCounts table.counts,table.payload,table.work⟩

def Oracle.project {I : ℕ} {Payload : Type*} (O : Oracle I Payload) :
    CountedArrayComposite.Oracle I Payload  :=
  ⟨fun selected candidate active => (O.table selected candidate active).project⟩

structure Call (I : ℕ) (Payload : Type*) where
  factors : ArrayCompositeAlgorithm.FactorCall I
  result : Table I Payload

def Call.project {I : ℕ} {Payload : Type*} (call : Call I Payload) :
    CountedArrayComposite.Call I Payload  :=  ⟨call.factors,call.result.project⟩

def projectCalls {I : ℕ} {Payload : Type*} (calls : List (Call I Payload))  :=  calls.map Call.project

abbrev Cache (P I : ℕ) (Payload : Type*)  :=  Vector (Option (Table I Payload)) P

def projectCache {P I : ℕ} {Payload : Type*} (cache : Cache P I Payload) :
    CountedArrayComposite.Cache P I Payload  :=  cache.map (Option.map Table.project)

/-- Exactly one producer dispatch per eligible slot; subsequent passes use
this stored result, including its original payload and binary backend work. -/
def evaluateOnce {P I : ℕ} {Payload : Type*} (O : Oracle I Payload)
    (active : Flags I) (primes : Primes P) (remaining : Flags P) (selected : List ℕ) :
    Result (Cache P I Payload)  :=
  tabulate (fun p =>
    if remaining.get p then ⟨some (O.table selected (primes.get p).control active),0,5,0⟩
    else ⟨none,0,3,0⟩)

/-- Empty rows are explicit zero cells; successful rows retain cache references. -/
def cacheRows {P I : ℕ} {Payload : Type*} (cache : Cache P I Payload) :
    Result (Vector (Counts I) P)  :=
  tabulate (fun p => match cache.get p with
    | none => ⟨Vector.replicate I zero,0,I+3,0⟩
    | some result => ⟨result.counts,0,3,0⟩)

def cacheCallsFrom {P I : ℕ} {Payload : Type*} (cache : Cache P I Payload)
    (active : Flags I) (primes : Primes P) (selected : List ℕ) :
    List (Fin P) → Result (List (Call I Payload))
  | [] => ⟨[],0,1,0⟩
  | p :: ps =>
    let tail := cacheCallsFrom cache active primes selected ps
    match cache.get p with
    | none => ⟨tail.value,tail.bitSteps,tail.controlSites+5,tail.arithSites⟩
    | some table =>
      ⟨⟨⟨selected,(primes.get p).control,active⟩,table⟩::tail.value,
        tail.bitSteps,tail.controlSites+5,tail.arithSites⟩

def cacheCalls {P I : ℕ} {Payload : Type*} (cache : Cache P I Payload)
    (active : Flags I) (primes : Primes P) (selected : List ℕ) : Result (List (Call I Payload))  :=
  let out := cacheCallsFrom cache active primes selected (List.finRange P)
  ⟨out.value,out.bitSteps,out.controlSites+4*P+1,out.arithSites⟩

/-- Resource annotations are ghost natural counters; this traversal retains
producer work once and charges its bounded public control operations. -/
def sumWork {I : ℕ} {Payload : Type*} : List (Call I Payload) → Result ℕ
  | [] => ⟨0,0,1,0⟩
  | call :: calls =>
    let tail := sumWork calls
    ⟨call.result.work+tail.value,tail.bitSteps,tail.controlSites+4,tail.arithSites⟩

def append {α : Type*} : List α → List α → Result (List α)
  | [],ys => ⟨ys,0,1,0⟩
  | x :: xs,ys =>
    let tail := append xs ys
    ⟨x::tail.value,tail.bitSteps,tail.controlSites+3,tail.arithSites⟩

def put {P : ℕ} (remaining : Flags P) (p : Fin P) : Result (Flags P)  :=
  ⟨ArrayCompositeAlgorithm.put remaining p false,0,2,0⟩

def copyRow {I : ℕ} (row : Counts I) : Result (Counts I)  :=
  tabulate (fun i => copy (row.get i))

structure GreedyResult (P I : ℕ) (Payload : Type*) where
  modulus : NatCell
  remaining : Flags P
  base : Counts I
  selected : List ℕ
  calls : List (Call I Payload)
  backendWork : ℕ
  controllerVisits : ℕ

def GreedyResult.project {P I : ℕ} {Payload : Type*} (out : GreedyResult P I Payload) :
    CountedArrayComposite.GreedyResult P I Payload  :=
  ⟨nview out.modulus,out.remaining,projectCounts out.base,out.selected,projectCalls out.calls,
    out.backendWork,out.controllerVisits⟩

def greedyExec {P I : ℕ} {Payload : Type*} (O : Oracle I Payload)
    (active : Flags I) (primes : Primes P) :
    ℕ → NatCell → Flags P → Counts I → List ℕ → Result (GreedyResult P I Payload)
  | 0,d,remaining,base,selected => ⟨⟨d,remaining,base,selected,[],0,0⟩,0,1,0⟩
  | k+1,d,remaining,base,selected =>
    let cache := evaluateOnce O active primes remaining selected
    let rows := cacheRows cache.value
    let scalarScores := scores active rows.value
    let chosen := choose remaining scalarScores.value
    let batchBits := cache.bitSteps+rows.bitSteps+scalarScores.bitSteps+chosen.bitSteps
    let batchControl := cache.controlSites+rows.controlSites+scalarScores.controlSites+chosen.controlSites+4
    let batchArith := cache.arithSites+rows.arithSites+scalarScores.arithSites+chosen.arithSites
    match chosen.value with
    | none => ⟨⟨d,remaining,base,selected,[],0,CountedArrayComposite.batchVisits P I⟩,
        batchBits,batchControl+1,batchArith⟩
    | some p =>
      let calls := cacheCalls cache.value active primes selected
      let prime := primes.get p
      let d' := mul d prime.cell
      let remaining' := put remaining p
      let base' := copyRow (rows.value.get p)
      let selected' := append selected [prime.control]
      let tail := greedyExec O active primes k d'.value remaining'.value base'.value selected'.value
      let history := append calls.value tail.value.calls
      let work := sumWork calls.value
      ⟨{tail.value with
          calls := history.value
          backendWork := work.value+tail.value.backendWork
          controllerVisits := CountedArrayComposite.batchVisits P I+tail.value.controllerVisits},
        batchBits+calls.bitSteps+d'.bitSteps+remaining'.bitSteps+base'.bitSteps+selected'.bitSteps+
          tail.bitSteps+history.bitSteps+work.bitSteps,
        batchControl+calls.controlSites+d'.controlSites+remaining'.controlSites+base'.controlSites+
          selected'.controlSites+tail.controlSites+history.controlSites+work.controlSites+12,
        batchArith+calls.arithSites+d'.arithSites+remaining'.arithSites+base'.arithSites+
          selected'.arithSites+tail.arithSites+history.arithSites+work.arithSites⟩


@[simp] theorem projectCalls_append {I : ℕ} {Payload : Type*} (xs ys : List (Call I Payload)) :
    projectCalls (xs++ys)=projectCalls xs++projectCalls ys  :=  by simp [projectCalls]

@[simp] theorem projectPrimes_get {P : ℕ} (primes : Primes P) (p : Fin P) :
    (projectPrimes primes).get p=(primes.get p).control  :=  by simp [projectPrimes]

theorem evaluateOnce_project {P I : ℕ} {Payload : Type*} (O : Oracle I Payload)
    (active : Flags I) (primes : Primes P) (remaining : Flags P) (selected : List ℕ) :
    projectCache (evaluateOnce O active primes remaining selected).value =
      CountedArrayComposite.evaluateOnce O.project active (projectPrimes primes) remaining selected  :=  by
  rw [evaluateOnce,tabulate_value]
  apply Vector.ext
  intro p hp
  simp [projectCache,CountedArrayComposite.evaluateOnce,Oracle.project,projectPrimes]
  split <;> rfl

theorem cacheRows_project {P I : ℕ} {Payload : Type*} (cache : Cache P I Payload) :
    tablesView (cacheRows cache).value=(projectCache cache).rows  :=  by
  rw [cacheRows,tabulate_value]
  apply Vector.ext
  intro p hp
  simp only [tablesView,Vector.getElem_map,Vector.getElem_ofFn,CountedArrayComposite.Cache.rows,
    projectCache]
  cases h : cache.get ⟨p,hp⟩ <;> simp [h,Table.project,countsView,projectCounts]

theorem cacheCallsFrom_project {P I : ℕ} {Payload : Type*} (cache : Cache P I Payload)
    (active : Flags I) (primes : Primes P) (selected : List ℕ) (ps : List (Fin P)) :
    projectCalls (cacheCallsFrom cache active primes selected ps).value =
      (projectCache cache).callsFrom active (projectPrimes primes) selected ps  :=  by
  induction ps with
  |nil => rfl
  |cons p ps ih =>
    simp only [cacheCallsFrom,CountedArrayComposite.Cache.callsFrom]
    simp only [projectCache,Vector.get_map]
    simp only [projectCalls,projectCache] at ih
    cases cache.get p <;> simp [projectCalls,Call.project,ih,projectPrimes_get]

theorem cacheCalls_project {P I : ℕ} {Payload : Type*} (cache : Cache P I Payload)
    (active : Flags I) (primes : Primes P) (selected : List ℕ) :
    projectCalls (cacheCalls cache active primes selected).value =
      (projectCache cache).calls active (projectPrimes primes) selected  :=
  cacheCallsFrom_project cache active primes selected _

theorem append_value {α : Type*} (xs ys : List α) : (append xs ys).value=xs++ys  :=  by
  induction xs with
  |nil => rfl
  |cons x xs ih => simp [append,ih]

theorem sumWork_project {I : ℕ} {Payload : Type*} (calls : List (Call I Payload)) :
    (sumWork calls).value=CountedArrayComposite.workSum (projectCalls calls)  :=  by
  induction calls with
  |nil => rfl
  |cons call calls ih => simp [sumWork,projectCalls,Call.project,Table.project,CountedArrayComposite.workSum,ih]

theorem copyRow_project {I : ℕ} (row : Counts I) :
    projectCounts (copyRow row).value=projectCounts row  :=  by
  rw [copyRow,tabulate_value]
  apply Vector.ext
  intro i hi
  simp only [projectCounts,Vector.getElem_map,Vector.getElem_ofFn,copy_nview]
  rfl

theorem greedyExec_project {P I : ℕ} {Payload : Type*} (O : Oracle I Payload)
    (active : Flags I) (primes : Primes P) (k : ℕ) (d : NatCell) (remaining : Flags P)
    (base : Counts I) (selected : List ℕ) :
    (greedyExec O active primes k d remaining base selected).value.project =
      CountedArrayComposite.greedy O.project active (projectPrimes primes) k (nview d) remaining
        (projectCounts base) selected  :=  by
  induction k generalizing d remaining base selected with
  |zero => rfl
  |succ k ih =>
    simp only [greedyExec,CountedArrayComposite.greedy,choose_value,scores_value,
      DenseControllerExecution.choose_value,DenseControllerExecution.scores_value]
    rw [cacheRows_project,evaluateOnce_project]
    split
    · rename_i h
      rw [h]
      rfl
    · rename_i p h
      rw [h]
      have ht := ih (mul d (primes.get p).cell).value (put remaining p).value
        (copyRow ((cacheRows (evaluateOnce O active primes remaining selected).value).value.get p)).value
        (append selected [(primes.get p).control]).value
      simp only [GreedyResult.project] at ht ⊢
      simp only [append_value,projectCalls_append,sumWork_project]
      rw [cacheCalls_project,evaluateOnce_project]
      have hm := congrArg CountedArrayComposite.GreedyResult.modulus ht
      have hr := congrArg CountedArrayComposite.GreedyResult.remaining ht
      have hb := congrArg CountedArrayComposite.GreedyResult.base ht
      have hs := congrArg CountedArrayComposite.GreedyResult.selected ht
      have hc := congrArg CountedArrayComposite.GreedyResult.calls ht
      have hw := congrArg CountedArrayComposite.GreedyResult.backendWork ht
      have hv := congrArg CountedArrayComposite.GreedyResult.controllerVisits ht
      have hrow : projectCounts ((cacheRows (evaluateOnce O active primes remaining selected).value).value.get p)=
          ((CountedArrayComposite.evaluateOnce O.project active (projectPrimes primes) remaining selected).rows).get p := by
        change countsView ((cacheRows (evaluateOnce O active primes remaining selected).value).value.get p)=_
        rw [← tablesView_get,cacheRows_project,evaluateOnce_project]
      simp only [mul_nview,(primes.get p).same,put,copyRow_project,append_value,hrow] at hm hr hb hs hc hw hv
      simp only [put,projectPrimes_get]
      rw [hm,hr,hb,hs,hc,hw,hv]



open ArrayCompositeAlgorithm (Flags Owners)
structure StageResult (P I Q : ℕ) (Payload : Type*) where
  active : Flags I
  marked : Flags Q
  selected : List ℕ
  calls : List (Call I Payload)
  backendWork : ℕ
  controllerVisits : ℕ

def StageResult.project {P I Q : ℕ} {Payload : Type*} (out : StageResult P I Q Payload) :
    CountedArrayComposite.StageResult P I Q Payload  :=
  ⟨out.active,out.marked,out.selected,projectCalls out.calls,out.backendWork,out.controllerVisits⟩

def stageExec {P I Q : ℕ} {Payload : Type*} (O : Oracle I Payload) (owner : Owners I Q)
    (primes : Primes P) (active : Flags I) (marked : Flags Q) (blockSizes : Counts I)
    (remaining : Flags P) (k : ℕ) (lam : NatCell) : Result (StageResult P I Q Payload)  :=
  let chosen := greedyExec O active primes k one remaining blockSizes []
  let cache := evaluateOnce O active primes chosen.value.remaining chosen.value.selected
  let rows := cacheRows cache.value
  let mu := minima rows.value chosen.value.remaining
  let count := population chosen.value.remaining
  let out := finish owner active marked chosen.value.base mu.value lam count.value
  let calls := cacheCalls cache.value active primes chosen.value.selected
  let history := append chosen.value.calls calls.value
  let work := sumWork calls.value
  ⟨⟨out.value.active,out.value.marked,chosen.value.selected,history.value,
      chosen.value.backendWork+work.value,chosen.value.controllerVisits+CountedArrayComposite.finalVisits P I⟩,
    chosen.bitSteps+cache.bitSteps+rows.bitSteps+mu.bitSteps+count.bitSteps+out.bitSteps+
      calls.bitSteps+history.bitSteps+work.bitSteps,
    chosen.controlSites+cache.controlSites+rows.controlSites+mu.controlSites+count.controlSites+
      out.controlSites+calls.controlSites+history.controlSites+work.controlSites+12,
    chosen.arithSites+cache.arithSites+rows.arithSites+mu.arithSites+count.arithSites+
      out.arithSites+calls.arithSites+history.arithSites+work.arithSites⟩

def restartsExec {P I Q : ℕ} {Payload : Type*} (O : Oracle I Payload) (owner : Owners I Q)
    (primes : Primes P) (blockSizes : Counts I) (remaining : Flags P) (k : ℕ) (lam : NatCell) :
    ℕ → Flags I → Flags Q → Result (StageResult P I Q Payload)
  | 0,active,marked => ⟨⟨active,marked,[],[],0,0⟩,0,1,0⟩
  | n+1,active,marked =>
    let one := stageExec O owner primes active marked blockSizes remaining k lam
    let tail := restartsExec O owner primes blockSizes remaining k lam n one.value.active one.value.marked
    let history := append one.value.calls tail.value.calls
    ⟨{tail.value with
        calls := history.value
        backendWork := one.value.backendWork+tail.value.backendWork
        controllerVisits := one.value.controllerVisits+tail.value.controllerVisits},
      one.bitSteps+tail.bitSteps+history.bitSteps,
      one.controlSites+tail.controlSites+history.controlSites+5,
      one.arithSites+tail.arithSites+history.arithSites⟩


theorem stageExec_project {P I Q : ℕ} {Payload : Type*} (O : Oracle I Payload) (owner : Owners I Q)
    (primes : Primes P) (active : Flags I) (marked : Flags Q) (blockSizes : Counts I)
    (remaining : Flags P) (k : ℕ) (lam : NatCell) :
    (stageExec O owner primes active marked blockSizes remaining k lam).value.project =
      CountedArrayComposite.stage O.project owner (projectPrimes primes) active marked
        (projectCounts blockSizes) remaining k (nview lam) := by
  have hg:=greedyExec_project O active primes k one remaining blockSizes []
  have hr:=congrArg CountedArrayComposite.GreedyResult.remaining hg
  have hb:=congrArg CountedArrayComposite.GreedyResult.base hg
  have hs:=congrArg CountedArrayComposite.GreedyResult.selected hg
  have hc:=congrArg CountedArrayComposite.GreedyResult.calls hg
  have hw:=congrArg CountedArrayComposite.GreedyResult.backendWork hg
  have hv:=congrArg CountedArrayComposite.GreedyResult.controllerVisits hg
  simp only [GreedyResult.project,one_nview] at hr hb hs hc hw hv
  simp only [stageExec,StageResult.project,CountedArrayComposite.stage,append_value,
    projectCalls_append,sumWork_project,finish_project,minima_project,population_project]
  rw [cacheRows_project,evaluateOnce_project,cacheCalls_project,evaluateOnce_project]
  rw [hr,hb,hs,hc,hw,hv]

theorem restartsExec_project {P I Q : ℕ} {Payload : Type*} (O : Oracle I Payload) (owner : Owners I Q)
    (primes : Primes P) (blockSizes : Counts I) (remaining : Flags P) (k : ℕ) (lam : NatCell)
    (n : ℕ) (active : Flags I) (marked : Flags Q) :
    (restartsExec O owner primes blockSizes remaining k lam n active marked).value.project =
      CountedArrayComposite.restarts O.project owner (projectPrimes primes) (projectCounts blockSizes)
        remaining k (nview lam) n active marked := by
  induction n generalizing active marked with
  |zero=>rfl
  |succ n ih=>
    have hs:=stageExec_project O owner primes active marked blockSizes remaining k lam
    have ha:=congrArg CountedArrayComposite.StageResult.active hs
    have hm:=congrArg CountedArrayComposite.StageResult.marked hs
    have hc:=congrArg CountedArrayComposite.StageResult.calls hs
    have hw:=congrArg CountedArrayComposite.StageResult.backendWork hs
    have hv:=congrArg CountedArrayComposite.StageResult.controllerVisits hs
    simp only [StageResult.project] at ha hm hc hw hv
    simp only [restartsExec,CountedArrayComposite.restarts,StageResult.project,append_value,projectCalls_append]
    have ht:=ih (stageExec O owner primes active marked blockSizes remaining k lam).value.active
      (stageExec O owner primes active marked blockSizes remaining k lam).value.marked
    have hta:=congrArg CountedArrayComposite.StageResult.active ht
    have htm:=congrArg CountedArrayComposite.StageResult.marked ht
    have hts:=congrArg CountedArrayComposite.StageResult.selected ht
    have htc:=congrArg CountedArrayComposite.StageResult.calls ht
    have htw:=congrArg CountedArrayComposite.StageResult.backendWork ht
    have htv:=congrArg CountedArrayComposite.StageResult.controllerVisits ht
    simp only [StageResult.project,ha,hm] at hta htm hts htc htw htv
    rw [ha,hm,hta,htm,hts,htc,htw,htv,hc,hw,hv]

abbrev PrimeSlot:=Prime
abbrev restarts:=@restartsExec



open ArrayCompositeAlgorithm (Flags Owners)

@[simp] theorem evaluateOnce_get {P I : ℕ} {Payload : Type*} (O : Oracle I Payload)
    (active : Flags I) (primes : Primes P) (remaining : Flags P) (selected : List ℕ) (p : Fin P) :
    (evaluateOnce O active primes remaining selected).value.get p=
      if remaining.get p then some (O.table selected (primes.get p).control active) else none := by
  simp only [evaluateOnce,tabulate_value,Vector.get_ofFn]
  split <;> rfl

theorem evaluateOnce_call_result {P I : ℕ} {Payload : Type*} (O : Oracle I Payload)
    (active : Flags I) (primes : Primes P) (remaining : Flags P) (selected : List ℕ)
    (ps : List (Fin P)) (call : Call I Payload)
    (hc : call∈(cacheCallsFrom (evaluateOnce O active primes remaining selected).value active primes selected ps).value) :
    call.result=O.table call.factors.selected call.factors.candidate call.factors.active := by
  induction ps with
  |nil=>simp [cacheCallsFrom] at hc
  |cons p ps ih=>
    simp only [cacheCallsFrom,evaluateOnce_get] at hc
    cases h : remaining.get p <;> simp only [h,Bool.false_eq_true,if_false,if_true] at hc
    · exact ih hc
    · rcases List.mem_cons.mp hc with rfl|hc
      · rfl
      · exact ih hc

theorem greedyExec_retained_results {P I : ℕ} {Payload : Type*} (O : Oracle I Payload)
    (active : Flags I) (primes : Primes P) (k : ℕ) (d : NatCell) (remaining : Flags P)
    (base : Counts I) (selected : List ℕ) :
    ∀call∈(greedyExec O active primes k d remaining base selected).value.calls,
      call.result=O.table call.factors.selected call.factors.candidate call.factors.active := by
  induction k generalizing d remaining base selected with
  |zero=>simp [greedyExec]
  |succ k ih=>
    simp only [greedyExec]
    split
    · simp
    · intro call hc
      simp only [append_value] at hc
      rcases List.mem_append.mp hc with hc|hc
      · exact evaluateOnce_call_result O active primes remaining selected (List.finRange P) call hc
      · exact ih _ _ _ _ call hc

theorem stageExec_retained_results {P I Q : ℕ} {Payload : Type*} (O : Oracle I Payload)
    (owner : Owners I Q) (primes : Primes P) (active : Flags I) (marked : Flags Q)
    (blockSizes : Counts I) (remaining : Flags P) (k : ℕ) (lam : NatCell) :
    ∀call∈(stageExec O owner primes active marked blockSizes remaining k lam).value.calls,
      call.result=O.table call.factors.selected call.factors.candidate call.factors.active := by
  intro call hc
  simp only [stageExec,append_value] at hc
  rcases List.mem_append.mp hc with hc|hc
  · exact greedyExec_retained_results O active primes k one remaining blockSizes [] call hc
  · exact evaluateOnce_call_result O active primes
      (greedyExec O active primes k one remaining blockSizes []).value.remaining
      (greedyExec O active primes k one remaining blockSizes []).value.selected
      (List.finRange P) call hc

theorem restartsExec_retained_results {P I Q : ℕ} {Payload : Type*} (O : Oracle I Payload)
    (owner : Owners I Q) (primes : Primes P) (blockSizes : Counts I) (remaining : Flags P)
    (k : ℕ) (lam : NatCell) (n : ℕ) (active : Flags I) (marked : Flags Q) :
    ∀call∈(restartsExec O owner primes blockSizes remaining k lam n active marked).value.calls,
      call.result=O.table call.factors.selected call.factors.candidate call.factors.active := by
  induction n generalizing active marked with
  |zero=>simp [restartsExec]
  |succ n ih=>
    intro call hc
    simp only [restartsExec,append_value] at hc
    rcases List.mem_append.mp hc with hc|hc
    · exact stageExec_retained_results O owner primes active marked blockSizes remaining k lam call hc
    · exact ih _ _ call hc

theorem restartsExec_backendWork {P I Q : ℕ} {Payload : Type*} (O : Oracle I Payload)
    (owner : Owners I Q) (primes : Primes P) (blockSizes : Counts I) (remaining : Flags P)
    (k : ℕ) (lam : NatCell) (n : ℕ) (active : Flags I) (marked : Flags Q) :
    (restartsExec O owner primes blockSizes remaining k lam n active marked).value.backendWork=
      CountedArrayComposite.workSum
        (projectCalls (restartsExec O owner primes blockSizes remaining k lam n active marked).value.calls) := by
  have h:=CountedArrayComposite.restarts_backendWork O.project owner (projectPrimes primes)
    (projectCounts blockSizes) remaining k (nview lam) n active marked
  rw [←restartsExec_project] at h
  exact h

theorem restartsExec_calls_length {P I Q : ℕ} {Payload : Type*} (O : Oracle I Payload)
    (owner : Owners I Q) (primes : Primes P) (blockSizes : Counts I) (remaining : Flags P)
    (k : ℕ) (lam : NatCell) (n : ℕ) (active : Flags I) (marked : Flags Q) :
    (restartsExec O owner primes blockSizes remaining k lam n active marked).value.calls.length ≤ n*(k+1)*P := by
  have h:=CountedArrayComposite.restarts_calls_bound O.project owner (projectPrimes primes)
    (projectCounts blockSizes) remaining k (nview lam) n active marked
  rw [←restartsExec_project] at h
  simpa only [StageResult.project,projectCalls,List.length_map] using h



open ArrayCompositeAlgorithm (Flags Owners)

set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

theorem tabulate_zero_arith {n : ℕ} {α : Type*} (f : Fin n → Result α)
    (h : ∀ i, (f i).arithSites=0) : (tabulate f).arithSites=0 := by
  apply Nat.eq_zero_of_le_zero
  simpa using tabulate_arith_le (C:=0) f (by intro i; rw [h])

theorem evaluateOnce_control_le {P I : ℕ} {Payload : Type*} (O : Oracle I Payload)
    (active : Flags I) (primes : Primes P) (remaining : Flags P) (selected : List ℕ) :
    (evaluateOnce O active primes remaining selected).controlSites≤18*P+2 := by
  simpa [evaluateOnce,Nat.mul_comm] using tabulate_control_le (C:=5)
    (fun p => if remaining.get p then
      (⟨some (O.table selected (primes.get p).control active),0,5,0⟩ : Result (Option (Table I Payload)))
      else ⟨none,0,3,0⟩) (by intro p; split <;> simp)

@[simp] theorem evaluateOnce_arith {P I : ℕ} {Payload : Type*} (O : Oracle I Payload)
    (active : Flags I) (primes : Primes P) (remaining : Flags P) (selected : List ℕ) :
    (evaluateOnce O active primes remaining selected).arithSites=0 := by
  apply tabulate_zero_arith
  intro p
  split <;> rfl

theorem cacheRows_control_le {P I : ℕ} {Payload : Type*} (cache : Cache P I Payload) :
    (cacheRows cache).controlSites≤P*(I+16)+2 := by
  apply tabulate_control_le (C:=I+3)
  intro p
  cases cache.get p <;> simp

@[simp] theorem cacheRows_arith {P I : ℕ} {Payload : Type*} (cache : Cache P I Payload) :
    (cacheRows cache).arithSites=0 := by
  apply tabulate_zero_arith
  intro p
  cases cache.get p <;> rfl

theorem cacheCallsFrom_control {P I : ℕ} {Payload : Type*} (cache : Cache P I Payload)
    (active : Flags I) (primes : Primes P) (selected : List ℕ) (ps : List (Fin P)) :
    (cacheCallsFrom cache active primes selected ps).controlSites=5*ps.length+1 := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simp only [cacheCallsFrom]
    cases cache.get p <;> simp [ih] <;> omega

@[simp] theorem cacheCallsFrom_arith {P I : ℕ} {Payload : Type*} (cache : Cache P I Payload)
    (active : Flags I) (primes : Primes P) (selected : List ℕ) (ps : List (Fin P)) :
    (cacheCallsFrom cache active primes selected ps).arithSites=0 := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simp only [cacheCallsFrom]
    cases cache.get p <;> exact ih

theorem cacheCallsFrom_length_le {P I : ℕ} {Payload : Type*} (cache : Cache P I Payload)
    (active : Flags I) (primes : Primes P) (selected : List ℕ) (ps : List (Fin P)) :
    (cacheCallsFrom cache active primes selected ps).value.length≤ps.length := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simp only [cacheCallsFrom]
    cases cache.get p <;> simp <;> omega

theorem cacheCalls_control {P I : ℕ} {Payload : Type*} (cache : Cache P I Payload)
    (active : Flags I) (primes : Primes P) (selected : List ℕ) :
    (cacheCalls cache active primes selected).controlSites=9*P+2 := by
  simp [cacheCalls,cacheCallsFrom_control]
  omega

@[simp] theorem cacheCalls_arith {P I : ℕ} {Payload : Type*} (cache : Cache P I Payload)
    (active : Flags I) (primes : Primes P) (selected : List ℕ) :
    (cacheCalls cache active primes selected).arithSites=0 := by
  simp [cacheCalls]

theorem cacheCalls_length_le {P I : ℕ} {Payload : Type*} (cache : Cache P I Payload)
    (active : Flags I) (primes : Primes P) (selected : List ℕ) :
    (cacheCalls cache active primes selected).value.length≤P := by
  simpa [cacheCalls] using cacheCallsFrom_length_le cache active primes selected (List.finRange P)

theorem append_control {α : Type*} (xs ys : List α) :
    (append xs ys).controlSites=3*xs.length+1 := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [append,ih]; omega

@[simp] theorem append_arith {α : Type*} (xs ys : List α) : (append xs ys).arithSites=0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih => exact ih

theorem sumWork_control {I : ℕ} {Payload : Type*} (calls : List (Call I Payload)) :
    (sumWork calls).controlSites=4*calls.length+1 := by
  induction calls with
  | nil => rfl
  | cons call calls ih => simp [sumWork,ih]; omega

@[simp] theorem sumWork_arith {I : ℕ} {Payload : Type*} (calls : List (Call I Payload)) :
    (sumWork calls).arithSites=0 := by
  induction calls with
  | nil => rfl
  | cons call calls ih => exact ih

theorem copyRow_control_le {I : ℕ} (row : Counts I) :
    (copyRow row).controlSites≤14*I+2 := by
  simpa [copyRow,Nat.mul_comm] using tabulate_control_le (C:=1)
    (fun i => copy (row.get i)) (by intro i; rfl)

theorem copyRow_arith_le {I : ℕ} (row : Counts I) :
    (copyRow row).arithSites≤I := by
  simpa [copyRow] using tabulate_arith_le (C:=1) (fun i => copy (row.get i)) (by intro i; rfl)

@[simp] theorem evaluateOnce_zero_bits {P I : ℕ} {Payload : Type*} (O : Oracle I Payload)
    (active : Flags I) (primes : Primes P) (remaining : Flags P) (selected : List ℕ) :
    (evaluateOnce O active primes remaining selected).bitSteps=0 := by
  apply tabulate_zero_bits
  intro p
  split <;> rfl

@[simp] theorem cacheRows_zero_bits {P I : ℕ} {Payload : Type*} (cache : Cache P I Payload) :
    (cacheRows cache).bitSteps=0 := by
  apply tabulate_zero_bits
  intro p
  cases cache.get p <;> rfl

@[simp] theorem cacheCallsFrom_zero_bits {P I : ℕ} {Payload : Type*} (cache : Cache P I Payload)
    (active : Flags I) (primes : Primes P) (selected : List ℕ) (ps : List (Fin P)) :
    (cacheCallsFrom cache active primes selected ps).bitSteps=0 := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simp only [cacheCallsFrom]
    cases cache.get p <;> exact ih

@[simp] theorem cacheCalls_zero_bits {P I : ℕ} {Payload : Type*} (cache : Cache P I Payload)
    (active : Flags I) (primes : Primes P) (selected : List ℕ) :
    (cacheCalls cache active primes selected).bitSteps=0 := by simp [cacheCalls]

@[simp] theorem append_zero_bits {α : Type*} (xs ys : List α) : (append xs ys).bitSteps=0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih => exact ih

@[simp] theorem sumWork_zero_bits {I : ℕ} {Payload : Type*} (calls : List (Call I Payload)) :
    (sumWork calls).bitSteps=0 := by
  induction calls with
  | nil => rfl
  | cons call calls ih => exact ih

@[simp] theorem put_zero_bits {P : ℕ} (remaining : Flags P) (p : Fin P) :
    (put remaining p).bitSteps=0 := rfl

@[simp] theorem put_zero_arith {P : ℕ} (remaining : Flags P) (p : Fin P) :
    (put remaining p).arithSites=0 := rfl

theorem copyRow_price {I X B : ℕ} (row : Counts I)
    (hrow : ∀ i, nview (row.get i)≤X) (hX : X.size≤B) :
    (copyRow row).bitSteps≤unit B*(copyRow row).arithSites := by
  apply tabulate_price
  intro i
  have ha : (copy (row.get i)).arithSites=1 := rfl
  simpa only [ha,Nat.mul_one] using copy_price B (row.get i) ((Nat.size_le_size (hrow i)).trans hX)

abbrev controlRoundUnit (P I R : ℕ) := DenseControllerExecution.roundUnit P I R

theorem greedyExec_control_le {P I R : ℕ} {Payload : Type*} (O : Oracle I Payload)
    (active : Flags I) (primes : Primes P) (k : ℕ) (d : NatCell) (remaining : Flags P)
    (base : Counts I) (selected : List ℕ) (hR : selected.length+k≤R) :
    (greedyExec O active primes k d remaining base selected).controlSites≤k*controlRoundUnit P I R+1 := by
  induction k generalizing d remaining base selected with
  | zero => simp [greedyExec]
  | succ k ih =>
    have hsize : 1≤DenseControllerExecution.denseSize P I := by simp [DenseControllerExecution.denseSize]
    have hmul : R≤R*DenseControllerExecution.denseSize P I := by nlinarith
    have hunit : 256*(DenseControllerExecution.denseSize P I+R)≤controlRoundUnit P I R := by
      dsimp [controlRoundUnit,DenseControllerExecution.roundUnit]
      nlinarith
    have hsel : selected.length≤R := by omega
    have hc := evaluateOnce_control_le O active primes remaining selected
    have hr := cacheRows_control_le (evaluateOnce O active primes remaining selected).value
    have hs := scores_control_le active (cacheRows (evaluateOnce O active primes remaining selected).value).value
    have hq := choose_control_le remaining
      (scores active (cacheRows (evaluateOnce O active primes remaining selected).value).value).value
    simp only [greedyExec]
    split
    · dsimp only
      dsimp [DenseControllerExecution.denseSize] at hunit
      nlinarith
    · rename_i p hp
      have hcalls := cacheCalls_control (evaluateOnce O active primes remaining selected).value active primes selected
      have hlen := cacheCalls_length_le (evaluateOnce O active primes remaining selected).value active primes selected
      have hb := copyRow_control_le
        ((cacheRows (evaluateOnce O active primes remaining selected).value).value.get p)
      have ht := ih (mul d (primes.get p).cell).value (put remaining p).value
        (copyRow ((cacheRows (evaluateOnce O active primes remaining selected).value).value.get p)).value
        (append selected [(primes.get p).control]).value (by
          simp only [append_value,List.length_append,List.length_singleton]
          omega)
      simp only [put,append_control,sumWork_control,mul]
      dsimp [DenseControllerExecution.denseSize] at hunit
      have hlocal :
          (evaluateOnce O active primes remaining selected).controlSites+
          (cacheRows (evaluateOnce O active primes remaining selected).value).controlSites+
          (scores active (cacheRows (evaluateOnce O active primes remaining selected).value).value).controlSites+
          (choose remaining (scores active (cacheRows (evaluateOnce O active primes remaining selected).value).value).value).controlSites+
          4+(cacheCalls (evaluateOnce O active primes remaining selected).value active primes selected).controlSites+
          1+2+(copyRow ((cacheRows (evaluateOnce O active primes remaining selected).value).value.get p)).controlSites+
          (3*selected.length+1)+
          (3*(cacheCalls (evaluateOnce O active primes remaining selected).value active primes selected).value.length+1)+
          (4*(cacheCalls (evaluateOnce O active primes remaining selected).value active primes selected).value.length+1)+12
           ≤controlRoundUnit P I R := by
        ring_nf at hr hs hunit ⊢
        omega
      simp only [put,mul] at ht
      simp only [Nat.add_mul,Nat.one_mul]
      omega

theorem greedyExec_arith_le {P I : ℕ} {Payload : Type*} (O : Oracle I Payload)
    (active : Flags I) (primes : Primes P) (k : ℕ) (d : NatCell) (remaining : Flags P)
    (base : Counts I) (selected : List ℕ) :
    (greedyExec O active primes k d remaining base selected).arithSites≤
      k*DenseControllerExecution.denseSize P I := by
  induction k generalizing d remaining base selected with
  | zero => simp [greedyExec]
  | succ k ih =>
    have hs := scores_arith_le active (cacheRows (evaluateOnce O active primes remaining selected).value).value
    have hq := choose_arith_le remaining
      (scores active (cacheRows (evaluateOnce O active primes remaining selected).value).value).value
    simp only [greedyExec]
    split
    · dsimp only
      simp only [evaluateOnce_arith,cacheRows_arith,zero_add]
      dsimp [DenseControllerExecution.denseSize]
      nlinarith
    · rename_i p hp
      have hb := copyRow_arith_le
        ((cacheRows (evaluateOnce O active primes remaining selected).value).value.get p)
      have ht := ih (mul d (primes.get p).cell).value (put remaining p).value
        (copyRow ((cacheRows (evaluateOnce O active primes remaining selected).value).value.get p)).value
        (append selected [(primes.get p).control]).value
      simp only [evaluateOnce_arith,cacheRows_arith,cacheCalls_arith,put,append_arith,sumWork_arith,mul]
      simp only [put,mul] at ht
      dsimp [DenseControllerExecution.denseSize] at ht ⊢
      nlinarith

def workSites {α : Type*} (out : Result α) : ℕ := out.controlSites+out.arithSites

theorem greedyExec_workSites_le {P I R : ℕ} {Payload : Type*} (O : Oracle I Payload)
    (active : Flags I) (primes : Primes P) (k : ℕ) (d : NatCell) (remaining : Flags P)
    (base : Counts I) (selected : List ℕ) (hR : selected.length+k≤R) :
    workSites (greedyExec O active primes k d remaining base selected)≤
      512*k*(R+1)*DenseControllerExecution.denseSize P I+1 := by
  have hc := greedyExec_control_le O active primes k d remaining base selected hR
  have ha := greedyExec_arith_le O active primes k d remaining base selected
  dsimp [controlRoundUnit,DenseControllerExecution.roundUnit] at hc
  dsimp [workSites]
  nlinarith

theorem greedyExec_calls_length {P I : ℕ} {Payload : Type*} (O : Oracle I Payload)
    (active : Flags I) (primes : Primes P) (k : ℕ) (d : NatCell) (remaining : Flags P)
    (base : Counts I) (selected : List ℕ) :
    (greedyExec O active primes k d remaining base selected).value.calls.length≤k*P := by
  have hp := congrArg (fun out : CountedArrayComposite.GreedyResult P I Payload => out.calls.length)
    (greedyExec_project O active primes k d remaining base selected)
  simp only [GreedyResult.project,projectCalls,List.length_map] at hp
  rw [hp]
  have he := CountedArrayComposite.greedy_erases O.project active (projectPrimes primes) k
    (nview d) remaining (projectCounts base) selected
  have hl := congrArg (fun out => out.calls.length) he
  simp only [CountedArrayComposite.GreedyResult.erase,CountedArrayComposite.eraseCalls,List.length_map] at hl
  rw [hl]
  exact ArrayCompositeAlgorithm.greedy_calls_bound O.project.erase active (projectPrimes primes) k
    (nview d) remaining (projectCounts base) selected

theorem stageExec_calls_length {P I Q : ℕ} {Payload : Type*} (O : Oracle I Payload)
    (owner : Owners I Q) (primes : Primes P) (active : Flags I) (marked : Flags Q)
    (blockSizes : Counts I) (remaining : Flags P) (k : ℕ) (lam : NatCell) :
    (stageExec O owner primes active marked blockSizes remaining k lam).value.calls.length≤(k+1)*P := by
  have hp := congrArg (fun out : CountedArrayComposite.StageResult P I Q Payload => out.calls.length)
    (stageExec_project O owner primes active marked blockSizes remaining k lam)
  simp only [StageResult.project,projectCalls,List.length_map] at hp
  rw [hp]
  have he := CountedArrayComposite.stage_erases O.project owner (projectPrimes primes) active marked
    (projectCounts blockSizes) remaining k (nview lam)
  have hl := congrArg (fun out => out.calls.length) he
  simp only [CountedArrayComposite.StageResult.erase,CountedArrayComposite.eraseCalls,List.length_map] at hl
  rw [hl]
  exact ArrayCompositeAlgorithm.stage_calls_bound O.project.erase owner (projectPrimes primes) active
    marked (projectCounts blockSizes) remaining k (nview lam)

theorem stageExec_control_le {P I Q : ℕ} {Payload : Type*} (O : Oracle I Payload)
    (owner : Owners I Q) (primes : Primes P) (active : Flags I) (marked : Flags Q)
    (blockSizes : Counts I) (remaining : Flags P) (k : ℕ) (lam : NatCell) :
    (stageExec O owner primes active marked blockSizes remaining k lam).controlSites≤
      (k+1)*controlRoundUnit P I k+1 := by
  let chosen := greedyExec O active primes k one remaining blockSizes []
  let cache := evaluateOnce O active primes chosen.value.remaining chosen.value.selected
  let rows := cacheRows cache.value
  have hg := greedyExec_control_le (R:=k) O active primes k one remaining blockSizes [] (by simp)
  have hc := evaluateOnce_control_le O active primes chosen.value.remaining chosen.value.selected
  have hr := cacheRows_control_le cache.value
  have hm := minima_control_le rows.value chosen.value.remaining
  have hp := population_control chosen.value.remaining
  have hf := finish_control owner active marked chosen.value.base
    (minima rows.value chosen.value.remaining).value lam (population chosen.value.remaining).value
  have hcalls := cacheCalls_control cache.value active primes chosen.value.selected
  have hlen := cacheCalls_length_le cache.value active primes chosen.value.selected
  have hhist := greedyExec_calls_length O active primes k one remaining blockSizes []
  have hsize : P≤DenseControllerExecution.denseSize P I := by simp [DenseControllerExecution.denseSize];omega
  have hk : k*P≤k*DenseControllerExecution.denseSize P I := Nat.mul_le_mul_left k hsize
  change chosen.controlSites≤_ at hg
  change chosen.value.calls.length≤_ at hhist
  change chosen.controlSites+cache.controlSites+rows.controlSites+
    (minima rows.value chosen.value.remaining).controlSites+
    (population chosen.value.remaining).controlSites+
    (finish owner active marked chosen.value.base (minima rows.value chosen.value.remaining).value
      lam (population chosen.value.remaining).value).controlSites+
    (cacheCalls cache.value active primes chosen.value.selected).controlSites+
    (append chosen.value.calls (cacheCalls cache.value active primes chosen.value.selected).value).controlSites+
    (sumWork (cacheCalls cache.value active primes chosen.value.selected).value).controlSites+12≤_
  rw [append_control,sumWork_control]
  have hu : controlRoundUnit P I k=256*(k+1)*DenseControllerExecution.denseSize P I := rfl
  dsimp [DenseControllerExecution.denseSize] at hsize hk hu
  nlinarith

theorem stageExec_arith_le {P I Q : ℕ} {Payload : Type*} (O : Oracle I Payload)
    (owner : Owners I Q) (primes : Primes P) (active : Flags I) (marked : Flags Q)
    (blockSizes : Counts I) (remaining : Flags P) (k : ℕ) (lam : NatCell) :
    (stageExec O owner primes active marked blockSizes remaining k lam).arithSites≤
      (k+8)*DenseControllerExecution.denseSize P I := by
  let chosen := greedyExec O active primes k one remaining blockSizes []
  let cache := evaluateOnce O active primes chosen.value.remaining chosen.value.selected
  let rows := cacheRows cache.value
  have hg := greedyExec_arith_le O active primes k one remaining blockSizes []
  have hm := minima_arith_le rows.value chosen.value.remaining
  have hp := population_arith_le chosen.value.remaining
  have hf := finish_arith owner active marked chosen.value.base
    (minima rows.value chosen.value.remaining).value lam (population chosen.value.remaining).value
  change chosen.arithSites≤_ at hg
  change chosen.arithSites+cache.arithSites+rows.arithSites+
    (minima rows.value chosen.value.remaining).arithSites+
    (population chosen.value.remaining).arithSites+
    (finish owner active marked chosen.value.base (minima rows.value chosen.value.remaining).value
      lam (population chosen.value.remaining).value).arithSites+
    (cacheCalls cache.value active primes chosen.value.selected).arithSites+
    (append chosen.value.calls (cacheCalls cache.value active primes chosen.value.selected).value).arithSites+
    (sumWork (cacheCalls cache.value active primes chosen.value.selected).value).arithSites≤_
  simp only [cache,rows,evaluateOnce_arith,cacheRows_arith,cacheCalls_arith,append_arith,sumWork_arith]
  dsimp [DenseControllerExecution.denseSize] at hg ⊢
  dsimp only [cache,rows] at hm hp hf
  nlinarith

theorem restartsExec_control_le {P I Q : ℕ} {Payload : Type*} (O : Oracle I Payload)
    (owner : Owners I Q) (primes : Primes P) (blockSizes : Counts I) (remaining : Flags P)
    (k : ℕ) (lam : NatCell) (n : ℕ) (active : Flags I) (marked : Flags Q) :
    (restartsExec O owner primes blockSizes remaining k lam n active marked).controlSites≤
      n*((k+2)*controlRoundUnit P I k)+1 := by
  induction n generalizing active marked with
  | zero => simp [restartsExec]
  | succ n ih =>
    let one := stageExec O owner primes active marked blockSizes remaining k lam
    have hs := stageExec_control_le O owner primes active marked blockSizes remaining k lam
    have hl := stageExec_calls_length O owner primes active marked blockSizes remaining k lam
    have ht := ih one.value.active one.value.marked
    change one.controlSites≤_ at hs
    change one.value.calls.length≤_ at hl
    have hsize : P+1≤DenseControllerExecution.denseSize P I := by simp [DenseControllerExecution.denseSize];omega
    have hk := Nat.mul_le_mul_left (k+1) hsize
    change one.controlSites+
      (restartsExec O owner primes blockSizes remaining k lam n one.value.active one.value.marked).controlSites+
      (append one.value.calls
        (restartsExec O owner primes blockSizes remaining k lam n one.value.active one.value.marked).value.calls).controlSites+5≤_
    rw [append_control]
    have hu : controlRoundUnit P I k=256*(k+1)*DenseControllerExecution.denseSize P I := rfl
    nlinarith

theorem restartsExec_arith_le {P I Q : ℕ} {Payload : Type*} (O : Oracle I Payload)
    (owner : Owners I Q) (primes : Primes P) (blockSizes : Counts I) (remaining : Flags P)
    (k : ℕ) (lam : NatCell) (n : ℕ) (active : Flags I) (marked : Flags Q) :
    (restartsExec O owner primes blockSizes remaining k lam n active marked).arithSites≤
      n*((k+8)*DenseControllerExecution.denseSize P I) := by
  induction n generalizing active marked with
  | zero => simp [restartsExec]
  | succ n ih =>
    let one := stageExec O owner primes active marked blockSizes remaining k lam
    have hs := stageExec_arith_le O owner primes active marked blockSizes remaining k lam
    have ht := ih one.value.active one.value.marked
    change one.arithSites≤_ at hs
    change one.arithSites+
      (restartsExec O owner primes blockSizes remaining k lam n one.value.active one.value.marked).arithSites+
      (append one.value.calls
        (restartsExec O owner primes blockSizes remaining k lam n one.value.active one.value.marked).value.calls).arithSites≤_
    rw [append_arith]
    nlinarith

theorem restartsExec_workSites_le {P I Q : ℕ} {Payload : Type*} (O : Oracle I Payload)
    (owner : Owners I Q) (primes : Primes P) (blockSizes : Counts I) (remaining : Flags P)
    (k : ℕ) (lam : NatCell) (n : ℕ) (active : Flags I) (marked : Flags Q) :
    workSites (restartsExec O owner primes blockSizes remaining k lam n active marked)≤
      512*n*(k+1)*(k+2)*DenseControllerExecution.denseSize P I+1 := by
  have hc := restartsExec_control_le O owner primes blockSizes remaining k lam n active marked
  have ha := restartsExec_arith_le O owner primes blockSizes remaining k lam n active marked
  dsimp [controlRoundUnit,DenseControllerExecution.roundUnit] at hc
  have hcoef : k+8≤256*(k+1)*(k+2) := by nlinarith
  have hm := Nat.mul_le_mul_right (DenseControllerExecution.denseSize P I)
    (Nat.mul_le_mul_left n hcoef)
  dsimp [workSites]
  ring_nf at hc ha hm ⊢
  omega

theorem restartsExec_workSites_by_visits {P I Q : ℕ} {Payload : Type*} (O : Oracle I Payload)
    (owner : Owners I Q) (primes : Primes P) (blockSizes : Counts I) (remaining : Flags P)
    (k : ℕ) (lam : NatCell) (n : ℕ) (active : Flags I) (marked : Flags Q) (hP : 0<P) :
    workSites (restartsExec O owner primes blockSizes remaining k lam n active marked)≤
      512*(k+1)*(k+2)*
        (restartsExec O owner primes blockSizes remaining k lam n active marked).value.controllerVisits+1 := by
  have hv := DenseControllerExecution.restarts_visits_lower O.project owner (projectPrimes primes)
    (projectCounts blockSizes) remaining k (nview lam) n active marked
  have hd : DenseControllerExecution.denseSize P I≤CountedArrayComposite.finalVisits P I := by
    dsimp [DenseControllerExecution.denseSize,CountedArrayComposite.finalVisits]
    ring_nf
    omega
  have hp := congrArg CountedArrayComposite.StageResult.controllerVisits
    (restartsExec_project O owner primes blockSizes remaining k lam n active marked)
  simp only [StageResult.project] at hp
  have hn : n*DenseControllerExecution.denseSize P I≤
      (restartsExec O owner primes blockSizes remaining k lam n active marked).value.controllerVisits := by
    rw [hp]
    exact (Nat.mul_le_mul_left n hd).trans hv
  calc
    _≤512*n*(k+1)*(k+2)*DenseControllerExecution.denseSize P I+1 :=
      restartsExec_workSites_le O owner primes blockSizes remaining k lam n active marked
    _=512*(k+1)*(k+2)*(n*DenseControllerExecution.denseSize P I)+1 := by ring
    _≤_ := Nat.add_le_add_right (Nat.mul_le_mul_left _ hn) 1




open ArrayCompositeAlgorithm (Flags Owners)
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The binary producer's actual retained count cells satisfy a value cap. -/
def OracleCountsBound {I : ℕ} {Payload : Type*} (O : Oracle I Payload) (X : ℕ) : Prop :=
  ∀ selected candidate active i, nview ((O.table selected candidate active).counts.get i)≤X

/-- Cache references preserve the actual producer cells; absent rows contain
literal binary zero. This proof never invokes a second runtime producer. -/
theorem pricing_rows_bound {P I X : ℕ} {Payload : Type*} (O : Oracle I Payload)
    (hO : OracleCountsBound O X) (active : Flags I) (primes : Primes P)
    (remaining : Flags P) (selected : List ℕ) :
    ∀ p i, nview (((cacheRows (evaluateOnce O active primes remaining selected).value).value.get p).get i)≤X := by
  intro p i
  rw [cacheRows,tabulate_value]
  simp only [Vector.get_ofFn]
  rw [evaluateOnce,tabulate_value]
  simp only [Vector.get_ofFn]
  cases h : remaining.get p
  · simp
  · simpa [h] using hO selected (primes.get p).control active i

theorem pricing_copyRow_bound {I X : ℕ} (row : Counts I)
    (hrow : ∀ i, nview (row.get i)≤X) :
    ∀ i, nview ((copyRow row).value.get i)≤X := by
  intro i
  rw [copyRow,tabulate_value]
  simpa using hrow i

/-- Base tables are selected and copied from the same produced binary cache. -/
theorem greedyExec_base_bound {P I X : ℕ} {Payload : Type*} (O : Oracle I Payload)
    (hO : OracleCountsBound O X) (active : Flags I) (primes : Primes P)
    (k : ℕ) (d : NatCell) (remaining : Flags P) (base : Counts I) (selected : List ℕ)
    (hbase : ∀ i, nview (base.get i)≤X) :
    ∀ i, nview ((greedyExec O active primes k d remaining base selected).value.base.get i)≤X := by
  have hb := DenseControllerExecution.counted_greedy_base_bound O.project
    (fun selected candidate active i => by simpa [Oracle.project,Table.project,projectCounts] using hO selected candidate active i)
    active (projectPrimes primes) k (nview d) remaining (projectCounts base) selected
    (by intro i; simpa [projectCounts] using hbase i)
  have he := congrArg CountedArrayComposite.GreedyResult.base
    (greedyExec_project O active primes k d remaining base selected)
  simp only [GreedyResult.project] at he
  rw [← he] at hb
  intro i
  simpa [projectCounts] using hb i

/-- The remaining-round product budget simultaneously bounds the current
modulus and each next binary multiplication's operands. -/
theorem greedyExec_price {P I X pmax Y B : ℕ} {Payload : Type*} (O : Oracle I Payload)
    (hO : OracleCountsBound O X) (active : Flags I) (primes : Primes P)
    (hprimes : ∀ p, (primes.get p).control≤pmax) (hpmax : 1≤pmax)
    (k : ℕ) (d : NatCell) (remaining : Flags P) (base : Counts I) (selected : List ℕ)
    (hbase : ∀ i, nview (base.get i)≤X) (hbudget : nview d*pmax^k≤Y)
    (hX : X.size≤B) (hIX : (I*X).size≤B) (hp : pmax.size≤B) (hY : Y.size≤B) :
    (greedyExec O active primes k d remaining base selected).bitSteps≤
      unit B*(greedyExec O active primes k d remaining base selected).arithSites := by
  induction k generalizing d remaining base selected with
  | zero => simp [greedyExec]
  | succ k ih =>
    have hrows := pricing_rows_bound O hO active primes remaining selected
    have hs := scores_price active (cacheRows (evaluateOnce O active primes remaining selected).value).value hrows hX hIX
    have hc := choose_price_of_bound remaining
      (scores active (cacheRows (evaluateOnce O active primes remaining selected).value).value).value
      (scores_bound active _ hrows) hIX
    have hd : nview d≤Y :=
      (Nat.le_mul_of_pos_right (nview d) (Nat.one_le_pow _ _ hpmax)).trans hbudget
    simp only [greedyExec]
    split
    · simp only [evaluateOnce_zero_bits,cacheRows_zero_bits,evaluateOnce_arith,cacheRows_arith,zero_add,Nat.mul_add]
      omega
    · rename_i p hchosen
      have hpc : nview (primes.get p).cell≤pmax := by rw [(primes.get p).same]; exact hprimes p
      have hmul := mul_price B d (primes.get p).cell
        ((Nat.size_le_size hd).trans hY) ((Nat.size_le_size hpc).trans hp)
      have hcopy := copyRow_price ((cacheRows (evaluateOnce O active primes remaining selected).value).value.get p)
        (hrows p) hX
      have hbudget' : nview (mul d (primes.get p).cell).value*pmax^k≤Y := by
        calc
          _ = (nview d*(primes.get p).control)*pmax^k := by rw [mul_nview,(primes.get p).same]
          _ ≤ (nview d*pmax)*pmax^k := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (hprimes p))
          _ = nview d*pmax^(k+1) := by rw [pow_succ]; ring
          _ ≤ Y := hbudget
      have ht := ih (mul d (primes.get p).cell).value (put remaining p).value
        (copyRow ((cacheRows (evaluateOnce O active primes remaining selected).value).value.get p)).value
        (append selected [(primes.get p).control]).value
        (pricing_copyRow_bound _ (hrows p)) hbudget'
      simp only [evaluateOnce_zero_bits,cacheRows_zero_bits,cacheCalls_zero_bits,put_zero_bits,
        append_zero_bits,sumWork_zero_bits,evaluateOnce_arith,cacheRows_arith,cacheCalls_arith,
        put_zero_arith,append_arith,sumWork_arith,zero_add,add_zero,Nat.mul_add]
      have hmularith : (mul d (primes.get p).cell).arithSites=1 := rfl
      simp only [hmularith,Nat.mul_one]
      omega

/-- A stage starts from the literal binary one. All final threshold operands
are bounded from the produced counts, the input multiplier, and pool size. -/
theorem stageExec_price {P I Q X pmax B : ℕ} {Payload : Type*} (O : Oracle I Payload)
    (hO : OracleCountsBound O X) (owner : Owners I Q) (primes : Primes P)
    (hprimes : ∀ p, (primes.get p).control≤pmax) (hpmax : 1≤pmax)
    (active : Flags I) (marked : Flags Q) (blockSizes : Counts I)
    (hbase : ∀ i, nview (blockSizes.get i)≤X) (remaining : Flags P) (k : ℕ) (lam : NatCell)
    (hX : X.size≤B) (hIX : (I*X).size≤B) (hp : pmax.size≤B) (hY : (pmax^k).size≤B)
    (hone : 1≤B) (hP : P.size≤B) (hlam : (nview lam).size≤B)
    (hlX : (nview lam*X).size≤B) (hPX : (P*X).size≤B) :
    (stageExec O owner primes active marked blockSizes remaining k lam).bitSteps≤
      unit B*(stageExec O owner primes active marked blockSizes remaining k lam).arithSites := by
  have hg := greedyExec_price O hO active primes hprimes hpmax k one remaining blockSizes [] hbase
    (by simp) hX hIX hp hY
  have hb := greedyExec_base_bound O hO active primes k one remaining blockSizes [] hbase
  have hrows := pricing_rows_bound O hO active primes
    (greedyExec O active primes k one remaining blockSizes []).value.remaining
    (greedyExec O active primes k one remaining blockSizes []).value.selected
  have hm := minima_price
    (cacheRows (evaluateOnce O active primes
      (greedyExec O active primes k one remaining blockSizes []).value.remaining
      (greedyExec O active primes k one remaining blockSizes []).value.selected).value).value
    (greedyExec O active primes k one remaining blockSizes []).value.remaining hrows hX
  have hmb := minima_bound
    (cacheRows (evaluateOnce O active primes
      (greedyExec O active primes k one remaining blockSizes []).value.remaining
      (greedyExec O active primes k one remaining blockSizes []).value.selected).value).value
    (greedyExec O active primes k one remaining blockSizes []).value.remaining hrows
  have hcount := population_price
    (greedyExec O active primes k one remaining blockSizes []).value.remaining hone hP
  have hcountb := population_bound
    (greedyExec O active primes k one remaining blockSizes []).value.remaining
  have hfit : FinishFits B
      (greedyExec O active primes k one remaining blockSizes []).value.base
      (minima
        (cacheRows (evaluateOnce O active primes
          (greedyExec O active primes k one remaining blockSizes []).value.remaining
          (greedyExec O active primes k one remaining blockSizes []).value.selected).value).value
        (greedyExec O active primes k one remaining blockSizes []).value.remaining).value lam
      (population (greedyExec O active primes k one remaining blockSizes []).value.remaining).value := by
    exact ⟨fun i => (Nat.size_le_size (hb i)).trans hX,
      fun i => (Nat.size_le_size (hmb i)).trans hX,hlam,
      (Nat.size_le_size hcountb).trans hP,
      fun i => (Nat.size_le_size (Nat.mul_le_mul_left (nview lam) (hb i))).trans hlX,
      fun i => (Nat.size_le_size (Nat.mul_le_mul hcountb (hmb i))).trans hPX⟩
  have hf := finish_price owner active marked
    (greedyExec O active primes k one remaining blockSizes []).value.base
    (minima
      (cacheRows (evaluateOnce O active primes
        (greedyExec O active primes k one remaining blockSizes []).value.remaining
        (greedyExec O active primes k one remaining blockSizes []).value.selected).value).value
      (greedyExec O active primes k one remaining blockSizes []).value.remaining).value lam
    (population (greedyExec O active primes k one remaining blockSizes []).value.remaining).value hfit
  simp only [stageExec,evaluateOnce_zero_bits,cacheRows_zero_bits,cacheCalls_zero_bits,
    append_zero_bits,sumWork_zero_bits,evaluateOnce_arith,cacheRows_arith,cacheCalls_arith,
    append_arith,sumWork_arith,add_zero,Nat.mul_add]
  omega

/-- Restart stages retain their actual joint counters, with the same count
and input-width caps valid for every new active mask. -/
theorem restartsExec_price {P I Q X pmax B : ℕ} {Payload : Type*} (O : Oracle I Payload)
    (hO : OracleCountsBound O X) (owner : Owners I Q) (primes : Primes P)
    (hprimes : ∀ p, (primes.get p).control≤pmax) (hpmax : 1≤pmax)
    (blockSizes : Counts I) (hbase : ∀ i, nview (blockSizes.get i)≤X)
    (remaining : Flags P) (k : ℕ) (lam : NatCell)
    (hX : X.size≤B) (hIX : (I*X).size≤B) (hp : pmax.size≤B) (hY : (pmax^k).size≤B)
    (hone : 1≤B) (hP : P.size≤B) (hlam : (nview lam).size≤B)
    (hlX : (nview lam*X).size≤B) (hPX : (P*X).size≤B)
    (n : ℕ) (active : Flags I) (marked : Flags Q) :
    (restartsExec O owner primes blockSizes remaining k lam n active marked).bitSteps≤
      unit B*(restartsExec O owner primes blockSizes remaining k lam n active marked).arithSites := by
  induction n generalizing active marked with
  | zero => simp [restartsExec]
  | succ n ih =>
    have hs := stageExec_price O hO owner primes hprimes hpmax active marked blockSizes hbase
      remaining k lam hX hIX hp hY hone hP hlam hlX hPX
    have ht := ih (stageExec O owner primes active marked blockSizes remaining k lam).value.active
      (stageExec O owner primes active marked blockSizes remaining k lam).value.marked
    simp only [restartsExec,append_zero_bits,append_arith,add_zero,Nat.mul_add]
    omega




open ArrayCompositeAlgorithm (Flags Owners)

/-- All binary data-width requirements follow from the concrete cap already
used by the semantic controller. `W` bounds returned backend counters. -/
theorem controllerCap_widths (P I Q k lam n X W pmax : ℕ) (hpmax : 1 ≤ pmax) :
    let B:=(DenseControllerExecution.controllerCap P I Q k lam n X W pmax).size
    X.size ≤ B ∧ (I*X).size ≤ B ∧ pmax.size ≤ B ∧ (pmax^k).size ≤ B ∧
    1 ≤ B ∧ P.size ≤ B ∧ lam.size ≤ B ∧ (lam*X).size ≤ B ∧ (P*X).size ≤ B := by
  rcases DenseControllerExecution.controllerCap_components P I Q k lam n X W pmax with
    ⟨hX,hIX,hlX,hPX,hpow,hwork,hcalls,hmeta⟩
  have hprime : pmax ≤ DenseControllerExecution.controllerCap P I Q k lam n X W pmax := by omega
  have hP : P ≤ DenseControllerExecution.controllerCap P I Q k lam n X W pmax := by omega
  have hlam : lam ≤ DenseControllerExecution.controllerCap P I Q k lam n X W pmax := by omega
  have hpos : 0<DenseControllerExecution.controllerCap P I Q k lam n X W pmax := by omega
  have hB := Nat.size_pos.mpr hpos
  have hpowk : pmax^k ≤ pmax^(k+1) := by
    rw [pow_succ]
    exact Nat.le_mul_of_pos_right _ hpmax
  exact ⟨Nat.size_le_size hX,Nat.size_le_size hIX,Nat.size_le_size hprime,
    Nat.size_le_size (hpowk.trans hpow),hB,Nat.size_le_size hP,Nat.size_le_size hlam,
    Nat.size_le_size hlX,Nat.size_le_size hPX⟩

/-- This prices the entire actual binary interpreter, rather than replacing a
native arithmetic evaluator by a declared global time allowance. -/
theorem restartsExec_price_cap {P I Q X W pmax : ℕ} {Payload : Type*}
    (O : Oracle I Payload) (hO : OracleCountsBound O X) (owner : Owners I Q)
    (primes : Primes P) (hprimes : ∀p,(primes.get p).control ≤ pmax) (hpmax : 1 ≤ pmax)
    (blockSizes : Counts I) (hbase : ∀i,nview (blockSizes.get i) ≤ X) (remaining : Flags P)
    (k : ℕ) (lam : NatCell) (n : ℕ) (active : Flags I) (marked : Flags Q) :
    let B:=(DenseControllerExecution.controllerCap P I Q k (nview lam) n X W pmax).size
    (restartsExec O owner primes blockSizes remaining k lam n active marked).bitSteps ≤
      unit B*(restartsExec O owner primes blockSizes remaining k lam n active marked).arithSites := by
  rcases controllerCap_widths P I Q k (nview lam) n X W pmax hpmax with
    ⟨hX,hIX,hp,hY,hone,hP,hlam,hlX,hPX⟩
  exact restartsExec_price O hO owner primes hprimes hpmax blockSizes hbase remaining k lam
    hX hIX hp hY hone hP hlam hlX hPX n active marked

/-- Bounded control/index/address operations retain their separate IR price.
Arithmetic is charged by the executed bit circuits, and producer work is
retained exactly once. All three summands are from this joint execution. -/
def executionWork {P I Q : ℕ} {Payload : Type*} (B A : ℕ)
    (out : Result (StageResult P I Q Payload)) : ℕ :=
  out.bitSteps+BackendScalarBits.addressedUnit B A*out.controlSites+out.value.backendWork

def executionUnit (B A : ℕ) : ℕ := unit B+BackendScalarBits.addressedUnit B A

theorem executionWork_bound {P I Q B A : ℕ} {Payload : Type*}
    (out : Result (StageResult P I Q Payload)) (hbits : out.bitSteps ≤ unit B*out.arithSites) :
    executionWork B A out ≤ executionUnit B A*workSites out+out.value.backendWork := by
  have h₁ : unit B*out.arithSites ≤ executionUnit B A*out.arithSites :=
    Nat.mul_le_mul_right _ (Nat.le_add_right _ _)
  have h₂ : BackendScalarBits.addressedUnit B A*out.controlSites ≤ executionUnit B A*out.controlSites :=
    Nat.mul_le_mul_right _ (Nat.le_add_left _ _)
  dsimp [executionWork,workSites]
  calc
    out.bitSteps+BackendScalarBits.addressedUnit B A*out.controlSites+out.value.backendWork
       ≤  executionUnit B A*out.arithSites+executionUnit B A*out.controlSites+out.value.backendWork := by omega
    _ = _ := by ring

/-- Final joint contract: binary execution, exact native specification,
retained literal producer returns, and fully derived arithmetic/control
charge. `A` is the independently certified public-address width. -/
theorem binary_controller_contract {P I Q X W pmax A : ℕ} {Payload : Type*}
    (O : Oracle I Payload) (hO : OracleCountsBound O X) (owner : Owners I Q)
    (primes : Primes P) (hprimes : ∀p,(primes.get p).control ≤ pmax) (hpmax : 1 ≤ pmax)
    (blockSizes : Counts I) (hbase : ∀i,nview (blockSizes.get i) ≤ X) (remaining : Flags P)
    (k : ℕ) (lam : NatCell) (n : ℕ) (active : Flags I) (marked : Flags Q) (hP : 0<P) :
    let out:=restartsExec O owner primes blockSizes remaining k lam n active marked
    let B:=(DenseControllerExecution.controllerCap P I Q k (nview lam) n X W pmax).size
    out.value.project=CountedArrayComposite.restarts O.project owner (projectPrimes primes)
      (projectCounts blockSizes) remaining k (nview lam) n active marked ∧
    (∀call∈out.value.calls,call.result=O.table call.factors.selected call.factors.candidate call.factors.active) ∧
    out.value.backendWork=CountedArrayComposite.workSum (projectCalls out.value.calls) ∧
    executionWork B A out ≤ executionUnit B A*
      (512*(k+1)*(k+2)*out.value.controllerVisits+1)+out.value.backendWork := by
  have hb:=restartsExec_price_cap (W:=W) O hO owner primes hprimes hpmax blockSizes hbase remaining k lam n active marked
  have hc:=restartsExec_workSites_by_visits O owner primes blockSizes remaining k lam n active marked hP
  refine ⟨restartsExec_project O owner primes blockSizes remaining k lam n active marked,
    restartsExec_retained_results O owner primes blockSizes remaining k lam n active marked,
    restartsExec_backendWork O owner primes blockSizes remaining k lam n active marked,?_⟩
  exact (executionWork_bound _ hb).trans (Nat.add_le_add_right (Nat.mul_le_mul_left _ hc) _)




def publicBits (n : ℕ) : Result (List Bool) :=
  Nat.binaryRec ⟨[],0,1,0⟩ (fun b _ tail=>⟨b::tail.value,tail.bitSteps,tail.controlSites+8,tail.arithSites⟩) n

theorem publicBits_value (n : ℕ) : (publicBits n).value=n.bits := by
  induction n using Nat.binaryRec' with
  |zero=>rfl
  |bit b n h ih=>
    rw [publicBits,Nat.binaryRec_eq b n (Or.inr h)]
    simp only [Nat.bits_append_bit _ _ h]
    exact congrArg (List.cons b) ih

theorem publicBits_control (n : ℕ) : (publicBits n).controlSites=8*n.size+1 := by
  induction n using Nat.binaryRec' with
  |zero=>rfl
  |bit b n h ih=>
    rw [publicBits,Nat.binaryRec_eq b n (Or.inr h)]
    have hn : Nat.bit b n≠0 := by cases b <;> simp_all [Nat.bit]
    change (publicBits n).controlSites+8=8*(Nat.bit b n).size+1
    rw [ih,Nat.size_bit hn]
    omega

theorem publicBits_zero_bits (n : ℕ) : (publicBits n).bitSteps=0 ∧ (publicBits n).arithSites=0 := by
  induction n using Nat.binaryRec' with
  |zero=>simp [publicBits,Nat.binaryRec_zero]
  |bit b n h ih=>
    rw [publicBits,Nat.binaryRec_eq b n (Or.inr h)]
    exact ih

/-- Static public shape/prime labels only. Binary recursion extracts one bit
per bounded-control iteration; this helper is never used to encode adaptive
count or original-weight values. -/
def fromPublic (n : ℕ) : Result NatCell :=
  let out:=publicBits n
  let cell : BinaryCell.Cell:=⟨⟨false,out.value⟩,by
    change out.value.length=(IntegerArithmetic.signedValue ⟨false,out.value⟩).natAbs.size
    dsimp only [out]
    rw [publicBits_value]
    simp [IntegerArithmetic.signedValue,IntegerArithmetic.value_bits,Nat.size_eq_bits_len]⟩
  ⟨⟨cell,by
    change 0≤IntegerArithmetic.signedValue ⟨false,out.value⟩
    simp [IntegerArithmetic.signedValue]⟩,out.bitSteps,out.controlSites+2,out.arithSites⟩

theorem fromPublic_nview (n : ℕ) : nview (fromPublic n).value=n := by
  simp [fromPublic,nview,NatCell.cell,BinaryCell.view,BinaryArrayFFT.Integer.view,
    IntegerArithmetic.signedValue,publicBits_value,IntegerArithmetic.value_bits]

theorem fromPublic_control (n : ℕ) : (fromPublic n).controlSites=8*n.size+3 := by
  simp [fromPublic,publicBits_control]

def preparePrime (n : ℕ) : Result Prime :=
  let out:=fromPublic n
  ⟨⟨n,out.value,fromPublic_nview n⟩,out.bitSteps,out.controlSites+2,out.arithSites⟩

theorem preparePrime_control (n : ℕ) : (preparePrime n).controlSites=8*n.size+5 := by
  simp [preparePrime,fromPublic_control]



open ArrayCompositeAlgorithm (Flags Owners)

/-- Proof-erased nonnegative wrapping preserves the producer's stored bits.
The joint tabulation charges its array visits; it never decodes counts. -/
def Table.fromCells {I : ℕ} {Payload : Type*} (cells : Vector BinaryCell.Cell I)
    (nonnegative : ∀i,0≤BinaryCell.view (cells.get i)) (payload : Payload) (work : ℕ) :
    Result (Table I Payload) :=
  let out:=tabulate (fun i=> (⟨⟨cells.get i,nonnegative i⟩,0,1,0⟩ : Result NatCell))
  ⟨⟨out.value,payload,work⟩,out.bitSteps,out.controlSites+3,out.arithSites⟩

theorem Table.fromCells_get {I : ℕ} {Payload : Type*} (cells : Vector BinaryCell.Cell I)
    (nonnegative : ∀i,0≤BinaryCell.view (cells.get i)) (payload : Payload) (work : ℕ) (i : Fin I) :
    ((Table.fromCells cells nonnegative payload work).value.counts.get i).cell=cells.get i := by
  simp [Table.fromCells,tabulate_value,NatCell.cell]

theorem Table.fromCells_control {I : ℕ} {Payload : Type*} (cells : Vector BinaryCell.Cell I)
    (nonnegative : ∀i,0≤BinaryCell.view (cells.get i)) (payload : Payload) (work : ℕ) :
    (Table.fromCells cells nonnegative payload work).controlSites≤14*I+5 := by
  have h:=tabulate_control_le (C:=1)
    (fun i=> (⟨⟨cells.get i,nonnegative i⟩,0,1,0⟩ : Result NatCell)) (by intro i;rfl)
  dsimp [Table.fromCells]
  omega

theorem restartsExec_dense_projection {P I Q : ℕ} {Payload : Type*} (O : Oracle I Payload)
    (owner : Owners I Q) (primes : Primes P) (blockSizes : Counts I) (remaining : Flags P)
    (k : ℕ) (lam : NatCell) (n : ℕ) (active : Flags I) (marked : Flags Q) :
    (restartsExec O owner primes blockSizes remaining k lam n active marked).value.project =
      (DenseControllerExecution.restartsExec O.project owner (projectPrimes primes)
        (projectCounts blockSizes) remaining k (nview lam) n active marked).value := by
  rw [DenseControllerExecution.restartsExec_value]
  exact restartsExec_project O owner primes blockSizes remaining k lam n active marked

/-- A supplied producer-counter cap bounds accumulated ghost metadata too. -/
theorem restartsExec_backendWork_bound {P I Q W : ℕ} {Payload : Type*} (O : Oracle I Payload)
    (hW : ∀selected candidate active,(O.table selected candidate active).work≤W)
    (owner : Owners I Q) (primes : Primes P) (blockSizes : Counts I) (remaining : Flags P)
    (k : ℕ) (lam : NatCell) (n : ℕ) (active : Flags I) (marked : Flags Q) :
    (restartsExec O owner primes blockSizes remaining k lam n active marked).value.backendWork≤n*(k+1)*P*W := by
  have h:=DenseControllerExecution.restartsExec_backendWork_bound O.project hW owner
    (projectPrimes primes) (projectCounts blockSizes) remaining k (nview lam) n active marked
  rw [DenseControllerExecution.restartsExec_value,←restartsExec_project] at h
  exact h


/-- A finite execution fixture with retained binary table payloads. -/
def exampleOracle : Oracle 2 ℕ :=
  ⟨fun _ prime _=>⟨Vector.replicate 2 one,prime,7⟩⟩
def examplePrimeSetup : Result (Primes 3) := tabulate (fun p : Fin 3=>preparePrime (p.val+2))
def exampleExecution : Result (StageResult 3 2 1 ℕ) :=
  restartsExec exampleOracle (Vector.replicate 2 (0 : Fin 1)) examplePrimeSetup.value
    (Vector.replicate 2 one) (Vector.replicate 3 true) 1 one 2
    (Vector.replicate 2 true) (Vector.replicate 1 false)
#eval (examplePrimeSetup.controlSites,exampleExecution.bitSteps,exampleExecution.controlSites,
  exampleExecution.arithSites,exampleExecution.value.calls.length,exampleExecution.value.backendWork,
  exampleExecution.value.active.toList,exampleExecution.value.marked.toList)

#print axioms add_nview
#print axioms mul_nview
#print axioms lt_value
#print axioms scoreScan_value
#print axioms scoreScan_price
#print axioms scores_project
#print axioms scores_price
#print axioms choose_project
#print axioms choose_price
#print axioms minima_project
#print axioms minima_price
#print axioms population_project
#print axioms finish_project
#print axioms finish_price
#print axioms evaluateOnce_project
#print axioms greedyExec_project
#print axioms stageExec_project
#print axioms restartsExec_project
#print axioms restartsExec_retained_results
#print axioms restartsExec_backendWork
#print axioms greedyExec_price
#print axioms stageExec_price
#print axioms restartsExec_price
#print axioms restartsExec_workSites_by_visits
#print axioms controllerCap_widths
#print axioms restartsExec_price_cap
#print axioms binary_controller_contract
#print axioms publicBits_value
#print axioms fromPublic_nview
#print axioms preparePrime_control
#print axioms Table.fromCells_get
#print axioms restartsExec_dense_projection
#print axioms restartsExec_backendWork_bound

end ThinMatrix.BinaryControllerExecution
