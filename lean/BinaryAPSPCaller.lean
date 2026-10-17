import BinaryModularCell
import BinaryMultiplierAdapter
import StoredMinPlusAPSP

/-!
# APSP host reduction on stored signed binary cells

The matrices below contain canonical signed Boolean lists. Every intermediate
coefficient is produced by binary arithmetic on stored operands. An Exact
Triangle callback receives those same stored cells, returns a materialized
Boolean table, and contributes its returned work exactly once. Integer views
are specifications and erased proofs; no computed coefficient is serialized
from its integer view. Public control constants and original graph inputs use
the separately charged boundary encoder.

The counter prices binary primitives and bounded array-address operations.
It is not a statement about Lean evaluator allocation or a compiled RAM.
-/

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000

namespace ThinMatrix.BinaryAPSPCaller
open scoped BigOperators
open IntegerArithmetic FFTBitCost
abbrev Cell := BinaryCell.Cell
abbrev Table := StoredMinPlusAPSP.Table
abbrev IntTable (n : ℕ) := Table n Cell
abbrev OptionalTable (n : ℕ) := Table n (Option Cell)
abbrev BoolTable := StoredMinPlusAPSP.BoolTable
abbrev Result := BinaryCell.Result
abbrev OracleOutput := StoredMinPlusAPSP.OracleOutput
abbrev Oracle (n : ℕ) (Payload : Type) :=
  IntTable n → IntTable n → IntTable n → OracleOutput n Payload

abbrev one : Cell := BinaryModularCell.one
abbrev two : Cell := BinaryModularCell.two
@[simp] theorem one_view : BinaryCell.view one = 1 := BinaryModularCell.one_view
@[simp] theorem two_view : BinaryCell.view two = 2 := BinaryModularCell.two_view
abbrev halfCell := BinaryModularCell.half
@[simp] theorem halfCell_view (a : Cell) :
    BinaryCell.view (halfCell a).value = BinaryCell.view a / 2 := BinaryModularCell.half_view a
abbrev less := BinaryModularCell.signedLess
theorem less_true (a b : Cell) :
    (less a b).value = true ↔ BinaryCell.view a < BinaryCell.view b := BinaryModularCell.signedLess_true a b

def viewTable {n : ℕ} (A : IntTable n) : StoredMinPlusAPSP.IntTable n :=
  A.map (fun row => row.map BinaryCell.view)

def viewOptional {n : ℕ} (A : OptionalTable n) : StoredMinPlusAPSP.OptionalTable n :=
  A.map (fun row => row.map (Option.map BinaryCell.view))

@[simp] theorem viewTable_get {n : ℕ} (A : IntTable n) (i j : Fin n) :
    StoredMinPlusAPSP.decode (viewTable A) i j =
      BinaryCell.view (StoredMinPlusAPSP.decode A i j) := by
  simp [viewTable,StoredMinPlusAPSP.decode]

@[simp] theorem viewOptional_get {n : ℕ} (A : OptionalTable n) (i j : Fin n) :
    StoredMinPlusAPSP.decode (viewOptional A) i j =
      Option.map BinaryCell.view (StoredMinPlusAPSP.decode A i j) := by
  simp [viewOptional,StoredMinPlusAPSP.decode]

/-- Each result is computed once, then its stored value and price are read.
The extra charge covers bounded row/column address traversal and the write. -/
def tabulate {n : ℕ} {α : Type} (f : Fin n → Fin n → Result α) : Result (Table n α) :=
  let rows := Vector.ofFn (fun i => Vector.ofFn (fun j => f i j))
  ⟨rows.map (fun row => row.map (fun r => r.value)),
    (rows.toList.map (fun row => (row.toList.map (fun r => r.bitSteps)).sum)).sum+
      n^2*(8*(n.size+1)+4)⟩

@[simp] theorem tabulate_get {n : ℕ} {α : Type}
    (f : Fin n → Fin n → Result α) (i j : Fin n) :
    StoredMinPlusAPSP.decode (tabulate f).value i j = (f i j).value := by
  simp [tabulate,StoredMinPlusAPSP.decode]

theorem tabulate_steps {n : ℕ} {α : Type} (f : Fin n → Fin n → Result α) :
    (tabulate f).bitSteps = (∑ i : Fin n, ∑ j : Fin n, (f i j).bitSteps)+
      n^2*(8*(n.size+1)+4) := by
  simp [tabulate,Vector.toList_ofFn,List.map_ofFn,List.sum_ofFn]

theorem tabulate_price {n : ℕ} {α : Type} (f : Fin n → Fin n → Result α) (C : ℕ)
    (h : ∀ i j, (f i j).bitSteps ≤ C) :
    (tabulate f).bitSteps ≤ n^2*(C+8*(n.size+1)+4) := by
  rw [tabulate_steps]
  have hs : (∑ i : Fin n, ∑ j : Fin n, (f i j).bitSteps) ≤ n*n*C := by
    calc
      _ ≤ ∑ i : Fin n, ∑ j : Fin n, C := Finset.sum_le_sum (fun i _ =>
        Finset.sum_le_sum (fun j _ => h i j))
      _ = _ := by simp; ring
  nlinarith

def half {n : ℕ} (A : IntTable n) : Result (IntTable n) :=
  tabulate (fun i j => halfCell (StoredMinPlusAPSP.decode A i j))

def shift {n : ℕ} (A : IntTable n) (u : Cell) : Result (IntTable n) :=
  tabulate (fun i j => BinaryCell.add (StoredMinPlusAPSP.decode A i j) u)

def targetCell (c offset : Cell) : Result Cell :=
  let doubled := BinaryCell.add c c
  let adjusted := BinaryCell.add doubled.value offset
  let output := BinaryCell.neg adjusted.value
  ⟨output.value,doubled.bitSteps+adjusted.bitSteps+output.bitSteps⟩

@[simp] theorem targetCell_view (c offset : Cell) :
    BinaryCell.view (targetCell c offset).value = -(2*BinaryCell.view c+BinaryCell.view offset) := by
  simp [targetCell]
  ring

def refineCell (c : Cell) (z0 z1 : Bool) : Result Cell :=
  let doubled := BinaryCell.add c c
  if z0 then ⟨doubled.value,doubled.bitSteps+4⟩
  else
    let offset := if z1 then one else two
    let adjusted := BinaryCell.add doubled.value offset
    ⟨adjusted.value,doubled.bitSteps+adjusted.bitSteps+6⟩

@[simp] theorem refineCell_view (c : Cell) (z0 z1 : Bool) :
    BinaryCell.view (refineCell c z0 z1).value =
      if z0 then 2*BinaryCell.view c else if z1 then 2*BinaryCell.view c+1 else 2*BinaryCell.view c+2 := by
  cases z0 <;> cases z1 <;> simp [refineCell] <;> ring

structure Call (n : ℕ) (Payload : Type) where
  left : IntTable n
  right : IntTable n
  target : IntTable n
  output : OracleOutput n Payload

def Call.erase {n : ℕ} {Payload : Type} (c : Call n Payload) : StoredMinPlusAPSP.Call n Payload :=
  ⟨viewTable c.left,viewTable c.right,viewTable c.target,c.output⟩

structure Execution (n : ℕ) (α Payload : Type) where
  value : Table n α
  calls : List (Call n Payload)
  hostBits : ℕ
  formationWrites : ℕ
  oracleWork : ℕ
  answerWrites : ℕ

/-- Only an answer refinement interface. It assigns no speed to either
oracle, and never converts the runtime binary arguments back to integers. -/
def Refines {n : ℕ} {Payload NativePayload : Type} (O : Oracle n Payload)
    (N : StoredMinPlusAPSP.DenseOracle n NativePayload) : Prop :=
  ∀ A B T, (O A B T).answers = (N (viewTable A) (viewTable B) (viewTable T)).answers

def bitScale {n : ℕ} {Payload : Type} (O : Oracle n Payload) :
    ℕ → IntTable n → IntTable n → Execution n Cell Payload
  | 0,_,_ =>
      let value := tabulate (fun _ _ => (⟨BinaryCell.zero,1⟩ : Result Cell))
      ⟨value.value,[],value.bitSteps,n^2,0,0⟩
  | d+1,A,B =>
      let Ahalf := half A
      let Bhalf := half B
      let coarse := bitScale O d Ahalf.value Bhalf.value
      let target0 := tabulate (fun i j => targetCell (StoredMinPlusAPSP.decode coarse.value i j) BinaryCell.zero)
      let target1 := tabulate (fun i j => targetCell (StoredMinPlusAPSP.decode coarse.value i j) one)
      let z0 := O A B target0.value
      let z1 := O A B target1.value
      let refined := tabulate (fun i j => refineCell (StoredMinPlusAPSP.decode coarse.value i j)
        (StoredMinPlusAPSP.decode z0.answers i j) (StoredMinPlusAPSP.decode z1.answers i j))
      ⟨refined.value,coarse.calls++[⟨A,B,target0.value,z0⟩,⟨A,B,target1.value,z1⟩],
        coarse.hostBits+Ahalf.bitSteps+Bhalf.bitSteps+target0.bitSteps+target1.bitSteps+refined.bitSteps+coarse.calls.length+8,
        coarse.formationWrites+5*n^2,coarse.oracleWork+z0.work+z1.work,
        coarse.answerWrites+z0.answerWrites+z1.answerWrites⟩

theorem half_view {n : ℕ} (A : IntTable n) :
    viewTable (half A).value = StoredMinPlusAPSP.half (viewTable A) := by
  apply Vector.ext
  intro i hi
  apply Vector.ext
  intro j hj
  simp [half,viewTable,tabulate,StoredMinPlusAPSP.half,StoredMinPlusAPSP.store,
    StoredMinPlusAPSP.decode,Vector.get]

theorem shift_view {n : ℕ} (A : IntTable n) (u : Cell) :
    viewTable (shift A u).value = StoredMinPlusAPSP.shift (viewTable A) (BinaryCell.view u) := by
  apply Vector.ext
  intro i hi
  apply Vector.ext
  intro j hj
  simp [shift,viewTable,tabulate,StoredMinPlusAPSP.shift,StoredMinPlusAPSP.store,
    StoredMinPlusAPSP.decode,Vector.get]

theorem viewTable_tabulate {n : ℕ} (f : Fin n → Fin n → Result Cell) :
    viewTable (tabulate f).value = StoredMinPlusAPSP.store (fun i j => BinaryCell.view (f i j).value) := by
  apply Vector.ext
  intro i hi
  apply Vector.ext
  intro j hj
  simp [viewTable,tabulate,StoredMinPlusAPSP.store]

theorem bitScale_value {n : ℕ} {Payload NativePayload : Type} (O : Oracle n Payload)
    (N : StoredMinPlusAPSP.DenseOracle n NativePayload) (hON : Refines O N)
    (d : ℕ) (A B : IntTable n) :
    viewTable (bitScale O d A B).value = (StoredMinPlusAPSP.bitScale N d (viewTable A) (viewTable B)).value := by
  induction d generalizing A B with
  | zero =>
    apply Vector.ext
    intro i hi
    apply Vector.ext
    intro j hj
    simp [bitScale,viewTable,tabulate,StoredMinPlusAPSP.bitScale,StoredMinPlusAPSP.store]
  | succ d ih =>
    have hc := ih (half A).value (half B).value
    rw [half_view,half_view] at hc
    have ht (offset : Cell) :
        viewTable (tabulate (fun i j => targetCell
          (StoredMinPlusAPSP.decode (bitScale O d (half A).value (half B).value).value i j) offset)).value =
          StoredMinPlusAPSP.store (fun i j =>
            -(2*StoredMinPlusAPSP.decode (StoredMinPlusAPSP.bitScale N d
              (StoredMinPlusAPSP.half (viewTable A)) (StoredMinPlusAPSP.half (viewTable B))).value i j+
                BinaryCell.view offset)) := by
      apply Vector.ext
      intro i hi
      apply Vector.ext
      intro j hj
      have he := congrArg (fun T => StoredMinPlusAPSP.decode T ⟨i,hi⟩ ⟨j,hj⟩) hc
      simpa [viewTable,tabulate,StoredMinPlusAPSP.store,StoredMinPlusAPSP.decode,Vector.get] using
        congrArg (fun z : ℤ => -(2*z+BinaryCell.view offset)) he
    let C := (bitScale O d (half A).value (half B).value).value
    let T0 := (tabulate (fun i j => targetCell (StoredMinPlusAPSP.decode C i j) BinaryCell.zero)).value
    let T1 := (tabulate (fun i j => targetCell (StoredMinPlusAPSP.decode C i j) one)).value
    change viewTable (tabulate (fun i j => refineCell (StoredMinPlusAPSP.decode C i j)
      (StoredMinPlusAPSP.decode (O A B T0).answers i j)
      (StoredMinPlusAPSP.decode (O A B T1).answers i j))).value = _
    rw [viewTable_tabulate]
    simp only [refineCell_view]
    rw [hON A B T0,hON A B T1]
    have ht0 := ht BinaryCell.zero
    have ht1 := ht one
    change viewTable T0 = _ at ht0
    change viewTable T1 = _ at ht1
    rw [ht0,ht1]
    simp only [BinaryCell.zero_view,one_view,add_zero]
    have he (i j : Fin n) : BinaryCell.view (StoredMinPlusAPSP.decode C i j) =
        StoredMinPlusAPSP.decode (StoredMinPlusAPSP.bitScale N d
          (StoredMinPlusAPSP.half (viewTable A)) (StoredMinPlusAPSP.half (viewTable B))).value i j := by
      exact (viewTable_get C i j).symm.trans
        (congrArg (fun T => StoredMinPlusAPSP.decode T i j) hc)
    simp only [he]
    rfl


def signedProduct {n : ℕ} {Payload : Type} (O : Oracle n Payload) (d : ℕ)
    (A B : IntTable n) (u v : Cell) : Execution n Cell Payload :=
  let shiftedA := shift A u
  let shiftedB := shift B v
  let core := bitScale O d shiftedA.value shiftedB.value
  let result := tabulate (fun i j =>
    let first := BinaryCell.sub (StoredMinPlusAPSP.decode core.value i j) u
    let second := BinaryCell.sub first.value v
    ⟨second.value,first.bitSteps+second.bitSteps⟩)
  ⟨result.value,core.calls,core.hostBits+shiftedA.bitSteps+shiftedB.bitSteps+result.bitSteps,
    core.formationWrites+3*n^2,core.oracleWork,core.answerWrites⟩

def encodeOptionalCell (sentinel : Cell) : Option Cell → Result Cell
  | none => BinaryCell.copy sentinel
  | some a => BinaryCell.copy a

@[simp] theorem encodeOptionalCell_view (s : Cell) (a : Option Cell) :
    BinaryCell.view (encodeOptionalCell s a).value =
      MinPlusReduction.encode (BinaryCell.view s) (a.map BinaryCell.view) := by
  cases a <;> simp [encodeOptionalCell,MinPlusReduction.encode]

def restoreCell (threshold : Cell) (c : Cell) : Result (Option Cell) :=
  let test := less threshold c
  if test.value then ⟨none,test.bitSteps+2⟩
  else
    let copied := BinaryCell.copy c
    ⟨some copied.value,test.bitSteps+copied.bitSteps+2⟩

@[simp] theorem restoreCell_view (threshold c : Cell) :
    Option.map BinaryCell.view (restoreCell threshold c).value =
      if BinaryCell.view threshold < BinaryCell.view c then none else some (BinaryCell.view c) := by
  have ht := less_true threshold c
  by_cases h : (less threshold c).value=true
  · simp [restoreCell,h,ht.mp h]
  · have hn : ¬ BinaryCell.view threshold < BinaryCell.view c := by simpa only [←ht] using h
    simp [restoreCell,h,hn]

def optionalProduct {n : ℕ} {Payload : Type} (O : Oracle n Payload) (W : ℕ)
    (A B : OptionalTable n) : Execution n (Option Cell) Payload :=
  let s := BinaryMultiplierAdapter.encodeInteger (APSPAlgorithm.sentinel W : ℤ)
  let threshold := BinaryMultiplierAdapter.encodeInteger (2*(W : ℤ))
  let encodedA := tabulate (fun i j => encodeOptionalCell s.value (StoredMinPlusAPSP.decode A i j))
  let encodedB := tabulate (fun i j => encodeOptionalCell s.value (StoredMinPlusAPSP.decode B i j))
  let core := signedProduct O (MinPlusReduction.signedLevels (APSPAlgorithm.sentinel W))
    encodedA.value encodedB.value s.value s.value
  let restored := tabulate (fun i j => restoreCell threshold.value (StoredMinPlusAPSP.decode core.value i j))
  ⟨restored.value,core.calls,
    core.hostBits+s.bitSteps+threshold.bitSteps+encodedA.bitSteps+encodedB.bitSteps+restored.bitSteps+
      8*(W.size+2)^2,
    core.formationWrites+3*n^2,core.oracleWork,core.answerWrites⟩

def initialCell (diagonal : Bool) (a : Option Cell) : Result (Option Cell) :=
  if diagonal then
    match a with
    | none => ⟨some BinaryCell.zero,2⟩
    | some z =>
        let test := less z BinaryCell.zero
        if test.value then
          let copied := BinaryCell.copy z
          ⟨some copied.value,test.bitSteps+copied.bitSteps+2⟩
        else ⟨some BinaryCell.zero,test.bitSteps+2⟩
  else
    match a with
    | none => ⟨none,2⟩
    | some z => let copied := BinaryCell.copy z; ⟨some copied.value,copied.bitSteps+2⟩

@[simp] theorem initialCell_view (diagonal : Bool) (a : Option Cell) :
    Option.map BinaryCell.view (initialCell diagonal a).value =
      if diagonal then
        match a.map BinaryCell.view with
        | none => some 0
        | some z => some (min 0 z)
      else a.map BinaryCell.view := by
  cases diagonal with
  | false => cases a <;> simp [initialCell]
  | true =>
    cases a with
    | none => rfl
    | some z =>
      by_cases h : (less z BinaryCell.zero).value=true
      · have hz : BinaryCell.view z < 0 := by simpa using (less_true z BinaryCell.zero).mp h
        simp [initialCell,h,min_eq_right hz.le]
      · have hz : 0 ≤ BinaryCell.view z := by
          have hn := mt (less_true z BinaryCell.zero).mpr h
          simpa using hn
        simp [initialCell,h,min_eq_left hz]

def squared {n : ℕ} {Payload : Type} (O : Oracle n Payload) (w : OptionalTable n)
    (B : ℕ) : ℕ → Execution n (Option Cell) Payload
  | 0 =>
    let initial := tabulate (fun i j => initialCell (decide (i=j)) (StoredMinPlusAPSP.decode w i j))
    ⟨initial.value,[],initial.bitSteps,n^2,0,0⟩
  | k+1 =>
    let previous := squared O w B k
    let current := optionalProduct O B previous.value previous.value
    ⟨current.value,previous.calls++current.calls,previous.hostBits+current.hostBits+previous.calls.length+4,
      previous.formationWrites+current.formationWrites,previous.oracleWork+current.oracleWork,
      previous.answerWrites+current.answerWrites⟩

def apsp {n : ℕ} {Payload : Type} (O : Oracle n Payload) (w : OptionalTable n) (W : ℕ) :
    Execution n (Option Cell) Payload :=
  squared O w (APSPAlgorithm.globalBound n W) (APSPReduction.rounds n)

theorem signedProduct_value {n : ℕ} {Payload NativePayload : Type} (O : Oracle n Payload)
    (N : StoredMinPlusAPSP.DenseOracle n NativePayload) (hON : Refines O N) (d : ℕ)
    (A B : IntTable n) (u v : Cell) :
    viewTable (signedProduct O d A B u v).value =
      (StoredMinPlusAPSP.signedProduct N d (viewTable A) (viewTable B)
        (BinaryCell.view u) (BinaryCell.view v)).value := by
  have hc := bitScale_value O N hON d (shift A u).value (shift B v).value
  rw [shift_view,shift_view] at hc
  apply Vector.ext
  intro i hi
  apply Vector.ext
  intro j hj
  have he := congrArg (fun T => StoredMinPlusAPSP.decode T ⟨i,hi⟩ ⟨j,hj⟩) hc
  simpa [signedProduct,viewTable,tabulate,StoredMinPlusAPSP.signedProduct,
    StoredMinPlusAPSP.decode,StoredMinPlusAPSP.store,Vector.get] using
      congrArg (fun z : ℤ => z-BinaryCell.view u-BinaryCell.view v) he

theorem optionalProduct_value {n : ℕ} {Payload NativePayload : Type} (O : Oracle n Payload)
    (N : StoredMinPlusAPSP.DenseOracle n NativePayload) (hON : Refines O N) (W : ℕ)
    (A B : OptionalTable n) :
    viewOptional (optionalProduct O W A B).value =
      (StoredMinPlusAPSP.optionalProduct N W (viewOptional A) (viewOptional B)).value := by
  let s := BinaryMultiplierAdapter.encodeInteger (APSPAlgorithm.sentinel W : ℤ)
  have hencode (C : OptionalTable n) :
      viewTable (tabulate (fun i j => encodeOptionalCell s.value (StoredMinPlusAPSP.decode C i j))).value =
        StoredMinPlusAPSP.store (fun i j => MinPlusReduction.encode (APSPAlgorithm.sentinel W)
          (StoredMinPlusAPSP.decode (viewOptional C) i j)) := by
    rw [viewTable_tabulate]
    apply congrArg StoredMinPlusAPSP.store
    funext i j
    rw [encodeOptionalCell_view]
    simp only [viewOptional_get,s,BinaryCell.view,BinaryMultiplierAdapter.encodeInteger_view]
  have hc := signedProduct_value O N hON (MinPlusReduction.signedLevels (APSPAlgorithm.sentinel W))
    (tabulate (fun i j => encodeOptionalCell s.value (StoredMinPlusAPSP.decode A i j))).value
    (tabulate (fun i j => encodeOptionalCell s.value (StoredMinPlusAPSP.decode B i j))).value s.value s.value
  rw [hencode,hencode] at hc
  simp only [s,BinaryCell.view,BinaryMultiplierAdapter.encodeInteger_view] at hc
  apply Vector.ext
  intro i hi
  apply Vector.ext
  intro j hj
  have he := congrArg (fun T => StoredMinPlusAPSP.decode T ⟨i,hi⟩ ⟨j,hj⟩) hc
  simp only [viewTable_get] at he
  simpa [optionalProduct,viewOptional,tabulate,StoredMinPlusAPSP.optionalProduct,
    StoredMinPlusAPSP.decode,StoredMinPlusAPSP.store,Vector.get,s,
    BinaryCell.view,BinaryMultiplierAdapter.encodeInteger_view] using
      congrArg (fun z : ℤ => if 2*(W : ℤ)<z then (none : Option ℤ) else some z) he

theorem squared_value {n : ℕ} {Payload NativePayload : Type} (O : Oracle n Payload)
    (N : StoredMinPlusAPSP.DenseOracle n NativePayload) (hON : Refines O N)
    (w : OptionalTable n) (B k : ℕ) :
    viewOptional (squared O w B k).value = (StoredMinPlusAPSP.squared N (viewOptional w) B k).value := by
  induction k with
  | zero =>
    apply Vector.ext
    intro i hi
    apply Vector.ext
    intro j hj
    simp [squared,viewOptional,tabulate,StoredMinPlusAPSP.squared,StoredMinPlusAPSP.store,
      StoredMinPlusAPSP.decode,APSPAlgorithm.initial,Vector.get]
    all_goals rfl
  | succ k ih =>
    change viewOptional (optionalProduct O B (squared O w B k).value (squared O w B k).value).value = _
    rw [optionalProduct_value O N hON,ih]
    rfl

theorem apsp_correct {n : ℕ} {Payload NativePayload : Type} (O : Oracle n Payload)
    (N : StoredMinPlusAPSP.DenseOracle n NativePayload) (hON : Refines O N)
    (hN : StoredMinPlusAPSP.DenseOracleCorrect N) (w : OptionalTable n) (W : ℕ)
    (hw : APSPReduction.EdgeBound (StoredMinPlusAPSP.decode (viewOptional w)) W)
    (hno : APSPReduction.NoNegativeCycles (StoredMinPlusAPSP.decode (viewOptional w))) :
    APSPReduction.IsAPSP (StoredMinPlusAPSP.decode (viewOptional w))
      (StoredMinPlusAPSP.decode (viewOptional (apsp O w W).value)) := by
  have hv := squared_value O N hON w (APSPAlgorithm.globalBound n W) (APSPReduction.rounds n)
  simpa only [apsp,hv,StoredMinPlusAPSP.apsp] using StoredMinPlusAPSP.apsp_correct N hN (viewOptional w) W hw hno

def Call.query {n : ℕ} {Payload : Type} (c : Call n Payload) : APSPAlgorithm.Query (Fin n) :=
  c.erase.query

theorem targetTable_view {n : ℕ} (C : IntTable n) (offset : Cell) :
    viewTable (tabulate (fun i j => targetCell (StoredMinPlusAPSP.decode C i j) offset)).value =
      StoredMinPlusAPSP.store (fun i j => -(2*StoredMinPlusAPSP.decode (viewTable C) i j+
        BinaryCell.view offset)) := by
  rw [viewTable_tabulate]
  simp only [targetCell_view,viewTable_get]

theorem bitScale_trace {n : ℕ} {Payload NativePayload : Type} (O : Oracle n Payload)
    (N : StoredMinPlusAPSP.DenseOracle n NativePayload) (hON : Refines O N)
    (d : ℕ) (A B : IntTable n) :
    (bitScale O d A B).calls.map Call.query=
      MinPlusReduction.queryTrace (StoredMinPlusAPSP.semanticOracle N) d
        (StoredMinPlusAPSP.decode (viewTable A)) (StoredMinPlusAPSP.decode (viewTable B)) := by
  induction d generalizing A B with
  | zero => rfl
  | succ d ih =>
    simp only [bitScale,List.map_append,List.map_cons,List.map_nil,Call.query,Call.erase,
      StoredMinPlusAPSP.Call.query,ih,half_view,targetTable_view,bitScale_value O N hON,
      StoredMinPlusAPSP.decode_store,BinaryCell.zero_view,one_view,add_zero,
      StoredMinPlusAPSP.bitScale_value]
    simp only [MinPlusReduction.queryTrace,StoredMinPlusAPSP.half,
      StoredMinPlusAPSP.decode_store]
    all_goals rfl


theorem encodeTable_view {n : ℕ} (sentinel : Cell) (A : OptionalTable n) :
    viewTable (tabulate (fun i j => encodeOptionalCell sentinel (StoredMinPlusAPSP.decode A i j))).value =
      StoredMinPlusAPSP.store (fun i j => MinPlusReduction.encode (BinaryCell.view sentinel)
        (StoredMinPlusAPSP.decode (viewOptional A) i j)) := by
  rw [viewTable_tabulate]
  apply congrArg StoredMinPlusAPSP.store
  funext i j
  simp only [encodeOptionalCell_view,viewOptional_get]

theorem signedProduct_trace {n : ℕ} {Payload NativePayload : Type} (O : Oracle n Payload)
    (N : StoredMinPlusAPSP.DenseOracle n NativePayload) (hON : Refines O N) (d : ℕ)
    (A B : IntTable n) (u v : Cell) :
    (signedProduct O d A B u v).calls.map Call.query=
      (StoredMinPlusAPSP.signedProduct N d (viewTable A) (viewTable B)
        (BinaryCell.view u) (BinaryCell.view v)).calls.map StoredMinPlusAPSP.Call.query := by
  simp only [signedProduct,StoredMinPlusAPSP.signedProduct,bitScale_trace O N hON,
    StoredMinPlusAPSP.bitScale_trace,shift_view]

theorem optionalProduct_trace {n : ℕ} {Payload NativePayload : Type} (O : Oracle n Payload)
    (N : StoredMinPlusAPSP.DenseOracle n NativePayload) (hON : Refines O N) (W : ℕ)
    (A B : OptionalTable n) :
    (optionalProduct O W A B).calls.map Call.query=
      (StoredMinPlusAPSP.optionalProduct N W (viewOptional A) (viewOptional B)).calls.map
        StoredMinPlusAPSP.Call.query := by
  simp only [optionalProduct,StoredMinPlusAPSP.optionalProduct,signedProduct_trace O N hON,
    encodeTable_view,BinaryCell.view,BinaryMultiplierAdapter.encodeInteger_view]

theorem squared_trace {n : ℕ} {Payload NativePayload : Type} (O : Oracle n Payload)
    (N : StoredMinPlusAPSP.DenseOracle n NativePayload) (hON : Refines O N)
    (w : OptionalTable n) (B k : ℕ) :
    (squared O w B k).calls.map Call.query=
      (StoredMinPlusAPSP.squared N (viewOptional w) B k).calls.map StoredMinPlusAPSP.Call.query := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [squared,StoredMinPlusAPSP.squared,List.map_append,ih,optionalProduct_trace O N hON,
      squared_value O N hON]


def callWork {n : ℕ} {Payload : Type} (calls : List (Call n Payload)) : ℕ :=
  (calls.map (fun c => c.output.work)).sum

def Call.Faithful {n : ℕ} {Payload : Type} (O : Oracle n Payload) (c : Call n Payload) : Prop :=
  c.output=O c.left c.right c.target

theorem bitScale_calls {n : ℕ} {Payload : Type} (O : Oracle n Payload)
    (d : ℕ) (A B : IntTable n) : (bitScale O d A B).calls.length=2*d := by
  induction d generalizing A B with
  | zero => rfl
  | succ d ih => simp only [bitScale,List.length_append,List.length_cons,List.length_nil,ih]; omega

theorem bitScale_formationWrites {n : ℕ} {Payload : Type} (O : Oracle n Payload)
    (d : ℕ) (A B : IntTable n) : (bitScale O d A B).formationWrites=(5*d+1)*n^2 := by
  induction d generalizing A B with
  | zero => simp [bitScale]
  | succ d ih => simp only [bitScale,ih]; ring

theorem bitScale_oracleWork {n : ℕ} {Payload : Type} (O : Oracle n Payload)
    (d : ℕ) (A B : IntTable n) : (bitScale O d A B).oracleWork=callWork (bitScale O d A B).calls := by
  induction d generalizing A B with
  | zero => rfl
  | succ d ih =>
    have hp := ih (half A).value (half B).value
    unfold callWork at hp
    simp only [bitScale,callWork,List.map_append,List.map_cons,List.map_nil,
      List.sum_append,List.sum_cons,List.sum_nil]
    omega

theorem bitScale_calls_faithful {n : ℕ} {Payload : Type} (O : Oracle n Payload)
    (d : ℕ) (A B : IntTable n) : ∀ c∈(bitScale O d A B).calls,c.Faithful O := by
  induction d generalizing A B with
  | zero => simp [bitScale]
  | succ d ih =>
    intro c hc
    simp only [bitScale,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with hp | rfl | rfl
    · exact ih _ _ c hp
    · rfl
    · rfl

theorem optionalProduct_calls {n : ℕ} {Payload : Type} (O : Oracle n Payload)
    (W : ℕ) (A B : OptionalTable n) :
    (optionalProduct O W A B).calls.length=2*MinPlusReduction.signedLevels (APSPAlgorithm.sentinel W) :=
  bitScale_calls _ _ _ _

theorem optionalProduct_formationWrites {n : ℕ} {Payload : Type} (O : Oracle n Payload)
    (W : ℕ) (A B : OptionalTable n) :
    (optionalProduct O W A B).formationWrites=
      (5*MinPlusReduction.signedLevels (APSPAlgorithm.sentinel W)+7)*n^2 := by
  simp only [optionalProduct,signedProduct,bitScale_formationWrites]
  ring

theorem optionalProduct_oracleWork {n : ℕ} {Payload : Type} (O : Oracle n Payload)
    (W : ℕ) (A B : OptionalTable n) :
    (optionalProduct O W A B).oracleWork=callWork (optionalProduct O W A B).calls :=
  bitScale_oracleWork _ _ _ _

theorem optionalProduct_calls_faithful {n : ℕ} {Payload : Type} (O : Oracle n Payload)
    (W : ℕ) (A B : OptionalTable n) : ∀c∈(optionalProduct O W A B).calls,c.Faithful O :=
  bitScale_calls_faithful _ _ _ _

theorem squared_calls {n : ℕ} {Payload : Type} (O : Oracle n Payload)
    (w : OptionalTable n) (B k : ℕ) :
    (squared O w B k).calls.length=k*(2*MinPlusReduction.signedLevels (APSPAlgorithm.sentinel B)) := by
  induction k with
  | zero => simp [squared]
  | succ k ih => simp only [squared,List.length_append,ih,optionalProduct_calls]; ring

theorem squared_formationWrites {n : ℕ} {Payload : Type} (O : Oracle n Payload)
    (w : OptionalTable n) (B k : ℕ) :
    (squared O w B k).formationWrites=
      (1+k*(5*MinPlusReduction.signedLevels (APSPAlgorithm.sentinel B)+7))*n^2 := by
  induction k with
  | zero => simp [squared]
  | succ k ih => simp only [squared,ih,optionalProduct_formationWrites]; ring

theorem squared_oracleWork {n : ℕ} {Payload : Type} (O : Oracle n Payload)
    (w : OptionalTable n) (B k : ℕ) :
    (squared O w B k).oracleWork=callWork (squared O w B k).calls := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hs := optionalProduct_oracleWork O B (squared O w B k).value (squared O w B k).value
    unfold callWork at ih hs
    simp only [squared,callWork,List.map_append,List.sum_append]
    omega

theorem squared_calls_faithful {n : ℕ} {Payload : Type} (O : Oracle n Payload)
    (w : OptionalTable n) (B k : ℕ) : ∀ c∈(squared O w B k).calls,c.Faithful O := by
  induction k with
  | zero => simp [squared]
  | succ k ih =>
    intro c hc
    rcases List.mem_append.mp hc with hp | hs
    · exact ih c hp
    · exact optionalProduct_calls_faithful _ _ _ _ c hs

/-- The only graph integer serialization is this original boundary pass. -/
def encodeGraph {n : ℕ} (w : StoredMinPlusAPSP.OptionalTable n) : Result (OptionalTable n) :=
  tabulate (fun i j => match StoredMinPlusAPSP.decode w i j with
    | none => ⟨none,2⟩
    | some z => let encoded := BinaryMultiplierAdapter.encodeInteger z
                ⟨some encoded.value,encoded.bitSteps+2⟩)

theorem encodeGraph_view {n : ℕ} (w : StoredMinPlusAPSP.OptionalTable n) :
    viewOptional (encodeGraph w).value=w := by
  apply Vector.ext
  intro i hi
  apply Vector.ext
  intro j hj
  simp only [encodeGraph,viewOptional,tabulate,Vector.getElem_map,Vector.getElem_ofFn]
  change Option.map BinaryCell.view
    (match w[i][j] with
    | none => (⟨none,2⟩ : Result (Option Cell))
    | some z => let encoded := BinaryMultiplierAdapter.encodeInteger z
                ⟨some encoded.value,encoded.bitSteps+2⟩).value=w[i][j]
  cases h : w[i][j] <;> simp [BinaryCell.view,BinaryMultiplierAdapter.encodeInteger_view]

theorem encodeGraph_price {n : ℕ} (w : StoredMinPlusAPSP.OptionalTable n) (B : ℕ)
    (hw : ∀i j z,StoredMinPlusAPSP.decode w i j=some z→z.natAbs.size≤B) :
    (encodeGraph w).bitSteps ≤ n^2*(10*(B+1)^2+8*(n.size+1)+6) := by
  apply (tabulate_price _ (10*(B+1)^2+2) ?_).trans_eq
    (by ring)
  intro i j
  cases h : StoredMinPlusAPSP.decode w i j with
  | none => change 2≤10*(B+1)^2+2; omega
  | some z =>
    have he := BinaryMultiplierAdapter.encodeInteger_cost z
    have hb := hw i j z h
    change (BinaryMultiplierAdapter.encodeInteger z).bitSteps+2≤_
    have hp := Nat.pow_le_pow_left (Nat.add_le_add_right hb 1) 2
    nlinarith

/-- Graph serialization is shared across every adaptive triangle invocation. -/
def run {n : ℕ} {Payload : Type} (O : Oracle n Payload)
    (w : StoredMinPlusAPSP.OptionalTable n) (W : ℕ) : Execution n (Option Cell) Payload :=
  let loaded := encodeGraph w
  let core := apsp O loaded.value W
  ⟨core.value,core.calls,core.hostBits+loaded.bitSteps+32*(n.size+W.size+2)^2,
    core.formationWrites+n^2,core.oracleWork,core.answerWrites⟩

theorem run_correct {n : ℕ} {Payload NativePayload : Type} (O : Oracle n Payload)
    (N : StoredMinPlusAPSP.DenseOracle n NativePayload) (hON : Refines O N)
    (hN : StoredMinPlusAPSP.DenseOracleCorrect N)
    (w : StoredMinPlusAPSP.OptionalTable n) (W : ℕ)
    (hw : APSPReduction.EdgeBound (StoredMinPlusAPSP.decode w) W)
    (hno : APSPReduction.NoNegativeCycles (StoredMinPlusAPSP.decode w)) :
    APSPReduction.IsAPSP (StoredMinPlusAPSP.decode w)
      (StoredMinPlusAPSP.decode (viewOptional (run O w W).value)) := by
  have he := apsp_correct O N hON hN (encodeGraph w).value W
  simpa only [run,encodeGraph_view] using he (by simpa only [encodeGraph_view] using hw)
    (by simpa only [encodeGraph_view] using hno)

theorem run_oracleWork {n : ℕ} {Payload : Type} (O : Oracle n Payload)
    (w : StoredMinPlusAPSP.OptionalTable n) (W : ℕ) :
    (run O w W).oracleWork=callWork (run O w W).calls := squared_oracleWork _ _ _ _

theorem run_calls_faithful {n : ℕ} {Payload : Type} (O : Oracle n Payload)
    (w : StoredMinPlusAPSP.OptionalTable n) (W : ℕ) :
    ∀c∈(run O w W).calls,c.Faithful O := squared_calls_faithful _ _ _ _


theorem callWork_le {n : ℕ} {Payload : Type} (calls : List (Call n Payload)) (M : ℕ)
    (h : ∀c∈calls,c.output.work≤M) : callWork calls≤calls.length*M := by
  induction calls with
  | nil => simp [callWork]
  | cons c cs ih =>
    have hh := h c (by simp)
    have ht := ih (fun t ht => h t (by simp [ht]))
    simp only [callWork,List.map_cons,List.sum_cons,List.length_cons] at *
    nlinarith


theorem apsp_query_bound {n : ℕ} {Payload NativePayload : Type} (O : Oracle n Payload)
    (N : StoredMinPlusAPSP.DenseOracle n NativePayload) (hON : Refines O N)
    (hN : StoredMinPlusAPSP.DenseOracleCorrect N) (w : OptionalTable n) (W : ℕ)
    (hw : APSPReduction.EdgeBound (StoredMinPlusAPSP.decode (viewOptional w)) W)
    (c : Call n Payload) (hc : c∈(apsp O w W).calls) :
    APSPAlgorithm.SymmetricQueryBound c.query ((64*n*W+13 : ℕ) : ℤ) := by
  have hm : c.query∈(apsp O w W).calls.map Call.query := List.mem_map.mpr ⟨c,hc,rfl⟩
  change c.query∈(squared O w (APSPAlgorithm.globalBound n W) (APSPReduction.rounds n)).calls.map Call.query at hm
  rw [squared_trace O N hON] at hm
  obtain ⟨native,hn,he⟩ := List.mem_map.mp hm
  rw [←he]
  exact StoredMinPlusAPSP.apsp_query_bound N hN (viewOptional w) W hw native hn


theorem run_query_bound {n : ℕ} {Payload NativePayload : Type} (O : Oracle n Payload)
    (N : StoredMinPlusAPSP.DenseOracle n NativePayload) (hON : Refines O N)
    (hN : StoredMinPlusAPSP.DenseOracleCorrect N)
    (w : StoredMinPlusAPSP.OptionalTable n) (W : ℕ)
    (hw : APSPReduction.EdgeBound (StoredMinPlusAPSP.decode w) W)
    (c : Call n Payload) (hc : c∈(run O w W).calls) :
    APSPAlgorithm.SymmetricQueryBound c.query ((64*n*W+13 : ℕ) : ℤ) := by
  exact apsp_query_bound O N hON hN (encodeGraph w).value W
    (by simpa only [encodeGraph_view] using hw) c hc


#print axioms run_query_bound
#print axioms run_correct
#print axioms run_oracleWork
#print axioms run_calls_faithful
#print axioms apsp_query_bound
#print axioms squared_trace
#print axioms bitScale_trace
#print axioms bitScale_value
#print axioms signedProduct_value
#print axioms optionalProduct_value
#print axioms squared_value
#print axioms apsp_correct
#print axioms squared_calls
#print axioms squared_formationWrites
#print axioms squared_oracleWork
#print axioms squared_calls_faithful
#print axioms encodeGraph_view
#print axioms encodeGraph_price

end ThinMatrix.BinaryAPSPCaller

