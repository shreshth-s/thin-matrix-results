import WeightedRootProducts
import RetainedWindowCompletion

set_option autoImplicit false

/-! Retain child executions and accumulate each request's entire cyclic row.
Children, row-reference tables, selectors and every addition are charged.
Nothing is deduplicated or selected after the fact. -/
namespace ThinMatrix.RootProductCollection
open BinaryCell BinaryGroupedCoordinates BinaryGroupedPreparation GroupedPreparation
open scoped BigOperators

structure Prepared (α : Type) (S M q : ℕ) where
  children : Run (Vector α S)
  rows : Run (Vector (RetainedWindowCompletion.SumRow S q) M)

def output {α : Type} {S M q : ℕ} (out : Prepared α S M q) (i : Fin M) : Vector Cell q :=
  (out.rows.value.get i).output

def sumRow {α : Type} {S M q : ℕ} (children : Vector α S) (get : α → Fin M → Vector Cell q)
    (i : Fin M) : Run (RetainedWindowCompletion.SumRow S q) :=
  let data := ofStoredFn children (fun s => get (children.get s) i)
  let mask := ofStoredFn children (fun _ => true)
  let out := BinaryGroupedCompletion.runRow mask data
  ⟨⟨data,mask,out.value⟩,out.bitSteps,out.control+16*children.toArray.size+8⟩

theorem sumRow_value {α : Type} {S M q : ℕ} (children : Vector α S) (get : α → Fin M → Vector Cell q)
    (i : Fin M) (r : Fin q) : view ((sumRow children get i).value.output.get r)=∑ s, view ((get (children.get s) i).get r) := by
  simp only [sumRow,BinaryGroupedCompletion.runRow_view,ofStoredFn_eq,Vector.get_ofFn,↓reduceIte]

theorem sumRow_bound {α : Type} {S M q : ℕ} (children : Vector α S) (get : α → Fin M → Vector Cell q)
    (A : ℕ) (ha : ∀ s i r, (view ((get (children.get s) i).get r)).natAbs≤A) (i : Fin M) (r : Fin q) :
    (view ((sumRow children get i).value.output.get r)).natAbs≤S*A := by
  apply BinaryGroupedCompletion.runRow_abs
  simpa only [ofStoredFn_eq,Vector.get_ofFn] using fun s r => ha s i r

theorem sumRow_bits {α : Type} {S M q : ℕ} (children : Vector α S) (get : α → Fin M → Vector Cell q)
    (A : ℕ) (ha : ∀ s i r, (view ((get (children.get s) i).get r)).natAbs≤A) (i : Fin M) :
    (sumRow children get i).bitSteps≤S*(q*BackendScalarBits.backendScalarUnit (S*A).size) := by
  apply BinaryGroupedCompletion.runRow_bits A _ _ _ (le_refl _)
  simpa only [ofStoredFn_eq,Vector.get_ofFn] using fun s r => ha s i r

theorem sumRow_control {α : Type} {S M q : ℕ} (children : Vector α S) (get : α → Fin M → Vector Cell q)
    (i : Fin M) : (sumRow children get i).control≤S*(40*q+40)+3*q+12 := by
  have h := BinaryGroupedCompletion.runRow_control
    (ofStoredFn children (fun _ => true)) (ofStoredFn children (fun s => get (children.get s) i))
  simp only [sumRow,Vector.size_toArray]
  nlinarith

def execute {α β : Type} {S M q : ℕ} (shape : Vector β S) (child : Fin S → Run α)
    (get : α → Fin M → Vector Cell q) : Run (Prepared α S M q) :=
  let children := tabulate shape child
  let rows := tabulate (Vector.replicate M ()) (sumRow children.value get)
  ⟨⟨children,rows⟩,children.bitSteps+rows.bitSteps,children.control+rows.control+3*M+12⟩

theorem execute_value {α β : Type} {S M q : ℕ} (shape : Vector β S) (child : Fin S → Run α)
    (get : α → Fin M → Vector Cell q) (i : Fin M) (r : Fin q) :
    view ((output (execute shape child get).value i).get r)=∑ s, view ((get (child s).value i).get r) := by
  simp only [execute,output,tabulate_get,sumRow_value]

theorem execute_bound {α β : Type} {S M q : ℕ} (shape : Vector β S) (child : Fin S → Run α)
    (get : α → Fin M → Vector Cell q) (A : ℕ)
    (ha : ∀ s i r, (view ((get (child s).value i).get r)).natAbs≤A) (i : Fin M) (r : Fin q) :
    (view ((output (execute shape child get).value i).get r)).natAbs≤S*A := by
  simp only [output,execute,tabulate_get]
  apply sumRow_bound _ _ A _ i r
  simpa only [tabulate_get] using ha

def bitBudget {S : ℕ} (budget : Fin S → ℕ) (M q A : ℕ) : ℕ :=
  (∑ s, budget s)+M*(S*(q*BackendScalarBits.backendScalarUnit (S*A).size))
def controlBudget {S : ℕ} (budget : Fin S → ℕ) (M q : ℕ) : ℕ :=
  GraphPrefixProgram.sumControl budget+(M*(S*(40*q+40)+3*q+44)+8)+3*M+12

theorem execute_bits {α β : Type} {S M q : ℕ} (shape : Vector β S) (child : Fin S → Run α)
    (get : α → Fin M → Vector Cell q) (A : ℕ) (budget : Fin S → ℕ)
    (ha : ∀ s i r, (view ((get (child s).value i).get r)).natAbs≤A)
    (hb : ∀ s, (child s).bitSteps≤budget s) :
    (execute shape child get).bitSteps≤bitBudget budget M q A := by
  apply Nat.add_le_add
  · exact GraphPrefixProgram.tabulate_bits_vary _ _ _ hb
  · apply tabulate_bits; intro i
    apply sumRow_bits _ _ A _ i
    simpa only [tabulate_get] using ha

theorem execute_control {α β : Type} {S M q : ℕ} (shape : Vector β S) (child : Fin S → Run α)
    (get : α → Fin M → Vector Cell q) (budget : Fin S → ℕ)
    (hb : ∀ s, (child s).control≤budget s) :
    (execute shape child get).control≤controlBudget budget M q := by
  have hc := GraphPrefixProgram.tabulate_control_vary shape child budget hb
  have hr := tabulate_control (Vector.replicate M ()) (sumRow (tabulate shape child).value get)
    (fun i => sumRow_control _ _ i)
  dsimp only [execute]
  unfold controlBudget
  simp only [GraphPrefixProgram.sumControl,Nat.add_assoc,Nat.reduceAdd] at hc hr ⊢
  omega

#print axioms sumRow_value
#print axioms sumRow_bound
#print axioms sumRow_bits
#print axioms sumRow_control
#print axioms execute_value
#print axioms execute_bound
#print axioms execute_bits
#print axioms execute_control
end ThinMatrix.RootProductCollection
