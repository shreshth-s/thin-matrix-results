import CroppedHighQueries

set_option autoImplicit false

/-! Retain counted HIGH children and sum every request's full cyclic row.
The charge combines the children's binary-arithmetic/indexed-register model
with the explicitly separated binary-addition and indexed-control charges of
the existing row accumulator. It is not a pure binary-address cost. -/
namespace ThinMatrix.CountedCyclicCollection
open BinaryCell BinaryGroupedCoordinates BinaryGroupedPreparation GroupedPreparation
open scoped BigOperators

structure Prepared (α : Type) (S M q : ℕ) where
  children : Vector (ToomCook.Counted α) S
  values : Vector α S
  rows : Run (Vector (RetainedWindowCompletion.SumRow S q) M)

def output {α : Type} {S M q : ℕ} (out : Prepared α S M q) (i : Fin M) : Vector Cell q :=
  (out.rows.value.get i).output

def execute {α β : Type} {S M q : ℕ} (shape : Vector β S) (child : Fin S → ToomCook.Counted α)
    (get : α → Fin M → Vector Cell q) : ToomCook.Counted (Prepared α S M q) :=
  let children := ofStoredFn shape child
  let values := ofStoredFn children (fun i => (children.get i).value)
  let rows := tabulate (Vector.replicate M ()) (RootProductCollection.sumRow values get)
  ⟨⟨children,values,rows⟩,(∑ s, (children.get s).operations)+rows.bitSteps+rows.control+64*S+3*M+16⟩

theorem execute_value {α β : Type} {S M q : ℕ} (shape : Vector β S) (child : Fin S → ToomCook.Counted α)
    (get : α → Fin M → Vector Cell q) (i : Fin M) (r : Fin q) :
    view ((output (execute shape child get).value i).get r)=∑ s, view ((get (child s).value i).get r) := by
  simp only [execute,output,tabulate_get,RootProductCollection.sumRow_value,ofStoredFn_eq,Vector.get_ofFn]

theorem execute_bound {α β : Type} {S M q : ℕ} (shape : Vector β S) (child : Fin S → ToomCook.Counted α)
    (get : α → Fin M → Vector Cell q) (A : ℕ)
    (ha : ∀ s i r, (view ((get (child s).value i).get r)).natAbs≤A) (i : Fin M) (r : Fin q) :
    (view ((output (execute shape child get).value i).get r)).natAbs≤S*A := by
  simp only [output,execute,tabulate_get]
  apply RootProductCollection.sumRow_bound _ _ A _ i r
  simpa only [ofStoredFn_eq,Vector.get_ofFn] using ha

def budget {S : ℕ} (childBudget : Fin S → ℕ) (M q A : ℕ) : ℕ :=
  (∑ s, childBudget s)+M*(S*(q*BackendScalarBits.backendScalarUnit (S*A).size))+
    (M*(S*(40*q+40)+3*q+44)+8)+64*S+3*M+16

theorem execute_work {α β : Type} {S M q : ℕ} (shape : Vector β S) (child : Fin S → ToomCook.Counted α)
    (get : α → Fin M → Vector Cell q) (A : ℕ) (childBudget : Fin S → ℕ)
    (ha : ∀ s i r, (view ((get (child s).value i).get r)).natAbs≤A)
    (hb : ∀ s, (child s).operations≤childBudget s) :
    (execute shape child get).operations≤budget childBudget M q A := by
  let values := ofStoredFn (ofStoredFn shape child) (fun i => ((ofStoredFn shape child).get i).value)
  have hv : ∀ s i r, (view ((get (values.get s) i).get r)).natAbs≤A := by
    simpa only [values,ofStoredFn_eq,Vector.get_ofFn] using ha
  have hs := Finset.sum_le_sum (fun s (_ : s∈(Finset.univ : Finset (Fin S))) => hb s)
  have hab := tabulate_bits (Vector.replicate M ()) (RootProductCollection.sumRow values get)
    (fun i => RootProductCollection.sumRow_bits values get A hv i)
  have hac := tabulate_control (Vector.replicate M ()) (RootProductCollection.sumRow values get)
    (fun i => RootProductCollection.sumRow_control values get i)
  simp only [execute,ofStoredFn_eq,Vector.get_ofFn,budget]
  simp only [values,ofStoredFn_eq,Vector.get_ofFn] at hab hac
  simp only [Nat.add_assoc,Nat.reduceAdd] at hac ⊢
  omega

#print axioms execute_value
#print axioms execute_bound
#print axioms execute_work
end ThinMatrix.CountedCyclicCollection
