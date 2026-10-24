import CroppedHighQueries
import FiniteRequestRouter

set_option autoImplicit false
set_option maxHeartbeats 1400000

/-! Read one requested cyclic coefficient from retained HIGH tables. Table
construction still retains and charges every cyclic coefficient. Querying
is restricted to routed own-band occurrences; each original occurrence ID
is preserved and no cyclic-vector loop appears in the per-request budget. -/
namespace ThinMatrix.SelectedHighQueries
open BinaryCell BinaryGroupedCoordinates BinaryGroupedPreparation
open scoped BigOperators
variable {L m q M S : ℕ}

def lookup (t : ℕ) (shape : ThinMatrixBackend.ShapePlan L m)
    (request : GraphCompletionRequests.Physical L m q) (table : BinaryHighTable.Table q) : ToomCook.Counted Cell :=
  let d := CroppedHighQueries.geometry shape request
  let out := BinaryHighTable.query t d.embedding request.outside table request.coefficient
  ⟨out.value,out.operations+1000*(L+m+1)^5+16⟩

def rowBudget (L m t A : ℕ) : ℕ :=
  ((2*m).choose t*4^t)*BinaryHighTable.queryUnit L (2*m) (CroppedHighQueries.queryMagnitude m t A).size+
    1000*(L+m+1)^5+16

theorem lookup_work (t A : ℕ) (ht : t ≤ 2*m) (shape : ThinMatrixBackend.ShapePlan L m)
    (request : GraphCompletionRequests.Physical L m q) (table : BinaryHighTable.Table q)
    (hA : BinaryHighTable.Bounds.TableBound A table) :
    (lookup t shape request table).operations ≤ rowBudget L m t A :=
  Nat.add_le_add_right (Nat.add_le_add_right
    (BinaryHighTable.query_work t A _ _ _ request.coefficient ht hA) _) _

theorem lookup_bound (t A : ℕ) (shape : ThinMatrixBackend.ShapePlan L m)
    (request : GraphCompletionRequests.Physical L m q) (table : BinaryHighTable.Table q)
    (hA : BinaryHighTable.Bounds.TableBound A table) :
    (lookup t shape request table).value.view.natAbs ≤ CroppedHighQueries.queryMagnitude m t A :=
  BinaryHighTable.query_bound t A _ _ _ _ hA

theorem lookup_matches (t bandL bandR : ℕ) (shape : ThinMatrixBackend.ShapePlan L m)
    (request : GraphCompletionRequests.Physical L m q) (table : BinaryHighTable.Table q)
    (ha : CroppedHighQueries.accepts bandL bandR request=true) :
    (lookup t shape request table).value.view=
      view ((CroppedHighQueries.output (CroppedHighQueries.row t bandL bandR shape request table).value).get request.coefficient) := by
  rw [CroppedHighQueries.row_value,ha]
  rfl

structure Prepared (M : ℕ) where
  indices : List (Fin M)
  values : Vector Cell indices.length

def query (t : ℕ) (shape : ThinMatrixBackend.ShapePlan L m)
    (requests : Vector (GraphCompletionRequests.Physical L m q) M) (ids : List (Fin M))
    (table : BinaryHighTable.Table q) : ToomCook.Counted (Prepared M) :=
  let children := Vector.ofFn (fun i : Fin ids.length => lookup t shape (requests.get (ids.get i)) table)
  let values := GroupedPreparation.ofStoredFn children (fun i => (children.get i).value)
  ⟨⟨ids,values⟩,(∑ i, (children.get i).operations)+32*ids.length+8⟩

theorem query_value (t : ℕ) (shape : ThinMatrixBackend.ShapePlan L m)
    (requests : Vector (GraphCompletionRequests.Physical L m q) M) (ids : List (Fin M))
    (table : BinaryHighTable.Table q) (i : Fin ids.length) :
    ((query t shape requests ids table).value.values.get i).view=
      (lookup t shape (requests.get (ids.get i)) table).value.view := by
  simp only [query,GroupedPreparation.ofStoredFn_eq,Vector.get_ofFn]

theorem query_work (t A : ℕ) (ht : t ≤ 2*m) (shape : ThinMatrixBackend.ShapePlan L m)
    (requests : Vector (GraphCompletionRequests.Physical L m q) M) (ids : List (Fin M))
    (table : BinaryHighTable.Table q) (hA : BinaryHighTable.Bounds.TableBound A table) :
    (query t shape requests ids table).operations ≤ ids.length*(rowBudget L m t A+32)+8 := by
  have hs : (∑ i : Fin ids.length, (lookup t shape (requests.get (ids.get i)) table).operations) ≤ ids.length*rowBudget L m t A := by
    calc
      _  ≤  ∑ _ : Fin ids.length,rowBudget L m t A := Finset.sum_le_sum (fun i _ => lookup_work t A ht _ _ _ hA)
      _ = _ := by simp
  simp only [query,Vector.get_ofFn]
  nlinarith

/-- HIGH table construction occurs once; request routing and reads use the
returned table repeatedly without rebuilding its full coefficient vectors. -/
def store (L m t q cap A : ℕ) (X Y : BinarySourceFormation.RawStore L q) :=
  BinaryCroppedHighBoxes.execute L m t q cap A X Y

theorem stored_matches [NeZero q] (t cap A bandL bandR : ℕ) (shape : ThinMatrixBackend.ShapePlan L m)
    (requests : Vector (GraphCompletionRequests.Physical L m q) M) (ids : List (Fin M))
    (X Y : BinarySourceFormation.RawStore L q) (i : Fin ids.length)
    (hown : ∀ j∈ids,CroppedHighQueries.accepts bandL bandR (requests.get j)=true) :
    ((query t shape requests ids (store L m t q cap A X Y).boxes).value.values.get i).view=
      view ((CroppedHighQueries.get (CroppedHighQueries.execute t cap A bandL bandR shape requests X Y).value
        (ids.get i)).get (requests.get (ids.get i)).coefficient) := by
  rw [query_value]
  simp only [CroppedHighQueries.get,CroppedHighQueries.execute,GroupedPreparation.ofStoredFn_eq,Vector.get_ofFn]
  exact lookup_matches _ _ _ _ _ _ (hown _ (List.get_mem _ _))

def bandKey (request : GraphCompletionRequests.Physical L m q)
    (hL : request.bandL<S) (hR : request.bandR<S) : Fin (S*S) := finProdFinEquiv (⟨request.bandL,hL⟩,⟨request.bandR,hR⟩)

def route (requests : Vector (GraphCompletionRequests.Physical L m q) M)
    (hb : ∀ i,(requests.get i).bandL<S ∧ (requests.get i).bandR<S) :=
  let keys := Vector.ofFn (fun i => bandKey (requests.get i) (hb i).1 (hb i).2)
  let out := FiniteRequestRouter.run keys
  (⟨out.value,out.bitSteps,out.control+M*(128*((S*S).size+L+m+1)^3)+8⟩ : Run _)

def ids (tree : BooleanRequestRouter.Tree (Fin M) (S*S).size) (a b : Fin S) :=
  FiniteRequestRouter.ids tree (finProdFinEquiv (a,b))

theorem ids_mem (requests : Vector (GraphCompletionRequests.Physical L m q) M)
    (hb : ∀ i,(requests.get i).bandL<S ∧ (requests.get i).bandR<S) (a b : Fin S) (i : Fin M) :
    i∈(ids (route requests hb).value a b).value ↔ CroppedHighQueries.accepts a.val b.val (requests.get i)=true := by
  simp only [ids,route,FiniteRequestRouter.ids_value,FiniteRequestRouter.selected,List.mem_filter,
    List.mem_finRange,true_and,decide_eq_true_eq,Vector.get_ofFn,CroppedHighQueries.accepts,bandKey,
    Equiv.apply_eq_iff_eq,Prod.mk.injEq,Fin.ext_iff]

theorem routed_work (t A : ℕ) (ht : t ≤ 2*m) (shape : ThinMatrixBackend.ShapePlan L m)
    (requests : Vector (GraphCompletionRequests.Physical L m q) M)
    (hb : ∀ i,(requests.get i).bandL<S ∧ (requests.get i).bandR<S) (a b : Fin S)
    (table : BinaryHighTable.Table q) (hA : BinaryHighTable.Bounds.TableBound A table) :
    (query t shape requests (ids (route requests hb).value a b).value table).operations  ≤ 
      (ids (route requests hb).value a b).value.length*(rowBudget L m t A+32)+8 := query_work t A ht _ _ _ _ hA

theorem total (requests : Vector (GraphCompletionRequests.Physical L m q) M)
    (hb : ∀ i,(requests.get i).bandL<S ∧ (requests.get i).bandR<S) :
    BooleanRequestRouter.items (route requests hb).value=M := FiniteRequestRouter.total _

theorem route_cost (requests : Vector (GraphCompletionRequests.Physical L m q) M)
    (hb : ∀ i,(requests.get i).bandL<S ∧ (requests.get i).bandR<S) :
    (route requests hb).bitSteps=0 ∧ (route requests hb).control ≤
      24*(S*S+1)+M*(16*((S*S).size+1)^2+64*((S*S).size+1)^3+
        128*((S*S).size+L+m+1)^3+36)+36 := by
  have hh := FiniteRequestRouter.cost (Vector.ofFn (fun i => bandKey (requests.get i) (hb i).1 (hb i).2))
  refine ⟨hh.1,?_⟩
  simp only [route]
  nlinarith [hh.2]

theorem routed_matches [NeZero q] (t cap A : ℕ) (shape : ThinMatrixBackend.ShapePlan L m)
    (requests : Vector (GraphCompletionRequests.Physical L m q) M)
    (hb : ∀ i,(requests.get i).bandL<S ∧ (requests.get i).bandR<S) (a b : Fin S)
    (X Y : BinarySourceFormation.RawStore L q) (i : Fin (ids (route requests hb).value a b).value.length) :
    ((query t shape requests (ids (route requests hb).value a b).value (store L m t q cap A X Y).boxes).value.values.get i).view=
      view ((CroppedHighQueries.get (CroppedHighQueries.execute t cap A a.val b.val shape requests X Y).value
        ((ids (route requests hb).value a b).value.get i)).get
          (requests.get ((ids (route requests hb).value a b).value.get i)).coefficient) :=
  stored_matches _ _ _ _ _ _ _ _ _ _ _ (fun j hj => (ids_mem requests hb a b j).mp hj)

#print axioms route_cost
#print axioms routed_matches
#print axioms lookup_work
#print axioms lookup_bound
#print axioms lookup_matches
#print axioms query_value
#print axioms query_work
#print axioms stored_matches
#print axioms ids_mem
#print axioms routed_work
#print axioms total
end ThinMatrix.SelectedHighQueries
