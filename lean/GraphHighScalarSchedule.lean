import GraphHighPreparation

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000

namespace ThinMatrix.GraphHighScalarSchedule
open ExactHalfSourcePlan SourceFormation BinaryGroupedCoordinates
open scoped BigOperators
variable {L m q M K : ℕ}

abbrev Family (m M : ℕ) := Vector (Vector (Vector (SelectedHighQueries.Prepared M) (2*m+1)) (J m)) (J m)

def family (t : ℕ) (shape : ThinMatrixBackend.ShapePlan L m)
    (requests : Vector (GraphCompletionRequests.Physical L m q) M) (indices : List (Fin M))
    (tables : Vector (Vector (Vector (BinaryHighTable.Table q) (2*m+1)) (J m)) (J m)) : Program (Family m M) :=
  vectorBuild (J m) fun u => vectorBuild (J m) fun v => vectorBuild (2*m+1) fun run =>
    let out := SelectedHighQueries.query t shape requests indices (((tables.get u).get v).get run)
    ⟨out.value,out.operations⟩

theorem family_work (t A : ℕ) (ht : t≤2*m) (shape : ThinMatrixBackend.ShapePlan L m)
    (requests : Vector (GraphCompletionRequests.Physical L m q) M) (indices : List (Fin M))
    (tables : Vector (Vector (Vector (BinaryHighTable.Table q) (2*m+1)) (J m)) (J m))
    (hA : ∀ u v run,BinaryHighTable.Bounds.TableBound A (((tables.get u).get v).get run)) :
    (family t shape requests indices tables).operations≤
      (J m)^2*(2*m+1)*(indices.length*(SelectedHighQueries.rowBudget L m t A+32)+40) := by
  have hr (u v : Fin (J m)) := vectorBuild_cost (2*m+1)
    (indices.length*(SelectedHighQueries.rowBudget L m t A+32)+8)
    (fun run => let out := SelectedHighQueries.query t shape requests indices (((tables.get u).get v).get run)
      (⟨out.value,out.operations⟩ : Program (SelectedHighQueries.Prepared M)))
    (fun run => SelectedHighQueries.query_work t A ht shape requests indices _ (hA u v run))
  have hv (u : Fin (J m)) := vectorBuild_cost (J m) _ _ (hr u)
  have hu := vectorBuild_cost (J m) _ _ hv
  have hJ := ExactHalfCroppedEmbedding.shifts_nonempty m
  have hj : J m≤(J m)^2*(2*m+1) := by nlinarith
  have hj2 : (J m)^2≤(J m)^2*(2*m+1) := by nlinarith
  change (family t shape requests indices tables).operations≤_ at hu
  nlinarith only[hu,hj,hj2]

def pairIndices (tree : BooleanRequestRouter.Tree (Fin M) (K*K).size) (g : Fin (K*K)) :=
  FiniteRequestRouter.ids tree g

def pair (t : ℕ) (shape : ThinMatrixBackend.ShapePlan L m)
    (requests : Vector (GraphCompletionRequests.Physical L m q) M)
    (tree : BooleanRequestRouter.Tree (Fin M) (K*K).size)
    (tables : GraphHighPreparation.Tables L m q K) (g : Fin (K*K)) : Program (Family m M) :=
  let ids := pairIndices tree g
  let ab := finProdFinEquiv.symm g
  let out := family t shape requests ids.value ((tables.get ab.1).get ab.2)
  ⟨out.value,ids.bitSteps+ids.control+out.operations+8⟩

def routeBudget (K L m M : ℕ) : ℕ :=
  24*(K*K+1)+M*(16*((K*K).size+1)^2+64*((K*K).size+1)^3+128*((K*K).size+L+m+1)^3+36)+36

def readBudget (K : ℕ) : ℕ := 16*((K*K).size+1)^2+64*((K*K).size+1)^3

def execute (t : ℕ) (shape : ThinMatrixBackend.ShapePlan L m)
    (requests : Vector (GraphCompletionRequests.Physical L m q) M)
    (hb : ∀ i,(requests.get i).bandL<K ∧ (requests.get i).bandR<K)
    (tables : GraphHighPreparation.Tables L m q K) : Program (Vector (Family m M) (K*K)) :=
  let routed := SelectedHighQueries.route requests hb
  let out := vectorBuild (K*K) (pair t shape requests routed.value tables)
  ⟨out.value,routed.bitSteps+routed.control+out.operations+8⟩

theorem total_selected (requests : Vector (GraphCompletionRequests.Physical L m q) M)
    (hb : ∀ i,(requests.get i).bandL<K ∧ (requests.get i).bandR<K) :
    (∑ g : Fin (K*K),(pairIndices (SelectedHighQueries.route requests hb).value g).value.length)=M := by
  simp only [pairIndices,SelectedHighQueries.route,FiniteRequestRouter.ids_value]
  exact FiniteRequestRouter.group_total _

def budget (K L m t M A : ℕ) : ℕ := routeBudget K L m M+
  K*K*(readBudget K+40*(J m)^2*(2*m+1)+16)+
    M*(J m)^2*(2*m+1)*(SelectedHighQueries.rowBudget L m t A+32)+8

theorem execute_work (t A : ℕ) (ht : t≤2*m) (shape : ThinMatrixBackend.ShapePlan L m)
    (requests : Vector (GraphCompletionRequests.Physical L m q) M)
    (hb : ∀ i,(requests.get i).bandL<K ∧ (requests.get i).bandR<K)
    (tables : GraphHighPreparation.Tables L m q K)
    (hA : ∀ a b u v run,BinaryHighTable.Bounds.TableBound A (((((tables.get a).get b).get u).get v).get run)) :
    (execute t shape requests hb tables).operations≤budget K L m t M A := by
  let routed := SelectedHighQueries.route requests hb
  let mul := (J m)^2*(2*m+1)
  let U := SelectedHighQueries.rowBudget L m t A+32
  have hp (g : Fin (K*K)) : (pair t shape requests routed.value tables g).operations≤
      readBudget K+mul*((pairIndices routed.value g).value.length*U+40)+8 := by
    have hi := FiniteRequestRouter.ids_cost routed.value g
    have hf := family_work t A ht shape requests (pairIndices routed.value g).value _
      (hA (finProdFinEquiv.symm g).1 (finProdFinEquiv.symm g).2)
    dsimp only [pair]
    change (pairIndices routed.value g).bitSteps=0 ∧ (pairIndices routed.value g).control≤readBudget K at hi
    dsimp only[mul,U]
    omega
  have hs := Finset.sum_le_sum (fun g (_ : g∈Finset.univ) => hp g)
  have ht := total_selected requests hb
  have hroute := SelectedHighQueries.route_cost requests hb
  have he : (∑ g : Fin (K*K),(readBudget K+mul*((pairIndices routed.value g).value.length*U+40)+8))=
      K*K*(readBudget K+40*mul+8)+M*mul*U := by
    simp_rw [mul_add,Finset.sum_add_distrib,←Finset.mul_sum,←Finset.sum_mul]
    simp only[Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul]
    dsimp only[routed]
    rw [ht]
    ring
  rw [he] at hs
  dsimp only [execute,vectorBuild]
  simp only[Vector.get_ofFn]
  dsimp only[routed] at hs
  unfold budget routeBudget
  dsimp only[mul,U] at hs
  rw [hroute.1]
  nlinarith only[hs,hroute.2]

 theorem selected_row (t : ℕ) (shape : ThinMatrixBackend.ShapePlan L m)
    (requests : Vector (GraphCompletionRequests.Physical L m q) M)
    (hb : ∀ i,(requests.get i).bandL<K ∧ (requests.get i).bandR<K)
    (tables : GraphHighPreparation.Tables L m q K) (g : Fin (K*K))
    (u v : Fin (J m)) (run : Fin (2*m+1)) :
    ((((execute t shape requests hb tables).value.get g).get u).get v).get run=
      (SelectedHighQueries.query t shape requests (pairIndices (SelectedHighQueries.route requests hb).value g).value
        (((((tables.get (finProdFinEquiv.symm g).1).get (finProdFinEquiv.symm g).2).get u).get v).get run)).value := by
  simp only[execute,pair,family,vectorBuild_get]

#print axioms family_work
#print axioms total_selected
#print axioms execute_work
#print axioms selected_row
end ThinMatrix.GraphHighScalarSchedule
