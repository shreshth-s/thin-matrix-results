import GraphHighScalarSchedule
import SelectedScalarRows

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 10000

namespace ThinMatrix.GraphHighScalarCollection
open BinaryCell BinaryGroupedCoordinates ExactHalfSourcePlan
open scoped BigOperators
variable {L m q M K : ℕ}

abbrev H (m : ℕ) := J m*(J m*(2*m+1))

def entry (family : GraphHighScalarSchedule.Family m M) (s : Fin (H m)) : SelectedHighQueries.Prepared M :=
  let uv := finProdFinEquiv.symm s
  let vr := finProdFinEquiv.symm uv.2
  ((family.get uv.1).get vr.1).get vr.2

variable (requests : Vector (GraphCompletionRequests.Physical L m q) M)
  (hb : ∀ i,(requests.get i).bandL<K ∧ (requests.get i).bandR<K)

variable (tree : BooleanRequestRouter.Tree (Fin M) (K*K).size)

abbrev ids (g : Fin (K*K)) :=
  (GraphHighScalarSchedule.pairIndices tree g).value

variable (families : Vector (GraphHighScalarSchedule.Family m M) (K*K))
  (hids : ∀ g s,(entry (families.get g) s).indices=ids tree g)

def gather (g : Fin (K*K)) : Vector (Vector Cell (ids tree g).length) (H m) :=
  Vector.ofFn (fun s => Vector.ofFn (fun j => (entry (families.get g) s).values.get
    ⟨j.val,by rw [hids g s]; exact j.isLt⟩))

def child (g : Fin (K*K)) : Run (OriginalRowCollection.Rows M 1) :=
  let rows := SelectedScalarRows.execute (ids tree g) (gather tree families hids g)
  ⟨rows.value,rows.bitSteps,rows.control+32*H m*((ids tree g).length+1)+(H m+4)*GraphHighScalarSchedule.readBudget K+8⟩

def execute := OriginalRowCollection.execute (child tree families hids)

theorem total (htree : tree=(SelectedHighQueries.route requests hb).value) : (∑ g : Fin (K*K),(child tree families hids g).value.indices.length)=M :=
  by subst tree; exact GraphHighScalarSchedule.total_selected requests hb

theorem coverage (htree : tree=(SelectedHighQueries.route requests hb).value) (i : Fin M) : ∃ g : Fin (K*K),i∈(child tree families hids g).value.indices := by
  subst tree
  let keys := Vector.ofFn (fun i => SelectedHighQueries.bandKey (requests.get i) (hb i).1 (hb i).2)
  simpa only [child,SelectedScalarRows.execute,ids,GraphHighScalarSchedule.pairIndices,SelectedHighQueries.route,FiniteRequestRouter.ids_value] using OriginalRowCollection.selected_cover keys i

theorem correct (htree : tree=(SelectedHighQueries.route requests hb).value) (expected : Fin M → ℤ)
    (hrow : ∀ g j, (∑ s,view (((gather tree families hids g).get s).get j))=
      expected ((ids tree g)[j.val])) (i : Fin M) (c : Fin 1) :
    view ((((execute tree families hids).value.get i).get c))=expected i := by
  apply OriginalRowCollection.correct _ (fun i _ => expected i)
  · intro g j c
    exact (SelectedScalarRows.value _ _ j c).trans (hrow g j)
  · exact coverage requests hb tree families hids htree

theorem bits (htree : tree=(SelectedHighQueries.route requests hb).value) (A : ℕ)
    (hA : ∀ g s j,(view (((gather tree families hids g).get s).get j)).natAbs≤A) :
    (execute tree families hids).bitSteps≤M*(H m*BackendScalarBits.backendScalarUnit (H m*A).size) := by
  rw [execute,OriginalRowCollection.bits]
  have hh := Finset.sum_le_sum (fun g (_ : g∈Finset.univ) =>
    SelectedScalarRows.bits (ids tree g) (gather tree families hids g) A (hA g))
  simp only [←Finset.sum_mul,ids,htree,GraphHighScalarSchedule.total_selected] at hh
  exact hh

theorem control (htree : tree=(SelectedHighQueries.route requests hb).value) : (execute tree families hids).control≤
      M*(112*H m+143)+(K*K)*(48*H m+72+(H m+4)*GraphHighScalarSchedule.readBudget K)+52 := by
  have hh := Finset.sum_le_sum (fun g (_ : g∈Finset.univ) =>
    SelectedScalarRows.control (ids tree g) (gather tree families hids g))
  have hs : (∑ g : Fin (K*K),(ids tree g).length)=M :=
    by subst tree; exact GraphHighScalarSchedule.total_selected requests hb
  rw [execute,OriginalRowCollection.control _ (total requests hb tree families hids htree)]
  dsimp only [child]
  simp only [Finset.sum_add_distrib,mul_add,←Finset.mul_sum,←Finset.sum_mul] at hh ⊢
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,hs] at hh ⊢
  nlinarith only [hh]

#print axioms total
#print axioms coverage
#print axioms correct
#print axioms bits
#print axioms control
end ThinMatrix.GraphHighScalarCollection
