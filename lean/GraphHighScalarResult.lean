import GraphHighScalarCollection

set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxRecDepth 10000
namespace ThinMatrix.GraphHighScalarResult
open BinaryCell BinaryGroupedCoordinates ExactHalfSourcePlan SourceFormation
open GraphHighScalarCollection (H)
open scoped BigOperators
variable {L m q M K : ℕ}

structure Prepared (L m q M K : ℕ) where
  tree : BooleanRequestRouter.Tree (Fin M) (K*K).size
  families : Vector (GraphHighScalarSchedule.Family m M) (K*K)

variable (t : ℕ) (shape : ThinMatrixBackend.ShapePlan L m)
  (requests : Vector (GraphCompletionRequests.Physical L m q) M)
  (hb : ∀ i,(requests.get i).bandL<K ∧ (requests.get i).bandR<K)
  (tables : GraphHighPreparation.Tables L m q K)

def prepare : Program (Prepared L m q M K) :=
  let routed := SelectedHighQueries.route requests hb
  let out := vectorBuild (K*K) (GraphHighScalarSchedule.pair t shape requests routed.value tables)
  ⟨⟨routed.value,out.value⟩,routed.bitSteps+routed.control+out.operations+8⟩

theorem prepared_ids (g : Fin (K*K)) (s : Fin (H m)) :
    (GraphHighScalarCollection.entry ((prepare t shape requests hb tables).value.families.get g) s).indices=
      GraphHighScalarCollection.ids (prepare t shape requests hb tables).value.tree g := by
  simp only [prepare,vectorBuild_get,GraphHighScalarSchedule.pair,GraphHighScalarSchedule.family,
    GraphHighScalarCollection.entry,SelectedHighQueries.query]

def execute : Program (Vector (Vector Cell 1) M) :=
  let prep := prepare t shape requests hb tables
  let out := GraphHighScalarCollection.execute prep.value.tree prep.value.families
    (prepared_ids t shape requests hb tables)
  ⟨out.value,prep.operations+out.bitSteps+out.control+8⟩

def ownTable (i : Fin M) (u v : Fin (J m)) (run : Fin (2*m+1)) : BinaryHighTable.Table q :=
  (((((tables.get ⟨(requests.get i).bandL,(hb i).1⟩).get
    ⟨(requests.get i).bandR,(hb i).2⟩).get u).get v).get run)

def scalar (i : Fin M) (u v : Fin (J m)) (run : Fin (2*m+1)) : ℤ :=
  view ((SelectedHighQueries.lookup t shape (requests.get i) (ownTable requests hb tables i u v run)).value)

private theorem query_get_eq (x : SelectedHighQueries.Prepared M) (indices : List (Fin M))
    (table : BinaryHighTable.Table q)
    (he : x=(SelectedHighQueries.query t shape requests indices table).value)
    (j : Fin x.indices.length) :
    view (x.values.get j)=view ((SelectedHighQueries.lookup t shape
      (requests.get (indices[j.val]'(by simpa only [he,SelectedHighQueries.query] using j.isLt))) table).value) := by
  subst x
  exact SelectedHighQueries.query_value _ _ _ _ _ j

theorem gather_value (g : Fin (K*K)) (s : Fin (H m))
    (j : Fin (GraphHighScalarCollection.ids (prepare t shape requests hb tables).value.tree g).length) :
    view (((GraphHighScalarCollection.gather (prepare t shape requests hb tables).value.tree
      (prepare t shape requests hb tables).value.families (prepared_ids t shape requests hb tables) g).get s).get j)=
      let uv := finProdFinEquiv.symm s
      let vr := finProdFinEquiv.symm uv.2
      scalar t shape requests hb tables ((GraphHighScalarCollection.ids (prepare t shape requests hb tables).value.tree g)[j.val]) uv.1 vr.1 vr.2 := by
  let row := (GraphHighScalarCollection.ids (prepare t shape requests hb tables).value.tree g)[j.val]
  have hm : row∈(SelectedHighQueries.ids (SelectedHighQueries.route requests hb).value
      (finProdFinEquiv.symm g).1 (finProdFinEquiv.symm g).2).value := by
    rw [SelectedHighQueries.ids,Equiv.apply_symm_apply]
    exact List.getElem_mem _
  have hp := (SelectedHighQueries.ids_mem requests hb _ _ row).mp hm
  have hbands : (requests.get row).bandL=(finProdFinEquiv.symm g).1.val ∧
      (requests.get row).bandR=(finProdFinEquiv.symm g).2.val := by
    simpa only [CroppedHighQueries.accepts,decide_eq_true_eq] using hp
  have hl : (⟨(requests.get row).bandL,(hb row).1⟩ : Fin K)=(finProdFinEquiv.symm g).1 := Fin.ext hbands.1
  have hr : (⟨(requests.get row).bandR,(hb row).2⟩ : Fin K)=(finProdFinEquiv.symm g).2 := Fin.ext hbands.2
  let uv := finProdFinEquiv.symm s
  let vr := finProdFinEquiv.symm uv.2
  let ent := GraphHighScalarCollection.entry ((prepare t shape requests hb tables).value.families.get g) s
  have he : ent=(SelectedHighQueries.query t shape requests
      (GraphHighScalarCollection.ids (prepare t shape requests hb tables).value.tree g)
      (((((tables.get (finProdFinEquiv.symm g).1).get (finProdFinEquiv.symm g).2).get uv.1).get vr.1).get vr.2)).value := by
    simp only [ent,prepare,GraphHighScalarCollection.entry,vectorBuild_get,GraphHighScalarSchedule.pair,GraphHighScalarSchedule.family]
    rfl
  have hj : j.val<ent.indices.length := by rw [he];exact j.isLt
  have hh := query_get_eq t shape requests ent _ _ he ⟨j.val,hj⟩
  simp only [GraphHighScalarCollection.gather,Vector.get_ofFn]
  change view (ent.values.get ⟨j.val,hj⟩)=_
  rw [hh]
  change _=view ((SelectedHighQueries.lookup t shape (requests.get row)
    (((((tables.get ⟨(requests.get row).bandL,(hb row).1⟩).get
      ⟨(requests.get row).bandR,(hb row).2⟩).get uv.1).get vr.1).get vr.2)).value)
  rw [hl,hr]


theorem value (i : Fin M) (c : Fin 1) :
    view (((execute t shape requests hb tables).value.get i).get c)=
      ∑ u, ∑ v, ∑ run,scalar t shape requests hb tables i u v run := by
  apply GraphHighScalarCollection.correct requests hb (prepare t shape requests hb tables).value.tree
    (prepare t shape requests hb tables).value.families (prepared_ids t shape requests hb tables) rfl
  intro g j
  have hh := Finset.sum_congr (s₁:=Finset.univ) (s₂:=Finset.univ) rfl
    (fun s _ => gather_value t shape requests hb tables g s j)
  apply hh.trans
  rw [←Equiv.sum_comp finProdFinEquiv]
  simp only [Fintype.sum_prod_type,Equiv.symm_apply_apply]
  simp_rw [←Equiv.sum_comp finProdFinEquiv]
  simp only [Fintype.sum_prod_type,Equiv.symm_apply_apply]

def budget (K L m t M A : ℕ) : ℕ :=
  GraphHighScalarSchedule.budget K L m t M A+
    M*(H m*BackendScalarBits.backendScalarUnit (H m*CroppedHighQueries.queryMagnitude m t A).size)+
    M*(112*H m+143)+(K*K)*(48*H m+72+(H m+4)*GraphHighScalarSchedule.readBudget K)+60

theorem work (A : ℕ) (ht : t≤2*m)
    (hA : ∀ a b u v run,BinaryHighTable.Bounds.TableBound A (((((tables.get a).get b).get u).get v).get run)) :
    (execute t shape requests hb tables).operations≤budget K L m t M A := by
  have hp : (prepare t shape requests hb tables).operations≤GraphHighScalarSchedule.budget K L m t M A :=
    GraphHighScalarSchedule.execute_work t A ht shape requests hb tables hA
  have hg (g : Fin (K*K)) (s : Fin (H m))
      (j : Fin (GraphHighScalarCollection.ids (prepare t shape requests hb tables).value.tree g).length) :
      (view (((GraphHighScalarCollection.gather (prepare t shape requests hb tables).value.tree
        (prepare t shape requests hb tables).value.families (prepared_ids t shape requests hb tables) g).get s).get j)).natAbs≤
          CroppedHighQueries.queryMagnitude m t A := by
    rw [gather_value]
    dsimp only [scalar,ownTable]
    exact SelectedHighQueries.lookup_bound _ _ _ _ _ (hA _ _ _ _ _)
  have hbits := GraphHighScalarCollection.bits requests hb (prepare t shape requests hb tables).value.tree
    (prepare t shape requests hb tables).value.families (prepared_ids t shape requests hb tables) rfl
    (CroppedHighQueries.queryMagnitude m t A) hg
  have hc := GraphHighScalarCollection.control requests hb (prepare t shape requests hb tables).value.tree
    (prepare t shape requests hb tables).value.families (prepared_ids t shape requests hb tables) rfl
  dsimp only [execute]
  unfold budget
  omega

#print axioms work

#print axioms prepared_ids
#print axioms gather_value
#print axioms value
end ThinMatrix.GraphHighScalarResult
