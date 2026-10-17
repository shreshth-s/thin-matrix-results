import ParameterExecution
import EndToEndAPSP

/-!
# Prime labels from retained parameter metadata

The parameter program already produces its prime list in ascending order.
Only proofs below mention `Finset.sort`. Executable label constructors consume
the already retained decoded list and copy it directly to an array; they
neither execute the parameter program again nor perform a sorting pass.
-/
namespace ThinMatrix.ParameterMetadata
open ParameterExecution ComputableParameters
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem pool_ascending (P : Word) :
    ((ParameterExecution.pool P).value.map Word.view).Pairwise (· ≤ ·) := by
  simp only [ParameterExecution.pool,decode_value,poolLoop_view,mul_view,input_view,poolSpec_filter]
  exact List.Pairwise.filter _ (List.pairwise_le_range' 1)

theorem preparedWith_pool_ascending (p q R n U : ℕ) :
    ((prepareWith p q R n U).value.pool.map Word.view).Pairwise (· ≤ ·) := by
  unfold prepareWith
  exact pool_ascending _

theorem prepared_pool_ascending (n U : ℕ) :
    ((prepare n U).value.pool.map Word.view).Pairwise (· ≤ ·) := by
  unfold prepare
  exact preparedWith_pool_ascending _ _ _ n U

theorem metadata_pool_projection (n U : ℕ) :
    (execute n U).metadata.pool=(prepare n U).value.pool.map Word.view := by
  rw [execute_metadata]
  exact (decodeData_correct (prepare n U).value).2.2.2.2.2

theorem metadata_pool_ascending (n U : ℕ) :
    (execute n U).metadata.pool.Pairwise (· ≤ ·) := by
  rw [metadata_pool_projection]
  exact prepared_pool_ascending n U

theorem metadata_pool_nodup (n U : ℕ) : (execute n U).metadata.pool.Nodup := by
  rw [metadata_pool_projection]
  exact (prepare_correct n U).2.2.2.2.2.2

theorem metadata_pool_finset (n U : ℕ) :
    (execute n U).metadata.pool.toFinset=computedPool n := by
  rw [metadata_pool_projection]
  exact (prepare_correct n U).2.2.2.2.2.1

/-- Sorting occurs only in the specification of the retained order. -/
theorem metadata_pool_eq_sort (n U : ℕ) :
    (execute n U).metadata.pool=(computedPool n).sort (· ≤ ·) := by
  have he := (List.toFinset_sort (· ≤ ·) (metadata_pool_nodup n U)).mpr
    (metadata_pool_ascending n U)
  rw [metadata_pool_finset] at he
  exact he.symm

theorem metadata_pool_length (n U : ℕ) :
    (execute n U).metadata.pool.length=(computedPool n).card := by
  rw [metadata_pool_eq_sort]
  exact Finset.length_sort (· ≤ ·)

/-- The only executable label construction: array materialization of the
retained list. The cardinality proof and the finite set are erased. -/
def labelsFromMetadata (metadata : Decoded) (pool : Finset ℕ)
    (h : metadata.pool.length=pool.card) : Vector ℕ pool.card :=
  ⟨metadata.pool.toArray,by simpa only [List.size_toArray] using h⟩

theorem labelsFromMetadata_eq (metadata : Decoded) (pool : Finset ℕ)
    (h : metadata.pool.length=pool.card) (hsorted : metadata.pool=pool.sort (· ≤ ·)) :
    labelsFromMetadata metadata pool h=EndToEndAPSP.primeVector pool := by
  unfold labelsFromMetadata EndToEndAPSP.primeVector
  congr 1
  rw [hsorted]

theorem success_pool (n U : ℕ) (parameters : CompleteAPSP.Parameters (block n) U)
    (h : (execute n U).value=some parameters) : parameters.pool=computedPool n := by
  have hp : program n U=some parameters := (execute_value n U).symm.trans h
  exact (program_sound n U parameters hp).1

theorem success_pool_length (n U : ℕ) (parameters : CompleteAPSP.Parameters (block n) U)
    (h : (execute n U).value=some parameters) :
    (execute n U).metadata.pool.length=parameters.pool.card := by
  rw [success_pool n U parameters h]
  exact metadata_pool_length n U

theorem success_pool_order (n U : ℕ) (parameters : CompleteAPSP.Parameters (block n) U)
    (h : (execute n U).value=some parameters) :
    (execute n U).metadata.pool=parameters.pool.sort (· ≤ ·) := by
  rw [success_pool n U parameters h]
  exact metadata_pool_eq_sort n U

/-- `setup` is the result already bound by the caller. Its equality proof is
erased, so this definition does not call `execute` at runtime. -/
def successfulLabels {n U : ℕ} (setup : ParameterExecution.Execution n U)
    (hsetup : setup=execute n U) (parameters : CompleteAPSP.Parameters (block n) U)
    (h : setup.value=some parameters) : Vector ℕ parameters.pool.card :=
  labelsFromMetadata setup.metadata parameters.pool (by
    rw [hsetup] at h ⊢
    exact success_pool_length n U parameters h)

theorem successfulLabels_eq {n U : ℕ} (setup : ParameterExecution.Execution n U)
    (hsetup : setup=execute n U) (parameters : CompleteAPSP.Parameters (block n) U)
    (h : setup.value=some parameters) :
    successfulLabels setup hsetup parameters h=EndToEndAPSP.primeVector parameters.pool := by
  apply labelsFromMetadata_eq
  rw [hsetup] at h ⊢
  exact success_pool_order n U parameters h

theorem successfulLabels_get_mem {n U : ℕ} (setup : ParameterExecution.Execution n U)
    (hsetup : setup=execute n U) (parameters : CompleteAPSP.Parameters (block n) U)
    (h : setup.value=some parameters) (i : Fin parameters.pool.card) :
    (successfulLabels setup hsetup parameters h).get i ∈ parameters.pool := by
  rw [successfulLabels_eq]
  exact EndToEndAPSP.primeVector_mem _ i

theorem successfulLabels_injective {n U : ℕ} (setup : ParameterExecution.Execution n U)
    (hsetup : setup=execute n U) (parameters : CompleteAPSP.Parameters (block n) U)
    (h : setup.value=some parameters) :
    Function.Injective (successfulLabels setup hsetup parameters h).get := by
  rw [successfulLabels_eq]
  exact EndToEndAPSP.primeVector_injective _

theorem decodeList_length_price (xs : List Word) :
    xs.length ≤ (decodeList xs).bitSteps := by
  induction xs with
  | nil => simp [decodeList]
  | cons x xs ih =>
    simp only [decodeList,List.length_cons]
    omega

theorem decodeData_pool_length_price (d : Data) :
    d.pool.length ≤ (decodeData d).bitSteps := by
  have hp := decodeList_length_price d.pool
  simp only [decodeData]
  omega

/-- One array copy per retained label fits inside the already charged setup
allowance. A caller may therefore add these copies explicitly at a fixed
factor in its one-time setup bound. -/
theorem metadata_pool_length_price (n U : ℕ) :
    (execute n U).metadata.pool.length ≤ (execute n U).bitSteps := by
  have hp := decodeData_pool_length_price (prepare n U).value
  rw [metadata_pool_projection,List.length_map,execute_steps,prepareEncoded_value]
  omega


#print axioms metadata_pool_length_price
#print axioms pool_ascending
#print axioms metadata_pool_eq_sort
#print axioms metadata_pool_length
#print axioms labelsFromMetadata_eq
#print axioms success_pool
#print axioms successfulLabels_eq
#print axioms successfulLabels_get_mem
#print axioms successfulLabels_injective

end ThinMatrix.ParameterMetadata
