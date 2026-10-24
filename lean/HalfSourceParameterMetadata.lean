import HalfSourceParameterExecution
import ParameterMetadata

/-! Reuse the retained ascending prime list produced by the exact-half
binary setup; label materialization performs no new trial division or sort. -/
namespace ThinMatrix.HalfSourceParameterMetadata
open ParameterExecution (Word decodeData_correct)
open HalfSourceBatchFit HalfSourcePrimeParameters HalfSourceParameterExecution
open ParameterMetadata (preparedWith_pool_ascending labelsFromMetadata labelsFromMetadata_eq decodeData_pool_length_price)
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
attribute [local irreducible] HalfSourceBatchFit.block

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
def successfulLabels {n U : ℕ} (setup : HalfSourceParameterExecution.Execution n U)
    (hsetup : setup=execute n U) (parameters : CompleteAPSP.Parameters (block n) U)
    (h : setup.value=some parameters) : Vector ℕ parameters.pool.card :=
  labelsFromMetadata setup.metadata parameters.pool (by
    rw [hsetup] at h ⊢
    exact success_pool_length n U parameters h)

theorem successfulLabels_eq {n U : ℕ} (setup : HalfSourceParameterExecution.Execution n U)
    (hsetup : setup=execute n U) (parameters : CompleteAPSP.Parameters (block n) U)
    (h : setup.value=some parameters) :
    successfulLabels setup hsetup parameters h=EndToEndAPSP.primeVector parameters.pool := by
  apply labelsFromMetadata_eq
  rw [hsetup] at h ⊢
  exact success_pool_order n U parameters h

theorem successfulLabels_get_mem {n U : ℕ} (setup : HalfSourceParameterExecution.Execution n U)
    (hsetup : setup=execute n U) (parameters : CompleteAPSP.Parameters (block n) U)
    (h : setup.value=some parameters) (i : Fin parameters.pool.card) :
    (successfulLabels setup hsetup parameters h).get i ∈ parameters.pool := by
  rw [successfulLabels_eq]
  exact EndToEndAPSP.primeVector_mem _ i

theorem successfulLabels_injective {n U : ℕ} (setup : HalfSourceParameterExecution.Execution n U)
    (hsetup : setup=execute n U) (parameters : CompleteAPSP.Parameters (block n) U)
    (h : setup.value=some parameters) :
    Function.Injective (successfulLabels setup hsetup parameters h).get := by
  rw [successfulLabels_eq]
  exact EndToEndAPSP.primeVector_injective _

/-- One array copy per retained label fits inside the already charged setup
allowance. A caller may therefore add these copies explicitly at a fixed
factor in its one-time setup bound. -/
theorem metadata_pool_length_price (n U : ℕ) :
    (execute n U).metadata.pool.length ≤ (execute n U).bitSteps := by
  have hp := decodeData_pool_length_price (prepare n U).value
  rw [metadata_pool_projection,List.length_map,execute_steps,prepareEncoded_value]
  omega

#print axioms metadata_pool_eq_sort
#print axioms metadata_pool_length
#print axioms success_pool
#print axioms successfulLabels_eq
#print axioms successfulLabels_get_mem
#print axioms successfulLabels_injective
#print axioms metadata_pool_length_price
end ThinMatrix.HalfSourceParameterMetadata
