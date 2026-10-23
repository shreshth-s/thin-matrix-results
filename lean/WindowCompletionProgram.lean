import WindowCompletionRequests

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace ThinMatrix.WindowCompletionProgram
open BinaryGroupedCoordinates

structure Prepared (k ell C : ℕ) where
  source : WindowPrefixProgram.Prepared k ell C
  requests : GroupedPreparation.Counted (Array (Vector (Fin 4) (WindowPrefixProgram.prefixLength k ell+WindowPrefixProgram.length k ell)))
  completed : Run (PrefixCompletionProgram.Prepared (WindowPrefixProgram.prefixLength k ell) (WindowPrefixProgram.length k ell) source.rareCap C)

def execute {k ell C : ℕ} (source : WindowPrefixProgram.Prepared k ell C)
    (layout : RetainedWindowPermutation.Layout (2*k)) (labels : Array (Vector (Fin 4) (2*k))) : Prepared k ell C :=
  let requests := WindowCompletionRequests.requests ell layout labels
  let completed := PrefixCompletionProgram.execute source.encoded requests.value
  ⟨source,requests,completed⟩

@[simp] theorem execute_size {k ell C : ℕ} (source : WindowPrefixProgram.Prepared k ell C)
    (layout : RetainedWindowPermutation.Layout (2*k)) (labels : Array (Vector (Fin 4) (2*k))) :
    (execute source layout labels).completed.value.requests.size=labels.size := by
  simp [execute]

theorem execute_value {k ell C : ℕ} (source : WindowPrefixProgram.Prepared k ell C)
    (layout : RetainedWindowPermutation.Layout (2*k)) (labels : Array (Vector (Fin 4) (2*k)))
    (i : ℕ) (hi : i<labels.size) (c : Fin C) :
    BinaryCell.view (((execute source layout labels).completed.value.requests[i]'(by simpa using hi)).output.get c)=
      let request := (WindowCompletionRequests.transport ell layout (WindowCompletionRequests.orient labels[i]).value).value
      let key := PrefixRequestKey.make source.encoded.grouped.pairs request
      CappedPrefixProgram.query source.encoded key.value.pair key.value.prefixDigits.get (CappedBitPreparation.support key.value.active) c := by
  have h := PrefixCompletionProgram.execute_value source.encoded (WindowCompletionRequests.requests ell layout labels).value
      i (by simpa using hi) c
  rw [WindowCompletionRequests.requests_get] at h
  exact h

theorem execute_bits {k ell C : ℕ} (source : WindowPrefixProgram.Prepared k ell C)
    (layout : RetainedWindowPermutation.Layout (2*k)) (labels : Array (Vector (Fin 4) (2*k)))
    (A : ℕ) (ha : ∀ p, PrefixCompletionMatrices.LeafBound (source.encoded.traces.get p) A) :
    (execute source layout labels).completed.bitSteps≤PrefixCompletionProgram.bitBudget
      (WindowPrefixProgram.prefixLength k ell) (WindowPrefixProgram.length k ell) source.rareCap C A labels.size := by
  simpa only [execute,WindowCompletionRequests.requests_size] using
    PrefixCompletionProgram.execute_bits source.encoded A ha (WindowCompletionRequests.requests ell layout labels).value

theorem execute_control {k ell C : ℕ} (source : WindowPrefixProgram.Prepared k ell C)
    (layout : RetainedWindowPermutation.Layout (2*k)) (labels : Array (Vector (Fin 4) (2*k))) :
    (execute source layout labels).requests.work+(execute source layout labels).completed.control≤
      labels.size*(48*k+56)+8+PrefixCompletionProgram.controlBudget
        (WindowPrefixProgram.prefixLength k ell) (WindowPrefixProgram.length k ell) source.rareCap C labels.size := by
  have h := PrefixCompletionProgram.execute_control source.encoded (WindowCompletionRequests.requests ell layout labels).value
  rw [WindowCompletionRequests.requests_size] at h
  exact Nat.add_le_add (WindowCompletionRequests.requests_work ell layout labels) h

#print axioms execute_size
#print axioms execute_value
#print axioms execute_bits
#print axioms execute_control
end ThinMatrix.WindowCompletionProgram
