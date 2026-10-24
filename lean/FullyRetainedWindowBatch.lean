import SharedFullyPrefixScatter
import RetainedWindowBatch
import SharedPrefixSourceBank
import WindowSharedCompletion

set_option autoImplicit false

/-! A window batch reuses the complete source bank, including the matrices
read by shared prefix completion. Only request transport, routing, shared
completion and occurrence scatter execute on repeated calls. -/
namespace ThinMatrix.FullyRetainedWindowBatch
open BinaryCell BinaryGroupedCoordinates
open RectangularBatch (Scheme)
variable {k ell total cn co C B A Z : ℕ}

def execute (scheme : Scheme) (hD : 0<WindowSharedCompletion.D k ell total cn co)
    (hA : 0<A) (hZ : 0<Z)
    (hfirst : (A-1)^scheme.den≤(WindowSharedCompletion.D k ell total cn co)^scheme.num)
    (hlast : Z≤(WindowSharedCompletion.D k ell total cn co)^scheme.z)
    (stored : SharedPrefixSourceBank.Prepared (WindowPrefixProgram.prefixLength k ell)
      (WindowPrefixProgram.length k ell) (WindowPrefixProgram.cap k ell total cn co) C B)
    (layout : RetainedWindowPermutation.Layout (2*k)) (labels : Array (Vector (Fin 4) (2*k))) :
    Run (Vector (Vector Cell (B*C)) labels.size) :=
  let requests := WindowCompletionRequests.requests ell layout labels
  let routed := SharedPrefixSourceBank.route stored requests.value
  let out := SharedFullyPrefixScatter.execute scheme hD hA hZ hfirst hlast requests.value routed.value
  ⟨Vector.cast (by simp [requests]) out.value,routed.bitSteps+out.bitSteps,
    requests.work+routed.control+out.control+16⟩

theorem value_eq (scheme : Scheme) (hD : 0<WindowSharedCompletion.D k ell total cn co)
    (hA : 0<A) (hZ : 0<Z)
    (hfirst : (A-1)^scheme.den≤(WindowSharedCompletion.D k ell total cn co)^scheme.num)
    (hlast : Z≤(WindowSharedCompletion.D k ell total cn co)^scheme.z)
    (stored : SharedPrefixSourceBank.Prepared (WindowPrefixProgram.prefixLength k ell)
      (WindowPrefixProgram.length k ell) (WindowPrefixProgram.cap k ell total cn co) C B)
    (layout : RetainedWindowPermutation.Layout (2*k)) (labels : Array (Vector (Fin 4) (2*k))) :
    (execute scheme hD hA hZ hfirst hlast stored layout labels).value=
      (RetainedWindowBatch.execute scheme hD hA hZ hfirst hlast stored layout labels).value := by
  simp only [execute,RetainedWindowBatch.execute,SharedFullyPrefixScatter.execute_value_eq,
    SharedPrefixScatter.execute_value_eq]

theorem bits (scheme : Scheme) (hD : 0<WindowSharedCompletion.D k ell total cn co)
    (hA : 0<A) (hZ : 0<Z)
    (hfirst : (A-1)^scheme.den≤(WindowSharedCompletion.D k ell total cn co)^scheme.num)
    (hlast : Z≤(WindowSharedCompletion.D k ell total cn co)^scheme.z)
    (stored : SharedPrefixSourceBank.Prepared (WindowPrefixProgram.prefixLength k ell)
      (WindowPrefixProgram.length k ell) (WindowPrefixProgram.cap k ell total cn co) C B)
    (layout : RetainedWindowPermutation.Layout (2*k)) (labels : Array (Vector (Fin 4) (2*k))) :
    (execute scheme hD hA hZ hfirst hlast stored layout labels).bitSteps=
      (SharedFullyPrefixSchedule.execute scheme hD hA hZ hfirst hlast
        (WindowCompletionRequests.requests ell layout labels).value
        (SharedPrefixSourceBank.route stored (WindowCompletionRequests.requests ell layout labels).value).value).bitSteps := by
  simp only [execute,SharedPrefixSourceBank.route_bits,zero_add,SharedFullyPrefixScatter.bits]

theorem correct (scheme : Scheme) (hv : scheme.Valid)
    (hD : 0<WindowSharedCompletion.D k ell total cn co) (hA : 0<A) (hZ : 0<Z)
    (hfirst : (A-1)^scheme.den≤(WindowSharedCompletion.D k ell total cn co)^scheme.num)
    (hlast : Z≤(WindowSharedCompletion.D k ell total cn co)^scheme.z)
    (xs : Vector (CappedPrefixProgram.Prepared (WindowPrefixProgram.prefixLength k ell)
      (WindowPrefixProgram.length k ell) (WindowPrefixProgram.cap k ell total cn co) C) B)
    (hk : ∀ b,(xs.get b).grouped.keys=GroupedPreparation.keyVector
      (WindowPrefixProgram.length k ell) (WindowPrefixProgram.cap k ell total cn co))
    (hp : ∀ b,(xs.get b).grouped.pairs=GroupedPreparation.pairKeys (WindowPrefixProgram.length k ell))
    (layout : RetainedWindowPermutation.Layout (2*k)) (labels : Array (Vector (Fin 4) (2*k)))
    (j : Fin labels.size) (b : Fin B) (c : Fin C) :
    view (((execute scheme hD hA hZ hfirst hlast (SharedPrefixSourceBank.prepare xs).value layout labels).value.get j).get
      (PrefixBlockBatch.column b c))=
      view ((PrefixCompletionProgram.row (xs.get b) (PrefixCompletionMatrices.prepare (xs.get b)).value
        ((WindowCompletionRequests.requests ell layout labels).value[j.val]'(by simp))).value.output.get c) := by
  rw [value_eq]
  exact RetainedWindowBatch.correct scheme hv hD hA hZ hfirst hlast xs hk hp layout labels j b c

#print axioms value_eq
#print axioms bits
#print axioms correct
end ThinMatrix.FullyRetainedWindowBatch
