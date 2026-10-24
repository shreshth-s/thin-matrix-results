import SharedPrefixScatter
import WindowCompletionProgram

set_option autoImplicit false
set_option maxHeartbeats 1400000

/-! Shared addressed completion for compatible production window sources.
Channel counts, chosen suffix length and retained permutation are common
across the actual block columns. Source encoders run once per block, request
transport once for the whole batch, and the matrix shape once per schedule.
This adapter charges its raw retained source inputs separately; no compact
source-generation bound is inferred from this correctness refinement. -/
namespace ThinMatrix.WindowSharedCompletion
open BinaryCell BinaryGroupedCoordinates BinaryGroupedPreparation
open RectangularBatch (Scheme)
variable {k ell total cn co C B A Z : ℕ}

abbrev D (k ell total cn co : ℕ) :=
  CappedSubsetList.count (WindowPrefixProgram.length k ell) (WindowPrefixProgram.cap k ell total cn co)

def encode (ell total cn co : ℕ) (sources : Vector (OppositeWindowLayer.Source (2*k) C) B) :
    Run (Vector (CappedPrefixProgram.Prepared (WindowPrefixProgram.prefixLength k ell)
      (WindowPrefixProgram.length k ell) (WindowPrefixProgram.cap k ell total cn co) C) B) :=
  tabulate sources (fun b => CappedPrefixProgram.execute (WindowPrefixProgram.cap k ell total cn co)
    (WindowPrefixProgram.reshape ell (sources.get b)))

@[simp] theorem encode_get (ell total cn co : ℕ) (sources : Vector (OppositeWindowLayer.Source (2*k) C) B) (b : Fin B) :
    (encode ell total cn co sources).value.get b=(WindowPrefixProgram.execute ell total cn co (sources.get b)).value.encoded := by
  simp only [encode,tabulate_get,WindowPrefixProgram.execute]

theorem encode_layout (ell total cn co : ℕ) (sources : Vector (OppositeWindowLayer.Source (2*k) C) B) (b : Fin B) :
    ((encode ell total cn co sources).value.get b).grouped.keys=
      GroupedPreparation.keyVector (WindowPrefixProgram.length k ell) (WindowPrefixProgram.cap k ell total cn co) ∧
    ((encode ell total cn co sources).value.get b).grouped.pairs=
      GroupedPreparation.pairKeys (WindowPrefixProgram.length k ell) := by
  simp only [encode,tabulate_get,CappedPrefixProgram.execute,RetainedCappedGroups.prepare,
    GroupedPreparation.storeKeys_value,GroupedPreparation.storePairs_value,and_self]

/-- Consume already retained compatible source encodings; no encoder is rerun. -/
def complete (scheme : Scheme) (hD : 0<D k ell total cn co) (hA : 0<A) (hZ : 0<Z)
    (hfirst : (A-1)^scheme.den≤(D k ell total cn co)^scheme.num)
    (hlast : Z≤(D k ell total cn co)^scheme.z)
    (xs : Vector (CappedPrefixProgram.Prepared (WindowPrefixProgram.prefixLength k ell)
      (WindowPrefixProgram.length k ell) (WindowPrefixProgram.cap k ell total cn co) C) B)
    (layout : RetainedWindowPermutation.Layout (2*k)) (labels : Array (Vector (Fin 4) (2*k))) :
    Run (Vector (Vector Cell (B*C)) labels.size) :=
  let requests := WindowCompletionRequests.requests ell layout labels
  let prepared := RoutedPrefixBatch.prepare xs requests.value
  let out := SharedPrefixScatter.execute scheme hD hA hZ hfirst hlast requests.value prepared.value
  ⟨Vector.cast (by simp [requests]) out.value,prepared.bitSteps+out.bitSteps,
    requests.work+prepared.control+out.control+16⟩

theorem complete_correct (scheme : Scheme) (hv : scheme.Valid)
    (hD : 0<D k ell total cn co) (hA : 0<A) (hZ : 0<Z)
    (hfirst : (A-1)^scheme.den≤(D k ell total cn co)^scheme.num)
    (hlast : Z≤(D k ell total cn co)^scheme.z)
    (xs : Vector (CappedPrefixProgram.Prepared (WindowPrefixProgram.prefixLength k ell)
      (WindowPrefixProgram.length k ell) (WindowPrefixProgram.cap k ell total cn co) C) B)
    (hk : ∀ b,(xs.get b).grouped.keys=GroupedPreparation.keyVector
      (WindowPrefixProgram.length k ell) (WindowPrefixProgram.cap k ell total cn co))
    (hp : ∀ b,(xs.get b).grouped.pairs=GroupedPreparation.pairKeys (WindowPrefixProgram.length k ell))
    (layout : RetainedWindowPermutation.Layout (2*k)) (labels : Array (Vector (Fin 4) (2*k)))
    (j : Fin labels.size) (b : Fin B) (c : Fin C) :
    view (((complete scheme hD hA hZ hfirst hlast xs layout labels).value.get j).get
      (PrefixBlockBatch.column b c))=
      view ((PrefixCompletionProgram.row (xs.get b) (PrefixCompletionMatrices.prepare (xs.get b)).value
        ((WindowCompletionRequests.requests ell layout labels).value[j.val]'(by simp))).value.output.get c) := by
  have hh := SharedPrefixScatter.correct scheme hv hD hA hZ hfirst hlast xs hk hp
    (WindowCompletionRequests.requests ell layout labels).value ⟨j.val,by simp⟩ b c
  simpa only [complete,Vector.get_eq_getElem,Vector.getElem_cast] using hh

def execute (scheme : Scheme) (hD : 0<D k ell total cn co) (hA : 0<A) (hZ : 0<Z)
    (hfirst : (A-1)^scheme.den≤(D k ell total cn co)^scheme.num)
    (hlast : Z≤(D k ell total cn co)^scheme.z)
    (sources : Vector (OppositeWindowLayer.Source (2*k) C) B)
    (layout : RetainedWindowPermutation.Layout (2*k)) (labels : Array (Vector (Fin 4) (2*k))) :
    Run (Vector (Vector Cell (B*C)) labels.size) :=
  let xs := encode ell total cn co sources
  let requests := WindowCompletionRequests.requests ell layout labels
  let prepared := RoutedPrefixBatch.prepare xs.value requests.value
  let out := SharedPrefixScatter.execute scheme hD hA hZ hfirst hlast requests.value prepared.value
  ⟨Vector.cast (by simp [requests]) out.value,xs.bitSteps+prepared.bitSteps+out.bitSteps,
    xs.control+requests.work+prepared.control+out.control+16⟩

theorem correct (scheme : Scheme) (hv : scheme.Valid)
    (hD : 0<D k ell total cn co) (hA : 0<A) (hZ : 0<Z)
    (hfirst : (A-1)^scheme.den≤(D k ell total cn co)^scheme.num)
    (hlast : Z≤(D k ell total cn co)^scheme.z)
    (sources : Vector (OppositeWindowLayer.Source (2*k) C) B)
    (layout : RetainedWindowPermutation.Layout (2*k)) (labels : Array (Vector (Fin 4) (2*k)))
    (j : Fin labels.size) (b : Fin B) (c : Fin C) :
    view (((execute scheme hD hA hZ hfirst hlast sources layout labels).value.get j).get
      (PrefixBlockBatch.column b c))=
      view (((WindowCompletionProgram.execute (WindowPrefixProgram.execute ell total cn co (sources.get b)).value
        layout labels).completed.value.requests[j.val]'(by simp)).output.get c) := by
  have hh := SharedPrefixScatter.correct scheme hv hD hA hZ hfirst hlast
    (encode ell total cn co sources).value
    (fun b => (encode_layout ell total cn co sources b).1)
    (fun b => (encode_layout ell total cn co sources b).2)
    (WindowCompletionRequests.requests ell layout labels).value
    ⟨j.val,by simp⟩ b c
  have hr := PrefixCompletionProgram.execute_get
    (WindowPrefixProgram.execute ell total cn co (sources.get b)).value.encoded
    (WindowCompletionRequests.requests ell layout labels).value j.val (by simp)
  have hr' := congrArg (fun row => view (row.output.get c)) hr
  apply Eq.trans _ hr'.symm
  simp only [encode_get] at hh
  simp only [execute,Vector.get_eq_getElem,Vector.getElem_cast]
  simp only [Vector.get_eq_getElem] at hh
  convert hh using 1
  rfl

theorem encode_bits (ell total cn co : ℕ) (sources : Vector (OppositeWindowLayer.Source (2*k) C) B)
    (H : ℕ) (hs : ∀ b,OppositeWindowLayer.Bound (sources.get b) H) :
    (encode ell total cn co sources).bitSteps≤B*WindowPrefixProgram.bitBudget k ell total cn co C H := by
  apply tabulate_bits
  intro b
  exact CappedPrefixProgram.execute_bits _ _ H
    (WindowPrefixProgram.castSource_bound _ _ H (hs b))

theorem encode_control (ell total cn co : ℕ) (sources : Vector (OppositeWindowLayer.Source (2*k) C) B) :
    (encode ell total cn co sources).control≤
      B*(CappedPrefixProgram.controlBudget (WindowPrefixProgram.prefixLength k ell)
        (WindowPrefixProgram.length k ell) (WindowPrefixProgram.cap k ell total cn co) C+32)+8 := by
  apply tabulate_control
  intro b
  exact CappedPrefixProgram.execute_control _ _

#print axioms encode_get
#print axioms encode_layout
#print axioms complete_correct
#print axioms correct
#print axioms encode_bits
#print axioms encode_control
end ThinMatrix.WindowSharedCompletion
