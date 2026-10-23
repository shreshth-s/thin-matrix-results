import WindowCompletionProgram

set_option autoImplicit false
set_option maxHeartbeats 400000

/-! Every completed request keeps every coefficient. This adapter executes one
window once, retains its matrix bank/requests/selectors, and copies the binary
outputs into a common rectangular row store. The copy and accumulation widths
are derived from the leaf magnitudes, not supplied output values. -/
namespace ThinMatrix.WindowCompletionRows
open BinaryCell BinaryGroupedCoordinates BinaryGroupedPreparation

theorem prefix_row_abs {P ell r C : ℕ} (xs : CappedPrefixProgram.Prepared P ell r C)
    (A : ℕ) (ha : ∀ p, PrefixCompletionMatrices.LeafBound (xs.traces.get p) A)
    (labels : Vector (Fin 4) (P+ell)) (c : Fin C) :
    (view ((PrefixCompletionProgram.row xs (PrefixCompletionMatrices.prepare xs).value labels).value.output.get c)).natAbs≤
      CappedSubsetList.count ell r*A := by
  apply BinaryGroupedCompletion.runRow_abs
  intro j c
  rw [PrefixCompletionMatrices.prepare_get]
  exact ha _ _ _ _

theorem prefix_execute_abs {P ell r C : ℕ} (xs : CappedPrefixProgram.Prepared P ell r C)
    (A : ℕ) (ha : ∀ p, PrefixCompletionMatrices.LeafBound (xs.traces.get p) A)
    (labels : Array (Vector (Fin 4) (P+ell))) (i : ℕ) (hi : i<labels.size) (c : Fin C) :
    (view (((PrefixCompletionProgram.execute xs labels).value.requests[i]'(by simpa using hi)).output.get c)).natAbs≤
      CappedSubsetList.count ell r*A := by
  rw [PrefixCompletionProgram.execute_get xs labels i hi]
  exact prefix_row_abs _ _ ha _ _

theorem window_abs {k ell C : ℕ} (source : WindowPrefixProgram.Prepared k ell C)
    (layout : RetainedWindowPermutation.Layout (2*k)) (labels : Array (Vector (Fin 4) (2*k)))
    (A : ℕ) (ha : ∀ p, PrefixCompletionMatrices.LeafBound (source.encoded.traces.get p) A)
    (i : ℕ) (hi : i<labels.size) (c : Fin C) :
    (view (((WindowCompletionProgram.execute source layout labels).completed.value.requests[i]'(by simpa using hi)).output.get c)).natAbs≤
      2^(WindowPrefixProgram.length k ell)*A := by
  exact (prefix_execute_abs source.encoded A ha _ i (by simpa using hi) c).trans
    (Nat.mul_le_mul_right A (BinaryGroupedCompletion.count_le_power _ _))

def copyRow {C : ℕ} (row : Vector Cell C) : Run (Vector Cell C) :=
  tabulate row (fun c => let x := copy (row.get c); ⟨x.value,x.bitSteps,8⟩)

@[simp] theorem copyRow_view {C : ℕ} (row : Vector Cell C) (c : Fin C) :
    view ((copyRow row).value.get c)=view (row.get c) := by
  simp only [copyRow,tabulate_get,copy_view]

theorem copyRow_bits {C : ℕ} (row : Vector Cell C) (A : ℕ)
    (ha : ∀ c, (view (row.get c)).natAbs≤A) :
    (copyRow row).bitSteps≤C*BackendScalarBits.backendScalarUnit A.size :=
  tabulate_bits _ _ (fun c => copy_price _ _ (Nat.size_le_size (ha c)))

theorem copyRow_control {C : ℕ} (row : Vector Cell C) :
    (copyRow row).control≤C*40+8 := tabulate_control _ _ (fun _ => le_refl 8)

structure Prepared (k ell C M : ℕ) where
  completed : WindowCompletionProgram.Prepared k ell C
  rows : Run (Vector (Vector Cell C) M)

def execute {k ell C M : ℕ} (source : WindowPrefixProgram.Prepared k ell C)
    (layout : RetainedWindowPermutation.Layout (2*k)) (labels : Vector (Vector (Fin 4) (2*k)) M) :
    Run (Prepared k ell C M) :=
  let out := WindowCompletionProgram.execute source layout labels.toArray
  let rows := tabulate labels (fun i => copyRow ((out.completed.value.requests[i.val]'(by simp [out])).output))
  ⟨⟨out,rows⟩,out.completed.bitSteps+rows.bitSteps,out.requests.work+out.completed.control+rows.control+8⟩

theorem execute_get {k ell C M : ℕ} (source : WindowPrefixProgram.Prepared k ell C)
    (layout : RetainedWindowPermutation.Layout (2*k)) (labels : Vector (Vector (Fin 4) (2*k)) M)
    (i : Fin M) (c : Fin C) :
    view ((((execute source layout labels).value.rows.value.get i).get c))=
      view (((WindowCompletionProgram.execute source layout labels.toArray).completed.value.requests[i.val]'(by simp)).output.get c) := by
  simp only [execute,tabulate_get,copyRow_view]

theorem execute_abs {k ell C M : ℕ} (source : WindowPrefixProgram.Prepared k ell C)
    (layout : RetainedWindowPermutation.Layout (2*k)) (labels : Vector (Vector (Fin 4) (2*k)) M)
    (A : ℕ) (ha : ∀ p, PrefixCompletionMatrices.LeafBound (source.encoded.traces.get p) A)
    (i : Fin M) (c : Fin C) :
    (view (((execute source layout labels).value.rows.value.get i).get c)).natAbs≤
      2^(WindowPrefixProgram.length k ell)*A := by
  rw [execute_get]
  exact window_abs _ _ _ A ha i.val (by simp) c

def bitBudget (k ell r C A M : ℕ) : ℕ :=
  PrefixCompletionProgram.bitBudget (WindowPrefixProgram.prefixLength k ell)
    (WindowPrefixProgram.length k ell) r C A M+
  M*(C*BackendScalarBits.backendScalarUnit (2^(WindowPrefixProgram.length k ell)*A).size)
def controlBudget (k ell r C M : ℕ) : ℕ :=
  M*(48*k+56)+8+PrefixCompletionProgram.controlBudget (WindowPrefixProgram.prefixLength k ell)
    (WindowPrefixProgram.length k ell) r C M+(M*(C*40+8+32)+8)+8

theorem execute_bits {k ell C M : ℕ} (source : WindowPrefixProgram.Prepared k ell C)
    (layout : RetainedWindowPermutation.Layout (2*k)) (labels : Vector (Vector (Fin 4) (2*k)) M)
    (A : ℕ) (ha : ∀ p, PrefixCompletionMatrices.LeafBound (source.encoded.traces.get p) A) :
    (execute source layout labels).bitSteps≤bitBudget k ell source.rareCap C A M := by
  apply Nat.add_le_add
  · simpa only [Vector.size_toArray] using WindowCompletionProgram.execute_bits source layout labels.toArray A ha
  · apply tabulate_bits
    intro i
    apply copyRow_bits
    intro c
    exact window_abs _ _ _ A ha i.val (by simp) c

theorem execute_control {k ell C M : ℕ} (source : WindowPrefixProgram.Prepared k ell C)
    (layout : RetainedWindowPermutation.Layout (2*k)) (labels : Vector (Vector (Fin 4) (2*k)) M) :
    (execute source layout labels).control≤controlBudget k ell source.rareCap C M := by
  apply Nat.add_le_add_right
  apply Nat.add_le_add
  · simpa only [Vector.size_toArray] using WindowCompletionProgram.execute_control source layout labels.toArray
  · exact tabulate_control _ _ (fun _ => copyRow_control _)

#print axioms prefix_row_abs
#print axioms prefix_execute_abs
#print axioms window_abs
#print axioms copyRow_view
#print axioms copyRow_bits
#print axioms copyRow_control
#print axioms execute_get
#print axioms execute_abs
#print axioms execute_bits
#print axioms execute_control
end ThinMatrix.WindowCompletionRows
