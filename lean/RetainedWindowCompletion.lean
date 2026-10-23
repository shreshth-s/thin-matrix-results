import WindowCompletionRows
import GraphPrefixProgram

set_option autoImplicit false

/-! Execute every retained window for the shared request vector, retain the
complete copied outputs, and perform elementary binary accumulation. Row
references and selectors are materialized and charged separately from cell
copies/additions. No request or coefficient is removed. -/
namespace ThinMatrix.RetainedWindowCompletion
open BinaryCell BinaryGroupedCoordinates BinaryGroupedPreparation GroupedPreparation
open scoped BigOperators

structure SumRow (S C : ℕ) where
  data : Vector (Vector Cell C) S
  mask : Vector Bool S
  output : Vector Cell C

def sumRow {k ell C M S : ℕ} (windows : Vector (WindowCompletionRows.Prepared k ell C M) S)
    (i : Fin M) : Run (SumRow S C) :=
  let data := ofStoredFn windows (fun s => (windows.get s).rows.value.get i)
  let mask := ofStoredFn windows (fun _ => true)
  let out := BinaryGroupedCompletion.runRow mask data
  ⟨⟨data,mask,out.value⟩,out.bitSteps,out.control+16*windows.toArray.size+8⟩

theorem sumRow_view {k ell C M S : ℕ} (windows : Vector (WindowCompletionRows.Prepared k ell C M) S)
    (i : Fin M) (c : Fin C) :
    view ((sumRow windows i).value.output.get c)=∑ s, view (((windows.get s).rows.value.get i).get c) := by
  simp only [sumRow,BinaryGroupedCompletion.runRow_view,ofStoredFn_eq,Vector.get_ofFn,↓reduceIte]

theorem sumRow_abs {k ell C M S : ℕ} (windows : Vector (WindowCompletionRows.Prepared k ell C M) S)
    (A : ℕ) (ha : ∀ s i c, (view (((windows.get s).rows.value.get i).get c)).natAbs≤A)
    (i : Fin M) (c : Fin C) :
    (view ((sumRow windows i).value.output.get c)).natAbs≤S*A := by
  apply BinaryGroupedCompletion.runRow_abs
  simpa only [ofStoredFn_eq,Vector.get_ofFn] using fun s c => ha s i c

theorem sumRow_bits {k ell C M S : ℕ} (windows : Vector (WindowCompletionRows.Prepared k ell C M) S)
    (A : ℕ) (ha : ∀ s i c, (view (((windows.get s).rows.value.get i).get c)).natAbs≤A)
    (i : Fin M) : (sumRow windows i).bitSteps≤S*(C*BackendScalarBits.backendScalarUnit (S*A).size) := by
  apply BinaryGroupedCompletion.runRow_bits A _ _ _ (le_refl _)
  simpa only [ofStoredFn_eq,Vector.get_ofFn] using fun s c => ha s i c

theorem sumRow_control {k ell C M S : ℕ} (windows : Vector (WindowCompletionRows.Prepared k ell C M) S)
    (i : Fin M) : (sumRow windows i).control≤S*(40*C+40)+3*C+12 := by
  have h := BinaryGroupedCompletion.runRow_control
    (ofStoredFn windows (fun _ => true)) (ofStoredFn windows (fun s => (windows.get s).rows.value.get i))
  simp only [sumRow,Vector.size_toArray]
  nlinarith

structure Prepared (k ell C M S : ℕ) where
  windows : Run (Vector (WindowCompletionRows.Prepared k ell C M) S)
  sums : Run (Vector (SumRow S C) M)

def execute {k ell C M S : ℕ} (sources : Vector (WindowPrefixProgram.Prepared k ell C) S)
    (layouts : Vector (RetainedWindowPermutation.Layout (2*k)) S)
    (labels : Vector (Vector (Fin 4) (2*k)) M) : Run (Prepared k ell C M S) :=
  let windows := tabulate sources (fun s => WindowCompletionRows.execute (sources.get s) (layouts.get s) labels)
  let sums := tabulate labels (sumRow windows.value)
  ⟨⟨windows,sums⟩,windows.bitSteps+sums.bitSteps,windows.control+sums.control+8⟩

theorem execute_view {k ell C M S : ℕ} (sources : Vector (WindowPrefixProgram.Prepared k ell C) S)
    (layouts : Vector (RetainedWindowPermutation.Layout (2*k)) S)
    (labels : Vector (Vector (Fin 4) (2*k)) M) (i : Fin M) (c : Fin C) :
    view (((execute sources layouts labels).value.sums.value.get i).output.get c)=
      ∑ s, view (((WindowCompletionProgram.execute (sources.get s) (layouts.get s) labels.toArray).completed.value.requests[i.val]'(by simp)).output.get c) := by
  simp only [execute,tabulate_get,sumRow_view,WindowCompletionRows.execute_get]

def leafMagnitude (k ell A : ℕ) : ℕ := 2^(WindowPrefixProgram.length k ell)*A

theorem execute_abs {k ell C M S : ℕ} (sources : Vector (WindowPrefixProgram.Prepared k ell C) S)
    (layouts : Vector (RetainedWindowPermutation.Layout (2*k)) S)
    (labels : Vector (Vector (Fin 4) (2*k)) M) (A : ℕ)
    (ha : ∀ s p, PrefixCompletionMatrices.LeafBound ((sources.get s).encoded.traces.get p) A)
    (i : Fin M) (c : Fin C) :
    (view (((execute sources layouts labels).value.sums.value.get i).output.get c)).natAbs≤S*leafMagnitude k ell A := by
  simp only [execute,tabulate_get]
  apply sumRow_abs
  intro s j c
  rw [tabulate_get]
  exact WindowCompletionRows.execute_abs _ _ _ A (ha s) j c

def bitBudget {k ell C S : ℕ} (sources : Vector (WindowPrefixProgram.Prepared k ell C) S) (A M : ℕ) : ℕ :=
  (∑ s, WindowCompletionRows.bitBudget k ell (sources.get s).rareCap C A M)+
    M*(S*(C*BackendScalarBits.backendScalarUnit (S*leafMagnitude k ell A).size))
def controlBudget {k ell C S : ℕ} (sources : Vector (WindowPrefixProgram.Prepared k ell C) S) (M : ℕ) : ℕ :=
  GraphPrefixProgram.sumControl (fun s => WindowCompletionRows.controlBudget k ell (sources.get s).rareCap C M)+
    (M*(S*(40*C+40)+3*C+12+32)+8)+8

theorem execute_bits {k ell C M S : ℕ} (sources : Vector (WindowPrefixProgram.Prepared k ell C) S)
    (layouts : Vector (RetainedWindowPermutation.Layout (2*k)) S)
    (labels : Vector (Vector (Fin 4) (2*k)) M) (A : ℕ)
    (ha : ∀ s p, PrefixCompletionMatrices.LeafBound ((sources.get s).encoded.traces.get p) A) :
    (execute sources layouts labels).bitSteps≤bitBudget sources A M := by
  apply Nat.add_le_add
  · exact GraphPrefixProgram.tabulate_bits_vary _ _ _ (fun s => WindowCompletionRows.execute_bits _ _ _ A (ha s))
  · apply tabulate_bits
    intro i
    apply sumRow_bits
    intro s j c
    rw [tabulate_get]
    exact WindowCompletionRows.execute_abs _ _ _ A (ha s) j c

theorem execute_control {k ell C M S : ℕ} (sources : Vector (WindowPrefixProgram.Prepared k ell C) S)
    (layouts : Vector (RetainedWindowPermutation.Layout (2*k)) S)
    (labels : Vector (Vector (Fin 4) (2*k)) M) :
    (execute sources layouts labels).control≤controlBudget sources M := by
  apply Nat.add_le_add_right
  apply Nat.add_le_add
  · exact GraphPrefixProgram.tabulate_control_vary _ _ _ (fun _ => WindowCompletionRows.execute_control _ _ _)
  · exact tabulate_control _ _ (sumRow_control _)

/-- Counts copied per-window output cells and final output cells, retaining
request multiplicity even when two label vectors are equal. -/
def outputCells {k ell C M S : ℕ} (out : Prepared k ell C M S) : ℕ :=
  (out.windows.value.toList.map (fun w => (w.rows.value.toList.map (fun r => r.toArray.size)).sum)).sum+
    (out.sums.value.toList.map (fun r => r.output.toArray.size)).sum

theorem outputCells_eq {k ell C M S : ℕ} (out : Prepared k ell C M S) :
    outputCells out=(S+1)*M*C := by
  simp only [outputCells,Vector.size_toArray,List.map_const',Vector.length_toList,List.sum_replicate,smul_eq_mul]
  ring

#print axioms sumRow_view
#print axioms sumRow_abs
#print axioms sumRow_bits
#print axioms sumRow_control
#print axioms execute_view
#print axioms execute_abs
#print axioms execute_bits
#print axioms execute_control
#print axioms outputCells_eq
end ThinMatrix.RetainedWindowCompletion
