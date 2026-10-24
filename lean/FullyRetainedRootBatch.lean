import FullyRetainedWindowBatch
import RetainedRootBatch
import RootProductCollection

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! Complete every window of a root using retained shared source banks and
accumulate all block/coefficient columns. The caller supplies its already
routed occurrence labels once. Costs retain every window, child execution,
output column and binary addition; no desired exponent is a hypothesis. -/
namespace ThinMatrix.FullyRetainedRootBatch
open BinaryCell BinaryGroupedCoordinates
open RectangularBatch (Scheme)
open scoped BigOperators
variable {k ell total cn co C B A Z W : ℕ}

abbrev Bank (k ell total cn co C B : ℕ) :=
  SharedPrefixSourceBank.Prepared (WindowPrefixProgram.prefixLength k ell)
    (WindowPrefixProgram.length k ell) (WindowPrefixProgram.cap k ell total cn co) C B
abbrev Sources (k ell total cn co C B : ℕ) :=
  Vector (CappedPrefixProgram.Prepared (WindowPrefixProgram.prefixLength k ell)
    (WindowPrefixProgram.length k ell) (WindowPrefixProgram.cap k ell total cn co) C) B

def execute (scheme : Scheme) (hD : 0<WindowSharedCompletion.D k ell total cn co)
    (hA : 0<A) (hZ : 0<Z)
    (hfirst : (A-1)^scheme.den≤(WindowSharedCompletion.D k ell total cn co)^scheme.num)
    (hlast : Z≤(WindowSharedCompletion.D k ell total cn co)^scheme.z)
    (banks : Vector (Bank k ell total cn co C B) W)
    (layouts : Vector (RetainedWindowPermutation.Layout (2*k)) W)
    (labels : Array (Vector (Fin 4) (2*k))) :=
  RootProductCollection.execute banks (fun s =>
    FullyRetainedWindowBatch.execute scheme hD hA hZ hfirst hlast (banks.get s) (layouts.get s) labels)
    (fun rows i => rows.get i)

/-- Child scalar arrays agree exactly. Child counters are intentionally fresh. -/
theorem children_value_eq (scheme : Scheme) (hD : 0<WindowSharedCompletion.D k ell total cn co)
    (hA : 0<A) (hZ : 0<Z)
    (hfirst : (A-1)^scheme.den≤(WindowSharedCompletion.D k ell total cn co)^scheme.num)
    (hlast : Z≤(WindowSharedCompletion.D k ell total cn co)^scheme.z)
    (banks : Vector (Bank k ell total cn co C B) W)
    (layouts : Vector (RetainedWindowPermutation.Layout (2*k)) W)
    (labels : Array (Vector (Fin 4) (2*k))) :
    (execute scheme hD hA hZ hfirst hlast banks layouts labels).value.children.value=
      (RetainedRootBatch.execute scheme hD hA hZ hfirst hlast banks layouts labels).value.children.value := by
  apply Vector.ext
  intro i hi
  have hh : ((execute scheme hD hA hZ hfirst hlast banks layouts labels).value.children.value.get ⟨i,hi⟩)=
      ((RetainedRootBatch.execute scheme hD hA hZ hfirst hlast banks layouts labels).value.children.value.get ⟨i,hi⟩) := by
    simp only [execute,RetainedRootBatch.execute,RootProductCollection.execute,
      BinaryGroupedPreparation.tabulate_get,FullyRetainedWindowBatch.value_eq]
  simpa only [Vector.get_eq_getElem] using hh

/-- The retained row data, masks and exact binary sum all agree. The child
run counters in the enclosing Prepared record are not asserted equal. -/
theorem rows_value_eq (scheme : Scheme) (hD : 0<WindowSharedCompletion.D k ell total cn co)
    (hA : 0<A) (hZ : 0<Z)
    (hfirst : (A-1)^scheme.den≤(WindowSharedCompletion.D k ell total cn co)^scheme.num)
    (hlast : Z≤(WindowSharedCompletion.D k ell total cn co)^scheme.z)
    (banks : Vector (Bank k ell total cn co C B) W)
    (layouts : Vector (RetainedWindowPermutation.Layout (2*k)) W)
    (labels : Array (Vector (Fin 4) (2*k))) :
    (execute scheme hD hA hZ hfirst hlast banks layouts labels).value.rows.value=
      (RetainedRootBatch.execute scheme hD hA hZ hfirst hlast banks layouts labels).value.rows.value := by
  have hh := children_value_eq scheme hD hA hZ hfirst hlast banks layouts labels
  change (BinaryGroupedPreparation.tabulate _ (RootProductCollection.sumRow _ _)).value=
    (BinaryGroupedPreparation.tabulate _ (RootProductCollection.sumRow _ _)).value
  change (BinaryGroupedPreparation.tabulate banks _).value=(BinaryGroupedPreparation.tabulate banks _).value at hh
  rw [hh]

theorem output_eq (scheme : Scheme) (hD : 0<WindowSharedCompletion.D k ell total cn co)
    (hA : 0<A) (hZ : 0<Z)
    (hfirst : (A-1)^scheme.den≤(WindowSharedCompletion.D k ell total cn co)^scheme.num)
    (hlast : Z≤(WindowSharedCompletion.D k ell total cn co)^scheme.z)
    (banks : Vector (Bank k ell total cn co C B) W)
    (layouts : Vector (RetainedWindowPermutation.Layout (2*k)) W)
    (labels : Array (Vector (Fin 4) (2*k))) (j : Fin labels.size) :
    RootProductCollection.output (execute scheme hD hA hZ hfirst hlast banks layouts labels).value j=
      RootProductCollection.output (RetainedRootBatch.execute scheme hD hA hZ hfirst hlast banks layouts labels).value j := by
  simp only [RootProductCollection.output,rows_value_eq]

theorem correct (scheme : Scheme) (hv : scheme.Valid)
    (hD : 0<WindowSharedCompletion.D k ell total cn co) (hA : 0<A) (hZ : 0<Z)
    (hfirst : (A-1)^scheme.den≤(WindowSharedCompletion.D k ell total cn co)^scheme.num)
    (hlast : Z≤(WindowSharedCompletion.D k ell total cn co)^scheme.z)
    (xs : Vector (Sources k ell total cn co C B) W)
    (banks : Vector (Bank k ell total cn co C B) W)
    (hb : ∀ s,banks.get s=(SharedPrefixSourceBank.prepare (xs.get s)).value)
    (hk : ∀ s b,((xs.get s).get b).grouped.keys=GroupedPreparation.keyVector
      (WindowPrefixProgram.length k ell) (WindowPrefixProgram.cap k ell total cn co))
    (hp : ∀ s b,((xs.get s).get b).grouped.pairs=GroupedPreparation.pairKeys (WindowPrefixProgram.length k ell))
    (layouts : Vector (RetainedWindowPermutation.Layout (2*k)) W)
    (labels : Array (Vector (Fin 4) (2*k))) (j : Fin labels.size) (b : Fin B) (c : Fin C) :
    view ((RootProductCollection.output (execute scheme hD hA hZ hfirst hlast banks layouts labels).value j).get
      (PrefixBlockBatch.column b c))=
      ∑ s, view ((PrefixCompletionProgram.row ((xs.get s).get b)
        (PrefixCompletionMatrices.prepare ((xs.get s).get b)).value
        ((WindowCompletionRequests.requests ell (layouts.get s) labels).value[j.val]'(by simp))).value.output.get c) := by
  rw [execute,RootProductCollection.execute_value]
  apply Finset.sum_congr rfl
  intro s _
  rw [hb s]
  exact FullyRetainedWindowBatch.correct scheme hv hD hA hZ hfirst hlast _ (hk s) (hp s) _ _ _ _ _

theorem prefix_row_bound {P len r C : ℕ} (xs : CappedPrefixProgram.Prepared P len r C)
    (H : ℕ) (hx : ∀ pair,PrefixCompletionMatrices.LeafBound (xs.traces.get pair) H)
    (labels : Vector (Fin 4) (P+len)) (c : Fin C) :
    (view ((PrefixCompletionProgram.row xs (PrefixCompletionMatrices.prepare xs).value labels).value.output.get c)).natAbs≤
      CappedSubsetList.count len r*H := by
  apply BinaryGroupedCompletion.runRow_abs
  intro j c
  rw [PrefixCompletionMatrices.prepare_get]
  exact hx _ _ _ _

theorem child_bound (scheme : Scheme) (hv : scheme.Valid)
    (hD : 0<WindowSharedCompletion.D k ell total cn co) (hA : 0<A) (hZ : 0<Z)
    (hfirst : (A-1)^scheme.den≤(WindowSharedCompletion.D k ell total cn co)^scheme.num)
    (hlast : Z≤(WindowSharedCompletion.D k ell total cn co)^scheme.z)
    (xs : Sources k ell total cn co C B)
    (hk : ∀ b,(xs.get b).grouped.keys=GroupedPreparation.keyVector
      (WindowPrefixProgram.length k ell) (WindowPrefixProgram.cap k ell total cn co))
    (hp : ∀ b,(xs.get b).grouped.pairs=GroupedPreparation.pairKeys (WindowPrefixProgram.length k ell))
    (H : ℕ) (hx : ∀ b pair,PrefixCompletionMatrices.LeafBound ((xs.get b).traces.get pair) H)
    (layout : RetainedWindowPermutation.Layout (2*k)) (labels : Array (Vector (Fin 4) (2*k)))
    (j : Fin labels.size) (column : Fin (B*C)) :
    (view (((FullyRetainedWindowBatch.execute scheme hD hA hZ hfirst hlast
      (SharedPrefixSourceBank.prepare xs).value layout labels).value.get j).get column)).natAbs≤
      WindowSharedCompletion.D k ell total cn co*H := by
  obtain ⟨⟨b,c⟩,he⟩ := finProdFinEquiv.surjective column
  subst column
  have hh := FullyRetainedWindowBatch.correct scheme hv hD hA hZ hfirst hlast xs hk hp layout labels j b c
  simp only [PrefixBlockBatch.column] at hh
  rw [hh]
  exact prefix_row_bound (xs.get b) H (hx b) _ c

theorem bits (scheme : Scheme) (hv : scheme.Valid)
    (hD : 0<WindowSharedCompletion.D k ell total cn co) (hA : 0<A) (hZ : 0<Z)
    (hfirst : (A-1)^scheme.den≤(WindowSharedCompletion.D k ell total cn co)^scheme.num)
    (hlast : Z≤(WindowSharedCompletion.D k ell total cn co)^scheme.z)
    (xs : Vector (Sources k ell total cn co C B) W)
    (banks : Vector (Bank k ell total cn co C B) W)
    (hb : ∀ s,banks.get s=(SharedPrefixSourceBank.prepare (xs.get s)).value)
    (hk : ∀ s b,((xs.get s).get b).grouped.keys=GroupedPreparation.keyVector
      (WindowPrefixProgram.length k ell) (WindowPrefixProgram.cap k ell total cn co))
    (hp : ∀ s b,((xs.get s).get b).grouped.pairs=GroupedPreparation.pairKeys (WindowPrefixProgram.length k ell))
    (H : ℕ) (hx : ∀ s b pair,PrefixCompletionMatrices.LeafBound (((xs.get s).get b).traces.get pair) H)
    (layouts : Vector (RetainedWindowPermutation.Layout (2*k)) W)
    (labels : Array (Vector (Fin 4) (2*k))) :
    (execute scheme hD hA hZ hfirst hlast banks layouts labels).bitSteps≤
      (∑ s,(FullyRetainedWindowBatch.execute scheme hD hA hZ hfirst hlast (banks.get s) (layouts.get s) labels).bitSteps)+
      labels.size*(W*((B*C)*BackendScalarBits.backendScalarUnit (W*(WindowSharedCompletion.D k ell total cn co*H)).size)) := by
  apply RootProductCollection.execute_bits
  · intro s j c
    rw [hb s]
    exact child_bound scheme hv hD hA hZ hfirst hlast _ (hk s) (hp s) H (hx s) _ _ _ _
  · intro s
    exact le_refl _

theorem control (scheme : Scheme)
    (hD : 0<WindowSharedCompletion.D k ell total cn co) (hA : 0<A) (hZ : 0<Z)
    (hfirst : (A-1)^scheme.den≤(WindowSharedCompletion.D k ell total cn co)^scheme.num)
    (hlast : Z≤(WindowSharedCompletion.D k ell total cn co)^scheme.z)
    (banks : Vector (Bank k ell total cn co C B) W)
    (layouts : Vector (RetainedWindowPermutation.Layout (2*k)) W)
    (labels : Array (Vector (Fin 4) (2*k))) :
    (execute scheme hD hA hZ hfirst hlast banks layouts labels).control≤
      RootProductCollection.controlBudget (fun s => (FullyRetainedWindowBatch.execute scheme hD hA hZ hfirst hlast
        (banks.get s) (layouts.get s) labels).control) labels.size (B*C) :=
  RootProductCollection.execute_control _ _ _ _ (fun _ => le_refl _)

#print axioms children_value_eq
#print axioms rows_value_eq
#print axioms output_eq
#print axioms correct
#print axioms prefix_row_bound
#print axioms child_bound
#print axioms bits
#print axioms control
end ThinMatrix.FullyRetainedRootBatch
