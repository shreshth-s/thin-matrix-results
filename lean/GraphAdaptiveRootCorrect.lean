import GraphAdaptiveRootBatch
import GraphSharedTargets

set_option autoImplicit false
set_option maxRecDepth 7000
set_option maxHeartbeats 1800000

/-! The retained addressed root batch reconstructs the original root at each
selected occurrence. The correctness comparison uses the elementary routine
only as a specification; no elementary completion is executed in the new path.
Physical targets and projected labels are retained outside the batch. -/
namespace ThinMatrix.GraphAdaptiveRootCorrect
open BinaryCell BinaryGroupedCoordinates BinaryGroupedPreparation
open scoped BigOperators
open GraphAdaptiveRootBatch
variable {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
  (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f)

/-- Only the selected label influences a completed row. -/
theorem window_label_eq {k ell C : ℕ} (source : WindowPrefixProgram.Prepared k ell C)
    (layout : RetainedWindowPermutation.Layout (2*k))
    (xs ys : Array (Vector (Fin 4) (2*k))) (i : Fin xs.size) (j : Fin ys.size)
    (he : xs[i.val]=ys[j.val]) (c : Fin C) :
    view (((WindowCompletionProgram.execute source layout xs).completed.value.requests[i.val]'(by simp)).output.get c)=
      view (((WindowCompletionProgram.execute source layout ys).completed.value.requests[j.val]'(by simp)).output.get c) := by
  rw [WindowCompletionProgram.execute_value _ _ _ i.val i.isLt c,WindowCompletionProgram.execute_value _ _ _ j.val j.isLt c]
  rw [he]

theorem reference_eq (input : BinaryFoldedFormation.Inputs n) (a b : ℕ)
    (i : Index f p) (block : Fin (CompactBlocks.blockCount n h)) (s : Fin (W f p))
    (labels : Array (Vector (Fin 4) (2*(p.L-p.m)))) (j : Fin labels.size)
    (request : Fin (FoldedBackendExecution.windowQuerySize n))
    (hl : labels[j.val]=(GraphSharedTargets.project f p input.target i).value.labels[request.val]'(by simp))
    (c : Fin ((p.m+1)*f.cyclic)) :
    view ((reference f p input a b i block s labels j).get c)=
      view (((GraphPrefixCompletion.fromInputs f p block input a b (E f p i) (i.atSlot s)).completed.completed.value.requests[request.val]'(by simp [GraphPrefixCompletion.fromInputs])).output.get c) := by
  dsimp only [reference,GraphPrefixCompletion.fromInputs,GraphPrefixCompletion.execute]
  exact window_label_eq _ _ labels _ j ⟨request.val,by simp⟩ hl c

attribute [local irreducible] GraphPrefixProgram.fromInputs GraphAdaptiveBatchSources.collect GraphAdaptiveBatchSources.source

theorem correct (hm : p.m≤p.L-p.m) (input : BinaryFoldedFormation.Inputs n) (a b : ℕ)
    (stored : GraphAdaptiveBatchSources.Stored f p)
    (hc : GraphAdaptiveBatchSources.Correct f p hm input a b stored)
    (i : Index f p) {A Z : ℕ} (scheme : RectangularBatch.Scheme) (hv : scheme.Valid)
    (hD : 0<D f p i) (hA : 0<A) (hZ : 0<Z)
    (hfirst : (A-1)^scheme.den≤(D f p i)^scheme.num) (hlast : Z≤(D f p i)^scheme.z)
    (labels : Array (Vector (Fin 4) (2*(p.L-p.m)))) (j : Fin labels.size)
    (request : Fin (FoldedBackendExecution.windowQuerySize n))
    (hl : labels[j.val]=(GraphSharedTargets.project f p input.target i).value.labels[request.val]'(by simp))
    (block : Fin (CompactBlocks.blockCount n h)) (c : Fin ((p.m+1)*f.cyclic)) :
    view ((RootProductCollection.output (execute f p i scheme hD hA hZ hfirst hlast
      (prepare f p hm input a b stored hc i).value labels).value j).get (PrefixBlockBatch.column block c))=
      view (((GraphRootCompletion.fromInputs f p block input a b (E f p i) i).completed.value.sums.value.get request).output.get c) := by
  rw [GraphAdaptiveRootBatch.correct f p hm input a b stored hc i scheme hv hD hA hZ hfirst hlast]
  rw [GraphRootCompletion.fromInputs,GraphRootCompletion.execute_view]
  apply Finset.sum_congr rfl
  intro s _
  exact reference_eq f p input a b i block s labels j request hl c


#print axioms window_label_eq
#print axioms reference_eq
#print axioms correct
end ThinMatrix.GraphAdaptiveRootCorrect
