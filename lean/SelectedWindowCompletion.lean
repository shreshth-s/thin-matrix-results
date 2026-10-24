import WindowSharedCompletion
import GraphOwnResiduals

set_option autoImplicit false
set_option maxHeartbeats 1200000

/-! Complete only a routed root's own original occurrences. This adapter
consumes a retained compatible encoding bank and projects physical labels once;
its output remains indexed by the original request list, including duplicates.
It does not assume that every original occurrence belongs to this root. -/
namespace ThinMatrix.SelectedWindowCompletion
open BinaryCell BinaryGroupedCoordinates
open RectangularBatch (Scheme)
variable {S L m q M ell total cn co C B A Z : ℕ}

abbrev Sources (L m ell total cn co C B : ℕ) :=
  Vector (CappedPrefixProgram.Prepared (WindowPrefixProgram.prefixLength (L-m) ell)
    (WindowPrefixProgram.length (L-m) ell) (WindowPrefixProgram.cap (L-m) ell total cn co) C) B

def execute (scheme : Scheme) (hD : 0<WindowSharedCompletion.D (L-m) ell total cn co)
    (hA : 0<A) (hZ : 0<Z)
    (hfirst : (A-1)^scheme.den≤(WindowSharedCompletion.D (L-m) ell total cn co)^scheme.num)
    (hlast : Z≤(WindowSharedCompletion.D (L-m) ell total cn co)^scheme.z)
    (xs : Sources L m ell total cn co C B) (layout : RetainedWindowPermutation.Layout (2*(L-m)))
    (right : Bool) (requests : Vector (GraphCompletionRequests.Physical L m q) M)
    (tree : BooleanRequestRouter.Tree (Fin M) (GraphOwnRequestRouter.count S L m).size)
    (a b : Fin S) (normal opposite : Fin (GoodMapEmbedding.goodSlots L m).card)
    (maskN maskO : ResidualFamilyKeys.Mask L m) :=
  let projected := GraphOwnResiduals.project right requests tree a b normal opposite maskN maskO
  let out := WindowSharedCompletion.complete scheme hD hA hZ hfirst hlast xs layout projected.value.residuals.labels
  (projected,out)

theorem correct (scheme : Scheme) (hv : scheme.Valid)
    (hD : 0<WindowSharedCompletion.D (L-m) ell total cn co) (hA : 0<A) (hZ : 0<Z)
    (hfirst : (A-1)^scheme.den≤(WindowSharedCompletion.D (L-m) ell total cn co)^scheme.num)
    (hlast : Z≤(WindowSharedCompletion.D (L-m) ell total cn co)^scheme.z)
    (xs : Sources L m ell total cn co C B)
    (hk : ∀ b,(xs.get b).grouped.keys=GroupedPreparation.keyVector
      (WindowPrefixProgram.length (L-m) ell) (WindowPrefixProgram.cap (L-m) ell total cn co))
    (hp : ∀ b,(xs.get b).grouped.pairs=GroupedPreparation.pairKeys (WindowPrefixProgram.length (L-m) ell))
    (layout : RetainedWindowPermutation.Layout (2*(L-m)))
    (right : Bool) (requests : Vector (GraphCompletionRequests.Physical L m q) M)
    (tree : BooleanRequestRouter.Tree (Fin M) (GraphOwnRequestRouter.count S L m).size)
    (a b : Fin S) (normal opposite : Fin (GoodMapEmbedding.goodSlots L m).card)
    (maskN maskO : ResidualFamilyKeys.Mask L m)
    (j : Fin (GraphOwnRequestRouter.ids tree a b normal opposite).value.length) (block : Fin B) (c : Fin C) :
    let out := execute scheme hD hA hZ hfirst hlast xs layout right requests tree a b normal opposite maskN maskO
    view ((out.2.value.get ⟨j.val,by simp [GraphOwnResiduals.project]⟩).get
      (PrefixBlockBatch.column block c))=
      view ((PrefixCompletionProgram.row (xs.get block) (PrefixCompletionMatrices.prepare (xs.get block)).value
        ((WindowCompletionRequests.requests ell layout
          (GraphCompletionRequests.project right maskN maskO requests).value.labels).value[
            ((GraphOwnRequestRouter.ids tree a b normal opposite).value[j.val]).val]'(by simp))).value.output.get c) := by
  dsimp only
  have hh := WindowSharedCompletion.complete_correct scheme hv hD hA hZ hfirst hlast xs hk hp layout
    (GraphOwnResiduals.project right requests tree a b normal opposite maskN maskO).value.residuals.labels
    ⟨j.val,by simp [GraphOwnResiduals.project]⟩ block c
  have ht := GraphOwnResiduals.transport_get ell layout right requests tree a b normal opposite maskN maskO j
  change (WindowCompletionRequests.requests ell layout
    (GraphOwnResiduals.project right requests tree a b normal opposite maskN maskO).value.residuals.labels).value[j.val]'(by simp [GraphOwnResiduals.project])=_ at ht
  rw [ht] at hh
  exact hh

#print axioms correct
end ThinMatrix.SelectedWindowCompletion
