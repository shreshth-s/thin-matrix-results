import GraphOwnRequestRouter

set_option autoImplicit false
set_option maxHeartbeats 1200000

/-! Project only the routed original physical occurrences. Both masks and
both remaining-position lists come from the retained production layout;
window transport preserves the same original occurrence index mapping. -/
namespace ThinMatrix.GraphOwnResiduals
open BinaryGroupedCoordinates
variable {S L m C M : ℕ}

structure Projected (L m M : ℕ) where
  indices : List (Fin M)
  residuals : GraphCompletionRequests.Residuals L m
  size_eq : residuals.labels.size=indices.length

def project (right : Bool) (requests : Vector (GraphCompletionRequests.Physical L m C) M)
    (tree : BooleanRequestRouter.Tree (Fin M) (GraphOwnRequestRouter.count S L m).size)
    (a b : Fin S) (normal opposite : Fin (GoodMapEmbedding.goodSlots L m).card)
    (maskN maskO : ResidualFamilyKeys.Mask L m) : Run (Projected L m M) :=
  let ids := GraphOwnRequestRouter.ids tree a b normal opposite
  let gathered := FiniteRequestRouter.gather requests ids.value
  let values : Vector _ ids.value.length := ⟨gathered.value,by simp [gathered]⟩
  let out := GraphCompletionRequests.project right maskN maskO values
  ⟨⟨ids.value,out.value,by simp [out]⟩,ids.bitSteps+gathered.bitSteps+out.bitSteps,
    ids.control+gathered.control+out.control+12⟩

theorem project_get (right : Bool) (requests : Vector (GraphCompletionRequests.Physical L m C) M)
    (tree : BooleanRequestRouter.Tree (Fin M) (GraphOwnRequestRouter.count S L m).size)
    (a b : Fin S) (normal opposite : Fin (GoodMapEmbedding.goodSlots L m).card)
    (maskN maskO : ResidualFamilyKeys.Mask L m)
    (j : Fin (GraphOwnRequestRouter.ids tree a b normal opposite).value.length) :
    (project right requests tree a b normal opposite maskN maskO).value.residuals.labels[j.val]'(by simp [project])=
      (GraphCompletionRequests.project right maskN maskO requests).value.labels[
        ((GraphOwnRequestRouter.ids tree a b normal opposite).value[j.val]).val]'(by simp) := by
  rw [GraphCompletionRequests.project_get]
  simp only [project,GraphCompletionRequests.project_get]
  simp [FiniteRequestRouter.gather,Vector.get_eq_getElem]

theorem project_bits (right : Bool) (requests : Vector (GraphCompletionRequests.Physical L m C) M)
    (tree : BooleanRequestRouter.Tree (Fin M) (GraphOwnRequestRouter.count S L m).size)
    (a b : Fin S) (normal opposite : Fin (GoodMapEmbedding.goodSlots L m).card)
    (maskN maskO : ResidualFamilyKeys.Mask L m) :
    (project right requests tree a b normal opposite maskN maskO).bitSteps=0 := by
  simp only [project,GraphOwnRequestRouter.ids,FiniteRequestRouter.ids,BooleanRequestRouter.read_bits,
    FiniteRequestRouter.gather,GraphCompletionRequests.project_bits,zero_add]

theorem project_control (right : Bool) (requests : Vector (GraphCompletionRequests.Physical L m C) M)
    (tree : BooleanRequestRouter.Tree (Fin M) (GraphOwnRequestRouter.count S L m).size)
    (a b : Fin S) (normal opposite : Fin (GoodMapEmbedding.goodSlots L m).card)
    (maskN maskO : ResidualFamilyKeys.Mask L m) :
    (project right requests tree a b normal opposite maskN maskO).control≤
      16*((GraphOwnRequestRouter.count S L m).size+1)^2+64*((GraphOwnRequestRouter.count S L m).size+1)^3+
      48*L+(GraphOwnRequestRouter.ids tree a b normal opposite).value.length*(32*(L-m)+80)+52 := by
  have hi := (FiniteRequestRouter.ids_cost tree (GraphOwnRequestRouter.encode a b normal opposite)).2
  have hp := GraphCompletionRequests.project_control right maskN maskO
    (⟨(FiniteRequestRouter.gather requests (GraphOwnRequestRouter.ids tree a b normal opposite).value).value,
      by simp⟩ : Vector _ (GraphOwnRequestRouter.ids tree a b normal opposite).value.length)
  change (GraphOwnRequestRouter.ids tree a b normal opposite).control≤_ at hi
  simp only [FiniteRequestRouter.gather] at hp
  simp only [project,FiniteRequestRouter.gather]
  nlinarith

structure WindowRequests (k ell M : ℕ) where
  indices : List (Fin M)
  labels : Array (Vector (Fin 4) (WindowPrefixProgram.prefixLength k ell+WindowPrefixProgram.length k ell))
  size_eq : labels.size=indices.length

def transport (ell : ℕ) (layout : RetainedWindowPermutation.Layout (2*(L-m)))
    (input : Projected L m M) : GroupedPreparation.Counted (WindowRequests (L-m) ell M) :=
  let out := WindowCompletionRequests.requests ell layout input.residuals.labels
  ⟨⟨input.indices,out.value,by simp [out,input.size_eq]⟩,out.work+8⟩

theorem transport_get (ell : ℕ) (layout : RetainedWindowPermutation.Layout (2*(L-m)))
    (right : Bool) (requests : Vector (GraphCompletionRequests.Physical L m C) M)
    (tree : BooleanRequestRouter.Tree (Fin M) (GraphOwnRequestRouter.count S L m).size)
    (a b : Fin S) (normal opposite : Fin (GoodMapEmbedding.goodSlots L m).card)
    (maskN maskO : ResidualFamilyKeys.Mask L m)
    (j : Fin (GraphOwnRequestRouter.ids tree a b normal opposite).value.length) :
    (transport ell layout (project right requests tree a b normal opposite maskN maskO).value).value.labels[j.val]'(by simp [transport,project])=
      (WindowCompletionRequests.requests ell layout (GraphCompletionRequests.project right maskN maskO requests).value.labels).value[
        ((GraphOwnRequestRouter.ids tree a b normal opposite).value[j.val]).val]'(by simp) := by
  have hl := WindowCompletionRequests.requests_get ell layout
    (project right requests tree a b normal opposite maskN maskO).value.residuals.labels j.val
    (by simp [project])
  have hr := WindowCompletionRequests.requests_get ell layout
    (GraphCompletionRequests.project right maskN maskO requests).value.labels
    ((GraphOwnRequestRouter.ids tree a b normal opposite).value[j.val]).val (by simp)
  have hh := congrArg (fun q => (WindowCompletionRequests.transport ell layout
    (WindowCompletionRequests.orient q).value).value)
    (project_get right requests tree a b normal opposite maskN maskO j)
  exact hl.trans (hh.trans hr.symm)

theorem transport_work (ell : ℕ) (layout : RetainedWindowPermutation.Layout (2*(L-m)))
    (input : Projected L m M) :
    (transport ell layout input).work ≤ input.indices.length*(48*(L-m)+56)+16 := by
  have hh := WindowCompletionRequests.requests_work ell layout input.residuals.labels
  rw [input.size_eq] at hh
  exact Nat.add_le_add_right hh 8

#print axioms project_get
#print axioms project_bits
#print axioms project_control
#print axioms transport_get
#print axioms transport_work
end ThinMatrix.GraphOwnResiduals
