import PrefixCompletionProgram

set_option autoImplicit false

/-! Request labels read the actual retained forward permutation. Opposite
ordinary forms use the same local transform as the graph-window source. -/
namespace ThinMatrix.WindowCompletionRequests
open BinaryGroupedCoordinates BinaryGroupedPreparation GroupedPreparation

/-- Original ordinary opposite labels, converted before the forward transform. -/
def oppositeLabel (q : Fin 4) : Fin 4 :=
  if q=0 then 1 else if q=1 then 3 else if q=2 then 0 else 2

theorem opposite_form (q : Fin 4) (a : Fin 3) :
    (∑ b, BinaryPrefixContraction.form (oppositeLabel q) b*OppositeWindowLayer.matrix b a)=
      WalshEmbedding.ordinaryOpposite (decide (2≤q.val)) (q.val%2==1) (SourceCoordinates.oppositeEquiv a) := by
  fin_cases q <;> fin_cases a <;> decide

theorem normal_form (q : Fin 4) (a : Fin 3) :
    BinaryPrefixContraction.form q a=WalshEmbedding.ordinaryNormal
      (decide (2≤q.val)) (q.val%2==1) (DistinguishedResidualSupport.normalRemaining a) := by
  fin_cases q <;> fin_cases a <;> decide


def orient {k : ℕ} (labels : Vector (Fin 4) (2*k)) : GroupedPreparation.Counted (Vector (Fin 4) (2*k)) :=
  ⟨ofStoredFn labels (fun i => if k ≤ i.val then oppositeLabel (labels.get i) else labels.get i),16*labels.toArray.size+8⟩

@[simp] theorem orient_get {k : ℕ} (labels : Vector (Fin 4) (2*k)) (i : Fin (2*k)) :
    (orient labels).value.get i=if k ≤ i.val then oppositeLabel (labels.get i) else labels.get i := by
  simp [orient,ofStoredFn_eq]

def transport {k : ℕ} (ell : ℕ) (layout : RetainedWindowPermutation.Layout (2*k))
    (labels : Vector (Fin 4) (2*k)) : GroupedPreparation.Counted
      (Vector (Fin 4) (WindowPrefixProgram.prefixLength k ell+WindowPrefixProgram.length k ell)) :=
  ⟨Vector.cast (WindowPrefixProgram.dimension k ell).symm
    (ofStoredFn layout.forward (fun i => labels.get (layout.forward.get i))),8*layout.forward.toArray.size+8⟩

theorem transport_get {k : ℕ} (ell : ℕ) (layout : RetainedWindowPermutation.Layout (2*k))
    (labels : Vector (Fin 4) (2*k))
    (i : Fin (WindowPrefixProgram.prefixLength k ell+WindowPrefixProgram.length k ell)) :
    (transport ell layout labels).value.get i=labels.get (layout.forward.get (Fin.cast (WindowPrefixProgram.dimension k ell) i)) := by
  simp [transport,ofStoredFn_eq]

theorem transport_work {k : ℕ} (ell : ℕ) (layout : RetainedWindowPermutation.Layout (2*k))
    (labels : Vector (Fin 4) (2*k)) : (transport ell layout labels).work=16*k+8 := by
  simp [transport]; ring

theorem forms {k : ℕ} (ell : ℕ) (normal : Bool) (slot : Fin (RetainedRootWindows.slots k))
    (labels : Vector (Fin 4) (2*k)) :
    GraphPrefixTensor.originalForms ell normal slot
      (fun i => BinaryPrefixContraction.form ((transport ell (RetainedWindowPermutation.build k (min ell k) normal slot).value labels).value.get i))=
      OppositeTensorBridge.pushForms (RetainedOppositeTransform.axes k) (fun i => BinaryPrefixContraction.form (labels.get i)) := by
  unfold GraphPrefixTensor.originalForms
  congr 1
  funext i a
  dsimp only
  rw [transport_get,RetainedWindowPermutation.build_forward]
  simp

theorem ordinary_forms {k : ℕ} (labels : Vector (Fin 4) (2*k)) (i : Fin (2*k)) (a : Fin 3) :
    OppositeTensorBridge.pushForms (RetainedOppositeTransform.axes k)
      (fun j => BinaryPrefixContraction.form ((orient labels).value.get j)) i a=
      if k ≤ i.val then WalshEmbedding.ordinaryOpposite (decide (2≤(labels.get i).val))
        ((labels.get i).val%2==1) (SourceCoordinates.oppositeEquiv a)
      else WalshEmbedding.ordinaryNormal (decide (2≤(labels.get i).val))
        ((labels.get i).val%2==1) (DistinguishedResidualSupport.normalRemaining a) := by
  rw [OppositeTensorBridge.actual_forms]
  by_cases h : k ≤ i.val
  · simp only [h,↓reduceIte,orient_get]
    exact opposite_form _ _
  · simp only [h,↓reduceIte,orient_get]
    exact normal_form _ _

def requests {k : ℕ} (ell : ℕ) (layout : RetainedWindowPermutation.Layout (2*k))
    (labels : Array (Vector (Fin 4) (2*k))) :=
  GroupedPreparation.mapArray (fun q =>
    let oriented := orient q
    let out := transport ell layout oriented.value
    (⟨out.value,oriented.work+out.work+8⟩ : GroupedPreparation.Counted _)) labels

@[simp] theorem requests_size {k : ℕ} (ell : ℕ) (layout : RetainedWindowPermutation.Layout (2*k))
    (labels : Array (Vector (Fin 4) (2*k))) : (requests ell layout labels).value.size=labels.size := by
  simp [requests]

theorem requests_get {k : ℕ} (ell : ℕ) (layout : RetainedWindowPermutation.Layout (2*k))
    (labels : Array (Vector (Fin 4) (2*k))) (i : ℕ) (hi : i<labels.size) :
    (requests ell layout labels).value[i]'(by simpa using hi)=
      (transport ell layout (orient labels[i]).value).value := GroupedPreparation.mapArray_get _ _ _ _

theorem requests_work {k : ℕ} (ell : ℕ) (layout : RetainedWindowPermutation.Layout (2*k))
    (labels : Array (Vector (Fin 4) (2*k))) :
    (requests ell layout labels).work≤labels.size*(48*k+56)+8 := by
  have h := GroupedPreparation.mapArray_work (fun q =>
    let oriented := orient q
    let out := transport ell layout oriented.value
    (⟨out.value,oriented.work+out.work+8⟩ : GroupedPreparation.Counted _)) labels
    (W:=48*k+24) (by intro q; simp [orient,transport_work]; omega)
  unfold requests
  exact h.trans (by nlinarith)

#print axioms normal_form
#print axioms opposite_form
#print axioms orient_get
#print axioms transport_get
#print axioms transport_work
#print axioms forms
#print axioms ordinary_forms
#print axioms requests_size
#print axioms requests_get
#print axioms requests_work
end ThinMatrix.WindowCompletionRequests
