import PhysicalWordReindex

set_option autoImplicit false
set_option maxRecDepth 6000
set_option maxHeartbeats 1600000

/-! Ordinary factors at the actual retained physical positions. The excluded
outside p1 words have zero factors before any source or degree restrictions. -/
namespace ThinMatrix.PhysicalOrdinaryForms
open WalshEmbedding ResidualFamilyKeys DistinguishedResidualSupport RetainedShiftedFactor PhysicalWordReindex
open scoped BigOperators

def normal (label : Fin 4) (n : NormalLetter) : ℤ :=
  ShiftedSourceEmbedding.ordinaryNormal (decide (2≤label.val)) (label.val%2==1) n

def opposite (label : Fin 4) (o : OppositeLetter) : ℤ :=
  ordinaryOpposite (decide (2≤label.val)) (label.val%2==1) o

def normalPosition {L : ℕ} (right : Bool) (i : Fin L) : Fin (2*L) :=
  if right then CompleteThinProduct.physicalRight i else CompleteThinProduct.physicalLeft i

def oppositePosition {L : ℕ} (right : Bool) (i : Fin L) : Fin (2*L) :=
  if right then CompleteThinProduct.physicalLeft i else CompleteThinProduct.physicalRight i

def ordinary {L m : ℕ} (a b : Mask L m) (right : Bool) (outside : Vector (Fin 4) (2*L)) (w : Words L) : ℤ :=
  (∏ i, normal (outside.get (normalPosition right (remainingPosition a i))) (w.1 (remainingPosition a i)))*
    ∏ i, opposite (outside.get (oppositePosition right (remainingPosition b i))) (w.2 (remainingPosition b i))

theorem ordinary_zero {L m : ℕ} (a b : Mask L m) (right : Bool) (outside : Vector (Fin 4) (2*L))
    (w : Words L) (h : ¬Supported a w) : ordinary a b right outside w=0 := by
  classical
  obtain ⟨i,hi⟩ := not_forall.mp h
  have he : w.1 (remainingPosition a i)=.p1 := by simpa only [remainingPosition,not_not] using hi
  have hz : (∏ j, normal (outside.get (normalPosition right (remainingPosition a j))) (w.1 (remainingPosition a j)))=0 :=
    Finset.prod_eq_zero (Finset.mem_univ i) (by simp [he,normal,ShiftedSourceEmbedding.ordinaryNormal])
  simp [ordinary,hz]

def residualForm {L m C : ℕ} (a b : Mask L m) (right : Bool) (q : GraphCompletionRequests.Physical L m C)
    (i : Fin (2*(L-m))) (letter : Fin 3) : ℤ :=
  let labels := (GraphCompletionRequests.residual right (GraphCompletionRequests.positions a).value (GraphCompletionRequests.positions b).value q).value
  if L - m ≤ i.val then opposite (labels.get i) (SourceCoordinates.oppositeEquiv letter)
  else normal (labels.get i) (normalRemaining letter)

theorem residual_normal {L m C : ℕ} (a b : Mask L m) (right : Bool) (q : GraphCompletionRequests.Physical L m C)
    (i : Fin (L-m)) (letter : Fin 3) :
    residualForm a b right q (Fin.cast (by omega : (L-m)+(L-m)=2*(L-m)) (Fin.castAdd (L-m) i)) letter=
      normal (q.outside.get (normalPosition right (remainingPosition a i))) (normalRemaining letter) := by
  simp only [residualForm,Fin.val_cast,Fin.val_castAdd,Nat.not_le_of_gt i.isLt,↓reduceIte,
    GraphCompletionRequests.residual_get,Fin.cast_cast,Fin.cast_eq_self,Fin.append_left,normalPosition,remaining_position]

theorem residual_opposite {L m C : ℕ} (a b : Mask L m) (right : Bool) (q : GraphCompletionRequests.Physical L m C)
    (i : Fin (L-m)) (letter : Fin 3) :
    residualForm a b right q (Fin.cast (by omega : (L-m)+(L-m)=2*(L-m)) (Fin.natAdd (L-m) i)) letter=
      opposite (q.outside.get (oppositePosition right (remainingPosition b i))) (SourceCoordinates.oppositeEquiv letter) := by
  simp only [residualForm,Fin.val_cast,Fin.val_natAdd,Nat.le_add_right,↓reduceIte,
    GraphCompletionRequests.residual_get,Fin.cast_cast,Fin.cast_eq_self,Fin.append_right,oppositePosition,remaining_position]

theorem product_residual {L m C : ℕ} (a b : Mask L m) (right : Bool) (q : GraphCompletionRequests.Physical L m C)
    (x : Data m (L-m)) :
    (∏ i, residualForm a b right q i (x.1 i))=ordinary a b right q.outside (pack a b x) := by
  rw [← Equiv.prod_comp (finCongr (by omega : (L-m)+(L-m)=2*(L-m))),Fin.prod_univ_add]
  simp only [finCongr_apply,residual_normal,residual_opposite,ordinary,pack_normal_remaining,pack_opposite_remaining,splitWord]

variable {n h r b ell : ℕ} {f : CompactBlocks.PhysicalFactorization r}
  {p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f}

theorem graph_form (graph : GraphPrefixProgram.Prepared f p b ell) (right : Bool)
    (a b : Fin (GoodMapEmbedding.goodSlots p.L p.m).card) (target : BinaryFoldedFormation.BinaryTable n)
    (request : Fin (FoldedBackendExecution.windowQuerySize n)) (i : Fin (2*(p.L-p.m))) (letter : Fin 3) :
    GraphShiftedRootFactors.forms graph right a b target request i letter=
      residualForm (graph.permuted.transformed.source.roots.keys.value.masks.get a)
        (graph.permuted.transformed.source.roots.keys.value.masks.get b) right
        (LowRequestLocator.physical graph target request) i letter := by
  exact GraphShiftedRootFactors.forms_physical graph right a b target request i letter

theorem graph_product (graph : GraphPrefixProgram.Prepared f p b ell) (right : Bool)
    (a b : Fin (GoodMapEmbedding.goodSlots p.L p.m).card) (target : BinaryFoldedFormation.BinaryTable n)
    (request : Fin (FoldedBackendExecution.windowQuerySize n)) (x : Data p.m (p.L-p.m)) :
    (∏ i, GraphShiftedRootFactors.forms graph right a b target request i (x.1 i))=
      ordinary (graph.permuted.transformed.source.roots.keys.value.masks.get a)
        (graph.permuted.transformed.source.roots.keys.value.masks.get b) right (LowRequestLocator.physical graph target request).outside
        (pack (graph.permuted.transformed.source.roots.keys.value.masks.get a)
          (graph.permuted.transformed.source.roots.keys.value.masks.get b) x) := by
  simp_rw [graph_form]
  exact product_residual _ _ _ _ _

#print axioms ordinary_zero
#print axioms residual_normal
#print axioms residual_opposite
#print axioms product_residual
#print axioms graph_form
#print axioms graph_product
end ThinMatrix.PhysicalOrdinaryForms
