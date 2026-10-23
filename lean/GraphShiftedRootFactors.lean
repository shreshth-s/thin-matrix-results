import RetainedShiftedFactor
import GraphRootFamilyProducts

set_option autoImplicit false
set_option maxRecDepth 6000
set_option maxHeartbeats 2000000

/-! Actual graph roots and their projected ordinary forms are shifted cache
factors of the retained cropped raw input. Forms and raw sources do not depend
on the channel index; transposition swaps the channel halves and mask roles. -/
namespace ThinMatrix.GraphShiftedRootFactors
open GoodMapEmbedding ExactHalfSourcePlan ResidualFamilyKeys
open scoped BigOperators

variable {n h r b ell : ℕ} {f : CompactBlocks.PhysicalFactorization r}
  {p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f}

noncomputable def forms (graph : GraphPrefixProgram.Prepared f p b ell) (right : Bool)
    (a b : Fin (goodSlots p.L p.m).card) (target : BinaryFoldedFormation.BinaryTable n)
    (request : Fin (FoldedBackendExecution.windowQuerySize n)) : Fin (2*(p.L-p.m)) → Fin 3 → ℤ :=
  let roots := graph.permuted.transformed.source.roots
  let targets := GraphCompletionRequests.prepare f p roots.source.shape target
  let residuals := GraphCompletionRequests.project right (roots.keys.value.masks.get a) (roots.keys.value.masks.get b) targets.physical.value
  OppositeTensorBridge.pushForms (RetainedOppositeTransform.axes (p.L-p.m))
    (fun j => BinaryPrefixContraction.form ((WindowCompletionRequests.orient
      (residuals.value.labels[request.val]'(by simp [residuals]))).value.get j))

def raw (graph : GraphPrefixProgram.Prepared f p b ell) (u v : Fin (J p.m))
    (run : Fin (2*p.m+1)) (right : Bool) : BinarySourceFormation.RawStore p.L f.cyclic :=
  (if right then (((graph.permuted.transformed.source.roots.source.sources.value.get u).get v).2)
    else (((graph.permuted.transformed.source.roots.source.sources.value.get u).get v).1)).get run

noncomputable def source (graph : GraphPrefixProgram.Prepared f p b ell) (u v : Fin (J p.m))
    (run : Fin (2*p.m+1)) (right : Bool) (a b : Fin (goodSlots p.L p.m).card)
    (target : BinaryFoldedFormation.BinaryTable n) (request : Fin (FoldedBackendExecution.windowQuerySize n)) :
    RetainedShiftedFactor.Data p.m (p.L-p.m) → Polynomial (CyclicRing.Cyclic f.cyclic) :=
  letI : NeZero f.cyclic := ⟨Nat.ne_of_gt f.cyclic_pos⟩
  RetainedShiftedFactor.source (raw graph u v run right)
    (graph.permuted.transformed.source.roots.keys.value.masks.get a)
    (graph.permuted.transformed.source.roots.keys.value.masks.get b) (forms graph right a b target request)

theorem root_query (graph : GraphPrefixProgram.Prepared f p b ell)
    (i : GraphRootCompletion.Index p.L p.m p.t) (target : BinaryFoldedFormation.BinaryTable n)
    (request : Fin (FoldedBackendExecution.windowQuerySize n)) :
    letI : NeZero f.cyclic := ⟨Nat.ne_of_gt f.cyclic_pos⟩
    GraphRootProducts.rootPolynomial graph i target request=
      StoredRootPolynomial.query (ResidualWindowSource.rows (GraphRootCompletion.root graph i))
        (forms graph i.right i.normal i.opposite target request) := by
  exact StoredRootPolynomial.polynomialOf_query _ _

theorem fromInputs_root (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (bandL bandR ell : ℕ) (i : GraphRootCompletion.Index p.L p.m p.t) :
    let graph := GraphPrefixProgram.fromInputs f p block input bandL bandR ell
    GraphRootCompletion.root graph i=(RetainedResidualFamily.produce (raw graph i.u i.v i.run i.right)
      (graph.permuted.transformed.source.roots.keys.value.masks.get i.normal)
      (graph.permuted.transformed.source.roots.keys.value.masks.get i.opposite)
      (graph.permuted.transformed.source.roots.keys.value.channels.get i.channel)).value := by
  rcases i with ⟨u,v,run,a,b,c,right⟩
  cases right
  · exact GraphResidualFamilies.fromInputs_left_entry f p block input bandL bandR u v run a b c
  · exact GraphResidualFamilies.fromInputs_right_entry f p block input bandL bandR u v run a b c

theorem fromInputs_factor (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (bandL bandR ell : ℕ) (i : GraphRootCompletion.Index p.L p.m p.t)
    (request : Fin (FoldedBackendExecution.windowQuerySize n)) :
    let graph := GraphPrefixProgram.fromInputs f p block input bandL bandR ell
    GraphRootProducts.rootPolynomial graph i input.target request=
      ShiftedLowChannelFormula.leftFactor (graph.permuted.transformed.source.roots.keys.value.channels.get i.channel)
        (source graph i.u i.v i.run i.right i.normal i.opposite input.target request) (fun x => x.2.1) (fun x => x.2.2) := by
  dsimp only
  letI : NeZero f.cyclic := ⟨Nat.ne_of_gt f.cyclic_pos⟩
  rw [root_query,fromInputs_root]
  exact RetainedShiftedFactor.query_factor _ _ _ _ _

theorem fromInputs_right_factor (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (bandL bandR ell : ℕ) (i : GraphRootProducts.Index p.L p.m p.t)
    (request : Fin (FoldedBackendExecution.windowQuerySize n)) :
    let graph := GraphPrefixProgram.fromInputs f p block input bandL bandR ell
    GraphRootProducts.rootPolynomial graph (GraphRootProducts.transpose graph i).value input.target request=
      ShiftedLowChannelFormula.rightFactor (graph.permuted.transformed.source.roots.keys.value.channels.get i.channel)
        (source graph i.u i.v i.run true i.right i.left input.target request) (fun x => x.2.1) (fun x => x.2.2) := by
  dsimp only
  rw [fromInputs_factor]
  unfold ShiftedLowChannelFormula.rightFactor
  congr 1
  exact ResidualChannelTranspose.locate_get _ (ResidualFamilyKeys.prepare_channels _ _) _

/-- Remaining normal letters contain no p1; hence the actual ordinary forms
are exactly the shifted ordinary forms, with the physical projected labels. -/
theorem forms_physical (graph : GraphPrefixProgram.Prepared f p b ell) (right : Bool)
    (a b : Fin (goodSlots p.L p.m).card) (target : BinaryFoldedFormation.BinaryTable n)
    (request : Fin (FoldedBackendExecution.windowQuerySize n)) (i : Fin (2*(p.L-p.m))) (letter : Fin 3) :
    let roots := graph.permuted.transformed.source.roots
    let targets := GraphCompletionRequests.prepare f p roots.source.shape target
    let labels := (GraphCompletionRequests.residual right
      (GraphCompletionRequests.positions (roots.keys.value.masks.get a)).value
      (GraphCompletionRequests.positions (roots.keys.value.masks.get b)).value
      (targets.physical.value.get request)).value
    forms graph right a b target request i letter=
      if p.L - p.m ≤ i.val then WalshEmbedding.ordinaryOpposite (decide (2≤(labels.get i).val))
        ((labels.get i).val%2==1) (SourceCoordinates.oppositeEquiv letter)
      else ShiftedSourceEmbedding.ordinaryNormal (R := ℤ) (decide (2≤(labels.get i).val))
        ((labels.get i).val%2==1) (DistinguishedResidualSupport.normalRemaining letter) := by
  dsimp only
  unfold forms
  rw [GraphCompletionRequests.project_get,WindowCompletionRequests.ordinary_forms]
  split
  · rfl
  · fin_cases letter <;> simp [ShiftedSourceEmbedding.ordinaryNormal,DistinguishedResidualSupport.normalRemaining]

#print axioms forms_physical

#print axioms root_query
#print axioms fromInputs_root
#print axioms fromInputs_factor
#print axioms fromInputs_right_factor
end ThinMatrix.GraphShiftedRootFactors
