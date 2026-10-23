import GraphShiftedRootFactors

set_option autoImplicit false
set_option maxRecDepth 6000
set_option maxHeartbeats 2000000

/-! The executed strict-channel sum is the shifted LOW functional of the
actual cropped raw sources and physical ordinary forms. This is for a fixed
mask pair and band pair, prior to full mask routing and normalization. -/
namespace ThinMatrix.GraphShiftedLow
open GoodMapEmbedding ExactHalfSourcePlan ResidualFamilyKeys BinaryCell TensorContraction
open scoped BigOperators

variable {n h r b ell : ℕ} {f : CompactBlocks.PhysicalFactorization r}
  {p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f}

def accepts (graph : GraphPrefixProgram.Prepared f p b ell)
    (left right : Fin (goodSlots p.L p.m).card) (target : BinaryFoldedFormation.BinaryTable n)
    (bandL bandR : ℕ) (request : Fin (FoldedBackendExecution.windowQuerySize n)) : Bool :=
  RootRequestSelection.accepts bandL bandR false left right
    ((GraphCompletionRequests.prepare f p graph.permuted.transformed.source.roots.source.shape target).physical.value.get request)

noncomputable def value (graph : GraphPrefixProgram.Prepared f p b ell)
    (u v : Fin (J p.m)) (run : Fin (2*p.m+1)) (left right : Fin (goodSlots p.L p.m).card)
    (target : BinaryFoldedFormation.BinaryTable n) (bandL bandR : ℕ)
    (request : Fin (FoldedBackendExecution.windowQuerySize n)) (residue : Fin f.cyclic) : ℤ :=
  letI : NeZero f.cyclic := ⟨Nat.ne_of_gt f.cyclic_pos⟩
  if accepts graph left right target bandL bandR request then
    weightedLow (2*p.m) p.t (ShiftedLowChannelFormula.pencil
      (GraphShiftedRootFactors.source graph u v run false left right target request)
      (GraphShiftedRootFactors.source graph u v run true right left target request)
      (fun x => x.2.1) (fun x => x.2.2) (fun x => x.2.1) (fun x => x.2.2)) residue
  else 0

theorem weight_cast {q : ℕ} [NeZero q] (n t d : ℕ) :
    (residualWeight n t d : CyclicRing.Cyclic q)=((residualWeight n t d : ℤ) : CyclicRing.Cyclic q) := by
  simp [residualWeight]

theorem channel_sum (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (bandL bandR ell : ℕ)
    (u v : Fin (J p.m)) (run : Fin (2*p.m+1)) (left right : Fin (goodSlots p.L p.m).card)
    (request : Fin (FoldedBackendExecution.windowQuerySize n)) (residue : Fin f.cyclic) :
    let graph := GraphPrefixProgram.fromInputs f p block input bandL bandR ell
    (∑ c : Fin (channelCount p.m p.t), GraphWeightedRootProducts.sourceValue graph
      ⟨u,v,run,left,right,c⟩ input.target bandL bandR request residue)=
      value graph u v run left right input.target bandL bandR request residue := by
  dsimp only
  letI : NeZero f.cyclic := ⟨Nat.ne_of_gt f.cyclic_pos⟩
  let graph := GraphPrefixProgram.fromInputs f p block input bandL bandR ell
  have ha (c : Fin (channelCount p.m p.t)) :
      GraphRootProducts.accepted graph (GraphRootProducts.Index.leftIndex ⟨u,v,run,left,right,c⟩) input.target bandL bandR request=
      accepts graph left right input.target bandL bandR request := rfl
  change (∑ c, GraphWeightedRootProducts.sourceValue graph _ _ _ _ _ _)=value graph _ _ _ _ _ _ _ _ _ _
  unfold GraphWeightedRootProducts.sourceValue value
  simp only [ha]
  split
  · rw [ShiftedLowChannelFormula.weighted_channels graph.permuted.transformed.source.roots.keys.value.channels (ResidualFamilyKeys.prepare_channels _ _)]
    simp only [CyclicRing.sum_coeff]
    apply Finset.sum_congr rfl
    intro c _
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro d hd
    have hc : GraphWeightedRootProducts.card graph ⟨u,v,run,left,right,c⟩=
        (CappedBitPreparation.support (graph.permuted.transformed.source.roots.keys.value.channels.get c)).card :=
      (RetainedChannelPowerset.joint_card _).symm
    simp only [hc]
    split
    · rw [weight_cast,CyclicRing.intCast_mul_coeff]
      congr 1
      rw [GraphShiftedRootFactors.fromInputs_factor,GraphShiftedRootFactors.fromInputs_right_factor]
      rfl
    · rfl
  · simp only [Finset.sum_const_zero]

theorem channels_value (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (bandL bandR ell : ℕ)
    (u v : Fin (J p.m)) (run : Fin (2*p.m+1)) (left right : Fin (goodSlots p.L p.m).card)
    (request : Fin (FoldedBackendExecution.windowQuerySize n)) (residue : Fin f.cyclic) :
    let graph := GraphPrefixProgram.fromInputs f p block input bandL bandR ell
    view ((RootProductCollection.output (GraphRootFamilyProducts.channels graph u v run left right input.target bandL bandR).value request).get residue)=
      value graph u v run left right input.target bandL bandR request residue := by
  dsimp only
  rw [← channel_sum]
  unfold GraphRootFamilyProducts.channels
  rw [RootProductCollection.execute_value]
  apply Finset.sum_congr rfl
  intro c _
  exact GraphWeightedRootProducts.fromInputs_value f p block input bandL bandR ell ⟨u,v,run,left,right,c⟩ request residue

theorem fromInputs_value (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (bandL bandR ell : ℕ)
    (left right : Fin (goodSlots p.L p.m).card)
    (request : Fin (FoldedBackendExecution.windowQuerySize n)) (residue : Fin f.cyclic) :
    let graph := GraphPrefixProgram.fromInputs f p block input bandL bandR ell
    view ((RootProductCollection.output (GraphRootFamilyProducts.execute graph left right input.target bandL bandR).value request).get residue)=
      ∑ u : Fin (J p.m), ∑ v : Fin (J p.m), ∑ run : Fin (2*p.m+1),
        value graph u v run left right input.target bandL bandR request residue := by
  dsimp only
  rw [GraphRootFamilyProducts.fromInputs_value]
  apply Finset.sum_congr rfl; intro u _
  apply Finset.sum_congr rfl; intro v _
  apply Finset.sum_congr rfl; intro run _
  exact channel_sum f p block input bandL bandR ell u v run left right request residue

#print axioms weight_cast
#print axioms channel_sum
#print axioms channels_value
#print axioms fromInputs_value
end ThinMatrix.GraphShiftedLow
