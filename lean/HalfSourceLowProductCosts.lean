import GraphOwnLowProduction
import HalfSourceSelectedRootCost

/-! Actual LOW selected products and family accumulation. Completed roots
are charged by their actual returned counters, not a requested runtime bound. -/
namespace ThinMatrix.HalfSourceLowProductCosts
open BinaryCell BinaryGroupedCoordinates ExactHalfSourcePlan ResidualFamilyKeys
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 8000
variable {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
  (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f)

 def extra (W A : ℕ) : ℕ :=
  2*RetainedRootWindows.countBudget p.m+32*p.m+80+
    16*FoldedBackendExecution.windowQuerySize n+
    ResidualChannelTranspose.budget p.m (channelCount p.m p.t)+
    102000*FoldedBackendExecution.windowQuerySize n*CompactBlocks.blockCount n h*f.cyclic*
      (HalfSourceSelectedRootCost.width (p.m+1) f.cyclic p.t W A)^4

variable (ws : Vector Cell p.t) (channels : Vector (Channel p.m) (channelCount p.m p.t))
  (requests : GraphOwnRootProduct.Requests f p) (roots : GraphOwnLowProgram.RootFamily f p)

 theorem channel_bound (u v : Fin (J p.m)) (run : Fin (2*p.m+1)) (c : Fin (channelCount p.m p.t))
    (W A : ℕ) (hw : ∀ d,(view (ws.get d)).natAbs≤W)
    (hr : ∀ u v run c side,SelectedRootRows.RowsBound A (roots u v run c side).value)
    (j : Fin (FoldedBackendExecution.windowQuerySize n)) (block : Fin (CompactBlocks.blockCount n h)) :
    (view (((GraphOwnLowProgram.channel f p ws channels requests roots u v run c).value.get j).get block)).natAbs≤
      p.t*(W*SelectedRootProduct.productMagnitude f.cyclic p.t A) := by
  letI : NeZero f.cyclic := ⟨Nat.ne_of_gt f.cyclic_pos⟩
  exact SelectedRootRows.execute_bound ws _ _ _ W A _ hw
    (hr u v run c false) (hr u v run (ResidualChannelTranspose.locate channels c).value true) j block

 theorem channel_price (u v : Fin (J p.m)) (run : Fin (2*p.m+1)) (c : Fin (channelCount p.m p.t))
    (W A price : ℕ) (hB : 1 ≤ CompactBlocks.blockCount n h)
    (hw : ∀ d,(view (ws.get d)).natAbs≤W)
    (hr : ∀ u v run c side,SelectedRootRows.RowsBound A (roots u v run c side).value) :
    (GraphOwnLowProgram.channel f p ws channels requests roots u v run c).bitSteps+
      price*(GraphOwnLowProgram.channel f p ws channels requests roots u v run c).control ≤
      (roots u v run c false).bitSteps+price*(roots u v run c false).control+
      ((roots u v run (ResidualChannelTranspose.locate channels c).value true).bitSteps+
        price*(roots u v run (ResidualChannelTranspose.locate channels c).value true).control)+
      (price+1)*extra f p W A := by
  have hb := GraphOwnRootProduct.bits f p ws (channels.get c) requests _ _ W A hw
    (hr u v run c false) (hr u v run (ResidualChannelTranspose.locate channels c).value true)
  have hc := GraphOwnRootProduct.control f p ws (channels.get c) requests
    (roots u v run c false).value (roots u v run (ResidualChannelTranspose.locate channels c).value true).value
  have hwc := RetainedRootWindows.weights_bits (channels.get c)
  rw[RetainedRootWindows.weights_control] at hc
  have he := HalfSourceSelectedRootCost.rows_budget (p.m+1) f.cyclic p.t (CompactBlocks.blockCount n h)
    (FoldedBackendExecution.windowQuerySize n) W A f.cyclic_pos hB
  rw[GraphOwnLowProgram.channel_bits,GraphOwnLowProgram.channel_control,ResidualChannelTranspose.locate_bits,
    ResidualChannelTranspose.locate_control]
  unfold extra
  have hp := Nat.mul_le_mul_left price hc
  have hx := Nat.mul_le_mul_left price he
  change _ ≤ _ at hb hc
  dsimp only[GraphOwnRootProduct.M,GraphOwnRootProduct.B] at hb hc
  nlinarith [Nat.zero_le (price*(2*RetainedRootWindows.countBudget p.m)),
    Nat.zero_le (32*p.m+80+16*FoldedBackendExecution.windowQuerySize n+
      ResidualChannelTranspose.budget p.m (channelCount p.m p.t))]

 def rootMagnitude : ℕ := RetainedRootWindows.slots (p.L-p.m)*2^(3*(p.L-p.m)+p.L+4*p.m)

 theorem root_magnitude (input : BinaryFoldedFormation.Inputs n)
    (u v : Fin (J p.m)) (run : Fin (2*p.m+1)) (c : Fin (channelCount p.m p.t))
    (side : Bool) (j : Fin (FoldedBackendExecution.windowQuerySize n))
    (block : Fin (CompactBlocks.blockCount n h)) (col : Fin ((p.m+1)*f.cyclic)) :
    (GraphOwnRootSpec.rootValue f p input u v run c side j block col).natAbs ≤ rootMagnitude f p := by
  unfold GraphOwnRootSpec.rootValue
  have hh := GraphRootCompletion.fromInputs_abs f p block input
    (GraphOwnBandRouter.ownBand side (GraphOwnRootSpec.physical f p input.target j))
    (GraphOwnBandRouter.ownBand side (GraphOwnRootSpec.physical f p input.target j)) 0
    (GraphOwnRootSpec.index f p u v run c side (GraphOwnRootSpec.physical f p input.target j)) j col
  rw[GraphRootCompletion.aggregate_magnitude] at hh
  exact hh

 theorem rows_bound_of_correct (input : BinaryFoldedFormation.Inputs n)
    (hroot : ∀ u v run c side j block col,
      view (((roots u v run c side).value.get j).get (PrefixBlockBatch.column block col))=
        GraphOwnRootSpec.rootValue f p input u v run c side j block col)
    (u v : Fin (J p.m)) (run : Fin (2*p.m+1)) (c : Fin (channelCount p.m p.t)) (side : Bool) :
    SelectedRootRows.RowsBound (rootMagnitude f p) (roots u v run c side).value := by
  intro j col
  obtain ⟨⟨b,k⟩,he⟩ := finProdFinEquiv.surjective col
  rw[←he]
  change (view (((roots u v run c side).value.get j).get (PrefixBlockBatch.column b k))).natAbs≤_
  rw[hroot]
  exact root_magnitude f p input u v run c side j b k

#print axioms channel_bound
#print axioms channel_price
#print axioms root_magnitude
#print axioms rows_bound_of_correct
end ThinMatrix.HalfSourceLowProductCosts
