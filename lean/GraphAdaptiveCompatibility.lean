import GraphAdaptivePrefix
import GraphWindowCompatibility

set_option autoImplicit false
set_option maxRecDepth 6000
set_option maxHeartbeats 1600000

/-! All adaptive entries with one channel index share the exact chosen length,
channel budgets and permutation layout across blocks, data and bands. -/
namespace ThinMatrix.GraphAdaptiveCompatibility
open GoodMapEmbedding ExactHalfSourcePlan ResidualFamilyKeys
open GraphPrefixCompletion GraphAdaptivePrefix
variable {n h r b : ℕ} {f : CompactBlocks.PhysicalFactorization r}
  {p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f}

def selected (graph : GraphAdaptivePrefix.Prepared f p b) (index : Index p.L p.m p.t) : Entry p.L p.m f.cyclic :=
  (((side index.right (((graph.encoded.value.get index.u).get index.v).get index.run)).get index.normal).get index.opposite).get index.channel

def root (graph : GraphAdaptivePrefix.Prepared f p b) (index : Index p.L p.m p.t) : RetainedResidualFamily.Entry p.L p.m f.cyclic :=
  (((side index.right (((graph.roots.roots.value.get index.u).get index.v).get index.run)).get index.normal).get index.opposite).get index.channel

theorem selected_entry (hm : p.m ≤ p.L-p.m) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (bandL bandR cap : ℕ) (index : Index p.L p.m p.t) :
    selected (GraphAdaptivePrefix.fromInputs f p hm block input bandL bandR cap) index=
      (GraphAdaptivePrefix.entry hm cap (root (GraphAdaptivePrefix.fromInputs f p hm block input bandL bandR cap) index)).value := by
  rcases index with ⟨u,v,run,i,j,c,slot,right⟩
  cases right <;> simp only [selected,root,GraphAdaptivePrefix.fromInputs,GraphAdaptivePrefix.execute_get,
    side,Bool.false_eq_true,ite_false,ite_true,GraphAdaptivePrefix.family_get]

theorem root_channel (hm : p.m ≤ p.L-p.m) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (bandL bandR cap : ℕ) (index : Index p.L p.m p.t) :
    (root (GraphAdaptivePrefix.fromInputs f p hm block input bandL bandR cap) index).channel=
      (GraphWindowCompatibility.channelVector p.m p.t).get index.channel := by
  rcases index with ⟨u,v,run,i,j,c,slot,right⟩
  cases right
  · change ((((((((GraphResidualFamilies.fromInputs f p block input bandL bandR).roots.value.get u).get v).get run).1).get i).get j).get c).channel=_
    rw [GraphResidualFamilies.fromInputs_left_entry]
    rfl
  · change ((((((((GraphResidualFamilies.fromInputs f p block input bandL bandR).roots.value.get u).get v).get run).2).get i).get j).get c).channel=_
    rw [GraphResidualFamilies.fromInputs_right_entry]
    rfl

theorem selected_weights (hm : p.m ≤ p.L-p.m) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (bandL bandR cap : ℕ) (index : Index p.L p.m p.t) :
    (selected (GraphAdaptivePrefix.fromInputs f p hm block input bandL bandR cap) index).weights=
      GraphWindowCompatibility.counts index.channel := by
  rw [selected_entry]
  change (RetainedRootWindows.weights (root _ index).channel).value=_
  rw [root_channel]
  rfl

def typeLength (L m t : ℕ) (c : Fin (channelCount m t)) : ℕ :=
  HalfSourceSuffixChoice.forType L m (GraphWindowCompatibility.counts c).1 (GraphWindowCompatibility.counts c).2

theorem selected_length (hm : p.m ≤ p.L-p.m) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (bandL bandR : ℕ) (index : Index p.L p.m p.t) :
    length (selected (GraphAdaptivePrefix.fromInputs f p hm block input bandL bandR
      (HalfSourceSuffixChoice.limit p.m (p.L-p.m))) index)=typeLength p.L p.m p.t index.channel := by
  rw [selected_entry,entry_optimal_length,root_channel]
  rfl

theorem selected_counts (hm : p.m ≤ p.L-p.m) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (bandL bandR cap : ℕ) (index : Index p.L p.m p.t) :
    (selected (GraphAdaptivePrefix.fromInputs f p hm block input bandL bandR cap) index).prepared.windows.counts=
      GraphWindowCompatibility.counts index.channel := by
  rw [selected_entry,entry_windows]
  change (RetainedRootWindows.weights (root _ index).channel).value=_
  rw [root_channel]
  rfl

theorem entry_layout {L m C : ℕ} (hm : m ≤ L-m) (cap : ℕ) (root : RetainedResidualFamily.Entry L m C)
    (slot : Fin (RetainedRootWindows.slots (L-m))) :
    ((GraphAdaptivePrefix.entry hm cap root).value.prepared.permuted.get slot).layout=
      (RetainedWindowPermutation.build (L-m) (length (GraphAdaptivePrefix.entry hm cap root).value)
        (decide ((GraphAdaptivePrefix.entry hm cap root).value.weights.2≤(GraphAdaptivePrefix.entry hm cap root).value.weights.1)) slot).value := by
  simp only [GraphAdaptivePrefix.entry,GraphAdaptivePrefix.fixed,GraphWindowPermutations.entry,
    BinaryGroupedPreparation.tabulate_get,RetainedWindowPermutation.prepare,RetainedRootWindows.execute,length]
  rfl

theorem entry_prefix {L m C : ℕ} (hm : m ≤ L-m) (cap : ℕ) (root : RetainedResidualFamily.Entry L m C)
    (slot : Fin (RetainedRootWindows.slots (L-m))) :
    (GraphAdaptivePrefix.entry hm cap root).value.prepared.encoded.get slot=
      (WindowPrefixProgram.execute (length (GraphAdaptivePrefix.entry hm cap root).value) (m/2)
        (GraphAdaptivePrefix.entry hm cap root).value.weights.1 (GraphAdaptivePrefix.entry hm cap root).value.weights.2
        ((GraphAdaptivePrefix.entry hm cap root).value.prepared.permuted.get slot).coefficients).value := by
  simp only [GraphAdaptivePrefix.entry,GraphAdaptivePrefix.fixed,GraphPrefixProgram.entry,
    BinaryGroupedPreparation.tabulate_get,RetainedRootWindows.execute,length]

theorem selected_layout (hm : p.m ≤ p.L-p.m) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (bandL bandR : ℕ) (index : Index p.L p.m p.t) :
    let graph := GraphAdaptivePrefix.fromInputs f p hm block input bandL bandR (HalfSourceSuffixChoice.limit p.m (p.L-p.m))
    ((selected graph index).prepared.permuted.get index.slot).layout=
      GraphWindowCompatibility.layout p.L p.m (typeLength p.L p.m p.t index.channel) p.t index := by
  dsimp only
  have hl := selected_length hm block input bandL bandR index
  have hc := selected_weights hm block input bandL bandR (HalfSourceSuffixChoice.limit p.m (p.L-p.m)) index
  have hb := (HalfSourceSuffixChoice.forType_fit p.L p.m
    (GraphWindowCompatibility.counts index.channel).1 (GraphWindowCompatibility.counts index.channel).2).1
  rw [selected_entry] at hl hc ⊢
  rw [entry_layout,hl,hc]
  change typeLength p.L p.m p.t index.channel ≤ p.L-p.m at hb
  unfold GraphWindowCompatibility.layout
  rw [Nat.min_eq_left hb]

theorem selected_prefix (hm : p.m ≤ p.L-p.m) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (bandL bandR cap : ℕ) (index : Index p.L p.m p.t) :
    let e := selected (GraphAdaptivePrefix.fromInputs f p hm block input bandL bandR cap) index
    e.prepared.encoded.get index.slot =
      (WindowPrefixProgram.execute (length e) (p.m/2) (GraphWindowCompatibility.counts index.channel).1
        (GraphWindowCompatibility.counts index.channel).2 (e.prepared.permuted.get index.slot).coefficients).value := by
  dsimp only
  have hc := selected_weights hm block input bandL bandR cap index
  rw [selected_entry] at hc ⊢
  rw [entry_prefix,hc]

#print axioms entry_layout
#print axioms entry_prefix
#print axioms selected_entry
#print axioms root_channel
#print axioms selected_weights
#print axioms selected_length
#print axioms selected_counts
#print axioms selected_layout
#print axioms selected_prefix
end ThinMatrix.GraphAdaptiveCompatibility
