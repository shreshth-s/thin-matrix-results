import GraphPrefixCompletion

set_option autoImplicit false
set_option maxRecDepth 6000
set_option maxHeartbeats 1400000

/-! Actual graph windows have channel-dependent counts and layouts. They do
not depend on the middle block or graph values. These identities discharge
compatibility for shared completion; no cost bound or arbitrary common-layout
assumption is introduced. -/
namespace ThinMatrix.GraphWindowCompatibility
open GoodMapEmbedding ExactHalfSourcePlan ResidualFamilyKeys BinaryGroupedCoordinates
open GraphPrefixCompletion
variable {n h r : ℕ}

def channelVector (m t : ℕ) : Vector (Channel m) (channelCount m t) :=
  ⟨(ResidualFamilyKeys.channels m t).value.toArray,by simp [channels_length]⟩

def counts {m t : ℕ} (c : Fin (channelCount m t)) : ℕ×ℕ :=
  (RetainedRootWindows.weights ((channelVector m t).get c)).value

theorem window_counts (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (bandL bandR ell : ℕ) (index : Index p.L p.m p.t) :
    (window (GraphPrefixProgram.fromInputs f p block input bandL bandR ell) index).counts=counts index.channel := by
  rcases index with ⟨u,v,run,i,j,c,slot,right⟩
  cases right
  · change ((((((((GraphRootWindows.fromInputs f p block input bandL bandR (min ell (p.L-p.m))).windows.value.get u).get v).get run).1).get i).get j).get c).counts=_
    rw [GraphRootWindows.fromInputs_left_entry]
    simp only [RetainedRootWindows.execute]
    simp only [GraphRootWindows.fromInputs]
    rw [GraphResidualFamilies.fromInputs_left_entry]
    rfl
  · change ((((((((GraphRootWindows.fromInputs f p block input bandL bandR (min ell (p.L-p.m))).windows.value.get u).get v).get run).2).get i).get j).get c).counts=_
    rw [GraphRootWindows.fromInputs_right_entry]
    simp only [RetainedRootWindows.execute]
    simp only [GraphRootWindows.fromInputs]
    rw [GraphResidualFamilies.fromInputs_right_entry]
    rfl

def layout (L m ell t : ℕ) (index : Index L m t) : RetainedWindowPermutation.Layout (2*(L-m)) :=
  (RetainedWindowPermutation.build (L-m) (min ell (L-m))
    (decide ((counts index.channel).2≤(counts index.channel).1)) index.slot).value

theorem common_layout (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (bandL bandR ell : ℕ) (index : Index p.L p.m p.t) :
    (permuted (GraphPrefixProgram.fromInputs f p block input bandL bandR ell) index).layout=
      layout p.L p.m ell p.t index := by
  rw [fromInputs_layout,window_counts]
  rfl

theorem common_prefix (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (bandL bandR ell : ℕ) (index : Index p.L p.m p.t) :
    encodedSlot (GraphPrefixProgram.fromInputs f p block input bandL bandR ell) index=
      (WindowPrefixProgram.execute ell (p.m/2) (counts index.channel).1 (counts index.channel).2
        (permuted (GraphPrefixProgram.fromInputs f p block input bandL bandR ell) index).coefficients).value := by
  rw [fromInputs_prefix,window_counts]

#print axioms window_counts
#print axioms common_layout
#print axioms common_prefix
end ThinMatrix.GraphWindowCompatibility
