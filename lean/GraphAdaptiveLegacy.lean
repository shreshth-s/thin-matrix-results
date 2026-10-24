import GraphAdaptiveBatchSources

set_option autoImplicit false
set_option maxRecDepth 7000
set_option maxHeartbeats 2200000

/-! The adaptive entry is the same algebraic source/window/encoder as the
existing fixed-length graph construction at that channel's chosen length.
The fixed-length construction occurs only in specifications, never reruns in
this adapter. -/
namespace ThinMatrix.GraphAdaptiveLegacy
open GraphAdaptiveCompatibility GraphPrefixCompletion
theorem entry_fixed_permuted {L m C : ℕ} (hm : m≤L-m) (cap : ℕ) (root : RetainedResidualFamily.Entry L m C) :
    (GraphAdaptivePrefix.entry hm cap root).value.prepared.permuted=
      (GraphAdaptivePrefix.fixed (GraphAdaptivePrefix.length (GraphAdaptivePrefix.entry hm cap root).value) root).value.permuted := rfl

variable {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
  (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f)
  (hm : p.m ≤ p.L-p.m) (block : Fin (CompactBlocks.blockCount n h))
  (input : BinaryFoldedFormation.Inputs n) (bandL bandR : ℕ)
  (index : Index p.L p.m p.t)

theorem permuted_eq :
    ((selected (GraphAdaptivePrefix.fromInputs f p hm block input bandL bandR
      (HalfSourceSuffixChoice.limit p.m (p.L-p.m))) index).prepared.permuted.get index.slot)=
      permuted (GraphPrefixProgram.fromInputs f p block input bandL bandR
        (typeLength p.L p.m p.t index.channel)) index := by
  have hl := selected_length hm block input bandL bandR index
  rw [selected_entry] at hl ⊢
  rw [entry_fixed_permuted,hl]
  have hlen : typeLength p.L p.m p.t index.channel≤p.L-p.m :=
    (HalfSourceSuffixChoice.forType_fit _ _ _ _).1
  rcases index with ⟨u,v,run,i,j,c,slot,right⟩
  cases right <;>
    simp only [GraphAdaptivePrefix.fixed,permuted,root,GraphAdaptivePrefix.fromInputs,
      GraphPrefixProgram.fromInputs,GraphWindowPermutations.fromInputs,GraphWindowTransforms.fromInputs,
      GraphRootWindows.fromInputs,GraphWindowPermutations.execute_get,GraphWindowPermutations.family_get,
      GraphWindowTransforms.execute_get,GraphWindowTransforms.family_get,GraphRootWindows.execute_get,
      GraphRootWindows.family_get,side,Bool.false_eq_true,ite_false,ite_true,Nat.min_eq_left hlen]

variable (stored : GraphAdaptiveBatchSources.Stored f p)
  (hc : GraphAdaptiveBatchSources.Correct f p hm input bandL bandR stored)

theorem window_eq :
    GraphAdaptiveBatchSources.window f p hm input bandL bandR stored hc block index=
      encodedSlot (GraphPrefixProgram.fromInputs f p block input bandL bandR
        (typeLength p.L p.m p.t index.channel)) index := by
  rw [GraphAdaptiveBatchSources.window_correct,GraphAdaptiveBatchSources.pick_correct f p hm input bandL bandR stored hc,
    permuted_eq,GraphWindowCompatibility.common_prefix]

theorem extracted_row {k ell total cn co C : ℕ} (x : WindowPrefixProgram.Prepared k ell C)
    (hr : x.rareCap=WindowPrefixProgram.cap k ell total cn co)
    (labels : Vector (Fin 4) (WindowPrefixProgram.prefixLength k ell+WindowPrefixProgram.length k ell))
    (c : Fin C) :
    BinaryCell.view ((PrefixCompletionProgram.row (GraphAdaptiveBatchSources.extract x hr)
      (PrefixCompletionMatrices.prepare (GraphAdaptiveBatchSources.extract x hr)).value labels).value.output.get c)=
    BinaryCell.view ((PrefixCompletionProgram.row x.encoded
      (PrefixCompletionMatrices.prepare x.encoded).value labels).value.output.get c) := by
  cases x with
  | mk cap source => cases hr; rfl

theorem row_eq (requests : Array (Vector (Fin 4) (2*(p.L-p.m)))) (j : Fin requests.size)
    (c : Fin ((p.m+1)*f.cyclic)) :
    BinaryCell.view ((PrefixCompletionProgram.row
      (GraphAdaptiveBatchSources.source f p hm input bandL bandR stored hc block index)
      (PrefixCompletionMatrices.prepare (GraphAdaptiveBatchSources.source f p hm input bandL bandR stored hc block index)).value
      ((WindowCompletionRequests.requests (typeLength p.L p.m p.t index.channel)
        (GraphWindowCompatibility.layout p.L p.m (typeLength p.L p.m p.t index.channel) p.t index)
        requests).value[j.val]'(by simp))).value.output.get c)=
      BinaryCell.view (((WindowCompletionProgram.execute
        (encodedSlot (GraphPrefixProgram.fromInputs f p block input bandL bandR
          (typeLength p.L p.m p.t index.channel)) index)
        (permuted (GraphPrefixProgram.fromInputs f p block input bandL bandR
          (typeLength p.L p.m p.t index.channel)) index).layout requests).completed.value.requests[j.val]'(by simp)).output.get c) := by
  rw [GraphAdaptiveBatchSources.source,extracted_row,window_eq]
  simp only [WindowCompletionProgram.execute,GraphWindowCompatibility.common_layout]
  rw [PrefixCompletionProgram.execute_get]

#print axioms entry_fixed_permuted
#print axioms window_eq
#print axioms extracted_row
#print axioms row_eq

#print axioms permuted_eq
end ThinMatrix.GraphAdaptiveLegacy
