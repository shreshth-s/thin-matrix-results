import HalfSourceSuffixProgram
import GraphBandSharing

set_option autoImplicit false
set_option maxHeartbeats 1800000

/-! Channel-dependent suffix selection begins before window partitioning.
Each selected length is used consistently for its partition, permutation and
prefix encoder. This module retains all roots externally and every generated
window/transform/permutation/encoder record internally. The common support
cap is public shape input, so constructing that cap is charged separately. -/
namespace ThinMatrix.GraphAdaptivePrefix
open GoodMapEmbedding BinaryGroupedCoordinates BinaryGroupedPreparation
open ExactHalfSourcePlan ResidualFamilyKeys
open scoped BigOperators

structure FixedEntry (L m C ell : ℕ) where
  windows : RetainedRootWindows.Prepared L m C
  transformed : GraphWindowTransforms.Entry L m C
  permuted : GraphWindowPermutations.Entry L m C
  encoded : GraphPrefixProgram.Entry L m C ell

def fixed {L m C : ℕ} (ell : ℕ) (root : RetainedResidualFamily.Entry L m C) : Run (FixedEntry L m C ell) :=
  let windows := RetainedRootWindows.execute ell root
  let transformed := GraphWindowTransforms.entry windows.value
  let permuted := GraphWindowPermutations.entry ell windows.value transformed.value
  let encoded := GraphPrefixProgram.entry ell windows.value permuted.value
  ⟨⟨windows.value,transformed.value,permuted.value,encoded.value⟩,
    windows.bitSteps+transformed.bitSteps+permuted.bitSteps+encoded.bitSteps,
    windows.control+transformed.control+permuted.control+encoded.control+16⟩

structure Entry (L m C : ℕ) where
  weights : ℕ×ℕ
  selection : HalfSourcePascal.History (L-m) (L-m) × Vector Bool (L-m+1) × ℕ
  prepared : FixedEntry L m C selection.2.2

def entry {L m C : ℕ} (hm : m ≤ L-m) (cap : ℕ) (root : RetainedResidualFamily.Entry L m C) : Run (Entry L m C) :=
  let weights := RetainedRootWindows.weights root.channel
  let selection := HalfSourceSuffixProgram.execute (L-m) (m/2-max weights.value.1 weights.value.2) cap (by omega)
  let prepared := fixed selection.value.2.2 root
  ⟨⟨weights.value,selection.value,prepared.value⟩,
    weights.bitSteps+selection.bitSteps+prepared.bitSteps,
    weights.control+selection.control+prepared.control+16⟩

def length {L m C : ℕ} (e : Entry L m C) : ℕ := e.selection.2.2

theorem entry_length {L m C : ℕ} (hm : m ≤ L-m) (cap : ℕ) (root : RetainedResidualFamily.Entry L m C) :
    length (entry hm cap root).value = HalfSourceSuffixChoice.choose (L-m)
      (m/2-max (RetainedRootWindows.weights root.channel).value.1 (RetainedRootWindows.weights root.channel).value.2) cap := by
  simp only [length,entry,HalfSourceSuffixProgram.execute_value]

theorem entry_optimal_length {L m C : ℕ} (hm : m ≤ L-m) (root : RetainedResidualFamily.Entry L m C) :
    length (entry hm (HalfSourceSuffixChoice.limit m (L-m)) root).value =
      HalfSourceSuffixChoice.forType L m (RetainedRootWindows.weights root.channel).value.1
        (RetainedRootWindows.weights root.channel).value.2 := entry_length hm _ root

theorem entry_windows {L m C : ℕ} (hm : m ≤ L-m) (cap : ℕ) (root : RetainedResidualFamily.Entry L m C) :
    (entry hm cap root).value.prepared.windows=
      (RetainedRootWindows.execute (length (entry hm cap root).value) root).value := rfl

theorem entry_transformed {L m C : ℕ} (hm : m ≤ L-m) (cap : ℕ) (root : RetainedResidualFamily.Entry L m C) :
    (entry hm cap root).value.prepared.transformed=
      (GraphWindowTransforms.entry (entry hm cap root).value.prepared.windows).value := rfl

theorem entry_permuted {L m C : ℕ} (hm : m ≤ L-m) (cap : ℕ) (root : RetainedResidualFamily.Entry L m C) :
    (entry hm cap root).value.prepared.permuted=
      (GraphWindowPermutations.entry (length (entry hm cap root).value)
        (entry hm cap root).value.prepared.windows (entry hm cap root).value.prepared.transformed).value := rfl

theorem entry_encoded {L m C : ℕ} (hm : m ≤ L-m) (cap : ℕ) (root : RetainedResidualFamily.Entry L m C) :
    (entry hm cap root).value.prepared.encoded=
      (GraphPrefixProgram.entry (length (entry hm cap root).value)
        (entry hm cap root).value.prepared.windows (entry hm cap root).value.prepared.permuted).value := rfl

theorem entry_support_fit {L m C : ℕ} (hm : m ≤ L-m) (root : RetainedResidualFamily.Entry L m C) :
    let e := (entry hm (HalfSourceSuffixChoice.limit m (L-m)) root).value
    length e ≤ L-m ∧ CappedSubsetList.count (length e)
      (WindowPrefixProgram.cap (L-m) (length e) (m/2) e.weights.1 e.weights.2) ≤ HalfSourceSuffixChoice.limit m (L-m) := by
  dsimp only
  rw [entry_optimal_length]
  exact HalfSourceSuffixChoice.forType_fit L m _ _

abbrev Family (L m C t : ℕ) := Vector (Vector (Vector (Entry L m C)
  (channelCount m t)) (goodSlots L m).card) (goodSlots L m).card
abbrev Results (L m C t : ℕ) := Vector (Vector (Vector (Family L m C t × Family L m C t)
  (2*m+1)) (J m)) (J m)

def family {L m C t : ℕ} (hm : m ≤ L-m) (cap : ℕ) (roots : RetainedResidualFamily.Family L m C t) : Run (Family L m C t) :=
  tabulate roots (fun i => tabulate (roots.get i) (fun j => tabulate ((roots.get i).get j)
    (fun c => entry hm cap (((roots.get i).get j).get c))))

@[simp] theorem family_get {L m C t : ℕ} (hm : m ≤ L-m) (cap : ℕ) (roots : RetainedResidualFamily.Family L m C t)
    (i j : Fin (goodSlots L m).card) (c : Fin (channelCount m t)) :
    (((family hm cap roots).value.get i).get j).get c=(entry hm cap (((roots.get i).get j).get c)).value := by
  simp only [family,tabulate_get]

def execute {L m C t : ℕ} (hm : m ≤ L-m) (cap : ℕ) (roots : GraphResidualFamilies.Roots L m C t) : Run (Results L m C t) :=
  tabulate roots (fun u => tabulate (roots.get u) (fun v => tabulate ((roots.get u).get v) (fun run =>
    let a := family hm cap ((((roots.get u).get v).get run).1)
    let b := family hm cap ((((roots.get u).get v).get run).2)
    ⟨(a.value,b.value),a.bitSteps+b.bitSteps,a.control+b.control+8⟩)))

@[simp] theorem execute_get {L m C t : ℕ} (hm : m ≤ L-m) (cap : ℕ) (roots : GraphResidualFamilies.Roots L m C t)
    (u v : Fin (J m)) (run : Fin (2*m+1)) :
    (((execute hm cap roots).value.get u).get v).get run=
      ((family hm cap ((((roots.get u).get v).get run).1)).value,
       (family hm cap ((((roots.get u).get v).get run).2)).value) := by
  simp only [execute,tabulate_get]

structure Prepared {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : ℕ) where
  roots : GraphResidualFamilies.Prepared f p block
  encoded : Run (Results p.L p.m f.cyclic p.t)

def fromInputs {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (hm : p.m ≤ p.L-p.m)
    (block : Fin (CompactBlocks.blockCount n h)) (input : BinaryFoldedFormation.Inputs n)
    (bandL bandR cap : ℕ) : Prepared f p block :=
  let roots := GraphResidualFamilies.fromInputs f p block input bandL bandR
  ⟨roots,execute hm cap roots.roots.value⟩

theorem left_independent {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (hm : p.m ≤ p.L-p.m)
    (block : Fin (CompactBlocks.blockCount n h)) (input : BinaryFoldedFormation.Inputs n)
    (a b₁ b₂ cap : ℕ) (u v : Fin (J p.m)) (run : Fin (2*p.m+1)) :
    ((((fromInputs f p hm block input a b₁ cap).encoded.value.get u).get v).get run).1=
      ((((fromInputs f p hm block input a b₂ cap).encoded.value.get u).get v).get run).1 := by
  simp only [fromInputs,execute_get]
  rw [GraphBandSharing.roots_left_independent f p block input a b₁ b₂ u v run]

theorem right_independent {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (hm : p.m ≤ p.L-p.m)
    (block : Fin (CompactBlocks.blockCount n h)) (input : BinaryFoldedFormation.Inputs n)
    (a₁ a₂ b cap : ℕ) (u v : Fin (J p.m)) (run : Fin (2*p.m+1)) :
    ((((fromInputs f p hm block input a₁ b cap).encoded.value.get u).get v).get run).2=
      ((((fromInputs f p hm block input a₂ b cap).encoded.value.get u).get v).get run).2 := by
  simp only [fromInputs,execute_get]
  rw [GraphBandSharing.roots_right_independent f p block input a₁ a₂ b u v run]

#print axioms entry_length
#print axioms entry_optimal_length
#print axioms entry_windows
#print axioms entry_transformed
#print axioms entry_permuted
#print axioms entry_encoded
#print axioms entry_support_fit
#print axioms family_get
#print axioms execute_get
#print axioms left_independent
#print axioms right_independent
end ThinMatrix.GraphAdaptivePrefix
