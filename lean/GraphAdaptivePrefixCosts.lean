import GraphAdaptivePrefix

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! Exact counters for every selected-type entry and all family occurrences.
The ledger includes selection, window partition, full transforms, permutation
copies and retained prefix encoders. Shape-cap generation remains separate. -/
namespace ThinMatrix.GraphAdaptivePrefixCosts
open BinaryGroupedCoordinates BinaryGroupedPreparation
open GraphAdaptivePrefix
open scoped BigOperators

variable {L m C : ℕ}

def fixedBitBudget (ell : ℕ) (root : RetainedResidualFamily.Entry L m C) (A : ℕ) : ℕ :=
  RetainedRootWindows.bitBudget L m C A+GraphWindowTransforms.entryBitBudget L m C A+
  GraphWindowPermutations.entryBitBudget L m C (2^(L-m)*A)+
  GraphPrefixProgram.entryBitBudget ell (RetainedRootWindows.execute ell root).value (2^(L-m)*A)

def fixedControlBudget (ell : ℕ) (root : RetainedResidualFamily.Entry L m C) : ℕ :=
  RetainedRootWindows.controlBudget L m C ell+GraphWindowTransforms.entryControlBudget L m C+
  GraphWindowPermutations.entryControlBudget L m C+
  GraphPrefixProgram.entryControlBudget ell (RetainedRootWindows.execute ell root).value+16

theorem transformed_bound (ell : ℕ) (root : RetainedResidualFamily.Entry L m C) (A : ℕ)
    (ha : ResidualWindowSource.BoundRows root A) :
    GraphWindowPermutations.EntryBound (fixed ell root).value.transformed (2^(L-m)*A) := by
  intro slot
  change OppositeWindowLayer.Bound
    (((GraphWindowTransforms.entry (RetainedRootWindows.execute ell root).value).value.get slot).result) _
  simp only [GraphWindowTransforms.entry,tabulate_get]
  exact RetainedOppositeTransform.execute_bound _ A (RetainedRootWindows.execute_magnitude ell root A ha slot)

theorem permuted_bound (ell : ℕ) (root : RetainedResidualFamily.Entry L m C) (A : ℕ)
    (ha : ResidualWindowSource.BoundRows root A) :
    GraphPrefixProgram.EntryBound (fixed ell root).value.permuted (2^(L-m)*A) := by
  intro slot
  change OppositeWindowLayer.Bound
    (((GraphWindowPermutations.entry ell (RetainedRootWindows.execute ell root).value
      (fixed ell root).value.transformed).value.get slot).coefficients) _
  simp only [GraphWindowPermutations.entry,tabulate_get]
  exact RetainedWindowPermutation.prepare_bound _ _ _ _ _ (transformed_bound ell root A ha slot)

theorem fixed_bits (ell : ℕ) (root : RetainedResidualFamily.Entry L m C) (A : ℕ)
    (ha : ResidualWindowSource.BoundRows root A) : (fixed ell root).bitSteps ≤ fixedBitBudget ell root A := by
  have hw := RetainedRootWindows.execute_bits ell root A ha
  have ht := GraphWindowTransforms.entry_bits (RetainedRootWindows.execute ell root).value A
    (RetainedRootWindows.execute_magnitude ell root A ha)
  have hp := GraphWindowPermutations.entry_bits ell (fixed ell root).value.windows (fixed ell root).value.transformed
    (2^(L-m)*A) (transformed_bound ell root A ha)
  have he := GraphPrefixProgram.entry_bits ell (fixed ell root).value.windows (fixed ell root).value.permuted
    (2^(L-m)*A) (permuted_bound ell root A ha)
  exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hw ht) hp) he

theorem fixed_control (ell : ℕ) (root : RetainedResidualFamily.Entry L m C) :
    (fixed ell root).control ≤ fixedControlBudget ell root := by
  have hw := RetainedRootWindows.execute_control ell root
  have ht := GraphWindowTransforms.entry_control (fixed ell root).value.windows
  have hp := GraphWindowPermutations.entry_control ell (fixed ell root).value.windows (fixed ell root).value.transformed
  have he := GraphPrefixProgram.entry_control ell (fixed ell root).value.windows (fixed ell root).value.permuted
  exact Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hw ht) hp) he) 16

def entryBitBudget (hm : m ≤ L-m) (cap : ℕ) (root : RetainedResidualFamily.Entry L m C) (A : ℕ) : ℕ :=
  2*RetainedRootWindows.countBudget m+HalfSourceSuffixProgram.bitBudget (L-m) cap.size+
    fixedBitBudget (length (entry hm cap root).value) root A

def entryControlBudget (hm : m ≤ L-m) (cap : ℕ) (root : RetainedResidualFamily.Entry L m C) : ℕ :=
  (32*m+24)+HalfSourceSuffixProgram.controlBudget (L-m) cap.size+
    fixedControlBudget (length (entry hm cap root).value) root+16

theorem entry_bits (hm : m ≤ L-m) (cap : ℕ) (root : RetainedResidualFamily.Entry L m C) (A : ℕ)
    (ha : ResidualWindowSource.BoundRows root A) : (entry hm cap root).bitSteps ≤ entryBitBudget hm cap root A := by
  have hw := RetainedRootWindows.weights_bits root.channel
  have hs := HalfSourceSuffixProgram.execute_bits (L-m)
    (m/2-max (RetainedRootWindows.weights root.channel).value.1 (RetainedRootWindows.weights root.channel).value.2) cap (by omega)
  have hf := fixed_bits (length (entry hm cap root).value) root A ha
  exact Nat.add_le_add (Nat.add_le_add hw hs) hf

theorem entry_control (hm : m ≤ L-m) (cap : ℕ) (root : RetainedResidualFamily.Entry L m C) :
    (entry hm cap root).control ≤ entryControlBudget hm cap root := by
  have hw := RetainedRootWindows.weights_control root.channel
  have hs := HalfSourceSuffixProgram.execute_control (L-m)
    (m/2-max (RetainedRootWindows.weights root.channel).value.1 (RetainedRootWindows.weights root.channel).value.2) cap (by omega)
  have hf := fixed_control (length (entry hm cap root).value) root
  unfold entry entryControlBudget
  change _+_+_+16≤_
  rw [hw]
  exact Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add_left hs _) hf) 16

variable {t : ℕ}

def familyBitBudget (hm : m ≤ L-m) (cap : ℕ) (roots : RetainedResidualFamily.Family L m C t) (A : ℕ) : ℕ :=
  ∑ i, ∑ j, ∑ c, entryBitBudget hm cap (((roots.get i).get j).get c) A

def familyControlBudget (hm : m ≤ L-m) (cap : ℕ) (roots : RetainedResidualFamily.Family L m C t) : ℕ :=
  GraphPrefixProgram.sumControl (fun i => GraphPrefixProgram.sumControl (fun j => GraphPrefixProgram.sumControl (fun c =>
    entryControlBudget hm cap (((roots.get i).get j).get c))))

theorem family_bits (hm : m ≤ L-m) (cap : ℕ) (roots : RetainedResidualFamily.Family L m C t) (A : ℕ)
    (ha : GraphRootWindows.FamilyBound roots A) : (family hm cap roots).bitSteps ≤ familyBitBudget hm cap roots A := by
  apply GraphPrefixProgram.tabulate_bits_vary; intro i
  apply GraphPrefixProgram.tabulate_bits_vary; intro j
  apply GraphPrefixProgram.tabulate_bits_vary; intro c
  exact entry_bits hm cap _ A (ha i j c)

theorem family_control (hm : m ≤ L-m) (cap : ℕ) (roots : RetainedResidualFamily.Family L m C t) :
    (family hm cap roots).control ≤ familyControlBudget hm cap roots := by
  apply GraphPrefixProgram.tabulate_control_vary; intro i
  apply GraphPrefixProgram.tabulate_control_vary; intro j
  apply GraphPrefixProgram.tabulate_control_vary; intro c
  exact entry_control hm cap _

def bitBudget (hm : m ≤ L-m) (cap : ℕ) (roots : GraphResidualFamilies.Roots L m C t) (A : ℕ) : ℕ :=
  ∑ u, ∑ v, ∑ run, (familyBitBudget hm cap ((((roots.get u).get v).get run).1) A+
    familyBitBudget hm cap ((((roots.get u).get v).get run).2) A)

def controlBudget (hm : m ≤ L-m) (cap : ℕ) (roots : GraphResidualFamilies.Roots L m C t) : ℕ :=
  GraphPrefixProgram.sumControl (fun u => GraphPrefixProgram.sumControl (fun v => GraphPrefixProgram.sumControl (fun run =>
    familyControlBudget hm cap ((((roots.get u).get v).get run).1)+
    familyControlBudget hm cap ((((roots.get u).get v).get run).2)+8)))

theorem execute_bits (hm : m ≤ L-m) (cap : ℕ) (roots : GraphResidualFamilies.Roots L m C t) (A : ℕ)
    (ha : GraphRootWindows.RootBound roots A) : (execute hm cap roots).bitSteps ≤ bitBudget hm cap roots A := by
  apply GraphPrefixProgram.tabulate_bits_vary; intro u
  apply GraphPrefixProgram.tabulate_bits_vary; intro v
  apply GraphPrefixProgram.tabulate_bits_vary; intro run
  exact Nat.add_le_add (family_bits hm cap _ A (ha u v run).1) (family_bits hm cap _ A (ha u v run).2)

theorem execute_control (hm : m ≤ L-m) (cap : ℕ) (roots : GraphResidualFamilies.Roots L m C t) :
    (execute hm cap roots).control ≤ controlBudget hm cap roots := by
  apply GraphPrefixProgram.tabulate_control_vary; intro u
  apply GraphPrefixProgram.tabulate_control_vary; intro v
  apply GraphPrefixProgram.tabulate_control_vary; intro run
  exact Nat.add_le_add_right (Nat.add_le_add (family_control hm cap _) (family_control hm cap _)) 8

#print axioms transformed_bound
#print axioms permuted_bound
#print axioms fixed_bits
#print axioms fixed_control
#print axioms entry_bits
#print axioms entry_control
#print axioms family_bits
#print axioms family_control
#print axioms execute_bits
#print axioms execute_control
end ThinMatrix.GraphAdaptivePrefixCosts
