import HalfSourceAdaptiveVolume

set_option autoImplicit false
set_option maxHeartbeats 2400000

namespace ThinMatrix.HalfSourceAdaptiveControl
open HalfSourcePrefixVolume HalfSourceAdaptiveVolume

 theorem affine (a b C : ℕ) (hC : 1 ≤ C) : a*C+b ≤ C*(a+b) := by
  have h := Nat.mul_le_mul_right b hC
  nlinarith

 theorem volume (a b Z : ℕ) (hZ : 1 ≤ Z) : Z*a+b ≤ Z*(a+b) := by
  have h := Nat.mul_le_mul_right b hZ
  nlinarith

 theorem row_transform (N m C : ℕ) (hC : 1 ≤ C) :
    OppositeWindowLayer.rowControlBudget N ((m+1)*C) ≤ C*OppositeWindowLayer.rowControlBudget N (m+1) := by
  have hh := affine (112*(m+1)) (N*(6*N+16)+2+3*(48*N+26)+8+8*N+24) C hC
  simpa only [OppositeWindowLayer.rowControlBudget] using (by convert hh using 1 <;> ring)

 theorem row_permutation (N m C : ℕ) (hC : 1 ≤ C) :
    RetainedWindowPermutation.rowControlBudget N ((m+1)*C) ≤ C*RetainedWindowPermutation.rowControlBudget N (m+1) := by
  have hh := affine (40*(m+1)) (N*(6*N+16)+2+8*N+(40*N+18)+8+16) C hC
  simpa only [RetainedWindowPermutation.rowControlBudget] using (by convert hh using 1 <;> ring)

def partitionUnit (k m : ℕ) : ℕ :=
  BinaryWindowPartition.assignBudget k k+32+k*(36*(m+1)+44)+44*k+128+36*(m+1)

 theorem partition (k m C ell : ℕ) (hC : 1 ≤ C) (he : ell ≤ k) :
    RetainedRootWindows.partitionControlBudget k ((m+1)*C) ell ≤ C*3^(2*k)*partitionUnit k m := by
  have hz : 1 ≤ 3^(2*k) := Nat.one_le_pow _ _ (by omega)
  have hassign : BinaryWindowPartition.assignBudget k ell ≤ BinaryWindowPartition.assignBudget k k := by
    unfold BinaryWindowPartition.assignBudget WindowSelection.budget
    nlinarith
  cases k with
  | zero =>
    unfold RetainedRootWindows.partitionControlBudget partitionUnit
    norm_num
    unfold BinaryWindowPartition.assignBudget WindowSelection.budget
    nlinarith
  | succ k =>
    have hcoeff : 36*((m+1)*C)+44 ≤ C*(36*(m+1)+44) := by have := affine (36*(m+1)) 44 C hC; nlinarith
    have h1 := Nat.mul_le_mul_left (3^(2*(k+1))) (Nat.add_le_add_right hassign 32)
    have h2 := Nat.mul_le_mul_left ((k+1)*3^(2*(k+1))) hcoeff
    have h3 := Nat.mul_le_mul_right (BinaryWindowPartition.assignBudget (k+1) (k+1)+32) hC
    have h4 := Nat.mul_le_mul_left (3^(2*(k+1))) h3
    have h5 := Nat.mul_le_mul_right (44*(k+1)+40) (Nat.mul_le_mul hC hz)
    unfold RetainedRootWindows.partitionControlBudget BinaryWindowPartition.controlBudget partitionUnit
    nlinarith

def sourceUnit (m : ℕ) : ℕ := (m+1)*88+8*(m+1)^2+56

 theorem source (L m C : ℕ) (hC : 1 ≤ C) :
    ResidualWindowSource.controlBudget L m C ≤ C*3^(2*(L-m))*sourceUnit m := by
  have hz : 1 ≤ 3^(2*(L-m)) := Nat.one_le_pow _ _ (by omega)
  have hc := affine (40*(m+1)+8*(m+1)^2) (48*(m+1)+48) C hC
  have h1 := Nat.mul_le_mul_left (3^(2*(L-m))) hc
  have h2 := Nat.mul_le_mul_right 8 (Nat.mul_le_mul hC hz)
  unfold ResidualWindowSource.controlBudget sourceUnit
  nlinarith

def transformUnit (k m : ℕ) : ℕ :=
  (k+1)*(k*(OppositeWindowLayer.rowControlBudget (2*k) (m+1)+32)+24*k+44)+8

 theorem transform (L m C : ℕ) (hC : 1 ≤ C) :
    GraphWindowTransforms.entryControlBudget L m C ≤ C*3^(2*(L-m))*transformUnit (L-m) m := by
  let k := L-m
  have hz : 1 ≤ 3^(2*k) := Nat.one_le_pow _ _ (by omega)
  have hs := slots_le k
  have hr := row_transform (2*k) m C hC
  have hc : OppositeWindowLayer.rowControlBudget (2*k) ((m+1)*C)+32 ≤ C*(OppositeWindowLayer.rowControlBudget (2*k) (m+1)+32) := by
    have hh := Nat.mul_le_mul_right 32 hC
    nlinarith
  have h1 := Nat.mul_le_mul_left (k*3^(2*k)) hc
  have h2 := Nat.mul_le_mul_right (24*k+44) (Nat.mul_le_mul hC hz)
  have h3 := Nat.mul_le_mul hs (show k*(3^(2*k)*(OppositeWindowLayer.rowControlBudget (2*k) ((m+1)*C)+32)+16)+4+8*k+40 ≤
      C*3^(2*k)*(k*(OppositeWindowLayer.rowControlBudget (2*k) (m+1)+32)+24*k+44) by nlinarith)
  have h4 := Nat.mul_le_mul_right 8 (Nat.mul_le_mul hC hz)
  unfold GraphWindowTransforms.entryControlBudget RetainedOppositeTransform.controlBudget OppositeWindowLayer.controlBudget transformUnit
  dsimp only [k] at *
  nlinarith

def permutationUnit (k m : ℕ) : ℕ :=
  (k+1)*(128*(2*k)+80+RetainedWindowPermutation.rowControlBudget (2*k) (m+1)+32)+16

 theorem permutation (L m C : ℕ) (hC : 1 ≤ C) :
    GraphWindowPermutations.entryControlBudget L m C ≤ C*3^(2*(L-m))*permutationUnit (L-m) m := by
  let k := L-m
  have hz : 1 ≤ 3^(2*k) := Nat.one_le_pow _ _ (by omega)
  have hs := slots_le k
  have hr := row_permutation (2*k) m C hC
  have hc : RetainedWindowPermutation.rowControlBudget (2*k) ((m+1)*C)+32 ≤ C*(RetainedWindowPermutation.rowControlBudget (2*k) (m+1)+32) := by
    have hh := Nat.mul_le_mul_right 32 hC
    nlinarith
  have h1 := Nat.mul_le_mul_left (3^(2*k)) hc
  have h2 := Nat.mul_le_mul_right (128*(2*k)+80) (Nat.mul_le_mul hC hz)
  have h3 := Nat.mul_le_mul hs (show 128*(2*k)+40+(3^(2*k)*(RetainedWindowPermutation.rowControlBudget (2*k) ((m+1)*C)+32)+8)+32 ≤
      C*3^(2*k)*(128*(2*k)+80+RetainedWindowPermutation.rowControlBudget (2*k) (m+1)+32) by nlinarith)
  have h4 := Nat.mul_le_mul_right 16 (Nat.mul_le_mul hC hz)
  unfold GraphWindowPermutations.entryControlBudget RetainedWindowPermutation.controlBudget permutationUnit
  dsimp only [k] at *
  nlinarith

def denseUnit (k m cap : ℕ) : ℕ :=
  64*m+164+64*k+HalfSourceSuffixProgram.controlBudget k cap.size+
    sourceUnit m+partitionUnit k m+transformUnit k m+permutationUnit k m

theorem entry_control {L m C : ℕ} (hm : m ≤ L-m) (cap : ℕ) (hcap : 0 < cap)
    (root : RetainedResidualFamily.Entry L m C) (hC : 1 ≤ C) :
    GraphAdaptivePrefixCosts.entryControlBudget hm cap root ≤
      C*(3^(2*(L-m))*denseUnit (L-m) m cap+
        RetainedRootWindows.slots (L-m)*(m+1)*entryGroups (GraphAdaptivePrefix.length (GraphAdaptivePrefix.entry hm cap root).value) root*
          controlUnit (WindowPrefixProgram.prefixLength (L-m) (GraphAdaptivePrefix.length (GraphAdaptivePrefix.entry hm cap root).value))
            (WindowPrefixProgram.length (L-m) (GraphAdaptivePrefix.length (GraphAdaptivePrefix.entry hm cap root).value))) := by
  let ell := GraphAdaptivePrefix.length (GraphAdaptivePrefix.entry hm cap root).value
  have he : ell ≤ L-m := by
    dsimp only [ell]
    rw [GraphAdaptivePrefix.entry_length]
    exact (HalfSourceSuffixChoice.choice_bounds _ _ _ hcap).1
  have hpre := entry_prefix_control ell root hC
  have hs := source L m C hC
  have hp := partition (L-m) m C ell hC he
  have ht := transform L m C hC
  have hperm := permutation L m C hC
  have hz : 1 ≤ 3^(2*(L-m)) := Nat.one_le_pow _ _ (by omega)
  have hslots := slots_le (L-m)
  have hsetup := Nat.mul_le_mul_right (64*m+164+64*(L-m)+HalfSourceSuffixProgram.controlBudget (L-m) cap.size) (Nat.mul_le_mul hC hz)
  unfold GraphAdaptivePrefixCosts.entryControlBudget GraphAdaptivePrefixCosts.fixedControlBudget
    RetainedRootWindows.controlBudget denseUnit
  dsimp only [ell] at *
  nlinarith

#print axioms entry_control
#print axioms affine
#print axioms volume
#print axioms row_transform
#print axioms row_permutation
#print axioms partition
#print axioms source
#print axioms transform
#print axioms permutation
end ThinMatrix.HalfSourceAdaptiveControl
