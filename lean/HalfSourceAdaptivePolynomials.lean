import HalfSourceAdaptiveFamilyCost
import HalfSourceRootPolynomials

/-! Explicit fixed-degree overhead for the adaptive family, including the
binary Pascal selector, control actions and coefficient/address bit widths. -/
namespace ThinMatrix.HalfSourceAdaptivePolynomials
open HalfSourceAdaptiveVolume HalfSourceAdaptiveFamilyCost
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
set_option linter.unnecessarySeqFocus false

theorem size_le (m : ℕ) : m.size≤ m := Nat.size_le.mpr (Nat.lt_two_pow_self)

theorem count_bound (m P : ℕ) (hP : 1≤P) (hm : m+1≤P) :
    RetainedRootWindows.countBudget m≤4000*P^3 := by
  have hsize : m.size+1≤P := (Nat.add_le_add_right (size_le m) 1).trans hm
  have hm0 : m≤P := by omega
  have hbound : RetainedRootWindows.countBudget m≤P*(8*(100*(2*P)^2)+4)+1+8*P^2 := by
    unfold RetainedRootWindows.countBudget BackendScalarBits.backendScalarUnit BackendScalarBits.scalarUnit
    gcongr <;> omega
  have h1 : P≤P^3 := le_self_pow₀ hP (by decide)
  have h2 : P^2≤P^3 := Nat.pow_le_pow_right hP (by decide)
  have h0 : 1≤P^3 := Nat.one_le_pow _ _ hP
  nlinarith only [hbound,h1,h2,h0]

theorem address_bound (k P : ℕ) (hP : 1≤P) (hk : k+1≤P) :
    BinaryGroupedCoordinates.addressBudget (2*k)≤200000*P^3 := by
  have hb : BinaryGroupedCoordinates.addressBudget (2*k)≤2*P*(2*(8*(100*(7*P)^2)))+8*(7*P)^2+16 := by
    unfold BinaryGroupedCoordinates.addressBudget BackendScalarBits.backendScalarUnit BackendScalarBits.scalarUnit
    gcongr <;> omega
  have h2 : P^2≤P^3 := Nat.pow_le_pow_right hP (by decide)
  have h0 : 1≤P^3 := Nat.one_le_pow _ _ hP
  nlinarith only [hb,h2,h0]

theorem selector_bound (k cap P : ℕ) (hP : 1≤P) (hk : k+1≤P) (hc : cap.size+1≤P) :
    HalfSourceSuffixProgram.bitBudget k cap.size≤100000*P^5 := by
  have hb : HalfSourceSuffixProgram.bitBudget k cap.size≤P*P*(8*(100*(2*P)^2))+P*(4224*(P*P+2)^2+8*(100*(3*P)^2)) := by
    unfold HalfSourceSuffixProgram.bitBudget HalfSourceSuffixProgram.testBudget HalfSourceSuffixProgram.radiusBudget
      BackendScalarBits.backendScalarUnit BackendScalarBits.scalarUnit
    gcongr <;> omega
  have h1 : P≤P^5 := le_self_pow₀ hP (by decide)
  have h3 : P^3≤P^5 := Nat.pow_le_pow_right hP (by decide)
  have h4 : P^4≤P^5 := Nat.pow_le_pow_right hP (by decide)
  nlinarith only [hb,h1,h3,h4]

theorem dense_bits_bound (k m cap W P : ℕ) (hP : 1≤P)
    (hk : k+2≤P) (hm : m+1≤P) (hc : cap.size+1≤P) (hW : W+1≤P) :
    denseBitUnit k m cap W≤2000000*P^5 := by
  have hk1 : k+1≤P := by omega
  have hk0 : k≤P := by omega
  have hcount := count_bound m P hP hm
  have had := address_bound k P hP hk1
  have hsel := selector_bound k cap P hP hk1 hc
  have hscalar : BackendScalarBits.backendScalarUnit W≤800*P^2 := by
    unfold BackendScalarBits.backendScalarUnit BackendScalarBits.scalarUnit
    calc
      _ =800*(W+1)^2 := by ring
      _ ≤ _ := by gcongr
  have hb : denseBitUnit k m cap W≤4*(4000*P^3)+100000*P^5+
    P*P*(800*P^2)+P*P*(3*(200000*P^3)+P*(5*(800*P^2)))+
    P*(200000*P^3+P*(800*P^2)) := by
    unfold denseBitUnit
    gcongr
  have h3 : P^3≤P^5 := Nat.pow_le_pow_right hP (by decide)
  have h4 : P^4≤P^5 := Nat.pow_le_pow_right hP (by decide)
  nlinarith only [hb,h3,h4]

theorem dense_control_bound (k m cap P : ℕ) (hP : 1≤P)
    (hk : k+1≤P) (hm : m+1≤P) (hc : cap.size≤P) :
    HalfSourceAdaptiveControl.denseUnit k m cap≤10000*P^4 := by
  have hk0 : k≤P := by omega
  have hm0 : m≤P := by omega
  have hb : HalfSourceAdaptiveControl.denseUnit k m cap≤
    64*P+164+64*P+
    (P*(64*P+16)+(8*P+3)+(P*(8*P+64)+8)+(16*P+8)+16)+
    (P*88+8*P^2+56)+
    ((2*P)*(6*(2*P)+16)+2+(P*(14*P+7)+6*P+12)+8*P+6+32+P*(36*P+44)+44*P+128+36*P)+
    (P*(P*((2*P)*(6*(2*P)+16)+2+3*(48*(2*P)+26)+(P*112+8)+8*(2*P)+24+32)+24*P+44)+8)+
    (P*(128*(2*P)+80+((2*P)*(6*(2*P)+16)+2+8*(2*P)+(40*(2*P)+18)+(40*P+8)+16)+32)+16) := by
    unfold HalfSourceAdaptiveControl.denseUnit HalfSourceAdaptiveControl.sourceUnit HalfSourceAdaptiveControl.partitionUnit
      HalfSourceAdaptiveControl.transformUnit HalfSourceAdaptiveControl.permutationUnit
      HalfSourceSuffixProgram.controlBudget BinaryWindowPartition.assignBudget WindowSelection.budget
      OppositeWindowLayer.rowControlBudget RetainedWindowPermutation.rowControlBudget
    simp only [add_assoc]
    gcongr
  have h0 : 1≤P^4 := Nat.one_le_pow _ _ hP
  have h1 : P≤P^4 := le_self_pow₀ hP (by decide)
  have h2 : P^2≤P^4 := Nat.pow_le_pow_right hP (by decide)
  have h3 : P^3≤P^4 := Nat.pow_le_pow_right hP (by decide)
  nlinarith only [hb,h0,h1,h2,h3]

theorem unit_bound (k m cap A P : ℕ) (hP : 1≤P) (hk : k+2≤P) (hm : m+1≤P)
    (hc : cap.size+1≤P) (hW : width k A+1≤P) : unit k m cap A+120≤3000000*P^5 := by
  have hb := dense_bits_bound k m cap (width k A) P hP hk hm hc hW
  have hct := dense_control_bound k m cap P hP (by omega) hm (by omega)
  have hextra : (k+1)*(m+1)*(110000*(width k A+1)^3)≤110000*P^5 := by
    calc
      _ ≤P*P*(110000*P^3) := by gcongr <;> omega
      _ = _ := by ring
  have h4 : P^4≤P^5 := Nat.pow_le_pow_right hP (by decide)
  have h0 : 1≤P^5 := Nat.one_le_pow _ _ hP
  unfold unit
  nlinarith only [hb,hct,hextra,h4,h0]

theorem canonical_unit (m : ℕ) :
    unit (OptimizedFoldedPlan.ordinaryLength m-m) m
      (HalfSourceSuffixChoice.limit m (OptimizedFoldedPlan.ordinaryLength m-m))
      (2^(OptimizedFoldedPlan.ordinaryLength m+4*m))+120≤10000000000000000*(m+1)^5 := by
  let L := OptimizedFoldedPlan.ordinaryLength m
  let W := m+1
  have hW : 1≤W := by dsimp[W];omega
  have hL : L≤12*W := HalfSourceRootPolynomials.ordinary_bound m
  have hk : L-m+2≤54*W := by dsimp[W] at *;omega
  have hm : m+1≤54*W := by dsimp[W];omega
  have hc := HalfSourceAdaptiveWidths.cap_size m (L-m)
  have hs := size_le (L-m)
  have hc' : (HalfSourceSuffixChoice.limit m (L-m)).size+1≤54*W := by dsimp[W] at *;omega
  have hwidth : width (L-m) (2^(L+4*m))+1≤54*W := by
    unfold width
    rw[Nat.size_pow]
    dsimp[W] at *
    omega
  have hu := unit_bound (L-m) m (HalfSourceSuffixChoice.limit m (L-m)) (2^(L+4*m)) (54*W) (by omega) hk hm hc' hwidth
  calc
    _ ≤3000000*(54*W)^5 := hu
    _ = (3000000*54^5)*W^5 := by ring
    _ ≤ _ := by dsimp[W];gcongr;norm_num

#print axioms count_bound
#print axioms address_bound
#print axioms selector_bound
#print axioms dense_bits_bound
#print axioms dense_control_bound
#print axioms unit_bound
#print axioms canonical_unit
end ThinMatrix.HalfSourceAdaptivePolynomials
