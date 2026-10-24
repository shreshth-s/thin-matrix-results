import HalfSourceRootPolynomials

/-! Actual root/key setup through the shared-band Eroot ledger term.
The q factor is retained once and all fixed polynomial factors are explicit. -/
namespace ThinMatrix.HalfSourceRootSetupCost
open HalfSourceParameters HalfSourceRootFamilyCosts HalfSourceRootPolynomials
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
attribute [local irreducible] GoodMapEmbedding.goodSlots OptimizedFoldedPlan.ordinaryLength

def keyPolynomial (L m : ℕ) : ℕ := ResidualFamilyKeys.decodeBudget L+40+8+(2*m+1)*(16*m+32)+4+2+8

theorem keys (L m t G : ℕ) (hG : 1≤G) (ht : 1≤ResidualFamilyKeys.channelCount m t) :
    ResidualFamilyKeys.prepareBudget L m t G≤G^2*ResidualFamilyKeys.channelCount m t*keyPolynomial L m := by
  let H := ResidualFamilyKeys.channelCount m t
  have hb : 1≤G^2*H := one_le_mul (Nat.one_le_pow 2 G hG) ht
  have hG' : G≤G^2*H := by nlinarith only [Nat.mul_le_mul_left (G*G) ht,hG]
  have hH : H≤G^2*H := by nlinarith only [Nat.mul_le_mul_right H (Nat.one_le_pow 2 G hG)]
  have h0 := Nat.mul_le_mul_right (ResidualFamilyKeys.decodeBudget L+40) hG'
  have h1 := Nat.mul_le_mul_right ((2*m+1)*(16*m+32)+2) hH
  have h2 := Nat.mul_le_mul_right 20 hb
  unfold ResidualFamilyKeys.prepareBudget keyPolynomial
  change G*(ResidualFamilyKeys.decodeBudget L+40)+8+(2*m+1)*(16*m+32)*H+4+2*H+8≤_
  nlinarith only [h0,h1,h2]

theorem key_polynomial (m : ℕ) : keyPolynomial (OptimizedFoldedPlan.ordinaryLength m) m≤1000000*(m+1)^3 := by
  have hL := ordinary_bound m
  let W := m+1
  have hm : m≤W := by dsimp[W];omega
  have hW : 1≤W := by dsimp[W];omega
  have hupper : keyPolynomial (OptimizedFoldedPlan.ordinaryLength m) m≤
      4*(12*W)^2+20*(12*W)+4+40+8+(2*W+1)*(16*W+32)+4+2+8 := by
    unfold keyPolynomial ResidualFamilyKeys.decodeBudget
    gcongr
  have h1 : W≤W^3 := le_self_pow₀ hW (by decide)
  have h2 : W^2≤W^3 := Nat.pow_le_pow_right hW (by decide)
  have h0 : 1≤W^3 := Nat.one_le_pow 3 W hW
  change _≤1000000*W^3
  nlinarith only [hupper,h1,h2,h0]

def budget (m q : ℕ) : ℕ :=
  let L := OptimizedFoldedPlan.ordinaryLength m
  let t := OptimizedFoldedPlan.channelLength m
  let G := (GoodMapEmbedding.goodSlots L m).card
  ResidualFamilyKeys.prepareBudget L m t G+
    GraphResidualFamilies.bitBudget L m q t G (2^(L+m))+
    GraphResidualFamilies.controlBudget L m q t G

theorem budget_finite (m q : ℕ) (hm : 0 < m) (hq : 1≤q) :
    budget m q≤200000000000000000000*HalfSourceActualVolumes.roots m*q*(m+1)^12 := by
  let L := OptimizedFoldedPlan.ordinaryLength m
  let t := OptimizedFoldedPlan.channelLength m
  let G := (GoodMapEmbedding.goodSlots L m).card
  have hG : 1≤G := by
    have hc := Nat.choose_pos (OptimizedFoldedPlan.ordinaryLength_lower m)
    have hd := GoodMapEmbedding.goodSlots_density L m
    change 1≤(GoodMapEmbedding.goodSlots L m).card
    change 0<L.choose m at hc
    omega
  have ht := channel_positive m hm
  have hk := keys L m t G hG ht
  have hb := actual_graph m q (2^(L+m)) hm hq
  have hp := source_polynomial m
  have hkp := key_polynomial m
  have hroots : G^2*ResidualFamilyKeys.channelCount m t≤HalfSourceActualVolumes.roots m*q := by
    rw [HalfSourceActualVolumes.roots_eq]
    have hpow : 1≤3^(2*(L-m)+m)*q := one_le_mul (Nat.one_le_pow _ _ (by decide)) hq
    have h := Nat.mul_le_mul_left (G^2*ResidualFamilyKeys.channelCount m t) hpow
    simpa only [one_mul,mul_one,mul_assoc,G,L,t] using h
  have hk' : ResidualFamilyKeys.prepareBudget L m t G≤HalfSourceActualVolumes.roots m*q*(1000000*(m+1)^3) :=
    hk.trans (Nat.mul_le_mul hroots hkp)
  have hb' := hb.trans (Nat.mul_le_mul_left (HalfSourceActualVolumes.roots m*q) hp)
  have hpow : (m+1)^3≤(m+1)^12 := Nat.pow_le_pow_right (by omega) (by decide)
  have hsmall := Nat.mul_le_mul_left (HalfSourceActualVolumes.roots m*q*1000000) hpow
  unfold budget
  change ResidualFamilyKeys.prepareBudget L m t G+_+_≤_
  nlinarith only [hk',hb',hsmall]

theorem budget_real (m q : ℕ) (hm : 0 < m) (hq : 1≤q) :
    (budget m q:ℝ)≤(200000000000000000000*HalfSourceRootVolume.rootConstant)*(q:ℝ)*(m+1:ℝ)^13*
      (((4:ℝ)^m)^(T+Eroot)) := by
  have hf : (budget m q:ℝ)≤200000000000000000000*(HalfSourceActualVolumes.roots m:ℝ)*(q:ℝ)*(m+1:ℝ)^12 := by
    exact_mod_cast budget_finite m q hm hq
  have hr := HalfSourceActualVolumes.roots_bound m hm
  calc
    _ ≤200000000000000000000*(HalfSourceActualVolumes.roots m:ℝ)*(q:ℝ)*(m+1:ℝ)^12 := hf
    _ ≤200000000000000000000*(HalfSourceRootVolume.rootConstant*(m+1:ℝ)*((4:ℝ)^m)^(T+Eroot))*(q:ℝ)*(m+1:ℝ)^12 := by gcongr
    _ = _ := by ring

theorem budget_bands (N m q : ℕ) (hm : 0 < m) (hq : 1≤q)
    (hfit : ThinProductCosts.gridSide (OptimizedFoldedPlan.ordinaryLength m) m≤N) :
    (TilingCosts.bandCount N (ThinMatrixBackend.tileWidth (OptimizedFoldedPlan.ordinaryLength m) m):ℝ)*(budget m q:ℝ)≤
      (1000000000000000000000000*HalfSourceRootVolume.rootConstant)*(q:ℝ)*(N:ℝ)*(m+1:ℝ)^14*
        (((4:ℝ)^m)^Eroot) := by
  have hr0 : 0≤HalfSourceRootVolume.rootConstant := by unfold HalfSourceRootVolume.rootConstant;positivity
  have h := HalfSourceBandVolume.transfer N m hm hfit _ _ _
    (show 0≤(200000000000000000000*HalfSourceRootVolume.rootConstant)*(q:ℝ)*(m+1:ℝ)^13 by unfold HalfSourceRootVolume.rootConstant;positivity)
    (budget_real m q hm hq)
  have hL : (OptimizedFoldedPlan.ordinaryLength m+1:ℝ)≤13*(m+1:ℝ) := by
    have hl : (OptimizedFoldedPlan.ordinaryLength m:ℝ)≤12*(m+1:ℝ) := by exact_mod_cast ordinary_bound m
    have hn : (0:ℝ)≤ m := Nat.cast_nonneg m
    linarith
  calc
    _ ≤32*(N:ℝ)*(OptimizedFoldedPlan.ordinaryLength m+1:ℝ)*
      ((200000000000000000000*HalfSourceRootVolume.rootConstant)*(q:ℝ)*(m+1:ℝ)^13)*((4:ℝ)^m)^Eroot := h
    _ ≤32*(N:ℝ)*(13*(m+1:ℝ))*
      ((200000000000000000000*HalfSourceRootVolume.rootConstant)*(q:ℝ)*(m+1:ℝ)^13)*((4:ℝ)^m)^Eroot := by gcongr
    _ = (83200000000000000000000*HalfSourceRootVolume.rootConstant)*(q:ℝ)*(N:ℝ)*(m+1:ℝ)^14*((4:ℝ)^m)^Eroot := by ring
    _ ≤ _ := by gcongr;norm_num

#print axioms keys
#print axioms key_polynomial
#print axioms budget_finite
#print axioms budget_real
#print axioms budget_bands
end
end ThinMatrix.HalfSourceRootSetupCost
