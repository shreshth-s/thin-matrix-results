import HalfSourceTargetPolynomial
import HalfSourceSourceCosts
import HalfSourceHighScheduleCost

set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace ThinMatrix.HalfSourceTargetVolume
open HalfSourceParameters
open HalfSourceAdaptiveFamilyCost (L t)
noncomputable section

 theorem band_pos (N m : ℕ) (hfit : ThinProductCosts.gridSide (L m) m ≤ N) :
    1≤TilingCosts.bandCount N (ThinMatrixBackend.tileWidth (L m) m) := by
  have ht := ThinMatrixBackend.tileWidth_pos (L m) m (OptimizedFoldedPlan.ordinaryLength_lower m)
  have hg := ThinProductCosts.gridSide_pos (L m) m (OptimizedFoldedPlan.ordinaryLength_lower m)
  exact TilingCosts.bandCount_pos N _ (by omega) ht

 theorem raw (N m : ℕ) (hm : 0 < m) (hfit : ThinProductCosts.gridSide (L m) m ≤ N) :
    (12:ℝ)^(L m)*(2:ℝ)^(L m-m)≤26624*(N:ℝ)*(m+1:ℝ)*(((4:ℝ)^m)^E) := by
  let S := TilingCosts.bandCount N (ThinMatrixBackend.tileWidth (L m) m)
  have hs : (1:ℝ)≤S := by exact_mod_cast band_pos N m hfit
  have hd : 1≤(4:ℝ)^m := one_le_pow₀ (by norm_num)
  have hraw := HalfSourceSourceCosts.rounded_raw_cost m
  have hL : Nat.ceil (c*(m:ℝ))=L m := by
    have he : c=OptimizedFoldedPlan.c := by norm_num [c,OptimizedFoldedPlan.c]
    rw [he,←OptimizedFoldedPlan.ordinaryLength_eq]
  rw [hL] at hraw
  have he : (((4:ℝ)^m)^HalfSourceSourceCosts.directSourceExponent)≤(((4:ℝ)^m)^(T+E)) :=
    Real.rpow_le_rpow_of_exponent_le hd (by linarith [HalfSourceSourceCosts.directSource_gap])
  have hbase := hraw.trans (mul_le_mul_of_nonneg_left he (by norm_num : (0:ℝ)≤64))
  have hh := HalfSourceBandVolume.transfer N m hm hfit 64 _ E (by norm_num) hbase
  have hdim : (L m+1:ℝ)≤13*(m+1:ℝ) := by
    have hx := HalfSourceRootPolynomials.ordinary_bound m
    exact_mod_cast (show L m+1≤13*(m+1) by dsimp only[L];omega)
  calc
    _ ≤(S:ℝ)*((12:ℝ)^(L m)*(2:ℝ)^(L m-m)) := by nlinarith only [mul_le_mul_of_nonneg_right hs (show 0≤(12:ℝ)^(L m)*(2:ℝ)^(L m-m) by positivity)]
    _ ≤32*(N:ℝ)*(L m+1:ℝ)*64*(((4:ℝ)^m)^E) := hh
    _ ≤32*(N:ℝ)*(13*(m+1:ℝ))*64*(((4:ℝ)^m)^E) := by gcongr
    _ = _ := by ring

 theorem small_volume (S B L m t M : ℕ)
    (hS : 1≤S) (hB : 1≤B) (hK : 1≤(GoodMapEmbedding.goodSlots L m).card)
    (hH : 1≤ResidualFamilyKeys.channelCount m t) :
    HalfSourceTargetPolynomial.volume S B L m t M≤12^L*2^(L-m)+M+
      8*B*(S^2*(GoodMapEmbedding.goodSlots L m).card^2*ResidualFamilyKeys.channelCount m t) := by
  let K := (GoodMapEmbedding.goodSlots L m).card
  let H := ResidualFamilyKeys.channelCount m t
  let F := S^2*K^2*H
  have hS2 : 1≤S^2 := one_le_pow₀ hS
  have hK2 : 1≤K^2 := one_le_pow₀ hK
  have hF : 1≤F := one_le_mul (one_le_mul hS2 hK2) hH
  have hSS : S≤S^2 := le_self_pow₀ hS (by decide)
  have hKK : K≤K^2 := le_self_pow₀ hK (by decide)
  have hsF : S≤F := by
    have hh : S^2≤S^2*(K^2*H) := Nat.le_mul_of_pos_right _ (by positivity)
    exact hSS.trans (hh.trans_eq (by dsimp[F];ring))
  have hkF : K≤F := by
    have hh : K^2≤S^2*K^2*H := by
      have ha := Nat.mul_le_mul_right (K^2) hS2
      have hb := Nat.mul_le_mul_right (S^2*K^2) hH
      nlinarith only [ha,hb]
    exact hKK.trans hh
  have hhF : H≤F := by
    have hh := Nat.mul_le_mul_right H (one_le_mul hS2 hK2)
    simpa only [one_mul,F] using hh
  have hgF : GraphOwnBandRouter.count S L m≤F := by
    have hh := Nat.mul_le_mul_right (K^2) hSS
    have ha := Nat.mul_le_mul_left (S^2*K^2) hH
    unfold GraphOwnBandRouter.count
    change S*(K*K)≤F
    dsimp[F]
    nlinarith only [hh,ha]
  have hsb := Nat.mul_le_mul_right B hsF
  have hfB := Nat.mul_le_mul_left F hB
  have hBf := Nat.mul_le_mul_left B hF
  unfold HalfSourceTargetPolynomial.volume
  change _≤12^L*2^(L-m)+M+8*B*F
  nlinarith only [hsF,hkF,hhF,hgF,hsb,hfB,hBf,hF]

 theorem volume_bound (N m B M : ℕ) (hm : 0 < m) (hB : 1≤B)
    (hfit : ThinProductCosts.gridSide (L m) m ≤ N) :
    let S := TilingCosts.bandCount N (ThinMatrixBackend.tileWidth (L m) m)
    (HalfSourceTargetPolynomial.volume S B (L m) m (t m) M:ℝ)≤
      30000*(B:ℝ)*(m+1:ℝ)*((N:ℝ)*(((4:ℝ)^m)^E)+(N:ℝ)^2*(((4:ℝ)^m)^(-G)))+
      (M:ℝ)*(((4:ℝ)^m)^q2) := by
  let S := TilingCosts.bandCount N (ThinMatrixBackend.tileWidth (L m) m)
  have hS := band_pos N m hfit
  have hK : 1≤(GoodMapEmbedding.goodSlots (L m) m).card := by
    have hc := Nat.choose_pos (OptimizedFoldedPlan.ordinaryLength_lower m)
    have hd := GoodMapEmbedding.goodSlots_density (L m) m
    change 0<(L m).choose m at hc
    omega
  have hH := HalfSourceRootFamilyCosts.channel_positive m hm
  have hv := small_volume S B (L m) m (t m) M hS hB hK hH
  have hvR : (HalfSourceTargetPolynomial.volume S B (L m) m (t m) M:ℝ)≤
      (12:ℝ)^(L m)*(2:ℝ)^(L m-m)+(M:ℝ)+8*(B:ℝ)*(HalfSourceEmptyRootCost.count N m:ℝ) := by
    exact_mod_cast hv
  have hu := raw N m hm hfit
  have hc := HalfSourceEmptyRootCost.count_bound N m hm hfit
  have hbr : (1:ℝ)≤B := by exact_mod_cast hB
  have huB : (12:ℝ)^(L m)*(2:ℝ)^(L m-m)≤26624*(B:ℝ)*(N:ℝ)*(m+1:ℝ)*(((4:ℝ)^m)^E) := by
    have hh := mul_le_mul_of_nonneg_left hbr (show 0≤26624*(N:ℝ)*(m+1:ℝ)*(((4:ℝ)^m)^E) by positivity)
    nlinarith only [hu,hh]
  have hq2 : 0≤q2 := by
    have hQ := QEnclosure.1
    norm_num [q2,theta] at *
    linarith
  have hquery : (M:ℝ)≤(M:ℝ)*(((4:ℝ)^m)^q2) := by
    exact le_mul_of_one_le_right (by positivity) (Real.one_le_rpow (one_le_pow₀ (by norm_num)) hq2)
  have hbox := mul_le_mul_of_nonneg_left hc (show 0≤8*(B:ℝ) by positivity)
  change (HalfSourceTargetPolynomial.volume S B (L m) m (t m) M:ℝ)≤_
  nlinarith only [hvR,huB,hquery,hbox,
    mul_nonneg (show 0≤(B:ℝ)*(m+1:ℝ) by positivity) (show 0≤(N:ℝ)*(((4:ℝ)^m)^E) by positivity),
    mul_nonneg (show 0≤(B:ℝ)*(m+1:ℝ) by positivity) (show 0≤(N:ℝ)^2*(((4:ℝ)^m)^(-G)) by positivity)]

#print axioms volume_bound

#print axioms band_pos
#print axioms raw
#print axioms small_volume
end
end ThinMatrix.HalfSourceTargetVolume
