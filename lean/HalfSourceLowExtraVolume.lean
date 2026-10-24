import HalfSourceLowExtraPolynomials
import HalfSourceCompletionTotal

/-! Selected LOW product/collection overhead charges only the existing
query and formation monomials. The linear channel locator is kept: its
quadratic channel count is bounded by D, with all rounding factors. -/
namespace ThinMatrix.HalfSourceLowExtraVolume
open HalfSourceParameters ResidualFamilyKeys ParameterExecution
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
noncomputable section

 theorem channel_square (m : ℕ) (hm : 0 < m) :
    (channelCount m (OptimizedFoldedPlan.channelLength m):ℝ)^2 ≤ (m+1:ℝ)^2*(4:ℝ)^m := by
  have hh := HalfSourceRootVolume.channelCount_bound m hm
  have hD : 1 ≤ (4:ℝ)^m := one_le_pow₀ (by norm_num)
  have hQ : 2*Q ≤ 1 := by linarith[QEnclosure.2]
  have hp := pow_le_pow_left₀ (Nat.cast_nonneg _) hh 2
  rw[mul_pow,←Real.rpow_mul_natCast (by positivity)] at hp
  have he : (((4:ℝ)^m)^(Q*2)) ≤ (4:ℝ)^m := by
    simpa only[Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hD (show Q*2≤1 by linarith)
  exact hp.trans (mul_le_mul_of_nonneg_left he (by positivity))

 theorem channel_size (m t : ℕ) : (channelCount m t).size ≤ 2*m+1 := by
  have hh : channelCount m t ≤ 2^(2*m) := by
    by_cases ht : t=0
    · simp only[channelCount,ht,ite_true];exact Nat.zero_le _
    · have h := (CappedSubsetList.generate_nodup (m+m) (t-1)).length_le_card
      rw[CappedSubsetList.generate_length] at h
      simpa only[channelCount,if_neg ht,Fintype.card_finset,Fintype.card_fin,←two_mul] using h
  exact (Nat.size_le_size hh).trans_eq Nat.size_pow

variable {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
  (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f)

 theorem canonical_width :
    HalfSourceLowExtraPolynomials.width f p (2^(2*p.m)) (HalfSourceLowProductCosts.rootMagnitude f p) ≤
      20*(p.L+p.m+f.cyclic.size+1) := by
  have hc := channel_size p.m p.t
  have hs := HalfSourceAdaptiveVolume.slots_le (p.L-p.m)
  have hr := size_mul (RetainedRootWindows.slots (p.L-p.m)) (2^(3*(p.L-p.m)+p.L+4*p.m))
  rw[Nat.size_pow] at hr
  have hss := (size_le_self (RetainedRootWindows.slots (p.L-p.m))).trans hs
  have hh : (HalfSourceLowProductCosts.rootMagnitude f p).size ≤ 5*p.L+4*p.m+2 := by
    unfold HalfSourceLowProductCosts.rootMagnitude
    omega
  unfold HalfSourceLowExtraPolynomials.width
  rw[Nat.size_pow]
  have ht := p.t_le
  omega

 theorem extra_rate (ht : p.t=OptimizedFoldedPlan.channelLength p.m) (hm : 0 < p.m)
    (hB : 1 ≤ CompactBlocks.blockCount n h) (W A : ℕ) :
    (HalfSourceLowCollectionCosts.extra f p W A:ℝ) ≤
      1000000000000*(HalfSourceLowExtraPolynomials.width f p W A:ℝ)^11*(p.m+1:ℝ)^2*
      ((FoldedBackendExecution.windowQuerySize n:ℝ)*CompactBlocks.blockCount n h*f.cyclic*(((4:ℝ)^p.m)^q1)+(4:ℝ)^p.m) := by
  have hH : 1 ≤ channelCount p.m p.t := by
    have hpos := OptimizedFoldedPlan.channels_pos p.m hm
    rw[ht,channelCount,if_neg (Nat.ne_of_gt hpos)]
    exact CappedSubsetList.count_pos _ _
  have he := HalfSourceLowExtraPolynomials.collection_extra f p W A hB hH
  have heR : (HalfSourceLowCollectionCosts.extra f p W A:ℝ) ≤
      1000000000000*(HalfSourceLowExtraPolynomials.width f p W A:ℝ)^11*
      ((FoldedBackendExecution.windowQuerySize n:ℝ)*CompactBlocks.blockCount n h*f.cyclic*channelCount p.m p.t+
        (channelCount p.m p.t:ℝ)^2) := by exact_mod_cast he
  have hch := HalfSourceCompletionTotal.channel_q1 p.m hm
  have hsq := channel_square p.m hm
  dsimp only[HalfSourceAdaptiveFamilyCost.t] at hch
  rw[←ht] at hch hsq
  have hpoly : (p.m+1:ℝ) ≤ (p.m+1:ℝ)^2 := le_self_pow₀ (by have := Nat.cast_nonneg (α:=ℝ) p.m;linarith) (by decide)
  have hch2 : (channelCount p.m p.t:ℝ) ≤ (p.m+1:ℝ)^2*(((4:ℝ)^p.m)^q1) :=
    hch.trans (mul_le_mul_of_nonneg_right hpoly (by positivity))
  have hsum := add_le_add (mul_le_mul_of_nonneg_left hch2
    (show 0≤(FoldedBackendExecution.windowQuerySize n:ℝ)*CompactBlocks.blockCount n h*f.cyclic by positivity)) hsq
  calc
    _ ≤ _ := heR
    _ ≤ 1000000000000*(HalfSourceLowExtraPolynomials.width f p W A:ℝ)^11*
        ((FoldedBackendExecution.windowQuerySize n:ℝ)*CompactBlocks.blockCount n h*f.cyclic*
          ((p.m+1:ℝ)^2*(((4:ℝ)^p.m)^q1))+(p.m+1:ℝ)^2*(4:ℝ)^p.m) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by ring

#print axioms channel_square
#print axioms channel_size
#print axioms canonical_width
#print axioms extra_rate
end
end ThinMatrix.HalfSourceLowExtraVolume
