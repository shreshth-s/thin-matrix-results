import HalfSourceHighGraphCost

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000

namespace ThinMatrix.HalfSourceHighBandCost
open HalfSourceParameters HalfSourceHighVolume HalfSourceHighPolynomials
noncomputable section

abbrev L (m : ℕ) := OptimizedFoldedPlan.ordinaryLength m
abbrev t (m : ℕ) := OptimizedFoldedPlan.channelLength m
abbrev bands (N m : ℕ) := TilingCosts.bandCount N (ThinMatrixBackend.tileWidth (L m) m)

theorem bands_pos (N m : ℕ) (hfit : ThinProductCosts.gridSide (L m) m ≤ N) : 1≤bands N m := by
  have hm := OptimizedFoldedPlan.ordinaryLength_lower m
  have hN := (ThinProductCosts.gridSide_pos (L m) m hm).trans_le hfit
  exact TilingCosts.bandCount_pos N _ hN (ThinMatrixBackend.tileWidth_pos (L m) m hm)

 theorem budget_bands (N m q : ℕ) (hm : 0 < m) (hq : 1 ≤ q)
    (hfit : ThinProductCosts.gridSide (L m) m ≤ N) :
    (GraphHighPreparation.budget (L m) m (t m) q (bands N m):ℝ)≤
      10^60*q*(m+1:ℝ)^7*(width (L m) m q:ℝ)^13*boxConstant*
        (32*N*(L m+1:ℝ)^5*(((4:ℝ)^m)^Ebox)+
          1024*N^2*(L m+1:ℝ)^6*(((4:ℝ)^m)^(-G))) := by
  have hb : (GraphHighPreparation.budget (L m) m (t m) q (bands N m):ℝ)≤
      10^60*q*(m+1:ℝ)^7*(width (L m) m q:ℝ)^13*
        ((bands N m:ℝ)*(HighBaseEncoder.baseCount (L m) m (t m):ℝ)+
          (bands N m:ℝ)^2*(HighBaseEncoder.baseCount (L m) m (t m):ℝ)) := by
    exact_mod_cast HalfSourceHighGraphCost.budget_polynomial (L m) m (t m) q (bands N m) hq (bands_pos N m hfit)
  have he := encoder_bands N m hm hfit
  have hp := pair_bands N m hm hfit
  have hv := add_le_add he hp
  have hc := mul_le_mul_of_nonneg_left hv
    (show 0≤(10:ℝ)^60*q*(m+1:ℝ)^7*(width (L m) m q:ℝ)^13 by positivity)
  exact hb.trans (hc.trans_eq (by ring))

/-- All actual high source encoders, pair tables and shared magnitude setup.
This uses one retained encoder per source band and every translation/degree
run, with no assumed cost domination premise. -/
 theorem actual {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f)
    (block : Fin (CompactBlocks.blockCount n h)) (input : BinaryFoldedFormation.Inputs n)
    (hL : p.L=L p.m) (ht : p.t=t p.m) (hm : 0 < p.m)
    (hfit : ThinProductCosts.gridSide p.L p.m≤p.N)
    (ids : Vector ℕ (bands p.N p.m))
    (sources : GraphRetainedHigh.Sources f p (K:=bands p.N p.m))
    (hc : GraphRetainedHigh.Correct f p block input ids sources) :
    ((GraphHighPreparation.execute f p sources).operations:ℝ)≤
      10^60*f.cyclic*(p.m+1:ℝ)^7*(width (L p.m) p.m f.cyclic:ℝ)^13*boxConstant*
        (32*p.N*(L p.m+1:ℝ)^5*(((4:ℝ)^p.m)^Ebox)+
          1024*p.N^2*(L p.m+1:ℝ)^6*(((4:ℝ)^p.m)^(-G))) := by
  have hh : ((GraphHighPreparation.execute f p sources).operations:ℝ)≤
      (GraphHighPreparation.budget p.L p.m p.t f.cyclic (bands p.N p.m):ℝ) := by
    exact_mod_cast GraphHighPreparation.execute_work f p block input ids sources hc
  apply hh.trans
  rw [hL,ht]
  exact budget_bands p.N p.m f.cyclic hm (Nat.one_le_of_lt f.cyclic_pos) (by simpa only [hL] using hfit)

#print axioms bands_pos
#print axioms budget_bands
#print axioms actual
end
end ThinMatrix.HalfSourceHighBandCost
