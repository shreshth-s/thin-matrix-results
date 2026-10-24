import HalfSourceControllerWidths
import AlignedAPSPCosts

/-! Exact-half controller bookkeeping bound, including candidate scans,
incidences and restarts for the actual new rounded block program. -/
namespace ThinMatrix.HalfSourceControllerBudget
open HalfSourceBatchFit HalfSourcePrimeParameters
open AlignedAPSPCosts.ControllerCosts
open EndToEndAPSP Filter Asymptotics
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
attribute [local irreducible] HalfSourceBatchFit.block
noncomputable section
theorem computed_referenceControllerBudget_le (R depth n : ℕ) (hn : 3 ≤ n) (hdepth : depth ≤ R) :
    (referenceControllerBudget n (block n) (computedPool n).card
      depth (2*n).size:ℝ) ≤
      referenceControllerConstant R*(Real.log (n:ℝ))^5*(n:ℝ)^(3-(b-eta)) := by
  let P := (computedPool n).card
  let I := incidenceSize n (block n)
  let logn := Real.log (n:ℝ)
  let Cs : ℝ := 2+1/Real.log 2
  have hl : 1 ≤ logn := PhaseGeometry.one_le_log_nat n hn
  have hl0 : 0 ≤ logn := by linarith
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast (show 1≤n by omega)
  have hnpos : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have heta := (show 0 ≤ eta by norm_num [eta,b,bNumerator,bDenominator,HalfSourceBatchFit.R])
  have hb : b ≤ 1 := by norm_num [b,bNumerator,bDenominator]
  have hspos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hCs : 0 ≤ Cs := by dsimp [Cs]; positivity
  have hbp := TilingCosts.bandCount_pos n (block n) (by omega) (block_pos n)
  have hblocks : 1 ≤ blocks n := by
    simpa only [blocks,CompactBlocks.blockCount,TilingCosts.bandCount] using Nat.succ_le_of_lt hbp
  have hIeq : I=3*n^2*blocks n := by
    dsimp [I,incidenceSize,blocks]
    ring
  have hinc : n^2 ≤ I := by rw[hIeq];nlinarith
  have hfinite := referenceControllerBudget_factor n (block n) P depth (2*n).size R hinc hdepth
  have hfiniteR : (referenceControllerBudget n (block n) P depth (2*n).size:ℝ) ≤
      (((2*n).size:ℝ)*(8*(R:ℝ)+11)+16)*((P:ℝ)+1)*((I:ℝ)+1) := by exact_mod_cast hfinite
  have hpool : (P:ℝ) ≤ 8192*logn^4*(n:ℝ)^eta := by
    have hp := HalfSourceComputedCosts.candidate_bound n hn
    rw [←HalfSourceBatchGeometry.witness_bridge.2.1] at hp
    exact (show (P:ℝ) ≤ (PrimePool.candidates (scale n)).card by
      exact_mod_cast Finset.card_le_card (HalfSourceBackendAggregation.pool_subset n)).trans hp
  have hnpow : 1 ≤ (n:ℝ)^eta := Real.one_le_rpow hn1 heta
  have hbase : 1 ≤ logn^4*(n:ℝ)^eta := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hl) hnpow
  have hP : (P:ℝ)+1 ≤ 8193*logn^4*(n:ℝ)^eta := by
    change (P:ℝ) ≤ 8192*logn^4*(n:ℝ)^eta at hpool
    nlinarith
  have hquery := HalfSourceBatchGeometry.blocks_upper n (by omega)
  have hI : (I:ℝ)+1 ≤ 7*(n:ℝ)^(3-b) := by
    have hI' : (I:ℝ) ≤ 6*(n:ℝ)^(3-b) := by
      rw[hIeq,Nat.cast_mul,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_pow]
      calc
        _ ≤ 3*(n:ℝ)^2*(2*(n:ℝ)^(1-b)) := mul_le_mul_of_nonneg_left hquery (by positivity)
        _ = _ := by rw [show (3:ℝ)-b=2+(1-b) by ring,Real.rpow_add hnpos,Real.rpow_two];ring
    have hpow : 1 ≤ (n:ℝ)^(3-b) := Real.one_le_rpow hn1 (by linarith)
    linarith
  have hstages := stages_le_log n hn
  have hround : ((2*n).size:ℝ)*(8*(R:ℝ)+11)+16 ≤
      (Cs*(8*(R:ℝ)+11)+16)*logn := by
    have hm := mul_le_mul_of_nonneg_right hstages (show 0 ≤ 8*(R:ℝ)+11 by positivity)
    change ((2*n).size:ℝ) ≤ Cs*logn at hstages
    nlinarith
  calc
    _ ≤ (((2*n).size:ℝ)*(8*(R:ℝ)+11)+16)*((P:ℝ)+1)*((I:ℝ)+1) := hfiniteR
    _ ≤ ((Cs*(8*(R:ℝ)+11)+16)*logn)*(8193*logn^4*(n:ℝ)^eta)*(7*(n:ℝ)^(3-b)) := by gcongr
    _ = referenceControllerConstant R*logn^5*(n:ℝ)^(3-(b-eta)) := by
      rw [show 3-(b-eta)=eta+(3-b) by ring, Real.rpow_add hnpos]
      dsimp [referenceControllerConstant,Cs]
      ring

#print axioms computed_referenceControllerBudget_le
end
end ThinMatrix.HalfSourceControllerBudget
