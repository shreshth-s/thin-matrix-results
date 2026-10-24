import SelectedHighQueries
import HalfSourceHighPolynomials
import HalfSourceParameters
import HalfSourceRootPolynomials
import BinaryBackendCosts

/-! Binary scalar HIGH reads retain the exact channel-subset count. Only the
requested cyclic coefficient is read; all q coefficients are still priced
in HIGH preprocessing. -/
namespace ThinMatrix.HalfSourceHighQueryCost
open HalfSourceParameters
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
noncomputable section

def table (L m q : ℕ) := CroppedHighQueries.tableMagnitude L q (2^(L+m))
def width (L m q : ℕ) := L+m+q.size+10

theorem query_width (L m t q : ℕ) (ht : t ≤ 2*m) :
    (CroppedHighQueries.queryMagnitude m t (table L m q)).size ≤ 20*width L m q := by
  have hm := HalfSourceHighCounters.magnitude_width L (2^(L+m))
  have ha : (2^(L+m)).size=L+m+1 := Nat.size_pow
  have htable := HalfSourceHighCounters.table_width L q (BinaryCroppedHighBoxes.magnitude L (2^(L+m)))
  have hr := BinaryQueryCosts.highReads_le_power m t ht
  have hsize := Nat.size_le_size hr
  have hpow : (2^(6*m)).size=6*m+1 := Nat.size_pow
  have hmul := ParameterExecution.size_mul ((2*m).choose t*4^t) (table L m q)
  rw [ThinProductCosts.highCoefficientReads_eq] at hsize
  change (table L m q).size ≤ _ at htable
  unfold CroppedHighQueries.queryMagnitude width
  omega

theorem reads_pos (m t : ℕ) (ht : t ≤ 2*m) : 1 ≤ (2*m).choose t*4^t := by
  have hchoose := Nat.choose_pos ht
  have hpow : 0<(4:ℕ)^t := pow_pos (by decide) _
  exact Nat.mul_pos hchoose hpow

theorem row_polynomial (L m t q : ℕ) (ht : t ≤ 2*m) :
    SelectedHighQueries.rowBudget L m t (table L m q)+32 ≤
      10000000*((2*m).choose t*4^t)*(width L m q)^5 := by
  have hw := query_width L m t q ht
  have hu := BinaryQueryCosts.highQueryUnit_polynomial L m
    (CroppedHighQueries.queryMagnitude m t (table L m q)).size
  have hP : 1 ≤ width L m q := by unfold width;omega
  have hsmall : L+m+1 ≤ width L m q := by unfold width;omega
  have hu' : BinaryHighTable.queryUnit L (2*m) (CroppedHighQueries.queryMagnitude m t (table L m q)).size ≤
      1000000*(width L m q)^2 := by
    calc
      _ ≤ 2048*(L+m+(CroppedHighQueries.queryMagnitude m t (table L m q)).size+10)^2 := hu
      _ ≤ 2048*(21*width L m q)^2 := by gcongr;unfold width at *;omega
      _ ≤ _ := by nlinarith only [Nat.zero_le ((width L m q)^2)]
  have h2 : (width L m q)^2 ≤ (width L m q)^5 := Nat.pow_le_pow_right hP (by decide)
  have h0 : 1 ≤ (width L m q)^5 := one_le_pow₀ hP
  have hr := reads_pos m t ht
  have hh := Nat.mul_le_mul_left ((2*m).choose t*4^t) hu'
  have hp : 1000*(L+m+1)^5 ≤ 1000*(width L m q)^5 := by gcongr
  have hx : (width L m q)^5 ≤ ((2*m).choose t*4^t)*(width L m q)^5 := by nlinarith
  have hy := Nat.mul_le_mul_left (1000000*((2*m).choose t*4^t)) h2
  unfold SelectedHighQueries.rowBudget
  nlinarith only [hh,hp,hx,hy,h0]

theorem exponent_eq : ThinProductCosts.highQueryExponent theta=q2 := by
  unfold ThinProductCosts.highQueryExponent EntropyBounds.channelExponent q2 Q
    entropy RealCertificate.entropy Real.binEntropy
  simp only [Real.log_inv]
  ring

def constant : ℝ := 80000000*Real.exp (Real.log (1-theta)-Real.log theta)

theorem row_bound (m q : ℕ) (hm : 0 < m) :
    (SelectedHighQueries.rowBudget (OptimizedFoldedPlan.ordinaryLength m) m
      (OptimizedFoldedPlan.channelLength m) (table (OptimizedFoldedPlan.ordinaryLength m) m q)+32:ℕ) ≤
      constant*(m+1:ℝ)*(width (OptimizedFoldedPlan.ordinaryLength m) m q:ℝ)^5*(((4:ℝ)^m)^q2) := by
  let L := OptimizedFoldedPlan.ordinaryLength m
  let t := OptimizedFoldedPlan.channelLength m
  have ht : t ≤ 2*m := (OptimizedFoldedPlan.channelLength_upper m).trans (by omega)
  have hr := row_polynomial L m t q ht
  have hrR : ((SelectedHighQueries.rowBudget L m t (table L m q)+32:ℕ):ℝ) ≤
      10000000*((2*m).choose t*4^t:ℕ)*(width L m q:ℝ)^5 := by exact_mod_cast hr
  have htheta0 : 0 < theta := by norm_num[theta]
  have htheta1 : theta < 1/2 := by norm_num[theta]
  have hh := ThinProductCosts.rounded_highReads theta m htheta0 htheta1 hm
  have het : t=Nat.ceil (2*theta*(m:ℝ)) := by
    dsimp[t];rw[OptimizedFoldedPlan.channelLength_eq]
    norm_num[OptimizedFoldedPlan.theta,theta]
  dsimp only at hh
  rw[←het,ThinProductCosts.highCoefficientReads_eq,exponent_eq] at hh
  have hchannel : ThinProductCosts.channelFactor theta m ≤
      2*(m+1:ℝ)*Real.exp (Real.log (1-theta)-Real.log theta) := by
    unfold ThinProductCosts.channelFactor
    rw[←het]
    have htR : (t:ℝ) ≤ 2*(m:ℝ) := by exact_mod_cast ht
    gcongr
    linarith
  calc
    _ ≤ 10000000*((2*m).choose t*4^t:ℕ)*(width L m q:ℝ)^5 := hrR
    _ ≤ 10000000*(4*ThinProductCosts.channelFactor theta m*(((4:ℝ)^m)^q2))*(width L m q:ℝ)^5 := by gcongr
    _ ≤ 10000000*(4*(2*(m+1:ℝ)*Real.exp (Real.log (1-theta)-Real.log theta))*(((4:ℝ)^m)^q2))*(width L m q:ℝ)^5 := by gcongr
    _ = _ := by unfold constant;dsimp[L];ring

#print axioms query_width
#print axioms reads_pos
#print axioms row_polynomial
#print axioms exponent_eq
#print axioms row_bound
end
end ThinMatrix.HalfSourceHighQueryCost
