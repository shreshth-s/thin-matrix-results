import GraphHalfSourceHostCosts
import HalfSourcePointwiseHost

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
namespace ThinMatrix.GraphHalfSourceWork
open Filter Asymptotics GraphHalfSourceHostCosts HalfSourceCallbackBudget
noncomputable section
variable (scheme : RectangularBatch.Scheme) (hnum : scheme.num=861) (hden : scheme.den=500)
  (hz : scheme.z=15) (hv : scheme.Valid)
attribute [local irreducible] GraphHalfSourceHostCosts.factory HalfSourceBatchFit.R
  HalfSourceCallbackBudget.addressPrice GraphHalfSourceHostCosts.finalPrice

theorem run_work_of_phasePrices
    (degree A k : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hphase : phasePrices scheme hnum hden hz hv (degree+2) A k C)
    (w : (n : ℕ)→StoredMinPlusAPSP.OptionalTable n) (W : ℕ→ℕ)
    (hw : ∀ n,APSPReduction.EdgeBound (StoredMinPlusAPSP.decode (w n)) (W n))
    (hW : ∀ n,W n ≤ n^degree) :
    (fun n : ℕ=>((HalfSourceAPSPHost.run (factory scheme hnum hden hz hv) (w n) (W n)
      (addressPrice n (degree+2) A)).work:ℝ)) =O[atTop]
      (fun n : ℕ=>(n:ℝ)^(14963431313/5000000000:ℝ)) := by
  let K : ℝ := 50*(degree+6:ℕ)+1
  have hb : (fun n : ℕ=>((HalfSourceAPSPHost.run (factory scheme hnum hden hz hv) (w n) (W n)
      (addressPrice n (degree+2) A)).work:ℝ)) =O[atTop]
      (fun n : ℕ=>BinaryAPSPHostTotalCosts.hostAllowance degree n+
        K*((Real.log (n:ℝ))^2*finalPrice degree A k C n)) := by
    apply IsBigO.of_norm_eventuallyLE
    filter_upwards [combined_price scheme hnum hden hz hv degree A k C hC hphase,
      eventually_ge_atTop (3:ℕ)] with n hp hn
    rw[Real.norm_of_nonneg (Nat.cast_nonneg _)]
    have hx := HalfSourcePointwiseHost.run_work_le (factory scheme hnum hden hz hv)
      (w n) (W n) (addressPrice n (degree+2) A) degree hn (hw n) (hW n)
      (finalPrice degree A k C n) (finalPrice_nonneg degree A k C hC n hn)
      (hp (W n) (hW n))
    simpa only[K,mul_assoc] using hx
  exact hb.trans ((HalfSourceAPSPCosts.hostAllowance_bigO degree).add
    ((finalPrice_bigO degree A k C).const_mul_left K))

#print axioms run_work_of_phasePrices
end
end ThinMatrix.GraphHalfSourceWork
