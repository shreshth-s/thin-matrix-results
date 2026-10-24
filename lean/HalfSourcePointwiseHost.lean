import HalfSourceAPSPCosts

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

/-! Pointwise assembly avoids higher-order reduction of an executable factory
or address-price function. All resources come from the same prepared run. -/
namespace ThinMatrix.HalfSourcePointwiseHost
open BinaryAPSPCaller HalfSourceAPSPHost HalfSourceAPSPCosts
open BinaryAPSPHostTotalCosts BinaryAPSPHostCosts BinaryAPSPUniformCosts
noncomputable section

theorem core_work_le {n : ℕ} {Payload : Type} (O : Oracle n Payload)
    (hON : Refines O (EndToEndAPSP.directCallback n))
    (w : StoredMinPlusAPSP.OptionalTable n) (W degree setup : ℕ)
    (hn : 3 ≤ n) (hw : APSPReduction.EdgeBound (StoredMinPlusAPSP.decode w) W)
    (hW : W ≤ n^degree) (F : ℝ) (hF0 : 0 ≤ F)
    (hprice : ∀ A B T,
      APSPAlgorithm.SymmetricQueryBound
        (StoredMinPlusAPSP.decode (viewTable A),StoredMinPlusAPSP.decode (viewTable B),
          StoredMinPlusAPSP.decode (viewTable T)) (64*n*W+13:ℕ) →
      (setup:ℝ)+(O A B T).work+(O A B T).answerWrites ≤ F) :
    (setup:ℝ)+(BinaryAPSPCaller.run O w W).hostBits+
      (BinaryAPSPCaller.run O w W).oracleWork+(BinaryAPSPCaller.run O w W).answerWrites ≤
      BinaryAPSPHostTotalCosts.hostAllowance degree n+
        (50*(degree+6:ℕ)+1)*(Real.log (n:ℝ))^2*F := by
  have hlocal : ∀ A B T,
      APSPAlgorithm.SymmetricQueryBound
        (StoredMinPlusAPSP.decode (viewTable A),StoredMinPlusAPSP.decode (viewTable B),
          StoredMinPlusAPSP.decode (viewTable T)) (64*n*W+13:ℕ) →
      ((O A B T).work:ℝ)+(O A B T).answerWrites ≤ F := by
    intro A B T hb
    have hp := hprice A B T hb
    have hs : (0:ℝ) ≤ setup := Nat.cast_nonneg _
    linarith only [hp,hs]
  have hc := actual_callback_resources_le O (EndToEndAPSP.directCallback n) hON
    (EndToEndAPSP.directCallback_correct n) w W degree hw hn hW F hF0 hlocal
  have hh : ((BinaryAPSPCaller.run O w W).hostBits:ℝ) ≤
      BinaryAPSPHostTotalCosts.hostAllowance degree n := by
    have ht := run_hostBits_le (show 0<n by omega) O w W degree hw hW
    unfold BinaryAPSPHostTotalCosts.hostAllowance
    exact_mod_cast ht
  have hs : (setup:ℝ) ≤ F := by
    have hz := hprice (BinaryAlignedAPSPCosts.zeroTable n)
      (BinaryAlignedAPSPCosts.zeroTable n) (BinaryAlignedAPSPCosts.zeroTable n)
      (BinaryAlignedAPSPCosts.zeroTable_query_bound n W)
    have ha : (0:ℝ) ≤ (O (BinaryAlignedAPSPCosts.zeroTable n)
      (BinaryAlignedAPSPCosts.zeroTable n) (BinaryAlignedAPSPCosts.zeroTable n)).work := Nat.cast_nonneg _
    have hb : (0:ℝ) ≤ (O (BinaryAlignedAPSPCosts.zeroTable n)
      (BinaryAlignedAPSPCosts.zeroTable n) (BinaryAlignedAPSPCosts.zeroTable n)).answerWrites := Nat.cast_nonneg _
    linarith only [hz,ha,hb]
  have hl : 1 ≤ (Real.log (n:ℝ))^2 := one_le_pow₀ (PhaseGeometry.one_le_log_nat n hn)
  have hsl : (setup:ℝ) ≤ (Real.log (n:ℝ))^2*F :=
    hs.trans (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hl hF0)
  nlinarith only [hsl,hh,hc]

#print axioms core_work_le

 theorem run_work_identity (factory : BackendFactory) {n : ℕ}
    (w : StoredMinPlusAPSP.OptionalTable n) (W a : ℕ) :
    ((HalfSourceAPSPHost.run factory w W a).work:ℝ)=
      (setupWork factory n W a:ℝ)+
        (BinaryAPSPCaller.run (prepare factory n W a).oracle w W).hostBits+
        (BinaryAPSPCaller.run (prepare factory n W a).oracle w W).oracleWork+
        (BinaryAPSPCaller.run (prepare factory n W a).oracle w W).answerWrites := by
  simp only [HalfSourceAPSPHost.run,setupWork,preparationWork,Nat.cast_add]

#print axioms run_work_identity

 theorem run_work_le (factory : BackendFactory) {n : ℕ}
    (w : StoredMinPlusAPSP.OptionalTable n) (W a degree : ℕ)
    (hn : 3 ≤ n) (hw : APSPReduction.EdgeBound (StoredMinPlusAPSP.decode w) W)
    (hW : W ≤ n^degree) (F : ℝ) (hF0 : 0 ≤ F)
    (hprice : ∀ A B T,
      APSPAlgorithm.SymmetricQueryBound
        (StoredMinPlusAPSP.decode (viewTable A),StoredMinPlusAPSP.decode (viewTable B),
          StoredMinPlusAPSP.decode (viewTable T)) (64*n*W+13:ℕ) →
      (setupWork factory n W a:ℝ)+((prepare factory n W a).oracle A B T).work+
        ((prepare factory n W a).oracle A B T).answerWrites ≤ F) :
    ((HalfSourceAPSPHost.run factory w W a).work:ℝ) ≤
      BinaryAPSPHostTotalCosts.hostAllowance degree n+
        (50*(degree+6:ℕ)+1)*(Real.log (n:ℝ))^2*F := by
  rw [run_work_identity]
  exact core_work_le (prepare factory n W a).oracle
    (correct_refines_direct factory (prepare factory n W a).oracle
      (prepare_correct factory n W a))
    w W degree (setupWork factory n W a) hn hw hW F hF0 hprice

#print axioms run_work_le
end
end ThinMatrix.HalfSourcePointwiseHost
