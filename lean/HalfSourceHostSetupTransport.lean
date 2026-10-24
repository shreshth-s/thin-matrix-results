import HalfSourceAPSPCosts
import HalfSourceAPSPTransport

/-! Finite composition with the retained exact-half parameter setup. -/
namespace ThinMatrix.HalfSourceHostSetupTransport
open HalfSourceAPSPHost HalfSourceAPSPTransport HalfSourceAPSPCosts
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
attribute [local irreducible] HalfSourceBatchFit.block
variable (factory : BackendFactory)
private theorem numerical_bound (a s p x y w out pub : ℕ)
    (ha : 1 ≤ a) (hp : p ≤ s) :
    (s+pub+x)+(a+1)*(p+y+64+8)+(w+4*(a+1))+out  ≤
      2*(x+a*y+w+out)+(a+2)*s+pub+76*(a+1) := by
  have hpy := Nat.mul_le_mul_left (a+1) hp
  have hay : (a+1)*y  ≤  2*a*y := Nat.mul_le_mul_right y (by omega)
  nlinarith only [hpy,hay]

private theorem setupFromSetup_and_callback_le_original {n : ℕ} (W a : ℕ) (ha : 1 ≤ a)
    (setup : HalfSourceParameterExecution.Execution n (cap n W))
    (hsetup : setup=HalfSourceParameterExecution.execute n (cap n W))
    (p : CompleteAPSP.Parameters (HalfSourceBatchFit.block n) (cap n W))
    (hp : setup.value=some p) (hpool : setup.metadata.pool.length ≤ setup.bitSteps)
    (A B T : BinaryAPSPCaller.IntTable n) :
    ((prepareFromSetup factory W a setup hsetup).setupBits+
      (a+1)*((prepareFromSetup factory W a setup hsetup).setupControl+8))+
      ((prepareFromSetup factory W a setup hsetup).oracle A B T).work+
      ((prepareFromSetup factory W a setup hsetup).oracle A B T).answerWrites ≤
      2*((originalCallback factory W a setup hsetup p hp).setupBits+
        a*(originalCallback factory W a setup hsetup p hp).setupControl+
        ((originalCallback factory W a setup hsetup p hp).oracle A B T).work+
        ((originalCallback factory W a setup hsetup p hp).oracle A B T).answerWrites)+
      (a+2)*setup.bitSteps+publicSetupBits n W+76*(a+1) := by
  rw [prepared_setupBits_original factory W a setup hsetup p hp,
    prepared_setupControl_original factory W a setup hsetup p hp,
    prepared_work_original factory W a setup hsetup p hp A B T,
    prepared_answerWrites_original factory W a setup hsetup p hp A B T]
  exact numerical_bound a _ _ _ _ _ _ _ ha hpool

theorem setup_and_callback_le_original {n : ℕ} (W a : ℕ) (ha : 1 ≤ a)
    (p : CompleteAPSP.Parameters (HalfSourceBatchFit.block n) (cap n W))
    (hp : (HalfSourceParameterExecution.execute n (cap n W)).value=some p)
    (A B T : BinaryAPSPCaller.IntTable n) :
    setupWork factory n W a+((prepare factory n W a).oracle A B T).work+
      ((prepare factory n W a).oracle A B T).answerWrites ≤
      2*((originalCallback factory W a (HalfSourceParameterExecution.execute n (cap n W)) rfl p hp).setupBits+
        a*(originalCallback factory W a (HalfSourceParameterExecution.execute n (cap n W)) rfl p hp).setupControl+
        ((originalCallback factory W a (HalfSourceParameterExecution.execute n (cap n W)) rfl p hp).oracle A B T).work+
        ((originalCallback factory W a (HalfSourceParameterExecution.execute n (cap n W)) rfl p hp).oracle A B T).answerWrites)+
      (a+2)*(HalfSourceParameterExecution.execute n (cap n W)).bitSteps+
      publicSetupBits n W+76*(a+1) := by
  have h := setupFromSetup_and_callback_le_original factory W a ha _ rfl p hp
    (HalfSourceParameterMetadata.metadata_pool_length_price n (cap n W)) A B T
  have he : prepare factory n W a=prepareFromSetup factory W a (HalfSourceParameterExecution.execute n (cap n W)) rfl := rfl
  rw [←he] at h
  exact h

#print axioms setup_and_callback_le_original
end ThinMatrix.HalfSourceHostSetupTransport
