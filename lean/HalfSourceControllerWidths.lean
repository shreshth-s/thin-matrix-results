import HalfSourceBackendAggregation
import BinaryControllerPolynomialBounds

/-! Actual controller scalar width for the exact-half parameter program.
No producer runtime premise occurs: W is only the integer count cap. -/
namespace ThinMatrix.HalfSourceControllerWidths
open HalfSourceBatchFit HalfSourcePrimeParameters
open BinaryControllerPolynomialBounds (pow_coeff_mono incidence_pow stages_pow)
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
attribute [local irreducible] HalfSourceBatchFit.block HalfSourceBatchFit.R

def basicConstant (κ : ℕ) : ℕ := κ+R+16
def controllerConstant (κ K : ℕ) : ℕ := 3*basicConstant κ+K+14*R+6

theorem eightScale_pow (n : ℕ) (hs : 1 ≤ n.size) : 8*scale n ≤ 2^(14*n.size) := by
  have h := ParameterExecution.size_eight_mul (scale n)
  have ht := HalfSourceParameterExecution.scale_width n
  have hw : (8*scale n).size ≤ 14*n.size := by omega
  exact (Nat.size_le.mp hw).le

theorem computed_pool_pow (n : ℕ) (hs : 1 ≤ n.size) :
    (computedPool n).card ≤ 2^(14*n.size) := by
  exact (ParameterExecution.pool_card_le (scale n)).trans (eightScale_pow n hs)

theorem computed_controller_width (n U W κ K : ℕ) (hn : 3≤n)
    (parameters : CompleteAPSP.Parameters (block n) U)
    (hp : program n U=some parameters) (hU : U≤n^κ) (hW : W≤n^K) :
    (DenseControllerExecution.controllerCap parameters.pool.card
      (EndToEndAPSP.incidenceSize n (block n)) (n*n) parameters.k parameters.lam
      parameters.stages (block n) W (8*scale n)).size ≤ controllerConstant κ K*n.size := by
  have hs : 1≤n.size := Nat.size_pos.mpr (by omega)
  rcases program_sound n U parameters hp with ⟨hpool,hscale,hlam,hk,hM,hstages⟩
  have hP : parameters.pool.card≤2^(basicConstant κ*n.size) := by
    rw [hpool]
    exact (computed_pool_pow n hs).trans (pow_coeff_mono n.size 14 (basicConstant κ) (by unfold basicConstant;omega))
  have hI : EndToEndAPSP.incidenceSize n (block n)≤2^(basicConstant κ*n.size) :=
    (incidence_pow n (block n) (HalfSourceBatchFit.block_pos n) hs).trans
      (pow_coeff_mono n.size 5 (basicConstant κ) (by unfold basicConstant;omega))
  have hQ : n*n≤2^(basicConstant κ*n.size) := by
    calc
      _ ≤ 2^n.size*2^n.size := Nat.mul_le_mul (AdaptiveBitBounds.nat_le_pow_size n) (AdaptiveBitBounds.nat_le_pow_size n)
      _ = 2^(2*n.size) := by rw [←pow_add];congr 1;omega
      _ ≤ _ := pow_coeff_mono n.size 2 (basicConstant κ) (by unfold basicConstant;omega)
  have hl : parameters.lam≤2^(basicConstant κ*n.size) := by
    rw [hlam]
    exact (ParameterExecution.size_le_self U).trans
      ((AdaptiveBitBounds.original_power_bound n κ U hU).trans
        (pow_coeff_mono n.size κ (basicConstant κ) (by unfold basicConstant;omega)))
  have ht : parameters.stages≤2^(basicConstant κ*n.size) := by
    rw [hstages]
    exact (stages_pow n hs).trans (pow_coeff_mono n.size 2 (basicConstant κ) (by unfold basicConstant;omega))
  have hX : block n≤2^(basicConstant κ*n.size) :=
    (HalfSourceBatchGeometry.block_le_n n (by omega)).trans ((AdaptiveBitBounds.nat_le_pow_size n).trans
      (by simpa only [Nat.one_mul] using pow_coeff_mono n.size 1 (basicConstant κ) (by unfold basicConstant;omega)))
  have hkp : parameters.k+1=R := by rw [hk];norm_num [HalfSourceBatchFit.R]
  have hround : parameters.k+1≤2^(basicConstant κ*n.size) := by
    rw [hkp]
    have hr : R≤2^R := (show R<2^R from Nat.lt_two_pow_self).le
    exact hr.trans (Nat.pow_le_pow_right (by decide) (by
      have hm : R≤R*n.size := Nat.le_mul_of_pos_right _ hs
      unfold basicConstant
      nlinarith))
  have hpmax:=eightScale_pow n hs
  have hWpow:=AdaptiveBitBounds.original_power_bound n K W hW
  have hc:=ControllerCapPow.controllerCap_size_le parameters.pool.card
    (EndToEndAPSP.incidenceSize n (block n)) (n*n) parameters.k parameters.lam
    parameters.stages (block n) W (8*scale n) (basicConstant κ) K 14 n.size
    hs hP hI hQ hl ht hX hround hWpow hpmax
  simpa only [ControllerCapPow.capExponent,hkp,controllerConstant] using hc

#print axioms eightScale_pow
#print axioms computed_pool_pow
#print axioms computed_controller_width
end ThinMatrix.HalfSourceControllerWidths
