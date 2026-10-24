import HalfSourceControllerBudget
import HalfSourceCallbackBudget

/-! Full controller, scan and write overhead under the new parameters.
This bound is independent of the production backend's runtime. -/
namespace ThinMatrix.HalfSourceCallbackCosts
open BinaryTriangleExecution HalfSourceBatchFit HalfSourcePrimeParameters
open HalfSourceCallbackBudget Filter Asymptotics
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
attribute [local irreducible] HalfSourceBatchFit.R HalfSourceBatchFit.block
noncomputable section

 def coefficient (κ A : ℕ) : ℝ :=
  (callbackCoefficient κ A:ℝ)*BinaryTriangleCosts.FixedPrices.sizeLogConstant^2*
    AlignedAPSPCosts.ControllerCosts.referenceControllerConstant R

 def overhead (κ A n : ℕ) : ℝ :=
  coefficient κ A*(Real.log (n:ℝ))^7*(n:ℝ)^(3-(b-eta))

 theorem callback_price {n U κ addressCoefficient : ℕ} {Payload : Type}
    (hn : 3 ≤ n) (parameters : CompleteAPSP.Parameters (block n) U)
    (hp : program n U=some parameters) (hU : U ≤ n^κ)
    (backend : Backend n (block n) Payload) (static : Static (n:=n) parameters)
    (A B T : IntTable n)
    (hcounts : BinaryControllerExecution.OracleCountsBound (backend.oracle A B T) (block n))
    (hcap : CountedEndToEndAPSP.entryQueryBound (viewTable A) (viewTable B) (viewTable T) ≤ U) :
    let addr := addressPrice n κ addressCoefficient
    ((callback backend parameters static addr A B T).work:ℝ)+
      (callback backend parameters static addr A B T).answerWrites ≤
      ((solve backend parameters static A B T).backendWork:ℝ)+overhead κ addressCoefficient n := by
  have hf := computed_callback_budget (addressCoefficient:=addressCoefficient) hn parameters hp hU backend static A B T hcounts hcap
  have hfR : ((callback backend parameters static (addressPrice n κ addressCoefficient) A B T).work:ℝ)+
      (callback backend parameters static (addressPrice n κ addressCoefficient) A B T).answerWrites ≤
      ((solve backend parameters static A B T).backendWork:ℝ)+
        (callbackCoefficient κ addressCoefficient:ℝ)*(n.size+1:ℝ)^2*
          (BinaryTriangleCosts.referenceBudget n (block n) parameters.pool.card parameters.k parameters.stages:ℝ) := by exact_mod_cast hf
  have hparams := program_sound n U parameters hp
  have hk : parameters.k ≤ R := by rw[hparams.2.2.2.1];exact Nat.sub_le _ _
  have hr := HalfSourceControllerBudget.computed_referenceControllerBudget_le R parameters.k n hn hk
  have hr' : (BinaryTriangleCosts.referenceBudget n (block n) parameters.pool.card parameters.k parameters.stages:ℝ) ≤
      AlignedAPSPCosts.ControllerCosts.referenceControllerConstant R*(Real.log (n:ℝ))^5*(n:ℝ)^(3-(b-eta)) := by
    rw[hparams.1,hparams.2.2.2.2.2]
    exact hr
  have hu := BinaryTriangleCosts.FixedPrices.sizeFactor_le_log (callbackCoefficient κ addressCoefficient) 2 n hn
  push_cast at hu
  have hnon : 0 ≤ (BinaryTriangleCosts.referenceBudget n (block n) parameters.pool.card parameters.k parameters.stages:ℝ) := Nat.cast_nonneg _
  have hc : 0 ≤ (callbackCoefficient κ addressCoefficient:ℝ)*BinaryTriangleCosts.FixedPrices.sizeLogConstant^2*(Real.log (n:ℝ))^2 := by positivity
  have hh := mul_le_mul hu hr' hnon hc
  have hfinal : (callbackCoefficient κ addressCoefficient:ℝ)*(n.size+1:ℝ)^2*
      (BinaryTriangleCosts.referenceBudget n (block n) parameters.pool.card parameters.k parameters.stages:ℝ) ≤ overhead κ addressCoefficient n := by
    simpa only [overhead,coefficient,pow_succ,pow_zero,mul_one,one_mul,mul_assoc,mul_comm,mul_left_comm] using hh
  exact hfR.trans (add_le_add_right hfinal _)

 theorem overhead_bigO (κ A k : ℕ) :
    (fun n : ℕ => (Real.log (n:ℝ))^k*overhead κ A n) =O[atTop]
      (fun n : ℕ => (n:ℝ)^(14963431313/5000000000:ℝ)) := by
  have hgap : 3-(b-eta) < (14963431313/5000000000:ℝ) := by
    norm_num[b,eta,bNumerator,bDenominator,HalfSourceBatchFit.R]
  have hh := (AsymptoticCosts.logPowMulRpowBigO hgap (k+7)).const_mul_left (coefficient κ A)
  simpa only [overhead,pow_add,mul_assoc,mul_comm,mul_left_comm] using hh

#print axioms callback_price
#print axioms overhead_bigO
end
end ThinMatrix.HalfSourceCallbackCosts
