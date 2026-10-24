import HalfSourcePublicWidths
import HalfSourceActualRaw

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
namespace ThinMatrix.HalfSourceOutputPhaseRate
open HalfSourceBatchFit HalfSourcePublicWidths
noncomputable section
attribute [local irreducible] HalfSourceBatchFit.block

def coefficient (scheme : RectangularBatch.Scheme) (κ : ℕ) : ℝ :=
  40000000000*(5*HalfSourcePublicWidths.coefficient scheme κ)^7

 theorem coefficient_pos (scheme : RectangularBatch.Scheme) (κ : ℕ) : 0<coefficient scheme κ := by
  have hc : 0<HalfSourcePublicWidths.coefficient scheme κ := by
    unfold HalfSourcePublicWidths.coefficient;omega
  unfold coefficient
  positivity

 theorem polynomial_bound (scheme : RectangularBatch.Scheme) (n κ : ℕ) (call : Call n) (hn : 3 ≤ n)
    (hv : EndToEndAPSP.ValidFactors call.factors) (price : ℕ) :
    let out := HalfSourceDispatch.prepare n (block n) call.factors hv
    10000000000*(price+1:ℝ)*(EndToEndAPSP.incidenceSize n (block n)+1:ℝ)*
      (GraphHalfSourceOutputCost.width out.split.plan out.plan.value:ℝ)^7 ≤
      coefficient scheme κ*(price+1)*(Real.log (n:ℝ))^7*HalfSourceComputedCosts.phaseRawSum n call := by
  let out := HalfSourceDispatch.prepare n (block n) call.factors hv
  let f := out.split.plan
  let p := out.plan.value
  let I := EndToEndAPSP.incidenceSize n (block n)
  let P : ℝ := HalfSourceComputedCosts.phaseRawSum n call
  have hB : 1 ≤ CompactBlocks.blockCount n (block n) :=
    HalfSourceInputMetadata.blocks_positive (by omega) (block_pos n)
  have hw := (widths scheme n κ call hn hv).2.2.2.2
  have hlog := bound_log scheme n κ hn
  have hwR : (GraphHalfSourceOutputCost.width f p:ℝ) ≤
      (5*HalfSourcePublicWidths.coefficient scheme κ:ℝ)*Real.log (n:ℝ) :=
    (show (GraphHalfSourceOutputCost.width f p:ℝ) ≤ HalfSourcePublicWidths.bound scheme n κ by exact_mod_cast hw).trans hlog
  have hI := HalfSourceRawAbsorption.writes (n:ℝ) p.N ((4:ℝ)^p.m) f.cyclic
    (CompactBlocks.blockCount n (block n))
    (by exact_mod_cast (show 1 ≤ n by omega)) (Nat.cast_nonneg _)
    (one_le_pow₀ (by norm_num)) (by exact_mod_cast f.cyclic_pos) (by exact_mod_cast hB)
  rw[HalfSourceActualRaw.eq_phase n call hv] at hI
  have hIR : (I:ℝ)+1 ≤ 4*P := by
    unfold I EndToEndAPSP.incidenceSize CompactBlocks.blockCount at ⊢
    push_cast
    simpa only [P,CompactBlocks.blockCount,pow_two,mul_assoc,mul_comm,mul_left_comm] using hI
  have hP := HalfSourceComputedCosts.phaseRawSum_nonneg n call
  have hW := pow_le_pow_left₀ (Nat.cast_nonneg (GraphHalfSourceOutputCost.width f p)) hwR 7
  dsimp only
  change 10000000000*(price+1)*(I+1:ℝ)*(GraphHalfSourceOutputCost.width f p:ℝ)^7 ≤ _
  calc
    _ ≤ 10000000000*(price+1)*(4*P)*
      (((5*HalfSourcePublicWidths.coefficient scheme κ:ℝ)*Real.log (n:ℝ))^7) := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left hIR (by positivity)
        · exact hW
        · positivity
        · dsimp only[P];positivity
    _ = _ := by unfold coefficient;rw[mul_pow];ring

 theorem bound (scheme : RectangularBatch.Scheme) (n κ : ℕ) (call : Call n) (hn : 3 ≤ n)
    (hv : EndToEndAPSP.ValidFactors call.factors) (price : ℕ) :
    let out := HalfSourceDispatch.prepare n (block n) call.factors hv
    (GraphHalfSourceOutputCost.extra out.split.plan out.plan.value price:ℝ) ≤
      coefficient scheme κ*(price+1)*(Real.log (n:ℝ))^7*HalfSourceComputedCosts.phaseRawSum n call := by
  have hB : 1 ≤ CompactBlocks.blockCount n (block n) :=
    HalfSourceInputMetadata.blocks_positive (by omega) (block_pos n)
  have he := GraphHalfSourceOutputCost.extra_polynomial
    (HalfSourceDispatch.prepare n (block n) call.factors hv).split.plan
    (HalfSourceDispatch.prepare n (block n) call.factors hv).plan.value price hB
  have heR := (Nat.cast_le (α:=ℝ)).mpr he
  push_cast at heR
  exact heR.trans (polynomial_bound scheme n κ call hn hv price)

#print axioms coefficient_pos
#print axioms polynomial_bound
#print axioms bound
end
end ThinMatrix.HalfSourceOutputPhaseRate
