import HalfSourcePlanExecution
import AlignedAPSP

/-! Actual factor split and public plan using the exact-half frozen S.
The split retains factor 3 on the physical folded side only. -/
namespace ThinMatrix.HalfSourceDispatch
open BinaryTriangleSetupCosts
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
attribute [local irreducible] HalfSourceBatchFit.S

structure Prepared (n h : ℕ) (factors : List ℕ) where
  split : AlignedAPSP.FactorSetup factors
  plan : Run (BinaryFoldedFactory.Plan (n:=n) (h:=h) split.plan)

 def prepare (n h : ℕ) (factors : List ℕ) (hv : EndToEndAPSP.ValidFactors factors) : Prepared n h factors :=
  let split := AlignedAPSP.prepareFactors HalfSourceBatchFit.S factors hv
  ⟨split,HalfSourcePlanExecution.preparePlan n h split.plan⟩

 theorem folded (n h : ℕ) (factors : List ℕ) (hv : EndToEndAPSP.ValidFactors factors) :
    (prepare n h factors hv).split.plan.folded=(factors.take HalfSourceBatchFit.S).prod := by
  change (AlignedAPSP.prepareFactors HalfSourceBatchFit.S factors hv).plan.folded=_
  rw[AlignedAPSP.prepareFactors_plan]
  rfl

 theorem cyclic (n h : ℕ) (factors : List ℕ) (hv : EndToEndAPSP.ValidFactors factors) :
    (prepare n h factors hv).split.plan.cyclic=(factors.drop HalfSourceBatchFit.S).prod := by
  change (AlignedAPSP.prepareFactors HalfSourceBatchFit.S factors hv).plan.cyclic=_
  rw[AlignedAPSP.prepareFactors_plan]
  rfl

 theorem plan_m (n h : ℕ) (factors : List ℕ) (hv : EndToEndAPSP.ValidFactors factors) :
    (prepare n h factors hv).plan.value.m=Nat.clog 4 (h*(3*(factors.take HalfSourceBatchFit.S).prod)) := by
  change (HalfSourcePlanExecution.preparePlan n h (prepare n h factors hv).split.plan).value.m=_
  rw[HalfSourcePlanExecution.preparePlan_m]
  change Nat.clog 4 (h*(3*(prepare n h factors hv).split.plan.folded))=_
  rw[folded]

 theorem canonical (n h : ℕ) (factors : List ℕ) (hv : EndToEndAPSP.ValidFactors factors) :
    let p := (prepare n h factors hv).plan.value
    p.L=OptimizedFoldedPlan.ordinaryLength p.m ∧ p.t=OptimizedFoldedPlan.channelLength p.m ∧ p.m ≤ p.L-p.m := by
  dsimp only[prepare]
  refine ⟨?_,?_,HalfSourcePlanExecution.preparePlan_half _ _ _⟩
  · rw[HalfSourcePlanExecution.preparePlan_L,HalfSourcePlanExecution.preparePlan_m]
  · rw[HalfSourcePlanExecution.preparePlan_t,HalfSourcePlanExecution.preparePlan_m]

 theorem actual_phase (n : ℕ) (call : HalfSourceBatchFit.Call n)
    (hv : EndToEndAPSP.ValidFactors call.factors) :
    let out := prepare n (HalfSourceBatchFit.block n) call.factors hv
    out.split.plan.folded=call.folded HalfSourceBatchFit.S ∧
    out.split.plan.cyclic=call.cyclic HalfSourceBatchFit.S ∧
    out.plan.value.m=HalfSourceLogGeometry.innerPower n call ∧
    out.plan.value.D=HalfSourceBatchFit.dimension n call ∧
    out.plan.value.N=HalfSourceBatchGeometry.outer n call := by
  dsimp only
  refine ⟨folded _ _ _ _,cyclic _ _ _ _,plan_m _ _ _ _,?_,?_⟩
  · rw[(prepare n (HalfSourceBatchFit.block n) call.factors hv).plan.value.D_eq]
    change 4^(Nat.clog 4 (HalfSourceBatchFit.block n*(3*(prepare n (HalfSourceBatchFit.block n) call.factors hv).split.plan.folded)))=_
    rw[folded]
    rfl
  · rw[(prepare n (HalfSourceBatchFit.block n) call.factors hv).plan.value.N_eq]
    change n*FoldedCounts.foldWidth (3*(prepare n (HalfSourceBatchFit.block n) call.factors hv).split.plan.folded)=_
    rw[folded]
    rfl

 theorem setup_sites (n h : ℕ) (factors : List ℕ) (hv : EndToEndAPSP.ValidFactors factors) :
    let out := prepare n h factors hv
    out.plan.sites ≤ 7*(3*out.split.plan.folded)+15*(h*(3*out.split.plan.folded)).size+
      4*out.plan.value.m+7*out.split.plan.cyclic.size+110 :=
  HalfSourcePlanExecution.preparePlan_sites _ _ _

#print axioms folded
#print axioms cyclic
#print axioms plan_m
#print axioms canonical
#print axioms actual_phase
#print axioms setup_sites
end ThinMatrix.HalfSourceDispatch
