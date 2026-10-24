import HalfSourceRootSetupCost
import GraphAdaptiveSourceBank

/-! Directly price root/key execution from original callback inputs and
its retained once-per-band schedule. Shape equalities are the executable
rounded factory's outputs, not cost hypotheses. -/
namespace ThinMatrix.HalfSourceRootRuntime
open HalfSourceParameters
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
attribute [local irreducible] GraphResidualFamilies.fromInputs

variable {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
  (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f)
  (block : Fin (CompactBlocks.blockCount n h)) (input : BinaryFoldedFormation.Inputs n)

def cost (a b : ℕ) : ℕ :=
  let result := GraphResidualFamilies.fromInputs f p block input a b
  result.keys.bitSteps+result.roots.bitSteps+result.keys.control+result.roots.control

theorem cost_budget (a b : ℕ)
    (hL : p.L=OptimizedFoldedPlan.ordinaryLength p.m) (ht : p.t=OptimizedFoldedPlan.channelLength p.m) :
    cost f p block input a b≤HalfSourceRootSetupCost.budget p.m f.cyclic := by
  have hb := GraphResidualFamilies.fromInputs_bits f p block input a b
  have hc := GraphResidualFamilies.fromInputs_control f p block input a b
  have hh := Nat.add_le_add hb hc
  unfold cost HalfSourceRootSetupCost.budget
  rw [← hL,← ht]
  dsimp only
  omega

theorem cost_finite (a b : ℕ) (hm : 0 < p.m)
    (hL : p.L=OptimizedFoldedPlan.ordinaryLength p.m) (ht : p.t=OptimizedFoldedPlan.channelLength p.m) :
    cost f p block input a b≤200000000000000000000*HalfSourceActualVolumes.roots p.m*f.cyclic*(p.m+1)^12 :=
  (cost_budget f p block input a b hL ht).trans (HalfSourceRootSetupCost.budget_finite p.m f.cyclic hm f.cyclic_pos)

/-- All ids are allowed, including repeats. A stored diagonal preparation
uses exactly one summand for each actual retained band. -/
theorem bank_sum {K : ℕ} (ids : Vector ℕ K)
    (hL : p.L=OptimizedFoldedPlan.ordinaryLength p.m) (ht : p.t=OptimizedFoldedPlan.channelLength p.m) :
    (∑ i, cost f p block input (ids.get i) (ids.get i))≤K*HalfSourceRootSetupCost.budget p.m f.cyclic := by
  have h := Finset.sum_le_sum (s:=Finset.univ) (fun (i : Fin K) _ => cost_budget f p block input (ids.get i) (ids.get i) hL ht)
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] using h

theorem actual_bank_cost
    (ids : Vector ℕ (TilingCosts.bandCount p.N (ThinMatrixBackend.tileWidth p.L p.m)))
    (hm : 0 < p.m) (hL : p.L=OptimizedFoldedPlan.ordinaryLength p.m)
    (ht : p.t=OptimizedFoldedPlan.channelLength p.m)
    (hfit : ThinProductCosts.gridSide p.L p.m≤p.N) :
    ((∑ i, cost f p block input (ids.get i) (ids.get i)):ℕ)≤
      TilingCosts.bandCount p.N (ThinMatrixBackend.tileWidth p.L p.m)*HalfSourceRootSetupCost.budget p.m f.cyclic ∧
    (((∑ i, cost f p block input (ids.get i) (ids.get i)):ℕ):ℝ)≤
      (1000000000000000000000000*HalfSourceRootVolume.rootConstant)*(f.cyclic:ℝ)*(p.N:ℝ)*(p.m+1:ℝ)^14*
        (((4:ℝ)^p.m)^Eroot) := by
  have hs := bank_sum f p block input ids hL ht
  refine ⟨hs,?_⟩
  have hsR : (((∑ i, cost f p block input (ids.get i) (ids.get i)):ℕ):ℝ)≤
    (TilingCosts.bandCount p.N (ThinMatrixBackend.tileWidth p.L p.m):ℝ)*(HalfSourceRootSetupCost.budget p.m f.cyclic:ℝ) := by exact_mod_cast hs
  have hb := HalfSourceRootSetupCost.budget_bands p.N p.m f.cyclic hm f.cyclic_pos (by simpa only [hL] using hfit)
  rw [← hL] at hb
  exact hsR.trans hb

#print axioms cost_budget
#print axioms cost_finite
#print axioms bank_sum
#print axioms actual_bank_cost
end
end ThinMatrix.HalfSourceRootRuntime
