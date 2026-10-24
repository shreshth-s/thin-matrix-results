import HalfSourceBinarySourceCosts
import HalfSourceBandVolume
import GraphAdaptiveSourceBank

/-! Actual all-pair translated source execution, including binary caches and
all degree runs, and its retained once-per-band cost. -/
namespace ThinMatrix.HalfSourceBinarySourceRuntime
open HalfSourceParameters
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 2000000
attribute [local irreducible] ExactHalfGraphSources.execute

variable {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
  (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f)
  (block : Fin (CompactBlocks.blockCount n h)) (input : BinaryFoldedFormation.Inputs n)

def cost (a b : ℕ) : ℕ := (ExactHalfGraphSources.execute f p block input a b).sources.operations

theorem cost_budget (a b : ℕ) (hL : p.L=OptimizedFoldedPlan.ordinaryLength p.m) :
    cost f p block input a b≤ExactHalfBandSources.familiesBudget (OptimizedFoldedPlan.ordinaryLength p.m) p.m f.cyclic 1 := by
  simpa only [cost,hL] using ExactHalfGraphSources.sources_work f p block input a b

theorem bank_sum {K : ℕ} (ids : Vector ℕ K)
    (hL : p.L=OptimizedFoldedPlan.ordinaryLength p.m) :
    (∑ i,cost f p block input (ids.get i) (ids.get i))≤
      K*ExactHalfBandSources.familiesBudget (OptimizedFoldedPlan.ordinaryLength p.m) p.m f.cyclic 1 := by
  have hs := Finset.sum_le_sum (s:=Finset.univ) (fun (i : Fin K) _ => cost_budget f p block input (ids.get i) (ids.get i) hL)
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] using hs

theorem eventual_band_budget : ∀ᶠ m : ℕ in Filter.atTop, ∀ N q : ℕ, 1≤q→
    ThinProductCosts.gridSide (OptimizedFoldedPlan.ordinaryLength m) m≤N→
    (TilingCosts.bandCount N (ThinMatrixBackend.tileWidth (OptimizedFoldedPlan.ordinaryLength m) m):ℝ)*
      (ExactHalfBandSources.familiesBudget (OptimizedFoldedPlan.ordinaryLength m) m q 1:ℝ)≤
      416*(q:ℝ)*(N:ℝ)*(m+1:ℝ)*(((4:ℝ)^m)^E) := by
  filter_upwards [HalfSourceBinarySourceCosts.eventual_families_fit,Filter.eventually_ge_atTop 1] with m hm hm1
  intro N q hq hfit
  have hb := HalfSourceBandVolume.transfer N m (by omega) hfit (q:ℝ) _ E (Nat.cast_nonneg q) (hm q hq)
  have hL := HalfSourceRootPolynomials.ordinary_bound m
  have hL' : (OptimizedFoldedPlan.ordinaryLength m+1:ℝ)≤13*(m+1:ℝ) := by exact_mod_cast (show OptimizedFoldedPlan.ordinaryLength m+1≤13*(m+1) by omega)
  calc
    _ ≤32*(N:ℝ)*(OptimizedFoldedPlan.ordinaryLength m+1:ℝ)*(q:ℝ)*(((4:ℝ)^m)^E) := hb
    _ ≤32*(N:ℝ)*(13*(m+1:ℝ))*(q:ℝ)*(((4:ℝ)^m)^E) := by gcongr
    _ = _ := by ring

#print axioms cost_budget
#print axioms bank_sum
#print axioms eventual_band_budget
end
end ThinMatrix.HalfSourceBinarySourceRuntime
