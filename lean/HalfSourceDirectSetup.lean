import HalfSourceSelectorTotal
import HalfSourceEncodedProduction
import HalfSourceRootRuntime
import HalfSourceFoldedSetupCost

/-! Every repeated public shape and exact-half selector is charged together
with the actual dense translated source families. Their strict source gap
allows arbitrary fixed polynomial metadata overhead. -/
namespace ThinMatrix.HalfSourceDirectSetup
open HalfSourceParameters HalfSourceAdaptiveFamilyCost
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 12000
noncomputable section

 def budget (L m q : ℕ) : ℕ :=
  300000000000000000000*(L+m+1)^14*q*12^L*2^(L-m)

 theorem shape_selector_source (L m q : ℕ) (hm : 4*m≤L) (hq : 1≤q) :
    (BinaryBackendExecution.prepareShapeRuntime L m).operations+
      (ExactHalfSourcePlan.prepare (BinaryBackendExecution.prepareShapeRuntime L m)).bitSteps+
      (ExactHalfSourcePlan.prepare (BinaryBackendExecution.prepareShapeRuntime L m)).control+
      ExactHalfBandSources.familiesBudget L m q 1≤budget L m q := by
  let P := L+m+1
  let U := q*12^L*2^(L-m)
  have hP : 1≤P := by dsimp[P];omega
  have hs := BackendCostRefinement.BandShapeCosts.prepareShape_polynomial L m q (by omega) hq
  have ht := HalfSourceSelectorTotal.actual (BinaryBackendExecution.prepareShapeRuntime L m) (by omega)
  have hf := HalfSourceBinarySourceCosts.families_polynomial L m q hm hq
  have hs' : (BinaryBackendExecution.prepareShapeRuntime L m).operations≤50000*P^14*U := by
    rw[BinaryBackendExecution.prepareShapeRuntime_refines]
    calc
      _ ≤50000*P^6*U := by simpa only[P,U,mul_assoc] using hs
      _ ≤_ := by gcongr;decide
  have ht' : (ExactHalfSourcePlan.prepare (BinaryBackendExecution.prepareShapeRuntime L m)).bitSteps+
      (ExactHalfSourcePlan.prepare (BinaryBackendExecution.prepareShapeRuntime L m)).control≤200000000000000000000*P^14*U := by
    calc
      _ ≤200000000000000000000*P^14*12^L*2^(L-m) := ht
      _ ≤200000000000000000000*P^14*q*12^L*2^(L-m) := by nlinarith only[Nat.mul_le_mul_left (200000000000000000000*P^14*12^L*2^(L-m)) hq]
      _ =_ := by dsimp[U];ring
  have hf' : ExactHalfBandSources.familiesBudget L m q 1≤10000000000000000*P^14*U := by simpa only[P,U,mul_assoc] using hf
  unfold budget
  change _≤300000000000000000000*P^14*q*12^L*2^(L-m)
  calc
    _ ≤300000000000000000000*P^14*U := by nlinarith only[hs',ht',hf',show 0≤P^14*U by omega]
    _ =_ := by dsimp[U];ring

 theorem eventual_budget_fit : ∀ᶠ m : ℕ in Filter.atTop, ∀ q : ℕ,
    (budget (L m) m q:ℝ)≤(q:ℝ)*(((4:ℝ)^m)^(T+E)) := by
  have hf := HalfSourceSourceCosts.eventual_polynomial_source_fit 14
    (300000000000000000000*(14:ℝ)^14) (by positivity)
  filter_upwards [hf] with m hm
  intro q
  have hL := HalfSourceRootPolynomials.ordinary_bound m
  have hshape : (L m+m+1:ℕ)≤14*(m+1) := by dsimp[L];omega
  have hcEq : OptimizedFoldedPlan.c=c := by norm_num[OptimizedFoldedPlan.c,c]
  rw[←hcEq,←OptimizedFoldedPlan.ordinaryLength_eq] at hm
  unfold budget
  push_cast
  calc
    _ ≤300000000000000000000*(14*(m+1:ℝ))^14*(q:ℝ)*12^(L m)*2^(L m-m) := by gcongr;exact_mod_cast hshape
    _ =(q:ℝ)*((300000000000000000000*(14:ℝ)^14)*(m+1:ℝ)^14*12^(L m)*2^(L m-m)) := by ring
    _ ≤_ := mul_le_mul_of_nonneg_left hm (Nat.cast_nonneg q)

variable {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
  (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f)

 theorem actual (hm : p.m≤p.L-p.m) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (a b : ℕ)
    (hL : p.L=OptimizedFoldedPlan.ordinaryLength p.m)
    (ht : p.t=OptimizedFoldedPlan.channelLength p.m) (hm0 : 0 < p.m) :
    GraphAdaptiveSourceBank.preparationRecorded f p
      (GraphAdaptivePrefix.fromInputs f p hm block input a b (HalfSourceSuffixChoice.limit p.m (p.L-p.m)))≤
      budget p.L p.m f.cyclic+
      HalfSourceFoldedSetupCost.cost f p block input a b+
      2*((BackendScalarBits.backendScalarUnit 1+9)*f.cyclic+24)*(ThinMatrixBackend.tileWidth p.L p.m*4^p.m)+
      HalfSourceRootSetupCost.budget p.m f.cyclic+HalfSourceEncodedProduction.budget p.m f.cyclic := by
  have h4 : 4*p.m≤p.L := by
    have h := (OptimizedFoldedPlan.rounded_bounds p.m).1
    rw[←hL] at h
    norm_num[OptimizedFoldedPlan.c] at h
    exact_mod_cast(show (4:ℝ)*p.m≤p.L by linarith[Nat.cast_nonneg (α:=ℝ) p.m])
  have hs := shape_selector_source p.L p.m f.cyclic h4 f.cyclic_pos
  have hsource := ExactHalfGraphSources.sources_work f p block input a b
  have hb := ExactHalfGraphSources.band_copy_work f p block input a b
  have hr := HalfSourceRootRuntime.cost_budget f p block input a b hL ht
  have he := HalfSourceEncodedProduction.actual f p hm block input a b hL ht hm0
  unfold GraphAdaptiveSourceBank.preparationRecorded GraphAdaptivePrefix.fromInputs
  dsimp only
  unfold HalfSourceRootRuntime.cost at hr
  unfold HalfSourceFoldedSetupCost.cost
  change _≤_ at he
  simp only[GraphAdaptivePrefix.fromInputs,GraphResidualFamilies.fromInputs,ExactHalfGraphSources.execute] at hs hsource hb hr he ⊢
  omega

#print axioms shape_selector_source
#print axioms eventual_budget_fit
#print axioms actual
end
end ThinMatrix.HalfSourceDirectSetup
