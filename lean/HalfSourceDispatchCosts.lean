import HalfSourceInputMetadata
import HalfSourceComputedCosts

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
namespace ThinMatrix.HalfSourceDispatchCosts
open scoped BigOperators
open FoldedBackendExecution BinaryTriangleSetupCosts HalfSourceBatchFit
noncomputable section
attribute [local irreducible] HalfSourceBatchFit.R HalfSourceBatchFit.S HalfSourceBatchFit.block

 theorem setup_sites {n h r : ℕ} (hn : 0<n) (hh : 0<h)
    (f : CompactBlocks.PhysicalFactorization r) :
    (HalfSourcePlanExecution.preparePlan n h f).sites ≤
      157*(f.cyclic*outerSize n (physicalFold f)*middleSize h (physicalFold f)) := by
  let D := middleSize h (physicalFold f)
  let N := outerSize n (physicalFold f)
  let X := f.cyclic*N*D
  have hD : 0<D := by dsimp[D];rw[middleSize_eq];positivity
  have hN : 0<N := by dsimp[N,outerSize,FoldedCounts.foldWidth];positivity
  have hraw : h*(3*f.folded) ≤ D := rawMiddle_le h (physicalFold f)
  have hd : 3*f.folded ≤ D := (Nat.le_mul_of_pos_left _ hh).trans hraw
  have hsize : (h*(3*f.folded)).size ≤ D :=
    (Nat.size_le.mpr Nat.lt_two_pow_self).trans hraw
  have hm : (HalfSourcePlanExecution.preparePlan n h f).value.m ≤ D := by
    rw[HalfSourcePlanExecution.preparePlan_m]
    exact (clog4_le_size _).trans hsize
  have hq : f.cyclic.size ≤ f.cyclic := Nat.size_le.mpr Nat.lt_two_pow_self
  have hDX : D ≤ X := by
    calc
      D ≤ N*D := Nat.le_mul_of_pos_left _ hN
      _ ≤ f.cyclic*(N*D) := Nat.le_mul_of_pos_left _ f.cyclic_pos
      _ = X := by dsimp[X];ring
  have hqX : f.cyclic ≤ X :=
    (Nat.le_mul_of_pos_right _ hN).trans (Nat.le_mul_of_pos_right _ hD)
  have hX : 1 ≤ X := hD.trans_le hDX
  have hs := HalfSourcePlanExecution.preparePlan_sites n h f
  change _ ≤ 157*X
  omega

 def metadataCoefficient (R : ℕ) := 256*(R+2)^3+400

 theorem metadata_bound {n h : ℕ} (hn : 0<n) (hh : 0<h)
    (selected : List ℕ) (candidate R : ℕ)
    (hv : EndToEndAPSP.ValidFactors (selected++[candidate]))
    (hlen : (selected++[candidate]).length ≤ R) :
    let out := HalfSourceDispatch.prepare n h (selected++[candidate]) hv
    BinaryTriangleExecution.historySites selected+(FactorValidation.validate (selected++[candidate])).2+
      out.split.work+out.plan.sites+32 ≤
      metadataCoefficient R*(out.split.plan.cyclic*out.plan.value.N*out.plan.value.D) := by
  let factors := selected++[candidate]
  let out := HalfSourceDispatch.prepare n h factors hv
  let f := out.split.plan
  let p := out.plan.value
  let X := f.cyclic*p.N*p.D
  have hD : 0<p.D := by rw[p.D_eq,middleSize_eq];positivity
  have hN : 0<p.N := by rw[p.N_eq];unfold outerSize FoldedCounts.foldWidth;positivity
  have hX : 1 ≤ X := Nat.mul_pos (Nat.mul_pos f.cyclic_pos hN) hD
  have hfold : f.folded ≤ p.D := by
    have hd : f.folded ≤ h*(3*f.folded) := by nlinarith only[hh]
    exact hd.trans (by rw[p.D_eq];exact rawMiddle_le h (physicalFold f))
  have hprod : factors.prod ≤ X := by
    rw[←f.product]
    have hd := Nat.mul_le_mul_right f.cyclic hfold
    have hnX := Nat.mul_le_mul_left (f.cyclic*p.D) (show 1 ≤ p.N from hN)
    dsimp[X]
    nlinarith only[hd,hnX]
  have hv0 := FactorValidation.validate_work_product factors hv
  have hlen' : factors.length ≤ R := hlen
  have hv1 : (FactorValidation.validate factors).2 ≤ 32*(R+2)^3*X :=
    hv0.trans (Nat.mul_le_mul (Nat.mul_le_mul_left 32 (Nat.pow_le_pow_left (by omega) 3)) hprod)
  have hs : out.split.work=8*factors.length+1 := FactorValidation.splitProducts_work _ factors
  have hp : out.plan.sites ≤ 157*X := by
    have hp := setup_sites hn hh f
    change (HalfSourcePlanExecution.preparePlan n h f).sites ≤ _ at hp
    change out.plan.sites ≤ 157*(f.cyclic*p.N*p.D)
    rw[p.N_eq,p.D_eq]
    exact hp
  have hhist : BinaryTriangleExecution.historySites selected ≤ 8*(R+1)+20 := by
    unfold BinaryTriangleExecution.historySites
    simp only[List.length_append,List.length_singleton] at hlen
    omega
  have hpoly : 1 ≤ (R+2)^3 ∧ R+1 ≤ (R+2)^3 := by
    constructor
    · exact one_le_pow₀ (by omega)
    · exact (show R+1 ≤ R+2 by omega).trans (le_self_pow₀ (by omega) (by decide))
  have hmisc : BinaryTriangleExecution.historySites selected+out.split.work+32 ≤ 100*(R+2)^3*X := by
    have hscale := Nat.mul_le_mul_left (100*(R+2)^3) hX
    rw[hs]
    nlinarith only[hhist,hlen',hpoly.1,hpoly.2,hscale]
  dsimp only
  change BinaryTriangleExecution.historySites selected+(FactorValidation.validate factors).2+
    out.split.work+out.plan.sites+32 ≤ metadataCoefficient R*X
  unfold metadataCoefficient
  nlinarith only[hv1,hp,hmisc]

 theorem formation_phase (n : ℕ) (call : Call n) (hn : 3 ≤ n)
    (hv : EndToEndAPSP.ValidFactors call.factors) :
    let out := HalfSourceDispatch.prepare n (block n) call.factors hv
    (out.split.plan.cyclic:ℝ)*out.plan.value.N*out.plan.value.D ≤
      HalfSourceComputedCosts.phaseRawSum n call := by
  have ha := HalfSourceDispatch.actual_phase n call hv
  dsimp only at ha ⊢
  rw[ha.2.1,ha.2.2.2.1,ha.2.2.2.2]
  let B := blocks n
  let X : ℝ := (call.cyclic S:ℝ)*(HalfSourceBatchGeometry.outer n call:ℝ)*(dimension n call:ℝ)
  let total : ℝ := ∑ i : Fin 7,HalfSourceRawCosts.rawTerm n
    (HalfSourceBatchGeometry.outer n call) (dimension n call) (call.cyclic S) i
  have hx0 : 0 ≤ X := by dsimp[X];positivity
  have ht : X ≤ total := by
    have h := Finset.single_le_sum (fun i _=>HalfSourceRawCosts.rawTerm_nonneg
      (n:ℝ) (HalfSourceBatchGeometry.outer n call) (dimension n call) (call.cyclic S)
      (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _) i) (Finset.mem_univ (6:Fin 7))
    change X ≤ total at h
    exact h
  have hB : (1:ℝ) ≤ B := by
    exact_mod_cast HalfSourceInputMetadata.blocks_positive (show 0<n by omega) (block_pos n)
  have hs : X ≤ (B:ℝ)*X := by simpa only[one_mul] using mul_le_mul_of_nonneg_right hB hx0
  exact hs.trans (mul_le_mul_of_nonneg_left ht (Nat.cast_nonneg B))

#print axioms setup_sites
#print axioms metadata_bound
#print axioms formation_phase
end
end ThinMatrix.HalfSourceDispatchCosts
