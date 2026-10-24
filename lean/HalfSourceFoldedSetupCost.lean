import HalfSourceBandVolume
import HalfSourceRootPolynomials
import BinaryFoldedFormationCost
import GraphAdaptiveSourceBank

/-! The present diagonal source preparation repeats physical folded-array
formation. Charge every repetition: its extra cost fits the existing box
monomial by T>1+G, with all original-input and metadata widths explicit. -/
namespace ThinMatrix.HalfSourceFoldedSetupCost
open HalfSourceParameters
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

theorem exponent_gap : 1+G<T := by linarith [TEnclosure.1,GEnclosure.2]

theorem band_formation (N m q : ℕ) (hm : 0 < m)
    (hfit : ThinProductCosts.gridSide (OptimizedFoldedPlan.ordinaryLength m) m≤N) :
    (TilingCosts.bandCount N (ThinMatrixBackend.tileWidth (OptimizedFoldedPlan.ordinaryLength m) m):ℝ)*
      ((q:ℝ)*(N:ℝ)*(4:ℝ)^m)≤416*(q:ℝ)*(N:ℝ)^2*(m+1:ℝ)*(((4:ℝ)^m)^(-G)) := by
  have hd : 1≤(4:ℝ)^m := one_le_pow₀ (by norm_num)
  have he : (4:ℝ)^m≤((4:ℝ)^m)^(T+(-G)) := by
    calc
      _ = ((4:ℝ)^m)^(1:ℝ) := (Real.rpow_one _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hd (by linarith [exponent_gap])
  have hv := mul_le_mul_of_nonneg_left he (show 0≤(q:ℝ)*(N:ℝ) by positivity)
  have hh := HalfSourceBandVolume.transfer N m hm hfit ((q:ℝ)*(N:ℝ)) _ (-G) (by positivity) hv
  have hL := HalfSourceRootPolynomials.ordinary_bound m
  have hsize : (OptimizedFoldedPlan.ordinaryLength m+1:ℝ)≤13*(m+1:ℝ) := by
    exact_mod_cast (show OptimizedFoldedPlan.ordinaryLength m+1≤13*(m+1) by omega)
  calc
    _ ≤32*(N:ℝ)*(OptimizedFoldedPlan.ordinaryLength m+1:ℝ)*((q:ℝ)*(N:ℝ))*(((4:ℝ)^m)^(-G)) := hh
    _ ≤32*(N:ℝ)*(13*(m+1:ℝ))*((q:ℝ)*(N:ℝ))*(((4:ℝ)^m)^(-G)) := by gcongr
    _ = _ := by ring

variable {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
  (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f)
  (block : Fin (CompactBlocks.blockCount n h)) (input : BinaryFoldedFormation.Inputs n)

def cost (a b : ℕ) : ℕ := (ExactHalfGraphSources.execute f p block input a b).folded.bitSteps

theorem cost_bound (a b W B : ℕ)
    (hb : BinaryFoldedFormationCost.MetadataBound n h (FoldedBackendExecution.physicalFold f) f.cyclic block.val B)
    (ha : BinaryFoldedFormationCost.TableBound W input.left) (hc : BinaryFoldedFormationCost.TableBound W input.right)
    (hn : 0 < n) (hd : 0 < FoldedBackendExecution.physicalFold f)
    (hbacking : (p.N*p.D).size≤B) :
    cost f p block input a b≤6000000000000*(W+B+10)^3*f.cyclic*p.N*p.D := by
  have hh := BinaryFoldedFormationCost.formSources_cost f block input hb ha hc hn hd f.cyclic_pos
    (by simpa only [← p.N_eq,← p.D_eq] using hbacking)
  unfold cost ExactHalfGraphSources.execute
  simp only [BinaryFoldedFormation.formSourcesCached_refines]
  rw [← p.N_eq,← p.D_eq] at hh
  exact hh.trans_eq (by ring)

theorem bank_bound {K : ℕ} (ids : Vector ℕ K) (W B : ℕ)
    (hb : BinaryFoldedFormationCost.MetadataBound n h (FoldedBackendExecution.physicalFold f) f.cyclic block.val B)
    (ha : BinaryFoldedFormationCost.TableBound W input.left) (hc : BinaryFoldedFormationCost.TableBound W input.right)
    (hn : 0 < n) (hd : 0 < FoldedBackendExecution.physicalFold f)
    (hbacking : (p.N*p.D).size≤B) :
    (∑ i,cost f p block input (ids.get i) (ids.get i))≤
      K*(6000000000000*(W+B+10)^3*f.cyclic*p.N*p.D) := by
  have hs := Finset.sum_le_sum (s:=Finset.univ) (fun (i : Fin K) _ => cost_bound f p block input (ids.get i) (ids.get i) W B hb ha hc hn hd hbacking)
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] using hs

theorem actual_bank_cost
    (ids : Vector ℕ (TilingCosts.bandCount p.N (ThinMatrixBackend.tileWidth p.L p.m))) (W B : ℕ)
    (hb : BinaryFoldedFormationCost.MetadataBound n h (FoldedBackendExecution.physicalFold f) f.cyclic block.val B)
    (ha : BinaryFoldedFormationCost.TableBound W input.left) (hc : BinaryFoldedFormationCost.TableBound W input.right)
    (hn : 0 < n) (hd : 0 < FoldedBackendExecution.physicalFold f)
    (hbacking : (p.N*p.D).size≤B) (hm : 0 < p.m)
    (hL : p.L=OptimizedFoldedPlan.ordinaryLength p.m)
    (hfit : ThinProductCosts.gridSide p.L p.m≤p.N) :
    (((∑ i,cost f p block input (ids.get i) (ids.get i)):ℕ):ℝ)≤
      10000000000000000*(W+B+10:ℝ)^3*(f.cyclic:ℝ)*(p.N:ℝ)^2*(p.m+1:ℝ)*(((4:ℝ)^p.m)^(-G)) := by
  have hs := bank_bound f p block input ids W B hb ha hc hn hd hbacking
  have hsR : (((∑ i,cost f p block input (ids.get i) (ids.get i)):ℕ):ℝ)≤
    (TilingCosts.bandCount p.N (ThinMatrixBackend.tileWidth p.L p.m):ℝ)*
      (6000000000000*(W+B+10:ℝ)^3*(f.cyclic:ℝ)*(p.N:ℝ)*(p.D:ℝ)) := by exact_mod_cast hs
  have hD : (p.D:ℝ)≤(4:ℝ)^p.m := by exact_mod_cast p.middle_fit
  have hbnd := band_formation p.N p.m f.cyclic hm (by simpa only [← hL] using hfit)
  rw [← hL] at hbnd
  have hh := mul_le_mul_of_nonneg_left hbnd (show 0≤6000000000000*(W+B+10:ℝ)^3 by positivity)
  calc
    _ ≤(TilingCosts.bandCount p.N (ThinMatrixBackend.tileWidth p.L p.m):ℝ)*
      (6000000000000*(W+B+10:ℝ)^3*(f.cyclic:ℝ)*(p.N:ℝ)*(p.D:ℝ)) := hsR
    _ ≤(TilingCosts.bandCount p.N (ThinMatrixBackend.tileWidth p.L p.m):ℝ)*
      (6000000000000*(W+B+10:ℝ)^3*(f.cyclic:ℝ)*(p.N:ℝ)*(4:ℝ)^p.m) := by gcongr
    _ ≤(6000000000000*416)*(W+B+10:ℝ)^3*(f.cyclic:ℝ)*(p.N:ℝ)^2*(p.m+1:ℝ)*(((4:ℝ)^p.m)^(-G)) := by
      ring_nf at hh ⊢
      exact hh
    _ ≤ _ := by gcongr;norm_num

#print axioms exponent_gap
#print axioms band_formation
#print axioms cost_bound
#print axioms bank_bound
#print axioms actual_bank_cost
end
end ThinMatrix.HalfSourceFoldedSetupCost
