import HalfSourceDirectSetup
import HalfSourceEncodedBandCost
import GraphSharedSourceProduction

namespace ThinMatrix.HalfSourceSharedSourceBudget
open HalfSourceParameters
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 12000
noncomputable section

variable {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
  (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f)

def bands : ℕ := TilingCosts.bandCount p.N (ThinMatrixBackend.tileWidth p.L p.m)
def copyBudget : ℕ := 2*((BackendScalarBits.backendScalarUnit 1+9)*f.cyclic+24)*(ThinMatrixBackend.tileWidth p.L p.m*4^p.m)
def common : ℕ := HalfSourceDirectSetup.budget p.L p.m f.cyclic+
  HalfSourceRootSetupCost.budget p.m f.cyclic+HalfSourceEncodedProduction.budget p.m f.cyclic

theorem copies (hm : p.m ≤ p.L) (hfit : ThinProductCosts.gridSide p.L p.m ≤ p.N) :
    bands f p*copyBudget f p ≤ 13000*f.cyclic*p.N*4^p.m := by
  have ht := (BackendCostRefinement.tileWidth_comparison p.L p.m).1.trans hfit
  have hb := TilingCosts.padding_upper p.N (ThinMatrixBackend.tileWidth p.L p.m)
    (ThinMatrixBackend.tileWidth_pos p.L p.m hm) ht
  change bands f p*ThinMatrixBackend.tileWidth p.L p.m ≤ 2*p.N at hb
  have hq := f.cyclic_pos
  have hu : 2*((BackendScalarBits.backendScalarUnit 1+9)*f.cyclic+24)≤6500*f.cyclic := by
    norm_num[BackendScalarBits.backendScalarUnit,BackendScalarBits.scalarUnit] at ⊢
    omega
  calc
    _ ≤ bands f p*((6500*f.cyclic)*(ThinMatrixBackend.tileWidth p.L p.m*4^p.m)) := by
      unfold copyBudget
      exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hu)
    _ =6500*f.cyclic*(bands f p*ThinMatrixBackend.tileWidth p.L p.m)*4^p.m := by ring
    _ ≤6500*f.cyclic*(2*p.N)*4^p.m := by gcongr
    _ =_ := by ring

def foldedBudget (W V : ℕ) : ℕ := 6000000000000*(W+V+10)^3*f.cyclic*p.N*p.D

theorem block (hm : p.m ≤ p.L-p.m) (b : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (W V : ℕ)
    (hb : BinaryFoldedFormationCost.MetadataBound n h (FoldedBackendExecution.physicalFold f) f.cyclic b.val V)
    (ha : BinaryFoldedFormationCost.TableBound W input.left) (hc : BinaryFoldedFormationCost.TableBound W input.right)
    (hn : 0 < n) (hd : 0 < FoldedBackendExecution.physicalFold f) (hbacking : (p.N*p.D).size ≤ V)
    (hL : p.L=OptimizedFoldedPlan.ordinaryLength p.m) (ht : p.t=OptimizedFoldedPlan.channelLength p.m)
    (hm0 : 0 < p.m) (hfit : ThinProductCosts.gridSide p.L p.m ≤ p.N) :
    (∑ a : Fin (bands f p), GraphAdaptiveSourceBank.preparationRecorded f p
      (GraphAdaptivePrefix.fromInputs f p hm b input a.val a.val (HalfSourceSuffixChoice.limit p.m (p.L-p.m))))≤
      bands f p*(common f p+foldedBudget f p W V)+13000*f.cyclic*p.N*4^p.m := by
  have hh : ∀ a : Fin (bands f p), GraphAdaptiveSourceBank.preparationRecorded f p
      (GraphAdaptivePrefix.fromInputs f p hm b input a.val a.val (HalfSourceSuffixChoice.limit p.m (p.L-p.m)))≤
      common f p+foldedBudget f p W V+copyBudget f p := by
    intro a
    have he := HalfSourceDirectSetup.actual f p hm b input a.val a.val hL ht hm0
    have hf := HalfSourceFoldedSetupCost.cost_bound f p b input a.val a.val W V hb ha hc hn hd hbacking
    unfold common foldedBudget copyBudget
    omega
  have hs := Finset.sum_le_sum (s:=Finset.univ) (fun a _=>hh a)
  simp only[Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] at hs
  have hc := copies f p (by omega) hfit
  nlinarith only[hs,hc]

def budget (W V : ℕ) : ℕ := HalfSourceCapSetup.bitBudget p.m (p.L-p.m)+
  CompactBlocks.blockCount n h*(bands f p*(common f p+foldedBudget f p W V)+13000*f.cyclic*p.N*4^p.m)+
  24*bands f p*CompactBlocks.blockCount n h+8*bands f p+8

theorem actual (hm : p.m ≤ p.L-p.m) (input : BinaryFoldedFormation.Inputs n) (W V : ℕ)
    (hb : ∀ b : Fin (CompactBlocks.blockCount n h), BinaryFoldedFormationCost.MetadataBound n h (FoldedBackendExecution.physicalFold f) f.cyclic b.val V)
    (ha : BinaryFoldedFormationCost.TableBound W input.left) (hc : BinaryFoldedFormationCost.TableBound W input.right)
    (hn : 0 < n) (hd : 0 < FoldedBackendExecution.physicalFold f) (hbacking : (p.N*p.D).size ≤ V)
    (hL : p.L=OptimizedFoldedPlan.ordinaryLength p.m) (ht : p.t=OptimizedFoldedPlan.channelLength p.m)
    (hm0 : 0 < p.m) (hfit : ThinProductCosts.gridSide p.L p.m ≤ p.N) :
    (GraphSharedSourceProduction.execute f p hm input (S:=bands f p)).operations ≤ budget f p W V := by
  rw[GraphSharedSourceProduction.work,Finset.sum_comm]
  have hs := Finset.sum_le_sum (s:=Finset.univ) (fun b _=>block f p hm b input W V (hb b) ha hc hn hd hbacking hL ht hm0 hfit)
  simp only[Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] at hs
  have hc := HalfSourceCapSetup.execute_bits p.m (p.L-p.m)
  unfold budget
  omega

#print axioms copies
#print axioms block
#print axioms actual
end
end ThinMatrix.HalfSourceSharedSourceBudget
