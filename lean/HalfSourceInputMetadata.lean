import HalfSourceAddressGeometry
import BinaryFoldedMetadataBounds
import BinaryTriangleCosts
import BinaryAPSPPublicCostBounds

set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxRecDepth 10000
namespace ThinMatrix.HalfSourceInputMetadata
open HalfSourceBatchFit HalfSourceAddressGeometry BinaryTriangleExecution
noncomputable section
attribute [local irreducible] shapeConstant HalfSourceBatchFit.block HalfSourceBatchFit.R

def metadataCoefficient : ℕ := 13*shapeConstant+14
def metadataWidth (n : ℕ) := metadataCoefficient*(n.size+1)
def inputWidth (n κ : ℕ) := κ*n.size+1

 theorem input_bounds {n κ : ℕ} (X Y T : IntTable n)
    (hc : CountedEndToEndAPSP.entryQueryBound (viewTable X) (viewTable Y) (viewTable T) ≤ n^κ) :
    BinaryFoldedFormationCost.TableBound (inputWidth n κ) X ∧
    BinaryFoldedFormationCost.TableBound (inputWidth n κ) Y ∧
    BinaryFoldedFormationCost.TableBound (inputWidth n κ) T :=
  BinaryTriangleCosts.inputBits_of_polynomial_entry_cap X Y T le_rfl hc

 theorem metadata (n : ℕ) (call : Call n) (hn : 3 ≤ n)
    (hv : EndToEndAPSP.ValidFactors call.factors)
    (j : Fin (CompactBlocks.blockCount n (block n))) :
    let out := HalfSourceDispatch.prepare n (block n) call.factors hv
    BinaryFoldedFormationCost.MetadataBound n (block n)
      (FoldedBackendExecution.physicalFold out.split.plan) out.split.plan.cyclic j.val (metadataWidth n) ∧
      (out.plan.value.N*out.plan.value.D).size ≤ metadataWidth n := by
  let out := HalfSourceDispatch.prepare n (block n) call.factors hv
  let f := out.split.plan
  let p := out.plan.value
  have hw := shape_width n call hn hv
  change GraphOwnBandShapeBounds.width f p ≤ shapeConstant*n.size at hw
  have hN : p.N.size ≤ shapeConstant*n.size := by unfold GraphOwnBandShapeBounds.width at hw;omega
  have hm : p.m ≤ shapeConstant*n.size := by unfold GraphOwnBandShapeBounds.width at hw;omega
  have hq : f.cyclic.size ≤ shapeConstant*n.size := by unfold GraphOwnBandShapeBounds.width at hw;omega
  have hD : p.D.size ≤ (2*shapeConstant)*n.size+1 := by
    have hs := Nat.size_le_size p.middle_fit
    rw [show (4:ℕ)=2^2 by decide,←pow_mul,Nat.size_pow] at hs
    nlinarith
  have hb := BinaryFoldedMetadataBounds.metadata_of_dimension_caps n (block n)
    (FoldedBackendExecution.physicalFold f) f.cyclic j.val shapeConstant (2*shapeConstant) shapeConstant
    (by omega) (block_pos n) j.isLt
    (by rw [←p.N_eq];omega) (by rw [←p.D_eq];exact hD) (by omega)
  have he : 4*shapeConstant+4*(2*shapeConstant)+shapeConstant+10 ≤ metadataCoefficient := by
    unfold metadataCoefficient;omega
  have hwidth : (4*shapeConstant+4*(2*shapeConstant)+shapeConstant+10)*(n.size+1) ≤ metadataWidth n :=
    Nat.mul_le_mul_right _ he
  rcases hb with ⟨hb,hback⟩
  dsimp only
  refine ⟨⟨hb.n_size.trans hwidth,hb.h_size.trans hwidth,hb.d_size.trans hwidth,
    hb.q_size.trans hwidth,hb.block_size.trans hwidth,hb.width_size.trans hwidth,
    hb.outer_size.trans hwidth,hb.middle_size.trans hwidth,hb.raw_size.trans hwidth⟩,?_⟩
  change (p.N*p.D).size ≤ _
  rw [p.N_eq,p.D_eq]
  exact hback.trans hwidth

 theorem blocks_positive {n h : ℕ} (hn : 0<n) (hh : 0<h) :
    0<CompactBlocks.blockCount n h := by
  have hf := CompactBlocks.block_fit n h hh
  by_contra he
  have hz : CompactBlocks.blockCount n h=0 := by omega
  rw [hz,zero_mul] at hf
  omega

 theorem metadata_zero (n : ℕ) (call : Call n) (hn : 3 ≤ n)
    (hv : EndToEndAPSP.ValidFactors call.factors) :
    let out := HalfSourceDispatch.prepare n (block n) call.factors hv
    BinaryFoldedFormationCost.MetadataBound n (block n)
      (FoldedBackendExecution.physicalFold out.split.plan) out.split.plan.cyclic 0 (metadataWidth n) :=
  (metadata n call hn hv ⟨0,blocks_positive (by omega) (block_pos n)⟩).1

 theorem widths_log (n κ : ℕ) (hn : 3 ≤ n) :
    (metadataWidth n:ℝ) ≤ (5*metadataCoefficient:ℝ)*Real.log (n:ℝ) ∧
    (inputWidth n κ:ℝ) ≤ (5*(κ+1):ℝ)*Real.log (n:ℝ) := by
  have hs := BinaryAPSPPublicCostBounds.size_add_one_le_log n hn
  push_cast at hs
  constructor
  · unfold metadataWidth
    push_cast
    nlinarith [Nat.cast_nonneg (α:=ℝ) metadataCoefficient]
  · have hi : inputWidth n κ ≤ (κ+1)*(n.size+1) := by unfold inputWidth;nlinarith
    have hr : (inputWidth n κ:ℝ) ≤ (κ+1:ℝ)*(n.size+1:ℝ) := by exact_mod_cast hi
    nlinarith [Nat.cast_nonneg (α:=ℝ) κ]

#print axioms input_bounds
#print axioms metadata
#print axioms blocks_positive
#print axioms metadata_zero
#print axioms widths_log
end
end ThinMatrix.HalfSourceInputMetadata
