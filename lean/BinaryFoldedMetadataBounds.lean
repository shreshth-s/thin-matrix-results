import BinaryFoldedFormationCost
import GlobalAddressBitBounds
import AdaptiveQueryBitBounds

/-! Public metadata caps for actual computed folded producers, derived from
phase geometry and original graph bounds rather than assumed final widths. -/
namespace ThinMatrix.BinaryFoldedMetadataBounds
open scoped BigOperators
open BinaryFoldedFormation BinaryFoldedFormationCost FoldedBackendExecution
open AdaptiveBitBounds GlobalAddressBitBounds StoredMinPlusAPSP
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
attribute [local irreducible] AlignedCertificate.R AlignedCertificate.S
  computedOuterConstant computedIndexConstant computedCyclicConstant

def metadataConstant : ℕ :=
  12*computedOuterConstant+computedCyclicConstant+34

def metadataWidth (n : ℕ) : ℕ := metadataConstant*(n.size+1)

private theorem affine_bound (a b C s : ℕ) (ha : a ≤ C) (hb : b ≤ C) :
    a*s+b ≤ C*(s+1) := by
  rw [Nat.mul_add,Nat.mul_one]
  exact Nat.add_le_add (Nat.mul_le_mul_right s ha) hb

theorem metadata_of_dimension_caps (n h d q block cN cD cq : ℕ)
    [NeZero d] (hn : 0<n) (hh : 0<h) (hb : block<CompactBlocks.blockCount n h)
    (hNsize : (outerSize n d).size ≤ cN*n.size+1)
    (hDsize : (middleSize h d).size ≤ cD*n.size+1)
    (hqsize : q.size ≤ cq*n.size+1) :
    MetadataBound n h d q block ((4*cN+4*cD+cq+10)*(n.size+1)) ∧
    (outerSize n d*middleSize h d).size ≤ (4*cN+4*cD+cq+10)*(n.size+1) := by
  let N:=outerSize n d
  let D:=middleSize h d
  let B:=(4*cN+4*cD+cq+10)*(n.size+1)
  have hd : 0<d:=Nat.pos_of_ne_zero (NeZero.ne d)
  have hwN : FoldedCounts.foldWidth d ≤ N:=Nat.le_mul_of_pos_left _ hn
  have hwidthsize : (FoldedCounts.foldWidth d).size ≤ cN*n.size+1:=
    (Nat.size_le_size hwN).trans hNsize
  have hdN : d ≤ N*N:=(FoldedCounts.modulus_fits (d:=d)).trans (Nat.mul_le_mul hwN hwN)
  have hdsize : d.size ≤ 2*cN*n.size+2 := by
    have hs:=(Nat.size_le_size hdN).trans (BinaryMultiplierAdapter.size_mul N N)
    dsimp only [N] at hs
    rw [Nat.mul_assoc]
    omega
  have hrawD : rawMiddle h d ≤ D:=rawMiddle_le h d
  have hrawsize : (rawMiddle h d).size ≤ cD*n.size+1:=(Nat.size_le_size hrawD).trans hDsize
  have hhD : h ≤ D:=(Nat.le_mul_of_pos_right h hd).trans hrawD
  have hhsize : h.size ≤ cD*n.size+1:=(Nat.size_le_size hhD).trans hDsize
  have hblocks : CompactBlocks.blockCount n h ≤ n := by
    unfold CompactBlocks.blockCount
    apply (ceilDiv_le_iff_le_smul hh).mpr
    exact Nat.le_mul_of_pos_left n hh
  have hbsize : block.size ≤ n.size:=Nat.size_le_size ((hb.trans_le hblocks).le)
  have hbacking : (N*D).size ≤ (cN+cD)*n.size+2 := by
    have hs:=BinaryMultiplierAdapter.size_mul N D
    dsimp only [N,D] at hs
    dsimp only [N,D]
    rw [Nat.add_mul]
    omega
  have hsmallN : n.size ≤ B := by
    simpa only [Nat.one_mul,Nat.add_zero] using
      affine_bound 1 0 (4*cN+4*cD+cq+10) n.size (by omega) (by omega)
  have hsmallOuter : cN*n.size+1 ≤ B := by
    exact affine_bound cN 1 _ _ (by omega) (by omega)
  have hsmallMiddle : cD*n.size+1 ≤ B := by
    exact affine_bound cD 1 _ _ (by omega) (by omega)
  have hsmallFold : 2*cN*n.size+2 ≤ B := by
    exact affine_bound (2*cN) 2 _ _ (by omega) (by omega)
  have hsmallCyclic : cq*n.size+1 ≤ B := by
    exact affine_bound cq 1 _ _ (by omega) (by omega)
  have hsmallBacking : (cN+cD)*n.size+2 ≤ B := by
    exact affine_bound (cN+cD) 2 _ _ (by omega) (by omega)
  exact ⟨⟨hsmallN,hhsize.trans hsmallMiddle,hdsize.trans hsmallFold,hqsize.trans hsmallCyclic,
    hbsize.trans hsmallN,hwidthsize.trans hsmallOuter,hNsize.trans hsmallOuter,
    hDsize.trans hsmallMiddle,hrawsize.trans hsmallMiddle⟩,hbacking.trans hsmallBacking⟩

private theorem matching_outer {R P n r S : ℕ}
    (call : PhaseGeometry.PhaseCall R P) (f : CompactBlocks.PhysicalFactorization r)
    (hfold : f.folded=call.folded S) :
    outerSize n (physicalFold f)=PhaseGeometry.outerSize call S n := by
  simp only [outerSize,physicalFold,PhaseGeometry.outerSize,PhaseGeometry.physicalFold,hfold]

private theorem size_le_of_pow_two {x e : ℕ} (hx : x ≤ 2^e) : x.size ≤ e+1 :=
  (Nat.size_le_size hx).trans_eq Nat.size_pow

private theorem middle_size_of_outer {n h d cN : ℕ} [NeZero d]
    (hn : 0<n) (hh : 0<h) (hhn : h≤n)
    (hN : (outerSize n d).size≤cN*n.size+1) :
    (middleSize h d).size≤(2*cN+6)*n.size+1 := by
  let N:=outerSize n d
  have hd : 0<d:=Nat.pos_of_ne_zero (NeZero.ne d)
  have hwN : FoldedCounts.foldWidth d≤N:=Nat.le_mul_of_pos_left _ hn
  have hdN : d≤N*N:=(FoldedCounts.modulus_fits (d:=d)).trans (Nat.mul_le_mul hwN hwN)
  have hdsize : d.size≤2*(cN*n.size)+2 := by
    have hs:=(Nat.size_le_size hdN).trans (BinaryMultiplierAdapter.size_mul N N)
    dsimp only [N] at hs
    omega
  have hp : middleSize h d≤4*h*d := by
    simpa only [middleSize,rawMiddle,Nat.mul_assoc] using
      PhaseGeometry.pad4_upper (h*d) (Nat.mul_pos hh hd)
  have hs1:=(Nat.size_le_size hp).trans (BinaryMultiplierAdapter.size_mul (4*h) d)
  have hs2:=BinaryMultiplierAdapter.size_mul 4 h
  have h4 : (4:ℕ).size=3 := by decide
  rw [h4] at hs2
  have hhs:=Nat.size_le_size hhn
  have hnsize : 1≤n.size:=Nat.size_pos.mpr hn
  rw [Nat.add_mul,Nat.mul_assoc]
  omega

theorem computed_metadata {n r : ℕ} (hn : 3 ≤ n)
    (call : ComputedPhaseGeometry.Call AlignedCertificate.R n)
    (f : CompactBlocks.PhysicalFactorization r)
    (hfold : f.folded=call.folded AlignedCertificate.S)
    (hcyclic : f.cyclic=call.cyclic AlignedCertificate.S)
    (b : Fin (CompactBlocks.blockCount n (ComputableParameters.block n))) :
    MetadataBound n (ComputableParameters.block n) (physicalFold f) f.cyclic b.val (metadataWidth n) ∧
    (outerSize n (physicalFold f)*middleSize (ComputableParameters.block n) (physicalFold f)).size ≤
      metadataWidth n := by
  let h:=ComputableParameters.block n
  let d:=physicalFold f
  have hNpow : outerSize n d≤2^(computedOuterConstant*n.size) := by
    rw [matching_outer call f hfold]
    exact computed_outer_le_pow_size n hn call
  have hNsize : (outerSize n d).size≤computedOuterConstant*n.size+1:=
    size_le_of_pow_two hNpow
  have hDsize : (middleSize h d).size≤(2*computedOuterConstant+6)*n.size+1:=
    middle_size_of_outer (by omega) (ComputedPhaseGeometry.block_pos n)
      (ComputableParameters.block_le_n n (by omega)) hNsize
  have hqsize : f.cyclic.size≤computedCyclicConstant*n.size+1 := by
    rw [hcyclic]
    exact size_le_of_pow_two (computed_cyclic_le_pow_size n hn call)
  have hcap:=metadata_of_dimension_caps n h d f.cyclic b.val computedOuterConstant
    (2*computedOuterConstant+6) computedCyclicConstant (by omega)
    (ComputedPhaseGeometry.block_pos n) b.isLt hNsize hDsize hqsize
  have hconstant : 4*computedOuterConstant+4*(2*computedOuterConstant+6)+computedCyclicConstant+10=
      metadataConstant := by unfold metadataConstant;omega
  simpa only [metadataWidth,hconstant] using hcap

/-- Every actual repeated-squaring callback supplies the original value
budget of the concrete binary boundary program. -/
theorem computed_apsp_call_formation_cost {n r : ℕ} {Payload : Type}
    (O : DenseOracle n Payload) (hO : DenseOracleCorrect O) (w : OptionalTable n)
    (W degree : ℕ) (hw : APSPReduction.EdgeBound (decode w) W) (hW : W ≤ n^degree)
    (c : Call n Payload) (hc : c ∈ (apsp O w W).calls) (hn : 3 ≤ n)
    (call : ComputedPhaseGeometry.Call AlignedCertificate.R n)
    (f : CompactBlocks.PhysicalFactorization r)
    (hfold : f.folded=call.folded AlignedCertificate.S)
    (hcyclic : f.cyclic=call.cyclic AlignedCertificate.S)
    (b : Fin (CompactBlocks.blockCount n (ComputableParameters.block n))) :
    (encodeInputs c.left c.right c.target).bitSteps+
      (formSources f b (encodeInputs c.left c.right c.target).value).bitSteps ≤
      10000000000000*((degree+1)*n.size+7+metadataWidth n+10)^3*
        (n^2+2*f.cyclic*outerSize n (physicalFold f)*middleSize (ComputableParameters.block n) (physicalFold f)) := by
  have hm:=computed_metadata hn call f hfold hcyclic b
  have hb:=AdaptiveQueryBitBounds.apsp_call_components_size O hO w W degree hw hW c hc
  exact encode_and_formSources_cost f b c.left c.right c.target hm.1 hb.1 hb.2.1 hb.2.2
    (by omega) (Nat.pos_of_ne_zero (NeZero.ne _)) f.cyclic_pos hm.2

end
end ThinMatrix.BinaryFoldedMetadataBounds

#print axioms ThinMatrix.BinaryFoldedMetadataBounds.computed_metadata
#print axioms ThinMatrix.BinaryFoldedMetadataBounds.computed_apsp_call_formation_cost
