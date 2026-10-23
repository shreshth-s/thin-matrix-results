import FoldedBandTransport

set_option autoImplicit false
set_option maxRecDepth 6000
set_option maxHeartbeats 2000000

/-! Original folded request identities, count bounds, and unique band tags.
These facts concern each request occurrence, including equal-valued requests. -/
namespace ThinMatrix.FoldedRequestBounds
open BinaryCell ThinMatrixBackend FoldedBandTransport
variable {n h r : ℕ}

noncomputable def count (f : CompactBlocks.PhysicalFactorization r)
    (block : Fin (CompactBlocks.blockCount n h)) (input : BinaryFoldedFormation.Inputs n)
    (index : Fin (FoldedBackendExecution.windowQuerySize n)) : ℤ :=
  let x := (FoldedBackendExecution.windowQueryEquiv n).symm index
  FoldedBackendExecution.semanticCoefficient f block (BinaryFoldedFormation.viewTable input.left)
    (BinaryFoldedFormation.viewTable input.right) (BinaryFoldedFormation.viewTable input.target) x.1.1 x.1.2 x.2

theorem count_nonnegative (f : CompactBlocks.PhysicalFactorization r)
    (block : Fin (CompactBlocks.blockCount n h)) (input : BinaryFoldedFormation.Inputs n)
    (index : Fin (FoldedBackendExecution.windowQuerySize n)) : 0≤count f block input index := by
  unfold count
  rw [FoldedBackendExecution.semanticCoefficient_count]
  exact Nat.cast_nonneg _

theorem count_bound (f : CompactBlocks.PhysicalFactorization r)
    (block : Fin (CompactBlocks.blockCount n h)) (input : BinaryFoldedFormation.Inputs n)
    (index : Fin (FoldedBackendExecution.windowQuerySize n)) : (count f block input index).natAbs≤h := by
  unfold count
  rw [FoldedBackendExecution.semanticCoefficient_count,Int.natAbs_natCast]
  exact (Finset.card_le_univ _).trans_eq (Fintype.card_fin h)

theorem normalized_value (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (bandL bandR ell : ℕ) (index : Fin (FoldedBackendExecution.windowQuerySize n)) :
    view (GraphNormalizedBand.output (GraphPrefixProgram.fromInputs f p block input bandL bandR ell) input.target bandL bandR
      index (physical f p input.target index).coefficient)=
      if (physical f p input.target index).bandL=bandL ∧ (physical f p input.target index).bandR=bandR then
        count f block input index else 0 := by
  rw [normalized_request,folded_semantic]
  rfl

theorem normalized_bound (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (bandL bandR ell : ℕ) (index : Fin (FoldedBackendExecution.windowQuerySize n)) :
    (view (GraphNormalizedBand.output (GraphPrefixProgram.fromInputs f p block input bandL bandR ell) input.target bandL bandR
      index (physical f p input.target index).coefficient)).natAbs≤h := by
  rw [normalized_value]
  split_ifs
  · exact count_bound f block input index
  · simp

theorem bands_lt (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (target : BinaryFoldedFormation.BinaryTable n)
    (index : Fin (FoldedBackendExecution.windowQuerySize n)) :
    (physical f p target index).bandL<TilingCosts.bandCount p.N (tileWidth p.L p.m) ∧
      (physical f p target index).bandR<TilingCosts.bandCount p.N (tileWidth p.L p.m) := by
  exact ⟨(storedLocate _ (tileWidth_pos p.L p.m p.m_le_L) (request f p target index).row).1.isLt,
    (storedLocate _ (tileWidth_pos p.L p.m p.m_le_L) (request f p target index).column).1.isLt⟩

theorem sum_bands {R : Type*} [AddCommMonoid R] (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (target : BinaryFoldedFormation.BinaryTable n)
    (index : Fin (FoldedBackendExecution.windowQuerySize n)) (value : R) :
    (∑ a : Fin (TilingCosts.bandCount p.N (tileWidth p.L p.m)),
      ∑ b : Fin (TilingCosts.bandCount p.N (tileWidth p.L p.m)),
        if (physical f p target index).bandL=a.val ∧ (physical f p target index).bandR=b.val then value else 0)=value := by
  classical
  let a : Fin (TilingCosts.bandCount p.N (tileWidth p.L p.m)) := ⟨_,(bands_lt f p target index).1⟩
  let b : Fin (TilingCosts.bandCount p.N (tileWidth p.L p.m)) := ⟨_,(bands_lt f p target index).2⟩
  change (∑ x : Fin (TilingCosts.bandCount p.N (tileWidth p.L p.m)), ∑ y : Fin (TilingCosts.bandCount p.N (tileWidth p.L p.m)), if a.val=x.val ∧ b.val=y.val then value else 0)=value
  simp only [←Fin.ext_iff,ite_and]
  simp

#print axioms count_nonnegative
#print axioms count_bound
#print axioms normalized_value
#print axioms normalized_bound
#print axioms bands_lt
#print axioms sum_bands
end ThinMatrix.FoldedRequestBounds
