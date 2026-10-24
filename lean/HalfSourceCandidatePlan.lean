import HalfSourceBatchGeometry

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! Actual candidate lists construct the exact-half factorization and typed
production shape. Both independent long-side and full original-grid guards
are proved on these values, without changing the fixed signed-window factor
or pretending root/good-mask slots are independent products. This adapter
does not select the type-dependent suffix or price the complete scheduler. -/
namespace ThinMatrix.HalfSourceCandidatePlan
open Filter
open HalfSourceBatchFit HalfSourceBatchGeometry

theorem scale_ge_three (n : ℕ) (hn : 3 ≤ n) : 3 ≤ scale n := by
  have hs : 1 < n.size := Nat.lt_size.mpr (by norm_num; omega)
  have hp : 16 ≤ n.size^4 := by
    have h := Nat.pow_le_pow_left (show 2 ≤ n.size by omega) 4
    norm_num at h
    exact h
  unfold scale ComputableParameters.roundedPower
  nlinarith

def factorization (n : ℕ) (call : Call n) (hn : 3 ≤ n) (hnd : call.factors.Nodup) :
    CompactBlocks.PhysicalFactorization call.factors.prod where
  folded := call.folded S
  cyclic := call.cyclic S
  folded_pos := folded_pos n hn call
  cyclic_pos := cyclic_pos n hn call
  coprime := PhaseGeometry.actual_call_coprime call S (scale_ge_three n hn) hnd
  product := call.split S

def produce (n : ℕ) (call : Call n) (hn : 3 ≤ n) (hnd : call.factors.Nodup) (lowWidth : ℕ) :
    BinaryFoldedFactory.Plan (n:=n) (h:=block n) (factorization n call hn hnd) :=
  OptimizedFoldedPlan.produce n (block n) lowWidth (factorization n call hn hnd)

theorem dimensions (n : ℕ) (call : Call n) (hn : 3 ≤ n) (hnd : call.factors.Nodup) (lowWidth : ℕ) :
    (produce n call hn hnd lowWidth).N=outer n call ∧
    (produce n call hn hnd lowWidth).D=dimension n call ∧
    (produce n call hn hnd lowWidth).raw=block n*(3*call.folded S) ∧
    (factorization n call hn hnd).cyclic=call.cyclic S := by
  exact ⟨rfl,rfl,rfl,rfl⟩

theorem exact_lengths (n : ℕ) (call : Call n) (hn : 3 ≤ n) (hnd : call.factors.Nodup) (lowWidth : ℕ) :
    let p := produce n call hn hnd lowWidth
    p.L=Nat.ceil (HalfSourceParameters.c*(p.m:ℝ)) ∧
    p.t=Nat.ceil (2*HalfSourceParameters.theta*(p.m:ℝ)) := by
  have h := OptimizedFoldedPlan.dimensions n (block n) lowWidth (factorization n call hn hnd)
  exact ⟨by simpa only [produce,witness_bridge.2.2.2.2.2.1] using h.1,
    by simpa only [produce,witness_bridge.2.2.2.2.2.2] using h.2.1⟩

theorem original_grid_fit : ∀ᶠ n : ℕ in atTop, ∀ call : Call n,
    ∀ hn : 3 ≤ n, ∀ hnd : call.factors.Nodup, ∀ lowWidth : ℕ,
    let p := produce n call hn hnd lowWidth
    p.L.choose p.m*4^(p.L-p.m) ≤ p.N := by
  filter_upwards [full_grid_fit] with n hfit
  intro call hn hnd lowWidth
  exact hfit call

theorem tileWidth_fit : ∀ᶠ n : ℕ in atTop, ∀ call : Call n,
    ∀ hn : 3 ≤ n, ∀ hnd : call.factors.Nodup, ∀ lowWidth : ℕ,
    let p := produce n call hn hnd lowWidth
    ThinMatrixBackend.tileWidth p.L p.m ≤ p.N := by
  filter_upwards [original_grid_fit] with n hfit
  intro call hn hnd lowWidth
  let p := produce n call hn hnd lowWidth
  have hgood : (GoodMapEmbedding.goodSlots p.L p.m).card ≤ p.L.choose p.m := by
    have h := Finset.card_le_card
      (Finset.filter_subset (fun Q => GoodSetConstruction.restrictionTest
        (GoodSetConstruction.constructGoodMaps p.L p.m).1 Q &&
        GoodSetConstruction.restrictionTest (GoodSetConstruction.constructGoodMaps p.L p.m).2 Qᶜ)
        (Finset.univ.powersetCard p.m))
    simpa only [GoodMapEmbedding.goodSlots,Finset.card_powersetCard,Finset.card_univ,Fintype.card_fin] using h
  exact (Nat.mul_le_mul_right _ hgood).trans (hfit call hn hnd lowWidth)

theorem independent_batch_fit (C k : ℕ) : ∀ᶠ n : ℕ in atTop, ∀ call : Call n,
    ∀ hn : 3 ≤ n, ∀ hnd : call.factors.Nodup, ∀ lowWidth : ℕ,
    let f := factorization n call hn hnd
    let p := produce n call hn hnd lowWidth
    (supportPadding C k n p.D)^15 ≤ CompactBlocks.blockCount n (block n)*((p.m+1)*f.cyclic) := by
  filter_upwards [production_columns_fit C k] with n hfit
  intro call hn hnd lowWidth
  exact hfit call (produce n call hn hnd lowWidth).m

/-- The rectangular chunk-count lemma now uses the proved production long
side. A valid row chunk is still needed; no query count replaces batch fit. -/
theorem padded_chunks_fit (C k : ℕ) (hC : 0 < C) :
    ∀ᶠ n : ℕ in atTop, ∀ call : Call n, ∀ hn : 3 ≤ n, ∀ hnd : call.factors.Nodup,
    ∀ lowWidth rows A : ℕ, 0 < A →
    let p := produce n call hn hnd lowWidth
    let P := CompactBlocks.blockCount n (block n)*((p.m+1)*(factorization n call hn hnd).cyclic)
    let Z := (supportPadding C k n p.D)^15
    CompactBlocks.blockCount rows A*CompactBlocks.blockCount P Z*A*Z ≤ 2*(rows+A)*P := by
  filter_upwards [independent_batch_fit C k] with n hfit
  intro call hn hnd lowWidth rows A hA
  apply RectangularBatch.batch_fit _ _ _ _ hA _ (hfit call hn hnd lowWidth)
  exact pow_pos (support_padding_pos C k n _ hC) _

/-- Finite graph semantics use the same original candidate factorization and
new L,t plan. This remains the exhaustive correctness scheduler. -/
theorem count_value (n : ℕ) (call : Call n) (hn : 3 ≤ n) (hnd : call.factors.Nodup)
    (lowWidth ell : ℕ) (blockId : Fin (CompactBlocks.blockCount n (block n)))
    (input : BinaryFoldedFormation.Inputs n) (i : Fin (FoldedBackendExecution.windowQuerySize n)) :
    BinaryCell.view (GraphBandSchedule.output (factorization n call hn hnd)
      (produce n call hn hnd lowWidth) blockId input ell i)=
        FoldedRequestBounds.count (factorization n call hn hnd) blockId input i :=
  GraphBandSchedule.execute_value _ _ _ _ _ _

#print axioms scale_ge_three
#print axioms dimensions
#print axioms exact_lengths
#print axioms original_grid_fit
#print axioms tileWidth_fit
#print axioms independent_batch_fit
#print axioms padded_chunks_fit
#print axioms count_value
end ThinMatrix.HalfSourceCandidatePlan
