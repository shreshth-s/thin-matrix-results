import BackendScalarBits
import AdaptiveBitBounds

/-!
# Widths of the literal LOW coefficient arrays

The sparse dense-array execution uses the same six source rows as the
shared-prefix cache invariant. The refinement covers the returned `formed`
trace, including internal arrays, and then projects actual stored integer
cells. Source bounds are propagated from original stored input bands below.
-/

namespace ThinMatrix.CacheSchemaBitBounds

open CacheBounds SharedEncoder CoefficientBounds PipelineBitBounds
open CacheDenseLowering SparseLocalForms

set_option maxHeartbeats 2000000

/-- The polynomial reference trace uses the identical row schema, including
the padded fourth opposite coordinate. -/
theorem reference_formed_bound {q L m t A : ℕ} [NeZero q]
    (hA : 1 ≤ A) (width : ℕ) (side : Bool)
    (input : PolyData q (2*L) (rootDims L side))
    (hinput : ∀ a, PolynomialCoeffBound
      (SharedEncoder.read (2*L) (rootDims L side) input a) (2^(L+m)*A)) :
    ∀ s ∈ (SharedEncoder.encode L m t q width side
      (CachedLowIdentity.sourceCacheForms L side) input).formed,
      ∀ a d, CoeffBound ((SharedEncoder.read s.remaining s.dims s.node.data a).coeff d)
        (uniformBudget L m t q A) := by
  have hm : SharedEncoder.materialize (2*L) (rootDims L side)
      (SharedEncoder.read (2*L) (rootDims L side) input) = input := by
    apply CacheDenseLowering.dense_ext
    intro a
    exact SharedEncoder.read_materialize _ _ _ _
  have hb := PipelineBitBounds.shared_run_uniform_bound (t := t) hA width
    (CacheDenseLowering.normalHere L side) (rootDims L side)
    (fun i => rawDim_le_four L side i.val)
    (SharedEncoder.read (2*L) (rootDims L side) input) hinput
  rw [hm] at hb
  rw [SharedEncoder.encode, BackendScalarBits.sourceCacheForms_eq_cacheForms]
  exact hb

/-- Every literal coefficient in every returned internal dense array is
bounded; no final coefficient width is assumed. -/
theorem encode_formed_bound {q L m t A : ℕ} [NeZero q]
    (hA : 1 ≤ A) (width : ℕ) (side : Bool)
    (input : PolyData q (2*L) (rootDims L side))
    (hinput : ∀ a, PolynomialCoeffBound
      (SharedEncoder.read (2*L) (rootDims L side) input a) (2^(L+m)*A)) :
    ∀ s ∈ (CacheDenseLowering.encode L m t q width side
      (CacheDenseLowering.lowerData (2*L) (rootDims L side) input)).formed,
      ∀ a d r, |denseRead (SharedEncoder.read s.remaining s.dims s.node.data a) d r| ≤
        (uniformBudget L m t q A : ℤ) := by
  intro s hs
  rw [CacheDenseLowering.encode_refines] at hs
  obtain ⟨ref,href,rfl⟩ := List.mem_map.mp hs
  intro a d r
  simpa only [lowerStored,lowerNode,read_lowerData,CachedLowQuery.extractedBlock,
    SparseLocalForms.denseRead_toDense,SparseLocalForms.extract] using
    reference_formed_bound hA width side input hinput ref href a d.val r

theorem encode_formed_bits {q L m t A : ℕ} [NeZero q]
    (hA : 1 ≤ A) (width : ℕ) (side : Bool)
    (input : PolyData q (2*L) (rootDims L side))
    (hinput : ∀ a, PolynomialCoeffBound
      (SharedEncoder.read (2*L) (rootDims L side) input a) (2^(L+m)*A))
    (r cL cm cq cA : ℕ) (hL : L ≤ cL*r) (hm : m ≤ cm*r)
    (hq : q ≤ 2^(cq*r)) (hAb : A ≤ 2^(cA*r)) (ht : t ≤ 2*m) :
    ∀ s ∈ (CacheDenseLowering.encode L m t q width side
      (CacheDenseLowering.lowerData (2*L) (rootDims L side) input)).formed,
      ∀ a d j, CoefficientBudget.signedBitLength
        (denseRead (SharedEncoder.read s.remaining s.dims s.node.data a) d j) ≤
        CoefficientBudget.budgetConstant cL cm cq cA*(r+1)+2 := by
  intro s hs a d j
  exact coeffBound_signedBitLength _
    (fun k => encode_formed_bound hA width side input hinput s hs a d k)
    r cL cm cq cA hL hm hq hAb ht j

theorem encode_formed_size_common {q L m t A : ℕ} [NeZero q]
    (hA : 1 ≤ A) (width : ℕ) (side : Bool)
    (input : PolyData q (2*L) (rootDims L side))
    (hinput : ∀ a, PolynomialCoeffBound
      (SharedEncoder.read (2*L) (rootDims L side) input a) (2^(L+m)*A))
    (n degree cL cm cq : ℕ) (hL : L ≤ cL*n.size) (hm : m ≤ cm*n.size)
    (hq : q ≤ 2^(cq*n.size)) (hAb : A ≤ n^degree) (ht : t ≤ 2*m) :
    ∀ s ∈ (CacheDenseLowering.encode L m t q width side
      (CacheDenseLowering.lowerData (2*L) (rootDims L side) input)).formed,
      ∀ a d j, (denseRead (SharedEncoder.read s.remaining s.dims s.node.data a) d j).natAbs.size ≤
        AdaptiveBitBounds.commonBitWidth n degree cL cm cq := by
  intro s hs a d j
  apply AdaptiveBitBounds.coefficient_size_le_common n degree L m t q A cL cm cq
    hL hm hq hAb ht
  exact_mod_cast (show ((denseRead (SharedEncoder.read s.remaining s.dims s.node.data a) d j).natAbs : ℤ)
      ≤ uniformBudget L m t q A by
    simpa only [Int.natCast_natAbs] using encode_formed_bound hA width side input hinput s hs a d j)

/-- Entry-point version for an already stored integer-vector source array. -/
theorem vectors_formed_bound {q L m t A : ℕ} [NeZero q]
    (hA : 1 ≤ A) (width : ℕ) (side : Bool)
    (input : SharedEncoder.Dense (R := Vector ℤ q) (2*L) (rootDims L side))
    (hinput : ∀ a r, |(SharedEncoder.read (2*L) (rootDims L side) input a).get r| ≤
      (2^(L+m)*A : ℕ)) :
    ∀ s ∈ (CacheDenseLowering.encodeVectors L m t q width side input).formed,
      ∀ a d r, |denseRead (SharedEncoder.read s.remaining s.dims s.node.data a) d r| ≤
        (uniformBudget L m t q A : ℤ) := by
  have hp : ∀ a, PolynomialCoeffBound (SharedEncoder.read (2*L) (rootDims L side)
      (CacheDenseLowering.inputPolynomial (2*L) (rootDims L side) input) a) (2^(L+m)*A) := by
    intro a
    rw [CacheDenseLowering.inputPolynomial, SharedEncoder.read_materialize]
    exact constantPolynomial_bound _ (hinput a)
  simpa only [CacheDenseLowering.encodeVectors,CacheDenseLowering.constantInput_refines] using
    encode_formed_bound hA width side _ hp

/-- Both physical source orientations are covered by the actual source
ordering projection used by `prepareSource`. -/
theorem source_formed_bound {q L m t A : ℕ} [NeZero q]
    (hA : 1 ≤ A) (width : ℕ) (side : Bool)
    (X : CompleteThinProduct.SourceWord L → CyclicRing.Cyclic q)
    (hX : ∀ a, CoeffBound (X a) (2^(L+m)*A)) :
    ∀ s ∈ (CacheDenseLowering.encode L m t q width side
      (CacheDenseLowering.constantInput (2*L) (rootDims L side)
        (CacheDenseLowering.sourceVectorInput side X))).formed,
      ∀ a d r, |denseRead (SharedEncoder.read s.remaining s.dims s.node.data a) d r| ≤
        (uniformBudget L m t q A : ℤ) := by
  have hp : ∀ a, PolynomialCoeffBound (SharedEncoder.read (2*L) (rootDims L side)
      (CachedLowIdentity.sourceCacheInput L side X) a) (2^(L+m)*A) := by
    cases side <;> intro a <;>
      simp only [CachedLowIdentity.sourceCacheInput,SourceCoordinates.leftInput,
        SourceCoordinates.rightInput,SharedEncoder.read_materialize] <;>
      exact constantPolynomial_bound _ (hX _)
  rw [CacheDenseLowering.sourceInput_refines]
  exact encode_formed_bound hA width side _ hp

theorem source_formed_bits {q L m t A : ℕ} [NeZero q]
    (hA : 1 ≤ A) (width : ℕ) (side : Bool)
    (X : CompleteThinProduct.SourceWord L → CyclicRing.Cyclic q)
    (hX : ∀ a, CoeffBound (X a) (2^(L+m)*A))
    (r cL cm cq cA : ℕ) (hL : L ≤ cL*r) (hm : m ≤ cm*r)
    (hq : q ≤ 2^(cq*r)) (hAb : A ≤ 2^(cA*r)) (ht : t ≤ 2*m) :
    ∀ s ∈ (CacheDenseLowering.encode L m t q width side
      (CacheDenseLowering.constantInput (2*L) (rootDims L side)
        (CacheDenseLowering.sourceVectorInput side X))).formed,
      ∀ a d j, CoefficientBudget.signedBitLength
        (denseRead (SharedEncoder.read s.remaining s.dims s.node.data a) d j) ≤
        CoefficientBudget.budgetConstant cL cm cq cA*(r+1)+2 := by
  intro s hs a d j
  exact coeffBound_signedBitLength _
    (fun k => source_formed_bound hA width side X hX s hs a d k)
    r cL cm cq cA hL hm hq hAb ht j

theorem source_formed_size_common {q L m t A : ℕ} [NeZero q]
    (hA : 1 ≤ A) (width : ℕ) (side : Bool)
    (X : CompleteThinProduct.SourceWord L → CyclicRing.Cyclic q)
    (hX : ∀ a, CoeffBound (X a) (2^(L+m)*A))
    (n degree cL cm cq : ℕ) (hL : L ≤ cL*n.size) (hm : m ≤ cm*n.size)
    (hq : q ≤ 2^(cq*n.size)) (hAb : A ≤ n^degree) (ht : t ≤ 2*m) :
    ∀ s ∈ (CacheDenseLowering.encode L m t q width side
      (CacheDenseLowering.constantInput (2*L) (rootDims L side)
        (CacheDenseLowering.sourceVectorInput side X))).formed,
      ∀ a d j, (denseRead (SharedEncoder.read s.remaining s.dims s.node.data a) d j).natAbs.size ≤
        AdaptiveBitBounds.commonBitWidth n degree cL cm cq := by
  intro s hs a d j
  apply AdaptiveBitBounds.coefficient_size_le_common n degree L m t q A cL cm cq
    hL hm hq hAb ht
  exact_mod_cast (show ((denseRead (SharedEncoder.read s.remaining s.dims s.node.data a) d j).natAbs : ℤ)
      ≤ uniformBudget L m t q A by
    simpa only [Int.natCast_natAbs] using source_formed_bound hA width side X hX s hs a d j)

open ThinMatrixBackend

/-- The actual degree-zero source vector root has the same coefficient cap
as the source, on both orientations and at every auxiliary degree. -/
theorem source_root_bound {q L width A : ℕ} [NeZero q] (side : Bool)
    (X : CompleteThinProduct.SourceWord L → CyclicRing.Cyclic q)
    (hX : ∀ a, CoeffBound (X a) A)
    (a : SharedEncoder.Coordinates (SharedEncoder.rootDims L side))
    (d : Fin width) (r : Fin q) :
    |denseRead (SharedEncoder.read (2*L) (SharedEncoder.rootDims L side)
      (CacheDenseLowering.constantInput (2*L) (SharedEncoder.rootDims L side)
        (CacheDenseLowering.sourceVectorInput side X)) a) d r| ≤ (A:ℤ) := by
  rw [CacheDenseLowering.constantInput,SharedEncoder.read_materialize]
  simp only [CacheDenseLowering.constantBlock,denseRead,Vector.get_ofFn]
  split_ifs
  · cases side with
    | false =>
      rw [CacheDenseLowering.sourceVectorInput,SourceCoordinates.rightVectorInput_read]
      exact hX _ r
    | true =>
      rw [CacheDenseLowering.sourceVectorInput,SourceCoordinates.leftVectorInput_read]
      exact hX _ r
  · simp

theorem prepared_left_source_root_bound {q L m t A : ℕ} [NeZero q]
    (shape : ShapePlan L m) (data : StoredLeftMatrix L m q)
    (hd : ∀ i r, |(data.get i).get r| ≤ (A:ℤ)) (run : Fin (2*m+1))
    (a : SharedEncoder.Coordinates (SharedEncoder.rootDims L true))
    (d : Fin (2*m+1)) (r : Fin q) :
    |denseRead (SharedEncoder.read (2*L) (SharedEncoder.rootDims L true)
      (CacheDenseLowering.constantInput (2*L) (SharedEncoder.rootDims L true)
        (CacheDenseLowering.sourceVectorInput true
          (sourceValue ((prepareLeftBand (t:=t) shape data).runs.get run).source))) a) d r| ≤
      ((2^(L+m)*A:ℕ):ℤ) :=
  source_root_bound true _ (AdaptiveBitBounds.prepared_left_source_bound (t:=t) shape data hd run) a d r

theorem prepared_right_source_root_bound {q L m t A : ℕ} [NeZero q]
    (shape : ShapePlan L m) (data : StoredRightMatrix L m q)
    (hd : ∀ i r, |(data.get i).get r| ≤ (A:ℤ)) (run : Fin (2*m+1))
    (a : SharedEncoder.Coordinates (SharedEncoder.rootDims L false))
    (d : Fin (2*m+1)) (r : Fin q) :
    |denseRead (SharedEncoder.read (2*L) (SharedEncoder.rootDims L false)
      (CacheDenseLowering.constantInput (2*L) (SharedEncoder.rootDims L false)
        (CacheDenseLowering.sourceVectorInput false
          (sourceValue ((prepareRightBand (t:=t) shape data).runs.get run).source))) a) d r| ≤
      ((2^(L+m)*A:ℕ):ℤ) :=
  source_root_bound false _ (AdaptiveBitBounds.prepared_right_source_bound (t:=t) shape data hd run) a d r

/-- Conversion needed by every actual formed-cache cell after the generic
schema invariant has produced an absolute-value coefficient bound. -/
theorem abs_bound_size_le_common (n degree L m t q A cL cm cq : ℕ)
    (hL : L ≤ cL*n.size) (hm : m ≤ cm*n.size) (hq : q ≤ 2^(cq*n.size))
    (hA : A ≤ n^degree) (ht : t ≤ 2*m) (z : ℤ)
    (hz : |z| ≤ (uniformBudget L m t q A:ℤ)) :
    z.natAbs.size ≤ AdaptiveBitBounds.commonBitWidth n degree cL cm cq := by
  apply AdaptiveBitBounds.coefficient_size_le_common n degree L m t q A cL cm cq
    hL hm hq hA ht z
  rw [← Int.natCast_natAbs] at hz
  exact_mod_cast hz


/-- Every actual formed coefficient of the left band's LOW preparation,
including internal arrays, from original stored matrix coefficients alone. -/
theorem prepared_left_formed_bound {q L m t A : ℕ} [NeZero q]
    (hA : 1 ≤ A) (shape : ShapePlan L m) (data : StoredLeftMatrix L m q)
    (hd : ∀ i r, |(data.get i).get r| ≤ (A:ℤ)) (run : Fin (2*m+1)) :
    ∀ s ∈ (CacheDenseLowering.encode L m t q (2*m+1) true
      (CacheDenseLowering.constantInput (2*L) (SharedEncoder.rootDims L true)
        (CacheDenseLowering.sourceVectorInput true
          (sourceValue ((prepareLeftBand (t:=t) shape data).runs.get run).source)))).formed,
      ∀ a d r, |denseRead (SharedEncoder.read s.remaining s.dims s.node.data a) d r| ≤
        (uniformBudget L m t q A:ℤ) :=
  CacheSchemaBitBounds.source_formed_bound hA (2*m+1) true _
    (AdaptiveBitBounds.prepared_left_source_bound (t:=t) shape data hd run)

/-- Right-band counterpart of the actual internal-array coefficient bound. -/
theorem prepared_right_formed_bound {q L m t A : ℕ} [NeZero q]
    (hA : 1 ≤ A) (shape : ShapePlan L m) (data : StoredRightMatrix L m q)
    (hd : ∀ i r, |(data.get i).get r| ≤ (A:ℤ)) (run : Fin (2*m+1)) :
    ∀ s ∈ (CacheDenseLowering.encode L m t q (2*m+1) false
      (CacheDenseLowering.constantInput (2*L) (SharedEncoder.rootDims L false)
        (CacheDenseLowering.sourceVectorInput false
          (sourceValue ((prepareRightBand (t:=t) shape data).runs.get run).source)))).formed,
      ∀ a d r, |denseRead (SharedEncoder.read s.remaining s.dims s.node.data a) d r| ≤
        (uniformBudget L m t q A:ℤ) :=
  CacheSchemaBitBounds.source_formed_bound hA (2*m+1) false _
    (AdaptiveBitBounds.prepared_right_source_bound (t:=t) shape data hd run)

/-- Common binary-width certificate for the left cache's actual formation
trace. No final coefficient-width hypothesis occurs. -/
theorem prepared_left_formed_size_common {q L m t A : ℕ} [NeZero q]
    (hA : 1 ≤ A) (shape : ShapePlan L m) (data : StoredLeftMatrix L m q)
    (hd : ∀ i r, |(data.get i).get r| ≤ (A:ℤ)) (run : Fin (2*m+1))
    (n degree cL cm cq : ℕ) (hL : L ≤ cL*n.size) (hm : m ≤ cm*n.size)
    (hq : q ≤ 2^(cq*n.size)) (hAb : A ≤ n^degree) (ht : t ≤ 2*m) :
    ∀ s ∈ (CacheDenseLowering.encode L m t q (2*m+1) true
      (CacheDenseLowering.constantInput (2*L) (SharedEncoder.rootDims L true)
        (CacheDenseLowering.sourceVectorInput true
          (sourceValue ((prepareLeftBand (t:=t) shape data).runs.get run).source)))).formed,
      ∀ a d r, (denseRead (SharedEncoder.read s.remaining s.dims s.node.data a) d r).natAbs.size ≤
        AdaptiveBitBounds.commonBitWidth n degree cL cm cq := by
  intro s hs a d r
  exact abs_bound_size_le_common n degree L m t q A cL cm cq hL hm hq hAb ht _
    (prepared_left_formed_bound hA shape data hd run s hs a d r)

/-- Common binary-width certificate for the right cache's actual formation. -/
theorem prepared_right_formed_size_common {q L m t A : ℕ} [NeZero q]
    (hA : 1 ≤ A) (shape : ShapePlan L m) (data : StoredRightMatrix L m q)
    (hd : ∀ i r, |(data.get i).get r| ≤ (A:ℤ)) (run : Fin (2*m+1))
    (n degree cL cm cq : ℕ) (hL : L ≤ cL*n.size) (hm : m ≤ cm*n.size)
    (hq : q ≤ 2^(cq*n.size)) (hAb : A ≤ n^degree) (ht : t ≤ 2*m) :
    ∀ s ∈ (CacheDenseLowering.encode L m t q (2*m+1) false
      (CacheDenseLowering.constantInput (2*L) (SharedEncoder.rootDims L false)
        (CacheDenseLowering.sourceVectorInput false
          (sourceValue ((prepareRightBand (t:=t) shape data).runs.get run).source)))).formed,
      ∀ a d r, (denseRead (SharedEncoder.read s.remaining s.dims s.node.data a) d r).natAbs.size ≤
        AdaptiveBitBounds.commonBitWidth n degree cL cm cq := by
  intro s hs a d r
  exact abs_bound_size_le_common n degree L m t q A cL cm cq hL hm hq hAb ht _
    (prepared_right_formed_bound hA shape data hd run s hs a d r)

#print axioms reference_formed_bound
#print axioms encode_formed_bound
#print axioms encode_formed_bits
#print axioms encode_formed_size_common
#print axioms vectors_formed_bound
#print axioms source_formed_bound
#print axioms source_formed_bits
#print axioms source_formed_size_common
#print axioms source_root_bound
#print axioms prepared_left_source_root_bound
#print axioms prepared_right_source_root_bound
#print axioms abs_bound_size_le_common
#print axioms prepared_left_formed_bound
#print axioms prepared_right_formed_bound
#print axioms prepared_left_formed_size_common
#print axioms prepared_right_formed_size_common

end ThinMatrix.CacheSchemaBitBounds
