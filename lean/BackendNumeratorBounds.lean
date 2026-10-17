import BackendCostRefinement
import CoefficientBounds

/-!
Bounds for the complete numerator produced by the actual stored global
backend. The identity is established before exact division, using the
complete residual-plus-HIGH numerator. The input coefficient hypotheses
refer to the original flat arrays; no final-numerator width is assumed.
-/
namespace ThinMatrix.BackendNumeratorBounds
open scoped BigOperators
open ThinMatrixBackend BackendCostRefinement CyclicRing CompleteThinProduct
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

/-- The actual LOW and HIGH query values together are the complete scaled
product coefficient at the selected tile location. -/
theorem tileNumerator_correct {L m t q : ℕ} [NeZero q] (M : FullMultiplier q)
    (shape : ShapePlan L m) (hm : m ≤ L) (ht : t ≤ 2*m)
    (left : StoredLeftMatrix L m q) (right : StoredRightMatrix L m q)
    (row col : OuterIndex L m) (r : Fin q) :
    (queryLowFromBands (t:=t) (prepareLeftBand (t:=t) shape left)
      (prepareRightBand (t:=t) shape right) row col r).1+
      (queryHighFromTile (prepareTile (t:=t) M (prepareLeftBand (t:=t) shape left)
        (prepareRightBand (t:=t) shape right)) row col r).1=
      ((4^L:ℕ):ℤ)*(readLeftMatrix left*readRightMatrix right) row col r := by
  simp only [queryLowFromBands_correct shape hm ht,queryHighFromTile_correct]
  have h:=congrFun (compactQuery_numerator t hm ht (readLeftMatrix left)
    (readRightMatrix right) row col) r
  have hc : ((4:Cyclic q)^L*(readLeftMatrix left*readRightMatrix right) row col) r=
      ((4^L:ℕ):ℤ)*(readLeftMatrix left*readRightMatrix right) row col r := by
    simpa only [Int.cast_pow,Int.cast_ofNat,Nat.cast_pow,Nat.cast_ofNat] using
      CyclicRing.intCast_mul_coeff ((4:ℤ)^L)
        ((readLeftMatrix left*readRightMatrix right) row col) r
  simpa only [SourceQueryData.numerator,CyclicRing.add_coeff,hc] using h

/-- Exact complete numerator of the genuine returned global preparation,
prior to its one coefficientwise integer division. -/
theorem globalNumerator_correct {N D L m t q : ℕ} [NeZero q] (M : FullMultiplier q)
    (hm : m ≤ L) (ht : t ≤ 2*m) (hD : D ≤ 4^m)
    (A : OriginalLeft N D q) (B : OriginalRight N D q) (i j : Fin N) (r : Fin q) :
    globalNumerator (tileWidth_pos L m hm)
      (prepareGlobal (L:=L) (m:=m) (t:=t) M A B) i j r=
      ((4^L:ℕ):ℤ)*(originalLeftMatrix A*originalRightMatrix B) i j r := by
  unfold globalNumerator
  rw [prepareGlobal_refines]
  simp only [prepareGlobalReference,prepareGlobalShapeReference,Vector.get_map,
    Vector.get_ofFn,RowIndexing.rowUnrank_value]
  rw [tileNumerator_correct M _ hm ht,makeLeftBand_value,makeRightBand_value]
  change ((4^L:ℕ):ℤ)*(((rowBand (padMiddleLeft (m:=m) (originalLeftMatrix A))
    (TilingCosts.locate (tileWidth_pos L m hm) i).1*
    columnBand (padMiddleRight (m:=m) (originalRightMatrix B))
      (TilingCosts.locate (tileWidth_pos L m hm) j).1)
    (localRow (tileWidth_pos L m hm) i) (localRow (tileWidth_pos L m hm) j)) r)=_
  rw [genuine_tile_product,padMiddle_product hD]

open CoefficientBounds ThinProductCosts

theorem original_product_coefficient_bound {N D q : ℕ} [NeZero q]
    (X : OriginalLeft N D q) (Y : OriginalRight N D q) (A : ℕ)
    (hX : ∀s : Fin (N*D),∀r : Fin q, |(X.get s).get r|≤(A:ℤ))
    (hY : ∀s : Fin (D*N),∀r : Fin q, |(Y.get s).get r|≤(A:ℤ))
    (i j : Fin N) (r : Fin q) :
    |(originalLeftMatrix X*originalRightMatrix Y) i j r|≤((D*q*A^2:ℕ):ℤ) := by
  have hterm (h : Fin D) :
      CoeffBound (originalLeftMatrix X i h*originalRightMatrix Y h j) (q*A*A) :=
    leaf_product_bound _ _
      (fun r=>hX (finProdFinEquiv (i,h)) r)
      (fun r=>hY (finProdFinEquiv (h,j)) r)
  have hsum:=finite_sum_bound (Finset.univ : Finset (Fin D))
    (fun h=>originalLeftMatrix X i h*originalRightMatrix Y h j)
    (q*A*A) (fun h _=>hterm h) r
  rw [Matrix.mul_apply]
  simpa only [sum_coeff,Finset.card_univ,Fintype.card_fin,pow_two,Nat.mul_assoc] using hsum



theorem backend_numeric_bits (L m D q A : ℕ) (hD : D ≤ 4^m) :
    (4^L*D*q*A^2).size ≤ 2*L+2*m+q.size+2*A.size+1 := by
  have h4 (j : ℕ) : (4:ℕ)^j = 2^(2*j) := by
    rw [show (4:ℕ)=2^2 by norm_num, pow_mul]
  have hp : 4^L*D*q*A^2 ≤ 2^(2*L+2*m+q.size+2*A.size) := by
    calc
      _ ≤ 4^L*4^m*(2^q.size)*(2^A.size)^2 :=
        Nat.mul_le_mul
          (Nat.mul_le_mul (Nat.mul_le_mul_left _ hD)
            (Nat.lt_size_self q).le)
          (Nat.pow_le_pow_left (Nat.lt_size_self A).le 2)
      _ = _ := by
        rw [h4 L,h4 m,←pow_mul,←pow_add,←pow_add,←pow_add]
        congr 1
        omega
  apply Nat.size_le.mpr
  exact hp.trans_lt
    (Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self _))


/-- Original flat coefficient bounds control the complete actual global
numerator, even though individual LOW or HIGH summands need not divide. -/
theorem globalNumerator_natAbs_le {N D L m t q : ℕ} [NeZero q] (M : FullMultiplier q)
    (hm : m ≤ L) (ht : t ≤ 2*m) (hD : D ≤ 4^m)
    (X : OriginalLeft N D q) (Y : OriginalRight N D q) (A : ℕ)
    (hX : ∀s : Fin (N*D),∀r : Fin q, |(X.get s).get r| ≤ (A:ℤ))
    (hY : ∀s : Fin (D*N),∀r : Fin q, |(Y.get s).get r| ≤ (A:ℤ))
    (i j : Fin N) (r : Fin q) :
    (globalNumerator (tileWidth_pos L m hm)
      (prepareGlobal (L:=L) (m:=m) (t:=t) M X Y) i j r).natAbs ≤ 4^L*D*q*A^2 := by
  have hp:=original_product_coefficient_bound X Y A hX hY i j r
  have hn : ((originalLeftMatrix X*originalRightMatrix Y) i j r).natAbs ≤ D*q*A^2 := by
    exact_mod_cast (show (((originalLeftMatrix X*originalRightMatrix Y) i j r).natAbs:ℤ) ≤
      ((D*q*A^2:ℕ):ℤ) by simpa only [Int.natCast_natAbs] using hp)
  rw [globalNumerator_correct M hm ht hD X Y i j r]
  simp only [Int.natAbs_mul,Int.natAbs_natCast]
  calc
    _ ≤ 4^L*(D*q*A^2) := Nat.mul_le_mul_left _ hn
    _ = _ := by ring

/-- Explicit original-input bit budget for exact query normalization. -/
def numeratorBitBudget (L m q A : ℕ) : ℕ := 2*L+2*m+q.size+2*A.size+1

theorem globalNumerator_size_le {N D L m t q : ℕ} [NeZero q] (M : FullMultiplier q)
    (hm : m ≤ L) (ht : t ≤ 2*m) (hD : D ≤ 4^m)
    (X : OriginalLeft N D q) (Y : OriginalRight N D q) (A : ℕ)
    (hX : ∀s : Fin (N*D),∀r : Fin q, |(X.get s).get r| ≤ (A:ℤ))
    (hY : ∀s : Fin (D*N),∀r : Fin q, |(Y.get s).get r| ≤ (A:ℤ))
    (i j : Fin N) (r : Fin q) :
    (globalNumerator (tileWidth_pos L m hm)
      (prepareGlobal (L:=L) (m:=m) (t:=t) M X Y) i j r).natAbs.size ≤
        numeratorBitBudget L m q A := by
  exact (Nat.size_le_size (globalNumerator_natAbs_le M hm ht hD X Y A hX hY i j r)).trans
    (backend_numeric_bits L m D q A hD)

/-- The actual selected query counter has no assumed final-width premise:
its exact-division budget follows from the original input coefficients. -/
theorem queryGlobal_operations_le_of_input_bounds {N D L m t q : ℕ} [NeZero q]
    (M : FullMultiplier q) (hm : m ≤ L) (ht : t ≤ 2*m) (hD : D ≤ 4^m)
    (X : OriginalLeft N D q) (Y : OriginalRight N D q) (A : ℕ)
    (hX : ∀s : Fin (N*D),∀r : Fin q, |(X.get s).get r| ≤ (A:ℤ))
    (hY : ∀s : Fin (D*N),∀r : Fin q, |(Y.get s).get r| ≤ (A:ℤ))
    (i j : Fin N) (r : Fin q) :
    (queryGlobal (tileWidth_pos L m hm)
      (prepareGlobal (L:=L) (m:=m) (t:=t) M X Y) i j r).2 ≤
      globalQueryRefinement N L m (numeratorBitBudget L m q A)*
        (lowCoefficientCost m t q (2*m+1)+highCoefficientReads m t) := by
  apply BackendCostRefinement.queryGlobal_operations_le _ _ _ _ _ _ hm ht
  exact globalNumerator_size_le M hm ht hD X Y A hX hY i j r

/-- One shared actual preparation answers a materialized request list.
Only its genuine full-multiplier operand budget remains a separate input;
the query numerator sizes are derived here from the original arrays. -/
theorem executeRequests_operations_le_of_input_bounds {N D L m t q Q : ℕ} [NeZero q]
    (M : FullMultiplier q) (hm : m ≤ L) (ht : t ≤ 2*m) (hD : D ≤ 4^m)
    (X : OriginalLeft N D q) (Y : OriginalRight N D q) (A : ℕ)
    (hX : ∀s : Fin (N*D),∀r : Fin q, |(X.get s).get r| ≤ (A:ℤ))
    (hY : ∀s : Fin (D*N),∀r : Fin q, |(Y.get s).get r| ≤ (A:ℤ))
    (requests : Vector (TilingCosts.Request N q) Q) (fullBudget : ℕ)
    (hmul : GlobalMultiplierBudget M (prepareGlobal (L:=L) (m:=m) (t:=t) M X Y) fullBudget) :
    (executeRequests (t:=t) (tileWidth_pos L m hm) M X Y requests).operations ≤
      globalPreparationBudget N L m t q fullBudget+
        Q*globalQueryRefinement N L m (numeratorBitBudget L m q A)*
          (lowCoefficientCost m t q (2*m+1)+highCoefficientReads m t) := by
  apply BackendCostRefinement.executeRequests_operations_le M X Y requests hm ht
    fullBudget (numeratorBitBudget L m q A) hmul
  intro i
  exact globalNumerator_size_le M hm ht hD X Y A hX hY
    (requests.get i).row (requests.get i).column (requests.get i).coefficient

#print axioms original_product_coefficient_bound
#print axioms backend_numeric_bits
#print axioms globalNumerator_natAbs_le
#print axioms globalNumerator_size_le
#print axioms queryGlobal_operations_le_of_input_bounds
#print axioms executeRequests_operations_le_of_input_bounds

/-- The normalization denominator also has a proved bit budget. -/
theorem normalization_denominator_bits (L : ℕ) :
    ((4:ℤ)^L).natAbs.size ≤ 2*L+1 := by
  simp only [Int.natAbs_pow,show (4:ℤ).natAbs=4 by decide]
  apply Nat.size_le.mpr
  rw [show (4:ℕ)=2^2 by decide,←pow_mul]
  exact Nat.pow_lt_pow_right (by decide) (by omega)

#print axioms tileNumerator_correct
#print axioms globalNumerator_correct
#print axioms normalization_denominator_bits
end
end ThinMatrix.BackendNumeratorBounds
