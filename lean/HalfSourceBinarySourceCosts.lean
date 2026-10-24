import HalfSourceSourceCosts
import HalfSourceRootPolynomials
import BinaryBackendCosts

/-! The actual binary translated source family, including adapter caches,
all J² pairs and all degree runs, fits the residual-source allowance.
The proof charges its actual binary conversion factor and complete cyclic
vectors, not only the unweighted semantic source counter. -/
namespace ThinMatrix.HalfSourceBinarySourceCosts
open SourceFormation ExactHalfBandSources HalfSourceParameters
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

theorem reader_polynomial (L m : ℕ) :
    readerBudget L m (BinaryBandSource.cachedReadBudget L m (1:ℕ).size)+1≤4000*(L+m+1)^2 := by
  unfold readerBudget BinaryBandSource.cachedReadBudget BackendScalarBits.backendScalarUnit BackendScalarBits.scalarUnit
  norm_num
  nlinarith [sq_nonneg (L+m)]

theorem bitUnit_polynomial (L m : ℕ) : BinarySourceFormation.bitUnit L (L-m) 1≤8000*(L+m+1)^3 := by
  have hk := Nat.sub_le L m
  unfold BinarySourceFormation.bitUnit BinarySourceFormation.formationWidth
  norm_num
  calc
    _ ≤1000*(2*(L+m+1))^3 := by gcongr;omega
    _ = _ := by ring

theorem band_polynomial (L m q : ℕ) (hq : 1≤q) :
    bandBudget L m q 1≤64000000000*(L+m+1)^8*q*12^L*2^(L-m) := by
  let P := L+m+1
  let W := q*12^L*2^(L-m)
  have hP : 1≤P := by dsimp[P];omega
  have hW : 1≤W := by dsimp[W];exact one_le_mul (one_le_mul hq (Nat.one_le_pow _ _ (by decide))) (Nat.one_le_pow _ _ (by decide))
  have hreader := reader_polynomial L m
  have hlen : L+m+(L-m)+1≤2*P := by dsimp[P];omega
  have hsource := sourceBudget_polynomial L m (L-m) q (readerBudget L m (BinaryBandSource.cachedReadBudget L m (1:ℕ).size)) hq
  have hs : sourceBudget L m (L-m) q (readerBudget L m (BinaryBandSource.cachedReadBudget L m (1:ℕ).size))≤3200000*P^4*W := by
    calc
      _ ≤200*(readerBudget L m (BinaryBandSource.cachedReadBudget L m (1:ℕ).size)+1)*(L+m+(L-m)+1)^2*q*12^L*2^(L-m) := hsource
      _ ≤200*(4000*P^2)*(2*P)^2*q*12^L*2^(L-m) := by gcongr
      _ = _ := by dsimp[W];ring
  have hPw : 1≤P^4*W := one_le_mul (Nat.one_le_pow _ _ hP) hW
  have hs8 : sourceBudget L m (L-m) q (readerBudget L m (BinaryBandSource.cachedReadBudget L m (1:ℕ).size))+8≤4000000*P^4*W := by nlinarith only [hs,hPw]
  have hbit := bitUnit_polynomial L m
  have hrun : 2*m+1≤2*P := by dsimp[P];omega
  unfold bandBudget
  calc
    _ ≤(4000000*P^4*W)*(2*P)*(8000*P^3) := by gcongr
    _ = _ := by dsimp[P,W];ring

theorem families_polynomial (L m q : ℕ) (hm : 4*m≤L) (hq : 1≤q) :
    familiesBudget L m q 1≤10000000000000000*(L+m+1)^14*q*12^L*2^(L-m) := by
  let P := L+m+1
  let W := q*12^L*2^(L-m)
  have hP : 1≤P := by dsimp[P];omega
  have hW : 1≤W := by dsimp[W];exact one_le_mul (one_le_mul hq (Nat.one_le_pow _ _ (by decide))) (Nat.one_le_pow _ _ (by decide))
  have hcache : cacheBudget L m q 1≤256000*P^3*W := by
    have h := BinarySourceFactor.adapterBudget_one L m q
    change cacheBudget L m q 1≤1000*ThinMatrixBackend.inputBudget L m q at h
    have hi := BackendCostRefinement.SourceCosts.inputBudget_exp_bound L m q (by omega) hq
    have he := BackendCostRefinement.SourceCosts.input_exp_le_raw L m hm
    calc
      _ ≤1000*ThinMatrixBackend.inputBudget L m q := h
      _ ≤1000*(256*P^3*q*2^(4*L+m)) := Nat.mul_le_mul_left 1000 hi
      _ ≤1000*(256*P^3*q*(12^L*2^(L-m))) := by gcongr
      _ = _ := by dsimp[W];ring
  have hband : bandBudget L m q 1≤64000000000*P^8*W := by simpa only [P,W,mul_assoc] using band_polynomial L m q hq
  have hJ : ExactHalfSourcePlan.J m≤64*P^3 := by
    rw [← ExactHalfSourcePlan.count_eq]
    unfold ExactHalfSourcePlan.count
    split_ifs with hm0
    · subst m;dsimp[P];nlinarith [Nat.one_le_pow 3 (L+1) (by omega)]
    · gcongr;dsimp[P];omega
  have hbound : familiesBudget L m q 1≤
      2*(256000*P^3*W)+((2*(64000000000*P^8*W)+12)*(64*P^3)+8)*(64*P^3)+8 := by
    unfold familiesBudget
    gcongr
  have h3 : P^3≤P^14 := Nat.pow_le_pow_right hP (by decide)
  have h6 : P^6≤P^14 := Nat.pow_le_pow_right hP (by decide)
  have h0 : 1≤P^14 := Nat.one_le_pow _ _ hP
  have h3W := Nat.mul_le_mul_right W h3
  have h6W := Nat.mul_le_mul_right W h6
  have h3' : P^3≤P^14*W := h3.trans (Nat.le_mul_of_pos_right _ hW)
  have h6' : P^6≤P^14*W := h6.trans (Nat.le_mul_of_pos_right _ hW)
  have h0' : 1≤P^14*W := one_le_mul h0 hW
  calc
    _ ≤10000000000000000*P^14*W := by nlinarith only [hbound,h3W,h6W,h3',h6',h0']
    _ = _ := by dsimp [P,W];ring

theorem eventual_families_fit : ∀ᶠ m : ℕ in Filter.atTop, ∀ q : ℕ, 1≤q→
    (familiesBudget (OptimizedFoldedPlan.ordinaryLength m) m q 1:ℝ)≤(q:ℝ)*(((4:ℝ)^m)^(T+E)) := by
  have hf := HalfSourceSourceCosts.eventual_polynomial_source_fit 14 (10000000000000000*(14:ℝ)^14) (by positivity)
  filter_upwards [hf] with m hm
  intro q hq
  have h4 : 4*m≤OptimizedFoldedPlan.ordinaryLength m := by
    have h := (OptimizedFoldedPlan.rounded_bounds m).1
    have hmR : (0:ℝ)≤ m := Nat.cast_nonneg m
    have hx : (4:ℝ)*m≤OptimizedFoldedPlan.ordinaryLength m := by norm_num [OptimizedFoldedPlan.c] at h;linarith
    exact_mod_cast hx
  have hpoly := families_polynomial (OptimizedFoldedPlan.ordinaryLength m) m q h4 hq
  have hL := HalfSourceRootPolynomials.ordinary_bound m
  have hshape : (OptimizedFoldedPlan.ordinaryLength m+m+1:ℕ)≤14*(m+1) := by omega
  have hcEq : OptimizedFoldedPlan.c=c := by norm_num [OptimizedFoldedPlan.c,c]
  rw [← hcEq,← OptimizedFoldedPlan.ordinaryLength_eq] at hm
  have hR : (familiesBudget (OptimizedFoldedPlan.ordinaryLength m) m q 1:ℝ)≤
      10000000000000000*(OptimizedFoldedPlan.ordinaryLength m+m+1:ℝ)^14*(q:ℝ)*12^(OptimizedFoldedPlan.ordinaryLength m)*2^(OptimizedFoldedPlan.ordinaryLength m-m) := by exact_mod_cast hpoly
  calc
    _ ≤10000000000000000*(OptimizedFoldedPlan.ordinaryLength m+m+1:ℝ)^14*(q:ℝ)*12^(OptimizedFoldedPlan.ordinaryLength m)*2^(OptimizedFoldedPlan.ordinaryLength m-m) := hR
    _ ≤10000000000000000*(14*(m+1:ℝ))^14*(q:ℝ)*12^(OptimizedFoldedPlan.ordinaryLength m)*2^(OptimizedFoldedPlan.ordinaryLength m-m) := by gcongr;exact_mod_cast hshape
    _ = (q:ℝ)*((10000000000000000*(14:ℝ)^14)*(m+1:ℝ)^14*12^(OptimizedFoldedPlan.ordinaryLength m)*2^(OptimizedFoldedPlan.ordinaryLength m-m)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hm (Nat.cast_nonneg q)

#print axioms reader_polynomial
#print axioms bitUnit_polynomial
#print axioms band_polynomial
#print axioms families_polynomial
#print axioms eventual_families_fit
end
end ThinMatrix.HalfSourceBinarySourceCosts
