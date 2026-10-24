import HalfSourceCandidatePlan
import HalfSourceSuffixChoice

set_option autoImplicit false
set_option maxHeartbeats 1500000

/-! Common padding for the actual type-dependent suffix selector. The
selected support cardinality and every production coefficient column are
connected to the proved candidate geometry. These bounds do not yet perform
the complete channel-type entropy summation or price selection arithmetic. -/
namespace ThinMatrix.HalfSourceSuffixPlan
open Filter
open HalfSourceBatchFit HalfSourceBatchGeometry HalfSourceCandidatePlan
open HalfSourceSuffixChoice

 theorem ordinaryLength_le (m : ℕ) : OptimizedFoldedPlan.ordinaryLength m ≤ 11*m := by
  rw [OptimizedFoldedPlan.ordinaryLength_eq,Nat.ceil_le]
  have hc : OptimizedFoldedPlan.c ≤ (11:ℝ) := by norm_num [OptimizedFoldedPlan.c]
  push_cast
  exact mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg m)

theorem ordinaryLength_twice (m : ℕ) : 2*m ≤ OptimizedFoldedPlan.ordinaryLength m := by
  have hc : (2:ℝ) ≤ OptimizedFoldedPlan.c := by norm_num [OptimizedFoldedPlan.c]
  have h := mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg m)
  have hceil := (OptimizedFoldedPlan.rounded_bounds m).1
  exact_mod_cast h.trans hceil

theorem ordinaryLength_suffix (m : ℕ) :
    m ≤ OptimizedFoldedPlan.ordinaryLength m-m ∧ OptimizedFoldedPlan.ordinaryLength m-m ≤ 10*m := by
  have hl := ordinaryLength_le m
  have hr := ordinaryLength_twice m
  omega

theorem type_half (m cn co : ℕ) :
    2*(m/2-max cn co) ≤ OptimizedFoldedPlan.ordinaryLength m-m := by
  have hm : 2*(m/2) ≤ m := by omega
  have h := (ordinaryLength_suffix m).1
  omega

/-- A coarse D≤n consequence is sufficient to bound public logarithmic
metadata; it is not substituted for the sharp T geometry. -/
theorem dimension_le_input : ∀ᶠ n : ℕ in atTop, ∀ call : Call n, dimension n call ≤ n := by
  have hg : 2*b < 1 := by norm_num [b,bNumerator,bDenominator]
  have hfit := AsymptoticCosts.eventualPowerFit hg (4*R) overheadConstant
  filter_upwards [hfit,eventually_ge_atTop (3:ℕ)] with n hfitn hn
  intro call
  have h := (dimension_upper n hn call).trans hfitn
  simpa only [Real.rpow_one,Nat.cast_le] using h

theorem middle_index_le_size : ∀ᶠ n : ℕ in atTop, ∀ call : Call n,
    Nat.clog 4 (block n*(3*call.folded S)) ≤ n.size := by
  filter_upwards [dimension_le_input] with n hfit
  intro call
  apply (Nat.clog_le_iff_le_pow (by norm_num : 1<(4:ℕ))).mpr
  have hraw := PhaseGeometry.pad4_lower (block n*(3*call.folded S))
  have hn : n ≤ 4^n.size := (Nat.lt_size_self n).le.trans (Nat.pow_le_pow_left (by norm_num) _)
  exact hraw.trans ((hfit call).trans hn)

/-- This concrete logarithmic padding contains every selected type, with
the same width for all compatible middle blocks. -/
theorem common_support_fit : ∀ᶠ n : ℕ in atTop, ∀ call : Call n,
    ∀ hn : 3 ≤ n, ∀ hnd : call.factors.Nodup, ∀ lowWidth cn co : ℕ,
    let p := produce n call hn hnd lowWidth
    let ell := forType p.L p.m cn co
    CappedSubsetList.count ell (WindowPrefixProgram.cap (p.L-p.m) ell (p.m/2) cn co) ≤
      supportPadding 10 1 n p.D := by
  filter_upwards [middle_index_le_size] with n hsize
  intro call hn hnd lowWidth cn co
  let p := produce n call hn hnd lowWidth
  have hm : p.m ≤ n.size := hsize call
  have hk : p.L-p.m ≤ 10*p.m := (ordinaryLength_suffix p.m).2
  have hlog : p.L-p.m+1 ≤ 10*(n.size+1) := by omega
  have hfit := (forType_fit p.L p.m cn co).2
  have hpD : 4^p.m=p.D := (OptimizedFoldedPlan.dimensions n (block n) lowWidth
    (factorization n call hn hnd)).2.2.symm
  apply hfit.trans
  unfold limit supportPadding
  rw [hpD,pow_one]
  exact Nat.mul_le_mul_right _ hlog

/-- All coefficients of every actual block supply the independent long
rectangle axis for the selected support count itself. -/
theorem selected_support_batch_fit : ∀ᶠ n : ℕ in atTop, ∀ call : Call n,
    ∀ hn : 3 ≤ n, ∀ hnd : call.factors.Nodup, ∀ lowWidth cn co : ℕ,
    let p := produce n call hn hnd lowWidth
    let ell := forType p.L p.m cn co
    let support := CappedSubsetList.count ell (WindowPrefixProgram.cap (p.L-p.m) ell (p.m/2) cn co)
    support^15 ≤ CompactBlocks.blockCount n (block n)*((p.m+1)*(factorization n call hn hnd).cyclic) := by
  filter_upwards [common_support_fit,independent_batch_fit 10 1] with n hs hb
  intro call hn hnd lowWidth cn co
  exact (Nat.pow_le_pow_left (hs call hn hnd lowWidth cn co) 15).trans (hb call hn hnd lowWidth)

/-- The selected length has the same one-unit entropy rounding loss as a
quotient-based choice, whenever the quotient lies inside the physical suffix. -/
theorem selected_length_lower (m cn co : ℕ)
    (hH : 0 < Real.binEntropy (((m/2-max cn co:ℕ):ℝ)/((OptimizedFoldedPlan.ordinaryLength m-m:ℕ):ℝ)))
    (hfit : (m:ℝ)*zeta*Real.log 4 /
      Real.binEntropy (((m/2-max cn co:ℕ):ℝ)/((OptimizedFoldedPlan.ordinaryLength m-m:ℕ):ℝ)) ≤
        (OptimizedFoldedPlan.ordinaryLength m-m:ℕ)) :
    (m:ℝ)*zeta*Real.log 4 /
      Real.binEntropy (((m/2-max cn co:ℕ):ℝ)/((OptimizedFoldedPlan.ordinaryLength m-m:ℕ):ℝ))-1 <
        (forType (OptimizedFoldedPlan.ordinaryLength m) m cn co:ℝ) :=
  choice_quotient_slack m (OptimizedFoldedPlan.ordinaryLength m-m) (m/2-max cn co)
    (type_half m cn co) hH hfit

#print axioms ordinaryLength_le
#print axioms ordinaryLength_twice
#print axioms ordinaryLength_suffix
#print axioms type_half
#print axioms dimension_le_input
#print axioms middle_index_le_size
#print axioms common_support_fit
#print axioms selected_support_batch_fit
#print axioms selected_length_lower
end ThinMatrix.HalfSourceSuffixPlan
