import HalfSourceRawCosts
import HalfSourceBatchGeometry

/-! Size bounds for the actual exact-half rounded block/prime programs
inserted into all seven monomials, including every candidate prime. This
bridges executable dimensions to the analytic phase ledger. It does not
supply the missing bound on the production scheduler's execution counters. -/
namespace ThinMatrix.HalfSourceComputedCosts
open HalfSourceParameters HalfSourcePhaseCosts HalfSourceRawCosts
open scoped BigOperators
open Filter Asymptotics
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

theorem candidate_bound (n : ℕ) (hn : 3 ≤ n) :
    ((PrimePool.candidates (HalfSourceBatchFit.scale n)).card:ℝ) ≤
      8192*(Real.log (n:ℝ))^4*(n:ℝ)^eta := by
  have hp : ((PrimePool.candidates (HalfSourceBatchFit.scale n)).card:ℝ) ≤
      8*(HalfSourceBatchFit.scale n:ℝ) := by
    exact_mod_cast PhaseGeometry.candidate_count_le (HalfSourceBatchFit.scale n)
  have hs := (HalfSourceBatchFit.scale_bounds n hn).2
  rw [HalfSourceBatchGeometry.witness_bridge.2.1] at hs
  have hlog : 0 ≤ Real.log (n:ℝ) := by linarith [PhaseGeometry.one_le_log_nat n hn]
  nlinarith [mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) eta) (pow_nonneg hlog 4)]

theorem actual_rawTerm_bound (n : ℕ) (hn : 3 ≤ n) (call : HalfSourceBatchFit.Call n)
    (i : Fin 7) :
    ((PrimePool.candidates (HalfSourceBatchFit.scale n)).card:ℝ)*
      (HalfSourceBatchFit.blocks n:ℝ)*
      rawTerm n (HalfSourceBatchGeometry.outer n call)
        (HalfSourceBatchFit.dimension n call) (call.cyclic HalfSourceBatchFit.S) i ≤
      phaseConstant i*(Real.log (n:ℝ))^(phaseLogDegree i)*
        (n:ℝ)^(3-saving (HalfSourceBatchGeometry.foldExponent call.factors.length)
          (HalfSourceBatchGeometry.ringExponent call.factors.length) i) := by
  have hb : (HalfSourceBatchFit.blocks n:ℝ) ≤ 2*(n:ℝ)^(1-b) := by
    simpa only [HalfSourceBatchGeometry.witness_bridge.1] using
      HalfSourceBatchGeometry.blocks_upper n (by omega)
  have hN : (HalfSourceBatchGeometry.outer n call:ℝ) ≤
      4*overhead n*(n:ℝ)^(1+HalfSourceBatchGeometry.foldExponent call.factors.length/2) :=
    (HalfSourceBatchGeometry.outer_bounds n hn call).2
  have hdlo : (n:ℝ)^(b+HalfSourceBatchGeometry.foldExponent call.factors.length) ≤
      (HalfSourceBatchFit.dimension n call:ℝ) := by
    simpa only [HalfSourceBatchGeometry.witness_bridge.1] using
      HalfSourceBatchGeometry.dimension_lower_refined n hn call
  have hdhi : (HalfSourceBatchFit.dimension n call:ℝ) ≤
      24*overhead n*(n:ℝ)^(b+HalfSourceBatchGeometry.foldExponent call.factors.length) := by
    simpa only [HalfSourceBatchFit.overheadConstant,HalfSourceBatchGeometry.witness_bridge.1,
      HalfSourceBatchGeometry.witness_bridge.2.2.2.1,overhead,mul_assoc] using HalfSourceBatchGeometry.dimension_bound n hn call
  have hq : (call.cyclic HalfSourceBatchFit.S:ℝ) ≤
      overhead n*(n:ℝ)^(HalfSourceBatchGeometry.ringExponent call.factors.length) :=
    (HalfSourceBatchGeometry.cyclic_bounds n hn call).2
  exact rawTerm_bound n hn _ _ _ _ _ _ _ (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (candidate_bound n hn) hb hN ⟨hdlo,hdhi⟩ hq i

theorem actual_stage_identity (j : Fin (R+1)) (i : Fin 7) :
    saving (HalfSourceBatchGeometry.foldExponent j.val)
      (HalfSourceBatchGeometry.ringExponent j.val) i=stageSaving j i := by
  have he := HalfSourceBatchGeometry.witness_bridge.2.1
  have hu := stageRelations.2.1
  unfold stageSaving HalfSourceBatchGeometry.foldExponent HalfSourceBatchGeometry.ringExponent
  rw [he,HalfSourceBatchGeometry.witness_bridge.2.2.2.2.1]
  by_cases hj : j.val ≤ S
  · rw [if_pos hj,Nat.min_eq_right hj,Nat.sub_eq_zero_of_le hj]
    simp
  · rw [if_neg hj,Nat.min_eq_left (Nat.le_of_lt (Nat.lt_of_not_ge hj)),←hu]

/-- The phase sums use seven separate exponents, including both source
encoders and the jointly capped high-box encoder. -/
def roundedPhaseLedger (n : ℕ) (j : Fin (R+1)) : ℝ :=
  ∑ i : Fin 7, phaseConstant i*(Real.log (n:ℝ))^(phaseLogDegree i)*
    (n:ℝ)^(3-stageSaving j i)

def allPhaseLedger (n : ℕ) : ℝ := ∑ j : Fin (R+1), roundedPhaseLedger n j

theorem roundedPhaseLedger_nonneg (n : ℕ) (hn : 3 ≤ n) (j : Fin (R+1)) :
    0 ≤ roundedPhaseLedger n j := by
  have hl : 0 ≤ Real.log (n:ℝ) := by linarith [PhaseGeometry.one_le_log_nat n hn]
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg (mul_nonneg (phaseConstant_nonneg _) (pow_nonneg hl _))
    (Real.rpow_nonneg (Nat.cast_nonneg n) _)

theorem actual_rawSum_bound (n : ℕ) (hn : 3 ≤ n) (call : HalfSourceBatchFit.Call n) :
    ((PrimePool.candidates (HalfSourceBatchFit.scale n)).card:ℝ)*
      (HalfSourceBatchFit.blocks n:ℝ)*
      (∑ i : Fin 7, rawTerm n (HalfSourceBatchGeometry.outer n call)
        (HalfSourceBatchFit.dimension n call) (call.cyclic HalfSourceBatchFit.S) i) ≤
      allPhaseLedger n := by
  let j : Fin (R+1) := ⟨call.factors.length,by exact Nat.lt_succ_of_le (call.length_le.trans_eq HalfSourceBatchGeometry.witness_bridge.2.2.2.1)⟩
  have hsum : ((PrimePool.candidates (HalfSourceBatchFit.scale n)).card:ℝ)*
      (HalfSourceBatchFit.blocks n:ℝ)*
      (∑ i : Fin 7, rawTerm n (HalfSourceBatchGeometry.outer n call)
        (HalfSourceBatchFit.dimension n call) (call.cyclic HalfSourceBatchFit.S) i) ≤ roundedPhaseLedger n j := by
    simp only [Finset.mul_sum,roundedPhaseLedger]
    apply Finset.sum_le_sum
    intro i _
    have h := actual_rawTerm_bound n hn call i
    rwa [actual_stage_identity j i] at h
  exact hsum.trans (Finset.single_le_sum
    (fun j _ => roundedPhaseLedger_nonneg n hn j) (Finset.mem_univ j))

theorem allPhaseLedgerBigO (k : ℕ) :
    (fun n : ℕ => (Real.log (n:ℝ))^k*allPhaseLedger n)
      =O[atTop] (fun n : ℕ => (n:ℝ)^(14963431313/5000000000:ℝ)) := by
  have h : (fun n : ℕ => ∑ j : Fin (R+1), ∑ i : Fin 7,
      phaseConstant i*((Real.log (n:ℝ))^(k+phaseLogDegree i)*(n:ℝ)^(3-stageSaving j i)))
      =O[atTop] (fun n : ℕ => (n:ℝ)^targetExponent) := by
    apply Asymptotics.IsBigO.sum
    intro j _
    apply Asymptotics.IsBigO.sum
    intro i _
    exact (AsymptoticCosts.logPowMulRpowBigO (stageExponentStrict j i)
      (k+phaseLogDegree i)).const_mul_left (phaseConstant i)
  simpa only [allPhaseLedger,roundedPhaseLedger,Finset.mul_sum,pow_add,mul_assoc,
    mul_left_comm,targetValue] using h

/-- Aggregate raw cost for one actual candidate product family. -/
def phaseRawSum (n : ℕ) (call : HalfSourceBatchFit.Call n) : ℝ :=
  (HalfSourceBatchFit.blocks n:ℝ)*∑ i : Fin 7,
    rawTerm n (HalfSourceBatchGeometry.outer n call)
      (HalfSourceBatchFit.dimension n call) (call.cyclic HalfSourceBatchFit.S) i

theorem phaseRawSum_nonneg (n : ℕ) (call : HalfSourceBatchFit.Call n) : 0 ≤ phaseRawSum n call := by
  unfold phaseRawSum
  apply mul_nonneg (Nat.cast_nonneg _)
  exact Finset.sum_nonneg (fun i _ => rawTerm_nonneg _ _ _ _
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _) i)

theorem allPhaseLedger_nonneg (n : ℕ) (hn : 3 ≤ n) : 0 ≤ allPhaseLedger n :=
  Finset.sum_nonneg (fun j _ => roundedPhaseLedger_nonneg n hn j)

/-- Every candidate's actual raw dimensions fit one common phase envelope.
No division is used, so the empty-prime-pool case is also represented. -/
theorem phaseRawSum_charged (n : ℕ) (hn : 3 ≤ n) (call : HalfSourceBatchFit.Call n) :
    ((PrimePool.candidates (HalfSourceBatchFit.scale n)).card:ℝ)*phaseRawSum n call ≤
      allPhaseLedger n := by
  simpa only [phaseRawSum,mul_assoc] using actual_rawSum_bound n hn call

/-- Summing an adaptive sequence requires only its proved call-count cap:
all middle blocks and all candidates are retained, and the common prime
pool is charged once per round. This remains a statement about raw costs. -/
theorem callFamily_bound (n M rounds : ℕ) (hn : 3 ≤ n)
    (calls : Fin M → HalfSourceBatchFit.Call n)
    (hcount : M ≤ rounds*(PrimePool.candidates (HalfSourceBatchFit.scale n)).card) :
    (∑ i : Fin M, phaseRawSum n (calls i)) ≤ (rounds:ℝ)*allPhaseLedger n := by
  let P := (PrimePool.candidates (HalfSourceBatchFit.scale n)).card
  have hL := allPhaseLedger_nonneg n hn
  by_cases hP : P=0
  · have hM : M=0 := by change M≤rounds*P at hcount; rw [hP] at hcount; omega
    subst M
    simp only [Finset.univ_eq_empty,Finset.sum_empty]
    exact mul_nonneg (Nat.cast_nonneg _) hL
  · have hPpos : (0:ℝ)<P := by exact_mod_cast Nat.pos_of_ne_zero hP
    apply (mul_le_mul_iff_right₀ hPpos).mp
    calc
      (P:ℝ)*(∑ i : Fin M, phaseRawSum n (calls i)) =
          ∑ i : Fin M, (P:ℝ)*phaseRawSum n (calls i) := Finset.mul_sum _ _ _
      _ ≤ ∑ _i : Fin M, allPhaseLedger n := Finset.sum_le_sum
        (fun i _ => phaseRawSum_charged n hn (calls i))
      _ = (M:ℝ)*allPhaseLedger n := by simp
      _ ≤ ((rounds*P:ℕ):ℝ)*allPhaseLedger n :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hcount) hL
      _ = (P:ℝ)*((rounds:ℝ)*allPhaseLedger n) := by push_cast; ring

/-- Arbitrary fixed powers of log n in restarts, bit levels, candidates'
bookkeeping and APSP repeated squaring are absorbed by the strict margin. -/
theorem callFamilyBigO (k : ℕ) (C : ℝ) :
    (fun n : ℕ => C*(Real.log (n:ℝ))^k*allPhaseLedger n)
      =O[atTop] (fun n : ℕ => (n:ℝ)^(14963431313/5000000000:ℝ)) := by
  simpa only [mul_assoc] using (allPhaseLedgerBigO k).const_mul_left C

#print axioms candidate_bound
#print axioms actual_rawTerm_bound
#print axioms actual_stage_identity
#print axioms actual_rawSum_bound
#print axioms allPhaseLedgerBigO
#print axioms phaseRawSum_charged
#print axioms callFamily_bound
#print axioms callFamilyBigO
end
end ThinMatrix.HalfSourceComputedCosts
