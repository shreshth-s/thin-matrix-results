import ReductionCosts
import ComputedPhaseGeometry

/-!
# Computed candidate costs

The actual integer scale and block size are inserted into all six phase terms.
The controller cancels one candidate count per round. Backend arithmetic and
local counters remain explicit in the finite resource interface.
-/
namespace ThinMatrix.ComputedReductionCosts
noncomputable section
open scoped BigOperators
open ReductionCosts PhaseGeometry EntropyBounds AsymptoticCosts
open Filter Asymptotics
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
/-- Fixed logarithmic factors obtained by inserting the actual padded D. -/
def innerConstant (R : ℕ) (i : Fin 6) : ℝ :=
  if i = 0 then 1 else (24*(8192:ℝ)^R)^(innerExponent i)

def innerLogDegree (R : ℕ) (i : Fin 6) : ℕ :=
  if i = 0 then 0 else Nat.ceil ((4*R:ℕ)*innerExponent i)

def phaseConstant (R : ℕ) (i : Fin 6) : ℝ :=
  16384*((8192:ℝ)^R)^(cyclicDegree i+outerDegree i)*4^(outerDegree i)*innerConstant R i

def phaseLogDegree (R : ℕ) (i : Fin 6) : ℕ :=
  4+(4*R)*(cyclicDegree i+outerDegree i)+innerLogDegree R i

lemma monomial_normalization (n : ℝ) (hn : 0 < n)
    (ell H CD a s w e : ℝ) (k r o p d : ℕ) :
    (8192*ell^k*n^AsymptoticCosts.eta)*(2*n^(1-AsymptoticCosts.b))*n^p*(H*n^w)^r*
      (4*H*n^(1+s/2))^o*(CD*ell^d*n^(a*e)) =
    (16384*H^(r+o)*4^o*CD)*ell^(k+d)*
      n^(AsymptoticCosts.eta+(1-AsymptoticCosts.b)+(p:ℝ)+(r:ℝ)*w+
        (o:ℝ)*(1+s/2)+a*e) := by
  have hn0 := hn.le
  simp only [mul_pow]
  rw [← Real.rpow_natCast n p, ← Real.rpow_mul_natCast hn0 w r,
    ← Real.rpow_mul_natCast hn0 (1+s/2) o]
  rw [pow_add H r o, pow_add ell k d]
  rw [show AsymptoticCosts.eta+(1-AsymptoticCosts.b)+(p:ℝ)+(r:ℝ)*w+
      (o:ℝ)*(1+s/2)+a*e =
    (((AsymptoticCosts.eta+(1-AsymptoticCosts.b))+(p:ℝ))+(w*(r:ℝ)))+
      ((1+s/2)*(o:ℝ))+a*e by ring]
  simp only [Real.rpow_add hn]
  ring

lemma degree_exponent_identity (s w : ℝ) (i : Fin 6) :
    AsymptoticCosts.eta+(1-AsymptoticCosts.b)+(pairDegree i:ℝ)+(cyclicDegree i:ℝ)*w+
      (outerDegree i:ℝ)*(1+s/2)+(AsymptoticCosts.b+s)*innerExponent i =
        phaseCostExponent s w i := by
  fin_cases i <;> norm_num [phaseCostExponent, pairDegree, cyclicDegree, outerDegree,
    innerExponent] <;> ring

/-- Actual D-powers: the box saving uses D's lower bound; all positive
powers use the padded upper bound. -/
theorem actual_inner_power_bound (R S n : ℕ) (hn : 3 ≤ n)
    (call : ComputedPhaseGeometry.Call R n) (i : Fin 6) :
    (ComputedPhaseGeometry.innerDimension n call S:ℝ)^(innerExponent i) ≤
      innerConstant R i*(Real.log (n:ℝ))^(innerLogDegree R i)*
        (n:ℝ)^((AsymptoticCosts.b+foldExponent S call.factors.length)*innerExponent i) := by
  have hd := ComputedPhaseGeometry.actual_inner_bounds R S n hn call
  have hnpos : 0 < (n:ℝ) := by exact_mod_cast (show 0<n by omega)
  by_cases hi : i = 0
  · subst i
    have hg : 0 ≤ RealCertificate.G := by linarith [RealCertificate.GEnclosure.1]
    have h := Real.rpow_le_rpow_of_nonpos
      (Real.rpow_pos_of_pos hnpos (AsymptoticCosts.b+foldExponent S call.factors.length))
      hd.1 (neg_nonpos.mpr hg)
    simpa [innerExponent, innerConstant, innerLogDegree, ← Real.rpow_mul hnpos.le] using h
  · have h := poweredLogBound (4*R) (Nat.cast_nonneg (ComputedPhaseGeometry.innerDimension n call S))
      (show 0 ≤ 24*(8192:ℝ)^R by positivity) hnpos.le (one_le_log_nat n hn)
      (innerExponent_nonneg i hi) hd.2
    simpa only [innerConstant, innerLogDegree, if_neg hi] using h

/-- Insert all actual finite counts, including the candidate pool. There is
one q factor in full-vector preprocessing and LOW, and no q factor in HIGH reads. -/
theorem actual_rawTerm_bound (R S n : ℕ) (hn : 3 ≤ n)
    (call : ComputedPhaseGeometry.Call R n)
    (hs : 0 ≤ foldExponent S call.factors.length) (i : Fin 6) :
    ((PrimePool.candidates (ComputableParameters.scale n)).card:ℝ)*
      (ComputedPhaseGeometry.blockCount n:ℝ)*
      rawTerm RealCertificate.c RealCertificate.theta n (outerSize call S n)
        (ComputedPhaseGeometry.innerDimension n call S) (call.cyclic S) i ≤
      phaseConstant R i*(Real.log (n:ℝ))^(phaseLogDegree R i)*
        (n:ℝ)^(phaseCostExponent (foldExponent S call.factors.length)
          (ringExponent S call.factors.length) i) := by
  have hnpos : 0 < (n:ℝ) := by exact_mod_cast (show 0<n by omega)
  have hp := ComputedPhaseGeometry.actual_candidate_count n hn
  have hb := ComputedPhaseGeometry.blockCount_upper n (by omega)
  have hq := (ComputedPhaseGeometry.actual_cyclic_bounds R S n hn call).2
  have hN := (ComputedPhaseGeometry.actual_outer_bounds R S n hn call hs).2
  have hD := actual_inner_power_bound R S n hn call i
  rw [rawTerm_canonical]
  calc
    _ = ((PrimePool.candidates (ComputableParameters.scale n)).card:ℝ)*
      (ComputedPhaseGeometry.blockCount n:ℝ)*(n:ℝ)^(pairDegree i)*
      (call.cyclic S:ℝ)^(cyclicDegree i)*(outerSize call S n:ℝ)^(outerDegree i)*
      (ComputedPhaseGeometry.innerDimension n call S:ℝ)^(innerExponent i) := by ring
    _ ≤ (8192*(Real.log (n:ℝ))^4*(n:ℝ)^AsymptoticCosts.eta)*
        (2*(n:ℝ)^(1-AsymptoticCosts.b))*(n:ℝ)^(pairDegree i)*
        (ComputedPhaseGeometry.phaseOverhead R n*(n:ℝ)^(ringExponent S call.factors.length))^(cyclicDegree i)*
        (4*ComputedPhaseGeometry.phaseOverhead R n*(n:ℝ)^(1+foldExponent S call.factors.length/2))^(outerDegree i)*
        (innerConstant R i*(Real.log (n:ℝ))^(innerLogDegree R i)*
          (n:ℝ)^((AsymptoticCosts.b+foldExponent S call.factors.length)*innerExponent i)) := by
      have hpp : 0 ≤ ComputedPhaseGeometry.phaseOverhead R n := by
        have := ComputedPhaseGeometry.phaseOverhead_ge_one R n hn; linarith
      have hcc : 0 ≤ innerConstant R i := by unfold innerConstant; split_ifs <;> positivity
      gcongr
    _ = _ := by
      rw [monomial_normalization (n:ℝ) hnpos, degree_exponent_identity]
      unfold ComputedPhaseGeometry.phaseOverhead phaseConstant phaseLogDegree
      rw [mul_pow, pow_mul, pow_add, pow_add]
      ring

/-- The phase ledger before the final fixed-logarithm absorption. Its six
exponents are obtained from actual moduli, packed dimensions and finite counts. -/
def roundedPhaseLedger (n j : ℕ) : ℝ :=
  ∑ i : Fin 6, phaseConstant AlignedCertificate.R i*
    (Real.log (n:ℝ))^(phaseLogDegree AlignedCertificate.R i)*
    (n:ℝ)^(phaseCostExponent (foldExponent AlignedCertificate.S j)
      (ringExponent AlignedCertificate.S j) i)

lemma phaseConstant_nonneg (R : ℕ) (i : Fin 6) : 0 ≤ phaseConstant R i := by
  unfold phaseConstant innerConstant
  split_ifs <;> positivity

lemma roundedPhaseLedger_nonneg (n j : ℕ) (hn : 3 ≤ n) :
    0 ≤ roundedPhaseLedger n j := by
  have hl : 0 ≤ Real.log (n:ℝ) := by linarith [one_le_log_nat n hn]
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg (mul_nonneg (phaseConstant_nonneg _ _) (pow_nonneg hl _))
    (Real.rpow_nonneg (Nat.cast_nonneg n) _)

/-- All phases, including the unfilled start and final R-factor call. -/
def allPhaseLedger (n : ℕ) : ℝ :=
  ∑ j : Fin (AlignedCertificate.R+1), roundedPhaseLedger n j.val

lemma roundedPhaseLedger_le_all (n j : ℕ) (hn : 3 ≤ n) (hj : j ≤ AlignedCertificate.R) :
    roundedPhaseLedger n j ≤ allPhaseLedger n := by
  let idx : Fin (AlignedCertificate.R+1) := ⟨j, by omega⟩
  change roundedPhaseLedger n idx.val ≤
    ∑ a : Fin (AlignedCertificate.R+1), roundedPhaseLedger n a.val
  exact Finset.single_le_sum (fun (a : Fin (AlignedCertificate.R+1)) _ =>
    roundedPhaseLedger_nonneg n a.val hn) (Finset.mem_univ idx)

/-- Fixed finite envelopes for the six logarithmic degrees and constants. -/
def ledgerLogDegree : ℕ := ∑ i : Fin 6, phaseLogDegree AlignedCertificate.R i
def ledgerConstant : ℝ := ∑ i : Fin 6, phaseConstant AlignedCertificate.R i

lemma ledgerConstant_nonneg : 0 ≤ ledgerConstant :=
  Finset.sum_nonneg (fun i _ => phaseConstant_nonneg _ i)

lemma phaseConstant_le_ledger (i : Fin 6) : phaseConstant AlignedCertificate.R i ≤ ledgerConstant :=
  Finset.single_le_sum (fun j _ => phaseConstant_nonneg _ j) (Finset.mem_univ i)

lemma phaseLogDegree_le_ledger (i : Fin 6) :
    phaseLogDegree AlignedCertificate.R i ≤ ledgerLogDegree :=
  Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)

/-- The only extra power is the explicitly certified arithmetic charge. -/
lemma charged_term_bound (n : ℕ) (hn : 3 ≤ n)
    (j : Fin (AlignedCertificate.R+1)) (i : Fin 6) :
    (n:ℝ)^(ArithmeticSlack.extra:ℝ)*
      (phaseConstant AlignedCertificate.R i*(Real.log (n:ℝ))^(phaseLogDegree AlignedCertificate.R i)*
        (n:ℝ)^(phaseCostExponent (foldExponent AlignedCertificate.S j.val)
          (ringExponent AlignedCertificate.S j.val) i)) ≤
      ledgerConstant*(Real.log (n:ℝ))^(ledgerLogDegree)*
        AsymptoticCosts.roundedPower (3-ArithmeticSlack.chargedSaving j i) n := by
  have hnpos : 0 < (n:ℝ) := by exact_mod_cast (show 0<n by omega)
  have hlog := pow_le_pow_right₀ (one_le_log_nat n hn) (phaseLogDegree_le_ledger i)
  have hp : (n:ℝ)^(ArithmeticSlack.extra:ℝ)*
      (n:ℝ)^(phaseCostExponent (foldExponent AlignedCertificate.S j.val)
        (ringExponent AlignedCertificate.S j.val) i) =
      (n:ℝ)^(3-ArithmeticSlack.chargedSaving j i) := by
    rw [← Real.rpow_add hnpos, actual_stage_exponent_identity]
    congr 1
    unfold ArithmeticSlack.chargedSaving
    ring
  calc
    _ = phaseConstant AlignedCertificate.R i*(Real.log (n:ℝ))^(phaseLogDegree AlignedCertificate.R i)*
        ((n:ℝ)^(ArithmeticSlack.extra:ℝ)*
          (n:ℝ)^(phaseCostExponent (foldExponent AlignedCertificate.S j.val)
            (ringExponent AlignedCertificate.S j.val) i)) := by ring
    _ = phaseConstant AlignedCertificate.R i*(Real.log (n:ℝ))^(phaseLogDegree AlignedCertificate.R i)*
        (n:ℝ)^(3-ArithmeticSlack.chargedSaving j i) := by rw [hp]
    _ ≤ ledgerConstant*(Real.log (n:ℝ))^(ledgerLogDegree)*
        AsymptoticCosts.roundedPower (3-ArithmeticSlack.chargedSaving j i) n := by
      have hr := Nat.le_ceil ((n:ℝ)^(3-ArithmeticSlack.chargedSaving j i))
      have hc := phaseConstant_le_ledger i
      have hc0 := phaseConstant_nonneg AlignedCertificate.R i
      have hledger := ledgerConstant_nonneg
      have hl0 : 0 ≤ Real.log (n:ℝ) := by linarith [one_le_log_nat n hn]
      change _ ≤ ledgerConstant*(Real.log (n:ℝ))^(ledgerLogDegree)*
        (Nat.ceil ((n:ℝ)^(3-ArithmeticSlack.chargedSaving j i)):ℝ)
      gcongr

/-- A finite sum over the actual stages fits the rounded charged ledger.
No algorithmic time bound is a premise of this algebraic conversion. -/
theorem charged_allPhaseLedger_bound (n : ℕ) (hn : 3 ≤ n) :
    (n:ℝ)^(ArithmeticSlack.extra:ℝ)*allPhaseLedger n ≤
      ledgerConstant*(Real.log (n:ℝ))^(ledgerLogDegree)*
        ∑ j : Fin (AlignedCertificate.R+1), ∑ i : Fin 6,
          AsymptoticCosts.roundedPower (3-ArithmeticSlack.chargedSaving j i) n := by
  unfold allPhaseLedger roundedPhaseLedger
  simp only [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  apply Finset.sum_le_sum
  intro i _
  exact charged_term_bound n hn j i


theorem charged_allPhaseLedger_le_chargedCost (n : ℕ) (hn : 3 ≤ n) :
    (n:ℝ)^(ArithmeticSlack.extra:ℝ)*allPhaseLedger n ≤
      ledgerConstant*ArithmeticSlack.chargedCost ledgerLogDegree n := by
  apply (charged_allPhaseLedger_bound n hn).trans
  have hp := ReductionCosts.chargedSum_le_chargedCost n ledgerLogDegree hn
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hp ledgerConstant_nonneg

/-- The six terms after the actual integer block count has been inserted. -/
def phaseRawSum (n : ℕ) (call : ComputedPhaseGeometry.Call AlignedCertificate.R n) : ℝ :=
  ∑ i : Fin 6, (ComputedPhaseGeometry.blockCount n:ℝ)*
    rawTerm RealCertificate.c RealCertificate.theta n (outerSize call AlignedCertificate.S n)
      (ComputedPhaseGeometry.innerDimension n call AlignedCertificate.S)
      (call.cyclic AlignedCertificate.S) i

/-- Uniform insertion of the actual candidate count into a call's six terms. -/
theorem actual_rawSum_bound (n : ℕ) (hn : 3 ≤ n)
    (call : ComputedPhaseGeometry.Call AlignedCertificate.R n) :
    ((PrimePool.candidates (ComputableParameters.scale n)).card:ℝ)*phaseRawSum n call ≤
      roundedPhaseLedger n call.factors.length := by
  unfold phaseRawSum roundedPhaseLedger
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have hs := (aligned_fold_exponent_range call.factors.length).1
  simpa only [mul_assoc] using
    actual_rawTerm_bound AlignedCertificate.R AlignedCertificate.S n hn call hs i

lemma allPhaseLedger_nonneg (n : ℕ) (hn : 3 ≤ n) : 0 ≤ allPhaseLedger n :=
  Finset.sum_nonneg (fun j _ => roundedPhaseLedger_nonneg n j.val hn)

/-- A finite backend ledger is inserted before the candidate cancellation. -/
theorem actual_callCost_bound (n : ℕ) (hn : 3 ≤ n)
    (call : ComputedPhaseGeometry.Call AlignedCertificate.R n) (cost : ℕ)
    (B : ℝ) (hB : 0 ≤ B) (hcost : (cost:ℝ) ≤ B*phaseRawSum n call) :
    ((PrimePool.candidates (ComputableParameters.scale n)).card:ℝ)*(cost:ℝ) ≤
      B*roundedPhaseLedger n call.factors.length := by
  calc
    _ ≤ ((PrimePool.candidates (ComputableParameters.scale n)).card:ℝ)*
        (B*phaseRawSum n call) :=
      mul_le_mul_of_nonneg_left hcost (Nat.cast_nonneg _)
    _ = B*(((PrimePool.candidates (ComputableParameters.scale n)).card:ℝ)*
        phaseRawSum n call) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (actual_rawSum_bound n hn call) hB

/-- The count of actual candidate calls cancels exactly once per controller
round. The costs can be any concrete finite counters with the displayed local
six-term bound. -/
theorem callCost_batch_bound {n count : ℕ}
    (calls : Fin count → ComputedPhaseGeometry.Call AlignedCertificate.R n)
    (cost : Fin count → ℕ) (hn : 3 ≤ n) (rounds : ℕ)
    (hcount : count ≤ rounds*(PrimePool.candidates (ComputableParameters.scale n)).card)
    (B : ℝ) (hB : 0 ≤ B)
    (hcost : ∀ i, (cost i:ℝ) ≤ B*phaseRawSum n (calls i)) :
    (∑ i, cost i:ℕ) ≤ (rounds:ℝ)*B*allPhaseLedger n := by
  have h := counted_batch_bound count (PrimePool.candidates (ComputableParameters.scale n)).card
    rounds cost (B*allPhaseLedger n) (mul_nonneg hB (allPhaseLedger_nonneg n hn))
    hcount (by
      intro i
      apply (actual_callCost_bound n hn (calls i) (cost i) B hB (hcost i)).trans
      exact mul_le_mul_of_nonneg_left
        (roundedPhaseLedger_le_all n (calls i).factors.length hn (calls i).length_le) hB)
  simpa only [mul_assoc] using h

/-- All logarithmic overheads are fixed but their degrees are left explicit,
so this interface accepts the actual backend's arithmetic and array counters. -/
theorem callCost_batch_le_chargedSum {n count : ℕ}
    (calls : Fin count → ComputedPhaseGeometry.Call AlignedCertificate.R n)
    (cost : Fin count → ℕ) (hn : 3 ≤ n) (rounds : ℕ)
    (hcount : count ≤ rounds*(PrimePool.candidates (ComputableParameters.scale n)).card)
    (A CB Cbit Cround : ℝ) (localLog bitLog roundLog : ℕ)
    (hA : 0 ≤ A) (hCB : 0 ≤ CB) (hCbit : 0 ≤ Cbit) (hCround : 0 ≤ Cround)
    (hcost : ∀ i, (cost i:ℝ) ≤
      A*CB*(Real.log (n:ℝ))^localLog*phaseRawSum n (calls i))
    (harithmetic : A ≤ Cbit*(Real.log (n:ℝ))^bitLog*(n:ℝ)^(ArithmeticSlack.extra:ℝ))
    (hrounds : (rounds:ℝ) ≤ Cround*(Real.log (n:ℝ))^roundLog) :
    (∑ i, cost i:ℕ) ≤
      (Cround*Cbit*CB*ledgerConstant)*
        (Real.log (n:ℝ))^(roundLog+bitLog+localLog+ledgerLogDegree)*
        ∑ j : Fin (AlignedCertificate.R+1), ∑ i : Fin 6,
          AsymptoticCosts.roundedPower (3-ArithmeticSlack.chargedSaving j i) n := by
  have hl : 0 ≤ Real.log (n:ℝ) := by linarith [one_le_log_nat n hn]
  have hB : 0 ≤ A*CB*(Real.log (n:ℝ))^localLog :=
    mul_nonneg (mul_nonneg hA hCB) (pow_nonneg hl _)
  have h := callCost_batch_bound calls cost hn rounds hcount
    (A*CB*(Real.log (n:ℝ))^localLog) hB hcost
  have hall := allPhaseLedger_nonneg n hn
  have hsum := charged_allPhaseLedger_bound n hn
  calc
    _ ≤ (rounds:ℝ)*(A*CB*(Real.log (n:ℝ))^localLog)*allPhaseLedger n := h
    _ = (rounds:ℝ)*A*CB*(Real.log (n:ℝ))^localLog*allPhaseLedger n := by ring
    _ ≤ (Cround*(Real.log (n:ℝ))^roundLog)*
        (Cbit*(Real.log (n:ℝ))^bitLog*(n:ℝ)^(ArithmeticSlack.extra:ℝ))*
        CB*(Real.log (n:ℝ))^localLog*allPhaseLedger n := by
      have hrA := mul_le_mul hrounds harithmetic hA
        (mul_nonneg hCround (pow_nonneg hl roundLog))
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hrA hCB)
          (pow_nonneg hl localLog)) hall
    _ = (Cround*Cbit*CB)*(Real.log (n:ℝ))^(roundLog+bitLog+localLog)*
        ((n:ℝ)^(ArithmeticSlack.extra:ℝ)*allPhaseLedger n) := by
      simp only [pow_add]
      ring
    _ ≤ (Cround*Cbit*CB)*(Real.log (n:ℝ))^(roundLog+bitLog+localLog)*
        (ledgerConstant*(Real.log (n:ℝ))^ledgerLogDegree*
          ∑ j : Fin (AlignedCertificate.R+1), ∑ i : Fin 6,
            AsymptoticCosts.roundedPower (3-ArithmeticSlack.chargedSaving j i) n) :=
      mul_le_mul_of_nonneg_left hsum
        (mul_nonneg (mul_nonneg (mul_nonneg hCround hCbit) hCB)
          (pow_nonneg hl _))
    _ = _ := by rw [pow_add]; ring

/-- A computed-call batch is bounded by the complete certified charged ledger,
including the exact additional arithmetic power. -/
theorem callCost_batch_le_chargedCost {n count : ℕ}
    (calls : Fin count → ComputedPhaseGeometry.Call AlignedCertificate.R n)
    (cost : Fin count → ℕ) (hn : 3 ≤ n) (rounds : ℕ)
    (hcount : count ≤ rounds*(PrimePool.candidates (ComputableParameters.scale n)).card)
    (A CB Cbit Cround : ℝ) (localLog bitLog roundLog : ℕ)
    (hA : 0 ≤ A) (hCB : 0 ≤ CB) (hCbit : 0 ≤ Cbit) (hCround : 0 ≤ Cround)
    (hcost : ∀ i, (cost i:ℝ) ≤
      A*CB*(Real.log (n:ℝ))^localLog*phaseRawSum n (calls i))
    (harithmetic : A ≤ Cbit*(Real.log (n:ℝ))^bitLog*(n:ℝ)^(ArithmeticSlack.extra:ℝ))
    (hrounds : (rounds:ℝ) ≤ Cround*(Real.log (n:ℝ))^roundLog) :
    (∑ i, cost i:ℕ) ≤ (Cround*Cbit*CB*ledgerConstant)*
      ArithmeticSlack.chargedCost (roundLog+bitLog+localLog+ledgerLogDegree) n := by
  apply (callCost_batch_le_chargedSum calls cost hn rounds hcount A CB Cbit Cround
    localLog bitLog roundLog hA hCB hCbit hCround hcost harithmetic hrounds).trans
  have hp := chargedSum_le_chargedCost n (roundLog+bitLog+localLog+ledgerLogDegree) hn
  have hc : 0 ≤ Cround*Cbit*CB*ledgerConstant :=
    mul_nonneg (mul_nonneg (mul_nonneg hCround hCbit) hCB) ledgerConstant_nonneg
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hp hc

/-- The executable pool excludes 3. Its smaller actual call count satisfies
the same complete candidate charge. -/
theorem callCost_batch_le_chargedCost_pool {n count : ℕ}
    (calls : Fin count → ComputedPhaseGeometry.Call AlignedCertificate.R n)
    (cost : Fin count → ℕ) (hn : 3 ≤ n) (rounds : ℕ)
    (hcount : count ≤ rounds*(ComputableParameters.computedPool n).card)
    (A CB Cbit Cround : ℝ) (localLog bitLog roundLog : ℕ)
    (hA : 0 ≤ A) (hCB : 0 ≤ CB) (hCbit : 0 ≤ Cbit) (hCround : 0 ≤ Cround)
    (hcost : ∀ i, (cost i:ℝ) ≤
      A*CB*(Real.log (n:ℝ))^localLog*phaseRawSum n (calls i))
    (harithmetic : A ≤ Cbit*(Real.log (n:ℝ))^bitLog*(n:ℝ)^(ArithmeticSlack.extra:ℝ))
    (hrounds : (rounds:ℝ) ≤ Cround*(Real.log (n:ℝ))^roundLog) :
    (∑ i, cost i:ℕ) ≤ (Cround*Cbit*CB*ledgerConstant)*
      ArithmeticSlack.chargedCost (roundLog+bitLog+localLog+ledgerLogDegree) n := by
  have hc := hcount.trans (Nat.mul_le_mul_left rounds
    (Finset.card_le_card (ComputedPhaseGeometry.computedPool_subset_candidates n)))
  exact callCost_batch_le_chargedCost calls cost hn rounds hc A CB Cbit Cround
    localLog bitLog roundLog hA hCB hCbit hCround hcost harithmetic hrounds

/-- Uniform families of actual computed calls inherit the exact certified
exponent after their finite backend counters and controller counts are inserted. -/
theorem callCost_batch_bigO
    (count rounds : ℕ → ℕ)
    (calls : (n : ℕ) → Fin (count n) → ComputedPhaseGeometry.Call AlignedCertificate.R n)
    (cost : (n : ℕ) → Fin (count n) → ℕ)
    (A : ℕ → ℝ) (CB Cbit Cround : ℝ) (localLog bitLog roundLog : ℕ)
    (hCB : 0 ≤ CB) (hCbit : 0 ≤ Cbit) (hCround : 0 ≤ Cround)
    (hresources : ∀ᶠ n : ℕ in atTop,
      count n ≤ rounds n*(ComputableParameters.computedPool n).card ∧
      0 ≤ A n ∧
      (∀ i, (cost n i:ℝ) ≤ A n*CB*(Real.log (n:ℝ))^localLog*phaseRawSum n (calls n i)) ∧
      A n ≤ Cbit*(Real.log (n:ℝ))^bitLog*(n:ℝ)^(ArithmeticSlack.extra:ℝ) ∧
      (rounds n:ℝ) ≤ Cround*(Real.log (n:ℝ))^roundLog) :
    (fun n => ((∑ i, cost n i:ℕ):ℝ)) =O[atTop]
      (fun n : ℕ => (n:ℝ)^(299294792/100000000:ℝ)) := by
  let K := roundLog+bitLog+localLog+ledgerLogDegree
  let C := Cround*Cbit*CB*ledgerConstant
  have hdom : ∀ᶠ n : ℕ in atTop,
      ((∑ i, cost n i:ℕ):ℝ) ≤ C*ArithmeticSlack.chargedCost K n := by
    filter_upwards [hresources, eventually_ge_atTop (3:ℕ)] with n hr hn
    rcases hr with ⟨hcount, hA, hcost, harithmetic, hrounds⟩
    exact callCost_batch_le_chargedCost_pool (calls n) (cost n) hn (rounds n) hcount
      (A n) CB Cbit Cround localLog bitLog roundLog hA hCB hCbit hCround
      hcost harithmetic hrounds
  have hO : (fun n => ((∑ i, cost n i:ℕ):ℝ)) =O[atTop]
      ArithmeticSlack.chargedCost K := by
    apply IsBigO.of_bound C
    filter_upwards [hdom, eventually_ge_atTop (3:ℕ)] with n hb hn
    simpa only [Real.norm_of_nonneg (Nat.cast_nonneg (∑ i, cost n i)),
      Real.norm_of_nonneg (chargedCost_nonneg K n hn)] using hb
  exact hO.trans (ArithmeticSlack.chargedCostBigO K)

end
end ThinMatrix.ComputedReductionCosts

#print axioms ThinMatrix.ComputedReductionCosts.actual_inner_power_bound
#print axioms ThinMatrix.ComputedReductionCosts.actual_rawTerm_bound
#print axioms ThinMatrix.ComputedReductionCosts.actual_rawSum_bound
#print axioms ThinMatrix.ComputedReductionCosts.callCost_batch_le_chargedCost
#print axioms ThinMatrix.ComputedReductionCosts.callCost_batch_le_chargedCost_pool
#print axioms ThinMatrix.ComputedReductionCosts.callCost_batch_bigO
