import AsymptoticCosts

/-!
# Explicit slack for slightly superlinear exact cyclic multiplication

This file checks an additional arithmetic charge, without claiming that a
fast multiplication program exists. A complete-vector multiplication cost
q^(1+10^-8), instead of q, adds at most `extra` to the exponent because the
cyclic-factor exponent is at most v. The witness and claimed APSP exponent
are unchanged. There remains a positive, explicitly checked margin.
-/

namespace ThinMatrix.ArithmeticSlack
noncomputable section
open Filter Asymptotics
open scoped BigOperators
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000

def epsilon : Rat := 1 / 100000000
def extra : Rat := epsilon * AlignedCertificate.v
def margin : Rat := 1 / 10000000000

theorem numericalMarginsWithArithmetic :
    AlignedCertificate.checks.all (fun check =>
      if check.target = AlignedCertificate.delta then
        decide (check.target + extra + margin < AlignedCertificate.lower check.expression)
      else true) = true := by
  decide +kernel

theorem arithmeticChargeValue :
    extra = 1063767082718043 / 10000000000000000000000000 ∧
    0 < epsilon ∧ 0 < extra ∧ 0 < margin := by
  decide +kernel

theorem realRuntimeMargin (check : AlignedCertificate.Check)
    (hm : check ∈ AlignedCertificate.checks)
    (ht : check.target = AlignedCertificate.delta) :
    (check.target : ℝ) + (extra : ℝ) + (margin : ℝ) <
      RealCertificate.evalReal check.expression := by
  have hb := (List.all_eq_true.mp numericalMarginsWithArithmetic) check hm
  rw [if_pos ht] at hb
  have hr : check.target + extra + margin < AlignedCertificate.lower check.expression :=
    of_decide_eq_true hb
  have hc : (check.target : ℝ) + (extra : ℝ) + (margin : ℝ) <
      (AlignedCertificate.lower check.expression : ℝ) := by exact_mod_cast hr
  exact lt_of_lt_of_le hc (RealCertificate.lowerLeActual check.expression)

private theorem scalarEndpoint (x : Rat) (tag : String)
    (hm : ∀ ch ∈ AlignedCertificate.scalarPhase x tag, ch ∈ AlignedCertificate.checks)
    (i : Fin 6) :
    AsymptoticCosts.delta + (extra : ℝ) + (margin : ℝ) ≤
      AsymptoticCosts.scalarSaving (x : ℝ) i := by
  let ch := (AlignedCertificate.scalarPhase x tag)[i.val]'(by
    simp only [AlignedCertificate.scalarPhase, List.length_cons, List.length_nil]
    omega)
  have ht : ch.target = AlignedCertificate.delta := by
    fin_cases i <;> simp [ch, AlignedCertificate.scalarPhase]
  have hc := (realRuntimeMargin ch (hm ch (List.getElem_mem _)) ht).le
  fin_cases i <;>
    norm_num [ch, AlignedCertificate.scalarPhase, RealCertificate.evalReal,
      AsymptoticCosts.scalarSaving, AsymptoticCosts.b, AsymptoticCosts.eta,
      AsymptoticCosts.delta, RealCertificate.q2Identity, RealCertificate.Esource,
      RealCertificate.Ebox, RealCertificate.theta, AlignedCertificate.theta] at hc ⊢ <;>
    linarith

private theorem cyclicEndpoint (z : Rat) (tag : String)
    (hm : ∀ ch ∈ AlignedCertificate.cyclicPhase z tag, ch ∈ AlignedCertificate.checks)
    (i : Fin 6) :
    AsymptoticCosts.delta + (extra : ℝ) + (margin : ℝ) ≤
      AsymptoticCosts.cyclicSaving (z : ℝ) i := by
  let ch := (AlignedCertificate.cyclicPhase z tag)[i.val]'(by
    simp only [AlignedCertificate.cyclicPhase, List.length_cons, List.length_nil]
    omega)
  have ht : ch.target = AlignedCertificate.delta := by
    fin_cases i <;> simp [ch, AlignedCertificate.cyclicPhase]
  have hc := (realRuntimeMargin ch (hm ch (List.getElem_mem _)) ht).le
  fin_cases i <;>
    norm_num [ch, AlignedCertificate.cyclicPhase, RealCertificate.evalReal,
      AsymptoticCosts.cyclicSaving, AsymptoticCosts.b, AsymptoticCosts.eta,
      AsymptoticCosts.delta, AsymptoticCosts.u, AsymptoticCosts.e,
      RealCertificate.q2Identity, RealCertificate.Esource,
      RealCertificate.Ebox, RealCertificate.theta, AlignedCertificate.theta] at hc ⊢ <;>
    linarith

private theorem affineLower (A B hi x lower : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ hi)
    (h0 : lower ≤ A+B*0) (h1 : lower ≤ A+B*hi) : lower ≤ A+B*x := by
  by_cases hB : 0 ≤ B
  · have h := mul_le_mul_of_nonneg_left hx0 hB
    linarith
  · have h := mul_le_mul_of_nonpos_left hx1 (le_of_not_ge hB)
    linarith

theorem scalarAllStages (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ AsymptoticCosts.u)
    (i : Fin 6) :
    AsymptoticCosts.delta + (margin : ℝ) ≤
      AsymptoticCosts.scalarSaving x i - (extra : ℝ) := by
  have h0 := scalarEndpoint 0 "initial"
    (by intro ch hm; simp only [AlignedCertificate.checks, List.mem_append]; aesop) i
  have h1 := scalarEndpoint AlignedCertificate.u "freeze"
    (by intro ch hm; simp only [AlignedCertificate.checks, List.mem_append]; aesop) i
  have h := affineLower (AsymptoticCosts.scalarSaving 0 i)
    (AsymptoticCosts.scalarSlope i) AsymptoticCosts.u x
    (AsymptoticCosts.delta+(extra : ℝ)+(margin : ℝ)) hx0 hx1
    (by simpa using h0)
    (by simpa only [← AsymptoticCosts.scalarAffine, AsymptoticCosts.u] using h1)
  rw [← AsymptoticCosts.scalarAffine] at h
  linarith

theorem cyclicAllStages (z : ℝ) (hz0 : 0 ≤ z) (hz1 : z ≤ AsymptoticCosts.v)
    (i : Fin 6) :
    AsymptoticCosts.delta + (margin : ℝ) ≤
      AsymptoticCosts.cyclicSaving z i - (extra : ℝ) := by
  have h0 := cyclicEndpoint 0 "start"
    (by intro ch hm; simp only [AlignedCertificate.checks, List.mem_append]; aesop) i
  have h1 := cyclicEndpoint AlignedCertificate.v "final"
    (by intro ch hm; simp only [AlignedCertificate.checks, List.mem_append]; aesop) i
  have h := affineLower (AsymptoticCosts.cyclicSaving 0 i)
    (AsymptoticCosts.cyclicSlope i) AsymptoticCosts.v z
    (AsymptoticCosts.delta+(extra : ℝ)+(margin : ℝ)) hz0 hz1
    (by simpa using h0)
    (by simpa only [← AsymptoticCosts.cyclicAffine, AsymptoticCosts.v] using h1)
  rw [← AsymptoticCosts.cyclicAffine] at h
  linarith

/-- A uniform ledger which conservatively adds the arithmetic charge to
every phase, including phases which only use linear operations. -/
def chargedSaving (j : Fin (AlignedCertificate.R+1)) (i : Fin 6) : ℝ :=
  AsymptoticCosts.stageSaving j i - (extra : ℝ)

theorem chargedStageMargin (j : Fin (AlignedCertificate.R+1)) (i : Fin 6) :
    AsymptoticCosts.delta + (margin : ℝ) ≤ chargedSaving j i := by
  rcases AsymptoticCosts.stageRelations with ⟨hη, hu, hv⟩
  have hjR : j.val ≤ AlignedCertificate.R := Nat.le_of_lt_succ j.isLt
  unfold chargedSaving AsymptoticCosts.stageSaving
  split_ifs with hj
  · apply scalarAllStages _ (mul_nonneg (Nat.cast_nonneg _) hη) _ i
    rw [hu]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hj) hη
  · apply cyclicAllStages _ (mul_nonneg (Nat.cast_nonneg _) hη) _ i
    rw [hv]
    apply mul_le_mul_of_nonneg_right _ hη
    exact_mod_cast Nat.sub_le_sub_right hjR AlignedCertificate.S

theorem chargedExponentStrict (j : Fin (AlignedCertificate.R+1)) (i : Fin 6) :
    3-chargedSaving j i < AsymptoticCosts.targetExponent := by
  have hs := chargedStageMargin j i
  have hm : 0 < (margin : ℝ) := by norm_num [margin]
  unfold AsymptoticCosts.targetExponent
  linarith

def chargedCost (k n : ℕ) : ℝ :=
  ((AlignedCertificate.R : ℝ)+1)^2 *
    (Real.log (n : ℝ))^(k+AlignedCertificate.R+10) *
    (AsymptoticCosts.roundedPower 2 n +
      AsymptoticCosts.roundedPower (3-(AsymptoticCosts.b-AsymptoticCosts.eta)) n +
      ∑ j : Fin (AlignedCertificate.R+1), ∑ i : Fin 6,
        AsymptoticCosts.roundedPower (3-chargedSaving j i) n)

theorem chargedCostBigO (k : ℕ) :
    chargedCost k =O[atTop]
      (fun n : ℕ => (n : ℝ)^(299294792 / 100000000 : ℝ)) := by
  let K := k+AlignedCertificate.R+10
  have hd : 0 < AsymptoticCosts.targetExponent :=
    lt_trans (by norm_num) AsymptoticCosts.targetAboveTwo
  have hscan := AsymptoticCosts.roundedLogPowBigO
    AsymptoticCosts.targetAboveTwo hd K
  have hbook := AsymptoticCosts.roundedLogPowBigO
    AsymptoticCosts.bookkeepingExponentStrict hd K
  have hstages : (fun n : ℕ =>
      ∑ j : Fin (AlignedCertificate.R+1), ∑ i : Fin 6,
        (Real.log (n : ℝ))^K *
          AsymptoticCosts.roundedPower (3-chargedSaving j i) n)
      =O[atTop] (fun n : ℕ => (n : ℝ)^AsymptoticCosts.targetExponent) := by
    apply IsBigO.sum
    intro j _
    apply IsBigO.sum
    intro i _
    exact AsymptoticCosts.roundedLogPowBigO (chargedExponentStrict j i) hd K
  have h := ((hscan.add hbook).add hstages).const_mul_left
    (((AlignedCertificate.R : ℝ)+1)^2)
  change (fun n : ℕ => ((AlignedCertificate.R : ℝ)+1)^2 *
    (Real.log (n : ℝ))^(k+AlignedCertificate.R+10) *
    (AsymptoticCosts.roundedPower 2 n +
      AsymptoticCosts.roundedPower (3-(AsymptoticCosts.b-AsymptoticCosts.eta)) n +
      ∑ j : Fin (AlignedCertificate.R+1), ∑ i : Fin 6,
        AsymptoticCosts.roundedPower (3-chargedSaving j i) n)) =O[atTop] _
  simpa only [K, mul_add, Finset.mul_sum, mul_assoc,
    AsymptoticCosts.targetValue] using h

/-- Polynomial-logarithmic padding on a cyclic length remains padding
after the small arithmetic exponent. This is a finite inequality, not an
assumption that the multiplication implementation meets a cost bound. -/
theorem cyclicLengthFactor (n q k : ℕ) (C : ℝ) (hC : 1 ≤ C)
    (hn : 1 ≤ (n : ℝ)) (hlog : 1 ≤ Real.log (n : ℝ))
    (hq : (q : ℝ) ≤ C*(Real.log (n : ℝ))^k*(n : ℝ)^AsymptoticCosts.v) :
    (q : ℝ)^(epsilon : ℝ) ≤
      C*(Real.log (n : ℝ))^k*(n : ℝ)^(extra : ℝ) := by
  have he0 : (0:ℝ) ≤ (epsilon : ℝ) := by norm_num [epsilon]
  have he1 : (epsilon : ℝ) ≤ 1 := by norm_num [epsilon]
  have hn0 : 0 ≤ (n : ℝ) := le_trans (by norm_num) hn
  have hl0 : 0 ≤ (Real.log (n : ℝ))^k :=
    pow_nonneg (le_trans (by norm_num) hlog) k
  have hc0 : 0 ≤ C := le_trans (by norm_num) hC
  have hv0 := Real.rpow_nonneg hn0 AsymptoticCosts.v
  have hb := Real.rpow_le_rpow (Nat.cast_nonneg q) hq he0
  have hc := Real.rpow_le_self_of_one_le hC he1
  have hl : ((Real.log (n : ℝ))^k)^(epsilon : ℝ) ≤ (Real.log (n : ℝ))^k :=
    Real.rpow_le_self_of_one_le (one_le_pow₀ hlog) he1
  have hextra : AsymptoticCosts.v*(epsilon : ℝ) = (extra : ℝ) := by
    norm_num [AsymptoticCosts.v, extra, epsilon]
    ring
  calc
    (q : ℝ)^(epsilon : ℝ) ≤
        (C*(Real.log (n : ℝ))^k*(n : ℝ)^AsymptoticCosts.v)^(epsilon : ℝ) := hb
    _ = C^(epsilon : ℝ)*((Real.log (n : ℝ))^k)^(epsilon : ℝ)*
        (n : ℝ)^(extra : ℝ) := by
      rw [Real.mul_rpow (mul_nonneg hc0 hl0) hv0,
        Real.mul_rpow hc0 hl0, ← Real.rpow_mul hn0, hextra]
    _ ≤ C*(Real.log (n : ℝ))^k*(n : ℝ)^(extra : ℝ) := by
      gcongr

#print axioms numericalMarginsWithArithmetic
#print axioms arithmeticChargeValue
#print axioms realRuntimeMargin
#print axioms scalarAllStages
#print axioms cyclicAllStages
#print axioms chargedStageMargin
#print axioms chargedCostBigO
#print axioms cyclicLengthFactor

end
end ThinMatrix.ArithmeticSlack
