import StoredMinPlusAPSP
import ArithmeticSlack
import PhaseGeometry
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Uniform composition of the stored APSP program's returned resources

This module composes the resource fields returned by the actual stored
repeated-squaring program. Its callback premise is deliberately explicit:
an eventual bound for every bounded adaptive query must be proved for the
concrete improved oracle. The theorem does not invent a runtime for a
functionally correct oracle, and does not assert a Light/RAM refinement.
-/

namespace ThinMatrix.UniformAPSPBound
noncomputable section
open Filter Asymptotics StoredMinPlusAPSP
open scoped BigOperators

def logFactor : ℝ := 1 / Real.log 2 + 1

theorem logFactor_pos : 0 < logFactor := by
  unfold logFactor
  positivity

theorem log2_add_one_le (n : ℕ) (hn : 3 ≤ n) :
    ((n.log2 + 1 : ℕ) : ℝ) ≤ logFactor * Real.log (n : ℝ) := by
  have h := Real.log2_le_logb n
  have hl := PhaseGeometry.one_le_log_nat n hn
  simp only [Real.logb, Nat.cast_add, Nat.cast_one] at h ⊢
  unfold logFactor
  calc
    (n.log2 : ℝ) + 1 ≤ Real.log (n:ℝ) / Real.log 2 + Real.log (n:ℝ) := add_le_add h hl
    _ = _ := by ring

/-- The resource sites recorded by this same returned execution. Pricing a
formation site by a bit-width factor is the concrete backend's final step. -/
def executionSites {n : ℕ} {Payload : Type}
    (e : Execution n (Option ℤ) Payload) : ℕ :=
  e.oracleWork + e.answerWrites + e.formationWrites

private theorem sum_call_resources_le {n : ℕ} {Payload : Type}
    (calls : List (Call n Payload)) (F : ℝ)
    (h : ∀ c ∈ calls, (c.output.work : ℝ) + c.output.answerWrites ≤ F) :
    (callWork calls : ℝ) + callAnswerWrites calls ≤ (calls.length : ℝ)*F := by
  induction calls with
  | nil => simp [callWork, callAnswerWrites]
  | cons c cs ih =>
    have hc := h c (by simp)
    have ht := ih (by intro d hd; exact h d (by simp [hd]))
    simp only [callWork, callAnswerWrites, List.map_cons, List.sum_cons,
      Nat.cast_add, List.length_cons, Nat.cast_one] at ht ⊢
    nlinarith

theorem actual_callback_resources_le {n : ℕ} {Payload : Type}
    (O : DenseOracle n Payload) (hO : DenseOracleCorrect O)
    (w : OptionalTable n) (W : ℕ) (hw : APSPReduction.EdgeBound (decode w) W)
    (F : ℝ)
    (hF : ∀ A B T, APSPAlgorithm.SymmetricQueryBound (decode A, decode B, decode T)
      (64*n*W+13 : ℕ) → (O A B T).work + ((O A B T).answerWrites : ℝ) ≤ F) :
    ((apsp O w W).oracleWork : ℝ) + (apsp O w W).answerWrites ≤
      ((apsp O w W).calls.length : ℝ)*F := by
  have hc : ∀ c ∈ (apsp O w W).calls,
      (c.output.work : ℝ) + c.output.answerWrites ≤ F := by
    intro c hc
    have hb := apsp_query_bound O hO w W hw c hc
    have hf := apsp_calls_faithful O w W c hc
    change c.output = O c.left c.right c.target at hf
    rw [hf]
    exact hF _ _ _ hb
  simpa only [apsp, squared_oracleWork, squared_answerWrites] using
    sum_call_resources_le (apsp O w W).calls F hc

theorem actual_execution_sites_le {n : ℕ} {Payload : Type}
    (O : DenseOracle n Payload) (hO : DenseOracleCorrect O)
    (w : OptionalTable n) (W degree : ℕ)
    (hw : APSPReduction.EdgeBound (decode w) W)
    (hn : 3 ≤ n) (hW : W ≤ n^degree) (F : ℝ) (hF0 : 0 ≤ F)
    (hF : ∀ A B T, APSPAlgorithm.SymmetricQueryBound (decode A, decode B, decode T)
      (64*n*W+13 : ℕ) → (O A B T).work + ((O A B T).answerWrites : ℝ) ≤ F) :
    (executionSites (apsp O w W) : ℝ) ≤
      (2*(degree+7 : ℕ) : ℝ)*logFactor^2*(Real.log (n:ℝ))^2*F +
      ((5*degree+43 : ℕ) : ℝ)*logFactor^2*(Real.log (n:ℝ))^2*(n:ℝ)^2 := by
  have hwork := actual_callback_resources_le O hO w W hw F hF
  have hcalls := apsp_calls_polylog O w W degree (by omega) hW
  have hform := apsp_formationWrites_polylog O w W degree (by omega) hW
  have hcallsR : ((apsp O w W).calls.length : ℝ) ≤
      ((n.log2+1 : ℕ):ℝ)*(2*((degree+5 : ℕ)*((n.log2+1 : ℕ):ℝ)+2)) := by
    exact_mod_cast hcalls
  have hformR : ((apsp O w W).formationWrites : ℝ) ≤
      (1+((n.log2+1 : ℕ):ℝ)*(5*((degree+5 : ℕ)*((n.log2+1 : ℕ):ℝ)+2)+7))*(n:ℝ)^2 := by
    exact_mod_cast hform
  have hℓ : (1:ℝ) ≤ ((n.log2+1 : ℕ):ℝ) := by exact_mod_cast Nat.le_add_left 1 n.log2
  have hlog := log2_add_one_le n hn
  have hsq : (((n.log2+1 : ℕ):ℝ))^2 ≤ logFactor^2*(Real.log (n:ℝ))^2 := by
    nlinarith [sq_nonneg (logFactor*Real.log (n:ℝ)-((n.log2+1 : ℕ):ℝ))]
  have hc : ((apsp O w W).calls.length : ℝ) ≤
      (2*(degree+7 : ℕ):ℝ)*logFactor^2*(Real.log (n:ℝ))^2 := by
    have hmid : ((apsp O w W).calls.length : ℝ) ≤
        (2*(degree+7 : ℕ):ℝ)*(((n.log2+1 : ℕ):ℝ))^2 := by
      push_cast at hcallsR ⊢
      nlinarith
    exact hmid.trans (by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hsq
        (show (0:ℝ) ≤ (2*(degree+7 : ℕ):ℝ) by positivity))
  have hf : ((apsp O w W).formationWrites : ℝ) ≤
      ((5*degree+43 : ℕ):ℝ)*logFactor^2*(Real.log (n:ℝ))^2*(n:ℝ)^2 := by
    have hmid : ((apsp O w W).formationWrites : ℝ) ≤
        ((5*degree+43 : ℕ):ℝ)*(((n.log2+1 : ℕ):ℝ))^2*(n:ℝ)^2 := by
      have hcoef : (1+((n.log2+1 : ℕ):ℝ)*(5*((degree+5 : ℕ)*((n.log2+1 : ℕ):ℝ)+2)+7)) ≤
          ((5*degree+43 : ℕ):ℝ)*(((n.log2+1 : ℕ):ℝ))^2 := by
        push_cast
        nlinarith
      exact hformR.trans (mul_le_mul_of_nonneg_right hcoef (sq_nonneg _))
    exact hmid.trans (by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hsq (show (0:ℝ) ≤ ((5*degree+43 : ℕ):ℝ) by positivity))
        (sq_nonneg (n:ℝ)))
  have hcF := mul_le_mul_of_nonneg_right hc hF0
  unfold executionSites
  push_cast
  push_cast at hcF hf
  linarith

/-- Multiplying the explicit strict-slack ledger by another fixed logarithmic
power does not weaken the displayed APSP exponent. -/
theorem log_mul_chargedCost_bigO (k j : ℕ) :
    (fun n : ℕ => (Real.log (n:ℝ))^j * ArithmeticSlack.chargedCost k n)
      =O[atTop] (fun n : ℕ => (n:ℝ)^(299294792/100000000 : ℝ)) := by
  have he : (fun n : ℕ => (Real.log (n:ℝ))^j * ArithmeticSlack.chargedCost k n) =
      ArithmeticSlack.chargedCost (k+j) := by
    funext n
    unfold ArithmeticSlack.chargedCost
    rw [show k+j+AlignedCertificate.R+10 = j+(k+AlignedCertificate.R+10) by omega,
      pow_add]
    ring
  rw [he]
  exact ArithmeticSlack.chargedCostBigO (k+j)

/-- Uniform families of inputs and actual stored callbacks. The remaining
premise is an actual callback bound, not functional correctness alone. -/
theorem apsp_sites_bigO_of_actual_callback_bound
    (Payload : ℕ → Type) (O : (n : ℕ) → DenseOracle n (Payload n))
    (w : (n : ℕ) → OptionalTable n) (W : ℕ → ℕ) (degree k : ℕ)
    (hO : ∀ n, DenseOracleCorrect (O n))
    (hw : ∀ n, APSPReduction.EdgeBound (decode (w n)) (W n))
    (hW : ∀ n, W n ≤ n^degree) (C : ℝ) (hC : 0 ≤ C)
    (hcallback : ∀ᶠ n : ℕ in atTop, ∀ A B T,
      APSPAlgorithm.SymmetricQueryBound (decode A, decode B, decode T)
        (64*n*W n+13 : ℕ) →
      ((O n A B T).work : ℝ) + (O n A B T).answerWrites ≤ C*ArithmeticSlack.chargedCost k n) :
    (fun n : ℕ => (executionSites (apsp (O n) (w n) (W n)) : ℝ))
      =O[atTop] (fun n : ℕ => (n:ℝ)^(299294792/100000000 : ℝ)) := by
  let a : ℝ := (2*(degree+7 : ℕ):ℝ)*logFactor^2*C
  let d : ℝ := ((5*degree+43 : ℕ):ℝ)*logFactor^2
  have hmain := (log_mul_chargedCost_bigO k 2).const_mul_left a
  have hformation : (fun n : ℕ => d*(Real.log (n:ℝ))^2*(n:ℝ)^2)
      =O[atTop] (fun n : ℕ => (n:ℝ)^(299294792/100000000 : ℝ)) := by
    have h := (AsymptoticCosts.logPowMulRpowBigO
      (a:=2) (d:=(299294792/100000000 : ℝ)) (by norm_num) 2).const_mul_left d
    simpa only [Real.rpow_two, mul_assoc] using h
  have hdom : (fun n : ℕ => (executionSites (apsp (O n) (w n) (W n)) : ℝ))
      =O[atTop] (fun n : ℕ => a*((Real.log (n:ℝ))^2*ArithmeticSlack.chargedCost k n) +
        d*(Real.log (n:ℝ))^2*(n:ℝ)^2) := by
    apply IsBigO.of_norm_eventuallyLE
    filter_upwards [hcallback, eventually_ge_atTop (3:ℕ)] with n hn hn3
    have hledger : 0 ≤ ArithmeticSlack.chargedCost k n := by
      unfold ArithmeticSlack.chargedCost AsymptoticCosts.roundedPower
      positivity
    have h := actual_execution_sites_le (O n) (hO n) (w n) (W n) degree (hw n)
      hn3 (hW n) (C*ArithmeticSlack.chargedCost k n) (mul_nonneg hC hledger) hn
    rw [Real.norm_of_nonneg (Nat.cast_nonneg _)]
    simpa only [a, d, mul_assoc, mul_left_comm, mul_comm] using h
  exact hdom.trans (hmain.add hformation)

/-- A fixed polynomial in the input bit width may price all the remaining
array/control and scalar sites. The numerical target has enough strict slack
to absorb this price; it still has to be supplied from concrete width proofs. -/
theorem apsp_priced_sites_bigO_of_actual_callback_bound
    (Payload : ℕ → Type) (O : (n : ℕ) → DenseOracle n (Payload n))
    (w : (n : ℕ) → OptionalTable n) (W unit : ℕ → ℕ) (degree k j : ℕ)
    (hO : ∀ n, DenseOracleCorrect (O n))
    (hw : ∀ n, APSPReduction.EdgeBound (decode (w n)) (W n))
    (hW : ∀ n, W n ≤ n^degree) (C U : ℝ) (hC : 0 ≤ C) (hU : 0 ≤ U)
    (hunit : ∀ᶠ n : ℕ in atTop, (unit n : ℝ) ≤ U*(Real.log (n:ℝ))^j)
    (hcallback : ∀ᶠ n : ℕ in atTop, ∀ A B T,
      APSPAlgorithm.SymmetricQueryBound (decode A, decode B, decode T)
        (64*n*W n+13 : ℕ) →
      ((O n A B T).work : ℝ) + (O n A B T).answerWrites ≤ C*ArithmeticSlack.chargedCost k n) :
    (fun n : ℕ => (unit n : ℝ)*(executionSites (apsp (O n) (w n) (W n)) : ℝ))
      =O[atTop] (fun n : ℕ => (n:ℝ)^(299294792/100000000 : ℝ)) := by
  let a : ℝ := U*(2*(degree+7 : ℕ):ℝ)*logFactor^2*C
  let d : ℝ := U*((5*degree+43 : ℕ):ℝ)*logFactor^2
  have hmain := (log_mul_chargedCost_bigO k (j+2)).const_mul_left a
  have hformation : (fun n : ℕ => d*(Real.log (n:ℝ))^(j+2)*(n:ℝ)^2)
      =O[atTop] (fun n : ℕ => (n:ℝ)^(299294792/100000000 : ℝ)) := by
    have h := (AsymptoticCosts.logPowMulRpowBigO
      (a:=2) (d:=(299294792/100000000 : ℝ)) (by norm_num) (j+2)).const_mul_left d
    simpa only [Real.rpow_two, mul_assoc] using h
  have hdom : (fun n : ℕ => (unit n : ℝ)*(executionSites (apsp (O n) (w n) (W n)) : ℝ))
      =O[atTop] (fun n : ℕ => a*((Real.log (n:ℝ))^(j+2)*ArithmeticSlack.chargedCost k n) +
        d*(Real.log (n:ℝ))^(j+2)*(n:ℝ)^2) := by
    apply IsBigO.of_norm_eventuallyLE
    filter_upwards [hcallback, hunit, eventually_ge_atTop (3:ℕ)] with n hn hu hn3
    have hledger : 0 ≤ ArithmeticSlack.chargedCost k n := by
      unfold ArithmeticSlack.chargedCost AsymptoticCosts.roundedPower
      positivity
    have h := actual_execution_sites_le (O n) (hO n) (w n) (W n) degree (hw n)
      hn3 (hW n) (C*ArithmeticSlack.chargedCost k n) (mul_nonneg hC hledger) hn
    have hs : (0:ℝ) ≤ executionSites (apsp (O n) (w n) (W n)) := Nat.cast_nonneg _
    have hbound := mul_le_mul hu h hs (by positivity : (0:ℝ) ≤ U*(Real.log (n:ℝ))^j)
    rw [Real.norm_of_nonneg (mul_nonneg (Nat.cast_nonneg _) hs)]
    calc
      (unit n : ℝ)*(executionSites (apsp (O n) (w n) (W n)) : ℝ) ≤
          U*(Real.log (n:ℝ))^j *
            ((2*(degree+7 : ℕ):ℝ)*logFactor^2*(Real.log (n:ℝ))^2*
              (C*ArithmeticSlack.chargedCost k n) +
              ((5*degree+43 : ℕ):ℝ)*logFactor^2*(Real.log (n:ℝ))^2*(n:ℝ)^2) := hbound
      _ = _ := by simp only [a, d, pow_add]; ring
  exact hdom.trans (hmain.add hformation)

#print axioms log2_add_one_le
#print axioms actual_callback_resources_le
#print axioms actual_execution_sites_le
#print axioms log_mul_chargedCost_bigO
#print axioms apsp_sites_bigO_of_actual_callback_bound
#print axioms apsp_priced_sites_bigO_of_actual_callback_bound

end
end ThinMatrix.UniformAPSPBound
