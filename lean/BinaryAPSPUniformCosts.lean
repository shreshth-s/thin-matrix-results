import BinaryAPSPCaller
import AdaptiveQueryBitBounds
import UniformAPSPBound
import ComputableParameters
import BinaryAPSPHostTotalCosts

/-!
# Uniform composition of retained binary APSP callback returns

Every summand below is the output retained by the actual caller. The generic
composition lemma states its callback-price premise explicitly; the concrete
end-to-end program must discharge it separately.
-/

namespace ThinMatrix.BinaryAPSPUniformCosts
open Filter Asymptotics BinaryAPSPCaller

def callbackWork {n : ℕ} {Payload : Type} (calls : List (Call n Payload)) : ℕ :=
  (calls.map (fun c => c.output.work+c.output.answerWrites)).sum

theorem bitScale_callbackWork {n : ℕ} {Payload : Type} (O : Oracle n Payload)
    (d : ℕ) (A B : IntTable n) :
    callbackWork (bitScale O d A B).calls =
      (bitScale O d A B).oracleWork+(bitScale O d A B).answerWrites := by
  induction d generalizing A B with
  | zero => rfl
  | succ d ih =>
    have h := ih (half A).value (half B).value
    unfold callbackWork at h
    simp only [bitScale,callbackWork,List.map_append,List.map_cons,List.map_nil,
      List.sum_append,List.sum_cons,List.sum_nil]
    omega

theorem squared_callbackWork {n : ℕ} {Payload : Type} (O : Oracle n Payload)
    (w : OptionalTable n) (B k : ℕ) :
    callbackWork (squared O w B k).calls =
      (squared O w B k).oracleWork+(squared O w B k).answerWrites := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have h := bitScale_callbackWork O
      (MinPlusReduction.signedLevels (APSPAlgorithm.sentinel B))
      (shift (tabulate (fun i j => encodeOptionalCell
        (BinaryMultiplierAdapter.encodeInteger (APSPAlgorithm.sentinel B : ℤ)).value
        (StoredMinPlusAPSP.decode (squared O w B k).value i j))).value
        (BinaryMultiplierAdapter.encodeInteger (APSPAlgorithm.sentinel B : ℤ)).value).value
      (shift (tabulate (fun i j => encodeOptionalCell
        (BinaryMultiplierAdapter.encodeInteger (APSPAlgorithm.sentinel B : ℤ)).value
        (StoredMinPlusAPSP.decode (squared O w B k).value i j))).value
        (BinaryMultiplierAdapter.encodeInteger (APSPAlgorithm.sentinel B : ℤ)).value).value
    change callbackWork (optionalProduct O B (squared O w B k).value
      (squared O w B k).value).calls =
      (optionalProduct O B (squared O w B k).value (squared O w B k).value).oracleWork+
      (optionalProduct O B (squared O w B k).value (squared O w B k).value).answerWrites at h
    unfold callbackWork at ih h
    simp only [squared,callbackWork,List.map_append,List.sum_append]
    omega

theorem run_callbackWork {n : ℕ} {Payload : Type} (O : Oracle n Payload)
    (w : StoredMinPlusAPSP.OptionalTable n) (W : ℕ) :
    callbackWork (run O w W).calls = (run O w W).oracleWork+(run O w W).answerWrites :=
  squared_callbackWork O (encodeGraph w).value
    (APSPAlgorithm.globalBound n W) (APSPReduction.rounds n)

theorem callbackWork_le_real {n : ℕ} {Payload : Type}
    (calls : List (Call n Payload)) (M : ℝ)
    (h : ∀ c∈calls, (c.output.work:ℝ)+c.output.answerWrites ≤ M) :
    (callbackWork calls:ℝ) ≤ calls.length*M := by
  induction calls with
  | nil => simp [callbackWork]
  | cons c cs ih =>
    have hc := h c (by simp)
    have ht := ih (fun t ht => h t (by simp [ht]))
    simp only [callbackWork,List.map_cons,List.sum_cons,Nat.cast_add,
      List.length_cons,Nat.cast_add,Nat.cast_one] at *
    nlinarith

theorem run_calls_length_bound {n : ℕ} {Payload : Type} (O : Oracle n Payload)
    (w : StoredMinPlusAPSP.OptionalTable n) (W degree : ℕ) (hW : W ≤ n^degree) :
    (run O w W).calls.length ≤
      2*(n.size+1)*(AdaptiveQueryBitBounds.exponent n degree+5) := by
  change (squared O (encodeGraph w).value (APSPAlgorithm.globalBound n W)
    (APSPReduction.rounds n)).calls.length ≤ _
  rw [squared_calls]
  have hr := AdaptiveQueryBitBounds.rounds_bound n
  have hd := AdaptiveQueryBitBounds.bit_depth_bound n degree W hW
  have hh := Nat.mul_le_mul hr (Nat.mul_le_mul_left 2 hd)
  nlinarith

theorem run_calls_polylog {n : ℕ} {Payload : Type} (O : Oracle n Payload)
    (w : StoredMinPlusAPSP.OptionalTable n) (W degree : ℕ)
    (hn : 3 ≤ n) (hW : W ≤ n^degree) :
    ((run O w W).calls.length:ℝ) ≤
      50*(degree+6:ℕ)*(Real.log (n:ℝ))^2 := by
  have hc := run_calls_length_bound O w W degree hW
  have he : AdaptiveQueryBitBounds.exponent n degree+5 ≤
      (degree+6)*(n.size+1) := by
    unfold AdaptiveQueryBitBounds.exponent
    nlinarith
  have hc' : (run O w W).calls.length ≤ 2*(degree+6)*(n.size+1)^2 := by
    have hm := Nat.mul_le_mul_left (2*(n.size+1)) he
    nlinarith
  have hs := ComputableParameters.size_le_four_log n hn
  have hl := PhaseGeometry.one_le_log_nat n hn
  have hs' : (n.size+1:ℝ) ≤ 5*Real.log (n:ℝ) := by
    linarith
  have hsq : (n.size+1:ℝ)^2 ≤ 25*(Real.log (n:ℝ))^2 := by
    nlinarith [sq_nonneg (5*Real.log (n:ℝ)-(n.size+1:ℝ))]
  have hcR : ((run O w W).calls.length:ℝ) ≤
      2*(degree+6:ℕ)*(n.size+1:ℝ)^2 := by exact_mod_cast hc'
  calc
    _ ≤ 2*(degree+6:ℕ)*(n.size+1:ℝ)^2 := hcR
    _ ≤ 2*(degree+6:ℕ)*(25*(Real.log (n:ℝ))^2) := by gcongr
    _ = _ := by ring

theorem actual_callback_resources_le {n : ℕ} {Payload NativePayload : Type}
    (O : Oracle n Payload) (N : StoredMinPlusAPSP.DenseOracle n NativePayload)
    (hON : Refines O N) (hN : StoredMinPlusAPSP.DenseOracleCorrect N)
    (w : StoredMinPlusAPSP.OptionalTable n) (W degree : ℕ)
    (hw : APSPReduction.EdgeBound (StoredMinPlusAPSP.decode w) W)
    (hn : 3 ≤ n) (hW : W ≤ n^degree) (F : ℝ) (hF0 : 0 ≤ F)
    (hF : ∀ A B T, APSPAlgorithm.SymmetricQueryBound
      (StoredMinPlusAPSP.decode (viewTable A),StoredMinPlusAPSP.decode (viewTable B),
        StoredMinPlusAPSP.decode (viewTable T)) (64*n*W+13:ℕ) →
      ((O A B T).work:ℝ)+(O A B T).answerWrites ≤ F) :
    ((run O w W).oracleWork:ℝ)+(run O w W).answerWrites ≤
      50*(degree+6:ℕ)*(Real.log (n:ℝ))^2*F := by
  have hs := callbackWork_le_real (run O w W).calls F (by
    intro c hc
    have hq := run_query_bound O N hON hN w W hw c hc
    have hf := run_calls_faithful O w W c hc
    change c.output = O c.left c.right c.target at hf
    rw [hf]
    exact hF _ _ _ hq)
  rw [run_callbackWork] at hs
  push_cast at hs
  exact hs.trans (mul_le_mul_of_nonneg_right (run_calls_polylog O w W degree hn hW) hF0)

/-- Actual callback returns, aggregated over the adaptive binary caller.
The concrete callback must supply the displayed uniform bound. -/
theorem callback_resources_bigO
    (Payload NativePayload : ℕ → Type)
    (O : (n : ℕ) → Oracle n (Payload n))
    (N : (n : ℕ) → StoredMinPlusAPSP.DenseOracle n (NativePayload n))
    (hON : ∀ n, Refines (O n) (N n))
    (hN : ∀ n, StoredMinPlusAPSP.DenseOracleCorrect (N n))
    (w : (n : ℕ) → StoredMinPlusAPSP.OptionalTable n) (W : ℕ → ℕ)
    (degree k : ℕ)
    (hw : ∀ n, APSPReduction.EdgeBound (StoredMinPlusAPSP.decode (w n)) (W n))
    (hW : ∀ n, W n ≤ n^degree) (C : ℝ) (hC : 0 ≤ C)
    (hcallback : ∀ᶠ n : ℕ in atTop, ∀ A B T,
      APSPAlgorithm.SymmetricQueryBound
        (StoredMinPlusAPSP.decode (viewTable A),StoredMinPlusAPSP.decode (viewTable B),
          StoredMinPlusAPSP.decode (viewTable T)) (64*n*W n+13:ℕ) →
      ((O n A B T).work:ℝ)+(O n A B T).answerWrites ≤
        C*ArithmeticSlack.chargedCost k n) :
    (fun n : ℕ => ((run (O n) (w n) (W n)).oracleWork:ℝ)+
      (run (O n) (w n) (W n)).answerWrites)
      =O[atTop] (fun n : ℕ => (n:ℝ)^(299294792/100000000:ℝ)) := by
  let a : ℝ := 50*(degree+6:ℕ)*C
  have hmain := (UniformAPSPBound.log_mul_chargedCost_bigO k 2).const_mul_left a
  have hdom : (fun n : ℕ => ((run (O n) (w n) (W n)).oracleWork:ℝ)+
      (run (O n) (w n) (W n)).answerWrites)
      =O[atTop] (fun n : ℕ => a*((Real.log (n:ℝ))^2*ArithmeticSlack.chargedCost k n)) := by
    apply IsBigO.of_norm_eventuallyLE
    filter_upwards [hcallback,eventually_ge_atTop (3:ℕ)] with n hn hn3
    have hledger : 0 ≤ ArithmeticSlack.chargedCost k n := by
      unfold ArithmeticSlack.chargedCost AsymptoticCosts.roundedPower
      positivity
    have h := actual_callback_resources_le (O n) (N n) (hON n) (hN n)
      (w n) (W n) degree (hw n) hn3 (hW n)
      (C*ArithmeticSlack.chargedCost k n) (mul_nonneg hC hledger) hn
    rw [Real.norm_of_nonneg (by positivity)]
    simpa only [a,mul_assoc,mul_left_comm,mul_comm] using h
  exact hdom.trans hmain

def executionWork {n : ℕ} {Payload : Type}
    (e : Execution n (Option Cell) Payload) : ℕ :=
  e.hostBits+e.oracleWork+e.answerWrites

/-- A general uniform price, allowing separately charged setup/formation
terms as well as the strict phase ledger. -/
theorem callback_resources_bigO_of_uniform_price
    (Payload NativePayload : ℕ → Type)
    (O : (n : ℕ) → Oracle n (Payload n))
    (N : (n : ℕ) → StoredMinPlusAPSP.DenseOracle n (NativePayload n))
    (hON : ∀ n, Refines (O n) (N n))
    (hN : ∀ n, StoredMinPlusAPSP.DenseOracleCorrect (N n))
    (w : (n : ℕ) → StoredMinPlusAPSP.OptionalTable n) (W : ℕ → ℕ)
    (degree : ℕ)
    (hw : ∀ n, APSPReduction.EdgeBound (StoredMinPlusAPSP.decode (w n)) (W n))
    (hW : ∀ n, W n ≤ n^degree) (F : ℕ → ℝ)
    (hF0 : ∀ᶠ n : ℕ in atTop, 0 ≤ F n)
    (hF : (fun n : ℕ => (Real.log (n:ℝ))^2*F n)
      =O[atTop] (fun n : ℕ => (n:ℝ)^(299294792/100000000:ℝ)))
    (hcallback : ∀ᶠ n : ℕ in atTop, ∀ A B T,
      APSPAlgorithm.SymmetricQueryBound
        (StoredMinPlusAPSP.decode (viewTable A),StoredMinPlusAPSP.decode (viewTable B),
          StoredMinPlusAPSP.decode (viewTable T)) (64*n*W n+13:ℕ) →
      ((O n A B T).work:ℝ)+(O n A B T).answerWrites ≤ F n) :
    (fun n : ℕ => ((run (O n) (w n) (W n)).oracleWork:ℝ)+
      (run (O n) (w n) (W n)).answerWrites)
      =O[atTop] (fun n : ℕ => (n:ℝ)^(299294792/100000000:ℝ)) := by
  let a : ℝ := 50*(degree+6:ℕ)
  have hdom : (fun n : ℕ => ((run (O n) (w n) (W n)).oracleWork:ℝ)+
      (run (O n) (w n) (W n)).answerWrites)
      =O[atTop] (fun n : ℕ => a*((Real.log (n:ℝ))^2*F n)) := by
    apply IsBigO.of_norm_eventuallyLE
    filter_upwards [hcallback,hF0,eventually_ge_atTop (3:ℕ)] with n hn hnonneg hn3
    have h := actual_callback_resources_le (O n) (N n) (hON n) (hN n)
      (w n) (W n) degree (hw n) hn3 (hW n) (F n) hnonneg hn
    rw [Real.norm_of_nonneg (by positivity)]
    simpa only [a,mul_assoc] using h
  exact hdom.trans (hF.const_mul_left a)

/-- Host arithmetic and actual callback work are both charged. This generic
theorem is an assembly tool, not a claim that its callback premise has been
discharged by any particular oracle. -/
theorem executionWork_bigO_of_callback_bound
    (Payload NativePayload : ℕ → Type)
    (O : (n : ℕ) → Oracle n (Payload n))
    (N : (n : ℕ) → StoredMinPlusAPSP.DenseOracle n (NativePayload n))
    (hON : ∀ n, Refines (O n) (N n))
    (hN : ∀ n, StoredMinPlusAPSP.DenseOracleCorrect (N n))
    (w : (n : ℕ) → StoredMinPlusAPSP.OptionalTable n) (W : ℕ → ℕ)
    (degree k : ℕ)
    (hw : ∀ n, APSPReduction.EdgeBound (StoredMinPlusAPSP.decode (w n)) (W n))
    (hW : ∀ n, W n ≤ n^degree) (C : ℝ) (hC : 0 ≤ C)
    (hcallback : ∀ᶠ n : ℕ in atTop, ∀ A B T,
      APSPAlgorithm.SymmetricQueryBound
        (StoredMinPlusAPSP.decode (viewTable A),StoredMinPlusAPSP.decode (viewTable B),
          StoredMinPlusAPSP.decode (viewTable T)) (64*n*W n+13:ℕ) →
      ((O n A B T).work:ℝ)+(O n A B T).answerWrites ≤
        C*ArithmeticSlack.chargedCost k n) :
    (fun n : ℕ => (executionWork (run (O n) (w n) (W n)):ℝ))
      =O[atTop] (fun n : ℕ => (n:ℝ)^(299294792/100000000:ℝ)) := by
  have hh := BinaryAPSPHostTotalCosts.run_hostBits_bigO Payload O w W degree hw hW
  have hc := callback_resources_bigO Payload NativePayload O N hON hN w W degree k
    hw hW C hC hcallback
  simpa only [executionWork,Nat.cast_add,add_assoc] using hh.add hc

#print axioms bitScale_callbackWork
#print axioms squared_callbackWork
#print axioms run_callbackWork
#print axioms callbackWork_le_real
#print axioms run_calls_length_bound
#print axioms run_calls_polylog
#print axioms actual_callback_resources_le
#print axioms callback_resources_bigO
#print axioms executionWork_bigO_of_callback_bound
#print axioms callback_resources_bigO_of_uniform_price

end ThinMatrix.BinaryAPSPUniformCosts
