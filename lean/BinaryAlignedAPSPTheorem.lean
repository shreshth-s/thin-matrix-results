import BinaryAlignedAPSPCosts
import BinaryAPSPPublicCostBounds
import BinaryTriangleCosts

/-!
# Concrete deterministic integer APSP: correctness and charged work

The work model counts the actual binary coefficient programs and bounded
indexed-array/control actions. Its fixed pricing constants may depend on the
fixed polynomial input promise. This is separate from a Light-to-RAM compiler
instantiation and from elapsed time of Lean's native evaluator.
-/
namespace ThinMatrix.BinaryAlignedAPSPTheorem
open Filter Asymptotics
open BinaryAlignedAPSP BinaryAlignedAPSPTransport BinaryAlignedAPSPCosts
open BinaryAPSPPublicCostBounds BinaryAPSPCaller
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
attribute [local irreducible] ComputableParameters.block ComputableParameters.factorCount
  AlignedCertificate.R AlignedCertificate.S
  BinaryControllerPolynomialBounds.publicUnitConstant
  BinaryControllerPolynomialBounds.controllerConstant
  BinaryControllerPolynomialBounds.addressConstant
  BinaryTriangleCosts.Closed.callbackCoefficient
  BinaryTriangleCosts.Closed.callbackLogDegree

def promiseDegree (degree : ℕ) : ℕ := degree+2

def addressPrice (degree n : ℕ) : ℕ :=
  BinaryTriangleCosts.FixedPrices.addressPrice n (promiseDegree degree) degree

def unitCoefficient (degree : ℕ) : ℕ :=
  BinaryControllerPolynomialBounds.publicUnitConstant (promiseDegree degree) 4 degree

def finalPrice (degree n : ℕ) : ℝ :=
  2*BinaryTriangleCosts.Closed.callbackCoefficient (promiseDegree degree) degree*
    ArithmeticSlack.chargedCost BinaryTriangleCosts.Closed.callbackLogDegree n+
      setupAllowance degree (unitCoefficient degree) n

theorem one_le_addressPrice (degree n : ℕ) : 1 ≤ addressPrice degree n := by
  apply one_le_addressedUnit

#print axioms one_le_addressPrice

theorem addressPrice_poly (degree n : ℕ) :
    addressPrice degree n ≤ unitCoefficient degree*(n.size+1)^2 :=
  BinaryTriangleCosts.FixedPrices.addressPrice_poly n (promiseDegree degree) degree

#print axioms addressPrice_poly

theorem finalPrice_nonneg (degree n : ℕ) (hn : 3 ≤ n) : 0 ≤ finalPrice degree n := by
  have hc := BinaryTriangleCosts.Closed.callbackCoefficient_nonneg (promiseDegree degree) degree
  have hl := ReductionCosts.chargedCost_nonneg BinaryTriangleCosts.Closed.callbackLogDegree n hn
  have hs : 0 ≤ setupAllowance degree (unitCoefficient degree) n := by
    unfold setupAllowance
    positivity
  unfold finalPrice
  positivity

#print axioms finalPrice_nonneg

theorem log_mul_finalPrice_bigO (degree : ℕ) :
    (fun n : ℕ => (Real.log (n:ℝ))^2*finalPrice degree n)
      =O[atTop] (fun n : ℕ => (n:ℝ)^(299294792/100000000:ℝ)) := by
  have ht := (UniformAPSPBound.log_mul_chargedCost_bigO
    BinaryTriangleCosts.Closed.callbackLogDegree 2).const_mul_left
      (2*BinaryTriangleCosts.Closed.callbackCoefficient (promiseDegree degree) degree)
  have hs := log_mul_setupAllowance_bigO degree (unitCoefficient degree)
  simpa only [finalPrice,mul_add,mul_assoc,mul_left_comm,mul_comm] using ht.add hs

#print axioms log_mul_finalPrice_bigO

/-- Cast and combine scalar counters before substituting concrete programs. -/
private theorem combine_charged_counters
    (s w out x a y ow oo steps pub : ℕ) (C E : ℝ)
    (hf : s+w+out ≤ 2*(x+a*y+ow+oo)+(a+2)*steps+pub+76*(a+1))
    (ht : (x:ℝ)+(a:ℝ)*y+ow+oo ≤ C)
    (he : (((a+2)*steps+pub+76*(a+1):ℕ):ℝ) ≤ E) :
    (s:ℝ)+w+out ≤ 2*C+E := by
  have hr : ((s+w+out:ℕ):ℝ) ≤
      ((2*(x+a*y+ow+oo)+(a+2)*steps+pub+76*(a+1):ℕ):ℝ) := by
    exact_mod_cast hf
  push_cast at hr he
  linarith only [hr,ht,he]

#print axioms combine_charged_counters

private theorem originalCallback_eq_prepared {n : ℕ} (W a : ℕ)
    (setup : ParameterExecution.Execution n (cap n W))
    (hsetup : setup=ParameterExecution.execute n (cap n W))
    (p : CompleteAPSP.Parameters (ComputableParameters.block n) (cap n W))
    (hp : setup.value=some p) :
    originalCallback W a setup hsetup p hp=
      BinaryTriangleExecution.prepareConcreteFromPrimes (n:=n) (EndToEndAPSP.block_pos n) p
        (ParameterMetadata.successfulLabels setup hsetup p hp)
        (ParameterMetadata.successfulLabels_eq setup hsetup p hp) a := rfl

private theorem original_price_le_of_concrete {n : ℕ} (W a : ℕ)
    (setup : ParameterExecution.Execution n (cap n W))
    (hsetup : setup=ParameterExecution.execute n (cap n W))
    (p : CompleteAPSP.Parameters (ComputableParameters.block n) (cap n W))
    (hp : setup.value=some p) (A B T : IntTable n) (C : ℝ)
    (ht : let prepared:=(BinaryTriangleExecution.prepareConcreteFromPrimes (n:=n)
        (EndToEndAPSP.block_pos n) p (ParameterMetadata.successfulLabels setup hsetup p hp)
        (ParameterMetadata.successfulLabels_eq setup hsetup p hp) a);
      (prepared.setupBits:ℝ)+(a:ℝ)*prepared.setupControl+
        ((prepared.oracle A B T).work:ℝ)+(prepared.oracle A B T).answerWrites ≤ C) :
    ((originalCallback W a setup hsetup p hp).setupBits:ℝ)+
      (a:ℝ)*(originalCallback W a setup hsetup p hp).setupControl+
      (((originalCallback W a setup hsetup p hp).oracle A B T).work:ℝ)+
      ((originalCallback W a setup hsetup p hp).oracle A B T).answerWrites ≤ C := by
  rw [originalCallback_eq_prepared]
  exact ht

private theorem successful_combined_price {n : ℕ} (W a : ℕ) (ha : 1≤a)
    (p : CompleteAPSP.Parameters (ComputableParameters.block n) (cap n W))
    (hp : (ParameterExecution.execute n (cap n W)).value=some p)
    (A B T : IntTable n) (C E : ℝ)
    (ht : ((originalCallback W a (ParameterExecution.execute n (cap n W)) rfl p hp).setupBits:ℝ)+
      (a:ℝ)*(originalCallback W a (ParameterExecution.execute n (cap n W)) rfl p hp).setupControl+
      (((originalCallback W a (ParameterExecution.execute n (cap n W)) rfl p hp).oracle A B T).work:ℝ)+
      ((originalCallback W a (ParameterExecution.execute n (cap n W)) rfl p hp).oracle A B T).answerWrites ≤ C)
    (he : (((a+2)*(ParameterExecution.execute n (cap n W)).bitSteps+
      publicSetupBits n W+76*(a+1):ℕ):ℝ) ≤ E) :
    (setupWork n W a:ℝ)+((prepare n W a).oracle A B T).work+
      ((prepare n W a).oracle A B T).answerWrites ≤ 2*C+E :=
  combine_charged_counters (setupWork n W a)
    ((prepare n W a).oracle A B T).work ((prepare n W a).oracle A B T).answerWrites
    (originalCallback W a (ParameterExecution.execute n (cap n W)) rfl p hp).setupBits a
    (originalCallback W a (ParameterExecution.execute n (cap n W)) rfl p hp).setupControl
    ((originalCallback W a (ParameterExecution.execute n (cap n W)) rfl p hp).oracle A B T).work
    ((originalCallback W a (ParameterExecution.execute n (cap n W)) rfl p hp).oracle A B T).answerWrites
    (ParameterExecution.execute n (cap n W)).bitSteps (publicSetupBits n W) C E
    (setup_and_callback_le_original W a ha p hp A B T) ht he

#print axioms original_price_le_of_concrete
#print axioms successful_combined_price

/-- Closed bound for the same prepared callback retained by the concrete
APSP entry point. The only size promise concerns the original graph cap. -/
theorem eventual_combined_price (degree : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ W : ℕ, W ≤ n^degree →
      ∀ A B T : BinaryAPSPCaller.IntTable n,
      APSPAlgorithm.SymmetricQueryBound
        (StoredMinPlusAPSP.decode (viewTable A),StoredMinPlusAPSP.decode (viewTable B),
          StoredMinPlusAPSP.decode (viewTable T)) (64*n*W+13:ℕ) →
      (setupWork n W (addressPrice degree n):ℝ)+
        ((prepare n W (addressPrice degree n)).oracle A B T).work+
        ((prepare n W (addressPrice degree n)).oracle A B T).answerWrites ≤ finalPrice degree n := by
  filter_upwards [BinaryTriangleCosts.Closed.eventual_prepared_resources_le (promiseDegree degree) degree,
    EndToEndAPSP.eventually_successful degree,
    actual_extraSetup_le_allowance_eventually degree (unitCoefficient degree),
    eventually_ge_atTop (232:ℕ)] with n htriangle hsuccess hextra hn
  intro W hW A B T hb
  have hU : cap n W ≤ n^(promiseDegree degree) := cap_le_power degree n W hn hW
  have hs : (ComputableParameters.program n (cap n W)).isSome=true := by
    simpa only [EndToEndAPSP.magnitudeCap,cap] using hsuccess W hW
  cases hp : ComputableParameters.program n (cap n W) with
  | none => simp only [hp,Option.isSome_none,Bool.false_eq_true] at hs
  | some p =>
    have he : (ParameterExecution.execute n (cap n W)).value=some p :=
      (ParameterExecution.execute_value n (cap n W)).trans hp
    have hentry := query_entryBound_le_cap A B T hb
    have ht := htriangle (cap n W) p hp hU
      (ParameterMetadata.successfulLabels (ParameterExecution.execute n (cap n W)) rfl p he)
      (ParameterMetadata.successfulLabels_eq (ParameterExecution.execute n (cap n W)) rfl p he)
      A B T hentry
    have htri :
        ((originalCallback W (addressPrice degree n) (ParameterExecution.execute n (cap n W)) rfl p he).setupBits:ℝ)+
        (addressPrice degree n:ℝ)*(originalCallback W (addressPrice degree n)
          (ParameterExecution.execute n (cap n W)) rfl p he).setupControl+
        (((originalCallback W (addressPrice degree n)
          (ParameterExecution.execute n (cap n W)) rfl p he).oracle A B T).work:ℝ)+
        ((originalCallback W (addressPrice degree n)
          (ParameterExecution.execute n (cap n W)) rfl p he).oracle A B T).answerWrites ≤
      BinaryTriangleCosts.Closed.callbackCoefficient (promiseDegree degree) degree*
        ArithmeticSlack.chargedCost BinaryTriangleCosts.Closed.callbackLogDegree n := by
      apply original_price_le_of_concrete W (addressPrice degree n)
        (ParameterExecution.execute n (cap n W)) rfl p he A B T
      simpa only [addressPrice] using ht
    have hx := hextra W (addressPrice degree n) hW (addressPrice_poly degree n)
    have htotal := successful_combined_price W (addressPrice degree n)
      (one_le_addressPrice degree n) p he A B T
      (BinaryTriangleCosts.Closed.callbackCoefficient (promiseDegree degree) degree*
        ArithmeticSlack.chargedCost BinaryTriangleCosts.Closed.callbackLogDegree n)
      (setupAllowance degree (unitCoefficient degree) n) htri hx
    simpa only [finalPrice,mul_assoc] using htotal

#print axioms eventual_combined_price

/-- The concrete program's complete returned work, including setup, original
input encoding, host arithmetic, callback work and output writes. No fast
oracle, final width, multiplier budget or desired-cost premise remains. -/
theorem run_work_bigO
    (w : (n : ℕ) → StoredMinPlusAPSP.OptionalTable n) (W : ℕ → ℕ) (degree : ℕ)
    (hw : ∀ n, APSPReduction.EdgeBound (StoredMinPlusAPSP.decode (w n)) (W n))
    (hW : ∀ n, W n ≤ n^degree) :
    (fun n : ℕ => ((BinaryAlignedAPSP.run (w n) (W n) (addressPrice degree n)).work:ℝ))
      =O[atTop] (fun n : ℕ => (n:ℝ)^(299294792/100000000:ℝ)) := by
  apply run_work_bigO_of_combined_price w W (addressPrice degree) degree hw hW (finalPrice degree)
  · filter_upwards [eventually_ge_atTop (3:ℕ)] with n hn
    exact finalPrice_nonneg degree n hn
  · exact log_mul_finalPrice_bigO degree
  · filter_upwards [eventual_combined_price degree] with n hn
    exact hn (W n) (hW n)

#print axioms run_work_bigO

theorem correctness_and_work
    (w : (n : ℕ) → StoredMinPlusAPSP.OptionalTable n) (W : ℕ → ℕ) (degree : ℕ)
    (hw : ∀ n, APSPReduction.EdgeBound (StoredMinPlusAPSP.decode (w n)) (W n))
    (hW : ∀ n, W n ≤ n^degree)
    (hno : ∀ n, APSPReduction.NoNegativeCycles (StoredMinPlusAPSP.decode (w n))) :
    (∀ n, APSPReduction.IsAPSP (StoredMinPlusAPSP.decode (w n))
      (StoredMinPlusAPSP.decode (viewOptional
        (BinaryAlignedAPSP.run (w n) (W n) (addressPrice degree n)).core.value))) ∧
      (fun n : ℕ => ((BinaryAlignedAPSP.run (w n) (W n) (addressPrice degree n)).work:ℝ))
        =O[atTop] (fun n : ℕ => (n:ℝ)^(299294792/100000000:ℝ)) :=
  ⟨fun n=>BinaryAlignedAPSP.run_correct (w n) (W n) (addressPrice degree n) (hw n) (hno n),
    run_work_bigO w W degree hw hW⟩

#print axioms one_le_addressPrice
#print axioms addressPrice_poly
#print axioms finalPrice_nonneg
#print axioms log_mul_finalPrice_bigO
#print axioms eventual_combined_price
#print axioms run_work_bigO
#print axioms correctness_and_work

end
end ThinMatrix.BinaryAlignedAPSPTheorem
