import AlignedAPSPCosts

/-!
# Closed resource theorem for the concrete aligned stored APSP program

There is no fast-oracle or desired-cost hypothesis in this theorem. The
callback bound is instantiated from the actual aligned producer, computed
geometry, exact cyclic multiplication, retained controller returns and phase
proofs. Its cost is the resource fields returned by the stored program.

This is NOT yet a simulation theorem for the complete persistent-bit program
or a Light/RAM execution. Parameter-setup execution and the binary array/caller
refinements are developed separately before a whole-runtime claim is made.
-/

namespace ThinMatrix.AlignedResourceTheorem
noncomputable section
open Filter Asymptotics StoredMinPlusAPSP

abbrev Payload (n : ℕ) :=
  CountedEndToEndAPSP.CallbackPayload n (ComputableParameters.block n)
    (AlignedAPSP.Payload n (ComputableParameters.block n))

def oracle (n W : ℕ) : DenseOracle n (Payload n) :=
  CountedEndToEndAPSP.fromConfiguration
    (AlignedAPSP.backend n (ComputableParameters.block n) (EndToEndAPSP.block_pos n)) W
    (ComputableParameters.program n (EndToEndAPSP.magnitudeCap n W))

theorem oracle_correct (n W : ℕ) : DenseOracleCorrect (oracle n W) :=
  CountedEndToEndAPSP.fromConfiguration_correct _ W _

theorem run_eq_apsp {n : ℕ} (w : OptionalTable n) (W : ℕ) :
    AlignedAPSP.run w W = StoredMinPlusAPSP.apsp (oracle n W) w W := rfl

theorem actual_callback_bound (degree : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ W : ℕ, W ≤ n^degree →
      ∀ A B T : IntTable n,
      APSPAlgorithm.SymmetricQueryBound (decode A,decode B,decode T) (64*n*W+13:ℕ) →
      ((oracle n W A B T).work:ℝ)+(oracle n W A B T).answerWrites ≤
        AlignedAPSPCosts.callbackCoefficient*
          ArithmeticSlack.chargedCost AlignedAPSPCosts.callbackLogDegree n := by
  filter_upwards [AlignedAPSPCosts.eventual_callback_resources_le,
    EndToEndAPSP.eventually_successful degree] with n hcost hsuccess
  intro W hW A B T hb
  have hs := hsuccess W hW
  have he := CountedEndToEndAPSP.entryMagnitude_le A B T hb
  have hcap : CountedEndToEndAPSP.entryQueryBound A B T ≤ EndToEndAPSP.magnitudeCap n W := by
    unfold CountedEndToEndAPSP.entryQueryBound EndToEndAPSP.magnitudeCap
    nlinarith
  cases hconfiguration : ComputableParameters.program n (EndToEndAPSP.magnitudeCap n W) with
  | none => simp only [hconfiguration, Option.isSome_none, Bool.false_eq_true] at hs
  | some parameters =>
    have h := hcost (EndToEndAPSP.magnitudeCap n W) parameters hconfiguration A B T hcap
    simpa only [oracle, hconfiguration, CountedEndToEndAPSP.fromConfiguration] using h

/-- Actual returned resource fields, uniformly for arbitrary input families
of polynomially bounded integer graphs. No running-time premise remains. -/
theorem resource_sites_bigO
    (w : (n : ℕ) → OptionalTable n) (W : ℕ → ℕ) (degree : ℕ)
    (hw : ∀ n, APSPReduction.EdgeBound (decode (w n)) (W n))
    (hW : ∀ n, W n ≤ n^degree) :
    (fun n : ℕ => (UniformAPSPBound.executionSites (AlignedAPSP.run (w n) (W n)):ℝ))
      =O[atTop] (fun n : ℕ => (n:ℝ)^(299294792/100000000:ℝ)) := by
  have hc : ∀ᶠ n : ℕ in atTop, ∀ A B T,
      APSPAlgorithm.SymmetricQueryBound (decode A,decode B,decode T) (64*n*W n+13:ℕ) →
      ((oracle n (W n) A B T).work:ℝ)+(oracle n (W n) A B T).answerWrites ≤
        AlignedAPSPCosts.callbackCoefficient*
          ArithmeticSlack.chargedCost AlignedAPSPCosts.callbackLogDegree n := by
    filter_upwards [actual_callback_bound degree] with n hn
    exact hn (W n) (hW n)
  have h := UniformAPSPBound.apsp_sites_bigO_of_actual_callback_bound Payload
    (fun n => oracle n (W n)) w W degree AlignedAPSPCosts.callbackLogDegree
    (fun n => oracle_correct n (W n)) hw hW AlignedAPSPCosts.callbackCoefficient
    AlignedAPSPCosts.callbackCoefficient_nonneg hc
  simpa only [run_eq_apsp] using h

theorem priced_resource_sites_bigO
    (w : (n : ℕ) → OptionalTable n) (W unit : ℕ → ℕ) (degree j : ℕ)
    (hw : ∀ n, APSPReduction.EdgeBound (decode (w n)) (W n))
    (hW : ∀ n, W n ≤ n^degree) (U : ℝ) (hU : 0 ≤ U)
    (hunit : ∀ᶠ n : ℕ in atTop, (unit n:ℝ) ≤ U*(Real.log (n:ℝ))^j) :
    (fun n : ℕ => (unit n:ℝ)*
      (UniformAPSPBound.executionSites (AlignedAPSP.run (w n) (W n)):ℝ))
      =O[atTop] (fun n : ℕ => (n:ℝ)^(299294792/100000000:ℝ)) := by
  have hc : ∀ᶠ n : ℕ in atTop, ∀ A B T,
      APSPAlgorithm.SymmetricQueryBound (decode A,decode B,decode T) (64*n*W n+13:ℕ) →
      ((oracle n (W n) A B T).work:ℝ)+(oracle n (W n) A B T).answerWrites ≤
        AlignedAPSPCosts.callbackCoefficient*
          ArithmeticSlack.chargedCost AlignedAPSPCosts.callbackLogDegree n := by
    filter_upwards [actual_callback_bound degree] with n hn
    exact hn (W n) (hW n)
  have h := UniformAPSPBound.apsp_priced_sites_bigO_of_actual_callback_bound Payload
    (fun n => oracle n (W n)) w W unit degree AlignedAPSPCosts.callbackLogDegree j
    (fun n => oracle_correct n (W n)) hw hW AlignedAPSPCosts.callbackCoefficient U
    AlignedAPSPCosts.callbackCoefficient_nonneg hU hunit hc
  simpa only [run_eq_apsp] using h

theorem correctness_and_resources
    (w : (n : ℕ) → OptionalTable n) (W : ℕ → ℕ) (degree : ℕ)
    (hw : ∀ n, APSPReduction.EdgeBound (decode (w n)) (W n))
    (hW : ∀ n, W n ≤ n^degree)
    (hno : ∀ n, APSPReduction.NoNegativeCycles (decode (w n))) :
    (∀ n, APSPReduction.IsAPSP (decode (w n)) (decode (AlignedAPSP.run (w n) (W n)).value)) ∧
      (fun n : ℕ => (UniformAPSPBound.executionSites (AlignedAPSP.run (w n) (W n)):ℝ))
        =O[atTop] (fun n : ℕ => (n:ℝ)^(299294792/100000000:ℝ)) :=
  ⟨fun n => AlignedAPSP.run_correct (w n) (W n) (hw n) (hno n),
    resource_sites_bigO w W degree hw hW⟩

#print axioms oracle_correct
#print axioms actual_callback_bound
#print axioms resource_sites_bigO
#print axioms priced_resource_sites_bigO
#print axioms correctness_and_resources

end
end ThinMatrix.AlignedResourceTheorem
