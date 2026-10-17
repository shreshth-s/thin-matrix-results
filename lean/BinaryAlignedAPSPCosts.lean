import BinaryAlignedAPSPTransport
import BinaryAPSPUniformCosts

/-!
# Composition of the same concrete binary APSP execution

The local assembly interfaces below are explicit. The concrete triangle and
phase proofs discharge them in the end-to-end theorem.
-/

namespace ThinMatrix.BinaryAlignedAPSPCosts
open BinaryAlignedAPSP BinaryAlignedAPSPTransport BinaryAPSPCaller
open Filter Asymptotics
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
attribute [local irreducible] ComputableParameters.block ComputableParameters.factorCount AlignedCertificate.S

def preparationWork {n W a : ℕ} (prep : Preparation n W a) : ℕ :=
  prep.setupBits+(a+1)*(prep.setupControl+8)

def setupWork (n W a : ℕ) : ℕ := preparationWork (prepare n W a)

private theorem setupWork_eq_preparationWork (n W a : ℕ) :
    setupWork n W a=preparationWork (prepare n W a) := rfl

private theorem numerical_bound (a s p x y w out pub : ℕ)
    (ha : 1 ≤ a) (hp : p ≤ s) :
    (s+pub+x)+(a+1)*(p+y+64+8)+(w+4*(a+1))+out  ≤
      2*(x+a*y+w+out)+(a+2)*s+pub+76*(a+1) := by
  have hpy := Nat.mul_le_mul_left (a+1) hp
  have hay : (a+1)*y  ≤  2*a*y := Nat.mul_le_mul_right y (by omega)
  nlinarith only [hpy,hay]

private theorem setupFromSetup_and_callback_le_original {n : ℕ} (W a : ℕ) (ha : 1 ≤ a)
    (setup : ParameterExecution.Execution n (cap n W))
    (hsetup : setup=ParameterExecution.execute n (cap n W))
    (p : CompleteAPSP.Parameters (ComputableParameters.block n) (cap n W))
    (hp : setup.value=some p) (hpool : setup.metadata.pool.length ≤ setup.bitSteps)
    (A B T : BinaryAPSPCaller.IntTable n) :
    ((prepareFromSetup W a setup hsetup).setupBits+
      (a+1)*((prepareFromSetup W a setup hsetup).setupControl+8))+
      ((prepareFromSetup W a setup hsetup).oracle A B T).work+
      ((prepareFromSetup W a setup hsetup).oracle A B T).answerWrites ≤
      2*((originalCallback W a setup hsetup p hp).setupBits+
        a*(originalCallback W a setup hsetup p hp).setupControl+
        ((originalCallback W a setup hsetup p hp).oracle A B T).work+
        ((originalCallback W a setup hsetup p hp).oracle A B T).answerWrites)+
      (a+2)*setup.bitSteps+publicSetupBits n W+76*(a+1) := by
  rw [prepared_setupBits_original W a setup hsetup p hp,
    prepared_setupControl_original W a setup hsetup p hp,
    prepared_work_original W a setup hsetup p hp A B T,
    prepared_answerWrites_original W a setup hsetup p hp A B T]
  exact numerical_bound a _ _ _ _ _ _ _ ha hpool

theorem setup_and_callback_le_original {n : ℕ} (W a : ℕ) (ha : 1 ≤ a)
    (p : CompleteAPSP.Parameters (ComputableParameters.block n) (cap n W))
    (hp : (ParameterExecution.execute n (cap n W)).value=some p)
    (A B T : BinaryAPSPCaller.IntTable n) :
    setupWork n W a+((prepare n W a).oracle A B T).work+
      ((prepare n W a).oracle A B T).answerWrites ≤
      2*((originalCallback W a (ParameterExecution.execute n (cap n W)) rfl p hp).setupBits+
        a*(originalCallback W a (ParameterExecution.execute n (cap n W)) rfl p hp).setupControl+
        ((originalCallback W a (ParameterExecution.execute n (cap n W)) rfl p hp).oracle A B T).work+
        ((originalCallback W a (ParameterExecution.execute n (cap n W)) rfl p hp).oracle A B T).answerWrites)+
      (a+2)*(ParameterExecution.execute n (cap n W)).bitSteps+
      publicSetupBits n W+76*(a+1) := by
  have h := setupFromSetup_and_callback_le_original W a ha _ rfl p hp
    (ParameterMetadata.metadata_pool_length_price n (cap n W)) A B T
  have he : prepare n W a=prepareFromSetup W a (ParameterExecution.execute n (cap n W)) rfl := rfl
  rw [←he] at h
  exact h

#print axioms setup_and_callback_le_original

def zeroTable (n : ℕ) : BinaryAPSPCaller.IntTable n :=
  Vector.replicate n (Vector.replicate n BinaryCell.zero)

theorem zeroTable_query_bound (n W : ℕ) :
    APSPAlgorithm.SymmetricQueryBound
      (StoredMinPlusAPSP.decode (viewTable (zeroTable n)),
        StoredMinPlusAPSP.decode (viewTable (zeroTable n)),
        StoredMinPlusAPSP.decode (viewTable (zeroTable n))) (64*n*W+13:ℕ) := by
  have hm : (0:ℤ) ≤ 64*n*W := by positivity
  constructor
  · intro i j
    simp [zeroTable,viewTable,StoredMinPlusAPSP.decode,BinaryCell.zero_view]
    omega
  · constructor <;> intro i j <;>
      simp [zeroTable,viewTable,StoredMinPlusAPSP.decode,BinaryCell.zero_view] <;> omega

/-- A proof-level assembly of the retained fields of one preparation. -/
def preparedExecution {n W a : ℕ} (prep : Preparation n W a)
    (w : StoredMinPlusAPSP.OptionalTable n) : BinaryAlignedAPSP.Execution n W a :=
  let core := BinaryAPSPCaller.run prep.oracle w W
  ⟨prep,core,prep.setupBits+(a+1)*(prep.setupControl+8)+
    core.hostBits+core.oracleWork+core.answerWrites⟩

private theorem run_eq_prepared {n : ℕ} (w : StoredMinPlusAPSP.OptionalTable n) (W a : ℕ) :
    BinaryAlignedAPSP.run w W a=preparedExecution (prepare n W a) w := rfl

private theorem prepared_work_bigO_of_combined_price
    (w : (n : ℕ) → StoredMinPlusAPSP.OptionalTable n) (W a : ℕ → ℕ)
    (degree : ℕ)
    (prep : (n : ℕ) → Preparation n (W n) (a n))
    (hcorrect : ∀ n, OracleCorrect (prep n).oracle)
    (hw : ∀ n, APSPReduction.EdgeBound (StoredMinPlusAPSP.decode (w n)) (W n))
    (hW : ∀ n, W n ≤ n^degree) (F : ℕ → ℝ)
    (hF0 : ∀ᶠ n : ℕ in atTop, 0 ≤ F n)
    (hF : (fun n : ℕ => (Real.log (n:ℝ))^2*F n)
      =O[atTop] (fun n : ℕ => (n:ℝ)^(299294792/100000000:ℝ)))
    (hprice : ∀ᶠ n : ℕ in atTop, ∀ A B T,
      APSPAlgorithm.SymmetricQueryBound
        (StoredMinPlusAPSP.decode (viewTable A),StoredMinPlusAPSP.decode (viewTable B),
          StoredMinPlusAPSP.decode (viewTable T)) (64*n*W n+13:ℕ) →
      ((preparationWork (prep n):ℕ):ℝ)+
        ((prep n).oracle A B T).work+
        ((prep n).oracle A B T).answerWrites  ≤  F n) :
    (fun n : ℕ => ((preparedExecution (prep n) (w n)).work:ℝ))
      =O[atTop] (fun n : ℕ => (n:ℝ)^(299294792/100000000:ℝ)) := by
  let O := fun n => (prep n).oracle
  have hcprice : ∀ᶠ n : ℕ in atTop, ∀ A B T,
      APSPAlgorithm.SymmetricQueryBound
        (StoredMinPlusAPSP.decode (viewTable A),StoredMinPlusAPSP.decode (viewTable B),
          StoredMinPlusAPSP.decode (viewTable T)) (64*n*W n+13:ℕ) →
      ((O n A B T).work:ℝ)+(O n A B T).answerWrites ≤ F n := by
    filter_upwards [hprice] with n hn
    intro A B T hb
    have h := hn A B T hb
    dsimp only [O]
    have hs : (0:ℝ) ≤ preparationWork (prep n):=Nat.cast_nonneg _
    linarith
  have hcallback := BinaryAPSPUniformCosts.callback_resources_bigO_of_uniform_price
    Payload EndToEndAPSP.Payload O EndToEndAPSP.directCallback
    (fun n=>correct_refines_direct _ (hcorrect n))
    EndToEndAPSP.directCallback_correct w W degree hw hW F hF0 hF hcprice
  have hhost := BinaryAPSPHostTotalCosts.run_hostBits_bigO Payload O w W degree hw hW
  have hsetup : (fun n : ℕ => (preparationWork (prep n):ℝ))
      =O[atTop] (fun n : ℕ => (Real.log (n:ℝ))^2*F n) := by
    apply IsBigO.of_norm_eventuallyLE
    filter_upwards [hprice,hF0,eventually_ge_atTop (3:ℕ)] with n hn hnonneg hn3
    have h := hn (zeroTable n) (zeroTable n) (zeroTable n) (zeroTable_query_bound n (W n))
    have hs : (preparationWork (prep n):ℝ) ≤ F n := by
      have hwc : (0:ℝ) ≤ ((prep n).oracle (zeroTable n) (zeroTable n) (zeroTable n)).work :=
        Nat.cast_nonneg _
      have hwrites : (0:ℝ) ≤ ((prep n).oracle (zeroTable n) (zeroTable n) (zeroTable n)).answerWrites :=
        Nat.cast_nonneg _
      linarith
    have hl := PhaseGeometry.one_le_log_nat n hn3
    have hlog : (1:ℝ) ≤ (Real.log (n:ℝ))^2 := one_le_pow₀ hl
    rw [Real.norm_of_nonneg (Nat.cast_nonneg _)]
    exact hs.trans (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hlog hnonneg)
  have htotal := ((hsetup.trans hF).add hhost).add hcallback
  simpa only [preparedExecution,preparationWork,O,Nat.cast_add,add_assoc] using htotal


#print axioms prepared_work_bigO_of_combined_price

private theorem prepared_price_from_setup
    (W a : ℕ → ℕ) (F : ℕ → ℝ)
    (hprice : ∀ᶠ n : ℕ in atTop, ∀ A B T,
      APSPAlgorithm.SymmetricQueryBound
        (StoredMinPlusAPSP.decode (viewTable A),StoredMinPlusAPSP.decode (viewTable B),
          StoredMinPlusAPSP.decode (viewTable T)) (64*n*W n+13:ℕ) →
      ((setupWork n (W n) (a n):ℕ):ℝ)+
        ((prepare n (W n) (a n)).oracle A B T).work+
        ((prepare n (W n) (a n)).oracle A B T).answerWrites ≤ F n) :
    ∀ᶠ n : ℕ in atTop, ∀ A B T,
      APSPAlgorithm.SymmetricQueryBound
        (StoredMinPlusAPSP.decode (viewTable A),StoredMinPlusAPSP.decode (viewTable B),
          StoredMinPlusAPSP.decode (viewTable T)) (64*n*W n+13:ℕ) →
      ((preparationWork (prepare n (W n) (a n)):ℕ):ℝ)+
        ((prepare n (W n) (a n)).oracle A B T).work+
        ((prepare n (W n) (a n)).oracle A B T).answerWrites ≤ F n := by
  filter_upwards [hprice] with n hn
  intro A B T hb
  rw [←setupWork_eq_preparationWork]
  exact hn A B T hb

#print axioms prepared_price_from_setup

private def preparationFamily (W a : ℕ → ℕ) (n : ℕ) : Preparation n (W n) (a n) :=
  prepare n (W n) (a n)

private theorem preparationFamily_apply (W a : ℕ → ℕ) (n : ℕ) :
    preparationFamily W a n=prepare n (W n) (a n) := rfl

private theorem preparationFamily_correct (W a : ℕ → ℕ) :
    ∀ n, OracleCorrect (preparationFamily W a n).oracle := by
  intro n
  rw [preparationFamily_apply]
  exact prepare_correct n (W n) (a n)

private theorem run_eq_family (W a : ℕ → ℕ) (n : ℕ)
    (w : StoredMinPlusAPSP.OptionalTable n) :
    BinaryAlignedAPSP.run w (W n) (a n)=preparedExecution (preparationFamily W a n) w :=
  (run_eq_prepared w (W n) (a n)).trans (congrArg
    (fun prep : Preparation n (W n) (a n) => preparedExecution prep w)
      (preparationFamily_apply W a n).symm)

private theorem family_price_from_setup
    (W a : ℕ → ℕ) (F : ℕ → ℝ)
    (hprice : ∀ᶠ n : ℕ in atTop, ∀ A B T,
      APSPAlgorithm.SymmetricQueryBound
        (StoredMinPlusAPSP.decode (viewTable A),StoredMinPlusAPSP.decode (viewTable B),
          StoredMinPlusAPSP.decode (viewTable T)) (64*n*W n+13:ℕ) →
      ((setupWork n (W n) (a n):ℕ):ℝ)+
        ((prepare n (W n) (a n)).oracle A B T).work+
        ((prepare n (W n) (a n)).oracle A B T).answerWrites ≤ F n) :
    ∀ᶠ n : ℕ in atTop, ∀ A B T,
      APSPAlgorithm.SymmetricQueryBound
        (StoredMinPlusAPSP.decode (viewTable A),StoredMinPlusAPSP.decode (viewTable B),
          StoredMinPlusAPSP.decode (viewTable T)) (64*n*W n+13:ℕ) →
      ((preparationWork (preparationFamily W a n):ℕ):ℝ)+
        ((preparationFamily W a n).oracle A B T).work+
        ((preparationFamily W a n).oracle A B T).answerWrites ≤ F n := by
  filter_upwards [prepared_price_from_setup W a F hprice] with n hn
  intro A B T hb
  rw [preparationFamily_apply]
  exact hn A B T hb

#print axioms preparationFamily_correct
#print axioms run_eq_family
#print axioms family_price_from_setup

private theorem concrete_prepared_work_bigO_of_combined_price
    (w : (n : ℕ) → StoredMinPlusAPSP.OptionalTable n) (W a : ℕ → ℕ)
    (degree : ℕ)
    (hw : ∀ n, APSPReduction.EdgeBound (StoredMinPlusAPSP.decode (w n)) (W n))
    (hW : ∀ n, W n ≤ n^degree) (F : ℕ → ℝ)
    (hF0 : ∀ᶠ n : ℕ in atTop, 0 ≤ F n)
    (hF : (fun n : ℕ => (Real.log (n:ℝ))^2*F n)
      =O[atTop] (fun n : ℕ => (n:ℝ)^(299294792/100000000:ℝ)))
    (hprice : ∀ᶠ n : ℕ in atTop, ∀ A B T,
      APSPAlgorithm.SymmetricQueryBound
        (StoredMinPlusAPSP.decode (viewTable A),StoredMinPlusAPSP.decode (viewTable B),
          StoredMinPlusAPSP.decode (viewTable T)) (64*n*W n+13:ℕ) →
      ((setupWork n (W n) (a n):ℕ):ℝ)+
        ((prepare n (W n) (a n)).oracle A B T).work+
        ((prepare n (W n) (a n)).oracle A B T).answerWrites ≤ F n) :
    (fun n : ℕ => ((preparedExecution (preparationFamily W a n) (w n)).work:ℝ))
      =O[atTop] (fun n : ℕ => (n:ℝ)^(299294792/100000000:ℝ)) :=
  prepared_work_bigO_of_combined_price w W a degree
    (preparationFamily W a) (preparationFamily_correct W a)
    hw hW F hF0 hF (family_price_from_setup W a F hprice)

#print axioms concrete_prepared_work_bigO_of_combined_price

theorem run_work_bigO_of_combined_price
    (w : (n : ℕ) → StoredMinPlusAPSP.OptionalTable n) (W a : ℕ → ℕ)
    (degree : ℕ)
    (hw : ∀ n, APSPReduction.EdgeBound (StoredMinPlusAPSP.decode (w n)) (W n))
    (hW : ∀ n, W n ≤ n^degree) (F : ℕ → ℝ)
    (hF0 : ∀ᶠ n : ℕ in atTop, 0 ≤ F n)
    (hF : (fun n : ℕ => (Real.log (n:ℝ))^2*F n)
      =O[atTop] (fun n : ℕ => (n:ℝ)^(299294792/100000000:ℝ)))
    (hprice : ∀ᶠ n : ℕ in atTop, ∀ A B T,
      APSPAlgorithm.SymmetricQueryBound
        (StoredMinPlusAPSP.decode (viewTable A),StoredMinPlusAPSP.decode (viewTable B),
          StoredMinPlusAPSP.decode (viewTable T)) (64*n*W n+13:ℕ) →
      ((setupWork n (W n) (a n):ℕ):ℝ)+
        ((prepare n (W n) (a n)).oracle A B T).work+
        ((prepare n (W n) (a n)).oracle A B T).answerWrites ≤ F n) :
    (fun n : ℕ => ((BinaryAlignedAPSP.run (w n) (W n) (a n)).work:ℝ))
      =O[atTop] (fun n : ℕ => (n:ℝ)^(299294792/100000000:ℝ)) := by
  have h := concrete_prepared_work_bigO_of_combined_price w W a degree hw hW F hF0 hF hprice
  exact h.congr_left (fun n => congrArg
    (fun e : BinaryAlignedAPSP.Execution n (W n) (a n) => (e.work:ℝ))
      (run_eq_family W a n (w n)).symm)

#print axioms setup_and_callback_le_original
#print axioms zeroTable_query_bound
#print axioms run_work_bigO_of_combined_price

end
end ThinMatrix.BinaryAlignedAPSPCosts
