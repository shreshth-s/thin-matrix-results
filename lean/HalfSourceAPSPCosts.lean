import HalfSourceAPSPHost
import HalfSourceComputedCosts
import BinaryAlignedAPSPCosts

/-! Intermediate uniform composition at the exact-half exponent. The
supplied actual callback must still discharge the displayed combined-price
premise. Host arithmetic and the actual new-parameter setup are retained. -/
namespace ThinMatrix.HalfSourceAPSPCosts
open Filter Asymptotics BinaryAPSPCaller BinaryAPSPHostTotalCosts BinaryAPSPHostCosts
open BinaryAPSPUniformCosts HalfSourceAPSPHost AdaptiveQueryBitBounds
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2500000

theorem hostAllowance_bigO (degree : ℕ) :
    hostAllowance degree =O[atTop] (fun n : ℕ => (n : ℝ)^(14963431313/5000000000 : ℝ)) := by
  let C : ℝ := ((5*(degree+1)+8 : ℕ) : ℝ)
  let K : ℝ := 40000000000*C^5
  have hlog : (fun n : ℕ => K*(Real.log (n : ℝ))^5*(n : ℝ)^2)
      =O[atTop] (fun n : ℕ => (n : ℝ)^(14963431313/5000000000 : ℝ)) := by
    have h := (AsymptoticCosts.logPowMulRpowBigO (a:=2)
      (d:=(14963431313/5000000000 : ℝ)) (by norm_num) 5).const_mul_left K
    simpa only [Real.rpow_two,mul_assoc] using h
  have hdom : hostAllowance degree =O[atTop] (fun n : ℕ => K*(Real.log (n : ℝ))^5*(n : ℝ)^2) := by
    apply IsBigO.of_norm_eventuallyLE
    filter_upwards [eventually_ge_atTop (3 : ℕ)] with n hn
    rw [Real.norm_of_nonneg (show 0 ≤ hostAllowance degree n by unfold hostAllowance; positivity)]
    have hb := budget_le_log n degree hn
    have hp := pow_le_pow_left₀ (Nat.cast_nonneg (budget n degree)) hb 5
    change (budget n degree : ℝ)^5 ≤ (C*Real.log (n : ℝ))^5 at hp
    calc
      hostAllowance degree n ≤ 40000000000*(n : ℝ)^2*(C*Real.log (n : ℝ))^5 :=
        mul_le_mul_of_nonneg_left hp (by positivity)
      _ = K*(Real.log (n : ℝ))^5*(n : ℝ)^2 := by rw [mul_pow]; dsimp only [K]; ring
  exact hdom.trans hlog

theorem run_hostBits_bigO (Payload : ℕ → Type) (O : (n : ℕ) → Oracle n (Payload n))
    (w : (n : ℕ) → StoredMinPlusAPSP.OptionalTable n) (W : ℕ → ℕ) (degree : ℕ)
    (hw : ∀ n, APSPReduction.EdgeBound (StoredMinPlusAPSP.decode (w n)) (W n))
    (hW : ∀ n, W n ≤ n^degree) :
    (fun n : ℕ => ((run (O n) (w n) (W n)).hostBits : ℝ))
      =O[atTop] (fun n : ℕ => (n : ℝ)^(14963431313/5000000000 : ℝ)) := by
  have hdom : (fun n : ℕ => ((run (O n) (w n) (W n)).hostBits : ℝ)) =O[atTop] hostAllowance degree := by
    apply IsBigO.of_norm_eventuallyLE
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    rw [Real.norm_of_nonneg (Nat.cast_nonneg _)]
    have h := run_hostBits_le (by omega) (O n) (w n) (W n) degree (hw n) (hW n)
    unfold hostAllowance
    exact_mod_cast h
  exact hdom.trans (hostAllowance_bigO degree)


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
      =O[atTop] (fun n : ℕ => (n:ℝ)^(14963431313/5000000000:ℝ)))
    (hcallback : ∀ᶠ n : ℕ in atTop, ∀ A B T,
      APSPAlgorithm.SymmetricQueryBound
        (StoredMinPlusAPSP.decode (viewTable A),StoredMinPlusAPSP.decode (viewTable B),
          StoredMinPlusAPSP.decode (viewTable T)) (64*n*W n+13:ℕ) →
      ((O n A B T).work:ℝ)+(O n A B T).answerWrites ≤ F n) :
    (fun n : ℕ => ((run (O n) (w n) (W n)).oracleWork:ℝ)+
      (run (O n) (w n) (W n)).answerWrites)
      =O[atTop] (fun n : ℕ => (n:ℝ)^(14963431313/5000000000:ℝ)) := by
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


variable (factory : BackendFactory)

def preparationWork {n W a : ℕ} (prep : Preparation factory n W a) : ℕ :=
  prep.setupBits+(a+1)*(prep.setupControl+8)

def setupWork (n W a : ℕ) : ℕ := preparationWork factory (prepare factory n W a)

/-- A proof-level assembly of the retained fields of one preparation. -/
def preparedExecution {n W a : ℕ} (prep : Preparation factory n W a)
    (w : StoredMinPlusAPSP.OptionalTable n) : HalfSourceAPSPHost.Execution factory n W a :=
  let core := BinaryAPSPCaller.run prep.oracle w W
  ⟨prep,core,prep.setupBits+(a+1)*(prep.setupControl+8)+
    core.hostBits+core.oracleWork+core.answerWrites⟩

private theorem run_eq_prepared {n : ℕ} (w : StoredMinPlusAPSP.OptionalTable n) (W a : ℕ) :
    HalfSourceAPSPHost.run factory w W a=preparedExecution factory (prepare factory n W a) w := rfl

private theorem prepared_work_bigO_of_combined_price
    (w : (n : ℕ) → StoredMinPlusAPSP.OptionalTable n) (W a : ℕ → ℕ)
    (degree : ℕ)
    (prep : (n : ℕ) → Preparation factory n (W n) (a n))
    (hcorrect : ∀ n, OracleCorrect factory (prep n).oracle)
    (hw : ∀ n, APSPReduction.EdgeBound (StoredMinPlusAPSP.decode (w n)) (W n))
    (hW : ∀ n, W n ≤ n^degree) (F : ℕ → ℝ)
    (hF0 : ∀ᶠ n : ℕ in atTop, 0 ≤ F n)
    (hF : (fun n : ℕ => (Real.log (n:ℝ))^2*F n)
      =O[atTop] (fun n : ℕ => (n:ℝ)^(14963431313/5000000000:ℝ)))
    (hprice : ∀ᶠ n : ℕ in atTop, ∀ A B T,
      APSPAlgorithm.SymmetricQueryBound
        (StoredMinPlusAPSP.decode (viewTable A),StoredMinPlusAPSP.decode (viewTable B),
          StoredMinPlusAPSP.decode (viewTable T)) (64*n*W n+13:ℕ) →
      ((preparationWork factory (prep n):ℕ):ℝ)+
        ((prep n).oracle A B T).work+
        ((prep n).oracle A B T).answerWrites  ≤  F n) :
    (fun n : ℕ => ((preparedExecution factory (prep n) (w n)).work:ℝ))
      =O[atTop] (fun n : ℕ => (n:ℝ)^(14963431313/5000000000:ℝ)) := by
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
    have hs : (0:ℝ) ≤ preparationWork factory (prep n):=Nat.cast_nonneg _
    linarith
  have hcallback := callback_resources_bigO_of_uniform_price
    (Payload factory) EndToEndAPSP.Payload O EndToEndAPSP.directCallback
    (fun n=>correct_refines_direct factory _ (hcorrect n))
    EndToEndAPSP.directCallback_correct w W degree hw hW F hF0 hF hcprice
  have hhost := run_hostBits_bigO (Payload factory) O w W degree hw hW
  have hsetup : (fun n : ℕ => (preparationWork factory (prep n):ℝ))
      =O[atTop] (fun n : ℕ => (Real.log (n:ℝ))^2*F n) := by
    apply IsBigO.of_norm_eventuallyLE
    filter_upwards [hprice,hF0,eventually_ge_atTop (3:ℕ)] with n hn hnonneg hn3
    have h := hn (BinaryAlignedAPSPCosts.zeroTable n) (BinaryAlignedAPSPCosts.zeroTable n) (BinaryAlignedAPSPCosts.zeroTable n) (BinaryAlignedAPSPCosts.zeroTable_query_bound n (W n))
    have hs : (preparationWork factory (prep n):ℝ) ≤ F n := by
      have hwc : (0:ℝ) ≤ ((prep n).oracle (BinaryAlignedAPSPCosts.zeroTable n) (BinaryAlignedAPSPCosts.zeroTable n) (BinaryAlignedAPSPCosts.zeroTable n)).work :=
        Nat.cast_nonneg _
      have hwrites : (0:ℝ) ≤ ((prep n).oracle (BinaryAlignedAPSPCosts.zeroTable n) (BinaryAlignedAPSPCosts.zeroTable n) (BinaryAlignedAPSPCosts.zeroTable n)).answerWrites :=
        Nat.cast_nonneg _
      linarith
    have hl := PhaseGeometry.one_le_log_nat n hn3
    have hlog : (1:ℝ) ≤ (Real.log (n:ℝ))^2 := one_le_pow₀ hl
    rw [Real.norm_of_nonneg (Nat.cast_nonneg _)]
    exact hs.trans (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hlog hnonneg)
  have htotal := ((hsetup.trans hF).add hhost).add hcallback
  simpa only [preparedExecution,preparationWork,O,Nat.cast_add,add_assoc] using htotal

private theorem prepared_price_from_setup
    (W a : ℕ → ℕ) (F : ℕ → ℝ)
    (hprice : ∀ᶠ n : ℕ in atTop, ∀ A B T,
      APSPAlgorithm.SymmetricQueryBound
        (StoredMinPlusAPSP.decode (viewTable A),StoredMinPlusAPSP.decode (viewTable B),
          StoredMinPlusAPSP.decode (viewTable T)) (64*n*W n+13:ℕ) →
      ((setupWork factory n (W n) (a n):ℕ):ℝ)+
        ((prepare factory n (W n) (a n)).oracle A B T).work+
        ((prepare factory n (W n) (a n)).oracle A B T).answerWrites ≤ F n) :
    ∀ᶠ n : ℕ in atTop, ∀ A B T,
      APSPAlgorithm.SymmetricQueryBound
        (StoredMinPlusAPSP.decode (viewTable A),StoredMinPlusAPSP.decode (viewTable B),
          StoredMinPlusAPSP.decode (viewTable T)) (64*n*W n+13:ℕ) →
      ((preparationWork factory (prepare factory n (W n) (a n)):ℕ):ℝ)+
        ((prepare factory n (W n) (a n)).oracle A B T).work+
        ((prepare factory n (W n) (a n)).oracle A B T).answerWrites ≤ F n := by
  filter_upwards [hprice] with n hn
  intro A B T hb
  rw [←show setupWork factory n (W n) (a n)=preparationWork factory (prepare factory n (W n) (a n)) by rfl]
  exact hn A B T hb

#print axioms prepared_price_from_setup

private def preparationFamily (W a : ℕ → ℕ) (n : ℕ) : Preparation factory n (W n) (a n) :=
  prepare factory n (W n) (a n)

private theorem preparationFamily_apply (W a : ℕ → ℕ) (n : ℕ) :
    preparationFamily factory W a n=prepare factory n (W n) (a n) := rfl

private theorem preparationFamily_correct (W a : ℕ → ℕ) :
    ∀ n, OracleCorrect factory (preparationFamily factory W a n).oracle := by
  intro n
  rw [preparationFamily_apply]
  exact prepare_correct factory n (W n) (a n)

private theorem run_eq_family (W a : ℕ → ℕ) (n : ℕ)
    (w : StoredMinPlusAPSP.OptionalTable n) :
    HalfSourceAPSPHost.run factory w (W n) (a n)=preparedExecution factory (preparationFamily factory W a n) w :=
  (run_eq_prepared factory w (W n) (a n)).trans (congrArg
    (fun prep : Preparation factory n (W n) (a n) => preparedExecution factory prep w)
      (preparationFamily_apply factory W a n).symm)

private theorem family_price_from_setup
    (W a : ℕ → ℕ) (F : ℕ → ℝ)
    (hprice : ∀ᶠ n : ℕ in atTop, ∀ A B T,
      APSPAlgorithm.SymmetricQueryBound
        (StoredMinPlusAPSP.decode (viewTable A),StoredMinPlusAPSP.decode (viewTable B),
          StoredMinPlusAPSP.decode (viewTable T)) (64*n*W n+13:ℕ) →
      ((setupWork factory n (W n) (a n):ℕ):ℝ)+
        ((prepare factory n (W n) (a n)).oracle A B T).work+
        ((prepare factory n (W n) (a n)).oracle A B T).answerWrites ≤ F n) :
    ∀ᶠ n : ℕ in atTop, ∀ A B T,
      APSPAlgorithm.SymmetricQueryBound
        (StoredMinPlusAPSP.decode (viewTable A),StoredMinPlusAPSP.decode (viewTable B),
          StoredMinPlusAPSP.decode (viewTable T)) (64*n*W n+13:ℕ) →
      ((preparationWork factory (preparationFamily factory W a n):ℕ):ℝ)+
        ((preparationFamily factory W a n).oracle A B T).work+
        ((preparationFamily factory W a n).oracle A B T).answerWrites ≤ F n := by
  filter_upwards [prepared_price_from_setup factory W a F hprice] with n hn
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
      =O[atTop] (fun n : ℕ => (n:ℝ)^(14963431313/5000000000:ℝ)))
    (hprice : ∀ᶠ n : ℕ in atTop, ∀ A B T,
      APSPAlgorithm.SymmetricQueryBound
        (StoredMinPlusAPSP.decode (viewTable A),StoredMinPlusAPSP.decode (viewTable B),
          StoredMinPlusAPSP.decode (viewTable T)) (64*n*W n+13:ℕ) →
      ((setupWork factory n (W n) (a n):ℕ):ℝ)+
        ((prepare factory n (W n) (a n)).oracle A B T).work+
        ((prepare factory n (W n) (a n)).oracle A B T).answerWrites ≤ F n) :
    (fun n : ℕ => ((preparedExecution factory (preparationFamily factory W a n) (w n)).work:ℝ))
      =O[atTop] (fun n : ℕ => (n:ℝ)^(14963431313/5000000000:ℝ)) :=
  prepared_work_bigO_of_combined_price factory w W a degree
    (preparationFamily factory W a) (preparationFamily_correct factory W a)
    hw hW F hF0 hF (family_price_from_setup factory W a F hprice)

#print axioms concrete_prepared_work_bigO_of_combined_price

theorem run_work_bigO_of_combined_price
    (w : (n : ℕ) → StoredMinPlusAPSP.OptionalTable n) (W a : ℕ → ℕ)
    (degree : ℕ)
    (hw : ∀ n, APSPReduction.EdgeBound (StoredMinPlusAPSP.decode (w n)) (W n))
    (hW : ∀ n, W n ≤ n^degree) (F : ℕ → ℝ)
    (hF0 : ∀ᶠ n : ℕ in atTop, 0 ≤ F n)
    (hF : (fun n : ℕ => (Real.log (n:ℝ))^2*F n)
      =O[atTop] (fun n : ℕ => (n:ℝ)^(14963431313/5000000000:ℝ)))
    (hprice : ∀ᶠ n : ℕ in atTop, ∀ A B T,
      APSPAlgorithm.SymmetricQueryBound
        (StoredMinPlusAPSP.decode (viewTable A),StoredMinPlusAPSP.decode (viewTable B),
          StoredMinPlusAPSP.decode (viewTable T)) (64*n*W n+13:ℕ) →
      ((setupWork factory n (W n) (a n):ℕ):ℝ)+
        ((prepare factory n (W n) (a n)).oracle A B T).work+
        ((prepare factory n (W n) (a n)).oracle A B T).answerWrites ≤ F n) :
    (fun n : ℕ => ((HalfSourceAPSPHost.run factory (w n) (W n) (a n)).work:ℝ))
      =O[atTop] (fun n : ℕ => (n:ℝ)^(14963431313/5000000000:ℝ)) := by
  have h := concrete_prepared_work_bigO_of_combined_price factory w W a degree hw hW F hF0 hF hprice
  exact h.congr_left (fun n => congrArg
    (fun e : HalfSourceAPSPHost.Execution factory n (W n) (a n) => (e.work:ℝ))
      (run_eq_family factory W a n (w n)).symm)

#print axioms hostAllowance_bigO
#print axioms run_hostBits_bigO
#print axioms callback_resources_bigO_of_uniform_price
#print axioms run_work_bigO_of_combined_price
end
end ThinMatrix.HalfSourceAPSPCosts
