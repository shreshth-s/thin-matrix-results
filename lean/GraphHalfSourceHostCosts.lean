import GraphHalfSourcePreparedCosts
import HalfSourceHostSetupTransport
import BinaryAPSPPublicCostBounds

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

/-! Remaining host assembly, with the local phase-cost obligation explicit.
This is an intermediate implication; the final theorem must instantiate
phasePrices from the concrete source, completion and address proofs. -/
namespace ThinMatrix.GraphHalfSourceHostCosts
open Filter Asymptotics BinaryAPSPCaller HalfSourceAPSPHost HalfSourceAPSPCosts
open BinaryAPSPPublicCostBounds HalfSourceCallbackBudget
noncomputable section
attribute [local irreducible] HalfSourceBatchFit.block HalfSourceBatchFit.R HalfSourceBatchFit.S
  GraphHalfSourceExecution.execute GraphHalfSourceBackend.concreteTable
  HalfSourceCallbackBudget.callbackCoefficient
variable (scheme : RectangularBatch.Scheme) (hnum : scheme.num=861) (hden : scheme.den=500)
  (hz : scheme.z=15) (hv : scheme.Valid)

def factory := GraphHalfSourceBackend.factory scheme hnum hden hz hv

def phasePrices (κ A k : ℕ) (C : ℝ) : Prop :=
  ∀ᶠ n : ℕ in atTop,∀ X Y T : BinaryTriangleExecution.IntTable n,
    CountedEndToEndAPSP.entryQueryBound (BinaryTriangleExecution.viewTable X)
      (BinaryTriangleExecution.viewTable Y) (BinaryTriangleExecution.viewTable T)≤n^κ →
    ∀ phase : HalfSourceBatchFit.Call n,EndToEndAPSP.ValidFactors phase.factors →
    ∀ (selected : List ℕ) (candidate : ℕ),phase.factors=selected++[candidate] →
    ∀ active : ArrayCompositeAlgorithm.Flags (EndToEndAPSP.incidenceSize n (HalfSourceBatchFit.block n)),
    ((GraphHalfSourceBackend.concreteTable scheme hnum hden hz hv X Y T selected candidate active
      (addressPrice n κ A)).work:ℝ)≤C*(Real.log (n:ℝ))^k*HalfSourceComputedCosts.phaseRawSum n phase

def hostAddress (degree A : ℕ) (n : ℕ) : ℕ := addressPrice n (degree+2) A

def finalPrice (degree A k : ℕ) (C : ℝ) (n : ℕ) : ℝ :=
  2*GraphHalfSourcePreparedCosts.price (degree+2) A k C n+
    setupAllowance degree (unitConstant (degree+2) A) n

theorem selector_extra (degree A : ℕ) :
    ∀ᶠ n : ℕ in atTop,∀ W, W≤n^degree →
    (((addressPrice n (degree+2) A+2)*(HalfSourceParameterExecution.execute n (cap n W)).bitSteps+
      publicSetupBits n W+76*(addressPrice n (degree+2) A+1):ℕ):ℝ)≤
      setupAllowance degree (unitConstant (degree+2) A) n := by
  filter_upwards [HalfSourceParameterExecution.execute_apspCap_eventually degree,eventually_ge_atTop (1:ℕ)] with n hs hn
  intro W hW
  have hsteps : (HalfSourceParameterExecution.execute n (cap n W)).bitSteps≤n^2 := by
    exact_mod_cast hs W hW
  have h := extraSetup_le_setupAllowance_nat degree (unitConstant (degree+2) A) n W
    (addressPrice n (degree+2) A) _ hn hW (addressPrice_poly n (degree+2) A) hsteps
  unfold setupAllowance
  exact_mod_cast h

theorem setup_allowance_bigO (degree A : ℕ) :
    (fun n : ℕ=>(Real.log (n:ℝ))^2*setupAllowance degree (unitConstant (degree+2) A) n) =O[atTop]
      (fun n : ℕ=>(n:ℝ)^(14963431313/5000000000:ℝ)) := by
  let H : ℝ := setupConstant degree (unitConstant (degree+2) A)
  have hm : (fun n : ℕ=>(25*H)*(Real.log (n:ℝ))^4*(n:ℝ)^2) =O[atTop]
      (fun n : ℕ=>(n:ℝ)^(14963431313/5000000000:ℝ)) := by
    simpa only [Real.rpow_two,mul_assoc] using
      (AsymptoticCosts.logPowMulRpowBigO (a:=2) (d:=(14963431313/5000000000:ℝ))
        (by norm_num) 4).const_mul_left (25*H)
  have hd : (fun n : ℕ=>(Real.log (n:ℝ))^2*setupAllowance degree (unitConstant (degree+2) A) n) =O[atTop]
      (fun n : ℕ=>(25*H)*(Real.log (n:ℝ))^4*(n:ℝ)^2) := by
    apply IsBigO.of_norm_eventuallyLE
    filter_upwards [eventually_ge_atTop (3:ℕ)] with n hn
    have hs := pow_le_pow_left₀ (Nat.cast_nonneg (n.size+1)) (size_add_one_le_log n hn) 2
    rw [Real.norm_of_nonneg (by unfold setupAllowance;positivity)]
    calc
      _ ≤ (Real.log (n:ℝ))^2*(H*(n:ℝ)^2*(5*Real.log (n:ℝ))^2) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hs (by dsimp [H];positivity)) (sq_nonneg _)
      _ = _ := by ring
  exact hd.trans hm

theorem finalPrice_bigO (degree A k : ℕ) (C : ℝ) :
    (fun n : ℕ=>(Real.log (n:ℝ))^2*finalPrice degree A k C n) =O[atTop]
      (fun n : ℕ=>(n:ℝ)^(14963431313/5000000000:ℝ)) := by
  have hp := (GraphHalfSourcePreparedCosts.price_bigO (degree+2) A k 2 C).const_mul_left 2
  have hs := setup_allowance_bigO degree A
  simpa only [finalPrice,mul_add,mul_assoc,mul_comm,mul_left_comm] using hp.add hs

theorem finalPrice_nonneg (degree A k : ℕ) (C : ℝ) (hC : 0≤C) (n : ℕ) (hn : 3≤n) :
    0≤finalPrice degree A k C n := by
  have hl : 0≤Real.log (n:ℝ) := le_trans (by norm_num) (PhaseGeometry.one_le_log_nat n hn)
  have hg := HalfSourceComputedCosts.allPhaseLedger_nonneg n hn
  have hr : 0≤AlignedAPSPCosts.ControllerCosts.referenceControllerConstant HalfSourceBatchFit.R := by
    have hlog2 : 0<Real.log 2 := Real.log_pos (by norm_num)
    have hR : 0≤(HalfSourceBatchFit.R:ℝ) := Nat.cast_nonneg _
    have hinner : 0≤8*(HalfSourceBatchFit.R:ℝ)+11 := add_nonneg (mul_nonneg (by norm_num) hR) (by norm_num)
    have hleft : 0≤2+1/Real.log 2 := add_nonneg (by norm_num) (le_of_lt (one_div_pos.mpr hlog2))
    exact mul_nonneg (by norm_num) (add_nonneg (mul_nonneg hleft hinner) (by norm_num))
  have hs : 0≤BinaryTriangleCosts.FixedPrices.sizeLogConstant := by
    unfold BinaryTriangleCosts.FixedPrices.sizeLogConstant
    positivity
  have hc : 0≤HalfSourceCallbackCosts.coefficient (degree+2) A :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hs 2)) hr
  have ht : 0≤GraphHalfSourcePreparedCosts.setupCoefficient (degree+2) A :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hs 3)) hr
  have hp : 0≤(n:ℝ)^(3-(HalfSourceBatchFit.b-HalfSourceBatchFit.eta)) :=
    Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hm : 0≤(6*(HalfSourceBatchFit.R:ℝ)*C)*(Real.log (n:ℝ))^(k+1)*HalfSourceComputedCosts.allPhaseLedger n :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) hC) (pow_nonneg hl _)) hg
  have hcall : 0≤HalfSourceCallbackCosts.overhead (degree+2) A n :=
    mul_nonneg (mul_nonneg hc (pow_nonneg hl _)) hp
  have hsetup : 0≤GraphHalfSourcePreparedCosts.setupOverhead (degree+2) A n :=
    mul_nonneg (mul_nonneg ht (pow_nonneg hl _)) hp
  have htotal : 0≤GraphHalfSourcePreparedCosts.price (degree+2) A k C n :=
    add_nonneg (add_nonneg hm hcall) hsetup
  have ha : 0≤ setupAllowance degree (unitConstant (degree+2) A) n := by
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)) (sq_nonneg _)
  exact add_nonneg (mul_nonneg (by norm_num) htotal) ha

theorem combined_price (degree A k : ℕ) (C : ℝ) (hC : 0≤C)
    (hphase : phasePrices scheme hnum hden hz hv (degree+2) A k C) :
    ∀ᶠ n : ℕ in atTop,∀ W,W≤n^degree →∀ X Y T : IntTable n,
      APSPAlgorithm.SymmetricQueryBound
        (StoredMinPlusAPSP.decode (viewTable X),StoredMinPlusAPSP.decode (viewTable Y),
          StoredMinPlusAPSP.decode (viewTable T)) (64*n*W+13:ℕ) →
      (setupWork (factory scheme hnum hden hz hv) n W (addressPrice n (degree+2) A):ℝ)+
        ((prepare (factory scheme hnum hden hz hv) n W (addressPrice n (degree+2) A)).oracle X Y T).work+
        ((prepare (factory scheme hnum hden hz hv) n W (addressPrice n (degree+2) A)).oracle X Y T).answerWrites≤
          finalPrice degree A k C n := by
  filter_upwards [hphase,HalfSourcePrimeParameters.eventually_program_apspCap degree,selector_extra degree A,
    eventually_ge_atTop (232:ℕ)] with n hlocal hsuccess hextra hn
  intro W hW X Y T hb
  have hn3 : 3≤n := by omega
  have hU : cap n W≤n^(degree+2) := cap_le_power degree n W hn hW
  have hentry : CountedEndToEndAPSP.entryQueryBound (BinaryTriangleExecution.viewTable X)
      (BinaryTriangleExecution.viewTable Y) (BinaryTriangleExecution.viewTable T)≤cap n W :=
    query_entryBound_le_cap X Y T hb
  have hs : (HalfSourcePrimeParameters.program n (cap n W)).isSome=true := hsuccess W hW
  cases hp : HalfSourcePrimeParameters.program n (cap n W) with
  | none => simp only [hp,Option.isSome_none,Bool.false_eq_true] at hs
  | some parameters =>
    have he : (HalfSourceParameterExecution.execute n (cap n W)).value=some parameters :=
      (HalfSourceParameterExecution.execute_value n (cap n W)).trans hp
    let labels := HalfSourceParameterMetadata.successfulLabels (HalfSourceParameterExecution.execute n (cap n W)) rfl parameters he
    have hl := HalfSourceParameterMetadata.successfulLabels_eq (HalfSourceParameterExecution.execute n (cap n W)) rfl parameters he
    have ht := GraphHalfSourcePreparedCosts.prepared_price scheme hnum hden hz hv
      (A:=A) hn3 parameters hp hU labels hl X Y T hentry C k hC (hlocal X Y T (hentry.trans hU))
    have ht' :
        ((HalfSourceAPSPTransport.originalCallback (factory scheme hnum hden hz hv) W (addressPrice n (degree+2) A)
          (HalfSourceParameterExecution.execute n (cap n W)) rfl parameters he).setupBits:ℝ)+
        (addressPrice n (degree+2) A:ℝ)*(HalfSourceAPSPTransport.originalCallback (factory scheme hnum hden hz hv) W (addressPrice n (degree+2) A)
          (HalfSourceParameterExecution.execute n (cap n W)) rfl parameters he).setupControl+
        ((HalfSourceAPSPTransport.originalCallback (factory scheme hnum hden hz hv) W (addressPrice n (degree+2) A)
          (HalfSourceParameterExecution.execute n (cap n W)) rfl parameters he).oracle X Y T).work+
        ((HalfSourceAPSPTransport.originalCallback (factory scheme hnum hden hz hv) W (addressPrice n (degree+2) A)
          (HalfSourceParameterExecution.execute n (cap n W)) rfl parameters he).oracle X Y T).answerWrites≤
          GraphHalfSourcePreparedCosts.price (degree+2) A k C n := ht
    have ha : 1≤addressPrice n (degree+2) A := one_le_addressedUnit _ _
    have hhost := HalfSourceHostSetupTransport.setup_and_callback_le_original
      (factory scheme hnum hden hz hv) W (addressPrice n (degree+2) A) ha parameters he X Y T
    have hx := hextra W hW
    have hh := (Nat.cast_le (α:=ℝ)).mpr hhost
    push_cast at hh hx
    unfold finalPrice
    linarith only [hh,hx,ht']

attribute [local irreducible] factory

theorem combined_price_at (degree A k : ℕ) (C : ℝ) (hC : 0≤C)
    (hphase : phasePrices scheme hnum hden hz hv (degree+2) A k C)
    (W : ℕ→ℕ) (hW : ∀ n,W n≤n^degree) :
    ∀ᶠ n : ℕ in atTop,∀ X Y T : IntTable n,
      APSPAlgorithm.SymmetricQueryBound
        (StoredMinPlusAPSP.decode (viewTable X),StoredMinPlusAPSP.decode (viewTable Y),
          StoredMinPlusAPSP.decode (viewTable T)) (64*n*W n+13:ℕ) →
      (setupWork (factory scheme hnum hden hz hv) n (W n) (addressPrice n (degree+2) A):ℝ)+
        ((prepare (factory scheme hnum hden hz hv) n (W n) (addressPrice n (degree+2) A)).oracle X Y T).work+
        ((prepare (factory scheme hnum hden hz hv) n (W n) (addressPrice n (degree+2) A)).oracle X Y T).answerWrites≤
          finalPrice degree A k C n := by
  filter_upwards [combined_price scheme hnum hden hz hv degree A k C hC hphase] with n hn
  exact hn (W n) (hW n)

theorem finalPrice_eventually_nonneg (degree A k : ℕ) (C : ℝ) (hC : 0≤C) :
    ∀ᶠ n : ℕ in atTop, 0≤finalPrice degree A k C n := by
  filter_upwards [eventually_ge_atTop (3:ℕ)] with n hn
  exact finalPrice_nonneg degree A k C hC n hn

/-- Named cost proposition keeps the executable backend opaque during kernel
conversion; unfolding it is exactly the displayed APSP work bound. -/
def workStatement (backend : BackendFactory)
    (w : (n : ℕ)→StoredMinPlusAPSP.OptionalTable n) (W a : ℕ→ℕ) : Prop :=
    (fun n : ℕ=>((HalfSourceAPSPHost.run backend (w n) (W n) (a n)).work:ℝ)) =O[atTop]
      (fun n : ℕ=>(n:ℝ)^(14963431313/5000000000:ℝ))

private theorem addressed_work_of_combined (backend : BackendFactory)
    (degree A k : ℕ) (C : ℝ) (hC : 0≤C)
    (w : (n : ℕ)→StoredMinPlusAPSP.OptionalTable n) (W : ℕ→ℕ)
    (hw : ∀ n,APSPReduction.EdgeBound (StoredMinPlusAPSP.decode (w n)) (W n))
    (hW : ∀ n,W n≤n^degree)
    (hp : ∀ᶠ n : ℕ in atTop,∀ X Y T,
      APSPAlgorithm.SymmetricQueryBound
        (StoredMinPlusAPSP.decode (viewTable X),StoredMinPlusAPSP.decode (viewTable Y),
          StoredMinPlusAPSP.decode (viewTable T)) (64*n*W n+13:ℕ) →
      (setupWork backend n (W n) (hostAddress degree A n):ℝ)+
        ((prepare backend n (W n) (hostAddress degree A n)).oracle X Y T).work+
        ((prepare backend n (W n) (hostAddress degree A n)).oracle X Y T).answerWrites≤
          finalPrice degree A k C n) :
    workStatement backend w W (hostAddress degree A) :=
  HalfSourceAPSPCosts.run_work_bigO_of_combined_price backend w W
    (hostAddress degree A) degree hw hW (finalPrice degree A k C)
    (finalPrice_eventually_nonneg degree A k C hC) (finalPrice_bigO degree A k C) hp

#print axioms selector_extra
#print axioms setup_allowance_bigO
#print axioms finalPrice_bigO
#print axioms finalPrice_nonneg
#print axioms combined_price
#print axioms combined_price_at
#print axioms finalPrice_eventually_nonneg
#print axioms addressed_work_of_combined
end
end ThinMatrix.GraphHalfSourceHostCosts
