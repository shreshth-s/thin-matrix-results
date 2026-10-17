import BinaryTriangleExecution
import AlignedAPSPCosts
import BinaryControllerPolynomialBounds
import BinaryFoldedFormationCost
import BinaryFoldedMetadataBounds
import BinaryFoldedCallFormationCosts
import BinaryBackendCosts

/-!
# Costs of the retained binary triangle callback

The callback executes binary coefficient arithmetic and retains every producer
return once.  The bounds in this file sum those retained returns in their
original order and separately price the cap check, binary controller, original
sum checks and output writes.  Public indexed-array operations retain the
explicit address price used by the binary execution interface.
-/

namespace ThinMatrix.BinaryTriangleCosts
open scoped BigOperators
open Filter BinaryTriangleExecution

/-- The magnitude cap inspected by the actual callback bounds every stored
input cell, including inputs which do not occur in a live incidence. -/
theorem inputBits_of_entry_cap {n U : ℕ} (A B T : IntTable n)
    (hcap : CountedEndToEndAPSP.entryQueryBound (viewTable A) (viewTable B) (viewTable T) ≤ U) :
    InputBits A B T U.size := by
  have hmag : CountedEndToEndAPSP.entryMagnitude (viewTable A) (viewTable B) (viewTable T) ≤ U := by
    unfold CountedEndToEndAPSP.entryQueryBound at hcap
    omega
  refine ⟨?_,?_,?_⟩
  · intro i j
    have h := (CountedEndToEndAPSP.entryMagnitude_bounds (viewTable A) (viewTable B) (viewTable T) i j).1
    rw [viewTable_read] at h
    exact Nat.size_le_size (h.trans hmag)
  · intro i j
    have h := (CountedEndToEndAPSP.entryMagnitude_bounds (viewTable A) (viewTable B) (viewTable T) i j).2.1
    rw [viewTable_read] at h
    exact Nat.size_le_size (h.trans hmag)
  · intro i j
    have h := (CountedEndToEndAPSP.entryMagnitude_bounds (viewTable A) (viewTable B) (viewTable T) i j).2.2
    rw [viewTable_read] at h
    exact Nat.size_le_size (h.trans hmag)

theorem polynomial_cap_size (n U degree : ℕ) (hU : U ≤ n^degree) :
    U.size ≤ degree*n.size+1 := by
  have hn : n ≤ 2^n.size := (Nat.lt_size_self n).le
  have hp : U ≤ 2^(degree*n.size) := by
    calc
      U ≤ n^degree := hU
      _ ≤ (2^n.size)^degree := Nat.pow_le_pow_left hn degree
      _ = _ := by rw [←pow_mul,Nat.mul_comm n.size degree]
  simpa only [Nat.size_pow] using Nat.size_le_size hp

theorem inputBits_mono {n B C : ℕ} (A D T : IntTable n)
    (h : InputBits A D T B) (hBC : B ≤ C) : InputBits A D T C :=
  ⟨fun i j => (h.1 i j).trans hBC,fun i j => (h.2.1 i j).trans hBC,
    fun i j => (h.2.2 i j).trans hBC⟩

theorem inputBits_of_polynomial_entry_cap {n U degree : ℕ} (A B T : IntTable n)
    (hU : U ≤ n^degree)
    (hcap : CountedEndToEndAPSP.entryQueryBound (viewTable A) (viewTable B) (viewTable T) ≤ U) :
    InputBits A B T (degree*n.size+1) :=
  inputBits_mono A B T (inputBits_of_entry_cap A B T hcap) (polynomial_cap_size n U degree hU)

/-- The finite reference controller budget is used only as an upper bound on
the actual binary controller and its surrounding scans. -/
def referenceBudget (n h P k stages : ℕ) : ℕ :=
  AlignedAPSPCosts.ControllerCosts.referenceControllerBudget n h P k stages

theorem computed_referenceBudget_le {n U : ℕ} (hn : 3 ≤ n)
    (parameters : CompleteAPSP.Parameters (ComputableParameters.block n) U)
    (hp : ComputableParameters.program n U=some parameters) :
    (referenceBudget n (ComputableParameters.block n) parameters.pool.card parameters.k parameters.stages : ℝ) ≤ AlignedAPSPCosts.ControllerCosts.referenceControllerConstant AlignedCertificate.R*
        (Real.log (n:ℝ))^5*(n:ℝ)^(3-(AsymptoticCosts.b-AsymptoticCosts.eta)) := by
  have hs := ComputableParameters.program_sound n U parameters hp
  have hk : parameters.k ≤ AlignedCertificate.R := by
    rw [hs.2.2.2.1]
    norm_num [ComputableParameters.factorCount,AlignedCertificate.R]
  have h := AlignedAPSPCosts.ControllerCosts.computed_referenceControllerBudget_le
    AlignedCertificate.R parameters.k n hn hk
  rw [←hs.1,←hs.2.2.2.2.2] at h
  exact h

theorem referenceCoefficient_nonneg :
    0 ≤ AlignedAPSPCosts.ControllerCosts.referenceControllerConstant AlignedCertificate.R := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold AlignedAPSPCosts.ControllerCosts.referenceControllerConstant
  exact mul_nonneg (by norm_num) (add_nonneg
    (mul_nonneg (add_nonneg (by norm_num) (one_div_nonneg.mpr hl.le))
      (by positivity)) (by norm_num))

/-- A polylogarithmic price for each already executed controller/scanning
site is absorbed by the separate bookkeeping term of the phase ledger. -/
theorem priced_referenceBudget_le_chargedCost {n U : ℕ} (hn : 3 ≤ n)
    (parameters : CompleteAPSP.Parameters (ComputableParameters.block n) U)
    (hp : ComputableParameters.program n U=some parameters)
    (price : ℕ) (C : ℝ) (j : ℕ) (hC : 0 ≤ C)
    (hprice : (price:ℝ) ≤ C*(Real.log (n:ℝ))^j) :
    (price:ℝ)*(referenceBudget n (ComputableParameters.block n) parameters.pool.card
      parameters.k parameters.stages:ℝ) ≤ (C*AlignedAPSPCosts.ControllerCosts.referenceControllerConstant AlignedCertificate.R)*
        ArithmeticSlack.chargedCost (j+5) n := by
  have hfinite := computed_referenceBudget_le hn parameters hp
  have hl : 0 ≤ Real.log (n:ℝ) := (PhaseGeometry.one_le_log_nat n hn).trans' (by norm_num)
  have hprice0 : 0 ≤ C*(Real.log (n:ℝ))^j := mul_nonneg hC (pow_nonneg hl j)
  have hb := ReductionCosts.bookScan_le_chargedCost n (j+5) hn
  have hb' : (Real.log (n:ℝ))^(j+5)*
      (n:ℝ)^(3-(AsymptoticCosts.b-AsymptoticCosts.eta)) ≤ ArithmeticSlack.chargedCost (j+5) n := by
    calc
      _ ≤ (Real.log (n:ℝ))^(j+5)*((n:ℝ)^2+
          (n:ℝ)^(3-(AsymptoticCosts.b-AsymptoticCosts.eta))) :=
        mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (sq_nonneg _)) (pow_nonneg hl _)
      _ ≤ _ := hb
  calc
    _ ≤ (C*(Real.log (n:ℝ))^j)*
        (AlignedAPSPCosts.ControllerCosts.referenceControllerConstant AlignedCertificate.R*
          (Real.log (n:ℝ))^5*(n:ℝ)^(3-(AsymptoticCosts.b-AsymptoticCosts.eta))) :=
      mul_le_mul hprice hfinite (Nat.cast_nonneg _) hprice0
    _ = (C*AlignedAPSPCosts.ControllerCosts.referenceControllerConstant AlignedCertificate.R)*
        ((Real.log (n:ℝ))^(j+5)*(n:ℝ)^(3-(AsymptoticCosts.b-AsymptoticCosts.eta))) := by
      rw [pow_add]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hb' (mul_nonneg hC referenceCoefficient_nonneg)

open Asymptotics
open scoped Topology

theorem rpow_target_littleO_four :
    (fun n : ℕ => (n:ℝ)^(299294792 / 100000000 : ℝ)) =o[atTop]
      (fun n : ℕ => (n:ℝ)^(4:ℕ)) := by
  apply (isLittleO_iff_tendsto' (by
    filter_upwards [Filter.eventually_ge_atTop (1:ℕ)] with n hn
    intro hz
    exact (pow_ne_zero (4:ℕ) (show (n:ℝ)≠0 by exact_mod_cast (show n≠0 by omega)) hz).elim)).mpr
  have h := (tendsto_rpow_neg_atTop
    (show (0:ℝ)<4-(299294792 / 100000000 : ℝ) by norm_num)).comp tendsto_natCast_atTop_atTop
  apply h.congr'
  filter_upwards [Filter.eventually_ge_atTop (1:ℕ)] with n hn
  have hn0 : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  change (n:ℝ)^(-(4-(299294792 / 100000000 : ℝ))) =
    (n:ℝ)^(299294792 / 100000000 : ℝ)/(n:ℝ)^(4:ℕ)
  rw [←Real.rpow_natCast,←Real.rpow_sub hn0]
  congr 1
  ring

theorem chargedCost_eventually_le_four (C : ℝ) (k : ℕ) :
    ∀ᶠ n : ℕ in atTop, C*ArithmeticSlack.chargedCost k n ≤ (n:ℝ)^(4:ℕ) := by
  have h := ((ArithmeticSlack.chargedCostBigO k).const_mul_left C).trans_isLittleO
    rpow_target_littleO_four
  filter_upwards [h.bound (by norm_num : (0:ℝ)<1)] with n hn
  have hle : C*ArithmeticSlack.chargedCost k n ≤ |C*ArithmeticSlack.chargedCost k n| := le_abs_self _
  simpa only [Real.norm_eq_abs,one_mul,abs_of_nonneg (pow_nonneg (Nat.cast_nonneg n : (0:ℝ) ≤ n) (4:ℕ))] using hle.trans hn

namespace Finite

def capUnit (Bnd Bcap : ℕ) : ℕ :=
  3*(12*Bnd+5)+3000*(Bnd+5)^2+12*(Bnd+Bcap+3)+2

theorem finalize_finishedWork_price {n h Bnd : ℕ} {Call : Type}
    (active : ArrayCompositeAlgorithm.Flags (EndToEndAPSP.incidenceSize n h))
    (marked : ArrayCompositeAlgorithm.Flags (n*n)) (calls : List Call)
    (backendWork controllerBits controllerSites addressPrice : ℕ)
    (A B T : IntTable n) (hx : InputBits A B T Bnd)
    (htests : (finalize active marked calls backendWork controllerBits controllerSites A B T).originalSumTests ≤ n^2) :
    let out := finalize active marked calls backendWork controllerBits controllerSites A B T
    finishedWork addressPrice out+(n*n+out.denseAnswerWrites+out.finalScatterWrites) ≤ backendWork+controllerBits+addressPrice*controllerSites+
        (scanUnit Bnd+16*addressPrice+2)*n^2+
        (4*addressPrice+1)*EndToEndAPSP.incidenceSize n h := by
  let out := finalize active marked calls backendWork controllerBits controllerSites A B T
  have hprice := finalize_price active marked calls backendWork controllerBits controllerSites A B T hx
  have hbits := hprice.1
  have hcontrol := Nat.mul_le_mul_left addressPrice hprice.2
  have hbitsScan := Nat.mul_le_mul_left (scanUnit Bnd) htests
  have hcontrolScan := Nat.mul_le_mul_left (15*addressPrice) htests
  have hscatter : out.finalScatterWrites ≤ EndToEndAPSP.incidenceSize n h := by
    exact (CountedEndToEndAPSP.scatter_writes_le (EndToEndAPSP.ownerTable n h)
      (scanAnswers (finalScans A B T active)) marked (List.finRange (EndToEndAPSP.incidenceSize n h))).trans_eq
      List.length_finRange
  have hdense : out.denseAnswerWrites = n*n := rfl
  have hbackend : out.backendWork = backendWork := rfl
  change finishedWork addressPrice out+(n*n+out.denseAnswerWrites+out.finalScatterWrites) ≤ _
  unfold finishedWork
  rw [hbackend,hdense]
  nlinarith only [hbits,hcontrol,hbitsScan,hcontrolScan,hscatter]

theorem solve_finishedWork_price {n h U Bnd : ℕ} {Payload : Type}
    (hh : 0 < h) (hhn : h ≤ n) (backend : Backend n h Payload)
    (parameters : CompleteAPSP.Parameters h U) (static : Static (n:=n) parameters)
    (hs : (2*n).size ≤ parameters.stages) (addressPrice : ℕ)
    (A B T : IntTable n) (hx : InputBits A B T Bnd)
    (hmag : ∀ i k, k ∈ (EndToEndAPSP.flatInstance (h:=h) (viewTable A) (viewTable B) (viewTable T)).block i →
      ((EndToEndAPSP.flatInstance (h:=h) (viewTable A) (viewTable B) (viewTable T)).value i k).natAbs ≤ U) :
    let out := solve backend parameters static A B T
    let controller := controllerExec backend parameters static A B T
    finishedWork addressPrice out+(n*n+out.denseAnswerWrites+out.finalScatterWrites) ≤ out.backendWork+controller.bitSteps+addressPrice*controller.controlSites+
        (scanUnit Bnd+16*addressPrice+2)*n^2+
        (4*addressPrice+1)*EndToEndAPSP.incidenceSize n h := by
  exact finalize_finishedWork_price _ _ _ _ _ _ addressPrice A B T hx
    (solve_scan_budget hh hhn backend parameters static hs A B T hmag)

theorem capWork_price {n h U Bnd Bcap : ℕ}
    (hn : 1 ≤ n) (parameters : CompleteAPSP.Parameters h U) (static : Static (n:=n) parameters)
    (addressPrice : ℕ) (A B T : IntTable n) (hx : InputBits A B T Bnd) (hU : U.size ≤ Bcap) :
    (entryBound A B T).bitSteps+
      (atMost (entryBound A B T).value static.cap.cell).bitSteps+addressPrice*(12*n*n+5) ≤ (capUnit Bnd Bcap+17*addressPrice)*n^2 := by
  have hentry := entryBound_price_explicit A B T hx
  have hentrySize := entryBound_size A B T hx
  have hcapSize : (BinaryCell.view static.cap.cell).natAbs.size ≤ Bcap := by
    rw [← BinaryControllerExecution.nview_cast,Int.natAbs_natCast,static.cap_eq]
    exact hU
  have hcheck := atMost_price (Bnd+Bcap+3) (entryBound A B T).value static.cap.cell
    (hentrySize.trans (by omega)) (hcapSize.trans (by omega))
  have hn2 : 1 ≤ n^2 := one_le_pow₀ hn
  have hconstant : 3000*(Bnd+5)^2+12*(Bnd+Bcap+3)+2 ≤ (3000*(Bnd+5)^2+12*(Bnd+Bcap+3)+2)*n^2 := Nat.le_mul_of_pos_right _ hn2
  have haddr : addressPrice*(12*n*n+5) ≤ 17*addressPrice*n^2 := by
    have h : 12*n*n+5 ≤ 17*n^2 := by nlinarith only [hn2]
    exact (Nat.mul_le_mul_left addressPrice h).trans_eq (by ring)
  unfold capUnit
  nlinarith only [hentry,hcheck,hconstant,haddr]



theorem callback_price_components {n h U Bnd Bcap : ℕ} {Payload : Type}
    (hn : 1 ≤ n) (hh : 0 < h) (hhn : h ≤ n) (backend : Backend n h Payload)
    (parameters : CompleteAPSP.Parameters h U) (static : Static (n:=n) parameters)
    (hs : (2*n).size ≤ parameters.stages) (addressPrice : ℕ)
    (A B T : IntTable n) (hx : InputBits A B T Bnd) (hU : U.size ≤ Bcap)
    (hcap : CountedEndToEndAPSP.entryQueryBound (viewTable A) (viewTable B) (viewTable T) ≤ U) :
    let out := solve backend parameters static A B T
    let controller := controllerExec backend parameters static A B T
    (callback backend parameters static addressPrice A B T).work+
      (callback backend parameters static addressPrice A B T).answerWrites ≤ out.backendWork+controller.bitSteps+addressPrice*controller.controlSites+
      (scanUnit Bnd+capUnit Bnd Bcap+33*addressPrice+2)*n^2+
      (4*addressPrice+1)*EndToEndAPSP.incidenceSize n h := by
  have hb := (capTest_true parameters static A B T).mpr hcap
  have hf := solve_finishedWork_price hh hhn backend parameters static hs addressPrice A B T hx
    (fun i k _ => (CountedEndToEndAPSP.entryQueryBound_flat (viewTable A) (viewTable B) (viewTable T) i k).trans hcap)
  have hc := capWork_price hn parameters static addressPrice A B T hx hU
  simp only [callback,hb,if_true]
  dsimp only at hf
  nlinarith only [hf,hc]

def setupUnit (Wp hbits lambits Ubits : ℕ) : ℕ :=
  (8*Wp+18)+(8*hbits+16)+8*lambits+8*Ubits+19

theorem setupStatic_price {n h U Wp : ℕ} (hn : 1 ≤ n)
    (parameters : CompleteAPSP.Parameters h U) (addressPrice : ℕ)
    (hp : ∀ i, ((EndToEndAPSP.primeVector parameters.pool).get i).size ≤ Wp) :
    (setupStatic (n:=n) parameters).bitSteps+addressPrice*((setupStatic (n:=n) parameters).controlSites+1) ≤ addressPrice*setupUnit Wp h.size parameters.lam.size U.size*
        (parameters.pool.card+EndToEndAPSP.incidenceSize n h+n^2) := by
  have hcontrol := setupStatic_control_public (n:=n) parameters hp
  have hn2 : 1 ≤ n^2 := one_le_pow₀ hn
  let S := setupUnit Wp h.size parameters.lam.size U.size
  have hfirst : 8*Wp+18 ≤ S := by unfold S setupUnit; omega
  have hsecond : 8*h.size+16 ≤ S := by unfold S setupUnit; omega
  have hconstant : 8*parameters.lam.size+8*U.size+19 ≤ S := by unfold S setupUnit; omega
  have hc : (setupStatic (n:=n) parameters).controlSites+1 ≤ S*(parameters.pool.card+EndToEndAPSP.incidenceSize n h+n^2) := by
    calc
      _ ≤ parameters.pool.card*(8*Wp+18)+EndToEndAPSP.incidenceSize n h*(8*h.size+16)+
          (8*parameters.lam.size+8*U.size+19) := by omega
      _ ≤ parameters.pool.card*S+EndToEndAPSP.incidenceSize n h*S+S :=
        Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left _ hfirst) (Nat.mul_le_mul_left _ hsecond)) hconstant
      _ ≤ parameters.pool.card*S+EndToEndAPSP.incidenceSize n h*S+S*n^2 :=
        Nat.add_le_add_left (Nat.le_mul_of_pos_right _ hn2) _
      _ = _ := by ring
  rw [(setupStatic_zero (n:=n) parameters).1,Nat.zero_add]
  simpa only [S,Nat.mul_assoc] using Nat.mul_le_mul_left addressPrice hc

def overheadUnit (k Bnd Bcap addressPrice controllerUnit setupWidth : ℕ) : ℕ :=
  controllerUnit*(512*(k+1)*(k+2)+1)+scanUnit Bnd+capUnit Bnd Bcap+
    37*addressPrice+3+addressPrice*setupWidth

theorem callback_referenceBudget_price {n h U Bnd Bcap Wp : ℕ} {Payload : Type}
    (hn : 1 ≤ n) (hh : 0 < h) (hhn : h ≤ n) (backend : Backend n h Payload)
    (parameters : CompleteAPSP.Parameters h U)
    (hs : (2*n).size ≤ parameters.stages) (addressPrice controllerUnit : ℕ)
    (A B T : IntTable n) (hx : InputBits A B T Bnd) (hU : U.size ≤ Bcap)
    (hcap : CountedEndToEndAPSP.entryQueryBound (viewTable A) (viewTable B) (viewTable T) ≤ U)
    (hp : ∀ i, ((EndToEndAPSP.primeVector parameters.pool).get i).size ≤ Wp)
    (hcontroller :
      (controllerExec backend parameters (setupStatic (n:=n) parameters).value A B T).bitSteps+
      addressPrice*(controllerExec backend parameters (setupStatic (n:=n) parameters).value A B T).controlSites ≤ controllerUnit*(512*(parameters.k+1)*(parameters.k+2)*
        (parameters.stages*(parameters.k*CountedArrayComposite.batchVisits parameters.pool.card (EndToEndAPSP.incidenceSize n h)+
          CountedArrayComposite.finalVisits parameters.pool.card (EndToEndAPSP.incidenceSize n h)))+1)) :
    let static := setupStatic (n:=n) parameters
    let out := solve backend parameters static.value A B T
    (callback backend parameters static.value addressPrice A B T).work+
      (callback backend parameters static.value addressPrice A B T).answerWrites+
      static.bitSteps+addressPrice*(static.controlSites+1) ≤ out.backendWork+
      overheadUnit parameters.k Bnd Bcap addressPrice controllerUnit
        (setupUnit Wp h.size parameters.lam.size U.size)*
        referenceBudget n h parameters.pool.card parameters.k parameters.stages := by
  let static := setupStatic (n:=n) parameters
  let controller := controllerExec backend parameters static.value A B T
  let out := solve backend parameters static.value A B T
  let I := EndToEndAPSP.incidenceSize n h
  let V := parameters.stages*(parameters.k*CountedArrayComposite.batchVisits parameters.pool.card I+
    CountedArrayComposite.finalVisits parameters.pool.card I)
  let R := referenceBudget n h parameters.pool.card parameters.k parameters.stages
  let F := 512*(parameters.k+1)*(parameters.k+2)
  let S := setupUnit Wp h.size parameters.lam.size U.size
  let a := scanUnit Bnd+capUnit Bnd Bcap+33*addressPrice+2
  let b := 4*addressPrice+1
  have hn2 : 1 ≤ n^2 := one_le_pow₀ hn
  have hR1 : 1 ≤ R := by dsimp [R,referenceBudget,AlignedAPSPCosts.ControllerCosts.referenceControllerBudget]; omega
  have hRV : V ≤ R := by dsimp [V,R,referenceBudget,AlignedAPSPCosts.ControllerCosts.referenceControllerBudget,I]; omega
  have hRn : n^2 ≤ R := by dsimp [R,referenceBudget,AlignedAPSPCosts.ControllerCosts.referenceControllerBudget]; omega
  have hRI : I ≤ R := by dsimp [R,referenceBudget,AlignedAPSPCosts.ControllerCosts.referenceControllerBudget,I]; omega
  have hRsetup : parameters.pool.card+I+n^2 ≤ R := by dsimp [R,referenceBudget,AlignedAPSPCosts.ControllerCosts.referenceControllerBudget,I]; omega
  have hcontrollerR : controller.bitSteps+addressPrice*controller.controlSites ≤ controllerUnit*(F+1)*R := by
    calc
      _ ≤ controllerUnit*(F*V+1) := hcontroller
      _ ≤ controllerUnit*(F*R+R) := by
        apply Nat.mul_le_mul_left
        exact Nat.add_le_add (Nat.mul_le_mul_left _ hRV) hR1
      _ = _ := by ring
  have hcallback := callback_price_components hn hh hhn backend parameters static.value hs addressPrice A B T hx hU hcap
  have hsetup := setupStatic_price hn parameters addressPrice hp
  have hsetupR : static.bitSteps+addressPrice*(static.controlSites+1) ≤ addressPrice*S*R :=
    hsetup.trans (Nat.mul_le_mul_left _ hRsetup)
  have han : a*n^2 ≤ a*R := Nat.mul_le_mul_left _ hRn
  have hbI : b*I ≤ b*R := Nat.mul_le_mul_left _ hRI
  change (callback backend parameters static.value addressPrice A B T).work+
      (callback backend parameters static.value addressPrice A B T).answerWrites ≤ out.backendWork+controller.bitSteps+addressPrice*controller.controlSites+a*n^2+b*I at hcallback
  change _ ≤ out.backendWork+overheadUnit parameters.k Bnd Bcap addressPrice controllerUnit S*R
  calc
    _ ≤ out.backendWork+controllerUnit*(F+1)*R+a*R+b*R+addressPrice*S*R := by
      nlinarith only [hcallback,hcontrollerR,hsetupR,han,hbI]
    _ = _ := by dsimp [overheadUnit,F,a,b]; ring

theorem cap_scan_le (B C : ℕ) : scanUnit B+capUnit B C ≤ 13000*(B+C+6)^2 := by
  unfold scanUnit capUnit
  nlinarith

def overheadCoefficient (R cb ca cc cs : ℕ) : ℕ :=
  cc*(512*(R+1)*(R+2)+1)+13000*(2*cb+6)^2+37*ca+3+ca*cs

theorem overheadUnit_polynomial (k B C a c s R cb ca cc cs u : ℕ)
    (hu : 1 ≤ u) (hk:k ≤ R) (hB:B ≤ cb*u) (hC:C ≤ cb*u)
    (ha:a ≤ ca*u^2) (hc:c ≤ cc*u^2) (hs:s ≤ cs*u) :
    overheadUnit k B C a c s ≤ overheadCoefficient R cb ca cc cs*u^3 := by
  have hu2 : u^2 ≤ u^3 := calc
    u^2 ≤ u^2*u := Nat.le_mul_of_pos_right _ hu
    _ = u^3 := (pow_succ u 2).symm
  have hu3 : 1 ≤ u^3 := one_le_pow₀ hu
  have hF : 512*(k+1)*(k+2)+1 ≤ 512*(R+1)*(R+2)+1 := by gcongr
  have hcu : c*(512*(k+1)*(k+2)+1) ≤ (cc*(512*(R+1)*(R+2)+1))*u^3 := by
    calc
      _ ≤ (cc*u^2)*(512*(R+1)*(R+2)+1) := Nat.mul_le_mul hc hF
      _ = (cc*(512*(R+1)*(R+2)+1))*u^2 := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ hu2
  have hsum : B+C+6 ≤ (2*cb+6)*u := by nlinarith
  have hscan : scanUnit B+capUnit B C ≤ 13000*(2*cb+6)^2*u^3 := by
    calc
      _ ≤ 13000*(B+C+6)^2 := cap_scan_le B C
      _ ≤ 13000*((2*cb+6)*u)^2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hsum 2)
      _ = (13000*(2*cb+6)^2)*u^2 := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ hu2
  have ha3 : 37*a ≤ 37*ca*u^3 := by
    calc
      _ ≤ 37*(ca*u^2) := Nat.mul_le_mul_left _ ha
      _ = (37*ca)*u^2 := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ hu2
  have has : a*s ≤ ca*cs*u^3 := by
    calc
      _ ≤ (ca*u^2)*(cs*u) := Nat.mul_le_mul ha hs
      _ = _ := by ring
  have h3 : 3 ≤ 3*u^3 := Nat.le_mul_of_pos_right _ hu3
  unfold overheadUnit overheadCoefficient
  nlinarith only [hcu,hscan,ha3,has,h3]

theorem callback_reference_price {n h U Bnd Bcap : ℕ} {Payload : Type}
    (hn : 1 ≤ n) (hh : 0 < h) (hhn : h ≤ n) (backend : Backend n h Payload)
    (parameters : CompleteAPSP.Parameters h U) (static : Static (n:=n) parameters)
    (hs : (2*n).size ≤ parameters.stages) (addressPrice CU : ℕ)
    (A B T : IntTable n) (hx : InputBits A B T Bnd) (hU : U.size ≤ Bcap)
    (hcap : CountedEndToEndAPSP.entryQueryBound (viewTable A) (viewTable B) (viewTable T) ≤ U)
    (hcontroller : (controllerExec backend parameters static A B T).bitSteps+
      addressPrice*(controllerExec backend parameters static A B T).controlSites ≤ CU*referenceBudget n h parameters.pool.card parameters.k parameters.stages) :
    let out := solve backend parameters static A B T
    (callback backend parameters static addressPrice A B T).work+
      (callback backend parameters static addressPrice A B T).answerWrites ≤ out.backendWork+(CU+scanUnit Bnd+Finite.capUnit Bnd Bcap+37*addressPrice+3)*
        referenceBudget n h parameters.pool.card parameters.k parameters.stages := by
  let R := referenceBudget n h parameters.pool.card parameters.k parameters.stages
  let I := EndToEndAPSP.incidenceSize n h
  let a := scanUnit Bnd+Finite.capUnit Bnd Bcap+33*addressPrice+2
  let b := 4*addressPrice+1
  have hn2 : 1 ≤ n^2 := one_le_pow₀ hn
  have hRn : n^2 ≤ R := by
    dsimp [R,referenceBudget,AlignedAPSPCosts.ControllerCosts.referenceControllerBudget]
    omega
  have hRI : I ≤ R := by
    dsimp [R,I,referenceBudget,AlignedAPSPCosts.ControllerCosts.referenceControllerBudget]
    omega
  have hf := Finite.callback_price_components (n:=n) (h:=h) (U:=U) (Bnd:=Bnd) (Bcap:=Bcap) hn hh hhn backend parameters static hs addressPrice A B T hx hU hcap
  have ha : a*n^2 ≤ a*R := Nat.mul_le_mul_left _ hRn
  have hb : b*I ≤ b*R := Nat.mul_le_mul_left _ hRI
  change _ ≤ (solve backend parameters static A B T).backendWork+
    (CU+scanUnit Bnd+Finite.capUnit Bnd Bcap+37*addressPrice+3)*R
  calc
    _ ≤ (solve backend parameters static A B T).backendWork+
        (controllerExec backend parameters static A B T).bitSteps+
        addressPrice*(controllerExec backend parameters static A B T).controlSites+a*n^2+b*I := hf
    _ = (solve backend parameters static A B T).backendWork+
        ((controllerExec backend parameters static A B T).bitSteps+
        addressPrice*(controllerExec backend parameters static A B T).controlSites)+a*n^2+b*I := by ring
    _ ≤ (solve backend parameters static A B T).backendWork+CU*R+a*R+b*R :=
      Nat.add_le_add (Nat.add_le_add (Nat.add_le_add_left hcontroller _) ha) hb
    _ = _ := by dsimp [a,b]; ring

theorem controllerFormationSites_le_reference (n h P k stages : ℕ) (hn : 1 ≤ n) :
    controllerFormationSites n h P ≤ 100*referenceBudget n h P k stages := by
  have hn2 : 1 ≤ n^2 := one_le_pow₀ hn
  let I := EndToEndAPSP.incidenceSize n h
  have he : 74*I+14*P+14*n^2+20 ≤ 100*(P+6*I+9*n^2) := by omega
  have hbase : P+6*I+9*n^2 ≤ referenceBudget n h P k stages := by
    unfold referenceBudget AlignedAPSPCosts.ControllerCosts.referenceControllerBudget
    dsimp [I]
    omega
  calc
    _ = 74*I+14*P+14*n^2+20 := by unfold controllerFormationSites; dsimp [I]; ring
    _ ≤ 100*(P+6*I+9*n^2) := he
    _ ≤ _ := Nat.mul_le_mul_left 100 hbase


def controllerWidth {h U : ℕ} (n : ℕ) (parameters : CompleteAPSP.Parameters h U)
    (W pmax : ℕ) : ℕ :=
  (DenseControllerExecution.controllerCap parameters.pool.card (EndToEndAPSP.incidenceSize n h)
    (n*n) parameters.k parameters.lam parameters.stages h W pmax).size

theorem controllerExec_reference_price {n h U W pmax : ℕ} {Payload : Type}
    (hn : 1 ≤ n) (backend : Backend n h Payload)
    (parameters : CompleteAPSP.Parameters h U) (static : Static (n:=n) parameters)
    (A B T : IntTable n)
    (hO : BinaryControllerExecution.OracleCountsBound (backend.oracle A B T) h)
    (hprimes : ∀ p, (static.primes.get p).control ≤ pmax) (hpmax : 1 ≤ pmax)
    (hP : 0 < parameters.pool.card) (addressBits : ℕ) :
    let Bctrl := controllerWidth n parameters W pmax
    let addr := BackendScalarBits.addressedUnit Bctrl addressBits
    (controllerExec backend parameters static A B T).bitSteps+
      addr*(controllerExec backend parameters static A B T).controlSites ≤ (BinaryControllerExecution.executionUnit Bctrl addressBits*(512*(parameters.k+1)*(parameters.k+2)+1)+
        100*addr)*referenceBudget n h parameters.pool.card parameters.k parameters.stages := by
  let raw := BinaryControllerExecution.restartsExec (backend.oracle A B T) (EndToEndAPSP.ownerTable n h)
    static.primes static.blockSizes (Vector.replicate parameters.pool.card true) parameters.k static.lam
    parameters.stages (EndToEndAPSP.initialFlags n h) (Vector.replicate (n*n) false)
  let Bctrl := controllerWidth n parameters W pmax
  let addr := BackendScalarBits.addressedUnit Bctrl addressBits
  let EU := BinaryControllerExecution.executionUnit Bctrl addressBits
  let F := 512*(parameters.k+1)*(parameters.k+2)
  let V := parameters.stages*(parameters.k*CountedArrayComposite.batchVisits parameters.pool.card (EndToEndAPSP.incidenceSize n h)+
    CountedArrayComposite.finalVisits parameters.pool.card (EndToEndAPSP.incidenceSize n h))
  let R := referenceBudget n h parameters.pool.card parameters.k parameters.stages
  have hbase : ∀ i, BinaryControllerExecution.nview (static.blockSizes.get i) ≤ h := by
    intro i
    have he := congrArg (fun counts => counts.get i) static.blockSizes_eq
    have he' : BinaryControllerExecution.nview (static.blockSizes.get i)=(EndToEndAPSP.blockSizeTable n h).get i := by
      simpa only [BinaryControllerExecution.projectCounts,Vector.get_map] using he
    rw [he']
    simp only [EndToEndAPSP.blockSizeTable,Vector.get_ofFn]
    exact min_le_left _ _
  have hbits : raw.bitSteps ≤ BinaryControllerExecution.unit Bctrl*raw.arithSites := by
    have hp := BinaryControllerExecution.restartsExec_price_cap (W:=W) (backend.oracle A B T) hO
      (EndToEndAPSP.ownerTable n h) static.primes hprimes hpmax static.blockSizes hbase
      (Vector.replicate parameters.pool.card true) parameters.k static.lam parameters.stages
      (EndToEndAPSP.initialFlags n h) (Vector.replicate (n*n) false)
    simpa only [raw,Bctrl,controllerWidth,static.lam_eq] using hp
  have hwork := BinaryControllerExecution.executionWork_bound (B:=Bctrl) (A:=addressBits) raw hbits
  have hsite := BinaryControllerExecution.restartsExec_workSites_by_visits (backend.oracle A B T)
    (EndToEndAPSP.ownerTable n h) static.primes static.blockSizes (Vector.replicate parameters.pool.card true)
    parameters.k static.lam parameters.stages (EndToEndAPSP.initialFlags n h) (Vector.replicate (n*n) false) hP
  have hvisit : raw.value.controllerVisits ≤ V := by
    simpa only [controllerExec_value] using controllerExec_visits_bound backend parameters static A B T
  have hsiteV : BinaryControllerExecution.workSites raw ≤ F*V+1 :=
    hsite.trans (Nat.add_le_add_right (Nat.mul_le_mul_left F hvisit) 1)
  have hrawprice : raw.bitSteps+addr*raw.controlSites ≤ EU*(F*V+1) := by
    have h := Nat.mul_le_mul_left EU hsiteV
    unfold BinaryControllerExecution.executionWork at hwork
    nlinarith only [hwork,h]
  have hbitEq : (controllerExec backend parameters static A B T).bitSteps = raw.bitSteps := by
    simp only [raw,controllerExec,formOwner_value,formInitial_value,formFlags_value]
  have hcontrolEq : (controllerExec backend parameters static A B T).controlSites =
      raw.controlSites+controllerFormationSites n h parameters.pool.card := controllerExec_control backend parameters static A B T
  have hform := controllerFormationSites_le_reference n h parameters.pool.card parameters.k parameters.stages hn
  have hn2 : 1 ≤ n^2 := one_le_pow₀ hn
  have hR1 : 1 ≤ R := by dsimp [R,referenceBudget,AlignedAPSPCosts.ControllerCosts.referenceControllerBudget]; omega
  have hRV : V ≤ R := by dsimp [V,R,referenceBudget,AlignedAPSPCosts.ControllerCosts.referenceControllerBudget]; omega
  have hbound : F*V+1 ≤ (F+1)*R := by
    have h := Nat.add_le_add (Nat.mul_le_mul_left F hRV) hR1
    nlinarith only [h]
  change _ ≤ (EU*(F+1)+100*addr)*R
  rw [hbitEq,hcontrolEq]
  calc
    _ = (raw.bitSteps+addr*raw.controlSites)+addr*controllerFormationSites n h parameters.pool.card := by ring
    _ ≤ EU*(F*V+1)+addr*(100*R) :=
      Nat.add_le_add hrawprice (Nat.mul_le_mul_left addr hform)
    _ ≤ EU*((F+1)*R)+addr*(100*R) :=
      Nat.add_le_add_right (Nat.mul_le_mul_left EU hbound) _
    _ = _ := by ring

theorem controllerExec_reference_price_of_width {n h U W pmax Bctrl : ℕ} {Payload : Type}
    (hn : 1 ≤ n) (backend : Backend n h Payload)
    (parameters : CompleteAPSP.Parameters h U) (static : Static (n:=n) parameters)
    (A B T : IntTable n)
    (hO : BinaryControllerExecution.OracleCountsBound (backend.oracle A B T) h)
    (hprimes : ∀ p, (static.primes.get p).control ≤ pmax) (hpmax : 1 ≤ pmax)
    (hP : 0 < parameters.pool.card) (addressBits : ℕ)
    (hwidth : controllerWidth n parameters W pmax ≤ Bctrl) :
    let addr := BackendScalarBits.addressedUnit Bctrl addressBits
    (controllerExec backend parameters static A B T).bitSteps+
      addr*(controllerExec backend parameters static A B T).controlSites ≤ (BinaryControllerExecution.executionUnit Bctrl addressBits*(512*(parameters.k+1)*(parameters.k+2)+1)+
        100*addr)*referenceBudget n h parameters.pool.card parameters.k parameters.stages := by
  let raw := BinaryControllerExecution.restartsExec (backend.oracle A B T) (EndToEndAPSP.ownerTable n h)
    static.primes static.blockSizes (Vector.replicate parameters.pool.card true) parameters.k static.lam
    parameters.stages (EndToEndAPSP.initialFlags n h) (Vector.replicate (n*n) false)
  let addr := BackendScalarBits.addressedUnit Bctrl addressBits
  let EU := BinaryControllerExecution.executionUnit Bctrl addressBits
  let F := 512*(parameters.k+1)*(parameters.k+2)
  let V := parameters.stages*(parameters.k*CountedArrayComposite.batchVisits parameters.pool.card (EndToEndAPSP.incidenceSize n h)+
    CountedArrayComposite.finalVisits parameters.pool.card (EndToEndAPSP.incidenceSize n h))
  let R := referenceBudget n h parameters.pool.card parameters.k parameters.stages
  have hbase : ∀ i, BinaryControllerExecution.nview (static.blockSizes.get i) ≤ h := by
    intro i
    have he := congrArg (fun counts => counts.get i) static.blockSizes_eq
    have he' : BinaryControllerExecution.nview (static.blockSizes.get i)=(EndToEndAPSP.blockSizeTable n h).get i := by
      simpa only [BinaryControllerExecution.projectCounts,Vector.get_map] using he
    rw [he']
    simp only [EndToEndAPSP.blockSizeTable,Vector.get_ofFn]
    exact min_le_left _ _
  have hbits : raw.bitSteps ≤ BinaryControllerExecution.unit Bctrl*raw.arithSites := by
    have hp := BinaryControllerExecution.restartsExec_price_cap (W:=W) (backend.oracle A B T) hO
      (EndToEndAPSP.ownerTable n h) static.primes hprimes hpmax static.blockSizes hbase
      (Vector.replicate parameters.pool.card true) parameters.k static.lam parameters.stages
      (EndToEndAPSP.initialFlags n h) (Vector.replicate (n*n) false)
    have hcap : raw.bitSteps ≤ BinaryControllerExecution.unit (controllerWidth n parameters W pmax)*raw.arithSites := by
      simpa only [raw,controllerWidth,static.lam_eq] using hp
    have hmono : BinaryControllerExecution.unit (controllerWidth n parameters W pmax) ≤ BinaryControllerExecution.unit Bctrl := by
      unfold BinaryControllerExecution.unit BackendScalarBits.backendScalarUnit BackendScalarBits.scalarUnit
      exact Nat.mul_le_mul_left 8 (Nat.mul_le_mul_left 100
        (Nat.pow_le_pow_left (Nat.add_le_add_right hwidth 1) 2))
    exact hcap.trans (Nat.mul_le_mul_right _ hmono)
  have hwork := BinaryControllerExecution.executionWork_bound (B:=Bctrl) (A:=addressBits) raw hbits
  have hsite := BinaryControllerExecution.restartsExec_workSites_by_visits (backend.oracle A B T)
    (EndToEndAPSP.ownerTable n h) static.primes static.blockSizes (Vector.replicate parameters.pool.card true)
    parameters.k static.lam parameters.stages (EndToEndAPSP.initialFlags n h) (Vector.replicate (n*n) false) hP
  have hvisit : raw.value.controllerVisits ≤ V := by
    simpa only [controllerExec_value] using controllerExec_visits_bound backend parameters static A B T
  have hsiteV : BinaryControllerExecution.workSites raw ≤ F*V+1 :=
    hsite.trans (Nat.add_le_add_right (Nat.mul_le_mul_left F hvisit) 1)
  have hrawprice : raw.bitSteps+addr*raw.controlSites ≤ EU*(F*V+1) := by
    have h := Nat.mul_le_mul_left EU hsiteV
    unfold BinaryControllerExecution.executionWork at hwork
    nlinarith only [hwork,h]
  have hbitEq : (controllerExec backend parameters static A B T).bitSteps = raw.bitSteps := by
    simp only [raw,controllerExec,formOwner_value,formInitial_value,formFlags_value]
  have hcontrolEq : (controllerExec backend parameters static A B T).controlSites =
      raw.controlSites+controllerFormationSites n h parameters.pool.card := controllerExec_control backend parameters static A B T
  have hform := controllerFormationSites_le_reference n h parameters.pool.card parameters.k parameters.stages hn
  have hn2 : 1 ≤ n^2 := one_le_pow₀ hn
  have hR1 : 1 ≤ R := by dsimp [R,referenceBudget,AlignedAPSPCosts.ControllerCosts.referenceControllerBudget]; omega
  have hRV : V ≤ R := by dsimp [V,R,referenceBudget,AlignedAPSPCosts.ControllerCosts.referenceControllerBudget]; omega
  have hbound : F*V+1 ≤ (F+1)*R := by
    have h := Nat.add_le_add (Nat.mul_le_mul_left F hRV) hR1
    nlinarith only [h]
  change _ ≤ (EU*(F+1)+100*addr)*R
  rw [hbitEq,hcontrolEq]
  calc
    _ = (raw.bitSteps+addr*raw.controlSites)+addr*controllerFormationSites n h parameters.pool.card := by ring
    _ ≤ EU*(F*V+1)+addr*(100*R) :=
      Nat.add_le_add hrawprice (Nat.mul_le_mul_left addr hform)
    _ ≤ EU*((F+1)*R)+addr*(100*R) :=
      Nat.add_le_add_right (Nat.mul_le_mul_left EU hbound) _
    _ = _ := by ring


end Finite

namespace FixedPrices
noncomputable section
open BinaryControllerPolynomialBounds
attribute [local irreducible] AlignedCertificate.R AlignedCertificate.S
  controllerConstant addressConstant publicUnitConstant

/-- The fixed polynomial input promise chooses the indexed-array price;
its value does not affect any arithmetic result or branch. -/
def addressPrice (n κ degree : ℕ) : ℕ :=
  BackendScalarBits.addressedUnit (publicScalarWidth n κ 4) (publicAddressWidth n κ 4 degree)

def controllerCoefficient (κ degree : ℕ) : ℕ :=
  publicUnitConstant κ 4 degree*(512*(AlignedCertificate.R+1)*(AlignedCertificate.R+2)+101)

attribute [local irreducible] controllerCoefficient

theorem addressPrice_le_unit (n κ degree : ℕ) :
    addressPrice n κ degree ≤ BinaryControllerExecution.executionUnit
      (publicScalarWidth n κ 4) (publicAddressWidth n κ 4 degree) :=
  Nat.le_add_left _ _

theorem addressPrice_poly (n κ degree : ℕ) :
    addressPrice n κ degree ≤ publicUnitConstant κ 4 degree*(n.size+1)^2 :=
  (addressPrice_le_unit n κ degree).trans (public_units_poly n κ 4 degree)

theorem pool_positive {h U : ℕ} (parameters : CompleteAPSP.Parameters h U) :
    0 < parameters.pool.card := by
  have ht := parameters.threshold
  have hs := parameters.size
  omega

theorem computed_primes_bound {n U : ℕ}
    (parameters : CompleteAPSP.Parameters (ComputableParameters.block n) U)
    (hp : ComputableParameters.program n U=some parameters)
    (static : Static (n:=n) parameters) :
    ∀ i, (static.primes.get i).control ≤ 8*ComputableParameters.scale n := by
  intro i
  have he := congrArg (fun primes=>primes.get i) static.primes_eq
  simp only [BinaryControllerExecution.projectPrimes,Vector.get_map] at he
  change (static.primes.get i).control=(EndToEndAPSP.primeVector parameters.pool).get i at he
  rw [he]
  have hm := EndToEndAPSP.primeVector_mem parameters.pool i
  have hm' := Eq.mp (congrArg
    (fun s : Finset ℕ => (EndToEndAPSP.primeVector parameters.pool).get i ∈ s)
    (ComputableParameters.program_sound n U parameters hp).1) hm
  have hc := (Finset.mem_sdiff.mp hm').1
  rw [PrimePool.enumeratedCandidates_eq] at hc
  exact (PrimePool.candidate_upper hc).le

theorem computed_controller_price {n U κ degree : ℕ} (hn : 3 ≤ n)
    (parameters : CompleteAPSP.Parameters (ComputableParameters.block n) U)
    (hp : ComputableParameters.program n U=some parameters) (hU : U ≤ n^κ)
    (static : Static (n:=n) parameters) (A B T : IntTable n) :
    let addr := addressPrice n κ degree
    let backend := concreteBackend n (ComputableParameters.block n) (EndToEndAPSP.block_pos n) addr
    (controllerExec backend parameters static A B T).bitSteps+
      addr*(controllerExec backend parameters static A B T).controlSites ≤ (controllerCoefficient κ degree*(n.size+1)^2)*
        referenceBudget n (ComputableParameters.block n) parameters.pool.card parameters.k parameters.stages := by
  let addr := addressPrice n κ degree
  let backend := concreteBackend n (ComputableParameters.block n) (EndToEndAPSP.block_pos n) addr
  let Bctrl := publicScalarWidth n κ 4
  let Abits := publicAddressWidth n κ 4 degree
  let EU := BinaryControllerExecution.executionUnit Bctrl Abits
  have hparams := ComputableParameters.program_sound n U parameters hp
  have hk : parameters.k ≤ AlignedCertificate.R := by
    rw [hparams.2.2.2.1]
    exact (Nat.sub_le _ _).trans_eq (by unfold ComputableParameters.factorCount AlignedCertificate.R; rfl)
  have hwidth : Finite.controllerWidth n parameters (n^4) (8*ComputableParameters.scale n) ≤ Bctrl := by
    exact computed_controller_width n U (n^4) κ 4 hn parameters hp hU le_rfl
  have hpmax : 1 ≤ 8*ComputableParameters.scale n := by
    have hs := parameters.P_pos
    rw [hparams.2.1] at hs
    omega
  have hcounts : BinaryControllerExecution.OracleCountsBound (backend.oracle A B T) (ComputableParameters.block n) :=
    concreteOracle_countsBound (EndToEndAPSP.block_pos n) A B T addr
  have hfinite := Finite.controllerExec_reference_price_of_width (W:=n^4) (Bctrl:=Bctrl) (by omega) backend parameters static
    A B T hcounts (computed_primes_bound parameters hp static) hpmax (pool_positive parameters) Abits hwidth
  have heu : EU ≤ publicUnitConstant κ 4 degree*(n.size+1)^2 := public_units_poly n κ 4 degree
  have ha : addr ≤ EU := addressPrice_le_unit n κ degree
  have hF : 512*(parameters.k+1)*(parameters.k+2)+1 ≤ 512*(AlignedCertificate.R+1)*(AlignedCertificate.R+2)+1 := by gcongr
  have hcoef : EU*(512*(parameters.k+1)*(parameters.k+2)+1)+100*addr ≤ controllerCoefficient κ degree*(n.size+1)^2 := by
    calc
      _ ≤ EU*(512*(AlignedCertificate.R+1)*(AlignedCertificate.R+2)+1)+100*EU :=
        Nat.add_le_add (Nat.mul_le_mul_left _ hF) (Nat.mul_le_mul_left _ ha)
      _ = EU*(512*(AlignedCertificate.R+1)*(AlignedCertificate.R+2)+101) := by ring
      _ ≤ (publicUnitConstant κ 4 degree*(n.size+1)^2)*
          (512*(AlignedCertificate.R+1)*(AlignedCertificate.R+2)+101) := Nat.mul_le_mul_right _ heu
      _ = _ := by unfold controllerCoefficient; ring
  exact hfinite.trans (Nat.mul_le_mul_right _ hcoef)


def callbackUnit (n κ degree : ℕ) : ℕ :=
  controllerCoefficient κ degree*(n.size+1)^2+
    scanUnit (κ*n.size+1)+Finite.capUnit (κ*n.size+1) (κ*n.size+1)+
    37*addressPrice n κ degree+3

def callbackCoefficient (κ degree : ℕ) : ℕ :=
  controllerCoefficient κ degree+13000*(2*(κ+1)+6)^2+
    37*publicUnitConstant κ 4 degree+3

attribute [local irreducible] callbackCoefficient

theorem callbackUnit_poly (n κ degree : ℕ) :
    callbackUnit n κ degree ≤ callbackCoefficient κ degree*(n.size+1)^2 := by
  let u:=n.size+1
  have hu : 1 ≤ u := by dsimp [u];omega
  have hsum : (κ*n.size+1)+(κ*n.size+1)+6 ≤ (2*(κ+1)+6)*u := by dsimp [u];nlinarith
  have hscan : scanUnit (κ*n.size+1)+Finite.capUnit (κ*n.size+1) (κ*n.size+1) ≤ (13000*(2*(κ+1)+6)^2)*u^2 := by
    calc
      _ ≤ 13000*((κ*n.size+1)+(κ*n.size+1)+6)^2 := Finite.cap_scan_le _ _
      _ ≤ 13000*((2*(κ+1)+6)*u)^2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hsum 2)
      _ = _ := by ring
  have haddr := Nat.mul_le_mul_left 37 (addressPrice_poly n κ degree)
  have h3 : 3 ≤ 3*u^2 := Nat.le_mul_of_pos_right _ (one_le_pow₀ hu)
  unfold callbackUnit callbackCoefficient
  change controllerCoefficient κ degree*u^2+scanUnit (κ*n.size+1)+
    Finite.capUnit (κ*n.size+1) (κ*n.size+1)+37*addressPrice n κ degree+3 ≤ _
  calc
    _ = controllerCoefficient κ degree*u^2+
        (scanUnit (κ*n.size+1)+Finite.capUnit (κ*n.size+1) (κ*n.size+1))+
        37*addressPrice n κ degree+3 := by ring
    _ ≤ controllerCoefficient κ degree*u^2+(13000*(2*(κ+1)+6)^2)*u^2+
        (37*publicUnitConstant κ 4 degree)*u^2+3*u^2 := by
      exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add_left hscan _)
        (by simpa only [u,Nat.mul_assoc] using haddr)) h3
    _ = _ := by dsimp [u];ring

theorem computed_callback_budget {n U κ degree : ℕ} (hn : 3 ≤ n)
    (parameters : CompleteAPSP.Parameters (ComputableParameters.block n) U)
    (hp : ComputableParameters.program n U=some parameters) (hU : U ≤ n^κ)
    (static : Static (n:=n) parameters) (A B T : IntTable n)
    (hcap : CountedEndToEndAPSP.entryQueryBound (viewTable A) (viewTable B) (viewTable T) ≤ U) :
    let addr := addressPrice n κ degree
    let backend := concreteBackend n (ComputableParameters.block n) (EndToEndAPSP.block_pos n) addr
    (callback backend parameters static addr A B T).work+
      (callback backend parameters static addr A B T).answerWrites ≤ (solve backend parameters static A B T).backendWork+
        (callbackCoefficient κ degree*(n.size+1)^2)*referenceBudget n (ComputableParameters.block n)
          parameters.pool.card parameters.k parameters.stages := by
  let addr := addressPrice n κ degree
  let backend := concreteBackend n (ComputableParameters.block n) (EndToEndAPSP.block_pos n) addr
  have hparams := ComputableParameters.program_sound n U parameters hp
  have hcontroller := computed_controller_price (degree:=degree) hn parameters hp hU static A B T
  have hfinite := Finite.callback_reference_price (by omega) (EndToEndAPSP.block_pos n)
    (ComputableParameters.block_le_n n (by omega)) backend parameters static hparams.2.2.2.2.2.ge
    addr (controllerCoefficient κ degree*(n.size+1)^2) A B T
    (inputBits_of_polynomial_entry_cap A B T hU hcap) (polynomial_cap_size n U κ hU) hcap hcontroller
  exact hfinite.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ (callbackUnit_poly n κ degree)) _)


def sizeLogConstant : ℝ := 2+1/Real.log 2

theorem sizeLogConstant_nonneg : 0 ≤ sizeLogConstant := by
  exact add_nonneg (by norm_num) (one_div_nonneg.mpr (Real.log_pos (by norm_num)).le)

theorem sizeFactor_le_log (C j n : ℕ) (hn : 3 ≤ n) :
    ((C*(n.size+1)^j:ℕ):ℝ) ≤ (C:ℝ)*sizeLogConstant^j*(Real.log (n:ℝ))^j := by
  have hs := BackendCostRefinement.size_add_one_le_log n hn
  push_cast at hs
  have hs0 : (0:ℝ) ≤ n.size+1 := by positivity
  have hp := pow_le_pow_left₀ hs0 hs j
  change (n.size+1:ℝ)^j ≤ (sizeLogConstant*Real.log (n:ℝ))^j at hp
  calc
    _ = (C:ℝ)*(n.size+1:ℝ)^j := by push_cast;rfl
    _ ≤ (C:ℝ)*(sizeLogConstant*Real.log (n:ℝ))^j := mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg C)
    _ = _ := by rw [mul_pow];ring

def callbackBookCoefficient (κ degree : ℕ) : ℝ :=
  (callbackCoefficient κ degree:ℝ)*sizeLogConstant^2*
    AlignedAPSPCosts.ControllerCosts.referenceControllerConstant AlignedCertificate.R

theorem callbackBookCoefficient_nonneg (κ degree : ℕ) : 0 ≤ callbackBookCoefficient κ degree :=
  mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)) referenceCoefficient_nonneg

theorem computed_callback_charged_overhead {n U κ degree : ℕ} (hn : 3 ≤ n)
    (parameters : CompleteAPSP.Parameters (ComputableParameters.block n) U)
    (hp : ComputableParameters.program n U=some parameters) (hU : U ≤ n^κ)
    (static : Static (n:=n) parameters) (A B T : IntTable n)
    (hcap : CountedEndToEndAPSP.entryQueryBound (viewTable A) (viewTable B) (viewTable T) ≤ U) :
    let addr:=addressPrice n κ degree
    let backend:=concreteBackend n (ComputableParameters.block n) (EndToEndAPSP.block_pos n) addr
    ((callback backend parameters static addr A B T).work:ℝ)+
      (callback backend parameters static addr A B T).answerWrites ≤ ((solve backend parameters static A B T).backendWork:ℝ)+
        callbackBookCoefficient κ degree*ArithmeticSlack.chargedCost 7 n := by
  let addr:=addressPrice n κ degree
  let backend:=concreteBackend n (ComputableParameters.block n) (EndToEndAPSP.block_pos n) addr
  have hf:=computed_callback_budget (degree:=degree) hn parameters hp hU static A B T hcap
  have hfR : ((callback backend parameters static addr A B T).work:ℝ)+
      (callback backend parameters static addr A B T).answerWrites ≤ ((solve backend parameters static A B T).backendWork:ℝ)+
      ((callbackCoefficient κ degree*(n.size+1)^2:ℕ):ℝ)*
        (referenceBudget n (ComputableParameters.block n) parameters.pool.card parameters.k parameters.stages:ℝ) := by
    exact_mod_cast hf
  have hprice:=sizeFactor_le_log (callbackCoefficient κ degree) 2 n hn
  have hcost:=priced_referenceBudget_le_chargedCost hn parameters hp
    (callbackCoefficient κ degree*(n.size+1)^2)
    ((callbackCoefficient κ degree:ℝ)*sizeLogConstant^2) 2
    (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)) hprice
  have hcost' : ((callbackCoefficient κ degree*(n.size+1)^2:ℕ):ℝ)*
      (referenceBudget n (ComputableParameters.block n) parameters.pool.card parameters.k parameters.stages:ℝ) ≤
      callbackBookCoefficient κ degree*ArithmeticSlack.chargedCost 7 n := hcost
  exact hfR.trans (add_le_add le_rfl hcost')

end
end FixedPrices

namespace PreparedSetup
noncomputable section
open BinaryControllerPolynomialBounds
attribute [local irreducible] AlignedCertificate.R AlignedCertificate.S
  controllerConstant addressConstant publicUnitConstant

theorem fromPrimes_setupBits_zero {n h U : ℕ} {Payload : Type}
    (backend : Backend n h Payload) (parameters : CompleteAPSP.Parameters h U)
    (labels : Vector ℕ parameters.pool.card)
    (hlabels : labels = EndToEndAPSP.primeVector parameters.pool) (addr : ℕ) :
    (prepareOracleFromPrimes backend parameters labels hlabels addr).setupBits = 0 := by
  simp only [prepareOracleFromPrimes, setupStaticFromPrimes,
    (prepareStaticPrimes_zero _).1, (prepareStaticCounts_zero _).1,
    (staticFromPublic_zero _).1, zero_add]

theorem computed_label_sizes {n U : ℕ} (hn : 3 ≤ n)
    (parameters : CompleteAPSP.Parameters (ComputableParameters.block n) U)
    (hp : ComputableParameters.program n U = some parameters)
    (labels : Vector ℕ parameters.pool.card)
    (hlabels : labels = EndToEndAPSP.primeVector parameters.pool) :
    ∀ i, (labels.get i).size ≤ 14 * n.size + 1 := by
  have hs : 1 ≤ n.size := Nat.size_pos.mpr (by omega)
  have hpool := (ComputableParameters.program_sound n U parameters hp).1
  intro i
  rw [hlabels]
  have hm := EndToEndAPSP.primeVector_mem parameters.pool i
  have hm' := Eq.mp (congrArg
    (fun s : Finset ℕ => (EndToEndAPSP.primeVector parameters.pool).get i ∈ s) hpool) hm
  have hc := ComputedPhaseGeometry.computedPool_subset_candidates n hm'
  have hbound : (EndToEndAPSP.primeVector parameters.pool).get i ≤ 2^(14*n.size) :=
    (PrimePool.candidate_upper hc).le.trans (eightScale_pow n hs)
  exact (Nat.size_le_size hbound).trans_eq Nat.size_pow

theorem fromPrimes_setupControl_bound {n U κ : ℕ} {Payload : Type} (hn : 3 ≤ n)
    (parameters : CompleteAPSP.Parameters (ComputableParameters.block n) U)
    (hp : ComputableParameters.program n U = some parameters) (hU : U ≤ n^κ)
    (backend : Backend n (ComputableParameters.block n) Payload)
    (labels : Vector ℕ parameters.pool.card)
    (hlabels : labels = EndToEndAPSP.primeVector parameters.pool) (addr : ℕ) :
    (prepareOracleFromPrimes backend parameters labels hlabels addr).setupControl ≤
      (16*κ+500) * (n.size+1) *
        referenceBudget n (ComputableParameters.block n) parameters.pool.card
          parameters.k parameters.stages := by
  let P := parameters.pool.card
  let I := EndToEndAPSP.incidenceSize n (ComputableParameters.block n)
  let L := n.size + 1
  let C := 16*κ+500
  let R := referenceBudget n (ComputableParameters.block n) P parameters.k parameters.stages
  have hlabelsBound := computed_label_sizes hn parameters hp labels hlabels
  have hstatic := setupStaticFromPrimes_control_public (n:=n) parameters labels hlabels hlabelsBound
  have hhsize : (ComputableParameters.block n).size ≤ n.size :=
    Nat.size_le_size (ComputableParameters.block_le_n n (by omega))
  have hUsize : U.size ≤ κ*n.size+1 := input_size_bound n U κ hU
  have hlam : parameters.lam = U.size :=
    (ComputableParameters.program_sound n U parameters hp).2.2.1
  have hlamsize : parameters.lam.size ≤ κ*n.size+1 := by
    rw [hlam]
    exact (ParameterExecution.size_le_self U.size).trans hUsize
  have hPcoef : 8*(14*n.size+1)+19 ≤ C*L := by dsimp only [C,L]; nlinarith
  have hIcoef : 8*(ComputableParameters.block n).size+61 ≤ C*L := by
    dsimp only [C,L]
    nlinarith
  have hrest : 8*parameters.lam.size+8*U.size+21 ≤ C*L := by
    dsimp only [C,L]
    nlinarith
  have hR : P+I+1 ≤ R := by
    have hn2 : 1 ≤ n^2 := by nlinarith only [hn]
    dsimp only [R, referenceBudget, AlignedAPSPCosts.ControllerCosts.referenceControllerBudget, I]
    omega
  have hfull : (prepareOracleFromPrimes backend parameters labels hlabels addr).setupControl ≤
      P*(8*(14*n.size+1)+19)+I*(8*(ComputableParameters.block n).size+61)+
        (8*parameters.lam.size+8*U.size+21) := by
    change (setupStaticFromPrimes (n:=n) parameters labels hlabels).controlSites+P+1 ≤ _
    calc
      _ ≤ (P*(8*(14*n.size+1)+18)+I*(8*(ComputableParameters.block n).size+61)+
          8*parameters.lam.size+8*U.size+20)+P+1 :=
        Nat.add_le_add_right (Nat.add_le_add_right hstatic P) 1
      _ = _ := by ring
  calc
    _ ≤ P*(8*(14*n.size+1)+19)+I*(8*(ComputableParameters.block n).size+61)+
        (8*parameters.lam.size+8*U.size+21) := hfull
    _ ≤ P*(C*L)+I*(C*L)+C*L :=
      Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left P hPcoef)
        (Nat.mul_le_mul_left I hIcoef)) hrest
    _ = C*L*(P+I+1) := by ring
    _ ≤ C*L*R := Nat.mul_le_mul_left _ hR

theorem fromPrimes_setup_price {n U κ degree : ℕ} {Payload : Type} (hn : 3 ≤ n)
    (parameters : CompleteAPSP.Parameters (ComputableParameters.block n) U)
    (hp : ComputableParameters.program n U = some parameters) (hU : U ≤ n^κ)
    (backend : Backend n (ComputableParameters.block n) Payload)
    (labels : Vector ℕ parameters.pool.card)
    (hlabels : labels = EndToEndAPSP.primeVector parameters.pool) :
    let prepared := prepareOracleFromPrimes backend parameters labels hlabels (FixedPrices.addressPrice n κ degree)
    prepared.setupBits + FixedPrices.addressPrice n κ degree * prepared.setupControl ≤
      (publicUnitConstant κ 4 degree * (16*κ+500)) * (n.size+1)^3 *
        referenceBudget n (ComputableParameters.block n) parameters.pool.card
          parameters.k parameters.stages := by
  dsimp only
  rw [fromPrimes_setupBits_zero, zero_add]
  have haddr : FixedPrices.addressPrice n κ degree ≤ publicUnitConstant κ 4 degree*(n.size+1)^2 := by
    apply (show FixedPrices.addressPrice n κ degree ≤ BinaryControllerExecution.executionUnit
      (publicScalarWidth n κ 4) (publicAddressWidth n κ 4 degree) from Nat.le_add_left _ _).trans
    exact public_units_poly n κ 4 degree
  have hc := fromPrimes_setupControl_bound hn parameters hp hU backend labels hlabels
    (FixedPrices.addressPrice n κ degree)
  apply (Nat.mul_le_mul haddr hc).trans_eq
  ring

theorem concrete_setupBits_zero {n h U : ℕ} (hh : 0<h)
    (parameters : CompleteAPSP.Parameters h U) (labels : Vector ℕ parameters.pool.card)
    (hlabels : labels=EndToEndAPSP.primeVector parameters.pool) (addr : ℕ) :
    (prepareConcreteFromPrimes (n:=n) hh parameters labels hlabels addr).setupBits=0 :=
  fromPrimes_setupBits_zero _ parameters labels hlabels addr

theorem concrete_setup_price {n U κ degree : ℕ} (hn : 3 ≤ n)
    (parameters : CompleteAPSP.Parameters (ComputableParameters.block n) U)
    (hp : ComputableParameters.program n U = some parameters) (hU : U ≤ n^κ)
    (labels : Vector ℕ parameters.pool.card)
    (hlabels : labels = EndToEndAPSP.primeVector parameters.pool) :
    let prepared := prepareConcreteFromPrimes (n:=n) (ComputedPhaseGeometry.block_pos n)
      parameters labels hlabels (FixedPrices.addressPrice n κ degree)
    prepared.setupBits + FixedPrices.addressPrice n κ degree * prepared.setupControl ≤
      (publicUnitConstant κ 4 degree * (16*κ+500)) * (n.size+1)^3 *
        referenceBudget n (ComputableParameters.block n) parameters.pool.card
          parameters.k parameters.stages :=
  fromPrimes_setup_price hn parameters hp hU _ labels hlabels



def setupCoefficient (κ degree : ℕ) : ℕ := publicUnitConstant κ 4 degree*(16*κ+500)
def setupBookCoefficient (κ degree : ℕ) : ℝ :=
  (setupCoefficient κ degree:ℝ)*FixedPrices.sizeLogConstant^3*
    AlignedAPSPCosts.ControllerCosts.referenceControllerConstant AlignedCertificate.R

theorem setupBookCoefficient_nonneg (κ degree : ℕ) : 0 ≤ setupBookCoefficient κ degree :=
  mul_nonneg (mul_nonneg (Nat.cast_nonneg _)
    (pow_nonneg FixedPrices.sizeLogConstant_nonneg 3)) referenceCoefficient_nonneg

theorem concrete_setup_charged {n U κ degree : ℕ} (hn : 3 ≤ n)
    (parameters : CompleteAPSP.Parameters (ComputableParameters.block n) U)
    (hp : ComputableParameters.program n U=some parameters) (hU : U ≤ n^κ)
    (labels : Vector ℕ parameters.pool.card)
    (hlabels : labels=EndToEndAPSP.primeVector parameters.pool) :
    let addr:=FixedPrices.addressPrice n κ degree
    let prepared:=prepareConcreteFromPrimes (n:=n) (ComputedPhaseGeometry.block_pos n)
      parameters labels hlabels addr
    (prepared.setupBits:ℝ)+(addr:ℝ)*prepared.setupControl ≤
      setupBookCoefficient κ degree*ArithmeticSlack.chargedCost 8 n := by
  let addr:=FixedPrices.addressPrice n κ degree
  let prepared:=prepareConcreteFromPrimes (n:=n) (ComputedPhaseGeometry.block_pos n)
    parameters labels hlabels addr
  have hf:=concrete_setup_price (degree:=degree) hn parameters hp hU labels hlabels
  have hfR : (prepared.setupBits:ℝ)+(addr:ℝ)*prepared.setupControl ≤
      ((setupCoefficient κ degree*(n.size+1)^3:ℕ):ℝ)*
        (referenceBudget n (ComputableParameters.block n) parameters.pool.card parameters.k parameters.stages:ℝ) := by
    exact_mod_cast hf
  have hpv:=priced_referenceBudget_le_chargedCost hn parameters hp
    (setupCoefficient κ degree*(n.size+1)^3)
    ((setupCoefficient κ degree:ℝ)*FixedPrices.sizeLogConstant^3) 3
    (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg FixedPrices.sizeLogConstant_nonneg 3))
    (FixedPrices.sizeFactor_le_log (setupCoefficient κ degree) 3 n hn)
  exact hfR.trans hpv

end
end PreparedSetup

namespace PlanGeometry
noncomputable section
attribute [local irreducible] AlignedCertificate.R AlignedCertificate.S

theorem physicalFold_eq {R n r : ℕ} (call : ComputedPhaseGeometry.Call R n) (S : ℕ)
    (f : CompactBlocks.PhysicalFactorization r) (hfold : f.folded = call.folded S) :
    FoldedBackendExecution.physicalFold f = PhaseGeometry.physicalFold call S := by
  change 3*f.folded = 3*call.folded S
  rw [hfold]

theorem middleExponent_eq {R n r : ℕ} (call : ComputedPhaseGeometry.Call R n) (S : ℕ)
    (f : CompactBlocks.PhysicalFactorization r) (hfold : f.folded = call.folded S) :
    FoldedBackendExecution.middleExponent (ComputableParameters.block n)
      (FoldedBackendExecution.physicalFold f) = ComputedPhaseGeometry.innerPower n call S := by
  change Nat.clog 4 (ComputableParameters.block n*(3*f.folded)) =
    Nat.clog 4 (ComputableParameters.block n*(3*call.folded S))
  rw [hfold]

theorem outerSize_eq {R n r : ℕ} (call : ComputedPhaseGeometry.Call R n) (S : ℕ)
    (f : CompactBlocks.PhysicalFactorization r) (hfold : f.folded = call.folded S) :
    FoldedBackendExecution.outerSize n (FoldedBackendExecution.physicalFold f) =
      PhaseGeometry.outerSize call S n := by
  change n*FoldedCounts.foldWidth (3*f.folded) = n*FoldedCounts.foldWidth (3*call.folded S)
  rw [hfold]

theorem preparePlan_m_eq {R n r : ℕ} (call : ComputedPhaseGeometry.Call R n) (S : ℕ)
    (f : CompactBlocks.PhysicalFactorization r) (hfold : f.folded = call.folded S) :
    (BinaryTriangleSetupCosts.preparePlan n (ComputableParameters.block n) f).value.m =
      ComputedPhaseGeometry.innerPower n call S := by
  rw [BinaryTriangleSetupCosts.preparePlan_m, middleExponent_eq call S f hfold]

theorem preparePlan_L_eq {R n r : ℕ} (call : ComputedPhaseGeometry.Call R n) (S : ℕ)
    (f : CompactBlocks.PhysicalFactorization r) (hfold : f.folded = call.folded S) :
    (BinaryTriangleSetupCosts.preparePlan n (ComputableParameters.block n) f).value.L =
      ComputableParameters.ordinaryLength (ComputedPhaseGeometry.innerPower n call S) := by
  rw [BinaryTriangleSetupCosts.preparePlan_L, middleExponent_eq call S f hfold]

theorem preparePlan_t_eq {R n r : ℕ} (call : ComputedPhaseGeometry.Call R n) (S : ℕ)
    (f : CompactBlocks.PhysicalFactorization r) (hfold : f.folded = call.folded S) :
    (BinaryTriangleSetupCosts.preparePlan n (ComputableParameters.block n) f).value.t =
      ComputableParameters.channelLength (ComputedPhaseGeometry.innerPower n call S) := by
  rw [BinaryTriangleSetupCosts.preparePlan_t, middleExponent_eq call S f hfold]

theorem preparePlan_N_eq {R n r : ℕ} (call : ComputedPhaseGeometry.Call R n) (S : ℕ)
    (f : CompactBlocks.PhysicalFactorization r) (hfold : f.folded = call.folded S) :
    (BinaryTriangleSetupCosts.preparePlan n (ComputableParameters.block n) f).value.N =
      PhaseGeometry.outerSize call S n := by
  exact ((BinaryTriangleSetupCosts.preparePlan n (ComputableParameters.block n) f).value.N_eq).trans
    (outerSize_eq call S f hfold)

theorem preparePlan_D_eq {R n r : ℕ} (call : ComputedPhaseGeometry.Call R n) (S : ℕ)
    (f : CompactBlocks.PhysicalFactorization r) (hfold : f.folded = call.folded S) :
    (BinaryTriangleSetupCosts.preparePlan n (ComputableParameters.block n) f).value.D =
      ComputedPhaseGeometry.innerDimension n call S := by
  rw [(BinaryTriangleSetupCosts.preparePlan n (ComputableParameters.block n) f).value.D_eq,
    FoldedBackendExecution.middleSize_eq, middleExponent_eq call S f hfold,
    ComputedPhaseGeometry.innerDimension_eq_power]

/-- Small straight-line width identity, independent of any phase constants. -/
theorem runtimeLowWidth_eq_geometryWidth (L m q : ℕ) :
    BinaryTriangleSetupCosts.runtimeLowWidth L m q.size =
      BinaryGeometryWidth.geometryWidth L m q := by
  simp only [BinaryTriangleSetupCosts.runtimeLowWidth, BinaryGeometryWidth.geometryWidth, pow_two]

theorem preparePlan_lowWidth_geometry (n h : ℕ) {r : ℕ}
    (f : CompactBlocks.PhysicalFactorization r) :
    (BinaryTriangleSetupCosts.preparePlan n h f).value.lowWidth =
      BinaryGeometryWidth.geometryWidth (BinaryTriangleSetupCosts.preparePlan n h f).value.L
        (BinaryTriangleSetupCosts.preparePlan n h f).value.m f.cyclic := by
  rw [BinaryTriangleSetupCosts.preparePlan_lowWidth, runtimeLowWidth_eq_geometryWidth]

theorem preparePlan_lowWidth_eq {R n r : ℕ} (call : ComputedPhaseGeometry.Call R n) (S : ℕ)
    (f : CompactBlocks.PhysicalFactorization r)
    (hfold : f.folded = call.folded S) (hcyclic : f.cyclic = call.cyclic S) :
    (BinaryTriangleSetupCosts.preparePlan n (ComputableParameters.block n) f).value.lowWidth =
      BinaryGeometryWidth.geometryWidth
        (ComputableParameters.ordinaryLength (ComputedPhaseGeometry.innerPower n call S))
        (ComputedPhaseGeometry.innerPower n call S) (call.cyclic S) := by
  rw [preparePlan_lowWidth_geometry, preparePlan_L_eq call S f hfold,
    preparePlan_m_eq call S f hfold, hcyclic]

/-- Reusable single decomposition for the real plan passed to prepareBlock. -/
theorem preparePlan_dimensions {R n r : ℕ} (call : ComputedPhaseGeometry.Call R n) (S : ℕ)
    (f : CompactBlocks.PhysicalFactorization r)
    (hfold : f.folded = call.folded S) (hcyclic : f.cyclic = call.cyclic S) :
    let p := (BinaryTriangleSetupCosts.preparePlan n (ComputableParameters.block n) f).value
    let m := ComputedPhaseGeometry.innerPower n call S
    p.m = m ∧ p.L = ComputableParameters.ordinaryLength m ∧
      p.t = ComputableParameters.channelLength m ∧ p.N = PhaseGeometry.outerSize call S n ∧
      p.D = ComputedPhaseGeometry.innerDimension n call S ∧
      p.lowWidth = BinaryGeometryWidth.geometryWidth (ComputableParameters.ordinaryLength m)
        m (call.cyclic S) := by
  exact ⟨preparePlan_m_eq call S f hfold, preparePlan_L_eq call S f hfold,
    preparePlan_t_eq call S f hfold, preparePlan_N_eq call S f hfold,
    preparePlan_D_eq call S f hfold, preparePlan_lowWidth_eq call S f hfold hcyclic⟩

end
end PlanGeometry

namespace BlockCosts
noncomputable section
open scoped BigOperators
open BinaryFoldedFactory
open BackendCostRefinement ThinProductCosts
open BinaryBackendCosts
set_option maxRecDepth 10000
set_option maxHeartbeats 500000
attribute [local irreducible] AlignedCertificate.R AlignedCertificate.S
  AdaptiveBitBounds.computedIndexConstant AdaptiveBitBounds.computedLengthConstant
  AdaptiveBitBounds.computedCyclicConstant BinaryBackendCosts.computedPreparationConstant BinaryBackendCosts.computedBatchConstant

/-- A proof-side view of the exact stored target requests, in their original
window order, with only the factory's public outer-index cast applied. -/
def retainedRequests {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : Plan (n:=n) (h:=h) f) (input : BinaryFoldedFormation.Inputs n) :
    Vector (Fin p.N × Fin p.N × Fin f.cyclic) (FoldedBackendExecution.windowQuerySize n) :=
  Vector.ofFn (fun i =>
    let request := (prepareRetained f p input).targets.requests.value.get i
    (Fin.cast p.N_eq.symm request.row, Fin.cast p.N_eq.symm request.column, request.coefficient))

/-- This equality reads the same prepared block and retained query vector;
it introduces no execution of a source, preparation, query, or target loop. -/
theorem retained_block_joint_counter {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : Plan (n:=n) (h:=h) f) (input : BinaryFoldedFormation.Inputs n)
    (b : Fin (CompactBlocks.blockCount n h)) :
    ((prepareRetained f p input).blocks.value.get b).prepared.bitSteps+
      (∑ i : Fin (FoldedBackendExecution.windowQuerySize n),
        (((prepareRetained f p input).blockQueries b).get i).result.operations) =
    let block := prepareBlock f p b input
    block.prepared.bitSteps+
      ∑ i : Fin (FoldedBackendExecution.windowQuerySize n),
        (BinaryBackendExecution.queryGlobalExecution
          (ThinMatrixBackend.tileWidth_pos p.L p.m p.m_le_L) block.prepared
          ((retainedRequests f p input).get i).1 ((retainedRequests f p input).get i).2.1
          ((retainedRequests f p input).get i).2.2).result.operations := by
  simp only [prepareRetained_block_get,prepareRetained_blockQueries,retainedRequests,Vector.get_ofFn]

/-- Direct specialization to one actually retained block. Original coefficient
caps are the factory's unconditional zero/one source theorem. -/
theorem computed_retained_preparation_price {n r : ℕ} (hn : 3 ≤ n)
    (call : ComputedPhaseGeometry.Call AlignedCertificate.R n)
    (f : CompactBlocks.PhysicalFactorization r)
    (hfold : f.folded=call.folded AlignedCertificate.S)
    (hcyclic : f.cyclic=call.cyclic AlignedCertificate.S)
    (input : BinaryFoldedFormation.Inputs n)
    (b : Fin (CompactBlocks.blockCount n (ComputableParameters.block n))) :
    let p := (BinaryTriangleSetupCosts.preparePlan n (ComputableParameters.block n) f).value
    let m := ComputedPhaseGeometry.innerPower n call AlignedCertificate.S
    let L := ComputableParameters.ordinaryLength m
    let t := ComputableParameters.channelLength m
    let q := call.cyclic AlignedCertificate.S
    let N := PhaseGeometry.outerSize call AlignedCertificate.S n
    ((prepareRetained f p input).blocks.value.get b).prepared.bitSteps ≤
      computedPreparationConstant*(n.size+1)^12*globalPreparationBudget N L m t q (fullBudget L m q) := by
  let p := (BinaryTriangleSetupCosts.preparePlan n (ComputableParameters.block n) f).value
  let m := ComputedPhaseGeometry.innerPower n call AlignedCertificate.S
  let L := ComputableParameters.ordinaryLength m
  let t := ComputableParameters.channelLength m
  let q := call.cyclic AlignedCertificate.S
  let N := PhaseGeometry.outerSize call AlignedCertificate.S n
  have hd := PlanGeometry.preparePlan_dimensions call AlignedCertificate.S f hfold hcyclic
  change p.m=m ∧ p.L=L ∧ p.t=t ∧ p.N=N ∧
    p.D=ComputedPhaseGeometry.innerDimension n call AlignedCertificate.S ∧
    p.lowWidth=BinaryGeometryWidth.geometryWidth L m q at hd
  obtain ⟨hpm,hpL,hpt,hpN,_hpD,_hpW⟩ := hd
  let block := prepareBlock f p b input
  let left := p.castLeft block.sources.value.left
  let right := p.castRight block.sources.value.right
  have hl : ∀ i r, (BinaryCell.view ((left.get i).get r)).natAbs ≤ 1 := by
    simpa only [left,BinaryBackendExecution.viewLeft_get] using sources_left_abs f p b input
  have hr : ∀ i r, (BinaryCell.view ((right.get i).get r)).natAbs ≤ 1 := by
    simpa only [right,BinaryBackendExecution.viewRight_get] using sources_right_abs f p b input
  have hL : p.L ≤ AdaptiveBitBounds.computedLengthConstant*n.size := by
    rw [hpL]
    dsimp only [L]
    rw [ComputableParameters.ordinaryLength_eq]
    exact AdaptiveBitBounds.computed_roundedLength_le_size n hn call
  have hm : p.m ≤ AdaptiveBitBounds.computedIndexConstant*n.size := by
    rw [hpm]
    exact AdaptiveBitBounds.computed_innerPower_le_size n hn call
  have hq : f.cyclic ≤ 2^(AdaptiveBitBounds.computedCyclicConstant*n.size) := by
    rw [hcyclic]
    exact AdaptiveBitBounds.computed_cyclic_le_pow_size n hn call
  have hc := prepareGlobal_geometry_price (t:=p.t) left right hl hr n
    AdaptiveBitBounds.computedLengthConstant AdaptiveBitBounds.computedIndexConstant
    AdaptiveBitBounds.computedCyclicConstant (by omega) p.m_le_L hL hm hq p.t_le
  have hwidth : p.lowWidth=BinaryGeometryWidth.geometryWidth p.L p.m f.cyclic :=
    PlanGeometry.preparePlan_lowWidth_geometry n (ComputableParameters.block n) f
  have heq : ((prepareRetained f p input).blocks.value.get b).prepared.bitSteps =
      (BinaryBackendExecution.prepareGlobal (L:=p.L) (m:=p.m) (t:=p.t)
        p.lowWidth 1 left right).bitSteps := by
    rw [prepareRetained_block_get]
    rfl
  have hp : ((prepareRetained f p input).blocks.value.get b).prepared.bitSteps ≤
      computedPreparationConstant*(n.size+1)^12*
        globalPreparationBudget p.N p.L p.m p.t f.cyclic (fullBudget p.L p.m f.cyclic) := by
    rw [heq,hwidth]
    simpa only [computedPreparationConstant] using hc
  simpa only [hpN,hpL,hpm,hpt,hcyclic] using hp

/-- Per-query resource specialization for the exact retained block query.
The factory's source arrays supply every LOW/HIGH magnitude premise. -/
theorem retained_query_resource_price {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : Plan (n:=n) (h:=h) f) (input : BinaryFoldedFormation.Inputs n)
    (b : Fin (CompactBlocks.blockCount n h)) (i : Fin (FoldedBackendExecution.windowQuerySize n))
    (B : ℕ) :
    (((prepareRetained f p input).blockQueries b).get i).result.operations ≤
      BinaryQueryCosts.queryFactor p.L p.m p.t f.cyclic 1 (CoefficientBounds.uniformBudget p.L p.m p.t f.cyclic 1)*
        globalQueryRefinement p.N p.L p.m B*
        (lowCoefficientCost p.m p.t f.cyclic (2*p.m+1)+highCoefficientReads p.m p.t) := by
  let block := prepareBlock f p b input
  let left := p.castLeft block.sources.value.left
  let right := p.castRight block.sources.value.right
  let request := (prepareRetained f p input).targets.requests.value.get i
  have hl : ∀ i r, (BinaryCell.view ((left.get i).get r)).natAbs ≤ 1 := by
    simpa only [left,BinaryBackendExecution.viewLeft_get] using sources_left_abs f p b input
  have hr : ∀ i r, (BinaryCell.view ((right.get i).get r)).natAbs ≤ 1 := by
    simpa only [right,BinaryBackendExecution.viewRight_get] using sources_right_abs f p b input
  have hc := BinaryQueryCosts.queryGlobal_cost_original_one B p.lowWidth
    (BinaryBackendExecution.prepareShapeRuntime p.L p.m) left right hl hr p.m_le_L p.t_le
    (Fin.cast p.N_eq.symm request.row) (Fin.cast p.N_eq.symm request.column) request.coefficient
  rw [prepareRetained_blockQueries]
  dsimp only
  rw [prepareRetained_block_get]
  exact hc

#print axioms PlanGeometry.preparePlan_dimensions
#print axioms retained_block_joint_counter
#print axioms computed_retained_preparation_price
#print axioms retained_query_resource_price


/-- Computed-price specialization of the same retained preparation and
all its stored signed-window query results, charged jointly once. -/
theorem computed_retained_joint_price {n r : ℕ} (hn : 3 ≤ n)
    (call : ComputedPhaseGeometry.Call AlignedCertificate.R n)
    (f : CompactBlocks.PhysicalFactorization r)
    (hfold : f.folded=call.folded AlignedCertificate.S)
    (hcyclic : f.cyclic=call.cyclic AlignedCertificate.S)
    (input : BinaryFoldedFormation.Inputs n)
    (b : Fin (CompactBlocks.blockCount n (ComputableParameters.block n))) :
    let p := (BinaryTriangleSetupCosts.preparePlan n (ComputableParameters.block n) f).value
    let payload := prepareRetained f p input
    let m := ComputedPhaseGeometry.innerPower n call AlignedCertificate.S
    let L := ComputableParameters.ordinaryLength m
    let t := ComputableParameters.channelLength m
    let q := call.cyclic AlignedCertificate.S
    let N := PhaseGeometry.outerSize call AlignedCertificate.S n
    let B := BackendNumeratorBounds.numeratorBitBudget L m q 1
    (payload.blocks.value.get b).prepared.bitSteps+
      (∑ i : Fin (FoldedBackendExecution.windowQuerySize n),
        ((payload.blockQueries b).get i).result.operations) ≤
      computedBatchConstant*(n.size+1)^12*
        (globalPreparationBudget N L m t q (fullBudget L m q)+
          (3*n^2)*globalQueryRefinement N L m B*
            (lowCoefficientCost m t q (2*m+1)+highCoefficientReads m t)) := by
  let p := (BinaryTriangleSetupCosts.preparePlan n (ComputableParameters.block n) f).value
  let payload := prepareRetained f p input
  let m := ComputedPhaseGeometry.innerPower n call AlignedCertificate.S
  let L := ComputableParameters.ordinaryLength m
  let t := ComputableParameters.channelLength m
  let q := call.cyclic AlignedCertificate.S
  let N := PhaseGeometry.outerSize call AlignedCertificate.S n
  have hd := PlanGeometry.preparePlan_dimensions call AlignedCertificate.S f hfold hcyclic
  change p.m=m ∧ p.L=L ∧ p.t=t ∧ p.N=N ∧
    p.D=ComputedPhaseGeometry.innerDimension n call AlignedCertificate.S ∧
    p.lowWidth=BinaryGeometryWidth.geometryWidth L m q at hd
  obtain ⟨hpm,hpL,hpt,hpN,_hpD,_hpW⟩ := hd
  let block := prepareBlock f p b input
  let left := p.castLeft block.sources.value.left
  let right := p.castRight block.sources.value.right
  have hl : ∀ i r, (BinaryCell.view ((left.get i).get r)).natAbs ≤ 1 := by
    simpa only [left,BinaryBackendExecution.viewLeft_get] using sources_left_abs f p b input
  have hr : ∀ i r, (BinaryCell.view ((right.get i).get r)).natAbs ≤ 1 := by
    simpa only [right,BinaryBackendExecution.viewRight_get] using sources_right_abs f p b input
  have hL : p.L ≤ AdaptiveBitBounds.computedLengthConstant*n.size := by
    rw [hpL]
    dsimp only [L]
    rw [ComputableParameters.ordinaryLength_eq]
    exact AdaptiveBitBounds.computed_roundedLength_le_size n hn call
  have hm : p.m ≤ AdaptiveBitBounds.computedIndexConstant*n.size := by
    rw [hpm]
    exact AdaptiveBitBounds.computed_innerPower_le_size n hn call
  have hq : f.cyclic ≤ 2^(AdaptiveBitBounds.computedCyclicConstant*n.size) := by
    rw [hcyclic]
    exact AdaptiveBitBounds.computed_cyclic_le_pow_size n hn call
  have hc := prepareGlobal_queries_price (t:=p.t) left right (retainedRequests f p input) hl hr n
    AdaptiveBitBounds.computedLengthConstant AdaptiveBitBounds.computedIndexConstant
    AdaptiveBitBounds.computedCyclicConstant (BackendNumeratorBounds.numeratorBitBudget p.L p.m f.cyclic 1)
    (by omega) p.m_le_L hL hm hq p.t_le
  have hwidth : p.lowWidth=BinaryGeometryWidth.geometryWidth p.L p.m f.cyclic :=
    PlanGeometry.preparePlan_lowWidth_geometry n (ComputableParameters.block n) f
  have hQ : FoldedBackendExecution.windowQuerySize n=3*n^2 := by
    unfold FoldedBackendExecution.windowQuerySize
    ring
  have hp : (payload.blocks.value.get b).prepared.bitSteps+
      (∑ i : Fin (FoldedBackendExecution.windowQuerySize n),
        ((payload.blockQueries b).get i).result.operations) ≤
      computedBatchConstant*(n.size+1)^12*
        (globalPreparationBudget p.N p.L p.m p.t f.cyclic (fullBudget p.L p.m f.cyclic)+
          FoldedBackendExecution.windowQuerySize n*
            globalQueryRefinement p.N p.L p.m (BackendNumeratorBounds.numeratorBitBudget p.L p.m f.cyclic 1)*
            (lowCoefficientCost p.m p.t f.cyclic (2*p.m+1)+highCoefficientReads p.m p.t)) := by
    rw [retained_block_joint_counter]
    change (BinaryBackendExecution.prepareGlobal (L:=p.L) (m:=p.m) (t:=p.t)
      p.lowWidth 1 left right).bitSteps+
      (∑ i : Fin (FoldedBackendExecution.windowQuerySize n),
        (BinaryBackendExecution.queryGlobalExecution (ThinMatrixBackend.tileWidth_pos p.L p.m p.m_le_L)
          (BinaryBackendExecution.prepareGlobal (L:=p.L) (m:=p.m) (t:=p.t) p.lowWidth 1 left right)
          ((retainedRequests f p input).get i).1 ((retainedRequests f p input).get i).2.1
          ((retainedRequests f p input).get i).2.2).result.operations) ≤ _
    rw [hwidth]
    simpa only [computedBatchConstant] using hc
  simpa only [hpN,hpL,hpm,hpt,hcyclic,hQ] using hp

/-- One actual retained factory block obeys the closed phase ledger. The
input contains arbitrary canonical binary cells; all coefficient caps used
by the preparation/query pipeline come from its own indicator formation. -/
theorem eventual_retained_block_work :
    ∀ᶠ n : ℕ in Filter.atTop,
      ∀ call : ComputedPhaseGeometry.Call AlignedCertificate.R n,
      ∀ r (f : CompactBlocks.PhysicalFactorization r),
      f.folded=call.folded AlignedCertificate.S →
      f.cyclic=call.cyclic AlignedCertificate.S →
      ∀ input : BinaryFoldedFormation.Inputs n,
      ∀ b : Fin (CompactBlocks.blockCount n (ComputableParameters.block n)),
      let p := (BinaryTriangleSetupCosts.preparePlan n (ComputableParameters.block n) f).value
      let payload := prepareRetained f p input
      let m := ComputedPhaseGeometry.innerPower n call AlignedCertificate.S
      let N := PhaseGeometry.outerSize call AlignedCertificate.S n
      (((payload.blocks.value.get b).prepared.bitSteps+
        (∑ i : Fin (FoldedBackendExecution.windowQuerySize n),
          ((payload.blockQueries b).get i).result.operations):ℕ):ℝ) ≤
        batchPhaseConstant*(Real.log (n:ℝ))^36*
          ∑ i : Fin 6, ReductionCosts.rawTerm RealCertificate.c RealCertificate.theta
            n N ((4:ℝ)^m) (call.cyclic AlignedCertificate.S) i := by
  filter_upwards [BinaryResourcePhase.eventual_resourceBudget_le_phase,
    Filter.eventually_ge_atTop (3:ℕ)] with n hresource hn
  intro call r f hfold hcyclic input b
  let p := (BinaryTriangleSetupCosts.preparePlan n (ComputableParameters.block n) f).value
  let payload := prepareRetained f p input
  let m := ComputedPhaseGeometry.innerPower n call AlignedCertificate.S
  let L := ComputableParameters.ordinaryLength m
  let t := ComputableParameters.channelLength m
  let q := call.cyclic AlignedCertificate.S
  let N := PhaseGeometry.outerSize call AlignedCertificate.S n
  let B := BackendNumeratorBounds.numeratorBitBudget L m q 1
  let P := globalPreparationBudget N L m t q (fullBudget L m q)+
    (3*n^2)*globalQueryRefinement N L m B*
      (lowCoefficientCost m t q (2*m+1)+highCoefficientReads m t)
  let G := BinaryPreparationComputed.preparationLogConstant computedBatchConstant
  let ell := Real.log (n:ℝ)
  let rawSum := ∑ i : Fin 6, ReductionCosts.rawTerm RealCertificate.c RealCertificate.theta
    n N ((4:ℝ)^m) q i
  have hb := computed_retained_joint_price hn call f hfold hcyclic input b
  have hbR : (((payload.blocks.value.get b).prepared.bitSteps+
      (∑ i : Fin (FoldedBackendExecution.windowQuerySize n),
        ((payload.blockQueries b).get i).result.operations):ℕ):ℝ) ≤
      ((computedBatchConstant*(n.size+1)^12:ℕ):ℝ)*(P:ℝ) := by
    exact_mod_cast hb
  have hlog := BinaryPreparationComputed.naturalFactor_mul_le_logFactor
    computedBatchConstant n (P:ℝ) hn (Nat.cast_nonneg P)
  have hP : (P:ℝ) ≤ BinaryResourcePhase.resourceCoefficient*ell^24*rawSum := by
    simpa only [P,N,L,m,t,q,ell,rawSum,fullBudget,
      BinaryResourcePhase.resourceLogDegree,Nat.mul_assoc] using hresource call
  have hG : 0 ≤ G*ell^12 := mul_nonneg
    (BinaryPreparationComputed.preparationLogConstant_nonneg _)
    (pow_nonneg (Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))) _)
  calc
    _ ≤ G*ell^12*(P:ℝ) := hbR.trans hlog
    _ ≤ G*ell^12*(BinaryResourcePhase.resourceCoefficient*ell^24*rawSum) :=
      mul_le_mul_of_nonneg_left hP hG
    _ = _ := by
      dsimp only [batchPhaseConstant,G,ell,rawSum]
      rw [show (36:ℕ)=12+24 by decide,pow_add]
      ring

#print axioms computed_retained_joint_price
#print axioms eventual_retained_block_work

end
end BlockCosts

namespace Producer
open BinaryFoldedFactory BinaryFoldedFormation

theorem produce_work_collection_real {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : Plan (n:=n) (h:=h) f) (input : Inputs n) (G R S K : ℝ)
    (hgeometry : ((prepareRetained f p input).targets.geometry.bitSteps:ℝ) ≤ G)
    (hrequests : ((prepareRetained f p input).targets.requests.bitSteps:ℝ) ≤ R)
    (hsources : ∀ b : Fin (CompactBlocks.blockCount n h),
      (((prepareRetained f p input).blocks.value.get b).sources.bitSteps:ℝ) ≤ S)
    (hjoint : ∀ b : Fin (CompactBlocks.blockCount n h),
      ((((prepareRetained f p input).blocks.value.get b).prepared.bitSteps+
        (∑ i : Fin (FoldedBackendExecution.windowQuerySize n),
          (((prepareRetained f p input).blockQueries b).get i).result.operations):ℕ):ℝ) ≤ K) :
    ((produce f p input).value.work:ℝ) ≤ G+R+(CompactBlocks.blockCount n h:ℝ)*(S+K)+19*(CompactBlocks.blockCount n h:ℝ)+
        47*(EndToEndAPSP.incidenceSize n h:ℝ)+19 := by
  let payload := prepareRetained f p input
  let sumBlock := ∑ b : Fin (CompactBlocks.blockCount n h),
    ((payload.blocks.value.get b).bitSteps+
      ∑ i : Fin (FoldedBackendExecution.windowQuerySize n),
        ((payload.blockQueries b).get i).result.operations)
  have hsum : (sumBlock:ℝ) ≤ (CompactBlocks.blockCount n h:ℝ)*(S+K) := by
    change ((∑ b : Fin (CompactBlocks.blockCount n h),
      ((payload.blocks.value.get b).bitSteps+
        ∑ i : Fin (FoldedBackendExecution.windowQuerySize n),
          ((payload.blockQueries b).get i).result.operations) :ℕ):ℝ) ≤ _
    rw [Nat.cast_sum]
    calc
      _ ≤ ∑ _b : Fin (CompactBlocks.blockCount n h), (S+K) := by
        apply Finset.sum_le_sum
        intro b _
        simpa only [PreparedBlock.bitSteps,Nat.cast_add,add_assoc] using add_le_add (hsources b) (hjoint b)
      _ = _ := by simp [mul_add]
  have hledger := produce_ledger f p input
  rw [Retained.queryCounter_reindex] at hledger
  have he : (produce f p input).value.work ≤ (prepareRetained f p input).targets.geometry.bitSteps+
      (prepareRetained f p input).targets.requests.bitSteps+sumBlock+
      19*CompactBlocks.blockCount n h+47*EndToEndAPSP.incidenceSize n h+19 := by
    exact hledger.trans_eq (by dsimp only [sumBlock];rw [Finset.sum_add_distrib];ring)
  have heR : ((produce f p input).value.work:ℝ) ≤ ((prepareRetained f p input).targets.geometry.bitSteps:ℝ)+
      ((prepareRetained f p input).targets.requests.bitSteps:ℝ)+(sumBlock:ℝ)+
      19*(CompactBlocks.blockCount n h:ℝ)+47*(EndToEndAPSP.incidenceSize n h:ℝ)+19 := by
    exact_mod_cast he
  exact heR.trans (add_le_add (add_le_add (add_le_add
    (add_le_add (add_le_add hgeometry hrequests) hsum) le_rfl) le_rfl) le_rfl)

theorem produce_work_collection_joint {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : Plan (n:=n) (h:=h) f) (input : Inputs n) (G R S K : ℕ)
    (hgeometry : (prepareRetained f p input).targets.geometry.bitSteps ≤ G)
    (hrequests : (prepareRetained f p input).targets.requests.bitSteps ≤ R)
    (hsources : ∀ b : Fin (CompactBlocks.blockCount n h),
      ((prepareRetained f p input).blocks.value.get b).sources.bitSteps ≤ S)
    (hjoint : ∀ b : Fin (CompactBlocks.blockCount n h),
      ((prepareRetained f p input).blocks.value.get b).prepared.bitSteps+
        (∑ i : Fin (FoldedBackendExecution.windowQuerySize n),
          (((prepareRetained f p input).blockQueries b).get i).result.operations) ≤ K) :
    (produce f p input).value.work ≤ G+R+CompactBlocks.blockCount n h*(S+K)+19*CompactBlocks.blockCount n h+
        47*EndToEndAPSP.incidenceSize n h+19 := by
  let payload := prepareRetained f p input
  have hsum : (∑ b : Fin (CompactBlocks.blockCount n h),
      ((payload.blocks.value.get b).bitSteps+
        ∑ i : Fin (FoldedBackendExecution.windowQuerySize n),
          ((payload.blockQueries b).get i).result.operations)) ≤ CompactBlocks.blockCount n h*(S+K) := by
    calc
      _ ≤ ∑ _b : Fin (CompactBlocks.blockCount n h), (S+K) := by
        apply Finset.sum_le_sum
        intro b _
        simpa only [PreparedBlock.bitSteps,Nat.add_assoc] using Nat.add_le_add (hsources b) (hjoint b)
      _ = _ := by simp
  have he : (∑ b : Fin (CompactBlocks.blockCount n h), (payload.blocks.value.get b).bitSteps)+
      (∑ b : Fin (CompactBlocks.blockCount n h),
        ∑ i : Fin (FoldedBackendExecution.windowQuerySize n), ((payload.blockQueries b).get i).result.operations) ≤ CompactBlocks.blockCount n h*(S+K) := by
    simpa only [Finset.sum_add_distrib] using hsum
  have hledger := produce_ledger f p input
  rw [Retained.queryCounter_reindex] at hledger
  have hbody := Nat.add_le_add (Nat.add_le_add hgeometry hrequests) he
  have hfull := Nat.add_le_add_right (Nat.add_le_add_right
    (Nat.add_le_add_right hbody (19*CompactBlocks.blockCount n h)) (47*EndToEndAPSP.incidenceSize n h)) 19
  calc
    _ ≤ (prepareRetained f p input).targets.geometry.bitSteps+
        (prepareRetained f p input).targets.requests.bitSteps+
        ((∑ b : Fin (CompactBlocks.blockCount n h), (payload.blocks.value.get b).bitSteps)+
          ∑ b : Fin (CompactBlocks.blockCount n h),
            ∑ i : Fin (FoldedBackendExecution.windowQuerySize n), ((payload.blockQueries b).get i).result.operations)+
        19*CompactBlocks.blockCount n h+47*EndToEndAPSP.incidenceSize n h+19 := by
      exact hledger.trans_eq (by ring)
    _ ≤ _ := hfull

theorem produce_work_collection {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : Plan (n:=n) (h:=h) f) (input : Inputs n) (G R S P K : ℕ)
    (hgeometry : (prepareRetained f p input).targets.geometry.bitSteps ≤ G)
    (hrequests : (prepareRetained f p input).targets.requests.bitSteps ≤ R)
    (hsources : ∀ b : Fin (CompactBlocks.blockCount n h),
      ((prepareRetained f p input).blocks.value.get b).sources.bitSteps ≤ S)
    (hprepared : ∀ b : Fin (CompactBlocks.blockCount n h),
      ((prepareRetained f p input).blocks.value.get b).prepared.bitSteps ≤ P)
    (hquery : ∀ (b : Fin (CompactBlocks.blockCount n h)) (i : Fin (FoldedBackendExecution.windowQuerySize n)),
      (((prepareRetained f p input).blockQueries b).get i).result.operations ≤ K) :
    (produce f p input).value.work ≤ G+R+CompactBlocks.blockCount n h*(S+P+FoldedBackendExecution.windowQuerySize n*K)+
        19*CompactBlocks.blockCount n h+47*EndToEndAPSP.incidenceSize n h+19 := by
  let payload := prepareRetained f p input
  have hblocks : (∑ b : Fin (CompactBlocks.blockCount n h), (payload.blocks.value.get b).bitSteps) ≤ CompactBlocks.blockCount n h*(S+P) := by
    calc
      _ ≤ ∑ _b : Fin (CompactBlocks.blockCount n h), (S+P) := by
        apply Finset.sum_le_sum
        intro b _
        exact Nat.add_le_add (hsources b) (hprepared b)
      _ = _ := by simp
  have hqueries : (∑ b : Fin (CompactBlocks.blockCount n h),
      ∑ i : Fin (FoldedBackendExecution.windowQuerySize n), ((payload.blockQueries b).get i).result.operations) ≤ CompactBlocks.blockCount n h*(FoldedBackendExecution.windowQuerySize n*K) := by
    calc
      _ ≤ ∑ _b : Fin (CompactBlocks.blockCount n h), ∑ _i : Fin (FoldedBackendExecution.windowQuerySize n), K := by
        apply Finset.sum_le_sum
        intro b _
        apply Finset.sum_le_sum
        intro i _
        exact hquery b i
      _ = _ := by simp
  have hledger := produce_ledger f p input
  rw [Retained.queryCounter_reindex] at hledger
  have hbody := Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hgeometry hrequests) hblocks) hqueries
  have hfull := Nat.add_le_add_right (Nat.add_le_add_right
    (Nat.add_le_add_right hbody (19*CompactBlocks.blockCount n h)) (47*EndToEndAPSP.incidenceSize n h)) 19
  calc
    _ ≤ (prepareRetained f p input).targets.geometry.bitSteps+
        (prepareRetained f p input).targets.requests.bitSteps+
        (∑ b : Fin (CompactBlocks.blockCount n h), (payload.blocks.value.get b).bitSteps)+
        (∑ b : Fin (CompactBlocks.blockCount n h), ∑ i : Fin (FoldedBackendExecution.windowQuerySize n),
          ((payload.blockQueries b).get i).result.operations)+
        19*CompactBlocks.blockCount n h+47*EndToEndAPSP.incidenceSize n h+19 := hledger
    _ ≤ G+R+CompactBlocks.blockCount n h*(S+P)+
        CompactBlocks.blockCount n h*(FoldedBackendExecution.windowQuerySize n*K)+
        19*CompactBlocks.blockCount n h+47*EndToEndAPSP.incidenceSize n h+19 := hfull
    _ = _ := by ring


theorem retained_geometry_cost {n h r B : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : Plan (n:=n) (h:=h) f) (input : Inputs n)
    (hb : BinaryFoldedFormationCost.MetadataBound n h
      (FoldedBackendExecution.physicalFold f) f.cyclic 0 B) :
    (prepareRetained f p input).targets.geometry.bitSteps ≤ 10000*(B+1)^2 := by
  change (makeGeometryCached n h (FoldedBackendExecution.physicalFold f) f.cyclic 0
    p.foldWidth p.N p.D p.raw p.foldWidth_eq p.N_eq p.D_eq p.raw_eq).bitSteps ≤ _
  rw [makeGeometryCached_refines]
  exact BinaryFoldedFormationCost.makeGeometry_cost hb

theorem retained_requests_cost {n h r W B : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : Plan (n:=n) (h:=h) f) (input : Inputs n)
    (hb : BinaryFoldedFormationCost.MetadataBound n h
      (FoldedBackendExecution.physicalFold f) f.cyclic 0 B)
    (hT : BinaryFoldedFormationCost.TableBound W input.target) :
    (prepareRetained f p input).targets.requests.bitSteps ≤ 2000000*FoldedBackendExecution.windowQuerySize n*(W+B+10)^2 := by
  change (BinaryFoldedTargets.requests f _ input.target).bitSteps ≤ _
  exact BinaryFoldedTargets.requests_cost f _ input.target
    ⟨hb.n_size,hb.d_size,hb.q_size,hb.width_size⟩ hT

theorem retained_sources_cost {n h r W B : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : Plan (n:=n) (h:=h) f) (input : Inputs n) (b : Fin (CompactBlocks.blockCount n h))
    (hb : BinaryFoldedFormationCost.MetadataBound n h
      (FoldedBackendExecution.physicalFold f) f.cyclic b.val B)
    (ha : BinaryFoldedFormationCost.TableBound W input.left)
    (hc : BinaryFoldedFormationCost.TableBound W input.right)
    (hn : 0<n) (hd : 0<FoldedBackendExecution.physicalFold f) (hq : 0<f.cyclic)
    (hbacking : (p.N*p.D).size ≤ B) :
    ((prepareRetained f p input).blocks.value.get b).sources.bitSteps ≤ 3000000000000*(W+B+10)^3*(2*f.cyclic*p.N*p.D) := by
  rw [prepareRetained_block_get]
  change (formSourcesCached f b input p.foldWidth p.N p.D p.raw
    p.foldWidth_eq p.N_eq p.D_eq p.raw_eq).bitSteps ≤ _
  rw [formSourcesCached_refines]
  simpa only [p.N_eq,p.D_eq] using BinaryFoldedFormationCost.formSources_cost f b input
    hb ha hc hn hd hq (by simpa only [p.N_eq,p.D_eq] using hbacking)

theorem shared_target_formation_phase_bound {n r : ℕ} (hn : 3  ≤  n)
    (f : CompactBlocks.PhysicalFactorization r)
    (p : Plan (n := n) (h := ComputableParameters.block n) f) (input : Inputs n)
    (κ M : ℕ)
    (hb : BinaryFoldedFormationCost.MetadataBound n (ComputableParameters.block n)
      (FoldedBackendExecution.physicalFold f) f.cyclic 0 (M*(n.size+1)))
    (hT : BinaryFoldedFormationCost.TableBound (κ*n.size+1) input.target) :
    ((prepareRetained f p input).targets.geometry.bitSteps+
      (prepareRetained f p input).targets.requests.bitSteps+
      19*CompactBlocks.blockCount n (ComputableParameters.block n)+
      47*EndToEndAPSP.incidenceSize n (ComputableParameters.block n)+19 : ℕ)  ≤
      100000000*(κ+M+12)^3*(n.size+1)^3*ComputedPhaseGeometry.queryCount n  :=  by
  let s := n.size+1
  let C := κ+M+12
  let F := C^3*s^3
  let J := ComputedPhaseGeometry.queryCount n
  have hs : 1 ≤ s  :=  by dsimp [s];omega
  have hC : 1 ≤ C  :=  by dsimp [C];omega
  have hCs : 1 ≤ C*s  :=  Nat.mul_le_mul hC hs
  have hcube : (C*s)^3 = F  :=  by dsimp [F];ring
  have hF : 1 ≤ F  :=  by rw [←hcube];exact one_le_pow₀ hCs
  have hsquare : (C*s)^2 ≤ F  :=  by
    rw [←hcube]
    exact Nat.pow_le_pow_right hCs (by decide)
  have hmeta : M*(n.size+1)+1 ≤ C*s  :=  by dsimp [C,s];nlinarith
  have hlength : κ*n.size+1+M*(n.size+1)+10 ≤ C*s  :=  by dsimp [C,s];nlinarith
  have hg0  :=  retained_geometry_cost f p input hb
  have hg : (prepareRetained f p input).targets.geometry.bitSteps ≤ 10000*F  :=
    hg0.trans (Nat.mul_le_mul_left _ ((Nat.pow_le_pow_left hmeta 2).trans hsquare))
  have hblocks : 1 ≤ ComputedPhaseGeometry.blockCount n  :=  by
    have hp := TilingCosts.bandCount_pos n (ComputableParameters.block n)
      (by omega) (ComputedPhaseGeometry.block_pos n)
    simpa only [ComputedPhaseGeometry.blockCount,TilingCosts.bandCount] using Nat.succ_le_of_lt hp
  have hn2 : 1 ≤ n^2  :=  one_le_pow₀ (by omega)
  have hJ : 1 ≤ J  :=  by
    dsimp [J,ComputedPhaseGeometry.queryCount]
    exact Nat.mul_le_mul hn2 hblocks
  have hB : CompactBlocks.blockCount n (ComputableParameters.block n) ≤ J  :=  by
    change ComputedPhaseGeometry.blockCount n ≤ n^2*ComputedPhaseGeometry.blockCount n
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right (ComputedPhaseGeometry.blockCount n) hn2
  have hQ : FoldedBackendExecution.windowQuerySize n ≤ 3*J  :=  by
    change n*n*3 ≤ 3*(n^2*ComputedPhaseGeometry.blockCount n)
    nlinarith
  have hI : EndToEndAPSP.incidenceSize n (ComputableParameters.block n) = 3*J  :=  by
    dsimp [EndToEndAPSP.incidenceSize,J,ComputedPhaseGeometry.queryCount,
      CompactBlocks.blockCount,ComputedPhaseGeometry.blockCount]
    ring
  have hr0  :=  retained_requests_cost f p input hb hT
  have hr : (prepareRetained f p input).targets.requests.bitSteps ≤ 6000000*J*F  :=  by
    calc
      _  ≤  2000000*FoldedBackendExecution.windowQuerySize n*
          (κ*n.size+1+M*(n.size+1)+10)^2  :=  hr0
      _  ≤  2000000*(3*J)*F  :=  Nat.mul_le_mul (Nat.mul_le_mul_left _ hQ)
          ((Nat.pow_le_pow_left hlength 2).trans hsquare)
      _ = _  :=  by ring
  have hgJ : (prepareRetained f p input).targets.geometry.bitSteps ≤ 10000*J*F  :=  by
    exact hg.trans (by simpa only [Nat.mul_one] using
      Nat.mul_le_mul_right F (Nat.mul_le_mul_left 10000 hJ))
  have hc0 : 19*CompactBlocks.blockCount n (ComputableParameters.block n)+
      47*EndToEndAPSP.incidenceSize n (ComputableParameters.block n)+19 ≤ 179*J  :=  by
    rw [hI]
    omega
  have hc : 19*CompactBlocks.blockCount n (ComputableParameters.block n)+
      47*EndToEndAPSP.incidenceSize n (ComputableParameters.block n)+19 ≤ 179*J*F  :=
    hc0.trans (by simpa only [Nat.mul_one] using Nat.mul_le_mul_left (179*J) hF)
  calc
    _ = (prepareRetained f p input).targets.geometry.bitSteps+
      (prepareRetained f p input).targets.requests.bitSteps+
      (19*CompactBlocks.blockCount n (ComputableParameters.block n)+
      47*EndToEndAPSP.incidenceSize n (ComputableParameters.block n)+19)  :=  by ring
    _  ≤  10000*J*F+6000000*J*F+179*J*F  :=  Nat.add_le_add (Nat.add_le_add hgJ hr) hc
    _ = 6010179*J*F  :=  by ring
    _  ≤  100000000*J*F  :=  Nat.mul_le_mul_right F (Nat.mul_le_mul_right J (by decide))
    _ = _  :=  by dsimp [F,C,s,J];ring

theorem shared_target_formation_le_phaseRawSum {n r : ℕ} (hn : 3  ≤  n)
    (call : ComputedPhaseGeometry.Call AlignedCertificate.R n)
    (f : CompactBlocks.PhysicalFactorization r)
    (p : Plan (n := n) (h := ComputableParameters.block n) f) (input : Inputs n)
    (κ M : ℕ)
    (hb : BinaryFoldedFormationCost.MetadataBound n (ComputableParameters.block n)
      (FoldedBackendExecution.physicalFold f) f.cyclic 0 (M*(n.size+1)))
    (hT : BinaryFoldedFormationCost.TableBound (κ*n.size+1) input.target) :
    (((prepareRetained f p input).targets.geometry.bitSteps+
      (prepareRetained f p input).targets.requests.bitSteps+
      19*CompactBlocks.blockCount n (ComputableParameters.block n)+
      47*EndToEndAPSP.incidenceSize n (ComputableParameters.block n)+19 : ℕ) : ℝ)  ≤
      (100000000*(κ+M+12)^3 : ℕ)*(n.size+1 : ℝ)^3*
        ComputedReductionCosts.phaseRawSum n call  :=  by
  have hnat := shared_target_formation_phase_bound hn f p input κ M hb hT
  have hreal : (((prepareRetained f p input).targets.geometry.bitSteps+
      (prepareRetained f p input).targets.requests.bitSteps+
      19*CompactBlocks.blockCount n (ComputableParameters.block n)+
      47*EndToEndAPSP.incidenceSize n (ComputableParameters.block n)+19 : ℕ) : ℝ)  ≤
      (100000000*(κ+M+12)^3 : ℕ)*(n.size+1 : ℝ)^3*
        (ComputedPhaseGeometry.queryCount n : ℝ)  :=  by exact_mod_cast hnat
  exact hreal.trans (mul_le_mul_of_nonneg_left
    (AlignedAPSPCosts.phaseRawSum_dominates_queries n call) (by positivity))


theorem computed_target_formation_le_phaseRawSum {n r : ℕ} (hn : 3 ≤ n)
    (call : ComputedPhaseGeometry.Call AlignedCertificate.R n)
    (f : CompactBlocks.PhysicalFactorization r)
    (hfold : f.folded=call.folded AlignedCertificate.S)
    (hcyclic : f.cyclic=call.cyclic AlignedCertificate.S)
    (p : Plan (n:=n) (h:=ComputableParameters.block n) f) (input : Inputs n) (κ : ℕ)
    (hT : BinaryFoldedFormationCost.TableBound (κ*n.size+1) input.target) :
    (((prepareRetained f p input).targets.geometry.bitSteps+
      (prepareRetained f p input).targets.requests.bitSteps+
      19*CompactBlocks.blockCount n (ComputableParameters.block n)+
      47*EndToEndAPSP.incidenceSize n (ComputableParameters.block n)+19 : ℕ) : ℝ) ≤
      (100000000*(κ+BinaryFoldedMetadataBounds.metadataConstant+12)^3 : ℕ)*(n.size+1 : ℝ)^3*
        ComputedReductionCosts.phaseRawSum n call := by
  have hbp : 0<CompactBlocks.blockCount n (ComputableParameters.block n) := by
    simpa only [CompactBlocks.blockCount,TilingCosts.bandCount] using
      TilingCosts.bandCount_pos n (ComputableParameters.block n)
        (by omega) (ComputedPhaseGeometry.block_pos n)
  let b0 : Fin (CompactBlocks.blockCount n (ComputableParameters.block n)):=⟨0,hbp⟩
  have hb:= (BinaryFoldedMetadataBounds.computed_metadata hn call f hfold hcyclic b0).1
  exact shared_target_formation_le_phaseRawSum hn call f p input κ
    BinaryFoldedMetadataBounds.metadataConstant hb hT

theorem computed_retained_sources_cost {n r κ : ℕ} (hn : 3 ≤ n)
    (call : ComputedPhaseGeometry.Call AlignedCertificate.R n)
    (f : CompactBlocks.PhysicalFactorization r)
    (hfold : f.folded=call.folded AlignedCertificate.S)
    (hcyclic : f.cyclic=call.cyclic AlignedCertificate.S)
    (p : Plan (n:=n) (h:=ComputableParameters.block n) f) (input : Inputs n)
    (hl : BinaryFoldedFormationCost.TableBound (κ*n.size+1) input.left)
    (hr : BinaryFoldedFormationCost.TableBound (κ*n.size+1) input.right)
    (b : Fin (CompactBlocks.blockCount n (ComputableParameters.block n))) :
    ((prepareRetained f p input).blocks.value.get b).sources.bitSteps ≤
      BinaryFoldedCallFormationCosts.formationFactor κ*(n.size+1)^3*
        (f.cyclic*FoldedBackendExecution.outerSize n (FoldedBackendExecution.physicalFold f)*
          FoldedBackendExecution.middleSize (ComputableParameters.block n) (FoldedBackendExecution.physicalFold f)) := by
  rw [prepareRetained_block_get]
  change (formSourcesCached f b input p.foldWidth p.N p.D p.raw
    p.foldWidth_eq p.N_eq p.D_eq p.raw_eq).bitSteps ≤ _
  rw [formSourcesCached_refines]
  exact BinaryFoldedCallFormationCosts.computed_formation_cost hn call f hfold hcyclic b input hl hr

noncomputable section
open scoped BigOperators
open BinaryFoldedFactory BinaryFoldedFormation
attribute [local irreducible] AlignedCertificate.R AlignedCertificate.S
  BinaryFoldedMetadataBounds.metadataConstant BinaryFoldedCallFormationCosts.formationFactor
  BinaryBackendCosts.batchPhaseConstant FixedPrices.sizeLogConstant

def producerCoefficient (κ : ℕ) : ℝ :=
  BinaryBackendCosts.batchPhaseConstant+
    ((100000000*(κ+BinaryFoldedMetadataBounds.metadataConstant+12)^3+
      BinaryFoldedCallFormationCosts.formationFactor κ : ℕ):ℝ)*FixedPrices.sizeLogConstant^3

theorem producerCoefficient_nonneg (κ : ℕ) : 0 ≤ producerCoefficient κ := by
  exact add_nonneg BinaryBackendCosts.batchPhaseConstant_nonneg
    (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg FixedPrices.sizeLogConstant_nonneg _))

theorem eventual_producer_work_le_phase (κ : ℕ) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ∀ call : ComputedPhaseGeometry.Call AlignedCertificate.R n,
      ∀ r (f : CompactBlocks.PhysicalFactorization r),
      f.folded=call.folded AlignedCertificate.S →
      f.cyclic=call.cyclic AlignedCertificate.S →
      ∀ input : Inputs n,
      BinaryFoldedFormationCost.TableBound (κ*n.size+1) input.left →
      BinaryFoldedFormationCost.TableBound (κ*n.size+1) input.right →
      BinaryFoldedFormationCost.TableBound (κ*n.size+1) input.target →
      let p := (BinaryTriangleSetupCosts.preparePlan n (ComputableParameters.block n) f).value
      ((produce f p input).value.work:ℝ) ≤
        producerCoefficient κ*(Real.log (n:ℝ))^36*ComputedReductionCosts.phaseRawSum n call := by
  filter_upwards [BlockCosts.eventual_retained_block_work,
    Filter.eventually_ge_atTop (3:ℕ)] with n hblock hn
  intro call r f hfold hcyclic input hl hr hT
  let p := (BinaryTriangleSetupCosts.preparePlan n (ComputableParameters.block n) f).value
  let payload := prepareRetained f p input
  let B := CompactBlocks.blockCount n (ComputableParameters.block n)
  let m := ComputedPhaseGeometry.innerPower n call AlignedCertificate.S
  let N := PhaseGeometry.outerSize call AlignedCertificate.S n
  let q := call.cyclic AlignedCertificate.S
  let ell := Real.log (n:ℝ)
  let phase := ComputedReductionCosts.phaseRawSum n call
  let rawSum := ∑ i : Fin 6, ReductionCosts.rawTerm RealCertificate.c RealCertificate.theta
    n N ((4:ℝ)^m) q i
  let Ct := 100000000*(κ+BinaryFoldedMetadataBounds.metadataConstant+12)^3
  let Cf := BinaryFoldedCallFormationCosts.formationFactor κ
  let sourceVolume := f.cyclic*FoldedBackendExecution.outerSize n (FoldedBackendExecution.physicalFold f)*
    FoldedBackendExecution.middleSize (ComputableParameters.block n) (FoldedBackendExecution.physicalFold f)
  let S : ℝ := ((Cf*(n.size+1)^3*sourceVolume:ℕ):ℝ)
  let K := BinaryBackendCosts.batchPhaseConstant*ell^36*rawSum
  have hsources (b : Fin B) : ((payload.blocks.value.get b).sources.bitSteps:ℝ) ≤ S := by
    dsimp only [payload,S,Cf,sourceVolume]
    exact_mod_cast Producer.computed_retained_sources_cost hn call f hfold hcyclic p input hl hr b
  have hjoint (b : Fin B) :
      ((((payload.blocks.value.get b).prepared.bitSteps+
        ∑ i : Fin (FoldedBackendExecution.windowQuerySize n),
          ((payload.blockQueries b).get i).result.operations):ℕ):ℝ) ≤ K :=
    hblock call r f hfold hcyclic input b
  have hcollection := Producer.produce_work_collection_real f p input
    (payload.targets.geometry.bitSteps:ℝ) (payload.targets.requests.bitSteps:ℝ) S K
    le_rfl le_rfl hsources hjoint
  have htarget : (((payload.targets.geometry.bitSteps+payload.targets.requests.bitSteps+
      19*B+47*EndToEndAPSP.incidenceSize n (ComputableParameters.block n)+19:ℕ):ℝ)) ≤
      (Ct:ℝ)*(n.size+1:ℝ)^3*phase :=
    Producer.computed_target_formation_le_phaseRawSum hn call f hfold hcyclic p input κ hT
  have hphase : (B:ℝ)*rawSum=phase := by
    dsimp only [phase]
    unfold ComputedReductionCosts.phaseRawSum
    rw [←Finset.mul_sum]
    simp only [ComputedPhaseGeometry.innerDimension,ComputedPhaseGeometry.innerPower,
      Nat.cast_pow,Nat.cast_ofNat]
    rfl
  have hvolume : (B:ℝ)*(sourceVolume:ℝ) ≤ phase := by
    have h := AlignedAPSPCosts.phaseRawSum_dominates_formation n call
    have hN := PlanGeometry.outerSize_eq call AlignedCertificate.S f hfold
    have hD : FoldedBackendExecution.middleSize (ComputableParameters.block n)
        (FoldedBackendExecution.physicalFold f)=ComputedPhaseGeometry.innerDimension n call AlignedCertificate.S := by
      rw [FoldedBackendExecution.middleSize_eq,
        PlanGeometry.middleExponent_eq call AlignedCertificate.S f hfold,
        ComputedPhaseGeometry.innerDimension_eq_power]
    dsimp only [sourceVolume]
    rw [hN,hD,hcyclic]
    push_cast
    change (ComputedPhaseGeometry.blockCount n:ℝ)*
      ((call.cyclic AlignedCertificate.S:ℝ)*PhaseGeometry.outerSize call AlignedCertificate.S n*
        ComputedPhaseGeometry.innerDimension n call AlignedCertificate.S) ≤ phase
    dsimp only [phase]
    nlinarith [h]
  have hsource : (B:ℝ)*S ≤ (Cf:ℝ)*(n.size+1:ℝ)^3*phase := by
    calc
      _ = ((Cf:ℝ)*(n.size+1:ℝ)^3)*((B:ℝ)*(sourceVolume:ℝ)) := by
        dsimp only [S]
        push_cast
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hvolume (by positivity)
  have hbackend : (B:ℝ)*K=BinaryBackendCosts.batchPhaseConstant*ell^36*phase := by
    dsimp only [K]
    rw [←hphase]
    ring
  have hcollected : ((produce f p input).value.work:ℝ) ≤
      ((Ct+Cf:ℕ):ℝ)*(n.size+1:ℝ)^3*phase+
        BinaryBackendCosts.batchPhaseConstant*ell^36*phase := by
    have htar : (payload.targets.geometry.bitSteps:ℝ)+(payload.targets.requests.bitSteps:ℝ)+
        19*(B:ℝ)+47*(EndToEndAPSP.incidenceSize n (ComputableParameters.block n):ℝ)+19 ≤
        (Ct:ℝ)*(n.size+1:ℝ)^3*phase := by
      simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] using htarget
    calc
      _ ≤ (payload.targets.geometry.bitSteps:ℝ)+(payload.targets.requests.bitSteps:ℝ)+
          (B:ℝ)*(S+K)+19*(B:ℝ)+
          47*(EndToEndAPSP.incidenceSize n (ComputableParameters.block n):ℝ)+19 := hcollection
      _ = ((payload.targets.geometry.bitSteps:ℝ)+(payload.targets.requests.bitSteps:ℝ)+
          19*(B:ℝ)+47*(EndToEndAPSP.incidenceSize n (ComputableParameters.block n):ℝ)+19)+
          (B:ℝ)*S+(B:ℝ)*K := by ring
      _ ≤ (Ct:ℝ)*(n.size+1:ℝ)^3*phase+(Cf:ℝ)*(n.size+1:ℝ)^3*phase+
          BinaryBackendCosts.batchPhaseConstant*ell^36*phase :=
        add_le_add (add_le_add htar hsource) hbackend.le
      _ = _ := by push_cast;ring
  have hell : 1 ≤ ell := PhaseGeometry.one_le_log_nat n hn
  have hpow : ell^3 ≤ ell^36 := pow_le_pow_right₀ hell (by norm_num)
  have hphase0 : 0 ≤ phase := AlignedAPSPCosts.phaseRawSum_nonneg n call
  have hfactor : ((Ct+Cf:ℕ):ℝ)*(n.size+1:ℝ)^3 ≤
      ((Ct+Cf:ℕ):ℝ)*FixedPrices.sizeLogConstant^3*ell^36 := by
    calc
      _ = (((Ct+Cf)*(n.size+1)^3:ℕ):ℝ) := by push_cast;rfl
      _ ≤ ((Ct+Cf:ℕ):ℝ)*FixedPrices.sizeLogConstant^3*ell^3 :=
        FixedPrices.sizeFactor_le_log (Ct+Cf) 3 n hn
      _ ≤ _ := mul_le_mul_of_nonneg_left hpow
        (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg FixedPrices.sizeLogConstant_nonneg _))
  calc
    _ ≤ ((Ct+Cf:ℕ):ℝ)*(n.size+1:ℝ)^3*phase+
        BinaryBackendCosts.batchPhaseConstant*ell^36*phase := hcollected
    _ ≤ (((Ct+Cf:ℕ):ℝ)*FixedPrices.sizeLogConstant^3*ell^36)*phase+
        BinaryBackendCosts.batchPhaseConstant*ell^36*phase :=
      add_le_add (mul_le_mul_of_nonneg_right hfactor hphase0) le_rfl
    _ = _ := by dsimp only [producerCoefficient,Ct,Cf,ell,phase];ring

#print axioms producerCoefficient_nonneg
#print axioms eventual_producer_work_le_phase
end
end Producer

namespace Metadata
open FoldedBackendExecution BinaryTriangleSetupCosts
attribute [local irreducible] AlignedCertificate.R AlignedCertificate.S

private theorem size_le_self (x : ℕ) : x.size ≤ x :=
  Nat.size_le.mpr Nat.lt_two_pow_self

theorem setup_sites_le_formation {n h r : ℕ} (hn : 0 < n) (hh : 0 < h)
    (f : CompactBlocks.PhysicalFactorization r) :
    (preparePlan n h f).sites ≤ 157 *
      (f.cyclic * outerSize n (physicalFold f) * middleSize h (physicalFold f)) := by
  let D := middleSize h (physicalFold f)
  let N := outerSize n (physicalFold f)
  let X := f.cyclic * N * D
  have hD : 0 < D := by
    dsimp only [D]
    rw [middleSize_eq]
    positivity
  have hN : 0 < N := by
    dsimp only [N, outerSize, FoldedCounts.foldWidth]
    positivity
  have hraw : h * (3 * f.folded) ≤ D := rawMiddle_le h (physicalFold f)
  have hfold : f.folded ≤ D := by
    have h : f.folded ≤ h * (3 * f.folded) := by nlinarith only [hh]
    exact h.trans hraw
  have hrawsize : (h * (3 * f.folded)).size ≤ D :=
    (size_le_self _).trans hraw
  have hm : (preparePlan n h f).value.m ≤ D := by
    rw [preparePlan_m]
    change Nat.clog 4 (h * (3 * f.folded)) ≤ D
    exact (clog4_le_size _).trans hrawsize
  have hqsize : f.cyclic.size ≤ f.cyclic := size_le_self _
  have hDX : D ≤ X := by
    calc
      D ≤ N * D := Nat.le_mul_of_pos_left _ hN
      _ ≤ f.cyclic * (N * D) := Nat.le_mul_of_pos_left _ f.cyclic_pos
      _ = X := by dsimp only [X]; ring
  have hqX : f.cyclic ≤ X := by
    calc
      f.cyclic ≤ f.cyclic * N := Nat.le_mul_of_pos_right _ hN
      _ ≤ f.cyclic * N * D := Nat.le_mul_of_pos_right _ hD
      _ = X := rfl
  have hX : 1 ≤ X := (Nat.succ_le_of_lt hD).trans hDX
  have hs := preparePlan_sites n h f
  change (preparePlan n h f).sites ≤ 157 * X
  omega

theorem computed_setup_price {n r : ℕ} (hn : 3 ≤ n)
    (call : ComputedPhaseGeometry.Call AlignedCertificate.R n)
    (f : CompactBlocks.PhysicalFactorization r)
    (hfold : f.folded = call.folded AlignedCertificate.S)
    (hcyclic : f.cyclic = call.cyclic AlignedCertificate.S) :
    ((preparePlan n (ComputableParameters.block n) f).sites : ℝ) ≤ 157 * ComputedReductionCosts.phaseRawSum n call := by
  let N := PhaseGeometry.outerSize call AlignedCertificate.S n
  let D := ComputedPhaseGeometry.innerDimension n call AlignedCertificate.S
  let q := call.cyclic AlignedCertificate.S
  let B := ComputedPhaseGeometry.blockCount n
  have hN : outerSize n (physicalFold f) = N := by
    simp only [N, outerSize, physicalFold, PhaseGeometry.outerSize,
      PhaseGeometry.physicalFold, hfold]
  have hD : middleSize (ComputableParameters.block n) (physicalFold f) = D := by
    simp only [D, middleSize, rawMiddle, PhaseGeometry.pad4,
      ComputedPhaseGeometry.innerDimension, ComputedPhaseGeometry.innerPower,
      physicalFold, PhaseGeometry.physicalFold, hfold]
  have hs := setup_sites_le_formation (by omega : 0 < n)
    (ComputedPhaseGeometry.block_pos n) f
  rw [hN, hD, hcyclic] at hs
  have hsR : ((preparePlan n (ComputableParameters.block n) f).sites : ℝ) ≤ 157 * ((q : ℝ) * N * D) := by exact_mod_cast hs
  have hB : 1 ≤ B := by
    have hb := TilingCosts.bandCount_pos n (ComputableParameters.block n)
      (by omega) (ComputedPhaseGeometry.block_pos n)
    simpa only [B, ComputedPhaseGeometry.blockCount, TilingCosts.bandCount] using
      Nat.succ_le_of_lt hb
  have hterm : (B : ℝ) * ReductionCosts.rawTerm RealCertificate.c RealCertificate.theta
      n N D q 5 ≤ ComputedReductionCosts.phaseRawSum n call :=
    Finset.single_le_sum (fun i _ =>
      mul_nonneg (Nat.cast_nonneg B) (ReductionCosts.rawTerm_nonneg _ _ _ _ _ _
        (Nat.cast_nonneg n) (Nat.cast_nonneg N) (Nat.cast_nonneg D)
        (Nat.cast_nonneg q) i)) (Finset.mem_univ (5 : Fin 6))
  change (B : ℝ) * ((q : ℝ) * N * D) ≤ ComputedReductionCosts.phaseRawSum n call at hterm
  have hform : (q : ℝ) * N * D ≤ ComputedReductionCosts.phaseRawSum n call := by
    apply (show (q : ℝ) * N * D ≤ (B : ℝ) * ((q : ℝ) * N * D) from ?_).trans hterm
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      (show (1 : ℝ) ≤ B by exact_mod_cast hB)
      (show (0 : ℝ) ≤ (q : ℝ) * N * D by positivity)
  exact hsR.trans (mul_le_mul_of_nonneg_left hform (by norm_num))

def historyConstant (R : ℕ) : ℕ := 8 * (R + 1) + 20

theorem history_price {n : ℕ} (hn : 3 ≤ n)
    (call : ComputedPhaseGeometry.Call AlignedCertificate.R n)
    (selected : List ℕ) (hlen : selected.length ≤ AlignedCertificate.R) :
    (BinaryTriangleExecution.historySites selected : ℝ) ≤ (historyConstant AlignedCertificate.R : ℝ) *
        ComputedReductionCosts.phaseRawSum n call := by
  have hh : BinaryTriangleExecution.historySites selected ≤ historyConstant AlignedCertificate.R := by
    unfold BinaryTriangleExecution.historySites historyConstant
    omega
  have hB : 1 ≤ ComputedPhaseGeometry.blockCount n := by
    have hb := TilingCosts.bandCount_pos n (ComputableParameters.block n)
      (by omega) (ComputedPhaseGeometry.block_pos n)
    simpa only [ComputedPhaseGeometry.blockCount, TilingCosts.bandCount] using
      Nat.succ_le_of_lt hb
  have hquery : 1 ≤ ComputedPhaseGeometry.queryCount n := by
    unfold ComputedPhaseGeometry.queryCount
    have hn1 : 1 ≤ n := by omega
    nlinarith only [hB, hn1]
  have hphase : (1 : ℝ) ≤ ComputedReductionCosts.phaseRawSum n call :=
    (show (1 : ℝ) ≤ ComputedPhaseGeometry.queryCount n by exact_mod_cast hquery).trans
      (AlignedAPSPCosts.phaseRawSum_dominates_queries n call)
  have hhR : (BinaryTriangleExecution.historySites selected : ℝ) ≤ (historyConstant AlignedCertificate.R : ℝ) := by exact_mod_cast hh
  exact hhR.trans (by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hphase
      (Nat.cast_nonneg (historyConstant AlignedCertificate.R)))

end Metadata

namespace TableCosts
noncomputable section
open BinaryTriangleExecution
attribute [local irreducible] AlignedCertificate.R AlignedCertificate.S
  BinaryControllerPolynomialBounds.publicUnitConstant
  AlignedAPSPCosts.GuardCosts.guardConstant Metadata.historyConstant
  Producer.producerCoefficient FixedPrices.sizeLogConstant

def addressLogCoefficient (κ degree : ℕ) : ℝ :=
  (BinaryControllerPolynomialBounds.publicUnitConstant κ 4 degree:ℝ)*FixedPrices.sizeLogConstant^2

def tableCoefficient (κ degree : ℕ) : ℝ :=
  addressLogCoefficient κ degree*(Producer.producerCoefficient κ+
    ((AlignedAPSPCosts.GuardCosts.guardConstant AlignedCertificate.R+
      Metadata.historyConstant AlignedCertificate.R+157:ℕ):ℝ))

theorem addressLogCoefficient_nonneg (κ degree : ℕ) : 0 ≤ addressLogCoefficient κ degree := by
  exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg FixedPrices.sizeLogConstant_nonneg _)

theorem tableCoefficient_nonneg (κ degree : ℕ) : 0 ≤ tableCoefficient κ degree := by
  exact mul_nonneg (addressLogCoefficient_nonneg κ degree)
    (add_nonneg (Producer.producerCoefficient_nonneg κ) (Nat.cast_nonneg _))

theorem eventual_concrete_table_work_le_phase (κ degree : ℕ) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ∀ call : ComputedPhaseGeometry.Call AlignedCertificate.R n,
      EndToEndAPSP.ValidFactors call.factors →
      ∀ A B T : IntTable n, InputBits A B T (κ*n.size+1) →
      ∀ (selected : List ℕ) (candidate : ℕ),
      call.factors=selected++[candidate] →
      ∀ active : ArrayCompositeAlgorithm.Flags
        (EndToEndAPSP.incidenceSize n (ComputableParameters.block n)),
      ((concreteTable A B T selected candidate active (FixedPrices.addressPrice n κ degree)).work:ℝ) ≤
        tableCoefficient κ degree*(Real.log (n:ℝ))^38*ComputedReductionCosts.phaseRawSum n call := by
  filter_upwards [Producer.eventual_producer_work_le_phase κ,
    Filter.eventually_ge_atTop (3:ℕ)] with n hproducer hn
  intro call hv A B T hA selected candidate hfac active
  have hvf : EndToEndAPSP.ValidFactors (selected++[candidate]) := by
    rw [←hfac]
    exact hv
  let split := AlignedAPSP.prepareFactors AlignedCertificate.S (selected++[candidate]) hvf
  let f := split.plan
  let plan := BinaryTriangleSetupCosts.preparePlan n (ComputableParameters.block n) f
  let input : BinaryFoldedFormation.Inputs n := ⟨A,B,T⟩
  let ell := Real.log (n:ℝ)
  let phase := ComputedReductionCosts.phaseRawSum n call
  let Cmeta := AlignedAPSPCosts.GuardCosts.guardConstant AlignedCertificate.R+
    Metadata.historyConstant AlignedCertificate.R+157
  let body := (BinaryFoldedFactory.produce f plan.value input).value.work+
    (historySites selected+(FactorValidation.validate (selected++[candidate])).2+split.work+plan.sites)
  have hfold : f.folded=call.folded AlignedCertificate.S := by
    dsimp only [f,split]
    rw [AlignedAPSP.prepareFactors_plan]
    change ((selected++[candidate]).take AlignedCertificate.S).prod =
      (call.factors.take AlignedCertificate.S).prod
    rw [hfac]
  have hcyclic : f.cyclic=call.cyclic AlignedCertificate.S := by
    dsimp only [f,split]
    rw [AlignedAPSP.prepareFactors_plan]
    change ((selected++[candidate]).drop AlignedCertificate.S).prod =
      (call.factors.drop AlignedCertificate.S).prod
    rw [hfac]
  have hleft : BinaryFoldedFormationCost.TableBound (κ*n.size+1) input.left := by
    exact hA.1
  have hright : BinaryFoldedFormationCost.TableBound (κ*n.size+1) input.right := by
    exact hA.2.1
  have htarget : BinaryFoldedFormationCost.TableBound (κ*n.size+1) input.target := by
    exact hA.2.2
  have hp : ((BinaryFoldedFactory.produce f plan.value input).value.work:ℝ) ≤
      Producer.producerCoefficient κ*ell^36*phase :=
    hproducer call _ f hfold hcyclic input hleft hright htarget
  have hlen : selected.length ≤ AlignedCertificate.R := by
    have h := call.length_le
    rw [hfac,List.length_append,List.length_singleton] at h
    omega
  have hh := Metadata.history_price hn call selected hlen
  have hg := AlignedAPSPCosts.GuardCosts.guard_price_le_phaseRawSum n hn call hv
  rw [hfac] at hg
  have hsplit : split.work=(FactorValidation.splitProducts AlignedCertificate.S
      (selected++[candidate])).2 := rfl
  rw [←hsplit] at hg
  have hs := Metadata.computed_setup_price hn call f hfold hcyclic
  have hm : ((historySites selected+(FactorValidation.validate (selected++[candidate])).2+
      split.work+plan.sites:ℕ):ℝ) ≤ (Cmeta:ℝ)*phase := by
    change (plan.sites:ℝ) ≤ 157*phase at hs
    change (historySites selected:ℝ) ≤ (Metadata.historyConstant AlignedCertificate.R:ℝ)*phase at hh
    change (((FactorValidation.validate (selected++[candidate])).2+split.work:ℕ):ℝ) ≤
      (AlignedAPSPCosts.GuardCosts.guardConstant AlignedCertificate.R:ℝ)*phase at hg
    dsimp only [Cmeta]
    push_cast at hg ⊢
    linarith
  have hell : 1 ≤ ell := PhaseGeometry.one_le_log_nat n hn
  have hphase0 : 0 ≤ phase := AlignedAPSPCosts.phaseRawSum_nonneg n call
  have hmeta : (Cmeta:ℝ)*phase ≤ (Cmeta:ℝ)*ell^36*phase := by
    exact mul_le_mul_of_nonneg_right
      (le_mul_of_one_le_right (Nat.cast_nonneg Cmeta) (one_le_pow₀ hell)) hphase0
  have hbody : (body:ℝ) ≤ (Producer.producerCoefficient κ+(Cmeta:ℝ))*ell^36*phase := by
    dsimp only [body]
    rw [Nat.cast_add]
    calc
      _ ≤ Producer.producerCoefficient κ*ell^36*phase+(Cmeta:ℝ)*phase := add_le_add hp hm
      _ ≤ Producer.producerCoefficient κ*ell^36*phase+(Cmeta:ℝ)*ell^36*phase :=
        add_le_add le_rfl hmeta
      _ = _ := by ring
  have ha : (FixedPrices.addressPrice n κ degree:ℝ) ≤ addressLogCoefficient κ degree*ell^2 := by
    have hnat := FixedPrices.addressPrice_poly n κ degree
    calc
      _ ≤ ((BinaryControllerPolynomialBounds.publicUnitConstant κ 4 degree*(n.size+1)^2:ℕ):ℝ) := by
        exact_mod_cast hnat
      _ ≤ _ := FixedPrices.sizeFactor_le_log
        (BinaryControllerPolynomialBounds.publicUnitConstant κ 4 degree) 2 n hn
  have hwork : (concreteTable A B T selected candidate active (FixedPrices.addressPrice n κ degree)).work=
      FixedPrices.addressPrice n κ degree*body := by
    rw [concreteTable_of_valid A B T selected candidate active (FixedPrices.addressPrice n κ degree) hvf]
    rfl
  rw [hwork,Nat.cast_mul]
  calc
    _ ≤ (addressLogCoefficient κ degree*ell^2)*
        ((Producer.producerCoefficient κ+(Cmeta:ℝ))*ell^36*phase) :=
      mul_le_mul ha hbody (Nat.cast_nonneg body)
        (mul_nonneg (addressLogCoefficient_nonneg κ degree) (pow_nonneg (by linarith [hell]) _))
    _ = _ := by
      dsimp only [tableCoefficient,Cmeta,ell,phase]
      rw [show (38:ℕ)=2+36 by decide,pow_add]
      ring

#print axioms addressLogCoefficient_nonneg
#print axioms tableCoefficient_nonneg
#print axioms eventual_concrete_table_work_le_phase
end
end TableCosts

namespace Aggregation
open ComputedReductionCosts

theorem phaseRawSum_le_chargedCost {n : ℕ} (hn : 3 ≤ n)
    (hpool : 1 ≤ (PrimePool.candidates (ComputableParameters.scale n)).card)
    (call : ComputedPhaseGeometry.Call AlignedCertificate.R n) :
    phaseRawSum n call ≤ ledgerConstant*ArithmeticSlack.chargedCost ledgerLogDegree n := by
  have hextra : (0:ℝ) ≤ (ArithmeticSlack.extra:ℝ) := by
    norm_num [ArithmeticSlack.extra,ArithmeticSlack.epsilon,AlignedCertificate.v,
      AlignedCertificate.eta,AlignedCertificate.b,AlignedCertificate.R,AlignedCertificate.S]
  have hp : 1 ≤ (n:ℝ)^(ArithmeticSlack.extra:ℝ) :=
    Real.one_le_rpow (by exact_mod_cast (show 1 ≤ n by omega)) hextra
  calc
    _ ≤ ((PrimePool.candidates (ComputableParameters.scale n)).card:ℝ)*phaseRawSum n call :=
      le_mul_of_one_le_left (AlignedAPSPCosts.phaseRawSum_nonneg n call) (by exact_mod_cast hpool)
    _ ≤ roundedPhaseLedger n call.factors.length := actual_rawSum_bound n hn call
    _ ≤ allPhaseLedger n := roundedPhaseLedger_le_all n call.factors.length hn call.length_le
    _ ≤ (n:ℝ)^(ArithmeticSlack.extra:ℝ)*allPhaseLedger n :=
      le_mul_of_one_le_left (allPhaseLedger_nonneg n hn) hp
    _ ≤ _ := charged_allPhaseLedger_le_chargedCost n hn

theorem candidates_nonempty_of_program {n U : ℕ}
    (parameters : CompleteAPSP.Parameters (ComputableParameters.block n) U)
    (hp : ComputableParameters.program n U=some parameters) :
    1 ≤ (PrimePool.candidates (ComputableParameters.scale n)).card := by
  have hcard : 1 ≤ parameters.pool.card := by
    have hm : 1 ≤ parameters.M := by have h := parameters.threshold; omega
    have hs := parameters.size
    omega
  have he := (ComputableParameters.program_sound n U parameters hp).1
  rw [he] at hcard
  exact hcard.trans (Finset.card_le_card (by
    intro p hmem
    simpa only [PrimePool.enumeratedCandidates_eq] using (Finset.mem_sdiff.mp hmem).1))

theorem log_mul_chargedCost (n j k : ℕ) :
    (Real.log (n:ℝ))^j*ArithmeticSlack.chargedCost k n =
      ArithmeticSlack.chargedCost (j+k) n := by
  unfold ArithmeticSlack.chargedCost
  rw [show j+k+AlignedCertificate.R+10=j+(k+AlignedCertificate.R+10) by omega,pow_add]
  ring

/-- Once the concrete producer is bounded by the six finite phase terms,
its retained work fields have a uniform polynomial cap. This auxiliary
statement is used to derive register and heap widths, not as a final runtime
assumption. -/
theorem eventual_phase_price_le_four (C : ℝ) (j : ℕ) (hC : 0 ≤ C) :
    ∀ᶠ n : ℕ in atTop, ∀ call : ComputedPhaseGeometry.Call AlignedCertificate.R n,
      1 ≤ (PrimePool.candidates (ComputableParameters.scale n)).card →
      ∀ work : ℕ, (work:ℝ) ≤ C*(Real.log (n:ℝ))^j*phaseRawSum n call → work ≤ n^4 := by
  filter_upwards [chargedCost_eventually_le_four (C*ledgerConstant) (j+ledgerLogDegree),
    eventually_ge_atTop (3:ℕ)] with n hfour hn
  intro call hpool work hwork
  have hphase := phaseRawSum_le_chargedCost hn hpool call
  have hl : 0 ≤ Real.log (n:ℝ) := by linarith [PhaseGeometry.one_le_log_nat n hn]
  have hc : 0 ≤ C*(Real.log (n:ℝ))^j := mul_nonneg hC (pow_nonneg hl j)
  have hbound : (work:ℝ) ≤ (n:ℝ)^(4:ℕ) := by
    calc
      _ ≤ C*(Real.log (n:ℝ))^j*phaseRawSum n call := hwork
      _ ≤ C*(Real.log (n:ℝ))^j*(ledgerConstant*ArithmeticSlack.chargedCost ledgerLogDegree n) :=
        mul_le_mul_of_nonneg_left hphase hc
      _ = (C*ledgerConstant)*ArithmeticSlack.chargedCost (j+ledgerLogDegree) n := by
        rw [←log_mul_chargedCost]
        ring
      _ ≤ _ := hfour
  exact_mod_cast hbound

/-- Projection preserves the actual payload work field of every retained
binary call, including its chronological position. -/
theorem projected_workSum_eq_fin_sum {I : ℕ} {Payload : Type*}
    (calls : List (BinaryControllerExecution.Call I Payload)) :
    CountedArrayComposite.workSum (BinaryControllerExecution.projectCalls calls) =
      ∑ i : Fin calls.length, (calls.get i).result.work := by
  unfold CountedArrayComposite.workSum BinaryControllerExecution.projectCalls
  rw [List.map_map]
  change (calls.map (fun call => call.result.work)).sum = _
  conv_lhs => rw [←List.ofFn_get calls]
  simp only [List.map_ofFn,List.sum_ofFn,Function.comp_apply]

/-- This is a sum of the original binary producer results. The native oracle
projection is used only in the existing erased trace theorem. -/
theorem solve_backendWork_eq_fin_sum {n h U : ℕ} {Payload : Type}
    (backend : Backend n h Payload) (parameters : CompleteAPSP.Parameters h U)
    (static : Static (n:=n) parameters) (X Y T : IntTable n) :
    (solve backend parameters static X Y T).backendWork =
      ∑ i : Fin (solve backend parameters static X Y T).calls.length,
        ((solve backend parameters static X Y T).calls.get i).result.work := by
  rw [solve_backendWork]
  exact projected_workSum_eq_fin_sum _

/-- Intermediate composition interface for the binary factory. Its local
bound must price the actual binary table returned by the original oracle.
This theorem only aggregates that finite premise over the actual call trace. -/
theorem solve_backend_le_chargedCost_of_factory {n U : ℕ} {Payload : Type}
    (hn : 3 ≤ n) (backend : Backend n (ComputableParameters.block n) Payload)
    (parameters : CompleteAPSP.Parameters (ComputableParameters.block n) U)
    (hp : ComputableParameters.program n U = some parameters)
    (static : Static (n:=n) parameters) (X Y T : IntTable n)
    (allowance CB Cbit Cround : ℝ) (localLog bitLog roundLog : ℕ)
    (hallowance : 0 ≤ allowance) (hCB : 0 ≤ CB) (hCbit : 0 ≤ Cbit) (hCround : 0 ≤ Cround)
    (hfactory : ∀ phase : ComputedPhaseGeometry.Call AlignedCertificate.R n,
      EndToEndAPSP.ValidFactors phase.factors → ∀ (selected : List ℕ) (candidate : ℕ),
      phase.factors = selected++[candidate] →
      ∀ active : ArrayCompositeAlgorithm.Flags
        (EndToEndAPSP.incidenceSize n (ComputableParameters.block n)),
      (((backend.oracle X Y T).table selected candidate active).work:ℝ) ≤ allowance*CB*(Real.log (n:ℝ))^localLog*phaseRawSum n phase)
    (harithmetic : allowance ≤ Cbit*(Real.log (n:ℝ))^bitLog*
      (n:ℝ)^(ArithmeticSlack.extra:ℝ))
    (hrounds : (parameters.stages*AlignedCertificate.R:ℕ) ≤ Cround*(Real.log (n:ℝ))^roundLog) :
    ((solve backend parameters static X Y T).backendWork:ℝ) ≤ (Cround*Cbit*CB*ledgerConstant)*
        ArithmeticSlack.chargedCost (roundLog+bitLog+localLog+ledgerLogDegree) n := by
  let out := solve backend parameters static X Y T
  let calls := out.calls
  have hparams := ComputableParameters.program_sound n U parameters hp
  have hpool : parameters.pool = ComputableParameters.computedPool n := hparams.1
  have hkR : parameters.k+1 = AlignedCertificate.R := by
    rw [hparams.2.2.2.1]
    norm_num [ComputableParameters.factorCount,AlignedCertificate.R]
  have hthree : ∀ q ∈ parameters.pool, q ≠ 3 := by
    intro q hq
    rw [hpool] at hq
    exact fun heq => (Finset.mem_sdiff.mp hq).2 (by simp only [heq,Finset.mem_singleton])
  have hlen (i : Fin calls.length) :
      ((calls.get i).factors.selected++[(calls.get i).factors.candidate]).length ≤ AlignedCertificate.R := by
    have h := solve_factors_length backend parameters static X Y T (calls.get i) (List.get_mem calls i)
    simpa only [List.length_append,List.length_singleton,hkR] using h
  have hmem (i : Fin calls.length) :
      ∀ q ∈ (calls.get i).factors.selected++[(calls.get i).factors.candidate],
        q ∈ ComputableParameters.computedPool n := by
    intro q hq
    rw [←hpool]
    exact solve_factor_property backend parameters static X Y T (fun p=>p∈parameters.pool)
      (fun _ h=>h) (calls.get i) (List.get_mem calls i) q hq
  let phases : Fin calls.length → ComputedPhaseGeometry.Call AlignedCertificate.R n := fun i =>
    ComputedPhaseGeometry.phaseCallOfPool AlignedCertificate.R n
      ((calls.get i).factors.selected++[(calls.get i).factors.candidate]) (hlen i) (hmem i)
  let cost : Fin calls.length → ℕ := fun i => (calls.get i).result.work
  let rounds := parameters.stages*AlignedCertificate.R
  have hcount : calls.length ≤ rounds*(ComputableParameters.computedPool n).card := by
    have h := solve_calls_bound backend parameters static X Y T
    simpa only [hkR,hpool] using h
  have hcost (i : Fin calls.length) : (cost i:ℝ) ≤ allowance*CB*(Real.log (n:ℝ))^localLog*phaseRawSum n (phases i) := by
    have hvalid := solve_valid_histories backend parameters static X Y T hthree
      (calls.get i) (List.get_mem calls i)
    have hresult := solve_provenance backend parameters static X Y T
      (calls.get i) (List.get_mem calls i)
    have h := hfactory (phases i) hvalid (calls.get i).factors.selected
      (calls.get i).factors.candidate rfl (calls.get i).factors.active
    rw [←hresult] at h
    exact h
  have hbatch := callCost_batch_le_chargedCost_pool phases cost hn rounds hcount
    allowance CB Cbit Cround localLog bitLog roundLog
    hallowance hCB hCbit hCround hcost harithmetic hrounds
  have heq : out.backendWork = ∑ i : Fin calls.length, cost i := by
    exact solve_backendWork_eq_fin_sum backend parameters static X Y T
  change (out.backendWork:ℝ) ≤ _
  rw [heq]
  exact hbatch

end Aggregation

namespace Closed
noncomputable section
open ComputedReductionCosts
attribute [local irreducible] AlignedCertificate.R AlignedCertificate.S
  TableCosts.tableCoefficient FixedPrices.callbackBookCoefficient PreparedSetup.setupBookCoefficient

def roundCoefficient : ℝ := (AlignedCertificate.R:ℝ)*FixedPrices.sizeLogConstant

def backendCoefficient (κ degree : ℕ) : ℝ :=
  roundCoefficient*TableCosts.tableCoefficient κ degree*ledgerConstant

def backendLogDegree : ℕ := 1+0+38+ledgerLogDegree

def callbackLogDegree : ℕ := backendLogDegree+8

def callbackCoefficient (κ degree : ℕ) : ℝ :=
  backendCoefficient κ degree+FixedPrices.callbackBookCoefficient κ degree+
    PreparedSetup.setupBookCoefficient κ degree

attribute [local irreducible] backendLogDegree callbackLogDegree

theorem roundCoefficient_nonneg : 0 ≤ roundCoefficient :=
  mul_nonneg (Nat.cast_nonneg _) FixedPrices.sizeLogConstant_nonneg

theorem backendCoefficient_nonneg (κ degree : ℕ) : 0 ≤ backendCoefficient κ degree :=
  mul_nonneg (mul_nonneg roundCoefficient_nonneg (TableCosts.tableCoefficient_nonneg κ degree))
    ledgerConstant_nonneg

theorem callbackCoefficient_nonneg (κ degree : ℕ) : 0 ≤ callbackCoefficient κ degree :=
  add_nonneg (add_nonneg (backendCoefficient_nonneg κ degree)
    (FixedPrices.callbackBookCoefficient_nonneg κ degree)) (PreparedSetup.setupBookCoefficient_nonneg κ degree)

/-- The original retained binary call returns are summed in their executed
order. Every pointwise producer, source, width and arithmetic bound is
instantiated from the actual computed parameters and stored inputs. -/
theorem eventual_solve_backendWork_le (κ degree : ℕ) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ U
      (parameters : CompleteAPSP.Parameters (ComputableParameters.block n) U),
      ComputableParameters.program n U=some parameters → U ≤ n^κ →
      ∀ static : Static (n:=n) parameters, ∀ A B T : IntTable n,
      CountedEndToEndAPSP.entryQueryBound (viewTable A) (viewTable B) (viewTable T) ≤ U →
      let addr:=FixedPrices.addressPrice n κ degree
      let backend:=concreteBackend n (ComputableParameters.block n) (EndToEndAPSP.block_pos n) addr
      ((solve backend parameters static A B T).backendWork:ℝ) ≤
        backendCoefficient κ degree*ArithmeticSlack.chargedCost backendLogDegree n := by
  filter_upwards [TableCosts.eventual_concrete_table_work_le_phase κ degree,
    Filter.eventually_ge_atTop (3:ℕ)] with n htable hn
  intro U parameters hp hU static A B T hcap
  let addr:=FixedPrices.addressPrice n κ degree
  let backend:=concreteBackend n (ComputableParameters.block n) (EndToEndAPSP.block_pos n) addr
  let CB:=TableCosts.tableCoefficient κ degree
  let ell:=Real.log (n:ℝ)
  have hA:=inputBits_of_polynomial_entry_cap A B T hU hcap
  have hf : ∀ phase : ComputedPhaseGeometry.Call AlignedCertificate.R n,
      EndToEndAPSP.ValidFactors phase.factors → ∀ selected candidate,
      phase.factors=selected++[candidate] → ∀ active,
      (((backend.oracle A B T).table selected candidate active).work:ℝ) ≤
        (1:ℝ)*CB*ell^38*phaseRawSum n phase := by
    intro phase hv selected candidate hfac active
    have h:=htable phase hv A B T hA selected candidate hfac active
    simpa only [one_mul,CB,ell,backend,concreteBackend,concreteOracle] using h
  have hextra : (0:ℝ) ≤ (ArithmeticSlack.extra:ℝ) := by
    norm_num [ArithmeticSlack.extra,ArithmeticSlack.epsilon,AlignedCertificate.v,
      AlignedCertificate.eta,AlignedCertificate.b,AlignedCertificate.R,AlignedCertificate.S]
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have harithmetic : (1:ℝ) ≤ (1:ℝ)*ell^0*(n:ℝ)^(ArithmeticSlack.extra:ℝ) := by
    simpa only [pow_zero,one_mul] using Real.one_le_rpow hn1 hextra
  have hparams:=ComputableParameters.program_sound n U parameters hp
  have hrounds : ((parameters.stages*AlignedCertificate.R:ℕ):ℝ) ≤ roundCoefficient*ell^1 := by
    have hs:=AlignedAPSPCosts.ControllerCosts.stages_le_log n hn
    have hm:=mul_le_mul_of_nonneg_right hs (Nat.cast_nonneg AlignedCertificate.R)
    simpa only [Nat.cast_mul,hparams.2.2.2.2.2,roundCoefficient,
      FixedPrices.sizeLogConstant,ell,pow_one,mul_assoc,mul_left_comm,mul_comm] using hm
  have hb:=Aggregation.solve_backend_le_chargedCost_of_factory hn backend parameters hp static A B T
    1 CB 1 roundCoefficient 38 0 1 (by norm_num) (TableCosts.tableCoefficient_nonneg κ degree)
    (by norm_num) roundCoefficient_nonneg hf harithmetic hrounds
  simpa only [backendCoefficient,backendLogDegree,mul_one,CB,addr,backend] using hb

/-- Every table retained on a valid computed history has polynomial-sized
work metadata. This closes the work-word cap used by the heap/register
width proofs, rather than postulating it about the final execution. -/
theorem eventual_valid_table_work_le_four (κ degree : ℕ) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ U
      (parameters : CompleteAPSP.Parameters (ComputableParameters.block n) U),
      ComputableParameters.program n U=some parameters → U ≤ n^κ →
      ∀ A B T : IntTable n,
      CountedEndToEndAPSP.entryQueryBound (viewTable A) (viewTable B) (viewTable T) ≤ U →
      ∀ phase : ComputedPhaseGeometry.Call AlignedCertificate.R n,
      EndToEndAPSP.ValidFactors phase.factors → ∀ selected candidate,
      phase.factors=selected++[candidate] → ∀ active,
      (concreteTable (h:=ComputableParameters.block n) A B T selected candidate active (FixedPrices.addressPrice n κ degree)).work ≤ n^4 := by
  filter_upwards [TableCosts.eventual_concrete_table_work_le_phase κ degree,
    Aggregation.eventual_phase_price_le_four (TableCosts.tableCoefficient κ degree) 38
      (TableCosts.tableCoefficient_nonneg κ degree)] with n htable hfour
  intro U parameters hp hU A B T hcap phase hv selected candidate hfac active
  exact hfour phase (Aggregation.candidates_nonempty_of_program parameters hp) _
    (htable phase hv A B T (inputBits_of_polynomial_entry_cap A B T hU hcap)
      selected candidate hfac active)

/-- Complete concrete prepared-callback resource bound. It includes the
one-time retained-prime setup, the actual binary producer/controller run,
cap scan, final original-sum checks and output writes. No oracle-time,
source-width, multiplier-budget or final-counter premise remains. -/
theorem eventual_prepared_resources_le (κ degree : ℕ) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ U
      (parameters : CompleteAPSP.Parameters (ComputableParameters.block n) U),
      ComputableParameters.program n U=some parameters → U ≤ n^κ →
      ∀ (labels : Vector ℕ parameters.pool.card)
        (hlabels : labels=EndToEndAPSP.primeVector parameters.pool),
      ∀ A B T : IntTable n,
      CountedEndToEndAPSP.entryQueryBound (viewTable A) (viewTable B) (viewTable T) ≤ U →
      let addr:=FixedPrices.addressPrice n κ degree
      let prepared:=prepareConcreteFromPrimes (n:=n) (EndToEndAPSP.block_pos n)
        parameters labels hlabels addr
      (prepared.setupBits:ℝ)+(addr:ℝ)*prepared.setupControl+
        ((prepared.oracle A B T).work:ℝ)+(prepared.oracle A B T).answerWrites ≤
          callbackCoefficient κ degree*ArithmeticSlack.chargedCost callbackLogDegree n := by
  filter_upwards [eventual_solve_backendWork_le κ degree,
    Filter.eventually_ge_atTop (3:ℕ)] with n hbackend hn
  intro U parameters hp hU labels hlabels A B T hcap
  let addr:=FixedPrices.addressPrice n κ degree
  let backend:=concreteBackend n (ComputableParameters.block n) (EndToEndAPSP.block_pos n) addr
  let static:=(setupStaticFromPrimes (n:=n) parameters labels hlabels).value
  let prepared:=prepareConcreteFromPrimes (n:=n) (EndToEndAPSP.block_pos n)
    parameters labels hlabels addr
  have hb:=hbackend U parameters hp hU static A B T hcap
  have hc:=FixedPrices.computed_callback_charged_overhead (degree:=degree) hn parameters hp hU static A B T hcap
  have hs:=PreparedSetup.concrete_setup_charged (degree:=degree) hn parameters hp hU labels hlabels
  change ((prepared.oracle A B T).work:ℝ)+(prepared.oracle A B T).answerWrites ≤
    ((solve backend parameters static A B T).backendWork:ℝ)+
      FixedPrices.callbackBookCoefficient κ degree*ArithmeticSlack.chargedCost 7 n at hc
  change (prepared.setupBits:ℝ)+(addr:ℝ)*prepared.setupControl ≤
    PreparedSetup.setupBookCoefficient κ degree*ArithmeticSlack.chargedCost 8 n at hs
  have hbm:=mul_le_mul_of_nonneg_left
    (ReductionCosts.chargedCost_mono n backendLogDegree callbackLogDegree hn
      (by unfold callbackLogDegree;omega)) (backendCoefficient_nonneg κ degree)
  have hcm:=mul_le_mul_of_nonneg_left
    (ReductionCosts.chargedCost_mono n 7 callbackLogDegree hn
      (by unfold callbackLogDegree;omega)) (FixedPrices.callbackBookCoefficient_nonneg κ degree)
  have hsm:=mul_le_mul_of_nonneg_left
    (ReductionCosts.chargedCost_mono n 8 callbackLogDegree hn
      (by unfold callbackLogDegree;omega)) (PreparedSetup.setupBookCoefficient_nonneg κ degree)
  calc
    _ = ((prepared.setupBits:ℝ)+(addr:ℝ)*prepared.setupControl)+
        (((prepared.oracle A B T).work:ℝ)+(prepared.oracle A B T).answerWrites) := by ring
    _ ≤ PreparedSetup.setupBookCoefficient κ degree*ArithmeticSlack.chargedCost 8 n+
        (((solve backend parameters static A B T).backendWork:ℝ)+
          FixedPrices.callbackBookCoefficient κ degree*ArithmeticSlack.chargedCost 7 n) :=
      add_le_add hs hc
    _ ≤ PreparedSetup.setupBookCoefficient κ degree*ArithmeticSlack.chargedCost callbackLogDegree n+
        (backendCoefficient κ degree*ArithmeticSlack.chargedCost callbackLogDegree n+
          FixedPrices.callbackBookCoefficient κ degree*ArithmeticSlack.chargedCost callbackLogDegree n) :=
      add_le_add hsm (add_le_add (hb.trans hbm) hcm)
    _ = _ := by unfold callbackCoefficient;ring

#print axioms eventual_solve_backendWork_le
#print axioms eventual_valid_table_work_le_four
#print axioms eventual_prepared_resources_le

end
end Closed

#print axioms PreparedSetup.concrete_setup_price
#print axioms PreparedSetup.concrete_setup_charged

#print axioms FixedPrices.addressPrice_poly
#print axioms FixedPrices.computed_controller_price
#print axioms FixedPrices.callbackUnit_poly
#print axioms FixedPrices.computed_callback_budget
#print axioms FixedPrices.sizeFactor_le_log
#print axioms FixedPrices.computed_callback_charged_overhead

#print axioms Producer.produce_work_collection_real
#print axioms Producer.produce_work_collection_joint
#print axioms Producer.computed_target_formation_le_phaseRawSum
#print axioms Producer.computed_retained_sources_cost
#print axioms Producer.produce_work_collection
#print axioms Producer.retained_geometry_cost
#print axioms Producer.retained_requests_cost
#print axioms Producer.retained_sources_cost
#print axioms Metadata.computed_setup_price
#print axioms Metadata.history_price

#print axioms Aggregation.projected_workSum_eq_fin_sum
#print axioms Aggregation.solve_backendWork_eq_fin_sum
#print axioms Aggregation.solve_backend_le_chargedCost_of_factory
#print axioms Aggregation.phaseRawSum_le_chargedCost
#print axioms Aggregation.candidates_nonempty_of_program
#print axioms Aggregation.eventual_phase_price_le_four

#print axioms chargedCost_eventually_le_four
#print axioms Finite.callback_reference_price
#print axioms Finite.controllerFormationSites_le_reference
#print axioms Finite.controllerExec_reference_price_of_width
#print axioms Finite.controllerExec_reference_price
#print axioms Finite.callback_referenceBudget_price
#print axioms Finite.callback_price_components
#print axioms Finite.setupStatic_price
#print axioms Finite.overheadUnit_polynomial

#print axioms inputBits_of_entry_cap
#print axioms polynomial_cap_size
#print axioms inputBits_of_polynomial_entry_cap
#print axioms computed_referenceBudget_le
#print axioms priced_referenceBudget_le_chargedCost

end ThinMatrix.BinaryTriangleCosts
