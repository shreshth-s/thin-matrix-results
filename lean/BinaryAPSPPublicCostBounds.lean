import BinaryAlignedAPSP
import AdaptiveQueryBitBounds
import UniformAPSPBound

/-!
# Public setup bounds for the concrete binary APSP program

The finite inequalities below concern the actual cap and setup expressions.
The selector bound is inherited from the executed parameter program. The
analytic statements absorb only this explicitly bounded setup overhead;
they do not postulate a callback cost or a coefficient-width bound.
-/
namespace ThinMatrix.BinaryAPSPPublicCostBounds
open Filter Asymptotics
open scoped BigOperators
set_option maxRecDepth 4000
set_option maxHeartbeats 1000000
attribute [local irreducible] ComputableParameters.block ComputableParameters.factorCount AlignedCertificate.S

theorem cap_le_power (degree n W : ℕ) (hn : 232 ≤ n) (hW : W ≤ n^degree) :
    BinaryAlignedAPSP.cap n W ≤ n^(degree+2) := by
  have hc:=ComputableParameters.apspCap_polynomial degree n W (by omega) hW
  unfold BinaryAlignedAPSP.cap
  calc
    _ ≤ 232*n^(degree+1) := hc
    _ ≤ n*n^(degree+1) := Nat.mul_le_mul_right _ hn
    _ = _ := by rw [show degree+2=degree+1+1 by omega,pow_succ]; ring

theorem cap_le_power_eventually (degree : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ W, W ≤ n^degree → BinaryAlignedAPSP.cap n W ≤ n^(degree+2) := by
  filter_upwards [eventually_ge_atTop (232 : ℕ)] with n hn
  exact fun W hW=>cap_le_power degree n W hn hW

theorem query_entryBound_le_cap {n W : ℕ} (A B T : BinaryTriangleExecution.IntTable n)
    (hb : APSPAlgorithm.SymmetricQueryBound
      (StoredMinPlusAPSP.decode (BinaryTriangleExecution.viewTable A),
        StoredMinPlusAPSP.decode (BinaryTriangleExecution.viewTable B),
        StoredMinPlusAPSP.decode (BinaryTriangleExecution.viewTable T)) (64*n*W+13 : ℕ)) :
    CountedEndToEndAPSP.entryQueryBound (BinaryTriangleExecution.viewTable A)
      (BinaryTriangleExecution.viewTable B) (BinaryTriangleExecution.viewTable T) ≤ BinaryAlignedAPSP.cap n W := by
  have hm:=CountedEndToEndAPSP.entryMagnitude_le (BinaryTriangleExecution.viewTable A)
    (BinaryTriangleExecution.viewTable B) (BinaryTriangleExecution.viewTable T) hb
  unfold CountedEndToEndAPSP.entryQueryBound BinaryAlignedAPSP.cap
  nlinarith only [hm]

theorem publicSetupBits_le (degree n W : ℕ) (hW : W ≤ n^degree) :
    BinaryAlignedAPSP.publicSetupBits n W ≤ 1024*(degree+12)^2*(n.size+1)^2 := by
  have hw:=AdaptiveQueryBitBounds.original_bound_size n degree W hW
  have hl : n.size+W.size+10 ≤ (degree+12)*(n.size+1) := by nlinarith only [hw]
  unfold BinaryAlignedAPSP.publicSetupBits
  calc
    _ ≤ 1024*((degree+12)*(n.size+1))^2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hl 2)
    _ = _ := by rw [mul_pow]; ring

def setupConstant (degree Uconst : ℕ) : ℕ :=
  100*(Uconst+2)+1024*(degree+12)^2

/-- A pure finite inequality, independent of the selector implementation. -/
theorem extraSetup_le_setupAllowance_nat (degree Uconst n W a steps : ℕ)
    (hn : 1≤n) (hW : W≤n^degree) (ha : a≤Uconst*(n.size+1)^2) (hs : steps≤n^2) :
    (a+2)*steps+BinaryAlignedAPSP.publicSetupBits n W+76*(a+1) ≤
      setupConstant degree Uconst*n^2*(n.size+1)^2 := by
  have hS : 1≤(n.size+1)^2 := Nat.one_le_pow _ _ (by omega)
  have hn2 : 1≤n^2 := Nat.one_le_pow _ _ hn
  have ha2 : a+2≤(Uconst+2)*(n.size+1)^2 := by nlinarith only [ha,hS]
  have ha1 : a+1≤(Uconst+1)*(n.size+1)^2 := by nlinarith only [ha,hS]
  have hfirst : (a+2)*steps ≤ (Uconst+2)*n^2*(n.size+1)^2 := by
    calc
      _ ≤ ((Uconst+2)*(n.size+1)^2)*n^2 := Nat.mul_le_mul ha2 hs
      _ = _ := by ring
  have hpad : (n.size+1)^2≤n^2*(n.size+1)^2 := Nat.le_mul_of_pos_left _ (by omega)
  have hpublic : BinaryAlignedAPSP.publicSetupBits n W ≤ 1024*(degree+12)^2*n^2*(n.size+1)^2 := by
    calc
      _ ≤ (1024*(degree+12)^2)*((n.size+1)^2) := publicSetupBits_le degree n W hW
      _ ≤ (1024*(degree+12)^2)*(n^2*(n.size+1)^2) := Nat.mul_le_mul_left _ hpad
      _ = _ := by ring
  have htail : 76*(a+1) ≤ (76*(Uconst+1))*n^2*(n.size+1)^2 := by
    calc
      _ ≤ 76*((Uconst+1)*(n.size+1)^2) := Nat.mul_le_mul_left _ ha1
      _ ≤ 76*((Uconst+1)*(n^2*(n.size+1)^2)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hpad)
      _ = _ := by ring
  calc
    _ ≤ (Uconst+2)*n^2*(n.size+1)^2+1024*(degree+12)^2*n^2*(n.size+1)^2+
        (76*(Uconst+1))*n^2*(n.size+1)^2 := Nat.add_le_add (Nat.add_le_add hfirst hpublic) htail
    _ = ((Uconst+2)+1024*(degree+12)^2+76*(Uconst+1))*n^2*(n.size+1)^2 := by ring
    _ ≤ _ := by
      apply Nat.mul_le_mul_right
      apply Nat.mul_le_mul_right
      unfold setupConstant
      omega

/-- The actual selector, uniformly over every original polynomial weight cap. -/
theorem actual_extraSetup_eventually (degree Uconst : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ W a : ℕ, W≤n^degree → a≤Uconst*(n.size+1)^2 →
      (a+2)*(ParameterExecution.execute n (BinaryAlignedAPSP.cap n W)).bitSteps+
        BinaryAlignedAPSP.publicSetupBits n W+76*(a+1) ≤
          setupConstant degree Uconst*n^2*(n.size+1)^2 := by
  filter_upwards [ParameterExecution.execute_apspCap_eventually degree,eventually_ge_atTop (1 : ℕ)]
    with n hsteps hn
  intro W a hW ha
  have hb : (ParameterExecution.execute n (BinaryAlignedAPSP.cap n W)).bitSteps≤n^2 := by
    exact_mod_cast hsteps W hW
  exact extraSetup_le_setupAllowance_nat degree Uconst n W a _ hn hW ha hb

noncomputable def setupAllowance (degree Uconst n : ℕ) : ℝ :=
  (setupConstant degree Uconst : ℝ)*(n : ℝ)^2*((n.size+1 : ℕ) : ℝ)^2

theorem actual_extraSetup_le_allowance_eventually (degree Uconst : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ W a : ℕ, W≤n^degree → a≤Uconst*(n.size+1)^2 →
      (((a+2)*(ParameterExecution.execute n (BinaryAlignedAPSP.cap n W)).bitSteps+
        BinaryAlignedAPSP.publicSetupBits n W+76*(a+1) : ℕ) : ℝ) ≤ setupAllowance degree Uconst n := by
  filter_upwards [actual_extraSetup_eventually degree Uconst] with n hn
  intro W a hW ha
  unfold setupAllowance
  exact_mod_cast hn W a hW ha

theorem size_add_one_le_log (n : ℕ) (hn : 3≤n) :
    ((n.size+1 : ℕ) : ℝ) ≤ 5*Real.log (n : ℝ) := by
  have hs:=ComputableParameters.size_le_four_log n hn
  have hl:=PhaseGeometry.one_le_log_nat n hn
  push_cast
  linarith only [hs,hl]

/-- A strict exponent gap absorbs the setup overhead and two further logarithms. -/
theorem log_mul_setupAllowance_bigO (degree Uconst : ℕ) :
    (fun n : ℕ => (Real.log (n : ℝ))^2*setupAllowance degree Uconst n)
      =O[atTop] (fun n : ℕ => (n : ℝ)^(299294792/100000000 : ℝ)) := by
  let H : ℝ := setupConstant degree Uconst
  have hmain : (fun n : ℕ => (25*H)*(Real.log (n : ℝ))^4*(n : ℝ)^2)
      =O[atTop] (fun n : ℕ => (n : ℝ)^(299294792/100000000 : ℝ)) := by
    simpa only [Real.rpow_two,mul_assoc] using
      (AsymptoticCosts.logPowMulRpowBigO (a:=2) (d:=(299294792/100000000 : ℝ))
        (by norm_num) 4).const_mul_left (25*H)
  have hdom : (fun n : ℕ => (Real.log (n : ℝ))^2*setupAllowance degree Uconst n)
      =O[atTop] (fun n : ℕ => (25*H)*(Real.log (n : ℝ))^4*(n : ℝ)^2) := by
    apply IsBigO.of_norm_eventuallyLE
    filter_upwards [eventually_ge_atTop (3 : ℕ)] with n hn
    have hs:=size_add_one_le_log n hn
    have hs2:=pow_le_pow_left₀ (Nat.cast_nonneg (n.size+1)) hs 2
    rw [Real.norm_of_nonneg (by unfold setupAllowance; positivity)]
    calc
      _ ≤ (Real.log (n : ℝ))^2*(H*(n : ℝ)^2*(5*Real.log (n : ℝ))^2) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hs2 (by dsimp only [H];positivity)) (sq_nonneg _)
      _ = _ := by ring
  exact hdom.trans hmain

theorem one_le_addressedUnit (B A : ℕ) : 1≤BackendScalarBits.addressedUnit B A := by
  have h : 0<BackendScalarBits.addressedUnit B A := by
    unfold BackendScalarBits.addressedUnit BackendScalarBits.scalarUnit
    positivity
  exact h

#print axioms one_le_addressedUnit
#print axioms cap_le_power_eventually
#print axioms query_entryBound_le_cap
#print axioms publicSetupBits_le
#print axioms extraSetup_le_setupAllowance_nat
#print axioms actual_extraSetup_eventually
#print axioms actual_extraSetup_le_allowance_eventually
#print axioms log_mul_setupAllowance_bigO
end ThinMatrix.BinaryAPSPPublicCostBounds
