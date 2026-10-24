import HalfSourceLowPhaseRate
import HalfSourceHighExecutionRate
import HalfSourceOutputPhaseRate
import HalfSourceDispatchCosts
import GraphHalfSourceHostCosts

/-! Literal producer/dispatcher cost assembly. SetupRate is an explicit
intermediate premise, discharged by HalfSourceSetupPhaseRate before the
public endpoint theorem. Every other component below is actual execution. -/
namespace ThinMatrix.HalfSourceBackendCostAssembly
open Filter HalfSourceBatchFit HalfSourceCallbackBudget
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000
noncomputable section
attribute [local irreducible] GraphHalfSourceExecution.execute GraphHalfSourceExecution.produce GraphHalfSourceSetup.execute
  HalfSourceDispatch.prepare GraphHalfSourceBackend.concreteTable HalfSourceBatchFit.block HalfSourceBatchFit.R HalfSourceBatchFit.S

variable (scheme : RectangularBatch.Scheme) (hnum : scheme.num=861)
  (hden : scheme.den=500) (hz : scheme.z=15) (hv : scheme.Valid)

def SetupRate (κ : ℕ) (C : ℝ) : Prop :=
  ∀ᶠ n : ℕ in atTop, ∀ call : Call n, ∀ hf : EndToEndAPSP.ValidFactors call.factors,
    let out := HalfSourceDispatch.prepare n (block n) call.factors hf
    let hm := (HalfSourceDispatch.canonical n (block n) call.factors hf).2.2
    ∀ X Y T : BinaryTriangleExecution.IntTable n,
    CountedEndToEndAPSP.entryQueryBound (BinaryTriangleExecution.viewTable X)
      (BinaryTriangleExecution.viewTable Y) (BinaryTriangleExecution.viewTable T)≤n^κ →
    ((GraphHalfSourceSetup.execute out.split.plan out.plan.value hm ⟨X,Y,T⟩).operations:ℝ)≤
      C*(Real.log (n:ℝ))^17*HalfSourceComputedCosts.phaseRawSum n call

 theorem low_price {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (hm : p.m≤p.L-p.m)
    (input : BinaryFoldedFormation.Inputs n) (a b : ℕ) :
    (GraphHalfSourceExecution.execute f p hm input scheme hnum hden hz a).low=
      (GraphHalfSourceExecution.execute f p hm input scheme hnum hden hz b).low := by
  unfold GraphHalfSourceExecution.execute
  rfl

 theorem setup_eq {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (hm : p.m≤p.L-p.m)
    (input : BinaryFoldedFormation.Inputs n) (a : ℕ) :
    (GraphHalfSourceExecution.execute f p hm input scheme hnum hden hz a).setup=
      GraphHalfSourceSetup.execute f p hm input := by unfold GraphHalfSourceExecution.execute;rfl

 theorem metadata_congr (n h : ℕ) (xs ys : List ℕ)
    (hx : EndToEndAPSP.ValidFactors xs) (hy : EndToEndAPSP.ValidFactors ys)
    (he : xs=ys) (a C : ℕ) :
    (let d := HalfSourceDispatch.prepare n h xs hx
     a+(FactorValidation.validate xs).2+d.split.work+d.plan.sites+32≤C*(d.split.plan.cyclic*d.plan.value.N*d.plan.value.D)) ↔
    (let d := HalfSourceDispatch.prepare n h ys hy
     a+(FactorValidation.validate ys).2+d.split.work+d.plan.sites+32≤C*(d.split.plan.cyclic*d.plan.value.N*d.plan.value.D)) := by
  subst ys
  rfl

 theorem positive_congr {n h : ℕ} (X Y T : BinaryTriangleExecution.IntTable n)
    (xs ys : List ℕ) (hx : EndToEndAPSP.ValidFactors xs) (hy : EndToEndAPSP.ValidFactors ys)
    (he : xs=ys) (a price : ℕ) :
    (GraphHalfSourceBackend.positiveTable scheme hnum hden hz hv (h:=h) X Y T xs hx
      (a+(FactorValidation.validate xs).2) price).work=
    (GraphHalfSourceBackend.positiveTable scheme hnum hden hz hv (h:=h) X Y T ys hy
      (a+(FactorValidation.validate ys).2) price).work := by
  subst ys
  rfl

 theorem price_log (n κ A : ℕ) (hn : 3≤n) :
    (addressPrice n κ A+1:ℝ)≤(25*(unitConstant κ A+1):ℝ)*(Real.log n)^2 := by
  have ha := addressPrice_poly n κ A
  have hs := BinaryAPSPPublicCostBounds.size_add_one_le_log n hn
  have hpow := pow_le_pow_left₀ (Nat.cast_nonneg (n.size+1)) hs 2
  push_cast at hpow
  have hp : 1≤(n.size+1)^2 := Nat.one_le_pow _ _ (by omega)
  have hh : addressPrice n κ A+1≤(unitConstant κ A+1)*(n.size+1)^2 := by nlinarith only[ha,hp]
  have hhR : (addressPrice n κ A:ℝ)+1≤(unitConstant κ A+1:ℝ)*(n.size+1:ℝ)^2 := by exact_mod_cast hh
  calc
    _ ≤(unitConstant κ A+1:ℝ)*(n.size+1:ℝ)^2 := hhR
    _ ≤(unitConstant κ A+1:ℝ)*(5*Real.log n)^2 := mul_le_mul_of_nonneg_left hpow (by positivity)
    _ =_ := by ring

 theorem metadata_phase (n : ℕ) (call : Call n) (hn : 3≤n)
    (hf : EndToEndAPSP.ValidFactors call.factors) (selected : List ℕ) (candidate : ℕ)
    (he : call.factors=selected++[candidate]) :
    let out := HalfSourceDispatch.prepare n (block n) call.factors hf
    ((BinaryTriangleExecution.historySites selected+(FactorValidation.validate call.factors).2+
      out.split.work+out.plan.sites+32:ℕ):ℝ)≤(HalfSourceDispatchCosts.metadataCoefficient R:ℝ)*HalfSourceComputedCosts.phaseRawSum n call := by
  have hf' : EndToEndAPSP.ValidFactors (selected++[candidate]) := he ▸ hf
  have hlen : (selected++[candidate]).length≤R := by rw[←he];exact call.length_le
  have hmeta := HalfSourceDispatchCosts.metadata_bound (lt_of_lt_of_le (by decide : 0<3) hn) (block_pos n) selected candidate R hf' hlen
  have hh := (metadata_congr n (block n) (selected++[candidate]) call.factors hf' hf he.symm
    (BinaryTriangleExecution.historySites selected) (HalfSourceDispatchCosts.metadataCoefficient R)).mp hmeta
  have hform := HalfSourceDispatchCosts.formation_phase n call hn hf
  have hx := (Nat.cast_le (α:=ℝ)).mpr hh
  push_cast at hx
  simpa only[Nat.cast_add,Nat.cast_ofNat] using hx.trans (mul_le_mul_of_nonneg_left hform (Nat.cast_nonneg _))

 def coefficient (κ A : ℕ) (Cs Cl : ℝ) : ℝ :=
  (25*(unitConstant κ A+1):ℝ)*(Cs+2*Cl+HalfSourceHighExecutionRate.coefficient scheme κ+
    HalfSourceOutputPhaseRate.coefficient scheme κ+(HalfSourceDispatchCosts.metadataCoefficient R:ℝ))


#print axioms low_price
#print axioms setup_eq
#print axioms metadata_congr
#print axioms positive_congr
#print axioms price_log
#print axioms metadata_phase

 theorem phase_prices (κ A : ℕ) (Cs Cl : ℝ) (hCs : 0<Cs) (hCl : 0<Cl)
    (hsetup : SetupRate κ Cs) (hlow : HalfSourceLowPhaseRate.Bound scheme hnum hden hz Cl) :
    GraphHalfSourceHostCosts.phasePrices scheme hnum hden hz hv κ A 42 (coefficient scheme κ A Cs Cl) := by
  filter_upwards [hsetup,hlow,HalfSourceHighExecutionRate.eventual scheme hnum hden hz κ,
    eventually_ge_atTop (3:ℕ)] with n hs hl hh hn
  intro X Y T hentry call hf selected candidate hhistory active
  let out := HalfSourceDispatch.prepare n (block n) call.factors hf
  let f := out.split.plan
  let p := out.plan.value
  let hm := (HalfSourceDispatch.canonical n (block n) call.factors hf).2.2
  let input : BinaryFoldedFormation.Inputs n := ⟨X,Y,T⟩
  let price := addressPrice n κ A
  have hprice0 : 0≤(price+1:ℝ) := add_nonneg (Nat.cast_nonneg price) (by norm_num)
  let execution := GraphHalfSourceExecution.execute f p hm input scheme hnum hden hz price
  let P : ℝ := HalfSourceComputedCosts.phaseRawSum n call
  let ell : ℝ := Real.log n
  have hP : 0≤P := HalfSourceComputedCosts.phaseRawSum_nonneg n call
  have hel : 1≤ell := PhaseGeometry.one_le_log_nat n hn
  have h17 : ell^17≤ell^40 := pow_le_pow_right₀ hel (by decide)
  have h19 : ell^19≤ell^40 := pow_le_pow_right₀ hel (by decide)
  have h7 : ell^7≤ell^40 := pow_le_pow_right₀ hel (by decide)
  have h40 : 1≤ell^40 := one_le_pow₀ hel
  have hB := HalfSourceInputMetadata.blocks_positive (h:=block n) (lt_of_lt_of_le (by decide : 0<3) hn) (block_pos n)
  have hp := GraphHalfSourceOutputCost.produce_work f p hm input scheme hnum hden hz hv price hB
  have hs' := hs call hf X Y T hentry
  have hl' := hl call hf input (price+1)
  dsimp only at hl'
  rw[low_price scheme hnum hden hz f p hm input (price+1) price] at hl'
  push_cast at hl'
  have hh' := hh call hn hf input price
  have ho := HalfSourceOutputPhaseRate.polynomial_bound scheme n κ call hn hf price
  have hhigh : 0≤HalfSourceHighExecutionRate.coefficient scheme κ := by
    unfold HalfSourceHighExecutionRate.coefficient
    have hc := HalfSourceHighBlockCost.constant_nonneg
    positivity
  have hout := (HalfSourceOutputPhaseRate.coefficient_pos scheme κ).le
  have hs40 : (price+1:ℝ)*execution.setup.operations≤Cs*(price+1)*ell^40*P := by
    change (price+1:ℝ)*(GraphHalfSourceExecution.execute f p hm input scheme hnum hden hz price).setup.operations≤_
    rw[setup_eq scheme hnum hden hz]
    have hx := mul_le_mul_of_nonneg_left hs' hprice0
    calc
      _ ≤(price+1:ℝ)*(Cs*ell^17*P) := hx
      _ ≤(price+1:ℝ)*(Cs*ell^40*P) := by gcongr
      _ =_ := by ring
  have hl40 : (execution.low.bitSteps:ℝ)+(price+1:ℝ)*execution.low.control≤2*Cl*(price+1)*ell^40*P := by
    have hprice : (price:ℝ)+1+1≤2*(price+1:ℝ) := by linarith[Nat.cast_nonneg (α:=ℝ) price]
    calc
      _ ≤Cl*((price:ℝ)+1+1)*ell^19*P := hl'
      _ ≤Cl*(2*(price+1:ℝ))*ell^40*P := by gcongr
      _ =_ := by ring
  have hh40 : (price+1:ℝ)*execution.high.operations≤HalfSourceHighExecutionRate.coefficient scheme κ*(price+1)*ell^40*P := by
    have hx := mul_le_mul_of_nonneg_left hh' hprice0
    simpa only[mul_assoc,mul_comm,mul_left_comm] using hx
  have ho40 : 10000000000*(price+1:ℝ)*(EndToEndAPSP.incidenceSize n (block n)+1:ℝ)*
      (GraphHalfSourceOutputCost.width f p:ℝ)^7≤HalfSourceOutputPhaseRate.coefficient scheme κ*(price+1)*ell^40*P :=
    ho.trans (by gcongr)
  have hproduced : ((GraphHalfSourceExecution.produce f p hm input scheme hnum hden hz hv price).work:ℝ)≤
      (Cs+2*Cl+HalfSourceHighExecutionRate.coefficient scheme κ+HalfSourceOutputPhaseRate.coefficient scheme κ)*(price+1)*ell^40*P := by
    have hpR := (Nat.cast_le (α:=ℝ)).mpr hp
    push_cast at hpR
    change _≤(price+1:ℝ)*execution.setup.operations+execution.low.bitSteps+(price+1:ℝ)*execution.low.control+
      (price+1:ℝ)*execution.high.operations+_ at hpR
    nlinarith only[hpR,hs40,hl40,hh40,ho40]
  have hf' : EndToEndAPSP.ValidFactors (selected++[candidate]) := hhistory ▸ hf
  have hmetaR := metadata_phase n call hn hf selected candidate hhistory
  change ((BinaryTriangleExecution.historySites selected+(FactorValidation.validate call.factors).2+
      out.split.work+out.plan.sites+32:ℕ):ℝ)≤(HalfSourceDispatchCosts.metadataCoefficient R:ℝ)*P at hmetaR
  have hm40 : (price+1:ℝ)*((BinaryTriangleExecution.historySites selected+(FactorValidation.validate call.factors).2+
      out.split.work+out.plan.sites+32:ℕ):ℝ)≤(HalfSourceDispatchCosts.metadataCoefficient R:ℝ)*(price+1)*ell^40*P := by
    have hx := mul_le_mul_of_nonneg_left hmetaR hprice0
    have hy := mul_le_mul_of_nonneg_left h40 (mul_nonneg (mul_nonneg (Nat.cast_nonneg (HalfSourceDispatchCosts.metadataCoefficient R)) hprice0) hP)
    nlinarith only[hx,hy]
  have htotal : ((GraphHalfSourceBackend.concreteTable scheme hnum hden hz hv X Y T selected candidate active price).work:ℝ)≤
      (Cs+2*Cl+HalfSourceHighExecutionRate.coefficient scheme κ+HalfSourceOutputPhaseRate.coefficient scheme κ+
        (HalfSourceDispatchCosts.metadataCoefficient R:ℝ))*(price+1)*ell^40*P := by
    rw[GraphHalfSourceBackend.concreteTable_of_valid scheme hnum hden hz hv X Y T selected candidate active price hf']
    rw[positive_congr scheme hnum hden hz hv X Y T (selected++[candidate]) call.factors hf' hf hhistory.symm
      (BinaryTriangleExecution.historySites selected) price]
    unfold GraphHalfSourceBackend.positiveTable
    change (((GraphHalfSourceExecution.produce f p hm input scheme hnum hden hz hv price).work+
      (price+1)*(BinaryTriangleExecution.historySites selected+(FactorValidation.validate call.factors).2+
        out.split.work+out.plan.sites+32):ℕ):ℝ)≤_
    push_cast at hm40 ⊢
    nlinarith only[hproduced,hm40]
  have hprice := price_log n κ A hn
  have hcoef : 0≤Cs+2*Cl+HalfSourceHighExecutionRate.coefficient scheme κ+
      HalfSourceOutputPhaseRate.coefficient scheme κ+(HalfSourceDispatchCosts.metadataCoefficient R:ℝ) := by positivity
  calc
    _ ≤(Cs+2*Cl+HalfSourceHighExecutionRate.coefficient scheme κ+HalfSourceOutputPhaseRate.coefficient scheme κ+
        (HalfSourceDispatchCosts.metadataCoefficient R:ℝ))*(price+1)*ell^40*P := htotal
    _ ≤(Cs+2*Cl+HalfSourceHighExecutionRate.coefficient scheme κ+HalfSourceOutputPhaseRate.coefficient scheme κ+
        (HalfSourceDispatchCosts.metadataCoefficient R:ℝ))*((25*(unitConstant κ A+1):ℝ)*ell^2)*ell^40*P := by gcongr
    _ =_ := by unfold coefficient;ring

#print axioms low_price
#print axioms price_log
#print axioms phase_prices
end
end ThinMatrix.HalfSourceBackendCostAssembly
