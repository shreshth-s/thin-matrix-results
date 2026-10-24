import GraphHalfSourceBackend
import HalfSourcePreparedSetup
import HalfSourceCallbackCosts

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 10000

/-! Composition of actual exact-half callback counters. The local phase
price remains explicit here and is discharged by the production cost proof. -/
namespace ThinMatrix.GraphHalfSourcePreparedCosts
open Filter Asymptotics BinaryTriangleExecution HalfSourceBatchFit HalfSourcePrimeParameters
open HalfSourceCallbackBudget HalfSourceComputedCosts
noncomputable section
attribute [local irreducible] HalfSourceBatchFit.R HalfSourceBatchFit.S HalfSourceBatchFit.block

def setupCoefficient (κ A : ℕ) : ℝ :=
  ((unitConstant κ A*(16*κ+500):ℕ):ℝ)*BinaryTriangleCosts.FixedPrices.sizeLogConstant^3*
    AlignedAPSPCosts.ControllerCosts.referenceControllerConstant R

def setupOverhead (κ A n : ℕ) : ℝ :=
  setupCoefficient κ A*(Real.log (n:ℝ))^8*(n:ℝ)^(3-(b-eta))

theorem setup_price {n U κ A : ℕ} {Payload : Type} (hn : 3≤n)
    (parameters : CompleteAPSP.Parameters (block n) U) (hp : program n U=some parameters)
    (hU : U≤n^κ) (backend : Backend n (block n) Payload)
    (labels : Vector ℕ parameters.pool.card) (hl : labels=EndToEndAPSP.primeVector parameters.pool) :
    let p := prepareOracleFromPrimes backend parameters labels hl (addressPrice n κ A)
    (p.setupBits:ℝ)+(addressPrice n κ A:ℝ)*p.setupControl≤ setupOverhead κ A n := by
  have hs := HalfSourcePreparedSetup.fromPrimes_setup_price (κ:=κ) (degree:=A) hn parameters hp hU backend labels hl
  have hsR : (((prepareOracleFromPrimes backend parameters labels hl (addressPrice n κ A)).setupBits:ℕ):ℝ)+
      (addressPrice n κ A:ℝ)*(prepareOracleFromPrimes backend parameters labels hl (addressPrice n κ A)).setupControl≤
      ((unitConstant κ A*(16*κ+500):ℕ):ℝ)*(n.size+1:ℝ)^3*
        (BinaryTriangleCosts.referenceBudget n (block n) parameters.pool.card parameters.k parameters.stages:ℝ) := by
    exact_mod_cast hs
  have hd := program_sound n U parameters hp
  have hk : parameters.k≤R := by rw[hd.2.2.2.1];exact Nat.sub_le _ _
  have hr := HalfSourceControllerBudget.computed_referenceControllerBudget_le R parameters.k n hn hk
  have hr' : (BinaryTriangleCosts.referenceBudget n (block n) parameters.pool.card parameters.k parameters.stages:ℝ)≤
      AlignedAPSPCosts.ControllerCosts.referenceControllerConstant R*(Real.log (n:ℝ))^5*(n:ℝ)^(3-(b-eta)) := by
    rw[hd.1,hd.2.2.2.2.2]
    exact hr
  have hu := BinaryTriangleCosts.FixedPrices.sizeFactor_le_log (unitConstant κ A*(16*κ+500)) 3 n hn
  push_cast at hu
  have hnon : 0≤(BinaryTriangleCosts.referenceBudget n (block n) parameters.pool.card parameters.k parameters.stages:ℝ) := Nat.cast_nonneg _
  have hc : 0≤((unitConstant κ A*(16*κ+500):ℕ):ℝ)*BinaryTriangleCosts.FixedPrices.sizeLogConstant^3*(Real.log (n:ℝ))^3 := by
    unfold BinaryTriangleCosts.FixedPrices.sizeLogConstant
    positivity
  push_cast at hc
  have hh := mul_le_mul hu hr' hnon hc
  apply hsR.trans
  simpa only [setupOverhead,setupCoefficient,Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat,pow_succ,pow_zero,mul_one,one_mul,mul_assoc,mul_comm,mul_left_comm] using hh

def price (κ A k : ℕ) (C : ℝ) (n : ℕ) : ℝ :=
  (6*(R:ℝ)*C)*(Real.log (n:ℝ))^(k+1)*allPhaseLedger n+
    HalfSourceCallbackCosts.overhead κ A n+setupOverhead κ A n

variable (scheme : RectangularBatch.Scheme) (hnum : scheme.num=861) (hden : scheme.den=500)
  (hz : scheme.z=15) (hv : scheme.Valid)

theorem prepared_price {n U κ A : ℕ} (hn : 3≤n)
    (parameters : CompleteAPSP.Parameters (block n) U) (hp : program n U=some parameters)
    (hU : U≤n^κ) (labels : Vector ℕ parameters.pool.card)
    (hl : labels=EndToEndAPSP.primeVector parameters.pool)
    (X Y T : IntTable n) (hcap : CountedEndToEndAPSP.entryQueryBound (viewTable X) (viewTable Y) (viewTable T)≤U)
    (C : ℝ) (k : ℕ) (hC : 0≤C)
    (hphase : ∀ phase : Call n,EndToEndAPSP.ValidFactors phase.factors →
      ∀ (selected : List ℕ) (candidate : ℕ),phase.factors=selected++[candidate] →
      ∀ active : ArrayCompositeAlgorithm.Flags (EndToEndAPSP.incidenceSize n (block n)),
      ((GraphHalfSourceBackend.concreteTable scheme hnum hden hz hv X Y T selected candidate active (addressPrice n κ A)).work:ℝ)≤
        C*(Real.log (n:ℝ))^k*phaseRawSum n phase) :
    let backend := GraphHalfSourceBackend.concreteBackend scheme hnum hden hz hv n (block n) (addressPrice n κ A) (block_pos n)
    let p := prepareOracleFromPrimes backend parameters labels hl (addressPrice n κ A)
    (p.setupBits:ℝ)+(addressPrice n κ A:ℝ)*p.setupControl+(p.oracle X Y T).work+
      (p.oracle X Y T).answerWrites≤price κ A k C n := by
  let backend := GraphHalfSourceBackend.concreteBackend scheme hnum hden hz hv n (block n) (addressPrice n κ A) (block_pos n)
  let static := (setupStaticFromPrimes (n:=n) parameters labels hl).value
  have hs := setup_price (A:=A) hn parameters hp hU backend labels hl
  have hc := HalfSourceCallbackCosts.callback_price (addressCoefficient:=A) hn parameters hp hU backend static X Y T
    (GraphHalfSourceBackend.concreteOracle_countsBound scheme hnum hden hz hv (block_pos n) X Y T (addressPrice n κ A)) hcap
  have hb := HalfSourceBackendAggregation.solve_backend_le_ledger hn backend parameters hp static X Y T C k hC hphase
  dsimp only
  change _≤price κ A k C n
  change ((prepareOracleFromPrimes backend parameters labels hl (addressPrice n κ A)).setupBits:ℝ)+
    (addressPrice n κ A:ℝ)*(prepareOracleFromPrimes backend parameters labels hl (addressPrice n κ A)).setupControl+
    (callback backend parameters static (addressPrice n κ A) X Y T).work+
    (callback backend parameters static (addressPrice n κ A) X Y T).answerWrites≤_
  unfold price
  dsimp only at hs hc
  linarith only [hs,hc,hb]

theorem setup_bigO (κ A k : ℕ) :
    (fun n : ℕ=>(Real.log (n:ℝ))^k*setupOverhead κ A n) =O[atTop]
      (fun n : ℕ=>(n:ℝ)^(14963431313/5000000000:ℝ)) := by
  have hg : 3-(b-eta)<(14963431313/5000000000:ℝ) := by
    norm_num [b,eta,bNumerator,bDenominator,HalfSourceBatchFit.R]
  have hh := (AsymptoticCosts.logPowMulRpowBigO hg (k+8)).const_mul_left (setupCoefficient κ A)
  simpa only [setupOverhead,pow_add,mul_assoc,mul_comm,mul_left_comm] using hh

theorem price_bigO (κ A k j : ℕ) (C : ℝ) :
    (fun n : ℕ=>(Real.log (n:ℝ))^j*price κ A k C n) =O[atTop]
      (fun n : ℕ=>(n:ℝ)^(14963431313/5000000000:ℝ)) := by
  have hm := (allPhaseLedgerBigO (j+(k+1))).const_mul_left (6*(R:ℝ)*C)
  have hc := HalfSourceCallbackCosts.overhead_bigO κ A j
  have hs := setup_bigO κ A j
  simpa only [price,mul_add,pow_add,mul_assoc,mul_comm,mul_left_comm] using (hm.add hc).add hs

#print axioms setup_price
#print axioms prepared_price
#print axioms setup_bigO
#print axioms price_bigO
end
end ThinMatrix.GraphHalfSourcePreparedCosts
