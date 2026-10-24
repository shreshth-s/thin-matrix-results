import HalfSourceParameters
import AsymptoticCosts

/-! Seven-term exact-half phase ledger. This certifies the actual real
expressions and every intermediate prime stage, including candidates, full
cyclic coefficient costs, source roots and the independent batching fit.
It does not assert that the production scheduler's counters satisfy this
ledger; that connection must be proved from its executable implementation. -/
namespace ThinMatrix.HalfSourcePhaseCosts
open HalfSourceParameters
open Filter Asymptotics
open scoped BigOperators
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

def slack : ℝ := 1/100000000000

theorem slack_pos : 0 < slack := by norm_num [slack]

def saving (x z : ℝ) (i : Fin 7) : ℝ :=
  ![b-x-z+(b+x)*G-eta,
    b-z-(b+x)*Q-beta*((b+x)*zeta)-eta,
    b-(b+x)*q2-eta,
    1+b-x/2-z-(b+x)*(T+Q)+A*((b+x)*zeta)-eta,
    1+b-x/2-z-(b+x)*Ebox-eta,
    1+b-x/2-z-(b+x)*Eroot-eta,
    1-3*x/2-z-eta] i

def geometry (x : ℝ) : ℝ := 1+x/2-(b+x)*T
def batchFit (x z : ℝ) : ℝ := 1-b+z-15*((b+x)*zeta)

def endpointX (p : Fin 4) : ℝ := ![0,u,u,u] p
def endpointZ (p : Fin 4) : ℝ := ![0,0,0,v] p

theorem endpointMargins (p : Fin 4) (i : Fin 7) :
    delta+slack < saving (endpointX p) (endpointZ p) i := by
  have ht := TEnclosure
  have hg := GEnclosure
  have hq := QEnclosure
  have ha := AEnclosure
  have hr := ErootEnclosure
  fin_cases p <;> fin_cases i <;>
    norm_num [saving,endpointX,endpointZ,b,u,v,eta,delta,slack,q2,Ebox,theta,beta,zeta] <;>
    linarith

theorem endpointGeometry (p : Fin 4) : slack < geometry (endpointX p) := by
  have ht := TEnclosure
  fin_cases p <;> norm_num [geometry,endpointX,b,u,slack] <;> linarith

theorem endpointBatchFit (p : Fin 4) : slack < batchFit (endpointX p) (endpointZ p) := by
  fin_cases p <;> norm_num [batchFit,endpointX,endpointZ,b,u,v,zeta,slack]

theorem bookkeepingMargin : delta+slack < b-eta := by
  norm_num [delta,slack,b,eta]

theorem stageRelations : 0 ≤ eta ∧ u=(S:ℝ)*eta ∧ v=((R-S:ℕ):ℝ)*eta ∧
    u+v=b ∧ e=b+u ∧ S≤R := by
  norm_num [eta,u,v,R,S,b,e]

private theorem affineIntervalLower (a d hi x low : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ hi)
    (hlo : low ≤ a+d*0) (hhi : low ≤ a+d*hi) : low ≤ a+d*x := by
  by_cases hd : 0 ≤ d
  · have hm := mul_le_mul_of_nonneg_left hx0 hd
    linarith
  · have hm := mul_le_mul_of_nonpos_left hx1 (le_of_not_ge hd)
    linarith

def scalarSlope (i : Fin 7) : ℝ :=
  ![G-1,-Q-beta*zeta,-q2,-1/2-(T+Q)+A*zeta,
    -1/2-Ebox,-1/2-Eroot,-3/2] i

def cyclicSlope (i : Fin 7) : ℝ := ![-1,-1,0,-1,-1,-1,-1] i

theorem scalarAffine (x : ℝ) (i : Fin 7) :
    saving x 0 i=saving 0 0 i+scalarSlope i*x := by
  fin_cases i <;> simp [saving,scalarSlope] <;> ring

theorem cyclicAffine (z : ℝ) (i : Fin 7) :
    saving u z i=saving u 0 i+cyclicSlope i*z := by
  fin_cases i <;> simp [saving,cyclicSlope] <;> ring

theorem scalarAllStages (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ u) (i : Fin 7) :
    delta+slack ≤ saving x 0 i := by
  rw [scalarAffine]
  apply affineIntervalLower _ _ u x _ hx0 hx1
  · simpa [endpointX,endpointZ] using (endpointMargins 0 i).le
  · rw [←scalarAffine]
    simpa [endpointX,endpointZ] using (endpointMargins 1 i).le

theorem cyclicAllStages (z : ℝ) (hz0 : 0 ≤ z) (hz1 : z ≤ v) (i : Fin 7) :
    delta+slack ≤ saving u z i := by
  rw [cyclicAffine]
  apply affineIntervalLower _ _ v z _ hz0 hz1
  · simpa [endpointX,endpointZ] using (endpointMargins 2 i).le
  · rw [←cyclicAffine]
    simpa [endpointX,endpointZ] using (endpointMargins 3 i).le

theorem geometryAllStages (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ u) :
    slack ≤ geometry x := by
  have heq (y : ℝ) : geometry y=geometry 0+(1/2-T)*y := by unfold geometry; ring
  rw [heq]
  apply affineIntervalLower _ _ u x _ hx0 hx1
  · simpa [endpointX] using (endpointGeometry 0).le
  · rw [←heq]
    simpa [endpointX] using (endpointGeometry 1).le

theorem scalarBatchAllStages (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ u) :
    slack ≤ batchFit x 0 := by
  have heq (y : ℝ) : batchFit y 0=batchFit 0 0+(-15*zeta)*y := by unfold batchFit; ring
  rw [heq]
  apply affineIntervalLower _ _ u x _ hx0 hx1
  · simpa [endpointX,endpointZ] using (endpointBatchFit 0).le
  · rw [←heq]
    simpa [endpointX,endpointZ] using (endpointBatchFit 1).le

theorem cyclicBatchAllStages (z : ℝ) (hz0 : 0 ≤ z) (hz1 : z ≤ v) :
    slack ≤ batchFit u z := by
  have heq (y : ℝ) : batchFit u y=batchFit u 0+1*y := by unfold batchFit; ring
  rw [heq]
  apply affineIntervalLower _ _ v z _ hz0 hz1
  · simpa [endpointX,endpointZ] using (endpointBatchFit 2).le
  · rw [←heq]
    simpa [endpointX,endpointZ] using (endpointBatchFit 3).le

/-- The selected factors and currently tested candidate remain charged at
all stages, not only at the final composite modulus. -/
def stageSaving (j : Fin (R+1)) (i : Fin 7) : ℝ :=
  if j.val ≤ S then saving ((j.val:ℝ)*eta) 0 i
  else saving u (((j.val-S:ℕ):ℝ)*eta) i

theorem stageUniformSlack (j : Fin (R+1)) (i : Fin 7) :
    delta+slack ≤ stageSaving j i := by
  have heta := stageRelations.1
  have hu := stageRelations.2.1
  have hv := stageRelations.2.2.1
  have hjR : j.val ≤ R := Nat.le_of_lt_succ j.isLt
  unfold stageSaving
  split_ifs with hj
  · apply scalarAllStages _ (mul_nonneg (Nat.cast_nonneg _) heta) _ i
    rw [hu]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hj) heta
  · apply cyclicAllStages _ (mul_nonneg (Nat.cast_nonneg _) heta) _ i
    rw [hv]
    apply mul_le_mul_of_nonneg_right _ heta
    exact_mod_cast Nat.sub_le_sub_right hjR S

def targetExponent : ℝ := 3-delta

theorem targetValue : targetExponent=14963431313/5000000000 := by
  norm_num [targetExponent,delta]

theorem targetAboveTwo : 2 < targetExponent := by rw [targetValue]; norm_num

theorem stageExponentStrict (j : Fin (R+1)) (i : Fin 7) :
    3-stageSaving j i < targetExponent := by
  have h := stageUniformSlack j i
  unfold targetExponent
  linarith [slack_pos]

theorem bookkeepingExponentStrict : 3-(b-eta)<targetExponent := by
  unfold targetExponent
  linarith [bookkeepingMargin,slack_pos]

/-- Algebraic ledger for all seven charged terms and all prime stages.
The logarithmic degree is arbitrary and hence includes fixed translations,
windows, padding, coefficient bits, restarts and repeated squaring whenever
those are separately shown to contribute only that fixed degree. -/
def completeCost (k n : ℕ) : ℝ :=
  ((R:ℝ)+1)^2*(Real.log (n:ℝ))^(k+R+10)*
    (AsymptoticCosts.roundedPower 2 n+
      AsymptoticCosts.roundedPower (3-(b-eta)) n+
      ∑ j : Fin (R+1), ∑ i : Fin 7,
        AsymptoticCosts.roundedPower (3-stageSaving j i) n)

theorem completeCostBigO (k : ℕ) :
    completeCost k =O[atTop] (fun n : ℕ => (n:ℝ)^targetExponent) := by
  let K := k+R+10
  have hd : 0 < targetExponent := lt_trans (by norm_num) targetAboveTwo
  have hscan := AsymptoticCosts.roundedLogPowBigO targetAboveTwo hd K
  have hbook := AsymptoticCosts.roundedLogPowBigO bookkeepingExponentStrict hd K
  have hstages : (fun n : ℕ => ∑ j : Fin (R+1), ∑ i : Fin 7,
      (Real.log (n:ℝ))^K*AsymptoticCosts.roundedPower (3-stageSaving j i) n)
      =O[atTop] (fun n : ℕ => (n:ℝ)^targetExponent) := by
    apply Asymptotics.IsBigO.sum
    intro j _
    apply Asymptotics.IsBigO.sum
    intro i _
    exact AsymptoticCosts.roundedLogPowBigO (stageExponentStrict j i) hd K
  have h := ((hscan.add hbook).add hstages).const_mul_left (((R:ℝ)+1)^2)
  change (fun n : ℕ => ((R:ℝ)+1)^2*(Real.log (n:ℝ))^(k+R+10)*
    (AsymptoticCosts.roundedPower 2 n+
      AsymptoticCosts.roundedPower (3-(b-eta)) n+
      ∑ j : Fin (R+1), ∑ i : Fin 7,
        AsymptoticCosts.roundedPower (3-stageSaving j i) n)) =O[atTop] _
  simpa only [K,mul_add,Finset.mul_sum,mul_assoc] using h

theorem completeCostNonnegative (k n : ℕ) (hn : 1 ≤ n) : 0 ≤ completeCost k n := by
  have hnR : 1 ≤ (n:ℝ) := by exact_mod_cast hn
  have hl := Real.log_nonneg hnR
  unfold completeCost AsymptoticCosts.roundedPower
  positivity

/-- Explicit remaining interface: no scheduler-cost premise is discharged
by the numerical ledger itself. -/
theorem costBoundOfEventualDomination (time : ℕ → ℕ) (k : ℕ) (C : ℝ)
    (hdom : ∀ᶠ n : ℕ in atTop, (time n:ℝ) ≤ C*completeCost k n) :
    (fun n => (time n:ℝ)) =O[atTop]
      (fun n : ℕ => (n:ℝ)^(14963431313/5000000000:ℝ)) := by
  have h : (fun n => (time n:ℝ)) =O[atTop] completeCost k := by
    apply IsBigO.of_bound C
    filter_upwards [hdom,eventually_ge_atTop (1:ℕ)] with n hb hn
    simpa only [Real.norm_of_nonneg (Nat.cast_nonneg (time n)),
      Real.norm_of_nonneg (completeCostNonnegative k n hn)] using hb
  simpa only [targetValue] using h.trans (completeCostBigO k)

#print axioms endpointMargins
#print axioms endpointGeometry
#print axioms endpointBatchFit
#print axioms bookkeepingMargin
#print axioms stageRelations
#print axioms scalarAllStages
#print axioms cyclicAllStages
#print axioms geometryAllStages
#print axioms scalarBatchAllStages
#print axioms cyclicBatchAllStages
#print axioms stageUniformSlack
#print axioms stageExponentStrict
#print axioms completeCostBigO
#print axioms costBoundOfEventualDomination
end
end ThinMatrix.HalfSourcePhaseCosts
