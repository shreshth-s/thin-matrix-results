import RealCertificate
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
Asymptotic composition of the aligned witness's explicit cost ledger.
This file does not assert that an APSP algorithm is implemented or that its
execution cost is bounded by the ledger. That domination is a separate interface.
Candidate-prime work, both encoders, cyclic coefficients, fixed stage counts,
fixed logarithmic powers and upward integer rounding are included below.
-/

namespace ThinMatrix.AsymptoticCosts
noncomputable section
open Filter Asymptotics
open scoped BigOperators
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000

private theorem listUniformPositive {α : Type*} (cs : List α) (margin : α → ℝ)
    (h : ∀ c ∈ cs, 0 < margin c) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ c ∈ cs, ε ≤ margin c := by
  revert h
  induction cs with
  | nil =>
    intro _
    exact ⟨1, by norm_num, by simp⟩
  | cons c cs ih =>
    intro h
    have hc : 0 < margin c := h c (by simp)
    have ht : ∀ d ∈ cs, 0 < margin d := by
      intro d hd
      exact h d (by simp [hd])
    obtain ⟨ε, hε, hb⟩ := ih ht
    refine ⟨min (margin c) ε, lt_min hc hε, ?_⟩
    intro d hd
    rcases List.mem_cons.mp hd with rfl | hd
    · exact min_le_left _ _
    · exact le_trans (min_le_right _ _) (hb d hd)

theorem existsUniformSlack : ∃ ε : ℝ, 0 < ε ∧
    ∀ check ∈ AlignedCertificate.checks,
      (check.target : ℝ) + ε ≤ RealCertificate.evalReal check.expression := by
  obtain ⟨ε, hε, hb⟩ := listUniformPositive AlignedCertificate.checks
    (fun check => RealCertificate.evalReal check.expression - (check.target : ℝ))
    (by intro check hm; exact sub_pos.mpr (RealCertificate.allActualRealCosts check hm))
  refine ⟨ε, hε, ?_⟩
  intro check hm
  have := hb check hm
  linarith

def slack : ℝ := Classical.choose existsUniformSlack
theorem slackPositive : 0 < slack := (Classical.choose_spec existsUniformSlack).1
theorem checkSlack (check : AlignedCertificate.Check) (hm : check ∈ AlignedCertificate.checks) :
    (check.target : ℝ) + slack ≤ RealCertificate.evalReal check.expression :=
  (Classical.choose_spec existsUniformSlack).2 check hm

def b : ℝ := (AlignedCertificate.b : ℝ)
def eta : ℝ := (AlignedCertificate.eta : ℝ)
def u : ℝ := (AlignedCertificate.u : ℝ)
def v : ℝ := (AlignedCertificate.v : ℝ)
def e : ℝ := (AlignedCertificate.e : ℝ)
def delta : ℝ := (AlignedCertificate.delta : ℝ)
def targetExponent : ℝ := 3 - delta

theorem targetValue : targetExponent = 299294792 / 100000000 := by
  norm_num [targetExponent, delta, AlignedCertificate.delta]

def scalarSaving (x : ℝ) (i : Fin 6) : ℝ :=
  ![b-x+(b+x)*RealCertificate.G-eta,
    b-(b+x)*RealCertificate.q1-eta,
    b-(b+x)*RealCertificate.q2-eta,
    1+b-x/2-(b+x)*RealCertificate.Esource-eta,
    1+b-x/2-(b+x)*RealCertificate.Ebox-eta,
    1-3*x/2-eta] i

def cyclicSaving (z : ℝ) (i : Fin 6) : ℝ :=
  ![b-u-z+e*RealCertificate.G-eta,
    b-z-e*RealCertificate.q1-eta,
    b-e*RealCertificate.q2-eta,
    1+b-u/2-z-e*RealCertificate.Esource-eta,
    1+b-u/2-z-e*RealCertificate.Ebox-eta,
    1-3*u/2-z-eta] i

private theorem scalarEndpoint (x : Rat) (tag : String)
    (hm : ∀ ch ∈ AlignedCertificate.scalarPhase x tag, ch ∈ AlignedCertificate.checks)
    (i : Fin 6) : delta + slack ≤ scalarSaving (x : ℝ) i := by
  let ch := (AlignedCertificate.scalarPhase x tag)[i.val]'(by
    simp only [AlignedCertificate.scalarPhase, List.length_cons, List.length_nil]
    omega)
  have hc := checkSlack ch (hm ch (List.getElem_mem _))
  fin_cases i <;>
    norm_num [ch, AlignedCertificate.scalarPhase, RealCertificate.evalReal, scalarSaving,
      b, eta, delta, RealCertificate.q2Identity, RealCertificate.Esource,
      RealCertificate.Ebox, RealCertificate.theta, AlignedCertificate.theta] at hc ⊢ <;>
    linarith

private theorem cyclicEndpoint (z : Rat) (tag : String)
    (hm : ∀ ch ∈ AlignedCertificate.cyclicPhase z tag, ch ∈ AlignedCertificate.checks)
    (i : Fin 6) : delta + slack ≤ cyclicSaving (z : ℝ) i := by
  let ch := (AlignedCertificate.cyclicPhase z tag)[i.val]'(by
    simp only [AlignedCertificate.cyclicPhase, List.length_cons, List.length_nil]
    omega)
  have hc := checkSlack ch (hm ch (List.getElem_mem _))
  fin_cases i <;>
    norm_num [ch, AlignedCertificate.cyclicPhase, RealCertificate.evalReal, cyclicSaving,
      b, eta, delta, u, e, RealCertificate.q2Identity, RealCertificate.Esource,
      RealCertificate.Ebox, RealCertificate.theta, AlignedCertificate.theta] at hc ⊢ <;>
    linarith

theorem scalarEndpoints (i : Fin 6) :
    delta + slack ≤ scalarSaving 0 i ∧ delta + slack ≤ scalarSaving u i := by
  constructor
  · simpa using scalarEndpoint 0 "initial"
      (by intro ch hm; simp only [AlignedCertificate.checks, List.mem_append]; aesop) i
  · exact scalarEndpoint AlignedCertificate.u "freeze"
      (by intro ch hm; simp only [AlignedCertificate.checks, List.mem_append]; aesop) i

theorem cyclicEndpoints (i : Fin 6) :
    delta + slack ≤ cyclicSaving 0 i ∧ delta + slack ≤ cyclicSaving v i := by
  constructor
  · simpa using cyclicEndpoint 0 "start"
      (by intro ch hm; simp only [AlignedCertificate.checks, List.mem_append]; aesop) i
  · exact cyclicEndpoint AlignedCertificate.v "final"
      (by intro ch hm; simp only [AlignedCertificate.checks, List.mem_append]; aesop) i

private theorem affineIntervalLower (A B hi x L : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ hi)
    (hlo : L ≤ A+B*0) (hhi : L ≤ A+B*hi) : L ≤ A+B*x := by
  by_cases hB : 0 ≤ B
  · have hm := mul_le_mul_of_nonneg_left hx0 hB
    linarith
  · have hm := mul_le_mul_of_nonpos_left hx1 (le_of_not_ge hB)
    linarith

def scalarSlope (i : Fin 6) : ℝ :=
  ![RealCertificate.G-1, -RealCertificate.q1, -RealCertificate.q2,
    -1/2-RealCertificate.Esource, -1/2-RealCertificate.Ebox, -3/2] i

def cyclicSlope (i : Fin 6) : ℝ := ![-1,-1,0,-1,-1,-1] i

theorem scalarAffine (x : ℝ) (i : Fin 6) :
    scalarSaving x i = scalarSaving 0 i + scalarSlope i*x := by
  fin_cases i <;> simp [scalarSaving, scalarSlope] <;> ring

theorem cyclicAffine (z : ℝ) (i : Fin 6) :
    cyclicSaving z i = cyclicSaving 0 i + cyclicSlope i*z := by
  fin_cases i <;> simp [cyclicSaving, cyclicSlope] <;> ring

theorem scalarAllStages (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ u) (i : Fin 6) :
    delta + slack ≤ scalarSaving x i := by
  rw [scalarAffine]
  apply affineIntervalLower _ _ u x _ hx0 hx1
  · simpa using (scalarEndpoints i).1
  · simpa only [← scalarAffine] using (scalarEndpoints i).2

theorem cyclicAllStages (z : ℝ) (hz0 : 0 ≤ z) (hz1 : z ≤ v) (i : Fin 6) :
    delta + slack ≤ cyclicSaving z i := by
  rw [cyclicAffine]
  apply affineIntervalLower _ _ v z _ hz0 hz1
  · simpa using (cyclicEndpoints i).1
  · simpa only [← cyclicAffine] using (cyclicEndpoints i).2

def scalarGeometry (x : ℝ) : ℝ := 1+x/2-(b+x)*RealCertificate.T
def cyclicGeometry : ℝ := 1+u/2-e*RealCertificate.T

private theorem scalarGeometryEndpoint (x : Rat) (tag : String)
    (hm : ∀ ch ∈ AlignedCertificate.scalarPhase x tag, ch ∈ AlignedCertificate.checks) :
    slack ≤ scalarGeometry (x : ℝ) := by
  let ch := (AlignedCertificate.scalarPhase x tag)[6]'(by simp [AlignedCertificate.scalarPhase])
  have hc := checkSlack ch (hm ch (List.getElem_mem _))
  norm_num [ch, AlignedCertificate.scalarPhase, RealCertificate.evalReal,
    scalarGeometry, b] at hc ⊢
  linarith

theorem scalarGeometryAllStages (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ u) :
    slack ≤ scalarGeometry x := by
  have h0 : slack ≤ scalarGeometry 0 := by
    simpa using scalarGeometryEndpoint 0 "initial"
      (by intro ch hm; simp only [AlignedCertificate.checks, List.mem_append]; aesop)
  have hu : slack ≤ scalarGeometry u := scalarGeometryEndpoint AlignedCertificate.u "freeze"
    (by intro ch hm; simp only [AlignedCertificate.checks, List.mem_append]; aesop)
  have heq (y : ℝ) : scalarGeometry y = scalarGeometry 0+(1/2-RealCertificate.T)*y := by
    unfold scalarGeometry
    ring
  rw [heq]
  apply affineIntervalLower _ _ u x _ hx0 hx1
  · simpa using h0
  · simpa only [← heq] using hu

theorem cyclicGeometrySlack : slack ≤ cyclicGeometry := by
  let ch := (AlignedCertificate.cyclicPhase 0 "start")[6]'(by
    simp [AlignedCertificate.cyclicPhase])
  have hm : ch ∈ AlignedCertificate.checks := by
    have hh := List.getElem_mem (l := AlignedCertificate.cyclicPhase 0 "start")
      (n := 6) (by simp [AlignedCertificate.cyclicPhase])
    simp only [AlignedCertificate.checks, List.mem_append]
    aesop
  have hc := checkSlack ch hm
  norm_num [ch, AlignedCertificate.cyclicPhase, RealCertificate.evalReal,
    cyclicGeometry, u, e] at hc ⊢
  linarith

theorem stageRelations : 0 ≤ eta ∧
    u = (AlignedCertificate.S : ℝ)*eta ∧
    v = ((AlignedCertificate.R-AlignedCertificate.S : ℕ) : ℝ)*eta := by
  norm_num [eta, u, v, AlignedCertificate.u, AlignedCertificate.v,
    AlignedCertificate.eta, AlignedCertificate.b, AlignedCertificate.R, AlignedCertificate.S]

/-- All selected and candidate stages, including the common endpoint. -/
def stageSaving (j : Fin (AlignedCertificate.R+1)) (i : Fin 6) : ℝ :=
  if j.val ≤ AlignedCertificate.S then scalarSaving ((j.val : ℝ)*eta) i
  else cyclicSaving (((j.val-AlignedCertificate.S : ℕ) : ℝ)*eta) i

theorem stageUniformSlack (j : Fin (AlignedCertificate.R+1)) (i : Fin 6) :
    delta + slack ≤ stageSaving j i := by
  rcases stageRelations with ⟨hη, hu, hv⟩
  have hjR : j.val ≤ AlignedCertificate.R := Nat.le_of_lt_succ j.isLt
  unfold stageSaving
  split_ifs with hj
  · apply scalarAllStages _ (mul_nonneg (Nat.cast_nonneg _) hη) _ i
    rw [hu]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hj) hη
  · apply cyclicAllStages _ (mul_nonneg (Nat.cast_nonneg _) hη) _ i
    rw [hv]
    apply mul_le_mul_of_nonneg_right _ hη
    exact_mod_cast Nat.sub_le_sub_right hjR AlignedCertificate.S

theorem bookkeepingSlack : delta + slack ≤ b-eta := by
  let ch : AlignedCertificate.Check :=
    ⟨"incidence bookkeeping after enumeration", AlignedCertificate.delta,
      ⟨AlignedCertificate.b-AlignedCertificate.eta,0,0,0⟩⟩
  have hm : ch ∈ AlignedCertificate.checks := by
    simp [ch, AlignedCertificate.checks, AlignedCertificate.regimes]
  have hc := checkSlack ch hm
  simpa [ch, delta, b, eta, RealCertificate.evalReal] using hc

theorem stageExponentStrict (j : Fin (AlignedCertificate.R+1)) (i : Fin 6) :
    3-stageSaving j i < targetExponent := by
  have hs := stageUniformSlack j i
  unfold targetExponent
  linarith [slackPositive]

theorem bookkeepingExponentStrict : 3-(b-eta) < targetExponent := by
  unfold targetExponent
  linarith [bookkeepingSlack, slackPositive]

theorem targetAboveTwo : 2 < targetExponent := by
  rw [targetValue]
  norm_num

/-- A strict power saving absorbs every fixed logarithmic power. -/
theorem logPowMulRpowBigO {a d : ℝ} (had : a < d) (k : ℕ) :
    (fun n : ℕ => (Real.log (n : ℝ))^k * (n : ℝ)^a)
      =O[atTop] (fun n : ℕ => (n : ℝ)^d) := by
  have hlogR : (fun x : ℝ => (Real.log x)^k)
      =O[atTop] (fun x : ℝ => x^(d-a)) := by
    simpa only [Real.rpow_natCast] using
      (isLittleO_log_rpow_rpow_atTop (s := d-a) (k : ℝ) (sub_pos.mpr had)).isBigO
  have hlog := hlogR.natCast_atTop
  have hp : (fun n : ℕ => (n : ℝ)^a) =O[atTop] (fun n : ℕ => (n : ℝ)^a) :=
    isBigO_refl _ _
  simpa only [Asymptotics.isBigO_iff, Real.norm_eq_abs, Pi.mul_apply] using
    IsBigO.mul_atTop_rpow_natCast_of_isBigO_rpow (d-a) a d hlog hp (by linarith)

theorem logPowMulRpowLittleO {a d : ℝ} (had : a < d) (k : ℕ) :
    (fun n : ℕ => (Real.log (n : ℝ))^k * (n : ℝ)^a)
      =o[atTop] (fun n : ℕ => (n : ℝ)^d) := by
  have hlogR : (fun x : ℝ => (Real.log x)^k)
      =o[atTop] (fun x : ℝ => x^(d-a)) := by
    simpa only [Real.rpow_natCast] using
      isLittleO_log_rpow_rpow_atTop (s := d-a) (k : ℝ) (sub_pos.mpr had)
  have hlog := hlogR.natCast_atTop
  have hp : (fun n : ℕ => (n : ℝ)^a) =O[atTop] (fun n : ℕ => (n : ℝ)^a) :=
    isBigO_refl _ _
  have hmul := hlog.mul_isBigO hp
  have heq : (fun n : ℕ => (n : ℝ)^(d-a)*(n : ℝ)^a)
      =ᶠ[atTop] (fun n : ℕ => (n : ℝ)^d) := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hnR : 0 < (n : ℝ) := lt_of_lt_of_le (zero_lt_one : (0 : ℝ) < 1)
      (show 1 ≤ (n : ℝ) by exact_mod_cast hn)
    rw [← Real.rpow_add hnR]
    congr 1
    ring
  simpa only [Asymptotics.isLittleO_iff, Real.norm_eq_abs] using
    hmul.congr' Filter.EventuallyEq.rfl heq

/-- Every fixed multiplicative/logarithmic padding fits inside a strict
geometry gap, eventually, with constant one on the available outer size. -/
theorem eventualPowerFit {a d : ℝ} (had : a < d) (k : ℕ) (C : ℝ) :
    ∀ᶠ n : ℕ in atTop,
      C*(Real.log (n : ℝ))^k*(n : ℝ)^a ≤ (n : ℝ)^d := by
  have h := (logPowMulRpowLittleO had k).const_mul_left C
  have hb := h.bound (show (0 : ℝ) < 1 by norm_num)
  filter_upwards [hb] with n hn
  calc
    C*(Real.log (n : ℝ))^k*(n : ℝ)^a
        ≤ ‖C*((Real.log (n : ℝ))^k*(n : ℝ)^a)‖ := by
          simpa only [mul_assoc, Real.norm_eq_abs] using
            le_abs_self (C*((Real.log (n : ℝ))^k*(n : ℝ)^a))
    _ ≤ 1*‖(n : ℝ)^d‖ := hn
    _ = (n : ℝ)^d := by
      rw [Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) d), one_mul]

theorem scalarTileFitsEventually (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ u)
    (k : ℕ) (C : ℝ) : ∀ᶠ n : ℕ in atTop,
    C*(Real.log (n : ℝ))^k*(n : ℝ)^((b+x)*RealCertificate.T)
      ≤ (n : ℝ)^(1+x/2) := by
  apply eventualPowerFit _ k C
  have h := scalarGeometryAllStages x hx0 hx1
  unfold scalarGeometry at h
  linarith [slackPositive]

theorem cyclicTileFitsEventually (k : ℕ) (C : ℝ) : ∀ᶠ n : ℕ in atTop,
    C*(Real.log (n : ℝ))^k*(n : ℝ)^(e*RealCertificate.T)
      ≤ (n : ℝ)^(1+u/2) := by
  apply eventualPowerFit _ k C
  have h := cyclicGeometrySlack
  unfold cyclicGeometry at h
  linarith [slackPositive]

def roundedPower (a : ℝ) (n : ℕ) : ℝ := (Nat.ceil ((n : ℝ)^a) : ℝ)

/-- Upward rounding costs at most one extra unit. Positive target exponent
is needed to absorb that unit; no unjustified ceiling identity is used. -/
theorem roundedLogPowBigO {a d : ℝ} (had : a < d) (hd : 0 < d) (k : ℕ) :
    (fun n : ℕ => (Real.log (n : ℝ))^k * roundedPower a n)
      =O[atTop] (fun n : ℕ => (n : ℝ)^d) := by
  have ha := logPowMulRpowBigO had k
  have hz := logPowMulRpowBigO (a := 0) hd k
  have hsum := ha.add hz
  have hdom : (fun n : ℕ => (Real.log (n : ℝ))^k * roundedPower a n)
      =O[atTop] (fun n : ℕ => (Real.log (n : ℝ))^k * (n : ℝ)^a +
        (Real.log (n : ℝ))^k * (n : ℝ)^(0 : ℝ)) := by
    apply IsBigO.of_norm_eventuallyLE
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hnR : 1 ≤ (n : ℝ) := by exact_mod_cast hn
    have hl : 0 ≤ (Real.log (n : ℝ))^k :=
      pow_nonneg (Real.log_nonneg hnR) _
    have hc := (Nat.ceil_lt_add_one (Real.rpow_nonneg (Nat.cast_nonneg n) a)).le
    rw [Real.norm_of_nonneg (mul_nonneg hl
      (show 0 ≤ roundedPower a n from Nat.cast_nonneg _))]
    simpa [roundedPower, Real.rpow_zero, mul_add] using mul_le_mul_of_nonneg_left hc hl
  exact hdom.trans hsum

/-- Complete algebraic ledger. The arbitrary fixed exponent `k` allows all
remaining fixed polylog overhead; `R+10` explicitly includes fixed-prime
products, restart levels, degree runs, bit scaling and repeated squaring.
The fixed prefactor includes final `O(R²)` scan bookkeeping. -/
def completeCost (k n : ℕ) : ℝ :=
  ((AlignedCertificate.R : ℝ)+1)^2 * (Real.log (n : ℝ))^(k+AlignedCertificate.R+10) *
    (roundedPower 2 n + roundedPower (3-(b-eta)) n +
      ∑ j : Fin (AlignedCertificate.R+1), ∑ i : Fin 6,
        roundedPower (3-stageSaving j i) n)

-- mathlib 4.33 names the pointwise form `fun_sum`; 4.31 calls it `sum`.
macro "aligned_cost_sum" : tactic =>
  `(tactic| first | apply Asymptotics.IsBigO.fun_sum | apply Asymptotics.IsBigO.sum)

theorem completeCostBigO (k : ℕ) :
    completeCost k =O[atTop] (fun n : ℕ => (n : ℝ)^targetExponent) := by
  let K := k+AlignedCertificate.R+10
  have hd : 0 < targetExponent := lt_trans (by norm_num) targetAboveTwo
  have hscan := roundedLogPowBigO targetAboveTwo hd K
  have hbook := roundedLogPowBigO bookkeepingExponentStrict hd K
  have hstages : (fun n : ℕ => ∑ j : Fin (AlignedCertificate.R+1), ∑ i : Fin 6,
      (Real.log (n : ℝ))^K * roundedPower (3-stageSaving j i) n)
      =O[atTop] (fun n : ℕ => (n : ℝ)^targetExponent) := by
    aligned_cost_sum
    intro j _
    aligned_cost_sum
    intro i _
    exact roundedLogPowBigO (stageExponentStrict j i) hd K
  have h := ((hscan.add hbook).add hstages).const_mul_left
    (((AlignedCertificate.R : ℝ)+1)^2)
  change (fun n : ℕ => ((AlignedCertificate.R : ℝ)+1)^2 *
    (Real.log (n : ℝ))^(k+AlignedCertificate.R+10) *
      (roundedPower 2 n + roundedPower (3-(b-eta)) n +
        ∑ j : Fin (AlignedCertificate.R+1), ∑ i : Fin 6,
          roundedPower (3-stageSaving j i) n)) =O[atTop] _
  simpa only [K, mul_add, Finset.mul_sum, mul_assoc] using h

/-- Cost-domination interface for a future algorithmic formalization. -/
theorem costBoundOfDomination (time : ℕ → ℝ) (k : ℕ)
    (hdom : time =O[atTop] completeCost k) :
    time =O[atTop] (fun n : ℕ => (n : ℝ)^(299294792 / 100000000 : ℝ)) := by
  simpa only [targetValue] using hdom.trans (completeCostBigO k)

theorem completeCostNonnegative (k n : ℕ) (hn : 1 ≤ n) : 0 ≤ completeCost k n := by
  have hnR : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hl := Real.log_nonneg hnR
  unfold completeCost roundedPower
  positivity

/-- A concrete future step-count bound suffices: the algorithmic layer only
needs an eventual pointwise domination of its natural-number operation count. -/
theorem costBoundOfEventualDomination (time : ℕ → ℕ) (k : ℕ) (C : ℝ)
    (hdom : ∀ᶠ n : ℕ in atTop, (time n : ℝ) ≤ C*completeCost k n) :
    (fun n => (time n : ℝ)) =O[atTop]
      (fun n : ℕ => (n : ℝ)^(299294792 / 100000000 : ℝ)) := by
  apply costBoundOfDomination _ k
  apply IsBigO.of_bound C
  filter_upwards [hdom, eventually_ge_atTop (1 : ℕ)] with n hb hn
  simpa only [Real.norm_of_nonneg (Nat.cast_nonneg (time n)),
    Real.norm_of_nonneg (completeCostNonnegative k n hn)] using hb

#print axioms existsUniformSlack
#print axioms stageUniformSlack
#print axioms scalarGeometryAllStages
#print axioms cyclicGeometrySlack
#print axioms scalarTileFitsEventually
#print axioms cyclicTileFitsEventually
#print axioms roundedLogPowBigO
#print axioms completeCostBigO
#print axioms costBoundOfDomination
#print axioms costBoundOfEventualDomination

end
end ThinMatrix.AsymptoticCosts
