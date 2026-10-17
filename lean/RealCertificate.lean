import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic
import AlignedCertificate

/-!
Actual real-logarithm enclosures for the canonical aligned witness.
This file proves analytic numerical statements; it does not formalize the
Walsh embedding, cache algorithm, reductions, or an APSP running-time theorem.
Mathlib's proved atanh-series tail bounds are used without custom axioms.
-/
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace ThinMatrix.RealCertificate
open scoped BigOperators
noncomputable section

theorem atanhLogBounds (z : ℝ) (hz0 : 0 ≤ z) (hz1 : z < 1) (n : ℕ) :
    2 * (∑ i ∈ Finset.range n, z ^ (2 * i + 1) / (2 * (i : ℝ) + 1))
        ≤ Real.log ((1 + z) / (1 - z)) ∧
    Real.log ((1 + z) / (1 - z)) ≤
      2 * ((∑ i ∈ Finset.range n, z ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) +
        z ^ (2 * n + 1) / (1 - z ^ 2)) := by
  have hlo := Real.sum_range_le_log_div hz0 hz1 n
  have hhi := Real.log_div_le_sum_range_add hz0 hz1 n
  constructor <;> linarith

theorem logTwo :
    (693147180559945309 / 10^18 : ℝ) < Real.log (2 / 1 : ℝ) ∧
    Real.log (2 / 1 : ℝ) < (693147180559945310 / 10^18 : ℝ) := by
  have h := atanhLogBounds (1 / 3 : ℝ) (by norm_num) (by norm_num) 20
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith [h.1, h.2]

theorem logC16 :
    (405574328760022632 / 10^18 : ℝ) < Real.log (1600000000 / 1066550171 : ℝ) ∧
    Real.log (1600000000 / 1066550171 : ℝ) < (405574328760022633 / 10^18 : ℝ) := by
  have h := atanhLogBounds (533449829 / 2666550171 : ℝ) (by norm_num) (by norm_num) 20
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith [h.1, h.2]

theorem logCComp2 :
    (594695808377684387 / 10^18 : ℝ) < Real.log (1933100342 / 1066550171 : ℝ) ∧
    Real.log (1933100342 / 1066550171 : ℝ) < (594695808377684388 / 10^18 : ℝ) := by
  have h := atanhLogBounds (866550171 / 2999650513 : ℝ) (by norm_num) (by norm_num) 20
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith [h.1, h.2]

theorem logD16 :
    (338047002765033636 / 10^18 : ℝ) < Real.log (37388087144 / 26663754275 : ℝ) ∧
    Real.log (37388087144 / 26663754275 : ℝ) < (338047002765033637 / 10^18 : ℝ) := by
  have h := atanhLogBounds (10724332869 / 64051841419 : ℝ) (by norm_num) (by norm_num) 20
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith [h.1, h.2]

theorem logDComp2 :
    (601428851680190950 / 10^18 : ℝ) < Real.log (48653997657 / 26663754275 : ℝ) ∧
    Real.log (48653997657 / 26663754275 : ℝ) < (601428851680190951 / 10^18 : ℝ) := by
  have h := atanhLogBounds (10995121691 / 37658875966 : ℝ) (by norm_num) (by norm_num) 20
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith [h.1, h.2]

theorem logTheta16 :
    (43792116043198641 / 10^18 : ℝ) < Real.log (326489107 / 312500000 : ℝ) ∧
    Real.log (326489107 / 312500000 : ℝ) < (43792116043198642 / 10^18 : ℝ) := by
  have h := atanhLogBounds (13989107 / 638989107 : ℝ) (by norm_num) (by norm_num) 20
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith [h.1, h.2]

theorem logThetaComp2 :
    (625619854564956313 / 10^18 : ℝ) < Real.log (4673510893 / 2500000000 : ℝ) ∧
    Real.log (4673510893 / 2500000000 : ℝ) < (625619854564956314 / 10^18 : ℝ) := by
  have h := atanhLogBounds (2173510893 / 7173510893 : ℝ) (by norm_num) (by norm_num) 20
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith [h.1, h.2]

def c : ℝ := 1066550171 / 10^8
def theta : ℝ := 652978214 / 10^10
def entropy (x : ℝ) : ℝ := -x * Real.log x - (1-x) * Real.log (1-x)

theorem witnessCompatibility :
    (ThinMatrix.AlignedCertificate.c : ℝ) = c ∧
    (ThinMatrix.AlignedCertificate.theta : ℝ) = theta := by
  norm_num [ThinMatrix.AlignedCertificate.c, ThinMatrix.AlignedCertificate.theta, c, theta]

theorem entropyScaled (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    entropy p = (1+3*p)*Real.log 2 - p*Real.log (16*p)
      - (1-p)*Real.log (2*(1-p)) := by
  have h16 : Real.log 16 = 4 * Real.log 2 := by
    convert Real.log_pow (2 : ℝ) 4 using 1 <;> norm_num
  have hmul := Real.log_mul (by norm_num : (16 : ℝ) ≠ 0) (ne_of_gt hp)
  have hcomp := Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
    (ne_of_gt (sub_pos.mpr hp1))
  have ha : Real.log p = Real.log (16*p) - 4*Real.log 2 := by
    rw [h16] at hmul
    linarith
  have hb : Real.log (1-p) = Real.log (2*(1-p)) - Real.log 2 := by
    linarith
  rw [entropy, ha, hb]
  ring

theorem entropyC :
    (311152385503602152 / 10^18 : ℝ) < entropy (1/c) ∧
    entropy (1/c) < (311152385503602155 / 10^18 : ℝ) := by
  have hs := entropyScaled (1/c) (by norm_num [c, theta]) (by norm_num [c, theta])
  have h0 := logTwo
  have h1 := logC16
  have h2 := logCComp2
  norm_num [c, theta] at hs ⊢
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2]

theorem entropyD :
    (297038452283886176 / 10^18 : ℝ) < entropy ((1-theta)/c) ∧
    entropy ((1-theta)/c) < (297038452283886179 / 10^18 : ℝ) := by
  have hs := entropyScaled ((1-theta)/c) (by norm_num [c, theta]) (by norm_num [c, theta])
  have h0 := logTwo
  have h1 := logD16
  have h2 := logDComp2
  norm_num [c, theta] at hs ⊢
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2]

theorem entropyTheta :
    (241302412150899209 / 10^18 : ℝ) < entropy (theta) ∧
    entropy (theta) < (241302412150899213 / 10^18 : ℝ) := by
  have hs := entropyScaled (theta) (by norm_num [c, theta]) (by norm_num [c, theta])
  have h0 := logTwo
  have h1 := logTheta16
  have h2 := logThetaComp2
  norm_num [c, theta] at hs ⊢
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2]

def T : ℝ := c - 1 + c * entropy (1/c) / Real.log 4
def G : ℝ := (c*entropy (1/c) - c*entropy ((1-theta)/c)
  - theta * Real.log 4) / Real.log 2
def q1 : ℝ := 2*entropy theta / Real.log 4
def q2 : ℝ := 2*(entropy theta + theta*Real.log 4) / Real.log 4
def Esource : ℝ := T + q1
def Ebox : ℝ := T - G

theorem logFour : Real.log 4 = 2 * Real.log 2 := by
  convert Real.log_pow (2 : ℝ) 2 using 1 <;> norm_num

theorem logTwoPositive : 0 < Real.log 2 := Real.log_pos (by norm_num)

theorem q2Identity : q2 = q1 + 2*theta := by
  have h4 : Real.log 4 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  unfold q2 q1
  field_simp

theorem TEnclosure :
    (12059362922115430 / 10^15 : ℝ) < T ∧
    T < (12059362922115431 / 10^15 : ℝ) := by
  have h0 := logTwo
  have hc := entropyC
  have hp : 0 < 2 * Real.log 2 := mul_pos (by norm_num) logTwoPositive
  have hlo : ((12059362922115430 / 10^15 : ℝ)-c+1)*(2*Real.log 2)
      < c*entropy (1/c) := by
    norm_num [c] at hc ⊢
    linarith [h0.1, h0.2, hc.1, hc.2]
  have hhi : c*entropy (1/c)
      < ((12059362922115431 / 10^15 : ℝ)-c+1)*(2*Real.log 2) := by
    norm_num [c] at hc ⊢
    linarith [h0.1, h0.2, hc.1, hc.2]
  have hl := (lt_div_iff₀ hp).2 hlo
  have hh := (div_lt_iff₀ hp).2 hhi
  dsimp [T]
  rw [logFour]
  constructor <;> linarith

theorem GEnclosure :
    (86576385178389 / 10^15 : ℝ) < G ∧
    G < (86576385178390 / 10^15 : ℝ) := by
  have h0 := logTwo
  have hc := entropyC
  have hd := entropyD
  dsimp [G]
  rw [logFour]
  constructor
  · apply (lt_div_iff₀ logTwoPositive).2
    norm_num [c, theta] at hc hd ⊢
    linarith [h0.1, h0.2, hc.1, hc.2, hd.1, hd.2]
  · apply (div_lt_iff₀ logTwoPositive).2
    norm_num [c, theta] at hc hd ⊢
    linarith [h0.1, h0.2, hc.1, hc.2, hd.1, hd.2]

theorem q1Enclosure :
    (348125793364647 / 10^15 : ℝ) < q1 ∧
    q1 < (348125793364648 / 10^15 : ℝ) := by
  have h0 := logTwo
  have ht := entropyTheta
  dsimp [q1]
  rw [logFour]
  constructor
  · apply (lt_div_iff₀ (mul_pos (by norm_num) logTwoPositive)).2
    linarith [h0.1, h0.2, ht.1, ht.2]
  · apply (div_lt_iff₀ (mul_pos (by norm_num) logTwoPositive)).2
    linarith [h0.1, h0.2, ht.1, ht.2]

def evalReal (a : ThinMatrix.AlignedCertificate.Affine) : ℝ :=
  (a.constant : ℝ) + (a.tCoeff : ℝ)*T + (a.gCoeff : ℝ)*G + (a.qCoeff : ℝ)*q1

theorem signedLowerReal (coefficient lo hi : Rat) (x : ℝ)
    (hlo : (lo : ℝ) ≤ x) (hhi : x ≤ (hi : ℝ)) :
    (ThinMatrix.AlignedCertificate.signedLower coefficient lo hi : ℝ)
      ≤ (coefficient : ℝ)*x := by
  unfold ThinMatrix.AlignedCertificate.signedLower
  split_ifs with h
  · push_cast
    apply mul_le_mul_of_nonneg_left hlo
    exact_mod_cast h
  · push_cast
    apply mul_le_mul_of_nonpos_left hhi
    have hn : coefficient ≤ 0 := le_of_not_ge h
    exact_mod_cast hn

theorem actualParameterEnclosures :
    (ThinMatrix.AlignedCertificate.tLo : ℝ) ≤ T ∧
    T ≤ (ThinMatrix.AlignedCertificate.tHi : ℝ) ∧
    (ThinMatrix.AlignedCertificate.gLo : ℝ) ≤ G ∧
    G ≤ (ThinMatrix.AlignedCertificate.gHi : ℝ) ∧
    (ThinMatrix.AlignedCertificate.qLo : ℝ) ≤ q1 ∧
    q1 ≤ (ThinMatrix.AlignedCertificate.qHi : ℝ) := by
  have ht := TEnclosure
  have hg := GEnclosure
  have hq := q1Enclosure
  norm_num [ThinMatrix.AlignedCertificate.tLo, ThinMatrix.AlignedCertificate.tHi,
    ThinMatrix.AlignedCertificate.gLo, ThinMatrix.AlignedCertificate.gHi,
    ThinMatrix.AlignedCertificate.qLo, ThinMatrix.AlignedCertificate.qHi]
  norm_num at ht hg hq
  exact ⟨ht.1.le, ht.2.le, hg.1.le, hg.2.le, hq.1.le, hq.2.le⟩

theorem lowerLeActual (a : ThinMatrix.AlignedCertificate.Affine) :
    (ThinMatrix.AlignedCertificate.lower a : ℝ) ≤ evalReal a := by
  rcases actualParameterEnclosures with ⟨ht0, ht1, hg0, hg1, hq0, hq1⟩
  have ht := signedLowerReal a.tCoeff _ _ T ht0 ht1
  have hg := signedLowerReal a.gCoeff _ _ G hg0 hg1
  have hq := signedLowerReal a.qCoeff _ _ q1 hq0 hq1
  unfold ThinMatrix.AlignedCertificate.lower evalReal
  push_cast
  linarith

/-- All 47 listed inequalities hold at the actual real logarithm/entropy
expressions, with no enclosure hypotheses. This is numerical feasibility,
not a formalization of the algorithms that motivate the affine costs. -/
theorem allActualRealCosts :
    ∀ check ∈ ThinMatrix.AlignedCertificate.checks,
      (check.target : ℝ) < evalReal check.expression := by
  intro check hmember
  have hb : decide (check.target < ThinMatrix.AlignedCertificate.lower check.expression)
      = true :=
    (List.all_eq_true.mp ThinMatrix.AlignedCertificate.numericalMargins) check hmember
  have hr : check.target < ThinMatrix.AlignedCertificate.lower check.expression :=
    of_decide_eq_true hb
  have hm : (check.target : ℝ) <
      (ThinMatrix.AlignedCertificate.lower check.expression : ℝ) := by
    exact_mod_cast hr
  exact lt_of_lt_of_le hm (lowerLeActual check.expression)

/-- Closed analytic numerical certificate, including the checklist size.
The target exponent and phase formulas are in `AlignedCertificate`;
their interpretation as algorithm costs remains a mathematical proof obligation. -/
theorem analyticNumericalCertificate :
    ThinMatrix.AlignedCertificate.checks.length = 47 ∧
    ∀ check ∈ ThinMatrix.AlignedCertificate.checks,
      (check.target : ℝ) < evalReal check.expression :=
  ⟨ThinMatrix.AlignedCertificate.checkCount, allActualRealCosts⟩

#print axioms actualParameterEnclosures
#print axioms q2Identity
#print axioms analyticNumericalCertificate
end
end ThinMatrix.RealCertificate
