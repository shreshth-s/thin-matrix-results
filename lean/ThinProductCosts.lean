import TilingCosts
import SharedEncoder
import EncoderCorrectness
import CappedEnumeration
import CacheCardinality
import EntropyBounds
import HighBoxDP
import TensorContraction
import CyclicRing
import Mathlib.Tactic

/-!
# Finite thin-product cost composition

The counters below count actual retained coefficient loops, actual capped
channel sets, actual labelled ordered-box handles and the bottom-up high-box
schedule. Full cyclic vectors are charged during formation and preprocessing;
a stored-box request reads only its selected coefficient. Integer primitive
costs remain explicit, so no constant-cost arbitrary integer operation or
unproved all-coefficient cyclic multiplication is assumed.
-/

namespace ThinMatrix.ThinProductCosts

open scoped BigOperators
open CacheBounds CacheCardinality EntropyBounds
noncomputable section

/-- The original full-grid side length; the encoder's larger count is not
substituted in this geometry. -/
def gridSide (L m : ℕ) : ℕ := L.choose m * 4 ^ (L - m)

@[simp] theorem gridSide_cast (L m : ℕ) : (gridSide L m : ℝ) = gridCount L m := by
  simp [gridSide, gridCount]

@[simp] theorem ordinaryHalfCount_cast (L m : ℕ) :
    (ordinaryHalfCount L m : ℝ) = ordinaryTail L m := by
  simp [ordinaryHalfCount, ordinaryTail, ordinaryTerm]

@[simp] theorem channelBall_cast (n t : ℕ) : (channelBall n t : ℝ) = channelTail n t := by
  simp [channelBall, channelTail]

/-- All low channels in the uniform cache. Enumerating the boundary
`|C|=t` too is harmless: its truncated contribution is zero. -/
abbrev LowChannels (m t : ℕ) := {C : Finset (Fin (2*m)) // C.card ≤ t}

@[simp] theorem lowChannels_card (m t : ℕ) :
    Fintype.card (LowChannels m t) = channelBall (2*m) t := by
  simpa [LowChannels, channelBall] using capped_subsets_card (Fin (2*m)) t

/-- For each channel and each auxiliary coefficient pair, a selected cyclic
coefficient is the length-q dot product of `CyclicRing.mul_coeff`. Five
scalar units cover operand reads, multiplication, weighting and accumulation. -/
def lowCoefficientCost (m t q width : ℕ) : ℕ :=
  ∑ _C : LowChannels m t, ∑ _i : Fin width, ∑ _j : Fin width, ∑ _r : Fin q, 5

@[simp] theorem lowCoefficientCost_eq (m t q width : ℕ) :
    lowCoefficientCost m t q width = 5 * channelBall (2*m) t * width^2 * q := by
  simp [lowCoefficientCost, pow_two]
  ring

/-- The exact finite ordered-mask/ordinary-label family used by high reads. -/
abbrev HighHandles (m t : ℕ) :=
  Σ ms : (OrderedBoxes.orderedBoxMasks t (2*m)).toFinset,
    (OrderedBoxes.ordinaryPositions ms.val) → Fin 4

@[simp] theorem highHandles_card (m t : ℕ) :
    Fintype.card (HighHandles m t) = (2*m).choose t * 4^t :=
  TensorContraction.labelled_ordered_box_count (2*m) t

/-- A completed stored polynomial permits one coefficient read per handle. -/
def highCoefficientReads (m t : ℕ) : ℕ := ∑ _h : HighHandles m t, 1

@[simp] theorem highCoefficientReads_eq (m t : ℕ) :
    highCoefficientReads m t = (2*m).choose t * 4^t := by
  simp only [highCoefficientReads, Finset.sum_const, Finset.card_univ, smul_eq_mul,
    mul_one, highHandles_card]

/-- The actual selected-coefficient convolution loop. -/
def selectedDotCost (q : ℕ) : ℕ := ∑ _i : Fin q, 2

@[simp] theorem selectedDotCost_eq (q : ℕ) : selectedDotCost q = 2*q := by
  simp [selectedDotCost, Nat.mul_comm]

/-- Selected-coefficient reads use exactly the certified cyclic dot product. -/
theorem selectedDot_value {q : ℕ} [NeZero q] (a b : CyclicRing.Cyclic q) (k : Fin q) :
    (a*b) k = ∑ i : Fin q, a i * b (k-i) := CyclicRing.mul_coeff a b k

/-- Root-inclusive cap enumeration counter, with rejected child tests paid. -/
def capEnumerationCost (L m t : ℕ) : ℕ :=
  1 + (CappedEnumeration.generateWithWork L m t (2*L)).extensions +
    (CappedEnumeration.generateWithWork L m t (2*L)).positionTests

def capFactor (L : ℕ) : ℕ := 1 + (1+3*(2*L))*(6*(2*L))

theorem capEnumerationCost_le (L m t : ℕ) :
    capEnumerationCost L m t ≤ capFactor L * retainedLeafCount L m t :=
  CappedEnumeration.enumeration_work_with_root_le L m t

/-- The literal local coefficient loops and cap enumeration, charged
separately on each side. Auxiliary and cyclic widths both remain explicit. -/
def encoderCost (L m t q width : ℕ) (side : Bool) : ℕ :=
  EncoderCorrectness.coefficientLoopCost L m t q width side + capEnumerationCost L m t

/-- A conservative complete per-band count, including all internal arrays. -/
theorem encoderCost_le (L m t q width : ℕ) (side : Bool) :
    encoderCost L m t q width side ≤
      (54*q*width*(2*L+1)+capFactor L) * retainedLeafCount L m t := by
  have hc := EncoderCorrectness.coefficientLoopCost_le L m t q width side
  have he := capEnumerationCost_le L m t
  unfold encoderCost
  nlinarith

/-- Full-vector linear work and multiplication work stay distinct. The
second argument may later be instantiated by a proved Toom or FFT bit cost. -/
def vectorUnit (q linearUnit fullMultiply : ℕ) : ℕ := q*linearUnit + fullMultiply

/-- Every actual DP work/read event is charged a full-vector unit; this
also pays writes and child-vector reads. -/
def highPreprocessingCost (L m t q linearUnit fullMultiply : ℕ) : ℕ :=
  (HighBoxDP.scheduledWork L m t + HighBoxDP.preprocessingReads L m t) *
    vectorUnit q linearUnit fullMultiply

theorem highPreprocessingCost_eq (L m t q linearUnit fullMultiply : ℕ) :
    highPreprocessingCost L m t q linearUnit fullMultiply =
      (HighBoxDP.preprocessingWork L m t + HighBoxDP.preprocessingReads L m t) *
        (q*linearUnit + fullMultiply) := by
  rw [highPreprocessingCost, HighBoxDP.scheduledWork_eq]
  rfl

/-- The two genuine input encoders are shared by all tiles in their bands. -/
def concreteLoopCosts (R Q L m t q width linearUnit fullMultiply lookupUnit : ℕ) :
    TilingCosts.LoopCosts R Q (highCoefficientReads m t) where
  leftEncoder _ := encoderCost L m t q width true * linearUnit
  rightEncoder _ := encoderCost L m t q width false * linearUnit
  tileDP _ _ := highPreprocessingCost L m t q linearUnit fullMultiply
  residual _ := lowCoefficientCost m t q width * linearUnit
  storedRead _ _ := lookupUnit

/-- Exact composition of the concrete finite nested schedule; no premise
assumes its cost is dominated by a desired asymptotic expression. -/
theorem concrete_executionCost (R Q L m t q width linearUnit fullMultiply lookupUnit : ℕ) :
    TilingCosts.executionCost
      (concreteLoopCosts R Q L m t q width linearUnit fullMultiply lookupUnit) =
      R * (encoderCost L m t q width true * linearUnit) +
      R * (encoderCost L m t q width false * linearUnit) +
      R^2 * highPreprocessingCost L m t q linearUnit fullMultiply +
      Q * (5 * channelBall (2*m) t * width^2 * q * linearUnit +
        highCoefficientReads m t * lookupUnit) := by
  rw [TilingCosts.executionCost_eq]
  simp [TilingCosts.loopLedger, concreteLoopCosts, pow_two]
  ring

/-- The genuine retained family obeys the cache product bound after casting. -/
theorem cacheCount_real_le (L m t : ℕ) (hm : m ≤ L) :
    (retainedLeafCount L m t : ℝ) ≤ ordinaryTail L m ^ 2 * channelTail (2*m) t := by
  have h : (retainedLeafCount L m t : ℝ) ≤
      (ordinaryHalfCount L m : ℝ)^2 * (channelBall (2*m) t : ℝ) := by
    exact_mod_cast retainedLeafCount_upper L m t hm
  simpa only [ordinaryHalfCount_cast, channelBall_cast] using h

/-- Named rounded factors, all polynomial in the logarithmic parameter
apart from fixed constants depending only on c and theta. -/
def channelFactor (theta : ℝ) (m : ℕ) : ℝ :=
  (Nat.ceil (2*theta*(m:ℝ))+1 : ℝ) * Real.exp (Real.log (1-theta)-Real.log theta)

def encoderTailFactor (c theta : ℝ) (m : ℕ) : ℝ :=
  channelFactor theta m / (1-4/(c-1))^2

/-- Actual rounded leaf cardinality relative to the original full grid. -/
theorem rounded_cacheCount (c theta : ℝ) (m : ℕ)
    (hc : 5 < c) (ht0 : 0 < theta) (ht1 : theta < 1/2) (hm : 0 < m) :
    let L := Nat.ceil (c*(m:ℝ))
    let t := Nat.ceil (2*theta*(m:ℝ))
    (retainedLeafCount L m t : ℝ) ≤
      encoderTailFactor c theta m * gridCount L m ^ 2 *
        ((4:ℝ)^m)^(channelExponent theta) := by
  let L := Nat.ceil (c*(m:ℝ))
  let t := Nat.ceil (2*theta*(m:ℝ))
  have hceil := Nat.le_ceil (c*(m:ℝ))
  have hmL : m ≤ L := by
    have hm' : (0:ℝ) < m := by exact_mod_cast hm
    exact_mod_cast (show (m:ℝ) ≤ L by dsimp [L]; nlinarith)
  have hs := cacheCount_real_le L m t hmL
  have hu := (rounded_ordinaryTail c m hc hm).2
  have hb := (rounded_channelTail theta m ht0 ht1 hm).2
  have hden : 0 < 1-4/(c-1) := by
    have : 4/(c-1) < (1:ℝ) := (div_lt_one (by linarith)).mpr (by linarith)
    linarith
  have htail : 0 ≤ ordinaryTail L m := by unfold ordinaryTail ordinaryTerm; positivity
  have hchannel : 0 ≤ channelTail (2*m) t := by unfold channelTail; positivity
  calc
    (retainedLeafCount L m t : ℝ) ≤ ordinaryTail L m ^ 2 * channelTail (2*m) t := hs
    _ ≤ (gridCount L m / (1-4/(c-1)))^2 *
        (channelFactor theta m * ((4:ℝ)^m)^(channelExponent theta)) := by
      dsimp [channelFactor]
      gcongr
    _ = encoderTailFactor c theta m * gridCount L m ^ 2 *
        ((4:ℝ)^m)^(channelExponent theta) := by
      unfold encoderTailFactor
      field_simp

/-- A single polynomial factor pays all cap tests and coefficient loops. -/
def encoderPolynomial (L : ℕ) : ℕ := 84*(2*L+1)+capFactor L

theorem encoderCost_width_le (L m t q width : ℕ) (side : Bool)
    (hq : 1 ≤ q) (hw : 1 ≤ width) :
    encoderCost L m t q width side ≤
      encoderPolynomial L * q * width * retainedLeafCount L m t := by
  have he := encoderCost_le L m t q width side
  have hqw : 1 ≤ q*width := by nlinarith
  have hcap : capFactor L ≤ capFactor L * (q*width) :=
    Nat.le_mul_of_pos_right _ hqw
  have hm := Nat.mul_le_mul_right (retainedLeafCount L m t) hcap
  unfold encoderPolynomial
  nlinarith

/-- The original grid side is positive whenever its m-slots exist. -/
theorem gridSide_pos (L m : ℕ) (hm : m ≤ L) : 0 < gridSide L m := by
  unfold gridSide
  exact Nat.mul_pos (Nat.choose_pos hm) (by positivity)

/-- Finite preprocessing/query bound obtained from the actual TilingCosts
schedule and local counters. Only primitive integer operation costs are parameters. -/
theorem concrete_original_bound (N Q L m t q width linearUnit fullMultiply lookupUnit : ℕ)
    (hmL : m ≤ L) (hgeometry : gridSide L m ≤ N) (hq : 1 ≤ q) (hw : 1 ≤ width) :
    (TilingCosts.executionCost (concreteLoopCosts (TilingCosts.bandCount N (gridSide L m))
      Q L m t q width linearUnit fullMultiply lookupUnit) : ℝ) ≤
      (4*(N:ℝ)/(gridSide L m)) *
        (encoderPolynomial L*q*width*retainedLeafCount L m t*linearUnit : ℕ) +
      4*((N:ℝ)/(gridSide L m))^2 *
        (highPreprocessingCost L m t q linearUnit fullMultiply : ℕ) +
      Q*((5*channelBall (2*m) t*width^2*q*linearUnit : ℕ) +
        (highCoefficientReads m t*lookupUnit : ℕ)) := by
  have h := TilingCosts.fullyChargedOriginal
    (concreteLoopCosts (TilingCosts.bandCount N (gridSide L m)) Q L m t q width
      linearUnit fullMultiply lookupUnit)
    (encoderPolynomial L*q*width*retainedLeafCount L m t*linearUnit)
    (highPreprocessingCost L m t q linearUnit fullMultiply)
    (5*channelBall (2*m) t*width^2*q*linearUnit) lookupUnit
    (gridSide_pos L m hmL) hgeometry
    (fun _ => Nat.mul_le_mul_right linearUnit (encoderCost_width_le L m t q width true hq hw))
    (fun _ => Nat.mul_le_mul_right linearUnit (encoderCost_width_le L m t q width false hq hw))
    (fun _ _ => le_refl _) (fun _ => by simp [concreteLoopCosts]) (fun _ _ => le_refl _)
  simpa only [Nat.cast_mul] using h

/-- High-box preprocessing factor includes every true state and vector read. -/
def boxFactor (c theta : ℝ) (m : ℕ) : ℝ :=
  let L := Nat.ceil (c*(m:ℝ))
  11*(2*L+1:ℝ)*(L+1:ℝ)^4*Real.exp (HighBoxEntropy.roundingConstant c theta)

theorem rounded_highCost (c theta : ℝ) (m q linearUnit fullMultiply : ℕ)
    (hc : 5 < c) (ht0 : 0 < theta) (ht1 : theta < 1/2) (hm : 0 < m) :
    let L := Nat.ceil (c*(m:ℝ))
    let t := Nat.ceil (2*theta*(m:ℝ))
    (highPreprocessingCost L m t q linearUnit fullMultiply : ℝ) ≤
      boxFactor c theta m * gridCount L m ^ 2 * ((4:ℝ)^m)^(-HighBoxEntropy.boxSaving c theta) *
        ((q:ℝ)*linearUnit+fullMultiply) := by
  dsimp only
  rw [highPreprocessingCost_eq]
  simp only [Nat.cast_mul, Nat.cast_add]
  have h := HighBoxDP.rounded_highPreprocessing_bound c theta m hc ht0 ht1 hm
  dsimp only at h
  have hu : (0:ℝ) ≤ (q:ℝ)*linearUnit+fullMultiply := by positivity
  have hr := mul_le_mul_of_nonneg_right h hu
  simpa only [boxFactor, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, mul_assoc] using hr

/-- The rounded switch count contributes exactly the additional `2 theta`
to the high-query exponent, with only a constant factor four. -/
theorem rounded_four_pow (theta : ℝ) (m : ℕ) (ht : 0 ≤ theta) :
    (4:ℝ)^(Nat.ceil (2*theta*(m:ℝ))) ≤ 4*((4:ℝ)^m)^(2*theta) := by
  have hceil := (Nat.ceil_lt_add_one (show 0 ≤ 2*theta*(m:ℝ) by positivity)).le
  have hlog : 0 < Real.log (4:ℝ) := Real.log_pos (by norm_num)
  calc
    (4:ℝ)^(Nat.ceil (2*theta*(m:ℝ))) =
        Real.exp ((Nat.ceil (2*theta*(m:ℝ)):ℝ)*Real.log 4) := by
      rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0:ℝ)<4)]
    _ ≤ Real.exp ((2*theta*(m:ℝ)+1)*Real.log 4) := by
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hceil hlog.le)
    _ = 4*((4:ℝ)^m)^(2*theta) := by
      rw [Real.rpow_def_of_pos (by positivity), Real.log_pow,
        show (2*theta*(m:ℝ)+1)*Real.log 4 = Real.log 4+((m:ℝ)*Real.log 4)*(2*theta) by ring,
        Real.exp_add, Real.exp_log (by norm_num : (0:ℝ)<4)]

def highQueryExponent (theta : ℝ) : ℝ := channelExponent theta + 2*theta

theorem highReads_le_ball (m t : ℕ) :
    highCoefficientReads m t ≤ channelBall (2*m) t * 4^t := by
  rw [highCoefficientReads_eq]
  apply Nat.mul_le_mul_right
  unfold channelBall
  exact Finset.single_le_sum (fun i hi => Nat.zero_le _) (Finset.mem_range.mpr (by omega))

theorem rounded_highReads (theta : ℝ) (m : ℕ)
    (ht0 : 0 < theta) (ht1 : theta < 1/2) (hm : 0 < m) :
    let t := Nat.ceil (2*theta*(m:ℝ))
    (highCoefficientReads m t : ℝ) ≤
      4*channelFactor theta m * ((4:ℝ)^m)^(highQueryExponent theta) := by
  let t := Nat.ceil (2*theta*(m:ℝ))
  have hball := (rounded_channelTail theta m ht0 ht1 hm).2
  have hfour := rounded_four_pow theta m ht0.le
  have hr : (highCoefficientReads m t : ℝ) ≤ channelTail (2*m) t * (4:ℝ)^t := by
    have h : (highCoefficientReads m t : ℝ) ≤ (channelBall (2*m) t : ℝ) * (4:ℝ)^t := by
      exact_mod_cast highReads_le_ball m t
    simpa only [channelBall_cast] using h
  have hchannel : 0 ≤ channelTail (2*m) t := by unfold channelTail; positivity
  have hfactor : 0 ≤ channelFactor theta m := by unfold channelFactor; positivity
  change channelTail (2*m) t ≤ channelFactor theta m *
    ((4:ℝ)^m)^(channelExponent theta) at hball
  calc
    (highCoefficientReads m t : ℝ) ≤ channelTail (2*m) t * (4:ℝ)^t := hr
    _ ≤ (channelFactor theta m*((4:ℝ)^m)^(channelExponent theta))*
        (4*((4:ℝ)^m)^(2*theta)) := by
      gcongr
    _ = 4*channelFactor theta m * ((4:ℝ)^m)^(highQueryExponent theta) := by
      rw [highQueryExponent, Real.rpow_add (by positivity)]
      ring

/-- The low cyclic dot-product factor is retained explicitly. -/
theorem rounded_lowCost (theta : ℝ) (m q width linearUnit : ℕ)
    (ht0 : 0 < theta) (ht1 : theta < 1/2) (hm : 0 < m) :
    let t := Nat.ceil (2*theta*(m:ℝ))
    (lowCoefficientCost m t q width * linearUnit : ℝ) ≤
      5*(width:ℝ)^2*q*linearUnit*channelFactor theta m*
        ((4:ℝ)^m)^(channelExponent theta) := by
  dsimp only
  rw [lowCoefficientCost_eq]
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, channelBall_cast]
  have h := (rounded_channelTail theta m ht0 ht1 hm).2
  have hm := mul_le_mul_of_nonneg_left h
    (show (0:ℝ) ≤ 5*(width:ℝ)^2*q*linearUnit by positivity)
  simpa only [channelFactor, mul_assoc, mul_left_comm, mul_comm] using hm

/-- Complete rounded finite schedule bound, with original grid geometry
and separate low coefficient and completed-box read terms. -/
theorem rounded_execution_grid (c theta : ℝ)
    (N Q m q width linearUnit fullMultiply lookupUnit : ℕ)
    (hc : 5 < c) (ht0 : 0 < theta) (ht1 : theta < 1/2) (hm : 0 < m)
    (hq : 1 ≤ q) (hw : 1 ≤ width)
    (hgeometry : gridSide (Nat.ceil (c*(m:ℝ))) m ≤ N) :
    let L := Nat.ceil (c*(m:ℝ))
    let t := Nat.ceil (2*theta*(m:ℝ))
    (TilingCosts.executionCost (concreteLoopCosts (TilingCosts.bandCount N (gridSide L m))
      Q L m t q width linearUnit fullMultiply lookupUnit) : ℝ) ≤
      4*(N:ℝ)*encoderPolynomial L*q*width*linearUnit*encoderTailFactor c theta m*
        gridCount L m*((4:ℝ)^m)^(channelExponent theta) +
      4*(N:ℝ)^2*boxFactor c theta m*((q:ℝ)*linearUnit+fullMultiply)*
        ((4:ℝ)^m)^(-HighBoxEntropy.boxSaving c theta) +
      Q*(5*(width:ℝ)^2*q*linearUnit*channelFactor theta m*
        ((4:ℝ)^m)^(channelExponent theta) +
        4*channelFactor theta m*lookupUnit*((4:ℝ)^m)^(highQueryExponent theta)) := by
  let L := Nat.ceil (c*(m:ℝ))
  let t := Nat.ceil (2*theta*(m:ℝ))
  have hmL : m ≤ L := by
    have hceil := Nat.le_ceil (c*(m:ℝ))
    have hm' : (0:ℝ) < m := by exact_mod_cast hm
    exact_mod_cast (show (m:ℝ) ≤ L by dsimp [L]; nlinarith)
  have hg : 0 < gridCount L m := by
    have h := gridSide_pos L m hmL
    rw [← gridSide_cast]
    exact_mod_cast h
  have hfinite := concrete_original_bound N Q L m t q width linearUnit fullMultiply lookupUnit
    hmL hgeometry hq hw
  have hfinite' : (TilingCosts.executionCost
      (concreteLoopCosts (TilingCosts.bandCount N (gridSide L m)) Q L m t q width
        linearUnit fullMultiply lookupUnit) : ℝ) ≤
      (4*(N:ℝ)/gridCount L m)*
        ((encoderPolynomial L:ℝ)*q*width*linearUnit*(retainedLeafCount L m t:ℝ)) +
      4*((N:ℝ)/gridCount L m)^2*(highPreprocessingCost L m t q linearUnit fullMultiply:ℝ) +
      Q*((lowCoefficientCost m t q width*linearUnit:ℕ)+(highCoefficientReads m t:ℝ)*lookupUnit) := by
    simpa only [gridSide_cast, lowCoefficientCost_eq, Nat.cast_mul, Nat.cast_pow,
      Nat.cast_ofNat, mul_assoc, mul_left_comm, mul_comm] using hfinite
  have hs := rounded_cacheCount c theta m hc ht0 ht1 hm
  have hb := rounded_highCost c theta m q linearUnit fullMultiply hc ht0 ht1 hm
  have hl := rounded_lowCost theta m q width linearUnit ht0 ht1 hm
  have hr := rounded_highReads theta m ht0 ht1 hm
  have htail : 0 ≤ encoderTailFactor c theta m := by unfold encoderTailFactor channelFactor; positivity
  have hbox : 0 ≤ boxFactor c theta m := by unfold boxFactor; positivity
  have hchannel : 0 ≤ channelFactor theta m := by unfold channelFactor; positivity
  calc
    (TilingCosts.executionCost
      (concreteLoopCosts (TilingCosts.bandCount N (gridSide L m)) Q L m t q width
        linearUnit fullMultiply lookupUnit) : ℝ) ≤
      (4*(N:ℝ)/gridCount L m)*
        ((encoderPolynomial L:ℝ)*q*width*linearUnit*(retainedLeafCount L m t:ℝ)) +
      4*((N:ℝ)/gridCount L m)^2*(highPreprocessingCost L m t q linearUnit fullMultiply:ℝ) +
      Q*((lowCoefficientCost m t q width*linearUnit:ℕ)+(highCoefficientReads m t:ℝ)*lookupUnit) := hfinite'
    _ ≤ (4*(N:ℝ)/gridCount L m)*
        ((encoderPolynomial L:ℝ)*q*width*linearUnit*
          (encoderTailFactor c theta m*gridCount L m^2*((4:ℝ)^m)^(channelExponent theta))) +
      4*((N:ℝ)/gridCount L m)^2*
        (boxFactor c theta m*gridCount L m^2*((4:ℝ)^m)^(-HighBoxEntropy.boxSaving c theta)*
          ((q:ℝ)*linearUnit+fullMultiply)) +
      Q*(5*(width:ℝ)^2*q*linearUnit*channelFactor theta m*((4:ℝ)^m)^(channelExponent theta) +
        (4*channelFactor theta m*((4:ℝ)^m)^(highQueryExponent theta))*lookupUnit) := by
      gcongr
      simpa only [Nat.cast_mul] using hl
    _ = _ := by
      field_simp
      ring

/-- The final source exponent is `T+Q`, whereas geometry continues to use T. -/
def sourceExponent (c theta : ℝ) : ℝ := tileExponent c + channelExponent theta

def gridRoundingFactor (c : ℝ) : ℝ := Real.exp (Real.log 4+Real.log (c/(c-1)))

/-- The encoder term loses one original-grid side through band sharing. -/
theorem rounded_encoder_source_power (c theta : ℝ) (m : ℕ)
    (hc : 5 < c) (hm : 0 < m) :
    gridCount (Nat.ceil (c*(m:ℝ))) m * ((4:ℝ)^m)^(channelExponent theta) ≤
      gridRoundingFactor c * ((4:ℝ)^m)^(sourceExponent c theta) := by
  have hg := (rounded_gridCount c m (by linarith) hm).2
  calc
    gridCount (Nat.ceil (c*(m:ℝ))) m * ((4:ℝ)^m)^(channelExponent theta) ≤
      (gridRoundingFactor c*((4:ℝ)^m)^(tileExponent c))*
        ((4:ℝ)^m)^(channelExponent theta) := by
      exact mul_le_mul_of_nonneg_right hg (Real.rpow_nonneg (by positivity) _)
    _ = gridRoundingFactor c*((4:ℝ)^m)^(sourceExponent c theta) := by
      rw [sourceExponent, Real.rpow_add (by positivity)]
      ring

/-- Coefficient extraction from the auxiliary polynomial product consists
of small auxiliary-degree loops and selected cyclic dot products. -/
theorem selectedPolynomialCoefficient_value {q : ℕ} [NeZero q]
    (P Q : Polynomial (CyclicRing.Cyclic q)) (d : ℕ) (k : Fin q) :
    ((P*Q).coeff d) k = ∑ i ∈ Finset.range (d+1), ∑ j : Fin q,
      P.coeff i j * Q.coeff (d-i) (k-j) := by
  rw [Polynomial.coeff_mul, CyclicRing.sum_coeff]
  simp only [CyclicRing.mul_coeff]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]

/-- Actual shifted auxiliary-coefficient loop: if a channel can contribute,
it reads degree j-|C| and runs its j-|C|+1 cyclic dot products. The two
additional units pay weighting and accumulation. Failed tests cost one. -/
def shiftedLowCost (m t q : ℕ) : ℕ :=
  ∑ C : LowChannels m t, ∑ j : Fin t,
    if C.val.card ≤ j.val then 2*q*(j.val-C.val.card+1)+2 else 1

theorem shiftedLowCost_le (m t q : ℕ) (ht : 1 ≤ t) (hq : 1 ≤ q) :
    shiftedLowCost m t q ≤ lowCoefficientCost m t q t := by
  have hstep (C : LowChannels m t) (j : Fin t) :
      (if C.val.card ≤ j.val then 2*q*(j.val-C.val.card+1)+2 else 1) ≤ 5*q*t := by
    split_ifs with h
    · have hd : j.val-C.val.card+1 ≤ t := by have := j.isLt; omega
      have hd' := Nat.mul_le_mul_left (2*q) hd
      have hqt : 1 ≤ q*t := by nlinarith
      nlinarith
    · nlinarith
  calc
    shiftedLowCost m t q ≤ ∑ _C : LowChannels m t, ∑ _j : Fin t, 5*q*t := by
      apply Finset.sum_le_sum
      intro C hC
      exact Finset.sum_le_sum (fun j hj => hstep C j)
    _ = lowCoefficientCost m t q t := by simp [lowCoefficientCost_eq]; ring

theorem shiftedLowCost_le_width (m t q width : ℕ) (ht : 1 ≤ t) (hq : 1 ≤ q)
    (hw : t ≤ width) : shiftedLowCost m t q ≤ lowCoefficientCost m t q width := by
  apply (shiftedLowCost_le m t q ht hq).trans
  rw [lowCoefficientCost_eq, lowCoefficientCost_eq]
  gcongr

/-- Work is read from the returned materialized shared encoder itself. -/
def sharedEncoderCost {R : Type*} [CommSemiring R] (L m t q width : ℕ) (side : Bool)
    (forms : SharedEncoder.LocalForms R)
    (input : SharedEncoder.Dense (R := R) (2*L) (SharedEncoder.rootDims L side)) : ℕ :=
  (SharedEncoder.encode L m t q width side forms input).coefficientWork +
    (SharedEncoder.encode L m t q width side forms input).capWork

theorem sharedEncoderCost_le {R : Type*} [CommSemiring R] (L m t q width : ℕ) (side : Bool)
    (forms : SharedEncoder.LocalForms R)
    (input : SharedEncoder.Dense (R := R) (2*L) (SharedEncoder.rootDims L side))
    (hq : 1 ≤ q) (hw : 1 ≤ width) :
    sharedEncoderCost L m t q width side forms input ≤
      encoderPolynomial L*q*width*retainedLeafCount L m t := by
  have h := SharedEncoder.encode_work_le L m t q width side forms input hq hw
  unfold sharedEncoderCost
  apply h.trans
  gcongr
  unfold encoderPolynomial capFactor
  have he : 6*(2*L)*(1+3*(2*L)) = (1+3*(2*L))*(6*(2*L)) := by ring
  rw [he]
  omega

/-- The concrete two-input shared-array execution, actual bottom-up high
schedule and actual shifted residual-coefficient loop. -/
def implementedLoopCosts {R : Type*} [CommSemiring R]
    (bands requests L m t q width linearUnit fullMultiply lookupUnit : ℕ)
    (leftForms rightForms : Fin bands → SharedEncoder.LocalForms R)
    (leftInput : Fin bands → SharedEncoder.Dense (R := R) (2*L) (SharedEncoder.rootDims L true))
    (rightInput : Fin bands → SharedEncoder.Dense (R := R) (2*L) (SharedEncoder.rootDims L false)) :
    TilingCosts.LoopCosts bands requests (highCoefficientReads m t) where
  leftEncoder b := sharedEncoderCost L m t q width true (leftForms b) (leftInput b)*linearUnit
  rightEncoder b := sharedEncoderCost L m t q width false (rightForms b) (rightInput b)*linearUnit
  tileDP _ _ := highPreprocessingCost L m t q linearUnit fullMultiply
  residual _ := shiftedLowCost m t q*linearUnit
  storedRead _ _ := lookupUnit

/-- Finite execution domination follows from implemented local loops,
not from an assumed asymptotic running-time inequality. -/
theorem implemented_execution_uniform {R : Type*} [CommSemiring R]
    (bands requests L m t q width linearUnit fullMultiply lookupUnit : ℕ)
    (leftForms rightForms : Fin bands → SharedEncoder.LocalForms R)
    (leftInput : Fin bands → SharedEncoder.Dense (R := R) (2*L) (SharedEncoder.rootDims L true))
    (rightInput : Fin bands → SharedEncoder.Dense (R := R) (2*L) (SharedEncoder.rootDims L false))
    (hq : 1 ≤ q) (ht : 1 ≤ t) (hw : t ≤ width) :
    TilingCosts.executionCost (implementedLoopCosts bands requests L m t q width linearUnit
      fullMultiply lookupUnit leftForms rightForms leftInput rightInput) ≤
    TilingCosts.uniformLedger bands requests (highCoefficientReads m t)
      (encoderPolynomial L*q*width*retainedLeafCount L m t*linearUnit)
      (highPreprocessingCost L m t q linearUnit fullMultiply)
      (lowCoefficientCost m t q width*linearUnit) lookupUnit := by
  apply TilingCosts.executionCost_le
  · intro b
    exact Nat.mul_le_mul_right linearUnit
      (sharedEncoderCost_le L m t q width true (leftForms b) (leftInput b) hq (by omega))
  · intro b
    exact Nat.mul_le_mul_right linearUnit
      (sharedEncoderCost_le L m t q width false (rightForms b) (rightInput b) hq (by omega))
  · intros; rfl
  · intro r
    exact Nat.mul_le_mul_right linearUnit (shiftedLowCost_le_width m t q width ht hq hw)
  · intros; rfl

/-- The uniform finite budget with coefficients supplied by the proved
local counters. Its construction is independent of any asymptotic target. -/
def uniformCost (N Q L m t q width linearUnit fullMultiply lookupUnit : ℕ) : ℕ :=
  TilingCosts.uniformLedger (TilingCosts.bandCount N (gridSide L m)) Q (highCoefficientReads m t)
    (encoderPolynomial L*q*width*retainedLeafCount L m t*linearUnit)
    (highPreprocessingCost L m t q linearUnit fullMultiply)
    (lowCoefficientCost m t q width*linearUnit) lookupUnit

theorem rounded_uniform_ledger (c theta : ℝ)
    (N Q m q width linearUnit fullMultiply lookupUnit : ℕ)
    (hc : 5 < c) (ht0 : 0 < theta) (ht1 : theta < 1/2) (hm : 0 < m)
    (hgeometry : gridSide (Nat.ceil (c*(m:ℝ))) m ≤ N) :
    let L := Nat.ceil (c*(m:ℝ))
    let t := Nat.ceil (2*theta*(m:ℝ))
    (uniformCost N Q L m t q width linearUnit fullMultiply lookupUnit : ℝ) ≤
      4*(N:ℝ)*encoderPolynomial L*q*width*linearUnit*encoderTailFactor c theta m*
        gridCount L m*((4:ℝ)^m)^(channelExponent theta) +
      4*(N:ℝ)^2*boxFactor c theta m*((q:ℝ)*linearUnit+fullMultiply)*
        ((4:ℝ)^m)^(-HighBoxEntropy.boxSaving c theta) +
      Q*(5*(width:ℝ)^2*q*linearUnit*channelFactor theta m*
        ((4:ℝ)^m)^(channelExponent theta) +
        4*channelFactor theta m*lookupUnit*((4:ℝ)^m)^(highQueryExponent theta)) := by
  let L := Nat.ceil (c*(m:ℝ))
  let t := Nat.ceil (2*theta*(m:ℝ))
  have hmL : m ≤ L := by
    have hceil := Nat.le_ceil (c*(m:ℝ))
    have hm' : (0:ℝ) < m := by exact_mod_cast hm
    exact_mod_cast (show (m:ℝ) ≤ L by dsimp [L]; nlinarith)
  have hg : 0 < gridCount L m := by
    have h := gridSide_pos L m hmL
    rw [← gridSide_cast]
    exact_mod_cast h
  have hfinite := TilingCosts.original_ledger_bound N (gridSide L m) Q (highCoefficientReads m t)
    (encoderPolynomial L*q*width*retainedLeafCount L m t*linearUnit)
    (highPreprocessingCost L m t q linearUnit fullMultiply)
    (lowCoefficientCost m t q width*linearUnit) lookupUnit (gridSide_pos L m hmL) hgeometry
  have hfinite' : (uniformCost N Q L m t q width linearUnit fullMultiply lookupUnit : ℝ) ≤
      (4*(N:ℝ)/gridCount L m)*
        ((encoderPolynomial L:ℝ)*q*width*linearUnit*(retainedLeafCount L m t:ℝ)) +
      4*((N:ℝ)/gridCount L m)^2*(highPreprocessingCost L m t q linearUnit fullMultiply:ℝ) +
      Q*((lowCoefficientCost m t q width*linearUnit:ℕ)+(highCoefficientReads m t:ℝ)*lookupUnit) := by
    simpa only [uniformCost, gridSide_cast, lowCoefficientCost_eq, Nat.cast_mul, Nat.cast_pow,
      Nat.cast_ofNat, mul_assoc, mul_left_comm, mul_comm] using hfinite
  have hs := rounded_cacheCount c theta m hc ht0 ht1 hm
  have hb := rounded_highCost c theta m q linearUnit fullMultiply hc ht0 ht1 hm
  have hl := rounded_lowCost theta m q width linearUnit ht0 ht1 hm
  have hr := rounded_highReads theta m ht0 ht1 hm
  have htail : 0 ≤ encoderTailFactor c theta m := by unfold encoderTailFactor channelFactor; positivity
  have hbox : 0 ≤ boxFactor c theta m := by unfold boxFactor; positivity
  have hchannel : 0 ≤ channelFactor theta m := by unfold channelFactor; positivity
  calc
    (uniformCost N Q L m t q width linearUnit fullMultiply lookupUnit : ℝ) ≤
      (4*(N:ℝ)/gridCount L m)*
        ((encoderPolynomial L:ℝ)*q*width*linearUnit*(retainedLeafCount L m t:ℝ)) +
      4*((N:ℝ)/gridCount L m)^2*(highPreprocessingCost L m t q linearUnit fullMultiply:ℝ) +
      Q*((lowCoefficientCost m t q width*linearUnit:ℕ)+(highCoefficientReads m t:ℝ)*lookupUnit) := hfinite'
    _ ≤ (4*(N:ℝ)/gridCount L m)*
        ((encoderPolynomial L:ℝ)*q*width*linearUnit*
          (encoderTailFactor c theta m*gridCount L m^2*((4:ℝ)^m)^(channelExponent theta))) +
      4*((N:ℝ)/gridCount L m)^2*
        (boxFactor c theta m*gridCount L m^2*((4:ℝ)^m)^(-HighBoxEntropy.boxSaving c theta)*
          ((q:ℝ)*linearUnit+fullMultiply)) +
      Q*(5*(width:ℝ)^2*q*linearUnit*channelFactor theta m*((4:ℝ)^m)^(channelExponent theta) +
        (4*channelFactor theta m*((4:ℝ)^m)^(highQueryExponent theta))*lookupUnit) := by
      gcongr
      simpa only [Nat.cast_mul] using hl
    _ = _ := by
      field_simp
      ring

/-- Explicit power form of the genuine finite budget. Full-vector
arithmetic is `q*linearUnit+fullMultiply`; selected low queries use only q. -/
def powerBound (c theta : ℝ) (N Q m q width linearUnit fullMultiply lookupUnit : ℕ) : ℝ :=
  let L := Nat.ceil (c*(m:ℝ))
  4*(N:ℝ)*encoderPolynomial L*q*width*linearUnit*encoderTailFactor c theta m*
    gridRoundingFactor c*((4:ℝ)^m)^(sourceExponent c theta) +
  4*(N:ℝ)^2*boxFactor c theta m*((q:ℝ)*linearUnit+fullMultiply)*
    ((4:ℝ)^m)^(-HighBoxEntropy.boxSaving c theta) +
  Q*(5*(width:ℝ)^2*q*linearUnit*channelFactor theta m*
    ((4:ℝ)^m)^(channelExponent theta) +
    4*channelFactor theta m*lookupUnit*((4:ℝ)^m)^(highQueryExponent theta))

theorem rounded_uniform_power (c theta : ℝ)
    (N Q m q width linearUnit fullMultiply lookupUnit : ℕ)
    (hc : 5 < c) (ht0 : 0 < theta) (ht1 : theta < 1/2) (hm : 0 < m)
    (hgeometry : gridSide (Nat.ceil (c*(m:ℝ))) m ≤ N) :
    let L := Nat.ceil (c*(m:ℝ))
    let t := Nat.ceil (2*theta*(m:ℝ))
    (uniformCost N Q L m t q width linearUnit fullMultiply lookupUnit : ℝ) ≤
      powerBound c theta N Q m q width linearUnit fullMultiply lookupUnit := by
  have h := rounded_uniform_ledger c theta N Q m q width linearUnit fullMultiply lookupUnit
    hc ht0 ht1 hm hgeometry
  have hp := rounded_encoder_source_power c theta m hc hm
  have htail : 0 ≤ encoderTailFactor c theta m := by unfold encoderTailFactor channelFactor; positivity
  have he := mul_le_mul_of_nonneg_left hp
    (show (0:ℝ) ≤ 4*(N:ℝ)*encoderPolynomial (Nat.ceil (c*(m:ℝ)))*q*width*linearUnit*
      encoderTailFactor c theta m by positivity)
  apply h.trans
  unfold powerBound
  dsimp only
  nlinarith

/-- Actual two shared materialized input encoders and shifted query loops
have the proved two-encoder/box/query bound. Geometry uses gridSide,
not the source exponent; no abstract time-domination premise occurs. -/
theorem implemented_rounded_power {R : Type*} [CommSemiring R] (c theta : ℝ)
    (N Q m q width linearUnit fullMultiply lookupUnit : ℕ)
    (hc : 5 < c) (ht0 : 0 < theta) (ht1 : theta < 1/2) (hm : 0 < m)
    (hq : 1 ≤ q) (hwidth : Nat.ceil (2*theta*(m:ℝ)) ≤ width)
    (hgeometry : gridSide (Nat.ceil (c*(m:ℝ))) m ≤ N)
    (leftForms rightForms : Fin (TilingCosts.bandCount N
      (gridSide (Nat.ceil (c*(m:ℝ))) m)) → SharedEncoder.LocalForms R)
    (leftInput : Fin (TilingCosts.bandCount N (gridSide (Nat.ceil (c*(m:ℝ))) m)) →
      SharedEncoder.Dense (R := R) (2*Nat.ceil (c*(m:ℝ)))
        (SharedEncoder.rootDims (Nat.ceil (c*(m:ℝ))) true))
    (rightInput : Fin (TilingCosts.bandCount N (gridSide (Nat.ceil (c*(m:ℝ))) m)) →
      SharedEncoder.Dense (R := R) (2*Nat.ceil (c*(m:ℝ)))
        (SharedEncoder.rootDims (Nat.ceil (c*(m:ℝ))) false)) :
    let L := Nat.ceil (c*(m:ℝ))
    let t := Nat.ceil (2*theta*(m:ℝ))
    (TilingCosts.executionCost
      (implementedLoopCosts (TilingCosts.bandCount N (gridSide L m)) Q L m t q width
        linearUnit fullMultiply lookupUnit leftForms rightForms leftInput rightInput) : ℝ) ≤
      powerBound c theta N Q m q width linearUnit fullMultiply lookupUnit := by
  have ht : 1 ≤ Nat.ceil (2*theta*(m:ℝ)) := by
    have hp : (0:ℝ) < 2*theta*(m:ℝ) := by positivity
    exact Nat.one_le_ceil_iff.mpr hp
  have hi := implemented_execution_uniform
    (TilingCosts.bandCount N (gridSide (Nat.ceil (c*(m:ℝ))) m)) Q
    (Nat.ceil (c*(m:ℝ))) m (Nat.ceil (2*theta*(m:ℝ))) q width
    linearUnit fullMultiply lookupUnit leftForms rightForms leftInput rightInput hq ht hwidth
  have hiR : (TilingCosts.executionCost
      (implementedLoopCosts (TilingCosts.bandCount N (gridSide (Nat.ceil (c*(m:ℝ))) m)) Q
        (Nat.ceil (c*(m:ℝ))) m (Nat.ceil (2*theta*(m:ℝ))) q width
        linearUnit fullMultiply lookupUnit leftForms rightForms leftInput rightInput) : ℝ) ≤
      (uniformCost N Q (Nat.ceil (c*(m:ℝ))) m (Nat.ceil (2*theta*(m:ℝ))) q width
        linearUnit fullMultiply lookupUnit : ℝ) := by exact_mod_cast hi
  exact hiR.trans (rounded_uniform_power c theta N Q m q width linearUnit fullMultiply lookupUnit
    hc ht0 ht1 hm hgeometry)

end
end ThinMatrix.ThinProductCosts

#print axioms ThinMatrix.ThinProductCosts.lowChannels_card
#print axioms ThinMatrix.ThinProductCosts.highHandles_card
#print axioms ThinMatrix.ThinProductCosts.concrete_executionCost
#print axioms ThinMatrix.ThinProductCosts.rounded_cacheCount

#print axioms ThinMatrix.ThinProductCosts.concrete_original_bound
#print axioms ThinMatrix.ThinProductCosts.rounded_highCost
#print axioms ThinMatrix.ThinProductCosts.rounded_highReads
#print axioms ThinMatrix.ThinProductCosts.rounded_lowCost

#print axioms ThinMatrix.ThinProductCosts.rounded_execution_grid
#print axioms ThinMatrix.ThinProductCosts.rounded_encoder_source_power

#print axioms ThinMatrix.ThinProductCosts.selectedPolynomialCoefficient_value
#print axioms ThinMatrix.ThinProductCosts.shiftedLowCost_le
#print axioms ThinMatrix.ThinProductCosts.sharedEncoderCost_le
#print axioms ThinMatrix.ThinProductCosts.implemented_execution_uniform

#print axioms ThinMatrix.ThinProductCosts.rounded_uniform_ledger

#print axioms ThinMatrix.ThinProductCosts.rounded_uniform_power
#print axioms ThinMatrix.ThinProductCosts.implemented_rounded_power
