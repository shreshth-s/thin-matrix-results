import RectangularBatch
import ComputableParameters

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! Independent long-side supply for the exact-half witness. The actual
middle-block count and all cyclic columns supply the batch width. No good-set,
root, or request count is used to invent independent products. This module
proves rounded geometric feasibility, not a complete production cost bound. -/
namespace ThinMatrix.HalfSourceBatchFit
open scoped BigOperators
open Filter Real

def bNumerator : ℕ := 4884094420
def bDenominator : ℕ := 100000000000
def R : ℕ := 100000000000000
def S : ℕ := 76777127384957
noncomputable def b : ℝ := (bNumerator:ℝ)/bDenominator
noncomputable def eta : ℝ := b/R
noncomputable def zeta : ℝ := 11/50

def block (n : ℕ) : ℕ := ComputableParameters.roundedPower bNumerator bDenominator n
def scale (n : ℕ) : ℕ :=
  ComputableParameters.roundedPower bNumerator (bDenominator*R) n*n.size^4
abbrev Call (n : ℕ) := PhaseGeometry.PhaseCall R (scale n)
def blocks (n : ℕ) : ℕ := CompactBlocks.blockCount n (block n)
def dimension (n : ℕ) (call : Call n) : ℕ :=
  PhaseGeometry.pad4 (block n*(3*call.folded S))

/-- All coefficients of every real compact middle block are retained. -/
def columns (n : ℕ) (call : Call n) : ℕ := blocks n*call.cyclic S

/-- A computable common support padding with arbitrary fixed polynomial
logarithmic overhead. Entropy bounds must separately prove that it contains
the actual suffix supports. -/
def supportPadding (C k n D : ℕ) : ℕ :=
  C*(n.size+1)^k*ComputableParameters.roundedPower 11 50 D

theorem witness_values : b=244204721/5000000000 ∧ zeta=11/50 ∧
    (R:ℝ)*eta=b ∧ 2*b*(15*zeta+1) < 1-b := by
  norm_num [b,bNumerator,bDenominator,zeta,eta,R]

theorem block_pos (n : ℕ) : 0 < block n := by
  simp only [block,ComputableParameters.roundedPower]; omega

theorem block_bounds (n : ℕ) (hn : 1 ≤ n) :
    (n:ℝ)^b ≤ block n ∧ (block n:ℝ) ≤ 2*(n:ℝ)^b := by
  exact ComputableParameters.roundedPower_bounds bNumerator bDenominator n
    (by norm_num [bDenominator]) (by norm_num [bNumerator,bDenominator]) hn

theorem scale_bounds (n : ℕ) (hn : 3 ≤ n) :
    (n:ℝ)^eta*(Real.log (n:ℝ))^4 ≤ scale n ∧
      (scale n:ℝ) ≤ 512*(n:ℝ)^eta*(Real.log (n:ℝ))^4 := by
  have hr := ComputableParameters.roundedPower_bounds bNumerator (bDenominator*R) n
    (by norm_num [bDenominator,R]) (by norm_num [bNumerator,bDenominator,R]) (by omega)
  have he : (bNumerator:ℝ)/(bDenominator*R)=eta := by
    simp [eta,b,div_mul_eq_div_div]
  rw [Nat.cast_mul,he] at hr
  have hslo := ComputableParameters.log_le_size n (by omega)
  have hshi := ComputableParameters.size_le_four_log n hn
  have hlog : 0 ≤ Real.log (n:ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
  unfold scale
  rw [Nat.cast_mul,Nat.cast_pow]
  constructor
  · exact mul_le_mul hr.1 (pow_le_pow_left₀ hlog hslo 4) (by positivity) (by positivity)
  · calc
      _  ≤  (2*(n:ℝ)^eta)*(4*Real.log (n:ℝ))^4 := by gcongr; exact hr.2
      _ = _ := by ring

theorem scale_pos (n : ℕ) (hn : 3 ≤ n) : 0 < scale n := by
  have h := (scale_bounds n hn).1
  have : 0 < (scale n:ℝ) := lt_of_lt_of_le (by
    have := PhaseGeometry.one_le_log_nat n hn
    have hn0 : 0 < (n:ℝ) := by exact_mod_cast (show 0 < n by omega)
    exact mul_pos (Real.rpow_pos_of_pos hn0 _) (pow_pos (by linarith) _)) h
  exact_mod_cast this

theorem folded_pos (n : ℕ) (hn : 3 ≤ n) (call : Call n) : 0 < call.folded S := by
  have h := (call.folded_bounds S).1
  exact lt_of_lt_of_le (pow_pos (scale_pos n hn) _) h

theorem cyclic_pos (n : ℕ) (hn : 3 ≤ n) (call : Call n) : 0 < call.cyclic S := by
  exact lt_of_lt_of_le (pow_pos (scale_pos n hn) _) (call.cyclic_bounds S).1

noncomputable def overheadConstant : ℝ := 24*(8192:ℝ)^R

theorem dimension_pos (n : ℕ) (call : Call n) : 0 < dimension n call := by
  exact pow_pos (by norm_num) _

theorem folded_upper (n : ℕ) (hn : 3 ≤ n) (call : Call n) :
    (call.folded S:ℝ) ≤ (8192:ℝ)^R*(Real.log (n:ℝ))^(4*R)*(n:ℝ)^b := by
  have hs := (scale_bounds n hn).2
  have hscale := scale_pos n hn
  have hp := (call.folded_bounds S).2
  have hj : min S call.factors.length ≤ R := (Nat.min_le_right _ _).trans call.length_le
  have hu : call.folded S ≤ (8*scale n)^R := hp.trans (Nat.pow_le_pow_right (by omega) hj)
  have huR : (call.folded S:ℝ) ≤ (8*(scale n:ℝ))^R := by exact_mod_cast hu
  have hbase : 8*(scale n:ℝ) ≤ 8192*((n:ℝ)^eta*(Real.log (n:ℝ))^4) := by
    nlinarith [mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) eta)
      (pow_nonneg (show 0 ≤ Real.log (n:ℝ) by linarith [PhaseGeometry.one_le_log_nat n hn]) 4)]
  calc
    (call.folded S:ℝ) ≤ (8*(scale n:ℝ))^R := huR
    _  ≤  (8192*((n:ℝ)^eta*(Real.log (n:ℝ))^4))^R := by gcongr
    _ = _ := by
      rw [mul_pow,mul_pow,← Real.rpow_mul_natCast (Nat.cast_nonneg n),← pow_mul]
      rw [show eta*(R:ℝ)=b by linarith [witness_values.2.2.1]]
      ring

theorem dimension_upper (n : ℕ) (hn : 3 ≤ n) (call : Call n) :
    (dimension n call:ℝ) ≤ overheadConstant*(Real.log (n:ℝ))^(4*R)*(n:ℝ)^(2*b) := by
  have hp := PhaseGeometry.pad4_upper (block n*(3*call.folded S))
    (by have := block_pos n; have := folded_pos n hn call; positivity)
  have hpR : (dimension n call:ℝ) ≤ 4*((block n:ℝ)*(3*(call.folded S:ℝ))) := by exact_mod_cast hp
  have hh := (block_bounds n (by omega)).2
  have hd := folded_upper n hn call
  calc
    (dimension n call:ℝ) ≤ 4*((block n:ℝ)*(3*(call.folded S:ℝ))) := hpR
    _  ≤  4*((2*(n:ℝ)^b)*(3*((8192:ℝ)^R*(Real.log (n:ℝ))^(4*R)*(n:ℝ)^b))) := by
      gcongr
    _ = _ := by
      rw [show 2*b=b+b by ring,Real.rpow_add (by exact_mod_cast (show 0 < n by omega))]
      unfold overheadConstant
      ring

/-- The actual number of compact blocks supplies n^(1-b)/2 columns even
before the nonempty cyclic axis is included. -/
theorem block_supply (n : ℕ) (hn : 1 ≤ n) :
    (n:ℝ)^(1-b) ≤ 2*(blocks n:ℝ) := by
  have hfit : (n:ℝ) ≤ (blocks n:ℝ)*(block n:ℝ) := by
    exact_mod_cast CompactBlocks.block_fit n (block n) (block_pos n)
  have hh := (block_bounds n hn).2
  have hn0 : 0 < (n:ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hp : 0 < (n:ℝ)^b := Real.rpow_pos_of_pos hn0 _
  apply (mul_le_mul_iff_left₀ hp).mp
  rw [mul_comm _ ((n:ℝ)^b),← Real.rpow_add hn0]
  rw [show b+(1-b)=1 by ring,Real.rpow_one]
  have hh' := mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg (blocks n))
  nlinarith

theorem column_supply (n : ℕ) (hn : 3 ≤ n) (call : Call n) :
    (n:ℝ)^(1-b) ≤ 2*(columns n call:ℝ) := by
  have h := block_supply n (by omega)
  have hq : 1 ≤ call.cyclic S := cyclic_pos n hn call
  have hc : blocks n ≤ columns n call := by
    exact Nat.le_mul_of_pos_right _ hq
  have hcR : (blocks n:ℝ) ≤ columns n call := by exact_mod_cast hc
  linarith

theorem dimension_lower (n : ℕ) (hn : 3 ≤ n) (call : Call n) :
    (n:ℝ)^b ≤ (dimension n call:ℝ) := by
  have hh := (block_bounds n (by omega)).1
  have hf : 1 ≤ call.folded S := folded_pos n hn call
  have hp := PhaseGeometry.pad4_lower (block n*(3*call.folded S))
  have hm : block n ≤ dimension n call := by
    exact (Nat.le_mul_of_pos_right _ (by omega : 0 < 3*call.folded S)).trans hp
  exact hh.trans (by exact_mod_cast hm)

/-- A full fixed positive power of D remains available beyond the long
rectangle axis exponent. The proof covers every intermediate candidate call,
including discarded candidates and the final stage. -/
theorem independent_strict_fit :
    ∀ᶠ n : ℕ in atTop, ∀ call : Call n,
      (dimension n call:ℝ)^(15*zeta+1) ≤ (columns n call:ℝ) := by
  let a : ℝ := 15*zeta+1
  have ha : 0 ≤ a := by norm_num [a,zeta]
  have hg : 2*b*a < 1-b := witness_values.2.2.2
  have hfit := AsymptoticCosts.eventualPowerFit hg
    (Nat.ceil ((4*R:ℕ)*a)) (2*overheadConstant^a)
  filter_upwards [hfit,eventually_ge_atTop (3:ℕ)] with n hnfit hn
  intro call
  have hD := PhaseGeometry.poweredLogBound (4*R) (Nat.cast_nonneg (dimension n call))
    (show 0 ≤ overheadConstant by unfold overheadConstant; positivity)
    (Nat.cast_nonneg n) (PhaseGeometry.one_le_log_nat n hn) ha (dimension_upper n hn call)
  have hB := column_supply n hn call
  change (dimension n call:ℝ)^a ≤ (columns n call:ℝ)
  nlinarith

theorem support_padding_pos (C k n D : ℕ) (hC : 0 < C) : 0 < supportPadding C k n D := by
  unfold supportPadding ComputableParameters.roundedPower
  positivity

/-- Every fixed amount of logarithmic support padding fits in the separate
one-power slack. No upper bound on the number of requests is used. -/
theorem padded_axis_fit (C k : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ call : Call n,
      (supportPadding C k n (dimension n call):ℝ)^15 ≤
        (dimension n call:ℝ)^(15*zeta+1) := by
  have hb : 0 < b := by norm_num [b,bNumerator,bDenominator]
  have hp := AsymptoticCosts.eventualPowerFit (a:=0) hb (15*k)
    ((2*(C:ℝ))^15*5^(15*k))
  filter_upwards [hp,eventually_ge_atTop (3:ℕ)] with n hpn hn
  intro call
  let D := dimension n call
  have hDpos : 0 < D := dimension_pos n call
  have hD0 : 0 ≤ (D:ℝ) := Nat.cast_nonneg D
  have hlog := PhaseGeometry.one_le_log_nat n hn
  have hs : ((n.size:ℝ)+1) ≤ 5*Real.log (n:ℝ) := by
    linarith [ComputableParameters.size_le_four_log n hn]
  have hr := (ComputableParameters.roundedPower_bounds 11 50 D (by norm_num) (by norm_num)
    (by omega)).2
  change (ComputableParameters.roundedPower 11 50 D:ℝ) ≤ 2*(D:ℝ)^zeta at hr
  have hbase : (supportPadding C k n D:ℝ) ≤
      (2*(C:ℝ))*(5*Real.log (n:ℝ))^k*(D:ℝ)^zeta := by
    unfold supportPadding
    push_cast
    calc
      (C:ℝ)*((n.size:ℝ)+1)^k*(ComputableParameters.roundedPower 11 50 D:ℝ)
          ≤ (C:ℝ)*(5*Real.log (n:ℝ))^k*(2*(D:ℝ)^zeta) := by gcongr
      _ = _ := by ring
  have hpower := pow_le_pow_left₀ (Nat.cast_nonneg (supportPadding C k n D)) hbase 15
  have hid : ((2*(C:ℝ))*(5*Real.log (n:ℝ))^k*(D:ℝ)^zeta)^15 =
      ((2*(C:ℝ))^15*5^(15*k)*(Real.log (n:ℝ))^(15*k)) * (D:ℝ)^(15*zeta) := by
    rw [mul_pow,mul_pow,mul_pow,← pow_mul,← Real.rpow_mul_natCast hD0]
    norm_num only [Nat.cast_ofNat]
    rw [show zeta*(15:ℝ)=15*zeta by ring, Nat.mul_comm k 15, mul_pow]
    ring
  rw [hid] at hpower
  have hcoeff : (2*(C:ℝ))^15*5^(15*k)*(Real.log (n:ℝ))^(15*k) ≤ (D:ℝ) := by
    simpa only [Real.rpow_zero,mul_one] using hpn.trans (dimension_lower n hn call)
  calc
    (supportPadding C k n D:ℝ)^15 ≤
      ((2*(C:ℝ))^15*5^(15*k)*(Real.log (n:ℝ))^(15*k)) * (D:ℝ)^(15*zeta) := hpower
    _ ≤ (D:ℝ)*(D:ℝ)^(15*zeta) :=
      mul_le_mul_of_nonneg_right hcoeff (Real.rpow_nonneg hD0 _)
    _ = (D:ℝ)^(15*zeta+1) := by
      rw [Real.rpow_add (by exact_mod_cast hDpos),Real.rpow_one,mul_comm]

/-- The actual integer long chunk fits in the actual independent block and
cyclic-column supply, after all fixed support padding. -/
theorem rounded_batch_fit (C k : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ call : Call n,
      (supportPadding C k n (dimension n call))^15 ≤ columns n call := by
  filter_upwards [padded_axis_fit C k,independent_strict_fit] with n hs hc
  intro call
  exact_mod_cast (hs call).trans (hc call)

/-- Formal-degree columns only increase the independently supplied batch.
This is the exact long side used by PrefixBlockBatch. -/
theorem production_columns_fit (C k : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ call : Call n, ∀ m : ℕ,
      (supportPadding C k n (dimension n call))^15 ≤
        blocks n*((m+1)*call.cyclic S) := by
  filter_upwards [rounded_batch_fit C k] with n hn
  intro call m
  have h := hn call
  have hm : columns n call ≤ blocks n*((m+1)*call.cyclic S) := by
    unfold columns
    calc
      blocks n*call.cyclic S = blocks n*(1*call.cyclic S) := by ring
      _ ≤ blocks n*((m+1)*call.cyclic S) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (by omega))
  exact h.trans hm

#print axioms dimension_lower
#print axioms independent_strict_fit
#print axioms support_padding_pos
#print axioms padded_axis_fit
#print axioms rounded_batch_fit
#print axioms production_columns_fit
#print axioms witness_values
#print axioms block_pos
#print axioms block_bounds
#print axioms scale_bounds
#print axioms scale_pos
#print axioms folded_pos
#print axioms cyclic_pos
#print axioms dimension_pos
#print axioms folded_upper
#print axioms dimension_upper
#print axioms block_supply
#print axioms column_supply
end ThinMatrix.HalfSourceBatchFit
