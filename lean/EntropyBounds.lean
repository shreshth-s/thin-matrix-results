import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Tactic

/-!
Finite binomial/entropy estimates used by the thin-product count analysis.
All entropy estimates below are derived from finite binomial sums.
-/
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
namespace ThinMatrix.EntropyBounds
open scoped BigOperators
noncomputable section

/-- The real-valued mass of one binomial coefficient. -/
def mass (n j : ℕ) (p : ℝ) : ℝ :=
  (n.choose j : ℝ) * p ^ j * (1-p) ^ (n-j)

theorem mass_nonneg (n j : ℕ) {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    0 ≤ mass n j p := by
  unfold mass
  positivity

theorem mass_sum (n : ℕ) (p : ℝ) :
    ∑ j ∈ Finset.range (n+1), mass n j p = 1 := by
  have h := add_pow p (1-p) n
  have heq : p + (1-p) = 1 := by ring
  rw [heq, one_pow] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro j hj
  unfold mass
  ring

theorem mass_le_one (n j : ℕ) (hj : j ≤ n) {p : ℝ}
    (hp : 0 ≤ p) (hp1 : p ≤ 1) : mass n j p ≤ 1 := by
  rw [← mass_sum n p]
  exact Finset.single_le_sum (fun i hi => mass_nonneg n i hp hp1)
    (Finset.mem_range.mpr (by omega))

/-- Exact adjacent-mass identity, including finite endpoints. -/
theorem mass_succ_identity (n j : ℕ) (hj : j < n) (p : ℝ) :
    mass n (j+1) p * ((j+1 : ℕ) : ℝ) * (1-p) =
      mass n j p * ((n-j : ℕ) : ℝ) * p := by
  have hchoose : (n.choose (j+1) : ℝ) * ((j+1 : ℕ) : ℝ) =
      (n.choose j : ℝ) * ((n-j : ℕ) : ℝ) := by
    exact_mod_cast Nat.choose_succ_right_eq n j
  have hn : n-j = (n-(j+1))+1 := by omega
  unfold mass
  rw [hn, pow_succ]
  simp only [pow_succ]
  rw [hn] at hchoose
  linear_combination (p ^ j * (1-p) ^ (n-(j+1)) * p * (1-p)) * hchoose


/-- At its empirical probability, the designated binomial mass increases
up to index `k`. -/
theorem mass_step_up (n k j : ℕ) (hk : k < n) (hj : j < k) :
    mass n j ((k:ℝ)/n) ≤ mass n (j+1) ((k:ℝ)/n) := by
  let p : ℝ := (k:ℝ)/n
  have hn : (0:ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt hk)
  have hp0 : 0 ≤ p := by positivity
  have hp1 : p < 1 := (div_lt_one hn).2 (by exact_mod_cast hk)
  have hnp : (n:ℝ)*p = k := by dsimp [p]; field_simp
  have hcast : ((n-j:ℕ):ℝ) = (n:ℝ)-j := Nat.cast_sub (by omega)
  have hcoeff : ((j+1:ℕ):ℝ)*(1-p) ≤ ((n-j:ℕ):ℝ)*p := by
    rw [hcast]
    have hkj : (j:ℝ)+1 ≤ k := by exact_mod_cast hj
    push_cast
    nlinarith
  have hpos : 0 < ((j+1:ℕ):ℝ)*(1-p) := by positivity
  have hid := mass_succ_identity n j (by omega) p
  apply (mul_le_mul_iff_left₀ hpos).mp
  calc
    mass n j p * (((j+1:ℕ):ℝ)*(1-p)) ≤
        mass n j p * (((n-j:ℕ):ℝ)*p) :=
      mul_le_mul_of_nonneg_left hcoeff (mass_nonneg n j hp0 hp1.le)
    _ = mass n (j+1) p * (((j+1:ℕ):ℝ)*(1-p)) := by nlinarith [hid]

/-- At its empirical probability, the designated binomial mass decreases
after index `k`. -/
theorem mass_step_down (n k j : ℕ) (hk : k < n) (hkj : k ≤ j) (hj : j < n) :
    mass n (j+1) ((k:ℝ)/n) ≤ mass n j ((k:ℝ)/n) := by
  let p : ℝ := (k:ℝ)/n
  have hn : (0:ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt hk)
  have hp0 : 0 ≤ p := by positivity
  have hp1 : p < 1 := (div_lt_one hn).2 (by exact_mod_cast hk)
  have hnp : (n:ℝ)*p = k := by dsimp [p]; field_simp
  have hcast : ((n-j:ℕ):ℝ) = (n:ℝ)-j := Nat.cast_sub hj.le
  have hcoeff : ((n-j:ℕ):ℝ)*p ≤ ((j+1:ℕ):ℝ)*(1-p) := by
    rw [hcast]
    have hkj' : (k:ℝ) ≤ j := by exact_mod_cast hkj
    push_cast
    nlinarith
  have hpos : 0 < ((j+1:ℕ):ℝ)*(1-p) := by positivity
  have hid := mass_succ_identity n j hj p
  apply (mul_le_mul_iff_left₀ hpos).mp
  calc
    mass n (j+1) p * (((j+1:ℕ):ℝ)*(1-p)) =
        mass n j p * (((n-j:ℕ):ℝ)*p) := by nlinarith [hid]
    _ ≤ mass n j p * (((j+1:ℕ):ℝ)*(1-p)) :=
      mul_le_mul_of_nonneg_left hcoeff (mass_nonneg n j hp0 hp1.le)


private theorem chain_le (f : ℕ → ℝ) (a b : ℕ) (hab : a ≤ b)
    (hstep : ∀ j, a ≤ j → j < b → f j ≤ f (j+1)) : f a ≤ f b := by
  have h : ∀ j, a ≤ j → j ≤ b → f a ≤ f j := by
    intro j hja
    induction j, hja using Nat.le_induction with
    | base => intro _; exact le_rfl
    | succ j hja ih =>
      intro hjb
      exact (ih (by omega)).trans (hstep j hja (by omega))
  exact h b hab le_rfl

/-- The empirical-probability coefficient is a mode of the finite
binomial distribution; this is proved from the adjacent coefficient identity. -/
theorem mass_mode (n k j : ℕ) (hk : k < n) (hj : j ≤ n) :
    mass n j ((k:ℝ)/n) ≤ mass n k ((k:ℝ)/n) := by
  rcases le_total j k with hjk | hkj
  · apply chain_le (fun i => mass n i ((k:ℝ)/n)) j k hjk
    intro i hji hik
    exact mass_step_up n k i hk hik
  · have h := chain_le (fun i => -mass n i ((k:ℝ)/n)) k j hkj (by
      intro i hki hij
      exact neg_le_neg (mass_step_down n k i hk hki (by omega)))
    linarith

/-- A finite mode has probability at least the reciprocal of the number
of possible outcomes. -/
theorem mass_mode_lower (n k : ℕ) (hk : k < n) :
    1 / (n+1:ℝ) ≤ mass n k ((k:ℝ)/n) := by
  have hsum : (1:ℝ) ≤ (n+1:ℝ) * mass n k ((k:ℝ)/n) := by
    calc
      (1:ℝ) = ∑ j ∈ Finset.range (n+1), mass n j ((k:ℝ)/n) := (mass_sum _ _).symm
      _ ≤ ∑ _j ∈ Finset.range (n+1), mass n k ((k:ℝ)/n) := by
        apply Finset.sum_le_sum
        intro j hj
        exact mass_mode n k j hk (by have := Finset.mem_range.mp hj; omega)
      _ = (n+1:ℝ) * mass n k ((k:ℝ)/n) := by simp
  exact (div_le_iff₀ (by positivity : (0:ℝ) < n+1)).2 (by nlinarith [hsum])

/-- Natural-log entropy agrees with the canonical proof's convention. -/
theorem binEntropy_eq (p : ℝ) :
    Real.binEntropy p = -p * Real.log p - (1-p) * Real.log (1-p) := by
  simp only [Real.binEntropy, Real.log_inv]
  ring

/-- The reciprocal Bernoulli weight is the entropy exponential. -/
theorem entropy_weight_identity (n k : ℕ) (hk0 : 0 < k) (hk : k < n) :
    Real.exp ((n:ℝ) * Real.binEntropy ((k:ℝ)/n)) *
      (((k:ℝ)/n)^k * (1-(k:ℝ)/n)^(n-k)) = 1 := by
  let p : ℝ := (k:ℝ)/n
  have hn : (0:ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt hk)
  have hp : 0 < p := div_pos (by exact_mod_cast hk0) hn
  have hp1 : p < 1 := (div_lt_one hn).2 (by exact_mod_cast hk)
  have hnp : (n:ℝ)*p = k := by dsimp [p]; field_simp
  have hcomp : (n:ℝ)*(1-p) = ((n-k:ℕ):ℝ) := by
    rw [Nat.cast_sub hk.le]
    nlinarith
  have hlog : Real.log (p^k * (1-p)^(n-k)) = -(n:ℝ)*Real.binEntropy p := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow,
      binEntropy_eq]
    linear_combination -(Real.log p)*hnp - (Real.log (1-p))*hcomp
  change Real.exp ((n:ℝ)*Real.binEntropy p) * (p^k*(1-p)^(n-k)) = 1
  rw [← Real.exp_log (by positivity : 0 < p^k*(1-p)^(n-k)), ← Real.exp_add, hlog]
  simp

/-- General finite upper entropy bound, proved by a single term of the
binomial theorem rather than assumed as an external estimate. -/
theorem choose_entropy_upper (n k : ℕ) (hk0 : 0 < k) (hk : k < n) :
    (n.choose k : ℝ) ≤ Real.exp ((n:ℝ)*Real.binEntropy ((k:ℝ)/n)) := by
  have hn : (0:ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt hk)
  have hp : (0:ℝ) < (k:ℝ)/n := div_pos (by exact_mod_cast hk0) hn
  have hp1 : (k:ℝ)/n < 1 := (div_lt_one hn).2 (by exact_mod_cast hk)
  have hmass := mass_le_one n k hk.le hp.le hp1.le
  have hid := entropy_weight_identity n k hk0 hk
  apply (mul_le_mul_iff_left₀ (by positivity : 0 < ((k:ℝ)/n)^k * (1-(k:ℝ)/n)^(n-k))).mp
  unfold mass at hmass
  nlinarith [hmass, hid]

/-- General finite lower entropy bound. The only loss is the finite
number `n+1` of binomial outcomes. -/
theorem choose_entropy_lower (n k : ℕ) (hk0 : 0 < k) (hk : k < n) :
    Real.exp ((n:ℝ)*Real.binEntropy ((k:ℝ)/n)) / (n+1) ≤ (n.choose k : ℝ) := by
  have hn : (0:ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt hk)
  have hp : (0:ℝ) < (k:ℝ)/n := div_pos (by exact_mod_cast hk0) hn
  have hp1 : (k:ℝ)/n < 1 := (div_lt_one hn).2 (by exact_mod_cast hk)
  have hmass := mass_mode_lower n k hk
  have hid := entropy_weight_identity n k hk0 hk
  apply (mul_le_mul_iff_left₀ (by positivity : 0 < ((k:ℝ)/n)^k * (1-(k:ℝ)/n)^(n-k))).mp
  unfold mass at hmass
  rw [div_mul_eq_mul_div, hid]
  simpa [mul_assoc] using hmass


/-- Endpoint-inclusive version of the upper coefficient bound. -/
theorem choose_entropy_upper_of_le (n k : ℕ) (hk : k ≤ n) :
    (n.choose k : ℝ) ≤ Real.exp ((n:ℝ)*Real.binEntropy ((k:ℝ)/n)) := by
  by_cases hk0 : k = 0
  · simp [hk0]
  by_cases hkn : k = n
  · subst k
    by_cases hn : n = 0
    · simp [hn]
    · simp [hn]
  exact choose_entropy_upper n k (Nat.pos_of_ne_zero hk0) (lt_of_le_of_ne hk hkn)

/-- Endpoint-inclusive version of the lower coefficient bound. -/
theorem choose_entropy_lower_of_le (n k : ℕ) (hk : k ≤ n) :
    Real.exp ((n:ℝ)*Real.binEntropy ((k:ℝ)/n)) / (n+1) ≤ (n.choose k : ℝ) := by
  by_cases hk0 : k = 0
  · simp only [hk0, Nat.cast_zero, zero_div, Real.binEntropy_zero, mul_zero, Real.exp_zero,
      Nat.choose_zero_right, Nat.cast_one]
    apply (div_le_iff₀ (by positivity : (0:ℝ)<n+1)).2
    norm_num
  by_cases hkn : k = n
  · subst k
    by_cases hn : n = 0
    · simp [hn]
    · simp only [div_self (by exact_mod_cast hn : (n:ℝ) ≠ 0), Real.binEntropy_one,
        mul_zero, Real.exp_zero, Nat.choose_self, Nat.cast_one]
      apply (div_le_iff₀ (by positivity : (0:ℝ)<n+1)).2
      norm_num
  exact choose_entropy_lower n k (Nat.pos_of_ne_zero hk0) (lt_of_le_of_ne hk hkn)

/-- Unweighted channel count. -/
def channelTail (n t : ℕ) : ℝ := ∑ j ∈ Finset.range (t+1), (n.choose j : ℝ)

/-- Both finite entropy bounds for the channel count, with its actual
integer cutoff. The upper loss is polynomial, not exponential. -/
theorem channelTail_entropy (n t : ℕ) (hn : 0 < n) (ht : (t:ℝ)/n ≤ 1/2) :
    Real.exp ((n:ℝ)*Real.binEntropy ((t:ℝ)/n)) / (n+1) ≤ channelTail n t ∧
    channelTail n t ≤ (t+1) * Real.exp ((n:ℝ)*Real.binEntropy ((t:ℝ)/n)) := by
  have hn' : (0:ℝ)<n := by exact_mod_cast hn
  have ht' : t ≤ n := by
    have := (div_le_iff₀ hn').1 ht
    exact_mod_cast (show (t:ℝ) ≤ n by nlinarith)
  constructor
  · apply (choose_entropy_lower_of_le n t ht').trans
    unfold channelTail
    exact Finset.single_le_sum (f := fun j => (n.choose j : ℝ))
      (a := t) (fun j hj => by positivity)
      (Finset.mem_range.mpr (by omega))
  · unfold channelTail
    calc
      (∑ j ∈ Finset.range (t+1), (n.choose j : ℝ)) ≤
          ∑ _j ∈ Finset.range (t+1), Real.exp ((n:ℝ)*Real.binEntropy ((t:ℝ)/n)) := by
        apply Finset.sum_le_sum
        intro j hj
        have hjt : j ≤ t := by have := Finset.mem_range.mp hj; omega
        have hje : Real.binEntropy ((j:ℝ)/n) ≤ Real.binEntropy ((t:ℝ)/n) := by
          apply Real.binEntropy_strictMonoOn.monotoneOn
          · constructor
            · positivity
            · have hdiv : (j:ℝ)/n ≤ (t:ℝ)/n := by gcongr
              norm_num at ht ⊢
              linarith
          · constructor
            · positivity
            · norm_num at ht ⊢; exact ht
          · gcongr
        apply (choose_entropy_upper_of_le n j (hjt.trans ht')).trans
        exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hje hn'.le)
      _ = (t+1) * Real.exp ((n:ℝ)*Real.binEntropy ((t:ℝ)/n)) := by simp


/-- One ordinary-label count at a fixed distinguished support size. -/
def ordinaryTerm (L j : ℕ) : ℝ := (L.choose j : ℝ) * 4^(L-j)
def ordinaryTail (L m : ℕ) : ℝ := ∑ j ∈ Finset.range (m+1), ordinaryTerm L j

theorem ordinaryTerm_identity (L j : ℕ) (hj : j < L) :
    ordinaryTerm L j * ((L-j:ℕ):ℝ) =
      4 * ((j+1:ℕ):ℝ) * ordinaryTerm L (j+1) := by
  have hchoose : (L.choose (j+1) : ℝ) * ((j+1:ℕ):ℝ) =
      (L.choose j : ℝ) * ((L-j:ℕ):ℝ) := by
    exact_mod_cast Nat.choose_succ_right_eq L j
  have hL : L-j = (L-(j+1))+1 := by omega
  unfold ordinaryTerm
  rw [hL, pow_succ]
  rw [hL] at hchoose
  linear_combination -(4:ℝ)^(L-(j+1))*4*hchoose

/-- Finite adjacent-ratio bound for the ordinary encoder tail. -/
theorem ordinaryTerm_step (L m j : ℕ) (hm : m ≤ L) (hj : j < m) :
    ordinaryTerm L j ≤ (4*(m:ℝ)/(L-m+1)) * ordinaryTerm L (j+1) := by
  have hLj : ((L-j:ℕ):ℝ) = (L:ℝ)-j := Nat.cast_sub (by omega)
  have hLm : (0:ℝ) < (L:ℝ)-m+1 := by
    have hm' : (m:ℝ) ≤ L := by exact_mod_cast hm
    linarith
  have hpos : (0:ℝ) < ((L-j:ℕ):ℝ) := by exact_mod_cast (show 0 < L-j by omega)
  have hid := ordinaryTerm_identity L j (by omega)
  have hcoeff : 4*((j+1:ℕ):ℝ) ≤ (4*(m:ℝ)/(L-m+1))*((L-j:ℕ):ℝ) := by
    rw [hLj, div_mul_eq_mul_div]
    apply (le_div_iff₀ hLm).2
    have hj' : (j:ℝ)+1 ≤ m := by exact_mod_cast hj
    have hm' : (m:ℝ) ≤ L := by exact_mod_cast hm
    push_cast
    nlinarith
  apply (mul_le_mul_iff_left₀ hpos).mp
  calc
    ordinaryTerm L j * ((L-j:ℕ):ℝ) =
        4*((j+1:ℕ):ℝ)*ordinaryTerm L (j+1) := hid
    _ ≤ ((4*(m:ℝ)/(L-m+1))*((L-j:ℕ):ℝ))*ordinaryTerm L (j+1) :=
      mul_le_mul_of_nonneg_right hcoeff (by unfold ordinaryTerm; positivity)
    _ = ((4*(m:ℝ)/(L-m+1))*ordinaryTerm L (j+1))*((L-j:ℕ):ℝ) := by ring

/-- A generic reverse-geometric finite tail bound. -/
theorem reverse_geometric_tail (f : ℕ → ℝ) (m : ℕ) (r : ℝ)
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hf : ∀ j, 0 ≤ f j)
    (hstep : ∀ j < m, f j ≤ r*f (j+1)) :
    (∑ j ∈ Finset.range (m+1), f j) ≤ f m / (1-r) := by
  have hsum := Finset.sum_le_sum (s := Finset.range m) (fun j hj =>
    hstep j (Finset.mem_range.mp hj))
  have hshift : (∑ j ∈ Finset.range m, f (j+1)) =
      (∑ j ∈ Finset.range (m+1), f j) - f 0 := by
    rw [Finset.sum_range_succ']
    ring
  rw [← Finset.mul_sum, hshift] at hsum
  have hlast : (∑ j ∈ Finset.range m, f j) =
      (∑ j ∈ Finset.range (m+1), f j) - f m := by
    rw [Finset.sum_range_succ]
    ring
  rw [hlast] at hsum
  apply (le_div_iff₀ (by linarith : 0 < 1-r)).2
  nlinarith [hf 0]

/-- The actual `c>5` geometric tail: no entropy estimate is a hypothesis. -/
theorem ordinaryTail_geometric (L m : ℕ) (hLm : 5*m ≤ L) :
    ordinaryTail L m ≤ ordinaryTerm L m / (1 - 4*(m:ℝ)/(L-m+1)) := by
  have hm : m ≤ L := by omega
  have hm' : (m:ℝ) ≤ L := by exact_mod_cast hm
  have hLm' : 5*(m:ℝ) ≤ L := by exact_mod_cast hLm
  have hden : (0:ℝ) < (L:ℝ)-m+1 := by linarith
  apply reverse_geometric_tail
  · positivity
  · apply (div_lt_one hden).2
    linarith
  · intro j; unfold ordinaryTerm; positivity
  · intro j hj; exact ordinaryTerm_step L m j hm hj


/-- The logarithm of the entropy approximation to one full-grid side. -/
def gridLog (m x : ℝ) : ℝ :=
  x*Real.log x - (x-m)*Real.log (x-m) - m*Real.log m + (x-m)*Real.log 4

theorem gridLog_entropy (m x : ℝ) (hm : 0 < m) (hx : m < x) :
    gridLog m x = (x-m)*Real.log 4 + x*Real.binEntropy (m/x) := by
  have hx0 : 0 < x := hm.trans hx
  have hcomp : 1-m/x = (x-m)/x := by field_simp
  rw [binEntropy_eq, hcomp, Real.log_div hm.ne' hx0.ne',
    Real.log_div (sub_pos.mpr hx).ne' hx0.ne']
  unfold gridLog
  field_simp
  ring

theorem hasDerivAt_gridLog (m x : ℝ) (hx : x ≠ 0) (hxm : x-m ≠ 0) :
    HasDerivAt (gridLog m) (Real.log x - Real.log (x-m) + Real.log 4) x := by
  have h1 := Real.hasDerivAt_mul_log hx
  have h2 := (Real.hasDerivAt_mul_log hxm).comp_sub_const x m
  have h3 := ((hasDerivAt_id x).sub_const m).mul_const (Real.log 4)
  have h := ((h1.sub h2).sub_const (m*Real.log m)).add h3
  have heq : Real.log x+1-(Real.log (x-m)+1)+1*Real.log 4 =
      Real.log x-Real.log (x-m)+Real.log 4 := by ring
  rw [heq] at h
  exact h

/-- Exact finite rounding control for the grid entropy expression.
The ceiling introduces a bounded additive logarithmic error. -/
theorem rounded_gridLog (c : ℝ) (m : ℕ) (hc : 1 < c) (hm : 0 < m) :
    let L := Nat.ceil (c*(m:ℝ))
    let base := (m:ℝ)*((c-1)*Real.log 4+c*Real.binEntropy (1/c))
    base ≤ gridLog m L ∧
      gridLog m L ≤ base + (Real.log 4+Real.log (c/(c-1))) := by
  let a : ℝ := c*(m:ℝ)
  let L : ℝ := Nat.ceil a
  let C : ℝ := Real.log 4+Real.log (c/(c-1))
  have hm' : (0:ℝ)<m := by exact_mod_cast hm
  have ha : 0 < a := mul_pos (by linarith) hm'
  have hma : (m:ℝ)<a := by dsimp [a]; nlinarith
  have haL : a ≤ L := Nat.le_ceil a
  have hLa : L < a+1 := Nat.ceil_lt_add_one ha.le
  have hC : 0 < C := by
    have hratio : 1 < c/(c-1) := (one_lt_div (by linarith)).2 (by linarith)
    dsimp [C]
    exact add_pos (Real.log_pos (by norm_num)) (Real.log_pos hratio)
  have hdiff : ∀ x ∈ Set.Icc a L, DifferentiableAt ℝ (gridLog m) x := by
    intro x hx
    exact (hasDerivAt_gridLog m x (by linarith [hx.1]) (by linarith [hx.1])).differentiableAt
  have hcont : ContinuousOn (gridLog m) (Set.Icc a L) := by
    intro x hx
    exact (hdiff x hx).continuousAt.continuousWithinAt
  have hdiffOn : DifferentiableOn ℝ (gridLog m) (interior (Set.Icc a L)) := by
    intro x hx
    apply (hdiff x (interior_subset hx)).differentiableWithinAt
  have hderiv : ∀ x ∈ interior (Set.Icc a L),
      deriv (gridLog m) x = Real.log (x/(x-m))+Real.log 4 := by
    intro x hx
    have hx' := interior_subset hx
    have hxm : (m:ℝ)<x := lt_of_lt_of_le hma hx'.1
    rw [(hasDerivAt_gridLog m x (by linarith) (by linarith)).deriv]
    rw [Real.log_div (by linarith) (by linarith)]
  have hupper : ∀ x ∈ interior (Set.Icc a L), deriv (gridLog m) x ≤ C := by
    intro x hx
    have hx' := interior_subset hx
    have hxm : (m:ℝ)<x := lt_of_lt_of_le hma hx'.1
    have hr : x/(x-m) ≤ c/(c-1) := by
      apply (div_le_div_iff₀ (by linarith) (by linarith)).2
      dsimp [a] at hx'
      nlinarith [hx'.1]
    rw [hderiv x hx]
    have hl := Real.log_le_log (div_pos (by linarith) (by linarith) : 0 < x/(x-m)) hr
    dsimp [C]
    linarith
  have hlower : ∀ x ∈ interior (Set.Icc a L), 0 ≤ deriv (gridLog m) x := by
    intro x hx
    have hx' := interior_subset hx
    have hxm : (m:ℝ)<x := lt_of_lt_of_le hma hx'.1
    have hr : 1 < x/(x-m) := (one_lt_div (by linarith)).2 (by linarith)
    rw [hderiv x hx]
    exact add_nonneg (Real.log_pos hr).le (Real.log_pos (by norm_num)).le
  have hmono := monotoneOn_of_deriv_nonneg (convex_Icc a L) hcont hdiffOn hlower
  have hlo := hmono (Set.left_mem_Icc.mpr haL) (Set.right_mem_Icc.mpr haL) haL
  have hhi := (convex_Icc a L).image_sub_le_mul_sub_of_deriv_le
    hcont hdiffOn hupper a (Set.left_mem_Icc.mpr haL) L (Set.right_mem_Icc.mpr haL) haL
  have hbase : gridLog m a = (m:ℝ)*((c-1)*Real.log 4+c*Real.binEntropy (1/c)) := by
    rw [gridLog_entropy m a hm' hma]
    have hr : (m:ℝ)/a = 1/c := by dsimp [a]; field_simp
    rw [hr]
    dsimp [a]
    ring
  change _ ≤ gridLog m L ∧ gridLog m L ≤ _+C
  rw [← hbase]
  constructor
  · exact hlo
  · nlinarith


/-- One side of the original full grid: `K*N₀`, with `N₀=4^(L-m)`. -/
def gridCount (L m : ℕ) : ℝ := (L.choose m : ℝ)*4^(L-m)

theorem gridCount_entropy (L m : ℕ) (hm : 0 < m) (hmL : m < L) :
    Real.exp (gridLog m L)/(L+1) ≤ gridCount L m ∧
      gridCount L m ≤ Real.exp (gridLog m L) := by
  have hm' : (0:ℝ)<m := by exact_mod_cast hm
  have hmL' : (m:ℝ)<L := by exact_mod_cast hmL
  have hexp : Real.exp (gridLog m L) =
      Real.exp ((L:ℝ)*Real.binEntropy ((m:ℝ)/L))*4^(L-m) := by
    rw [gridLog_entropy m L hm' hmL', Real.exp_add]
    have h4 : Real.exp (((L-m:ℕ):ℝ)*Real.log 4) = (4:ℝ)^(L-m) := by
      rw [← Real.log_pow, Real.exp_log (by positivity)]
    rw [← Nat.cast_sub hmL.le, h4]
    ring
  constructor
  · rw [hexp]
    unfold gridCount
    rw [← div_mul_eq_mul_div]
    exact mul_le_mul_of_nonneg_right (choose_entropy_lower L m hm hmL) (by positivity)
  · rw [hexp]
    unfold gridCount
    exact mul_le_mul_of_nonneg_right (choose_entropy_upper L m hm hmL) (by positivity)

/-- The original geometric exponent; the encoder exponent is a separate quantity. -/
def tileExponent (c : ℝ) : ℝ := c-1+c*Real.binEntropy (1/c)/Real.log 4

theorem grid_exponential_power (c : ℝ) (m : ℕ) :
    Real.exp ((m:ℝ)*((c-1)*Real.log 4+c*Real.binEntropy (1/c))) =
      ((4:ℝ)^m)^(tileExponent c) := by
  rw [Real.rpow_def_of_pos (by positivity), Real.log_pow]
  congr 1
  unfold tileExponent
  have h4 : Real.log (4:ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  field_simp

/-- Explicit two-sided full-grid bounds at the actual ceiling. The
lower loss is linear in `m=log₄ D`, while the upper factor is constant. -/
theorem rounded_gridCount (c : ℝ) (m : ℕ) (hc : 1 < c) (hm : 0 < m) :
    let L := Nat.ceil (c*(m:ℝ))
    ((4:ℝ)^m)^(tileExponent c) / (L+1) ≤ gridCount L m ∧
    gridCount L m ≤ Real.exp (Real.log 4+Real.log (c/(c-1))) *
      ((4:ℝ)^m)^(tileExponent c) := by
  let L := Nat.ceil (c*(m:ℝ))
  have hm' : (0:ℝ)<m := by exact_mod_cast hm
  have hceil : c*(m:ℝ) ≤ (L:ℝ) := Nat.le_ceil _
  have hmL : m < L := by
    have hmL' : (m:ℝ)<L := by nlinarith
    exact_mod_cast hmL'
  have hg := gridCount_entropy L m hm hmL
  have hr := rounded_gridLog c m hc hm
  dsimp only at hr
  change _ ≤ gridCount L m ∧ gridCount L m ≤ _
  rw [← grid_exponential_power c m]
  constructor
  · apply le_trans _ hg.1
    exact div_le_div_of_nonneg_right (Real.exp_le_exp.mpr hr.1) (by positivity)
  · apply le_trans hg.2
    rw [mul_comm, ← Real.exp_add]
    exact Real.exp_le_exp.mpr hr.2

/-- The ceiling denominator is itself polynomial in the logarithmic parameter. -/
theorem rounded_grid_denominator (c : ℝ) (m : ℕ) (hc : 0 ≤ c) (hm : 0 < m) :
    (Nat.ceil (c*(m:ℝ)) : ℝ)+1 ≤ (c+2)*(m:ℝ) := by
  have h := Nat.ceil_lt_add_one (mul_nonneg hc (Nat.cast_nonneg m))
  have hm' : (1:ℝ) ≤ m := by exact_mod_cast hm
  nlinarith


/-- A proved entropy modulus on the increasing half-interval. -/
theorem binEntropy_right_bound (theta p : ℝ) (ht0 : 0 < theta) (ht1 : theta < 1/2)
    (hp0 : theta ≤ p) (hp1 : p ≤ 1/2) :
    Real.binEntropy theta ≤ Real.binEntropy p ∧
    Real.binEntropy p-Real.binEntropy theta ≤
      (Real.log (1-theta)-Real.log theta)*(p-theta) := by
  have hcont : ContinuousOn Real.binEntropy (Set.Icc theta (1/2)) :=
    Real.binEntropy_continuous.continuousOn
  have hdiff : DifferentiableOn ℝ Real.binEntropy (interior (Set.Icc theta (1/2))) := by
    intro x hx
    have hx' := interior_subset hx
    exact (Real.differentiableAt_binEntropy (by linarith [hx'.1])
      (by linarith [hx'.2])).differentiableWithinAt
  have hbound : ∀ x ∈ interior (Set.Icc theta (1/2)),
      deriv Real.binEntropy x ≤ Real.log (1-theta)-Real.log theta := by
    intro x hx
    have hx' := interior_subset hx
    rw [Real.deriv_binEntropy]
    have hla := Real.log_le_log (by linarith [hx'.2] : 0 < 1-x) (by linarith [hx'.1] : 1-x ≤ 1-theta)
    have hlb := Real.log_le_log ht0 hx'.1
    linarith
  constructor
  · apply Real.binEntropy_strictMonoOn.monotoneOn
    · constructor <;> norm_num <;> linarith
    · constructor <;> norm_num <;> linarith
    · exact hp0
  · exact (convex_Icc theta (1/2)).image_sub_le_mul_sub_of_deriv_le
      hcont hdiff hbound theta (by constructor <;> linarith)
      p (by constructor <;> assumption) hp0

/-- The actual channel ceiling changes the entropy logarithm by a
constant, uniformly in the integer dimension parameter. -/
theorem rounded_channel_entropy (theta : ℝ) (m : ℕ)
    (ht0 : 0 < theta) (ht1 : theta < 1/2) (hm : 0 < m) :
    let t := Nat.ceil (2*theta*(m:ℝ))
    (2*(m:ℝ))*Real.binEntropy theta ≤
      (2*(m:ℝ))*Real.binEntropy ((t:ℝ)/(2*m)) ∧
    (2*(m:ℝ))*Real.binEntropy ((t:ℝ)/(2*m)) ≤
      (2*(m:ℝ))*Real.binEntropy theta + Real.log (1-theta)-Real.log theta := by
  let t := Nat.ceil (2*theta*(m:ℝ))
  let p : ℝ := (t:ℝ)/(2*m)
  have hm' : (0:ℝ)<m := by exact_mod_cast hm
  have hceil : 2*theta*(m:ℝ) ≤ (t:ℝ) := Nat.le_ceil _
  have hceil' : (t:ℝ) < 2*theta*(m:ℝ)+1 := Nat.ceil_lt_add_one (by positivity)
  have htm : t ≤ m := by
    apply Nat.ceil_le.mpr
    nlinarith
  have hp0 : theta ≤ p := by
    apply (le_div_iff₀ (by positivity : (0:ℝ)<2*m)).2
    nlinarith
  have hp1 : p ≤ 1/2 := by
    dsimp [p]
    apply (div_le_iff₀ (by positivity : (0:ℝ)<2*m)).2
    have htm' : (t:ℝ)≤m := by exact_mod_cast htm
    nlinarith
  have h := binEntropy_right_bound theta p ht0 ht1 hp0 hp1
  have hC : 0 < Real.log (1-theta)-Real.log theta := by
    have hl := Real.log_lt_log ht0 (by linarith : theta < 1-theta)
    linarith
  have hdelta : (2*(m:ℝ))*(p-theta) < 1 := by
    dsimp [p]
    field_simp at *
    nlinarith [hceil']
  change _ ≤ (2*(m:ℝ))*Real.binEntropy p ∧ (2*(m:ℝ))*Real.binEntropy p ≤ _
  constructor
  · exact mul_le_mul_of_nonneg_left h.1 (by positivity)
  · have hh := mul_le_mul_of_nonneg_left h.2 (show (0:ℝ) ≤ 2*m by positivity)
    nlinarith

/-- The channel entropy exponent in powers of `D=4^m`. -/
def channelExponent (theta : ℝ) : ℝ := 2*Real.binEntropy theta/Real.log 4

theorem channel_exponential_power (theta : ℝ) (m : ℕ) :
    Real.exp ((2*(m:ℝ))*Real.binEntropy theta) =
      ((4:ℝ)^m)^(channelExponent theta) := by
  rw [Real.rpow_def_of_pos (by positivity), Real.log_pow]
  congr 1
  unfold channelExponent
  have h4 : Real.log (4:ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  field_simp

/-- Two-sided channel counts at the actual cutoff `ceil(2 theta m)`.
Both losses are polynomial in the logarithmic dimension parameter. -/
theorem rounded_channelTail (theta : ℝ) (m : ℕ)
    (ht0 : 0 < theta) (ht1 : theta < 1/2) (hm : 0 < m) :
    let t := Nat.ceil (2*theta*(m:ℝ))
    ((4:ℝ)^m)^(channelExponent theta)/(2*m+1) ≤ channelTail (2*m) t ∧
    channelTail (2*m) t ≤ (t+1)*Real.exp (Real.log (1-theta)-Real.log theta)*
      ((4:ℝ)^m)^(channelExponent theta) := by
  let t := Nat.ceil (2*theta*(m:ℝ))
  have hm' : (0:ℝ)<m := by exact_mod_cast hm
  have htm : t ≤ m := by apply Nat.ceil_le.mpr; nlinarith
  have hp : (t:ℝ)/(2*m) ≤ 1/2 := by
    apply (div_le_iff₀ (by positivity : (0:ℝ)<2*m)).2
    have htm' : (t:ℝ)≤m := by exact_mod_cast htm
    nlinarith
  have hc := channelTail_entropy (2*m) t (by omega) (by simpa only [Nat.cast_mul, Nat.cast_ofNat] using hp)
  have hr := rounded_channel_entropy theta m ht0 ht1 hm
  norm_num only [Nat.cast_mul, Nat.cast_ofNat] at hc
  dsimp only at hr
  change _ ≤ channelTail (2*m) t ∧ channelTail (2*m) t ≤ _
  rw [← channel_exponential_power theta m]
  constructor
  · apply le_trans _ hc.1
    apply div_le_div_of_nonneg_right
    · apply Real.exp_le_exp.mpr
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using hr.1
    · positivity
  · apply le_trans hc.2
    have hh : Real.exp ((2*(m:ℝ))*Real.binEntropy ((t:ℝ)/(2*m))) ≤
        Real.exp (Real.log (1-theta)-Real.log theta)*
          Real.exp ((2*(m:ℝ))*Real.binEntropy theta) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      linarith [hr.2]
    have h := mul_le_mul_of_nonneg_left hh (show (0:ℝ)≤t+1 by positivity)
    simpa only [Nat.cast_mul, Nat.cast_ofNat, mul_assoc, t] using h


/-- The ordinary encoder tail is within a constant of the original
full-grid side at every actual ceiling with `c>5`. -/
theorem rounded_ordinaryTail (c : ℝ) (m : ℕ) (hc : 5 < c) (hm : 0 < m) :
    let L := Nat.ceil (c*(m:ℝ))
    gridCount L m ≤ ordinaryTail L m ∧
    ordinaryTail L m ≤ gridCount L m / (1-4/(c-1)) := by
  let L := Nat.ceil (c*(m:ℝ))
  have hm' : (0:ℝ)<m := by exact_mod_cast hm
  have hceil : c*(m:ℝ) ≤ (L:ℝ) := Nat.le_ceil _
  have hLm : 5*m ≤ L := by
    have hLm' : 5*(m:ℝ) ≤ L := by nlinarith
    exact_mod_cast hLm'
  have hu := ordinaryTail_geometric L m hLm
  have hden : (0:ℝ)<(L:ℝ)-m+1 := by nlinarith
  have hr : 4*(m:ℝ)/(L-m+1) ≤ 4/(c-1) := by
    apply (div_le_div_iff₀ hden (by linarith)).2
    nlinarith
  have hr1 : 4/(c-1) < (1:ℝ) := (div_lt_one (by linarith)).2 (by linarith)
  have hnonneg : 0 ≤ ordinaryTail L m := by unfold ordinaryTail ordinaryTerm; positivity
  change gridCount L m ≤ ordinaryTail L m ∧ ordinaryTail L m ≤ _
  constructor
  · change ordinaryTerm L m ≤ ordinaryTail L m
    unfold ordinaryTail
    exact Finset.single_le_sum (f := ordinaryTerm L) (a := m)
      (fun j hj => by unfold ordinaryTerm; positivity) (Finset.mem_range.mpr (by omega))
  · apply (le_div_iff₀ (by linarith : (0:ℝ)<1-4/(c-1))).2
    have hu' := (le_div_iff₀ (by linarith : (0:ℝ)<1-4*(m:ℝ)/(L-m+1))).1 hu
    have hh := mul_le_mul_of_nonneg_left (sub_le_sub_left hr 1) hnonneg
    change ordinaryTail L m*(1-4/(c-1)) ≤ ordinaryTerm L m
    nlinarith

/-- The geometric dimension is exactly exponential in `m`, so the
explicit linear losses above are logarithmic in that dimension. -/
theorem log_dimension (m : ℕ) : Real.log ((4:ℝ)^m) = (m:ℝ)*Real.log 4 :=
  Real.log_pow 4 m

/-!
Scope: these are finite analytic count inequalities. Identifying a retained
word family with a particular double-binomial expression is a separate finite
combinatorial theorem. Band sharing, exact integer/polynomial bit costs, and
algorithm-to-cost-ledger reductions are separate obligations; none is asserted
by these estimates. The explicit linear factors in `m` establish the claimed
polynomial-logarithmic losses using `log_dimension`.
-/

#print axioms choose_entropy_upper
#print axioms choose_entropy_lower
#print axioms ordinaryTail_geometric
#print axioms rounded_gridCount
#print axioms rounded_grid_denominator
#print axioms rounded_channelTail
#print axioms rounded_ordinaryTail
#print axioms log_dimension
end
end ThinMatrix.EntropyBounds
