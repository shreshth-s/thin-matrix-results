import EntropyBounds
import CacheCardinality

/-!
Finite entropy bound for the genuine total-capped high-box base family.
The proof uses a fixed Bernoulli probability to bound each admissible pair;
no balanced-binomial maximum or entropy inequality is assumed.
-/
set_option maxRecDepth 10000
set_option maxHeartbeats 1500000
namespace ThinMatrix.HighBoxEntropy
open scoped BigOperators
open ThinMatrix.EntropyBounds
noncomputable section

/-- The genuine finite total-cap count, written over the reals. -/
def highBoxSum (L m t : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (m+1), ∑ k ∈ Finset.range (m+1),
    if j+k ≤ 2*m-t then (L.choose j : ℝ)*(L.choose k : ℝ)*4^(2*L-j-k) else 0

def crossExponent (L j : ℕ) (p : ℝ) : ℝ :=
  -(j:ℝ)*Real.log p + ((L:ℝ)-j)*(Real.log 4-Real.log (1-p))

/-- One weighted binomial coefficient is bounded directly by a term of
its finite binomial sum at any probability in `(0,1)`. -/
theorem ordinaryTerm_cross_upper (L j : ℕ) (hj : j ≤ L) (p : ℝ)
    (hp : 0 < p) (hp1 : p < 1) :
    ordinaryTerm L j ≤ Real.exp (crossExponent L j p) := by
  let w : ℝ := p^j*(1-p)^(L-j)
  have hw : 0 < w := by dsimp [w]; positivity
  have hid : Real.exp (crossExponent L j p)*w = (4:ℝ)^(L-j) := by
    have he : crossExponent L j p + Real.log w = ((L-j:ℕ):ℝ)*Real.log 4 := by
      dsimp [crossExponent, w]
      rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow,
        Nat.cast_sub hj]
      ring
    rw [← Real.exp_log hw, ← Real.exp_add, he, ← Real.log_pow, Real.exp_log (by positivity)]
  have hmass := mass_le_one L j hj hp.le hp1.le
  apply (mul_le_mul_iff_left₀ hw).mp
  calc
    ordinaryTerm L j*w = (4:ℝ)^(L-j)*mass L j p := by
      unfold ordinaryTerm mass w
      ring
    _ ≤ (4:ℝ)^(L-j)*1 := mul_le_mul_of_nonneg_left hmass (by positivity)
    _ = Real.exp (crossExponent L j p)*w := by simpa using hid.symm

/-- The box saving uses the original full-grid geometry exponent. -/
def boxSaving (c theta : ℝ) : ℝ :=
  (c*Real.binEntropy (1/c)-c*Real.binEntropy ((1-theta)/c)-theta*Real.log 4)/Real.log 2

def balancedLog (c theta : ℝ) : ℝ :=
  (c-1+theta)*Real.log 4+c*Real.binEntropy ((1-theta)/c)

def roundingConstant (c theta : ℝ) : ℝ :=
  2*(Real.log 4-Real.log (1-(1-theta)/c))

/-- Actual rounded parameters give the intended balanced entropy
exponent as an upper bound for every retained pair. -/
theorem rounded_pair_exponent (c theta : ℝ) (m j k : ℕ)
    (hc : 5 < c) (ht0 : 0 < theta) (ht1 : theta < 1/2) (hm : 0 < m)
    (hcap : j+k ≤ 2*m-Nat.ceil (2*theta*(m:ℝ))) :
    let L := Nat.ceil (c*(m:ℝ))
    crossExponent L j ((1-theta)/c)+crossExponent L k ((1-theta)/c) ≤
      2*(m:ℝ)*balancedLog c theta+roundingConstant c theta := by
  let p : ℝ := (1-theta)/c
  let A : ℝ := Real.log 4-Real.log (1-p)
  let B : ℝ := Real.log (1-p)-Real.log p-Real.log 4
  let L := Nat.ceil (c*(m:ℝ))
  let t := Nat.ceil (2*theta*(m:ℝ))
  have hm' : (0:ℝ)< m := by exact_mod_cast hm
  have hc0 : 0 < c := by linarith
  have hp : 0 < p := div_pos (by linarith) hc0
  have hp5 : p < 1/5 := by
    apply (div_lt_iff₀ hc0).2
    nlinarith
  have hp1 : p < 1 := by linarith
  have hA : 0 ≤ A := by
    have hl : Real.log (1-p) ≤ 0 := Real.log_nonpos (by linarith) (by linarith)
    dsimp [A]
    linarith [Real.log_pos (by norm_num : (1:ℝ)<4)]
  have hB : 0 ≤ B := by
    have hl := Real.log_le_log (mul_pos (by norm_num : (0:ℝ)<4) hp)
      (show 4*p ≤ 1-p by linarith)
    rw [Real.log_mul (by norm_num) hp.ne'] at hl
    dsimp [B]
    linarith
  have hL : (L:ℝ) ≤ c*(m:ℝ)+1 :=
    (Nat.ceil_lt_add_one (mul_nonneg hc0.le hm'.le)).le
  have ht : t ≤ 2*m := by
    apply Nat.ceil_le.mpr
    push_cast
    nlinarith
  have htcast : ((2*m-t:ℕ):ℝ) = 2*(m:ℝ)-t := by
    rw [Nat.cast_sub ht]
    push_cast
    ring
  have hsum : (j:ℝ)+k ≤ 2*(1-theta)*(m:ℝ) := by
    have hcap' : ((j+k:ℕ):ℝ) ≤ ((2*m-t:ℕ):ℝ) := by exact_mod_cast hcap
    have htceil : 2*theta*(m:ℝ) ≤ (t:ℝ) := Nat.le_ceil _
    rw [htcast] at hcap'
    push_cast at hcap'
    nlinarith
  have hbal : c*A+(1-theta)*B = balancedLog c theta := by
    have hcp : c*p = 1-theta := by dsimp [p]; field_simp
    dsimp [A, B, balancedLog]
    change c*(Real.log 4-Real.log (1-p))+(1-theta)*
      (Real.log (1-p)-Real.log p-Real.log 4) =
      (c-1+theta)*Real.log 4+c*Real.binEntropy p
    rw [binEntropy_eq]
    linear_combination (Real.log p-Real.log (1-p))*hcp
  have hlinear : crossExponent L j p+crossExponent L k p = 2*(L:ℝ)*A+((j:ℝ)+k)*B := by
    dsimp [crossExponent, A, B]
    ring
  change crossExponent L j p+crossExponent L k p ≤ _
  rw [hlinear]
  have hLa := mul_le_mul_of_nonneg_right hL hA
  have hSb := mul_le_mul_of_nonneg_right hsum hB
  change _ ≤ 2*(m:ℝ)*balancedLog c theta+2*A
  rw [← hbal]
  nlinarith


/-- Finite real sum bound at the actual two ceilings. -/
theorem rounded_highBoxSum_exp (c theta : ℝ) (m : ℕ)
    (hc : 5 < c) (ht0 : 0 < theta) (ht1 : theta < 1/2) (hm : 0 < m) :
    let L := Nat.ceil (c*(m:ℝ))
    let t := Nat.ceil (2*theta*(m:ℝ))
    highBoxSum L m t ≤ (m+1:ℝ)^2*Real.exp (roundingConstant c theta)*
      Real.exp (2*(m:ℝ)*balancedLog c theta) := by
  let L := Nat.ceil (c*(m:ℝ))
  let t := Nat.ceil (2*theta*(m:ℝ))
  let p : ℝ := (1-theta)/c
  have hm' : (0:ℝ)< m := by exact_mod_cast hm
  have hc0 : 0 < c := by linarith
  have hp : 0 < p := div_pos (by linarith) hc0
  have hp1 : p < 1 := (div_lt_one hc0).2 (by linarith)
  have hceil : c*(m:ℝ) ≤ (L:ℝ) := Nat.le_ceil _
  have hmL : m ≤ L := by
    have hh : (m:ℝ) ≤ L := by nlinarith
    exact_mod_cast hh
  change highBoxSum L m t ≤ _
  calc
    highBoxSum L m t ≤ ∑ _j ∈ Finset.range (m+1), ∑ _k ∈ Finset.range (m+1),
        Real.exp (2*(m:ℝ)*balancedLog c theta+roundingConstant c theta) := by
      unfold highBoxSum
      apply Finset.sum_le_sum
      intro j hj
      apply Finset.sum_le_sum
      intro k hk
      have hjm : j ≤ m := by have := Finset.mem_range.mp hj; omega
      have hkm : k ≤ m := by have := Finset.mem_range.mp hk; omega
      split_ifs with hcap
      · have hjL := hjm.trans hmL
        have hkL := hkm.trans hmL
        have hpow : 2*L-j-k = (L-j)+(L-k) := by omega
        have hprod : (L.choose j : ℝ)*(L.choose k : ℝ)*4^(2*L-j-k) =
            ordinaryTerm L j*ordinaryTerm L k := by
          unfold ordinaryTerm
          rw [hpow, pow_add]
          ring
        rw [hprod]
        calc
          ordinaryTerm L j*ordinaryTerm L k ≤
              Real.exp (crossExponent L j p)*Real.exp (crossExponent L k p) := by
            apply mul_le_mul (ordinaryTerm_cross_upper L j hjL p hp hp1)
              (ordinaryTerm_cross_upper L k hkL p hp hp1)
            · unfold ordinaryTerm; positivity
            · positivity
          _ = Real.exp (crossExponent L j p+crossExponent L k p) := (Real.exp_add _ _).symm
          _ ≤ Real.exp (2*(m:ℝ)*balancedLog c theta+roundingConstant c theta) := by
            apply Real.exp_le_exp.mpr
            exact rounded_pair_exponent c theta m j k hc ht0 ht1 hm hcap
      · positivity
    _ = (m+1:ℝ)^2*Real.exp (roundingConstant c theta)*
        Real.exp (2*(m:ℝ)*balancedLog c theta) := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one,
        Real.exp_add]
      ring

/-- Algebraic identity between the balanced count exponent and the
canonical saving `G`; no numerical enclosure is involved. -/
theorem balanced_power_identity (c theta : ℝ) (m : ℕ) :
    Real.exp (2*(m:ℝ)*balancedLog c theta) =
      (((4:ℝ)^m)^(tileExponent c))^2 * ((4:ℝ)^m)^(-boxSaving c theta) := by
  rw [← grid_exponential_power c m, Real.rpow_def_of_pos (by positivity), Real.log_pow,
    ← Real.exp_nat_mul, ← Real.exp_add]
  congr 1
  unfold balancedLog boxSaving
  have h4 : Real.log (4:ℝ) = 2*Real.log 2 := by
    convert Real.log_pow (2:ℝ) 2 using 1 <;> norm_num
  have h2 : Real.log (2:ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  rw [h4]
  norm_num
  field_simp
  ring

/-- The high-box base count has the claimed saving relative to the
original full grid, with explicit polynomial-logarithmic factors. -/
theorem rounded_highBoxSum_grid (c theta : ℝ) (m : ℕ)
    (hc : 5 < c) (ht0 : 0 < theta) (ht1 : theta < 1/2) (hm : 0 < m) :
    let L := Nat.ceil (c*(m:ℝ))
    let t := Nat.ceil (2*theta*(m:ℝ))
    highBoxSum L m t ≤ (m+1:ℝ)^2*(L+1:ℝ)^2*Real.exp (roundingConstant c theta)*
      (gridCount L m)^2*((4:ℝ)^m)^(-boxSaving c theta) := by
  let L := Nat.ceil (c*(m:ℝ))
  let t := Nat.ceil (2*theta*(m:ℝ))
  have hhigh := rounded_highBoxSum_exp c theta m hc ht0 ht1 hm
  have hg := (rounded_gridCount c m (by linarith) hm).1
  dsimp only at hg hhigh
  have hden : (0:ℝ)<L+1 := by positivity
  have hgrid : ((4:ℝ)^m)^(tileExponent c) ≤ gridCount L m*(L+1) :=
    (div_le_iff₀ hden).1 hg
  have hgrid0 : 0 ≤ gridCount L m := by unfold gridCount; positivity
  have hsq : (((4:ℝ)^m)^(tileExponent c))^2 ≤ (gridCount L m*(L+1))^2 := by
    gcongr
  rw [balanced_power_identity] at hhigh
  change highBoxSum L m t ≤ _
  calc
    highBoxSum L m t ≤ (m+1:ℝ)^2*Real.exp (roundingConstant c theta)*
        ((((4:ℝ)^m)^(tileExponent c))^2*((4:ℝ)^m)^(-boxSaving c theta)) := hhigh
    _ ≤ (m+1:ℝ)^2*Real.exp (roundingConstant c theta)*
        ((gridCount L m*(L+1))^2*((4:ℝ)^m)^(-boxSaving c theta)) := by
      gcongr
    _ = (m+1:ℝ)^2*(L+1:ℝ)^2*Real.exp (roundingConstant c theta)*
        (gridCount L m)^2*((4:ℝ)^m)^(-boxSaving c theta) := by ring

/-- Exact bridge to the actual finite base-word family, not just a
formal sum used as a proxy for that family. -/
theorem totalCappedLeaves_card_real (L m t : ℕ) :
    (Fintype.card (ThinMatrix.CacheCardinality.TotalCappedLeaves L m (2*m-t)) : ℝ) =
      highBoxSum L m t := by
  rw [ThinMatrix.CacheCardinality.totalCappedLeaves_card]
  simp only [highBoxSum, Nat.cast_sum, Nat.cast_ite, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
    Nat.cast_zero]

/-- The genuine high-box base-family cardinality obeys the entropy
saving with the actual rounded parameters. -/
theorem rounded_totalCappedLeaves_bound (c theta : ℝ) (m : ℕ)
    (hc : 5 < c) (ht0 : 0 < theta) (ht1 : theta < 1/2) (hm : 0 < m) :
    let L := Nat.ceil (c*(m:ℝ))
    let t := Nat.ceil (2*theta*(m:ℝ))
    (Fintype.card (ThinMatrix.CacheCardinality.TotalCappedLeaves L m (2*m-t)) : ℝ) ≤
      (m+1:ℝ)^2*(L+1:ℝ)^2*Real.exp (roundingConstant c theta)*
        (gridCount L m)^2*((4:ℝ)^m)^(-boxSaving c theta) := by
  dsimp only
  rw [totalCappedLeaves_card_real]
  exact rounded_highBoxSum_grid c theta m hc ht0 ht1 hm


/-- A version with a single explicit polynomial in the physical length.
The extra high-box star-cut factor is separate from this base-family bound. -/
theorem rounded_totalCappedLeaves_polynomial (c theta : ℝ) (m : ℕ)
    (hc : 5 < c) (ht0 : 0 < theta) (ht1 : theta < 1/2) (hm : 0 < m) :
    let L := Nat.ceil (c*(m:ℝ))
    let t := Nat.ceil (2*theta*(m:ℝ))
    (Fintype.card (ThinMatrix.CacheCardinality.TotalCappedLeaves L m (2*m-t)) : ℝ) ≤
      (L+1:ℝ)^4*Real.exp (roundingConstant c theta)*
        (gridCount L m)^2*((4:ℝ)^m)^(-boxSaving c theta) := by
  let L := Nat.ceil (c*(m:ℝ))
  let t := Nat.ceil (2*theta*(m:ℝ))
  have hm' : (0:ℝ)< m := by exact_mod_cast hm
  have hceil : c*(m:ℝ) ≤ (L:ℝ) := Nat.le_ceil _
  have hmL : (m:ℝ) ≤ L := by nlinarith
  have hpoly : (m+1:ℝ)^2*(L+1:ℝ)^2 ≤ (L+1:ℝ)^4 := by
    calc
      (m+1:ℝ)^2*(L+1:ℝ)^2 ≤ (L+1:ℝ)^2*(L+1:ℝ)^2 := by gcongr
      _ = (L+1:ℝ)^4 := by ring
  have h := rounded_totalCappedLeaves_bound c theta m hc ht0 ht1 hm
  dsimp only at h ⊢
  exact h.trans (by gcongr)

/-!
This theorem bounds the genuine base-word family. HighBoxDP separately charges
its star/private cut by `2L+1`; coefficient-vector work, band sharing, and the
algorithmic reduction ledger remain separate, explicitly named obligations.
-/

#print axioms ordinaryTerm_cross_upper
#print axioms rounded_pair_exponent
#print axioms balanced_power_identity
#print axioms rounded_highBoxSum_grid
#print axioms totalCappedLeaves_card_real
#print axioms rounded_totalCappedLeaves_bound
#print axioms rounded_totalCappedLeaves_polynomial
end
end ThinMatrix.HighBoxEntropy
