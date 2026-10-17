import Mathlib
import PrimePool
import FoldedCounts
import EntropyBounds
import AsymptoticCosts

/-!
# Rounded prime products and the actual two-phase folded geometry

A call contains its selected prefix and its currently tested candidate. Bounds
are proved for every such list of at most R factors, rather than inferred only
from a completed modulus. The fixed physical factor three is explicit. The
geometric tile exponent remains T throughout.
-/
namespace ThinMatrix.PhaseGeometry

open scoped BigOperators Nat
open Filter
open PrimePool FoldedCounts AsymptoticCosts
noncomputable section

/-- A positive scale loses at most a factor two under upward integer rounding. -/
theorem ceil_bounds {x : ℝ} (hx : 1 ≤ x) :
    x ≤ (Nat.ceil x : ℝ) ∧ (Nat.ceil x : ℝ) ≤ 2*x := by
  refine ⟨Nat.le_ceil x, ?_⟩
  have hc := (Nat.ceil_lt_add_one (show 0 ≤ x by linarith)).le
  linarith

noncomputable def blockSize (n : ℕ) (b : ℝ) : ℕ := Nat.ceil ((n : ℝ)^b)

theorem blockSize_bounds (n : ℕ) (b : ℝ) (hn : 1 ≤ n) (hb : 0 ≤ b) :
    (n : ℝ)^b ≤ (blockSize n b : ℝ) ∧
      (blockSize n b : ℝ) ≤ 2*(n : ℝ)^b := by
  exact ceil_bounds (Real.one_le_rpow (by exact_mod_cast hn) hb)

noncomputable def primeScale (n : ℕ) (eta : ℝ) (k : ℕ) : ℕ :=
  Nat.ceil ((n : ℝ)^eta * (Real.log (n : ℝ))^k)

lemma one_le_log_nat (n : ℕ) (hn : 3 ≤ n) : 1 ≤ Real.log (n : ℝ) := by
  apply (Real.le_log_iff_exp_le (show 0 < (n : ℝ) by exact_mod_cast (by omega : 0<n))).mpr
  exact Real.exp_one_lt_three.le.trans (by exact_mod_cast hn)

theorem primeScale_bounds (n : ℕ) (eta : ℝ) (k : ℕ)
    (hn : 3 ≤ n) (heta : 0 ≤ eta) :
    (n : ℝ)^eta * (Real.log (n : ℝ))^k ≤ (primeScale n eta k : ℝ) ∧
      (primeScale n eta k : ℝ) ≤ 2*((n : ℝ)^eta * (Real.log (n : ℝ))^k) := by
  apply ceil_bounds
  exact one_le_mul_of_one_le_of_one_le
    (Real.one_le_rpow (by exact_mod_cast (show 1≤n by omega)) heta)
    (one_le_pow₀ (one_le_log_nat n hn))

/-- Any chosen integer in [P,8P] has the desired unrounded scale bounds. -/
theorem prime_factor_bounds (n : ℕ) (eta : ℝ) (k p : ℕ)
    (hn : 3 ≤ n) (heta : 0 ≤ eta)
    (hp : primeScale n eta k ≤ p ∧ p ≤ 8*primeScale n eta k) :
    (n : ℝ)^eta ≤ (p : ℝ) ∧
      (p : ℝ) ≤ 16*((n : ℝ)^eta * (Real.log (n : ℝ))^k) := by
  have hs := primeScale_bounds n eta k hn heta
  have hn0 : 0 ≤ (n : ℝ)^eta := Real.rpow_nonneg (Nat.cast_nonneg n) eta
  have hl : 1 ≤ (Real.log (n : ℝ))^k := one_le_pow₀ (one_le_log_nat n hn)
  have hP : (primeScale n eta k : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.1
  have hp8 : (p : ℝ) ≤ 8*(primeScale n eta k : ℝ) := by exact_mod_cast hp.2
  constructor
  · exact (show (n : ℝ)^eta ≤ (n : ℝ)^eta * (Real.log (n : ℝ))^k by
      simpa using mul_le_mul_of_nonneg_left hl hn0).trans (hs.1.trans hP)
  · calc
      (p : ℝ) ≤ 8*(primeScale n eta k : ℝ) := hp8
      _ ≤ 8*(2*((n : ℝ)^eta * (Real.log (n : ℝ))^k)) :=
        mul_le_mul_of_nonneg_left hs.2 (by norm_num)
      _ = _ := by ring

/-- Real scale bounds from the integer product interval supplied by prime selection. -/
theorem primeProductScale_bounds (n : ℕ) (eta : ℝ) (k j d : ℕ)
    (hn : 3 ≤ n) (heta : 0 ≤ eta)
    (hd : (primeScale n eta k : ℝ)^j ≤ (d : ℝ) ∧
      (d : ℝ) ≤ (8*(primeScale n eta k : ℝ))^j) :
    (n : ℝ)^((j : ℝ)*eta) ≤ (d : ℝ) ∧
      (d : ℝ) ≤ (16 : ℝ)^j * (Real.log (n : ℝ))^(k*j) *
        (n : ℝ)^((j : ℝ)*eta) := by
  have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hP : primeScale n eta k ≤ primeScale n eta k ∧
      primeScale n eta k ≤ 8*primeScale n eta k := ⟨le_rfl, by omega⟩
  have hs := prime_factor_bounds n eta k (primeScale n eta k) hn heta hP
  have hlo : ((n : ℝ)^eta)^j ≤ (primeScale n eta k : ℝ)^j := by
    gcongr
    exact hs.1
  have h8 : 8*(primeScale n eta k : ℝ) ≤
      16*((n : ℝ)^eta * (Real.log (n : ℝ))^k) := by
    have hceil := (primeScale_bounds n eta k hn heta).2
    linarith
  have hhi : (8*(primeScale n eta k : ℝ))^j ≤
      (16*((n : ℝ)^eta * (Real.log (n : ℝ))^k))^j := by gcongr
  have he : (n : ℝ)^((j : ℝ)*eta) = ((n : ℝ)^eta)^j := by
    rw [mul_comm, Real.rpow_mul_natCast hn0 eta j]
  constructor
  · rw [he]
    exact hlo.trans hd.1
  · calc
      (d : ℝ) ≤ (8*(primeScale n eta k : ℝ))^j := hd.2
      _ ≤ (16*((n : ℝ)^eta * (Real.log (n : ℝ))^k))^j := hhi
      _ = _ := by
        rw [he, mul_pow, mul_pow, pow_mul]
        ring

/-- Finite products of the chosen factors retain the exact j*eta exponent.
The constant and logarithmic power may be bounded uniformly for j ≤ R. -/
theorem primeProduct_bounds (n : ℕ) (eta : ℝ) (k j R : ℕ)
    (p : Fin j → ℕ) (hn : 3 ≤ n) (heta : 0 ≤ eta) (hj : j ≤ R)
    (hp : ∀ i, primeScale n eta k ≤ p i ∧ p i ≤ 8*primeScale n eta k) :
    (n : ℝ)^((j : ℝ)*eta) ≤ (∏ i, (p i : ℝ)) ∧
      (∏ i, (p i : ℝ)) ≤
        (16 : ℝ)^R * (Real.log (n : ℝ))^(k*R) * (n : ℝ)^((j : ℝ)*eta) := by
  have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have ha0 : 0 ≤ (n : ℝ)^eta := Real.rpow_nonneg hn0 eta
  have hl1 : 1 ≤ Real.log (n : ℝ) := one_le_log_nat n hn
  have hl0 : 0 ≤ Real.log (n : ℝ) := by linarith
  have hf := fun i => prime_factor_bounds n eta k (p i) hn heta (hp i)
  have hlo : ((n : ℝ)^eta)^j ≤ ∏ i, (p i : ℝ) := by
    calc
      _ = ∏ _i : Fin j, (n : ℝ)^eta := by simp
      _ ≤ _ := Finset.prod_le_prod (fun _ _ => ha0) (fun i _ => (hf i).1)
  have hhi : (∏ i, (p i : ℝ)) ≤
      (16*((n : ℝ)^eta * (Real.log (n : ℝ))^k))^j := by
    calc
      _ ≤ ∏ _i : Fin j, (16*((n : ℝ)^eta * (Real.log (n : ℝ))^k)) :=
        Finset.prod_le_prod (fun i _ => Nat.cast_nonneg (p i)) (fun i _ => (hf i).2)
      _ = _ := by simp
  have he : (n : ℝ)^((j : ℝ)*eta) = ((n : ℝ)^eta)^j := by
    rw [mul_comm, Real.rpow_mul_natCast hn0 eta j]
  refine ⟨by simpa only [he] using hlo, ?_⟩
  have h16 : (16 : ℝ)^j ≤ (16 : ℝ)^R := pow_le_pow_right₀ (by norm_num) hj
  have hlog : (Real.log (n : ℝ))^(k*j) ≤ (Real.log (n : ℝ))^(k*R) :=
    pow_le_pow_right₀ hl1 (Nat.mul_le_mul_left k hj)
  calc
    (∏ i, (p i : ℝ)) ≤ (16*((n : ℝ)^eta * (Real.log (n : ℝ))^k))^j := hhi
    _ = (16 : ℝ)^j * (Real.log (n : ℝ))^(k*j) * (n : ℝ)^((j : ℝ)*eta) := by
      rw [he, mul_pow, mul_pow, pow_mul]
      ring
    _ ≤ _ := by gcongr

/-- Canonical next-power-of-four padding. -/
def pad4 (M : ℕ) : ℕ := 4^(Nat.clog 4 M)

theorem pad4_lower (M : ℕ) : M ≤ pad4 M := Nat.le_pow_clog (by norm_num) M

theorem pad4_upper (M : ℕ) (hM : 0 < M) : pad4 M ≤ 4*M := by
  by_cases h1 : M = 1
  · subst M
    norm_num [pad4]
  have hM' : 1 < M := by omega
  have hc : 0 < Nat.clog 4 M := Nat.clog_pos (by norm_num) hM'
  have he : Nat.clog 4 M = (Nat.clog 4 M).pred+1 := by
    simpa only [Nat.succ_eq_add_one] using (Nat.succ_pred_eq_of_pos hc).symm
  calc
    pad4 M = 4^((Nat.clog 4 M).pred+1) := congrArg (fun a => 4^a) he
    _ = 4^(Nat.clog 4 M).pred * 4 := by rw [pow_succ]
    _ ≤ M*4 := Nat.mul_le_mul_right 4
      (Nat.le_of_lt (Nat.pow_pred_clog_lt_self (by norm_num) hM'))
    _ = 4*M := Nat.mul_comm _ _

theorem pad4_bounds (M : ℕ) (hM : 0 < M) : M ≤ pad4 M ∧ pad4 M ≤ 4*M :=
  ⟨pad4_lower M, pad4_upper M hM⟩

/-- Integer folded width is within one of the real square root. -/
theorem foldWidth_bounds (d : ℕ) (hd : 0 < d) :
    Real.sqrt (d : ℝ) ≤ (FoldedCounts.foldWidth d : ℝ) ∧
      (FoldedCounts.foldWidth d : ℝ) ≤ Real.sqrt (d : ℝ)+1 := by
  letI : NeZero d := ⟨by omega⟩
  constructor
  · apply Real.sqrt_le_iff.mpr
    refine ⟨Nat.cast_nonneg _, ?_⟩
    have hf : d ≤ FoldedCounts.foldWidth d * FoldedCounts.foldWidth d :=
      FoldedCounts.modulus_fits
    exact_mod_cast (show d ≤ FoldedCounts.foldWidth d ^ 2 by simpa only [pow_two] using hf)
  · have hs : Nat.sqrt (d-1) * Nat.sqrt (d-1) ≤ d :=
      (Nat.sqrt_le (d-1)).trans (Nat.sub_le d 1)
    have hsR : (Nat.sqrt (d-1) : ℝ)^2 ≤ (d : ℝ) := by
      exact_mod_cast (show Nat.sqrt (d-1)^2 ≤ d by simpa only [pow_two] using hs)
    have hle := Real.le_sqrt_of_sq_le hsR
    simpa only [FoldedCounts.foldWidth, Nat.cast_add, Nat.cast_one, add_comm] using
      add_le_add_right hle 1




/-- Every actual factor, including a temporarily tested candidate, lies in the
same finite interval. Primality and distinctness are unnecessary for these
size bounds and remain separate hypotheses in the reduction. -/
def FactorBounds (P : ℕ) (factors : List ℕ) : Prop :=
  ∀ p ∈ factors, P ≤ p ∧ p ≤ 8*P

theorem list_product_bounds {P : ℕ} {factors : List ℕ}
    (h : FactorBounds P factors) :
    P^factors.length ≤ factors.prod ∧ factors.prod ≤ (8*P)^factors.length := by
  exact ⟨List.pow_card_le_prod factors P (fun p hp => (h p hp).1),
    List.prod_le_pow_card factors (8*P) (fun p hp => (h p hp).2)⟩

theorem factorBounds_take {P S : ℕ} {factors : List ℕ}
    (h : FactorBounds P factors) : FactorBounds P (factors.take S) := by
  intro p hp
  exact h p (List.mem_of_mem_take hp)

theorem factorBounds_drop {P S : ℕ} {factors : List ℕ}
    (h : FactorBounds P factors) : FactorBounds P (factors.drop S) := by
  intro p hp
  exact h p (List.mem_of_mem_drop hp)

theorem factorBounds_append_candidate {P candidate : ℕ} {factors : List ℕ}
    (h : FactorBounds P factors) (hc : P ≤ candidate ∧ candidate ≤ 8*P) :
    FactorBounds P (factors ++ [candidate]) := by
  intro p hp
  rcases List.mem_append.mp hp with hp | hp
  · exact h p hp
  · have hp' : p = candidate := List.mem_singleton.mp hp
    simpa [hp'] using hc

/-- A temporarily tested candidate increases the charged prefix length by one.
It need not be the candidate ultimately selected for the next stage. -/
theorem candidate_product_bounds {P candidate : ℕ} {factors : List ℕ}
    (h : FactorBounds P factors) (hc : P ≤ candidate ∧ candidate ≤ 8*P) :
    P^(factors.length+1) ≤ (factors ++ [candidate]).prod ∧
      (factors ++ [candidate]).prod ≤ (8*P)^(factors.length+1) := by
  simpa only [List.length_append, List.length_singleton] using
    list_product_bounds (factorBounds_append_candidate h hc)

theorem candidate_length_le {R candidate : ℕ} {factors : List ℕ}
    (h : factors.length < R) : (factors ++ [candidate]).length ≤ R := by
  simp only [List.length_append, List.length_singleton]
  omega

theorem list_product_upper_of_length_le {P R : ℕ} {factors : List ℕ}
    (h : FactorBounds P factors) (hP : 1 ≤ P) (hR : factors.length ≤ R) :
    factors.prod ≤ (8*P)^R := by
  exact (list_product_bounds h).2.trans
    (Nat.pow_le_pow_right (by omega) hR)

theorem candidate_product_upper_of_length_lt {P R candidate : ℕ} {factors : List ℕ}
    (h : FactorBounds P factors) (hc : P ≤ candidate ∧ candidate ≤ 8*P)
    (hP : 1 ≤ P) (hR : factors.length < R) :
    (factors ++ [candidate]).prod ≤ (8*P)^R := by
  exact list_product_upper_of_length_le (factorBounds_append_candidate h hc)
    hP (candidate_length_le hR)



/-- The factors allocated to the frozen phase. -/
def frozenProduct (factors : List ℕ) (S : ℕ) : ℕ :=
  (factors.take S).prod

/-- The factors allocated to the cyclic phase. -/
def cyclicProduct (factors : List ℕ) (S : ℕ) : ℕ :=
  (factors.drop S).prod

theorem frozenProduct_mul_cyclicProduct (factors : List ℕ) (S : ℕ) :
    frozenProduct factors S * cyclicProduct factors S = factors.prod := by
  exact List.prod_take_mul_prod_drop factors S

theorem frozen_length (factors : List ℕ) (S : ℕ) :
    (factors.take S).length = min S factors.length := by
  exact List.length_take

theorem cyclic_length (factors : List ℕ) (S : ℕ) :
    (factors.drop S).length = factors.length - S := by
  exact List.length_drop

theorem phase_lengths (factors : List ℕ) (S : ℕ) :
    (factors.take S).length + (factors.drop S).length = factors.length := by
  rw [frozen_length, cyclic_length]
  omega

theorem frozenProduct_eq_prod_of_length_le {factors : List ℕ} {S : ℕ}
    (h : factors.length ≤ S) : frozenProduct factors S = factors.prod := by
  simp [frozenProduct, List.take_of_length_le h]

theorem cyclicProduct_eq_one_of_length_le {factors : List ℕ} {S : ℕ}
    (h : factors.length ≤ S) : cyclicProduct factors S = 1 := by
  simp [cyclicProduct, List.drop_eq_nil_of_le h]

theorem prod_append_candidate (factors : List ℕ) (candidate : ℕ) :
    (factors ++ [candidate]).prod = factors.prod * candidate := by
  simp

theorem mem_append_candidate {factors : List ℕ} {candidate a : ℕ} :
    a ∈ factors ++ [candidate] ↔ a ∈ factors ∨ a = candidate := by
  simp

theorem frozenProduct_append_of_le_length (factors : List ℕ) (candidate : ℕ)
    {S : ℕ} (h : S ≤ factors.length) :
    frozenProduct (factors ++ [candidate]) S = frozenProduct factors S := by
  simp [frozenProduct, List.take_append, Nat.sub_eq_zero_of_le h]

theorem cyclicProduct_append_of_le_length (factors : List ℕ) (candidate : ℕ)
    {S : ℕ} (h : S ≤ factors.length) :
    cyclicProduct (factors ++ [candidate]) S = cyclicProduct factors S * candidate := by
  simp [cyclicProduct, List.drop_append, Nat.sub_eq_zero_of_le h]

theorem frozenProduct_append_of_length_lt (factors : List ℕ) (candidate : ℕ)
    {S : ℕ} (h : factors.length < S) :
    frozenProduct (factors ++ [candidate]) S = frozenProduct factors S * candidate := by
  have hnew : (factors ++ [candidate]).length ≤ S := by simp; omega
  rw [frozenProduct_eq_prod_of_length_le hnew, frozenProduct_eq_prod_of_length_le h.le]
  exact prod_append_candidate factors candidate

theorem cyclicProduct_append_of_length_lt (factors : List ℕ) (candidate : ℕ)
    {S : ℕ} (h : factors.length < S) :
    cyclicProduct (factors ++ [candidate]) S = 1 := by
  apply cyclicProduct_eq_one_of_length_le
  simp
  omega



theorem frozenProduct_bounds {P S : ℕ} {factors : List ℕ}
    (h : FactorBounds P factors) :
    P^(min S factors.length) ≤ frozenProduct factors S ∧
      frozenProduct factors S ≤ (8*P)^(min S factors.length) := by
  simpa only [frozenProduct, List.length_take] using
    list_product_bounds (factorBounds_take (S := S) h)

/-- This bound also includes the first phase, when the exponent is zero. -/
theorem cyclicProduct_bounds {P S : ℕ} {factors : List ℕ}
    (h : FactorBounds P factors) :
    P^(factors.length-S) ≤ cyclicProduct factors S ∧
      cyclicProduct factors S ≤ (8*P)^(factors.length-S) := by
  simpa only [cyclicProduct, List.length_drop] using
    list_product_bounds (factorBounds_drop (S := S) h)

/-- The largest charged cyclic exponent comes from at most R factors. -/
theorem cyclicProduct_upper_of_length_le {P R S : ℕ} {factors : List ℕ}
    (h : FactorBounds P factors) (hP : 1 ≤ P) (hR : factors.length ≤ R) :
    cyclicProduct factors S ≤ (8*P)^(R-S) := by
  exact (cyclicProduct_bounds h).2.trans
    (Nat.pow_le_pow_right (by omega) (Nat.sub_le_sub_right hR S))

theorem candidate_frozenProduct_bounds {P S candidate : ℕ} {factors : List ℕ}
    (h : FactorBounds P factors) (hc : P ≤ candidate ∧ candidate ≤ 8*P) :
    P^(min S (factors.length+1)) ≤ frozenProduct (factors ++ [candidate]) S ∧
      frozenProduct (factors ++ [candidate]) S ≤ (8*P)^(min S (factors.length+1)) := by
  simpa only [List.length_append, List.length_singleton] using
    frozenProduct_bounds (S := S) (factorBounds_append_candidate h hc)

theorem candidate_cyclicProduct_bounds {P S candidate : ℕ} {factors : List ℕ}
    (h : FactorBounds P factors) (hc : P ≤ candidate ∧ candidate ≤ 8*P) :
    P^((factors.length+1)-S) ≤ cyclicProduct (factors ++ [candidate]) S ∧
      cyclicProduct (factors ++ [candidate]) S ≤ (8*P)^((factors.length+1)-S) := by
  simpa only [List.length_append, List.length_singleton] using
    cyclicProduct_bounds (S := S) (factorBounds_append_candidate h hc)

/-- Every intermediate candidate call obeys the same terminal cyclic bound,
including candidates that are discarded by the selection rule. -/
theorem candidate_cyclicProduct_upper_of_length_lt {P R S candidate : ℕ}
    {factors : List ℕ} (h : FactorBounds P factors)
    (hc : P ≤ candidate ∧ candidate ≤ 8*P) (hP : 1 ≤ P)
    (hR : factors.length < R) :
    cyclicProduct (factors ++ [candidate]) S ≤ (8*P)^(R-S) := by
  exact cyclicProduct_upper_of_length_le (factorBounds_append_candidate h hc)
    hP (candidate_length_le hR)

/-- A conventional j-prefix is one instance of the arbitrary actual-factor
interface. The list bound never assumes that a trial candidate will be kept. -/
theorem prefix_product_bounds {P j : ℕ} {factors : List ℕ}
    (h : FactorBounds P factors) (hj : j ≤ factors.length) :
    P^j ≤ (factors.take j).prod ∧ (factors.take j).prod ≤ (8*P)^j := by
  simpa only [List.length_take, Nat.min_eq_left hj] using
    list_product_bounds (factorBounds_take (S := j) h)


theorem foldedOuter_upper (n d : ℕ) (H s : ℝ) (hn : 3 ≤ n)
    (hd : 0 < d) (hH : 1 ≤ H) (hs : 0 ≤ s)
    (hdscale : (d : ℝ) ≤ H*(n : ℝ)^s) :
    (n : ℝ) * (FoldedCounts.foldWidth (3*d) : ℝ) ≤
      4*H*(n : ℝ)^(1+s/2) := by
  have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (show 0<n by omega)
  have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast (show 1≤n by omega)
  have hH0 : 0 ≤ H := by linarith
  have hhalf : 0 ≤ s/2 := by linarith
  have hx1 : 1 ≤ (n : ℝ)^(s/2) := Real.one_le_rpow hn1 hhalf
  have hx0 : 0 ≤ (n : ℝ)^(s/2) := by linarith
  have hs0 : 0 ≤ (n : ℝ)^s := Real.rpow_nonneg hn0 s
  have hsq : ((n : ℝ)^(s/2))^2 = (n : ℝ)^s := by
    have he := Real.rpow_mul_natCast hn0 (s/2) 2
    norm_num only [Nat.cast_ofNat] at he
    rw [show s/2*(2:ℝ)=s by ring] at he
    exact he.symm
  have hh : 3*H ≤ 4*H^2 := by nlinarith
  have hroot : Real.sqrt ((3*d : ℕ) : ℝ) ≤ 2*H*(n : ℝ)^(s/2) := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    have hthree : 3*(d : ℝ) ≤ 3*(H*(n : ℝ)^s) :=
      mul_le_mul_of_nonneg_left hdscale (by norm_num)
    have hscaled := mul_le_mul_of_nonneg_right hh hs0
    push_cast
    nlinarith [hthree, hscaled, hsq]
  have hfold := (foldWidth_bounds (3*d) (by omega)).2
  have hHx : 1 ≤ H*(n : ℝ)^(s/2) := one_le_mul_of_one_le_of_one_le hH hx1
  have hwidth : (FoldedCounts.foldWidth (3*d) : ℝ) ≤ 4*H*(n : ℝ)^(s/2) := by
    linarith
  calc
    (n : ℝ) * (FoldedCounts.foldWidth (3*d) : ℝ) ≤
        (n : ℝ) * (4*H*(n : ℝ)^(s/2)) := mul_le_mul_of_nonneg_left hwidth hn0
    _ = 4*H*(n : ℝ)^(1+s/2) := by
      rw [Real.rpow_add hnpos, Real.rpow_one]
      ring


/-- The entropy exponent of the full original grid equals the certified `T`.
No encoder exponent is used in geometry. -/
theorem tileExponent_eq_T :
    EntropyBounds.tileExponent RealCertificate.c = RealCertificate.T := by
  unfold EntropyBounds.tileExponent RealCertificate.T RealCertificate.entropy Real.binEntropy
  simp only [Real.log_inv]
  ring

/-- Raising a dimension bound to a nonnegative tile exponent retains only a
fixed logarithmic power; its integer ceiling is an explicit upper bound. -/
theorem poweredLogBound {D C x a T : ℝ} (k : ℕ)
    (hD0 : 0 ≤ D) (hC : 0 ≤ C) (hx : 0 ≤ x)
    (hlog : 1 ≤ Real.log x) (hT : 0 ≤ T)
    (hD : D ≤ C * (Real.log x)^k * x^a) :
    D^T ≤ C^T * (Real.log x)^(Nat.ceil ((k:ℝ)*T)) * x^(a*T) := by
  have hlog0 : 0 ≤ Real.log x := le_trans (by norm_num) hlog
  calc
    D^T ≤ (C * (Real.log x)^k * x^a)^T := Real.rpow_le_rpow hD0 hD hT
    _ = C^T * (Real.log x)^((k:ℝ)*T) * x^(a*T) := by
      rw [Real.mul_rpow (mul_nonneg hC (pow_nonneg hlog0 _)) (Real.rpow_nonneg hx _),
        Real.mul_rpow hC (pow_nonneg hlog0 _), ← Real.rpow_mul hx,
        ← Real.rpow_natCast, ← Real.rpow_mul hlog0]
    _ ≤ C^T * (Real.log x)^(Nat.ceil ((k:ℝ)*T)) * x^(a*T) := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hx _)
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hC _)
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le hlog (Nat.le_ceil _)

/-- The constant upper bound for the original ceiling-rounded grid also
includes the empty tensor power. -/
theorem gridCeilUpper (c : ℝ) (m : ℕ) (hc : 1 < c) :
    EntropyBounds.gridCount (Nat.ceil (c*(m:ℝ))) m ≤
      Real.exp (Real.log 4 + Real.log (c/(c-1))) *
        ((4:ℝ)^m)^(EntropyBounds.tileExponent c) := by
  by_cases hm : 0 < m
  · exact (EntropyBounds.rounded_gridCount c m hc hm).2
  · have hm0 : m = 0 := by omega
    subst m
    have hdiv : 1 ≤ c/(c-1) := by
      apply (le_div_iff₀ (by linarith : 0 < c-1)).2
      linarith
    have hlog : 0 ≤ Real.log 4 + Real.log (c/(c-1)) :=
      add_nonneg (Real.log_nonneg (by norm_num)) (Real.log_nonneg hdiv)
    simpa [EntropyBounds.gridCount] using Real.one_le_exp_iff.mpr hlog

/-- Eventual fit of the actual ceiling-rounded full grid, conditional only on
an actual padded-dimension bound, a lower bound on the available outer size,
and a strict geometry gap. -/
theorem actualGridFitsEventually
    (c a d C : ℝ) (k : ℕ) (m N : ℕ → ℕ)
    (hc : 1 < c) (hT : 0 ≤ EntropyBounds.tileExponent c) (hC : 0 ≤ C)
    (hgap : a * EntropyBounds.tileExponent c < d)
    (hD : ∀ᶠ n : ℕ in atTop,
      (4:ℝ)^(m n) ≤ C * (Real.log (n:ℝ))^k * (n:ℝ)^a)
    (hN : ∀ᶠ n : ℕ in atTop, (n:ℝ)^d ≤ (N n:ℝ)) :
    ∀ᶠ n : ℕ in atTop,
      EntropyBounds.gridCount (Nat.ceil (c*(m n:ℝ))) (m n) ≤ (N n:ℝ) := by
  let C₀ := Real.exp (Real.log 4 + Real.log (c/(c-1)))
  have hlog : ∀ᶠ n : ℕ in atTop, 1 ≤ Real.log (n:ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop 1)
  have hfit := AsymptoticCosts.eventualPowerFit hgap
    (Nat.ceil ((k:ℝ)*EntropyBounds.tileExponent c))
    (C₀*C^(EntropyBounds.tileExponent c))
  filter_upwards [hD, hN, hlog, hfit] with n hDn hNn hlogn hfitn
  have hgrid := gridCeilUpper c (m n) hc
  have hp := poweredLogBound k (by positivity) hC (Nat.cast_nonneg n) hlogn hT hDn
  calc
    EntropyBounds.gridCount (Nat.ceil (c*(m n:ℝ))) (m n)
        ≤ C₀ * ((4:ℝ)^(m n))^(EntropyBounds.tileExponent c) := hgrid
    _ ≤ C₀ * (C^(EntropyBounds.tileExponent c) *
        (Real.log (n:ℝ))^(Nat.ceil ((k:ℝ)*EntropyBounds.tileExponent c)) *
        (n:ℝ)^(a*EntropyBounds.tileExponent c)) :=
      mul_le_mul_of_nonneg_left hp (Real.exp_nonneg _)
    _ = (C₀*C^(EntropyBounds.tileExponent c)) *
        (Real.log (n:ℝ))^(Nat.ceil ((k:ℝ)*EntropyBounds.tileExponent c)) *
        (n:ℝ)^(a*EntropyBounds.tileExponent c) := by ring
    _ ≤ (n:ℝ)^d := hfitn
    _ ≤ (N n:ℝ) := hNn

/-- A real power lower bound for the modulus forces the corresponding
square-root lower bound for its folded outer width. -/
theorem foldedOuterLower (n d : ℕ) (s : ℝ) (hn : 1 ≤ n)
    (hlower : (n : ℝ) ^ s ≤ (d : ℝ)) :
    (n : ℝ) ^ (1 + s / 2) ≤ ((n * FoldedCounts.foldWidth d : ℕ) : ℝ) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hdpos : (0 : ℝ) < d := (Real.rpow_pos_of_pos hnpos s).trans_le hlower
  have hd : d ≠ 0 := by exact_mod_cast (ne_of_gt hdpos)
  letI : NeZero d := ⟨hd⟩
  have hfit : (d : ℝ) ≤ (FoldedCounts.foldWidth d : ℝ) * (FoldedCounts.foldWidth d : ℝ) := by
    exact_mod_cast (FoldedCounts.modulus_fits (d := d))
  have hsq : ((n : ℝ) ^ (s / 2)) ^ (2 : ℕ) = (n : ℝ) ^ s := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hnpos.le]
    congr 1
    norm_num
  have hroot : (n : ℝ) ^ (s / 2) ≤ (FoldedCounts.foldWidth d : ℝ) := by
    have hnonneg : 0 ≤ (n : ℝ) ^ (s / 2) := Real.rpow_nonneg hnpos.le _
    have hwnonneg : (0 : ℝ) ≤ FoldedCounts.foldWidth d := Nat.cast_nonneg _
    nlinarith
  rw [Real.rpow_add hnpos, Real.rpow_one, Nat.cast_mul]
  exact mul_le_mul_of_nonneg_left hroot hnpos.le


/-- The literal natural-number grid `K*N₀` fits the folded outer dimension.
The hypotheses concern the actual padded dimension and actual modulus. -/
theorem actualFoldedGridFitsEventually
    (c a s C : ℝ) (k : ℕ) (m d : ℕ → ℕ)
    (hc : 1 < c) (hT : 0 ≤ EntropyBounds.tileExponent c) (hC : 0 ≤ C)
    (hgap : a * EntropyBounds.tileExponent c < 1+s/2)
    (hD : ∀ᶠ n : ℕ in atTop,
      (4:ℝ)^(m n) ≤ C * (Real.log (n:ℝ))^k * (n:ℝ)^a)
    (hd : ∀ᶠ n : ℕ in atTop, (n:ℝ)^s ≤ (d n:ℝ)) :
    ∀ᶠ n : ℕ in atTop,
      (Nat.ceil (c*(m n:ℝ))).choose (m n) *
        4^(Nat.ceil (c*(m n:ℝ)) - m n) ≤ n * FoldedCounts.foldWidth (d n) := by
  have hN : ∀ᶠ n : ℕ in atTop,
      (n:ℝ)^(1+s/2) ≤ (n * FoldedCounts.foldWidth (d n):ℕ) := by
    filter_upwards [hd, eventually_ge_atTop (1:ℕ)] with n hdn hn
    exact foldedOuterLower n (d n) s hn hdn
  have hf := actualGridFitsEventually c a (1+s/2) C k m
    (fun n => n * FoldedCounts.foldWidth (d n)) hc hT hC hgap hD hN
  filter_upwards [hf] with n hn
  have hcast :
      (((Nat.ceil (c*(m n:ℝ))).choose (m n) *
        4^(Nat.ceil (c*(m n:ℝ)) - m n):ℕ):ℝ) ≤
      ((n * FoldedCounts.foldWidth (d n):ℕ):ℝ) := by
    simpa [EntropyBounds.gridCount] using hn
  exact_mod_cast hcast

/-- Full-grid scalar phase geometry from actual input bounds, uniformly at
any fixed phase exponent `s ∈ [0,u]`. -/
theorem alignedScalarGridFitsEventually
    (s C : ℝ) (k : ℕ) (m d : ℕ → ℕ)
    (hs0 : 0 ≤ s) (hsu : s ≤ AsymptoticCosts.u) (hC : 0 ≤ C)
    (hD : ∀ᶠ n : ℕ in atTop,
      (4:ℝ)^(m n) ≤ C * (Real.log (n:ℝ))^k *
        (n:ℝ)^(AsymptoticCosts.b+s))
    (hd : ∀ᶠ n : ℕ in atTop, (n:ℝ)^s ≤ (d n:ℝ)) :
    ∀ᶠ n : ℕ in atTop,
      (Nat.ceil (RealCertificate.c*(m n:ℝ))).choose (m n) *
        4^(Nat.ceil (RealCertificate.c*(m n:ℝ)) - m n) ≤
      n * FoldedCounts.foldWidth (d n) := by
  apply actualFoldedGridFitsEventually RealCertificate.c
    (AsymptoticCosts.b+s) s C k m d
    (by norm_num [RealCertificate.c]) _ hC _ hD hd
  · rw [tileExponent_eq_T]
    exact le_of_lt (lt_trans (by norm_num) RealCertificate.TEnclosure.1)
  · rw [tileExponent_eq_T]
    have h := AsymptoticCosts.scalarGeometryAllStages s hs0 hsu
    unfold AsymptoticCosts.scalarGeometry at h
    linarith [AsymptoticCosts.slackPositive]

/-- Full-grid cyclic phase geometry uses the frozen folding exponent `u`
and total padded-dimension exponent `e`, still with original `T`. -/
theorem alignedCyclicGridFitsEventually
    (C : ℝ) (k : ℕ) (m d : ℕ → ℕ) (hC : 0 ≤ C)
    (hD : ∀ᶠ n : ℕ in atTop,
      (4:ℝ)^(m n) ≤ C * (Real.log (n:ℝ))^k * (n:ℝ)^AsymptoticCosts.e)
    (hd : ∀ᶠ n : ℕ in atTop, (n:ℝ)^AsymptoticCosts.u ≤ (d n:ℝ)) :
    ∀ᶠ n : ℕ in atTop,
      (Nat.ceil (RealCertificate.c*(m n:ℝ))).choose (m n) *
        4^(Nat.ceil (RealCertificate.c*(m n:ℝ)) - m n) ≤
      n * FoldedCounts.foldWidth (d n) := by
  apply actualFoldedGridFitsEventually RealCertificate.c
    AsymptoticCosts.e AsymptoticCosts.u C k m d
    (by norm_num [RealCertificate.c]) _ hC _ hD hd
  · rw [tileExponent_eq_T]
    exact le_of_lt (lt_trans (by norm_num) RealCertificate.TEnclosure.1)
  · rw [tileExponent_eq_T]
    have h := AsymptoticCosts.cyclicGeometrySlack
    unfold AsymptoticCosts.cyclicGeometry at h
    linarith [AsymptoticCosts.slackPositive]

/-- The common eventual threshold is independent of the candidate grid
parameter and outer dimension: only their pointwise bounds are needed. -/
theorem actualGridFitsUniformlyEventually
    (c a d C : ℝ) (k : ℕ)
    (hc : 1 < c) (hT : 0 ≤ EntropyBounds.tileExponent c) (hC : 0 ≤ C)
    (hgap : a * EntropyBounds.tileExponent c < d) :
    ∀ᶠ n : ℕ in atTop, ∀ m N : ℕ,
      (4:ℝ)^m ≤ C * (Real.log (n:ℝ))^k * (n:ℝ)^a →
      (n:ℝ)^d ≤ (N:ℝ) →
      EntropyBounds.gridCount (Nat.ceil (c*(m:ℝ))) m ≤ (N:ℝ) := by
  let C₀ := Real.exp (Real.log 4 + Real.log (c/(c-1)))
  have hlog : ∀ᶠ n : ℕ in atTop, 1 ≤ Real.log (n:ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop 1)
  have hfit := AsymptoticCosts.eventualPowerFit hgap
    (Nat.ceil ((k:ℝ)*EntropyBounds.tileExponent c))
    (C₀*C^(EntropyBounds.tileExponent c))
  filter_upwards [hlog, hfit] with n hlogn hfitn
  intro m N hDn hNn
  have hgrid := gridCeilUpper c m hc
  have hp := poweredLogBound k (by positivity) hC (Nat.cast_nonneg n) hlogn hT hDn
  calc
    EntropyBounds.gridCount (Nat.ceil (c*(m:ℝ))) m
        ≤ C₀ * ((4:ℝ)^m)^(EntropyBounds.tileExponent c) := hgrid
    _ ≤ C₀ * (C^(EntropyBounds.tileExponent c) *
        (Real.log (n:ℝ))^(Nat.ceil ((k:ℝ)*EntropyBounds.tileExponent c)) *
        (n:ℝ)^(a*EntropyBounds.tileExponent c)) :=
      mul_le_mul_of_nonneg_left hp (Real.exp_nonneg _)
    _ = (C₀*C^(EntropyBounds.tileExponent c)) *
        (Real.log (n:ℝ))^(Nat.ceil ((k:ℝ)*EntropyBounds.tileExponent c)) *
        (n:ℝ)^(a*EntropyBounds.tileExponent c) := by ring
    _ ≤ (n:ℝ)^d := hfitn
    _ ≤ (N:ℝ) := hNn

/-- One eventual threshold fits all candidate choices of `m` and `d` whose
actual pointwise bounds have the same constants and exponents. -/
theorem actualFoldedGridFitsUniformlyEventually
    (c a s C : ℝ) (k : ℕ)
    (hc : 1 < c) (hT : 0 ≤ EntropyBounds.tileExponent c) (hC : 0 ≤ C)
    (hgap : a * EntropyBounds.tileExponent c < 1+s/2) :
    ∀ᶠ n : ℕ in atTop, ∀ m d : ℕ,
      (4:ℝ)^m ≤ C * (Real.log (n:ℝ))^k * (n:ℝ)^a →
      (n:ℝ)^s ≤ (d:ℝ) →
      (Nat.ceil (c*(m:ℝ))).choose m *
        4^(Nat.ceil (c*(m:ℝ)) - m) ≤ n * FoldedCounts.foldWidth d := by
  have hf := actualGridFitsUniformlyEventually c a (1+s/2) C k hc hT hC hgap
  filter_upwards [hf, eventually_ge_atTop (1:ℕ)] with n hfn hn
  intro m d hDn hdn
  have hfit := hfn m (n * FoldedCounts.foldWidth d) hDn
    (foldedOuterLower n d s hn hdn)
  have hcast :
      (((Nat.ceil (c*(m:ℝ))).choose m *
        4^(Nat.ceil (c*(m:ℝ)) - m):ℕ):ℝ) ≤
      ((n * FoldedCounts.foldWidth d:ℕ):ℝ) := by
    simpa [EntropyBounds.gridCount] using hfit
  exact_mod_cast hcast

/-- Candidate-uniform scalar phase fit. Its threshold is independent of
all candidate padded dimensions and folding moduli. -/
theorem alignedScalarGridFitsUniformlyEventually
    (s C : ℝ) (k : ℕ)
    (hs0 : 0 ≤ s) (hsu : s ≤ AsymptoticCosts.u) (hC : 0 ≤ C) :
    ∀ᶠ n : ℕ in atTop, ∀ m d : ℕ,
      (4:ℝ)^m ≤ C * (Real.log (n:ℝ))^k * (n:ℝ)^(AsymptoticCosts.b+s) →
      (n:ℝ)^s ≤ (d:ℝ) →
      (Nat.ceil (RealCertificate.c*(m:ℝ))).choose m *
        4^(Nat.ceil (RealCertificate.c*(m:ℝ)) - m) ≤
      n * FoldedCounts.foldWidth d := by
  apply actualFoldedGridFitsUniformlyEventually RealCertificate.c
    (AsymptoticCosts.b+s) s C k
    (by norm_num [RealCertificate.c]) _ hC _
  · rw [tileExponent_eq_T]
    exact le_of_lt (lt_trans (by norm_num) RealCertificate.TEnclosure.1)
  · rw [tileExponent_eq_T]
    have h := AsymptoticCosts.scalarGeometryAllStages s hs0 hsu
    unfold AsymptoticCosts.scalarGeometry at h
    linarith [AsymptoticCosts.slackPositive]

/-- Candidate-uniform cyclic phase fit. The frozen folding exponent is `u`
and the dimension exponent is `e`. -/
theorem alignedCyclicGridFitsUniformlyEventually
    (C : ℝ) (k : ℕ) (hC : 0 ≤ C) :
    ∀ᶠ n : ℕ in atTop, ∀ m d : ℕ,
      (4:ℝ)^m ≤ C * (Real.log (n:ℝ))^k * (n:ℝ)^AsymptoticCosts.e →
      (n:ℝ)^AsymptoticCosts.u ≤ (d:ℝ) →
      (Nat.ceil (RealCertificate.c*(m:ℝ))).choose m *
        4^(Nat.ceil (RealCertificate.c*(m:ℝ)) - m) ≤
      n * FoldedCounts.foldWidth d := by
  apply actualFoldedGridFitsUniformlyEventually RealCertificate.c
    AsymptoticCosts.e AsymptoticCosts.u C k
    (by norm_num [RealCertificate.c]) _ hC _
  · rw [tileExponent_eq_T]
    exact le_of_lt (lt_trans (by norm_num) RealCertificate.TEnclosure.1)
  · rw [tileExponent_eq_T]
    have h := AsymptoticCosts.cyclicGeometrySlack
    unfold AsymptoticCosts.cyclicGeometry at h
    linarith [AsymptoticCosts.slackPositive]



lemma ceilDiv_cast_le_div_add_one (n h : ℕ) (hh : 0 < h) :
    ((n ⌈/⌉ h : ℕ) : ℝ) ≤ (n : ℝ) / (h : ℝ) + 1 := by
  have hhR : (0 : ℝ) < h := by exact_mod_cast hh
  rw [Nat.ceilDiv_eq_add_pred_div]
  calc
    (((n + h - 1) / h : ℕ) : ℝ) ≤ ((n + h - 1 : ℕ) : ℝ) / (h : ℝ) := Nat.cast_div_le
    _ ≤ ((n + h : ℕ) : ℝ) / (h : ℝ) := div_le_div_of_nonneg_right (by exact_mod_cast Nat.sub_le (n + h) 1) (le_of_lt hhR)
    _ = (n : ℝ) / (h : ℝ) + 1 := by push_cast; field_simp

lemma ceilDiv_cast_le_two_mul_div (n h : ℕ) (hh : 0 < h) (hhn : h ≤ n) :
    ((n ⌈/⌉ h : ℕ) : ℝ) ≤ 2 * (n : ℝ) / (h : ℝ) := by
  have hhR : (0 : ℝ) < h := by exact_mod_cast hh
  have hhnR : (h : ℝ) ≤ n := by exact_mod_cast hhn
  have hone : (1 : ℝ) ≤ (n : ℝ) / h := (le_div_iff₀ hhR).2 (by simpa using hhnR)
  calc
    ((n ⌈/⌉ h : ℕ) : ℝ) ≤ (n : ℝ) / (h : ℝ) + 1 := ceilDiv_cast_le_div_add_one n h hh
    _ ≤ 2 * ((n : ℝ) / (h : ℝ)) := by linarith
    _ = 2 * (n : ℝ) / (h : ℝ) := by ring





/-- The actual number of blocks after upward rounding of the block size. -/
noncomputable def blockCount (n : ℕ) (b : ℝ) : ℕ :=
  n ⌈/⌉ blockSize n b

theorem blockSize_pos (n : ℕ) (b : ℝ) (hn : 1 ≤ n) :
    0 < blockSize n b := by
  apply Nat.ceil_pos.mpr
  exact Real.rpow_pos_of_pos (by exact_mod_cast (by omega : 0 < n)) b

theorem blockSize_le_n (n : ℕ) (b : ℝ) (hn : 1 ≤ n) (hb : b ≤ 1) :
    blockSize n b ≤ n := by
  apply Nat.ceil_le.mpr
  exact Real.rpow_le_self_of_one_le (by exact_mod_cast hn) hb

lemma n_div_blockSize_le_rpow (n : ℕ) (b : ℝ) (hn : 1 ≤ n) :
    (n : ℝ) / (blockSize n b : ℝ) ≤ (n : ℝ)^(1-b) := by
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hlo : (n : ℝ)^b ≤ (blockSize n b : ℝ) := Nat.le_ceil _
  calc
    (n : ℝ) / (blockSize n b : ℝ) ≤ (n : ℝ) / (n : ℝ)^b :=
      div_le_div_of_nonneg_left hn0.le (Real.rpow_pos_of_pos hn0 b) hlo
    _ = (n : ℝ)^(1-b) := by rw [Real.rpow_sub hn0, Real.rpow_one]

/-- The number of individual outer-pair block queries. -/
noncomputable def queryCount (n : ℕ) (b : ℝ) : ℕ := n^2 * blockCount n b

lemma pair_times_block_exponent (n : ℕ) (b : ℝ) (hn : 1 ≤ n) :
    (n : ℝ)^2 * (n : ℝ)^(1-b) = (n : ℝ)^(3-b) := by
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  rw [← Real.rpow_natCast (n : ℝ) 2, ← Real.rpow_add hn0]
  congr 1
  norm_num
  ring

/-- Upward integer rounding still gives the asserted number of blocks.
The lower restriction `0 ≤ b` used by the application is unnecessary here. -/
theorem blockCount_upper (n : ℕ) (b : ℝ) (hn : 1 ≤ n) (hb : b ≤ 1) :
    (blockCount n b : ℝ) ≤ 2*(n : ℝ)^(1-b) := by
  calc
    (blockCount n b : ℝ) ≤ 2*(n : ℝ)/(blockSize n b : ℝ) :=
      ceilDiv_cast_le_two_mul_div n (blockSize n b)
        (blockSize_pos n b hn) (blockSize_le_n n b hn hb)
    _ = 2*((n : ℝ)/(blockSize n b : ℝ)) := by ring
    _ ≤ 2*(n : ℝ)^(1-b) :=
      mul_le_mul_of_nonneg_left (n_div_blockSize_le_rpow n b hn) (by norm_num)

theorem outerPairBlockQueries_upper (n : ℕ) (b : ℝ) (hn : 1 ≤ n) (hb : b ≤ 1) :
    (n : ℝ)^2 * (blockCount n b : ℝ) ≤ 2*(n : ℝ)^(3-b) := by
  calc
    (n : ℝ)^2 * (blockCount n b : ℝ) ≤ (n : ℝ)^2 * (2*(n : ℝ)^(1-b)) :=
      mul_le_mul_of_nonneg_left (blockCount_upper n b hn hb) (sq_nonneg _)
    _ = 2*((n : ℝ)^2 * (n : ℝ)^(1-b)) := by ring
    _ = 2*(n : ℝ)^(3-b) := by rw [pair_times_block_exponent n b hn]

theorem queryCount_upper (n : ℕ) (b : ℝ) (hn : 1 ≤ n) (hb : b ≤ 1) :
    (queryCount n b : ℝ) ≤ 2*(n : ℝ)^(3-b) := by
  simpa only [queryCount, Nat.cast_mul, Nat.cast_pow] using
    outerPairBlockQueries_upper n b hn hb

/-- Splitting a list of distinct primes, all different from three, yields
coprime physical and cyclic factors even after the physical factor three. -/
theorem split_prime_products_coprime
    (factors : List ℕ) (S : ℕ) (hnd : factors.Nodup)
    (hprime : ∀ p ∈ factors, Nat.Prime p)
    (hthree : ∀ p ∈ factors, p ≠ 3) :
    Nat.Coprime (3 * (factors.take S).prod) ((factors.drop S).prod) := by
  rw [Nat.coprime_mul_iff_left]
  constructor
  · apply Nat.coprime_list_prod_right_iff.mpr
    intro p hp
    have hpf : p ∈ factors := List.mem_of_mem_drop hp
    apply (Nat.coprime_primes (by norm_num : Nat.Prime 3) (hprime p hpf)).mpr
    exact (hthree p hpf).symm
  · apply Nat.coprime_list_prod_left_iff.mpr
    intro p hp
    apply Nat.coprime_list_prod_right_iff.mpr
    intro q hq
    have hpf : p ∈ factors := List.mem_of_mem_take hp
    have hqf : q ∈ factors := List.mem_of_mem_drop hq
    apply (Nat.coprime_primes (hprime p hpf) (hprime q hqf)).mpr
    intro hpq
    subst q
    exact (List.disjoint_take_drop hnd (Nat.le_refl S)) hp hq


/-- The actual finite candidate enumeration has at most 8P entries. -/
theorem candidate_count_le (P : ℕ) : (PrimePool.candidates P).card ≤ 8*P := by
  have hs : PrimePool.candidates P ⊆ Finset.range (8*P) := by
    intro p hp
    exact Finset.mem_range.mpr (PrimePool.candidate_upper hp)
  simpa using Finset.card_le_card hs

/-- A candidate call is bounded by its actual number of prime factors. -/
structure PhaseCall (R P : ℕ) where
  factors : List ℕ
  length_le : factors.length ≤ R
  valid : ∀ p ∈ factors, p ∈ PrimePool.candidates P

def PhaseCall.folded {R P : ℕ} (call : PhaseCall R P) (S : ℕ) : ℕ :=
  (call.factors.take S).prod

def PhaseCall.cyclic {R P : ℕ} (call : PhaseCall R P) (S : ℕ) : ℕ :=
  (call.factors.drop S).prod

/-- This includes a final R-factor certification call, not just selected prefixes. -/
def candidateCall {R P : ℕ} (selected : List ℕ) (hpref : selected.length < R)
    (valid : ∀ p ∈ selected, p ∈ PrimePool.candidates P)
    (p : ℕ) (hp : p ∈ PrimePool.candidates P) : PhaseCall R P where
  factors := selected ++ [p]
  length_le := by simp only [List.length_append, List.length_singleton]; omega
  valid := by
    intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · exact valid q hq
    · have heq : q = p := List.mem_singleton.mp hq
      simpa only [heq] using hp

/-- The physical signed-window modulus folds the fixed factor three once. -/
def physicalFold {R P : ℕ} (call : PhaseCall R P) (S : ℕ) : ℕ :=
  3*call.folded S

/-- The actual outer dimensions, with upward residue padding. -/
def outerSize {R P : ℕ} (call : PhaseCall R P) (S n : ℕ) : ℕ :=
  n*FoldedCounts.foldWidth (physicalFold call S)

/-- Scalar and cyclic exponents record exact integral factor counts. -/
def foldExponent (S j : ℕ) : ℝ := ((min S j : ℕ) : ℝ)*eta
def ringExponent (S j : ℕ) : ℝ := ((j-S : ℕ) : ℝ)*eta

lemma foldExponent_scalar (S j : ℕ) (hj : j ≤ S) :
    foldExponent S j = (j:ℝ)*eta := by simp [foldExponent, Nat.min_eq_right hj]

lemma foldExponent_frozen (S j : ℕ) (hj : S ≤ j) :
    foldExponent S j = (S:ℝ)*eta := by simp [foldExponent, Nat.min_eq_left hj]

lemma aligned_fold_exponent_range (j : ℕ) :
    0 ≤ foldExponent AlignedCertificate.S j ∧ foldExponent AlignedCertificate.S j ≤ u := by
  rcases stageRelations with ⟨hη, hu, hv⟩
  constructor
  · exact mul_nonneg (Nat.cast_nonneg _) hη
  · rw [hu]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.min_le_left AlignedCertificate.S j) hη

lemma aligned_ring_exponent_range (j : ℕ) (hj : j ≤ AlignedCertificate.R) :
    0 ≤ ringExponent AlignedCertificate.S j ∧ ringExponent AlignedCertificate.S j ≤ v := by
  rcases stageRelations with ⟨hη, hu, hv⟩
  constructor
  · exact mul_nonneg (Nat.cast_nonneg _) hη
  · rw [hv]
    exact mul_le_mul_of_nonneg_right
      (by exact_mod_cast Nat.sub_le_sub_right hj AlignedCertificate.S) hη

/-- Every actual list length, including all candidate products, lies in one
of the certified scalar/cyclic intervals. No large R-element list is evaluated. -/
theorem actual_call_stage_slack {P : ℕ} (call : PhaseCall AlignedCertificate.R P)
    (i : Fin 6) :
    delta + slack ≤
      if call.factors.length ≤ AlignedCertificate.S then
        scalarSaving (foldExponent AlignedCertificate.S call.factors.length) i
      else cyclicSaving (ringExponent AlignedCertificate.S call.factors.length) i := by
  split_ifs with hphase
  · apply scalarAllStages _ (aligned_fold_exponent_range _).1 (aligned_fold_exponent_range _).2
  · apply cyclicAllStages _ (aligned_ring_exponent_range _ call.length_le).1
      (aligned_ring_exponent_range _ call.length_le).2


/-- Uniform fixed polylog overhead for at most R actual prime factors. -/
def phaseOverhead (R k n : ℕ) : ℝ := (16:ℝ)^R * (Real.log (n:ℝ))^(k*R)

lemma phaseOverhead_ge_one (R k n : ℕ) (hn : 3 ≤ n) : 1 ≤ phaseOverhead R k n := by
  exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num))
    (one_le_pow₀ (one_le_log_nat n hn))

lemma PhaseCall.interval {R P : ℕ} (call : PhaseCall R P) : FactorBounds P call.factors := by
  intro p hp
  exact ⟨PrimePool.candidate_lower (call.valid p hp),
    le_of_lt (PrimePool.candidate_upper (call.valid p hp))⟩

lemma PhaseCall.split {R P : ℕ} (call : PhaseCall R P) (S : ℕ) :
    call.folded S * call.cyclic S = call.factors.prod :=
  List.prod_take_mul_prod_drop call.factors S

lemma PhaseCall.folded_bounds {R P : ℕ} (call : PhaseCall R P) (S : ℕ) :
    P^(min S call.factors.length) ≤ call.folded S ∧
      call.folded S ≤ (8*P)^(min S call.factors.length) :=
  frozenProduct_bounds call.interval

lemma PhaseCall.cyclic_bounds {R P : ℕ} (call : PhaseCall R P) (S : ℕ) :
    P^(call.factors.length-S) ≤ call.cyclic S ∧
      call.cyclic S ≤ (8*P)^(call.factors.length-S) :=
  cyclicProduct_bounds call.interval

/-- Every selected or discarded R-factor candidate modulus is charged. -/
theorem actual_composite_upper {R P : ℕ} (call : PhaseCall R P) (hP : 1 ≤ P) :
    3*call.folded S*call.cyclic S ≤ 3*(8*P)^R := by
  rw [mul_assoc, call.split]
  exact Nat.mul_le_mul_left _ (list_product_upper_of_length_le call.interval hP call.length_le)

lemma productScale_uniform (n k j R d : ℕ) (hn : 3 ≤ n) (hj : j ≤ R)
    (hd : (primeScale n eta k)^j ≤ d ∧ d ≤ (8*primeScale n eta k)^j) :
    (n:ℝ)^((j:ℝ)*eta) ≤ (d:ℝ) ∧
      (d:ℝ) ≤ phaseOverhead R k n * (n:ℝ)^((j:ℝ)*eta) := by
  have heta := stageRelations.1
  have hdR : (primeScale n eta k:ℝ)^j ≤ (d:ℝ) ∧
      (d:ℝ) ≤ (8*(primeScale n eta k:ℝ))^j := by exact_mod_cast hd
  have hb := primeProductScale_bounds n eta k j d hn heta hdR
  refine ⟨hb.1, hb.2.trans ?_⟩
  have h16 : (16:ℝ)^j ≤ (16:ℝ)^R := pow_le_pow_right₀ (by norm_num) hj
  have hlog : (Real.log (n:ℝ))^(k*j) ≤ (Real.log (n:ℝ))^(k*R) :=
    pow_le_pow_right₀ (one_le_log_nat n hn) (Nat.mul_le_mul_left k hj)
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul h16 hlog (pow_nonneg (by linarith [one_le_log_nat n hn]) _)
      (by positivity)) (Real.rpow_nonneg (Nat.cast_nonneg n) _)

/-- Actual frozen modulus bounds with exact integral stage exponent. -/
theorem actual_folded_bounds (R S n k : ℕ) (hn : 3 ≤ n)
    (call : PhaseCall R (primeScale n eta k)) :
    (n:ℝ)^(foldExponent S call.factors.length) ≤ (call.folded S:ℝ) ∧
      (call.folded S:ℝ) ≤ phaseOverhead R k n * (n:ℝ)^(foldExponent S call.factors.length) := by
  exact productScale_uniform n k (min S call.factors.length) R (call.folded S) hn
    ((Nat.min_le_right _ _).trans call.length_le) (call.folded_bounds S)

/-- Actual cyclic modulus bounds include every intermediate trial candidate. -/
theorem actual_cyclic_bounds (R S n k : ℕ) (hn : 3 ≤ n)
    (call : PhaseCall R (primeScale n eta k)) :
    (n:ℝ)^(ringExponent S call.factors.length) ≤ (call.cyclic S:ℝ) ∧
      (call.cyclic S:ℝ) ≤ phaseOverhead R k n * (n:ℝ)^(ringExponent S call.factors.length) := by
  exact productScale_uniform n k (call.factors.length-S) R (call.cyclic S) hn
    ((Nat.sub_le _ _).trans call.length_le) (call.cyclic_bounds S)

/-- The cyclic exponent never exceeds v, including the last certification call. -/
theorem actual_cyclic_terminal_bound (n k : ℕ) (hn : 3 ≤ n)
    (call : PhaseCall AlignedCertificate.R (primeScale n eta k)) :
    (call.cyclic AlignedCertificate.S : ℝ) ≤
      phaseOverhead AlignedCertificate.R k n * (n:ℝ)^v := by
  have h := (actual_cyclic_bounds AlignedCertificate.R AlignedCertificate.S n k hn call).2
  exact h.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1≤n by omega))
      (aligned_ring_exponent_range call.factors.length call.length_le).2)
    (by have hH := phaseOverhead_ge_one AlignedCertificate.R k n hn; linarith))

/-- Candidate enumeration costs one n^eta factor, with its actual ceiling. -/
theorem actual_candidate_count (n k : ℕ) (hn : 3 ≤ n) :
    ((PrimePool.candidates (primeScale n eta k)).card : ℝ) ≤
      16*(Real.log (n:ℝ))^k*(n:ℝ)^eta := by
  have hp := (primeScale_bounds n eta k hn stageRelations.1).2
  have hc : ((PrimePool.candidates (primeScale n eta k)).card : ℝ) ≤
      8*(primeScale n eta k:ℝ) := by exact_mod_cast candidate_count_le (primeScale n eta k)
  nlinarith

def innerDimension (n : ℕ) {R P : ℕ} (call : PhaseCall R P) (S : ℕ) : ℕ :=
  pad4 (blockSize n b * physicalFold call S)

def innerPower (n : ℕ) {R P : ℕ} (call : PhaseCall R P) (S : ℕ) : ℕ :=
  Nat.clog 4 (blockSize n b * physicalFold call S)

lemma innerDimension_eq_power (n : ℕ) {R P : ℕ} (call : PhaseCall R P) (S : ℕ) :
    innerDimension n call S = 4^(innerPower n call S) := rfl

/-- Actual 3hd physical packing and power-of-four padding retain exponent b+s. -/
theorem actual_inner_bounds (R S n k : ℕ) (hn : 3 ≤ n)
    (call : PhaseCall R (primeScale n eta k)) :
    (n:ℝ)^(b+foldExponent S call.factors.length) ≤ (innerDimension n call S:ℝ) ∧
      (innerDimension n call S:ℝ) ≤
        (24*(16:ℝ)^R)*(Real.log (n:ℝ))^(k*R) *
          (n:ℝ)^(b+foldExponent S call.factors.length) := by
  have hb : 0 ≤ b := by norm_num [b, AlignedCertificate.b]
  have hh := blockSize_bounds n b (by omega) hb
  have hd := actual_folded_bounds R S n k hn call
  have hnpos : 0 < (n:ℝ) := by exact_mod_cast (show 0<n by omega)
  have hhp : 0 < blockSize n b := by
    have h := (Real.rpow_pos_of_pos hnpos b).trans_le hh.1
    exact_mod_cast h
  have hdp : 0 < call.folded S := by
    have h := (Real.rpow_pos_of_pos hnpos _).trans_le hd.1
    exact_mod_cast h
  have hp := pad4_bounds (blockSize n b * (3*call.folded S)) (by positivity)
  have hpR : (blockSize n b:ℝ)*(3*(call.folded S:ℝ)) ≤ (innerDimension n call S:ℝ) ∧
      (innerDimension n call S:ℝ) ≤ 4*((blockSize n b:ℝ)*(3*(call.folded S:ℝ))) := by
    exact_mod_cast hp
  rw [Real.rpow_add hnpos]
  constructor
  · calc
      (n:ℝ)^b * (n:ℝ)^(foldExponent S call.factors.length) ≤
          (blockSize n b:ℝ)*(call.folded S:ℝ) := by gcongr; exact hh.1; exact hd.1
      _ ≤ (innerDimension n call S:ℝ) := by nlinarith [hpR.1]
  · calc
      (innerDimension n call S:ℝ) ≤ 4*((blockSize n b:ℝ)*(3*(call.folded S:ℝ))) := hpR.2
      _ ≤ 4*((2*(n:ℝ)^b)*(3*(phaseOverhead R k n*(n:ℝ)^(foldExponent S call.factors.length)))) := by
        gcongr; exact hh.2; exact hd.2
      _ = _ := by unfold phaseOverhead; ring

/-- The actual folded outer dimension has the certified square-root exponent. -/
theorem actual_outer_bounds (R S n k : ℕ) (hn : 3 ≤ n)
    (call : PhaseCall R (primeScale n eta k))
    (hs : 0 ≤ foldExponent S call.factors.length) :
    (n:ℝ)^(1+foldExponent S call.factors.length/2) ≤ (outerSize call S n:ℝ) ∧
      (outerSize call S n:ℝ) ≤ 4*phaseOverhead R k n*
        (n:ℝ)^(1+foldExponent S call.factors.length/2) := by
  have hd := actual_folded_bounds R S n k hn call
  have hnpos : 0 < (n:ℝ) := by exact_mod_cast (show 0<n by omega)
  have hdp : 0 < call.folded S := by
    have h := (Real.rpow_pos_of_pos hnpos _).trans_le hd.1
    exact_mod_cast h
  constructor
  · apply foldedOuterLower n (physicalFold call S) _ (by omega)
    exact hd.1.trans (by dsimp [physicalFold]; push_cast; nlinarith)
  · simpa only [outerSize, physicalFold, Nat.cast_mul] using
      foldedOuter_upper n (call.folded S) (phaseOverhead R k n) _ hn hdp
        (phaseOverhead_ge_one R k n hn) hs hd.2


/-- Distinct candidate primes preserve the actual physical/cyclic coprimality. -/
theorem actual_call_coprime {R P : ℕ} (call : PhaseCall R P) (S : ℕ)
    (hP : 3 ≤ P) (hnd : call.factors.Nodup) :
    (physicalFold call S).Coprime (call.cyclic S) := by
  apply split_prime_products_coprime call.factors S hnd
  · intro p hp
    exact PrimePool.candidate_prime (call.valid p hp)
  · intro p hp
    have h := (PrimePool.mem_candidates.mp (call.valid p hp)).2.1
    omega

/-- A common threshold fits every candidate at every scalar or cyclic stage.
The dimension is the actual power-of-four padding of 3h*d. -/
theorem all_actual_candidate_tiles_fit (k : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      ∀ call : PhaseCall AlignedCertificate.R (primeScale n eta k),
        (Nat.ceil (RealCertificate.c*(innerPower n call AlignedCertificate.S:ℝ))).choose
            (innerPower n call AlignedCertificate.S) *
          4^(Nat.ceil (RealCertificate.c*(innerPower n call AlignedCertificate.S:ℝ)) -
            innerPower n call AlignedCertificate.S) ≤ outerSize call AlignedCertificate.S n := by
  let C : ℝ := 24*(16:ℝ)^AlignedCertificate.R
  have hfit : ∀ᶠ n : ℕ in atTop, ∀ j : Fin (AlignedCertificate.R+1), ∀ m d : ℕ,
      (4:ℝ)^m ≤ C*(Real.log (n:ℝ))^(k*AlignedCertificate.R)*
        (n:ℝ)^(b+foldExponent AlignedCertificate.S j.val) →
      (n:ℝ)^(foldExponent AlignedCertificate.S j.val) ≤ (d:ℝ) →
      (Nat.ceil (RealCertificate.c*(m:ℝ))).choose m *
        4^(Nat.ceil (RealCertificate.c*(m:ℝ))-m) ≤ n*FoldedCounts.foldWidth d := by
    apply Filter.eventually_all.mpr
    intro j
    exact alignedScalarGridFitsUniformlyEventually
      (foldExponent AlignedCertificate.S j.val) C (k*AlignedCertificate.R)
      (aligned_fold_exponent_range _).1 (aligned_fold_exponent_range _).2 (by dsimp [C]; positivity)
  filter_upwards [hfit, eventually_ge_atTop (3:ℕ)] with n hfitn hn
  intro call
  let j : Fin (AlignedCertificate.R+1) := ⟨call.factors.length, by have h := call.length_le; omega⟩
  apply hfitn j (innerPower n call AlignedCertificate.S) (physicalFold call AlignedCertificate.S)
  · have hD := (actual_inner_bounds AlignedCertificate.R AlignedCertificate.S n k hn call).2
    simpa only [C, innerDimension_eq_power, Nat.cast_pow, Nat.cast_ofNat, j] using hD
  · have hd := (actual_folded_bounds AlignedCertificate.R AlignedCertificate.S n k hn call).1
    exact hd.trans (by dsimp [physicalFold]; push_cast; nlinarith)

/-- These exponents are obtained by multiplying the actual product count,
query count, candidate count, cyclic width and folded dimension scales. -/
def phaseCostExponent (s w : ℝ) (i : Fin 6) : ℝ :=
  ![eta+(1-b)+w+2*(1+s/2)-(b+s)*RealCertificate.G,
    eta+(3-b)+w+(b+s)*RealCertificate.q1,
    eta+(3-b)+(b+s)*RealCertificate.q2,
    eta+(1-b)+w+(1+s/2)+(b+s)*RealCertificate.Esource,
    eta+(1-b)+w+(1+s/2)+(b+s)*RealCertificate.Ebox,
    eta+(1-b)+w+(1+s/2)+(b+s)] i

lemma phaseCostExponent_scalar (s : ℝ) (i : Fin 6) :
    phaseCostExponent s 0 i = 3-scalarSaving s i := by
  fin_cases i <;> simp [phaseCostExponent, scalarSaving] <;> ring

lemma e_eq_b_add_u : e = b+u := by
  norm_num [e, b, u, AlignedCertificate.e, AlignedCertificate.b, AlignedCertificate.u]

lemma phaseCostExponent_cyclic (w : ℝ) (i : Fin 6) :
    phaseCostExponent u w i = 3-cyclicSaving w i := by
  fin_cases i <;> simp [phaseCostExponent, cyclicSaving, e_eq_b_add_u] <;> ring

/-- Strict certified exponent bounds apply to every actual candidate-factor
list, including the final R-factor certification products. -/
theorem actual_call_exponent_strict {P : ℕ} (call : PhaseCall AlignedCertificate.R P)
    (i : Fin 6) :
    phaseCostExponent (foldExponent AlignedCertificate.S call.factors.length)
      (ringExponent AlignedCertificate.S call.factors.length) i < targetExponent := by
  by_cases hj : call.factors.length ≤ AlignedCertificate.S
  · have hw : ringExponent AlignedCertificate.S call.factors.length = 0 := by
      simp [ringExponent, Nat.sub_eq_zero_of_le hj]
    rw [hw, phaseCostExponent_scalar]
    have h := scalarAllStages (foldExponent AlignedCertificate.S call.factors.length)
      (aligned_fold_exponent_range call.factors.length).1
      (aligned_fold_exponent_range call.factors.length).2 i
    unfold targetExponent
    linarith [slackPositive]
  · have hs : foldExponent AlignedCertificate.S call.factors.length = u := by
      rw [foldExponent_frozen _ _ (by omega)]
      exact stageRelations.2.1.symm
    rw [hs, phaseCostExponent_cyclic]
    have h := cyclicAllStages _
      (aligned_ring_exponent_range _ call.length_le).1
      (aligned_ring_exponent_range _ call.length_le).2 i
    unfold targetExponent
    linarith [slackPositive]

#print axioms actual_composite_upper
#print axioms actual_folded_bounds
#print axioms actual_cyclic_terminal_bound
#print axioms actual_candidate_count
#print axioms actual_inner_bounds
#print axioms actual_outer_bounds
#print axioms blockCount_upper
#print axioms queryCount_upper
#print axioms actual_call_coprime
#print axioms all_actual_candidate_tiles_fit
#print axioms actual_call_exponent_strict

end
end ThinMatrix.PhaseGeometry
