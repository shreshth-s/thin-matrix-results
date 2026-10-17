import Mathlib

/-!
# Finite algebra of aligned tensor contractions

The raw arrays below are arbitrary functions on finite index types. In
particular, the index types may be finite coordinate function spaces; no
source homogeneity, nonnegativity, support restriction, or embedding
assumption occurs in the algebraic statements.

This module concerns finite identities only. It does not prove the
Walsh/source embedding, normalization/divisibility, compact storage,
asymptotic operation or bit costs, prime selection, or an APSP reduction.
-/

namespace ThinMatrix.TensorContraction

open scoped BigOperators
open Finset Polynomial

universe u v w x

variable {R : Type u} [CommRing R]
variable {A : Type v} {B : Type w} {ι : Type x}
variable [Fintype A] [Fintype B] [DecidableEq ι]

/-- Bilinear contraction of arbitrary raw arrays against a finite kernel. -/
def bilinear (X : A → R) (Y : B → R) (K : A → B → R) : R :=
  ∑ a, ∑ b, X a * Y b * K a b

/-- A tensor-product kernel on the specified physical coordinates. -/
def tensorKernel (q : Finset ι) (K : ι → A → B → R) (a : A) (b : B) : R :=
  ∏ i ∈ q, K i a b

theorem bilinear_separable (X : A → R) (Y : B → R) (f : A → R) (g : B → R) :
    bilinear X Y (fun a b => f a * g b) =
      (∑ a, X a * f a) * (∑ b, Y b * g b) := by
  unfold bilinear
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  ring

theorem bilinear_sum {κ : Type*} (s : Finset κ)
    (X : A → R) (Y : B → R) (K : κ → A → B → R) :
    bilinear X Y (fun a b => ∑ c ∈ s, K c a b) =
      ∑ c ∈ s, bilinear X Y (K c) := by
  classical
  unfold bilinear
  simp_rw [Finset.mul_sum]
  calc
    (∑ a, ∑ b, ∑ c ∈ s, X a * Y b * K c a b) =
        ∑ a, ∑ c ∈ s, ∑ b, X a * Y b * K c a b := by
      apply Finset.sum_congr rfl
      intro a ha
      exact Finset.sum_comm
    _ = ∑ c ∈ s, ∑ a, ∑ b, X a * Y b * K c a b := Finset.sum_comm

theorem bilinear_scale (X : A → R) (Y : B → R) (K : A → B → R) (r : R) :
    bilinear X Y (fun a b => r * K a b) = r * bilinear X Y K := by
  unfold bilinear
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  ring

/-- The canonical five-term local identity over Mathlib's commutative rings. -/
theorem aligned_local (x₁ x₂ p₁ p₂ s v w : R) :
    (x₁+p₁+p₂)*(s+v) + (x₁+p₁)*(s-v) +
      (x₂-p₂)*(s+v-w) + x₂*(s-v+w) + (-x₁-x₂)*(2*s) =
      2*p₁*s+p₂*w := by ring

theorem shared_local (x₁ x₂ p₁ p₂ s w z : R) :
    (-x₁-x₂)*(2*s) + z*(2*p₁*s+p₂*w) =
      (-x₁-x₂+z*p₁)*(2*s)+z*p₂*w := by ring

/-- The five normal forms, including the private term at label four. -/
def alignedLeft (x₁ x₂ p₁ p₂ : R) : Fin 5 → R :=
  ![x₁+p₁+p₂, x₁+p₁, x₂-p₂, x₂, -x₁-x₂]

/-- The matching opposite forms; the private factor is `2*s`. -/
def alignedRight (s v w : R) : Fin 5 → R :=
  ![s+v, s-v, s+v-w, s-v+w, 2*s]

theorem aligned_label_sum (x₁ x₂ p₁ p₂ s v w : R) :
    (∑ l : Fin 5, alignedLeft x₁ x₂ p₁ p₂ l * alignedRight s v w l) =
      2*p₁*s+p₂*w := by
  simp [alignedLeft, alignedRight, Fin.sum_univ_succ]
  ring

/-- A local rank-one sum tensors and contracts on the same full label word. -/
theorem tensor_rank_one_expansion [Fintype ι] {Λ : Type*} [Fintype Λ]
    (X : A → R) (Y : B → R)
    (f : ι → Λ → A → R) (g : ι → Λ → B → R) :
    bilinear X Y (fun a b => ∏ i, ∑ l, f i l a * g i l b) =
      ∑ labels : ι → Λ,
        (∑ a, X a * ∏ i, f i (labels i) a) *
        (∑ b, Y b * ∏ i, g i (labels i) b) := by
  classical
  simp_rw [Finset.prod_univ_sum]
  rw [bilinear_sum]
  apply Finset.sum_congr rfl
  intro labels hlabels
  simp_rw [Finset.prod_mul_distrib]
  exact bilinear_separable X Y _ _

/-- The canonical five-term identity tensored on any finite number of
coordinates and contracted against arbitrary raw arrays. -/
theorem aligned_tensor_contraction [Fintype ι]
    (X : A → R) (Y : B → R)
    (x₁ x₂ p₁ p₂ : ι → A → R) (s v w : ι → B → R) :
    bilinear X Y (fun a b => ∏ i, (2*p₁ i a*s i b+p₂ i a*w i b)) =
      ∑ labels : ι → Fin 5,
        (∑ a, X a * ∏ i, alignedLeft (x₁ i a) (x₂ i a) (p₁ i a) (p₂ i a) (labels i)) *
        (∑ b, Y b * ∏ i, alignedRight (s i b) (v i b) (w i b) (labels i)) := by
  calc
    _ = bilinear X Y (fun a b => ∏ i, ∑ l : Fin 5,
        alignedLeft (x₁ i a) (x₂ i a) (p₁ i a) (p₂ i a) l *
        alignedRight (s i b) (v i b) (w i b) l) := by
      apply congrArg (bilinear X Y)
      funext a b
      apply Finset.prod_congr rfl
      intro i hi
      exact (aligned_label_sum _ _ _ _ _ _ _).symm
    _ = _ := tensor_rank_one_expansion X Y _ _

/-- Pointwise shared-factor expansion. A physical channel contributes one `z`. -/
theorem shared_product_expansion (q : Finset ι)
    (h d u v : ι → R) (z : R) :
    (∏ i ∈ q, (h i * d i + z * u i * v i)) =
      ∑ C ∈ q.powerset,
        z ^ C.card *
          ((∏ i ∈ C, u i) * ∏ i ∈ q \ C, h i) *
          ((∏ i ∈ C, v i) * ∏ i ∈ q \ C, d i) := by
  classical
  calc
    (∏ i ∈ q, (h i * d i + z * u i * v i)) =
        ∏ i ∈ q, (z * u i * v i + h i * d i) := by
      apply Finset.prod_congr rfl
      intro i hi
      ring
    _ = _ := by
      rw [Finset.prod_add]
      apply Finset.sum_congr rfl
      intro C hC
      simp_rw [Finset.prod_mul_distrib, Finset.prod_const]
      ring

/-- A cached left input, with the channel at precisely the physical set `C`. -/
def leftCache (q C : Finset ι) (X : A → R) (h u : ι → A → R) : R :=
  ∑ a, X a * ((∏ i ∈ C, u i a) * ∏ i ∈ q \ C, h i a)

/-- A cached right input using the same physical channel set. -/
def rightCache (q C : Finset ι) (Y : B → R) (d v : ι → B → R) : R :=
  ∑ b, Y b * ((∏ i ∈ C, v i b) * ∏ i ∈ q \ C, d i b)

/-- Exact shared-channel contraction on arbitrary raw arrays. -/
theorem shared_channel_contraction (q : Finset ι)
    (X : A → R) (Y : B → R)
    (h u : ι → A → R) (d v : ι → B → R) (z : R) :
    bilinear X Y (tensorKernel q (fun i a b => h i a * d i b + z*u i a*v i b)) =
      ∑ C ∈ q.powerset,
        z ^ C.card * leftCache q C X h u * rightCache q C Y d v := by
  classical
  unfold tensorKernel
  simp_rw [shared_product_expansion]
  rw [bilinear_sum]
  apply Finset.sum_congr rfl
  intro C hC
  simp_rw [mul_assoc]
  rw [bilinear_scale]
  simpa only [leftCache, rightCache, mul_assoc] using
    congrArg (fun r => z ^ C.card * r)
      (bilinear_separable X Y
        (fun a => (∏ i ∈ C, u i a) * ∏ i ∈ q \ C, h i a)
        (fun b => (∏ i ∈ C, v i b) * ∏ i ∈ q \ C, d i b))

/-- Polynomial specialization: the shift is `X^|C|`, once for both inputs. -/
theorem polynomial_channel_contraction (q : Finset ι)
    (Xraw : A → Polynomial R) (Yraw : B → Polynomial R)
    (h u : ι → A → Polynomial R) (d v : ι → B → Polynomial R) :
    bilinear Xraw Yraw
        (tensorKernel q (fun i a b => h i a*d i b+Polynomial.X*u i a*v i b)) =
      ∑ C ∈ q.powerset,
        Polynomial.X ^ C.card * leftCache q C Xraw h u * rightCache q C Yraw d v := by
  exact shared_channel_contraction q Xraw Yraw h u d v Polynomial.X

/-- Coefficient extraction applies the global channel shift exactly once. -/
theorem polynomial_channel_coefficient (q : Finset ι)
    (Xraw : A → Polynomial R) (Yraw : B → Polynomial R)
    (h u : ι → A → Polynomial R) (d v : ι → B → Polynomial R) (j : ℕ) :
    (bilinear Xraw Yraw
      (tensorKernel q (fun i a b => h i a*d i b+Polynomial.X*u i a*v i b))).coeff j =
      ∑ C ∈ q.powerset,
        if C.card ≤ j then
          (leftCache q C Xraw h u * rightCache q C Yraw d v).coeff (j-C.card)
        else 0 := by
  rw [polynomial_channel_contraction]
  simp only [mul_assoc, Polynomial.finsetSum_coeff, Polynomial.coeff_X_pow_mul']

/-- The integer binomial weight used in (A11), interpreted in any ring. -/
def residualWeight (n t j : ℕ) : R :=
  (-1 : R) ^ (t-j-1) * ((n-j-1).choose (t-j-1) : R)

/-- The complete low polynomial functional from (A11). -/
def weightedLow (n t : ℕ) (F : Polynomial R) : R :=
  ∑ j ∈ Finset.range t, residualWeight n t j * F.coeff j

/-- Only channel sets of size below `t` enter the weighted low functional.
The coefficient is read at `j-|C|`, so the physical shift is applied once. -/
theorem weighted_low_uses_small_channel_sets (q : Finset ι)
    (Xraw : A → Polynomial R) (Yraw : B → Polynomial R)
    (h u : ι → A → Polynomial R) (d v : ι → B → Polynomial R) (n t : ℕ) :
    weightedLow n t (bilinear Xraw Yraw
      (tensorKernel q (fun i a b => h i a*d i b+Polynomial.X*u i a*v i b))) =
      ∑ C ∈ q.powerset.filter (fun C => C.card < t),
        ∑ j ∈ Finset.range t,
          if C.card ≤ j then residualWeight n t j *
            (leftCache q C Xraw h u * rightCache q C Yraw d v).coeff (j-C.card)
          else 0 := by
  classical
  unfold weightedLow
  simp_rw [polynomial_channel_coefficient, Finset.mul_sum]
  rw [Finset.sum_comm, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro C hC
  by_cases hc : C.card < t
  · simp only [hc, if_true, mul_ite, mul_zero]
  · simp only [hc, if_false]
    apply Finset.sum_eq_zero
    intro j hj
    have hjt : j < t := Finset.mem_range.mp hj
    have hnot : ¬ C.card ≤ j := by omega
    simp [hnot]

end ThinMatrix.TensorContraction


open Finset
namespace ThinMatrix.BinomialPartition
variable {α R : Type*} [DecidableEq α] [CommRing R]

/-- The alternating partial binomial sum, in an arbitrary commutative ring. -/
theorem alternating_sum_range_choose_succ (n m : ℕ) :
    (∑ r ∈ range (m + 1), (-1 : R) ^ r * ((n + 1).choose r : R)) =
      (-1 : R) ^ m * (n.choose m : R) := by
  have h := congrArg (fun z : ℤ => (z : R))
    (Int.alternating_sum_range_choose_eq_choose (n := n) (m := m))
  simpa only [Int.cast_sum, Int.cast_mul, Int.cast_pow, Int.cast_neg,
    Int.cast_one, Int.cast_natCast] using h

/-- The truncated alternating binomial sum, with the indexing used by the
finite support partition. No characteristic assumption is needed. -/
theorem alternating_sum_range_choose (n m : ℕ) (hmn : m < n) :
    (∑ r ∈ range (m + 1), (-1 : R) ^ r * (n.choose r : R)) =
      (-1 : R) ^ m * ((n - 1).choose m : R) := by
  have hn : 0 < n := Nat.zero_lt_of_lt hmn
  have hs : n - 1 + 1 = n := Nat.sub_add_cancel hn
  simpa only [hs] using (alternating_sum_range_choose_succ (R := R) (n - 1) m)


/-- A finite-support form of the same identity: sum over all subsets of size
at most `m`. -/
theorem alternating_sum_powerset_card_le {α : Type*} [DecidableEq α]
    (A : Finset α) (m : ℕ) (hm : m < A.card) :
    (∑ S ∈ A.powerset.filter (fun S => S.card ≤ m), (-1 : R) ^ S.card) =
      (-1 : R) ^ m * ((A.card - 1).choose m : R) := by
  rw [sum_filter,
    sum_powerset_apply_card (fun k => if k ≤ m then (-1 : R) ^ k else 0)]
  calc
    (∑ r ∈ range (A.card + 1), A.card.choose r •
        (if r ≤ m then (-1 : R) ^ r else 0)) =
        ∑ r ∈ range (m + 1), (-1 : R) ^ r * (A.card.choose r : R) := by
      calc
        _ = ∑ r ∈ range (m + 1), A.card.choose r •
            (if r ≤ m then (-1 : R) ^ r else 0) := by
          symm
          apply sum_subset (range_mono (Nat.succ_le_succ (Nat.le_of_lt hm)))
          intro r hr hsmall
          have hlarge : ¬r ≤ m := by simpa using hsmall
          simp [hlarge]
        _ = _ := by
          apply sum_congr rfl
          intro r hr
          have hrm : r ≤ m := Nat.le_of_lt_succ (mem_range.mp hr)
          simp [hrm, nsmul_eq_mul, mul_comm]
    _ = _ := alternating_sum_range_choose _ _ hm


def mono (s J : Finset α) (P I : α → R) : R :=
  (∏ a ∈ J, I a) * ∏ a ∈ s \ J, P a

lemma expansion (s B : Finset α) (hB : B ⊆ s) (P I : α → R) :
    (∏ a ∈ B, (I a - P a)) * (∏ a ∈ s \ B, P a) =
      ∑ J ∈ B.powerset, (-1 : R) ^ (B.card - J.card) * mono s J P I := by
  simp_rw [sub_eq_add_neg]
  rw [prod_add, sum_mul]
  apply sum_congr rfl
  intro J hJ
  have hJB : J ⊆ B := mem_powerset.mp hJ
  rw [prod_neg, card_sdiff_of_subset hJB]
  unfold mono
  have hu : (s \ B) ∪ (B \ J) = s \ J := sdiff_union_sdiff_cancel hB hJB
  have hd : Disjoint (s \ B) (B \ J) := by
    apply disjoint_left.mpr
    intro a ha hb
    exact (mem_sdiff.mp ha).2 (mem_sdiff.mp hb).1
  have hp : (∏ a ∈ B \ J, P a) * (∏ a ∈ s \ B, P a) = ∏ a ∈ s \ J, P a := by
    rw [mul_comm, ← prod_union hd, hu]
  calc
    _ = (-1 : R) ^ (B.card - J.card) * ((∏ a ∈ J, I a) *
        ((∏ a ∈ B \ J, P a) * (∏ a ∈ s \ B, P a))) := by ring
    _ = _ := by rw [hp]

lemma superset_sum (s J : Finset α) (hJ : J ⊆ s) (t : ℕ)
    (ht : J.card < t) :
    (∑ B ∈ s.powerset.filter (fun B => J ⊆ B ∧ B.card < t),
      (-1 : R) ^ (B.card - J.card)) =
    ∑ C ∈ (s \ J).powerset.filter (fun C => C.card < t - J.card),
      (-1 : R) ^ C.card := by
  symm
  apply sum_bij (fun C _ => C ∪ J)
  · intro C hC
    rcases mem_filter.mp hC with ⟨hCs, hCt⟩
    have hCs' := mem_powerset.mp hCs
    apply mem_filter.mpr
    constructor
    · exact mem_powerset.mpr (union_subset (hCs'.trans sdiff_subset) hJ)
    · refine ⟨subset_union_right, ?_⟩
      have hd : Disjoint C J := disjoint_of_subset_left hCs' sdiff_disjoint
      rw [card_union_of_disjoint hd]
      omega
  · intro C₁ hC₁ C₂ hC₂ heq
    have hc₁ := mem_powerset.mp (mem_filter.mp hC₁).1
    have hc₂ := mem_powerset.mp (mem_filter.mp hC₂).1
    have hd₁ : Disjoint C₁ J := disjoint_of_subset_left hc₁ sdiff_disjoint
    have hd₂ : Disjoint C₂ J := disjoint_of_subset_left hc₂ sdiff_disjoint
    have hsd := congrArg (fun B : Finset α => B \ J) heq
    simpa [union_sdiff_distrib, Finset.sdiff_eq_self_iff_disjoint.mpr hd₁,
      Finset.sdiff_eq_self_iff_disjoint.mpr hd₂] using hsd
  · intro B hB
    rcases mem_filter.mp hB with ⟨hBs, hJB, hBt⟩
    have hBs' := mem_powerset.mp hBs
    refine ⟨B \ J, ?_, sdiff_union_of_subset hJB⟩
    apply mem_filter.mpr
    constructor
    · apply mem_powerset.mpr
      exact sdiff_subset_sdiff hBs' subset_rfl
    · rw [card_sdiff_of_subset hJB]
      omega
  · intro C hC
    have hCs' := mem_powerset.mp (mem_filter.mp hC).1
    have hd : Disjoint C J := disjoint_of_subset_left hCs' sdiff_disjoint
    rw [card_union_of_disjoint hd, Nat.add_sub_cancel_right]

lemma low_expand (s : Finset α) (t : ℕ) (P I : α → R) :
    (∑ B ∈ s.powerset.filter (fun B => B.card < t),
      (∏ a ∈ B, (I a - P a)) * (∏ a ∈ s \ B, P a)) =
    ∑ J ∈ s.powerset.filter (fun J => J.card < t),
      (∑ B ∈ s.powerset.filter (fun B => J ⊆ B ∧ B.card < t),
        (-1 : R) ^ (B.card - J.card)) * mono s J P I := by
  let S := s.powerset.filter (fun B => B.card < t)
  calc
    _ = ∑ B ∈ S, ∑ J ∈ B.powerset,
        (-1 : R) ^ (B.card - J.card) * mono s J P I := by
      apply sum_congr rfl
      intro B hB
      exact expansion s B (mem_powerset.mp (mem_filter.mp hB).1) P I
    _ = ∑ B ∈ S, ∑ J ∈ S,
        if J ⊆ B then (-1 : R) ^ (B.card - J.card) * mono s J P I else 0 := by
      apply sum_congr rfl
      intro B hB
      have hB' := mem_filter.mp hB
      have hBs := mem_powerset.mp hB'.1
      have heq : S.filter (fun J => J ⊆ B) = B.powerset := by
        ext J
        simp only [S, mem_filter, mem_powerset]
        constructor
        · exact fun h => h.2
        · intro hJB
          exact ⟨⟨hJB.trans hBs, (card_le_card hJB).trans_lt hB'.2⟩, hJB⟩
      rw [← sum_filter, heq]
    _ = ∑ J ∈ S, ∑ B ∈ S,
        if J ⊆ B then (-1 : R) ^ (B.card - J.card) * mono s J P I else 0 :=
      sum_comm
    _ = _ := by
      apply sum_congr rfl
      intro J hJ
      rw [← sum_filter, ← sum_mul]
      have heq : S.filter (fun B => J ⊆ B) =
          s.powerset.filter (fun B => J ⊆ B ∧ B.card < t) := by
        ext B
        simp only [S, mem_filter]
        tauto
      rw [heq]

lemma superset_coefficient (s J : Finset α) (hJ : J ⊆ s) (t : ℕ)
    (ht : J.card < t) (hts : t ≤ s.card) :
    (∑ B ∈ s.powerset.filter (fun B => J ⊆ B ∧ B.card < t),
      (-1 : R) ^ (B.card - J.card)) =
    (-1 : R) ^ (t - J.card - 1) *
      ((s.card - J.card - 1).choose (t - J.card - 1) : R) := by
  rw [superset_sum s J hJ t ht]
  have hp : 0 < t - J.card := Nat.sub_pos_of_lt ht
  have heq : (s \ J).powerset.filter (fun C => C.card < t - J.card) =
      (s \ J).powerset.filter (fun C => C.card ≤ t - J.card - 1) := by
    apply filter_congr
    intro C hC
    omega
  have hm : t - J.card - 1 < (s \ J).card := by
    rw [card_sdiff_of_subset hJ]
    omega
  rw [heq, alternating_sum_powerset_card_le (s \ J) (t - J.card - 1) hm,
    card_sdiff_of_subset hJ]

theorem finite_low_weighted (s : Finset α) (t : ℕ) (hts : t ≤ s.card)
    (P I : α → R) :
    (∑ B ∈ s.powerset.filter (fun B => B.card < t),
      (∏ a ∈ B, (I a - P a)) * (∏ a ∈ s \ B, P a)) =
    ∑ J ∈ s.powerset.filter (fun J => J.card < t),
      ((-1 : R) ^ (t - J.card - 1) *
        ((s.card - J.card - 1).choose (t - J.card - 1) : R)) * mono s J P I := by
  rw [low_expand]
  apply sum_congr rfl
  intro J hJ
  rw [superset_coefficient s J (mem_powerset.mp (mem_filter.mp hJ).1) t
    (mem_filter.mp hJ).2 hts]

omit [DecidableEq α] in
lemma rank_regroup (s : Finset α) (t : ℕ) (hts : t ≤ s.card + 1)
    (w : ℕ → R) (f : Finset α → R) :
    (∑ J ∈ s.powerset.filter (fun J => J.card < t), w J.card * f J) =
    ∑ j ∈ range t, w j * ∑ J ∈ s.powersetCard j, f J := by
  rw [sum_filter, sum_powerset]
  calc
    _ = ∑ j ∈ range (s.card + 1),
        if j < t then w j * ∑ J ∈ s.powersetCard j, f J else 0 := by
      apply sum_congr rfl
      intro j hj
      by_cases h : j < t
      · rw [if_pos h, mul_sum]
        apply sum_congr rfl
        intro J hJ
        have hcard := (mem_powersetCard.mp hJ).2
        simp only [hcard, h, if_true]
      · rw [if_neg h]
        apply sum_eq_zero
        intro J hJ
        have hcard := (mem_powersetCard.mp hJ).2
        simp only [hcard, h, if_false]
    _ = ∑ j ∈ range t, w j * ∑ J ∈ s.powersetCard j, f J := by
      symm
      calc
        _ = ∑ j ∈ range t,
            if j < t then w j * ∑ J ∈ s.powersetCard j, f J else 0 := by
          apply sum_congr rfl
          intro j hj
          simp only [mem_range.mp hj, if_true]
        _ = _ := sum_subset (range_mono hts) (by
          intro j hj hsmall
          have hlarge : ¬j < t := by simpa only [mem_range] using hsmall
          rw [if_neg hlarge])

/-- Finite binomial Möbius transform, in arbitrary characteristic. -/
theorem finite_binomial_transform (s : Finset α) (t : ℕ) (hts : t ≤ s.card)
    (P I : α → R) :
    (∑ j ∈ range t, ((-1 : R) ^ (t - j - 1) *
        ((s.card - j - 1).choose (t - j - 1) : R)) *
      (∑ J ∈ s.powersetCard j, (∏ a ∈ J, I a) * (∏ a ∈ s \ J, P a))) =
    ∑ B ∈ s.powerset.filter (fun B => B.card < t),
      (∏ a ∈ B, (I a - P a)) * (∏ a ∈ s \ B, P a) := by
  rw [finite_low_weighted s t hts P I]
  exact (rank_regroup s t (hts.trans (Nat.le_succ s.card))
    (fun j => ((-1 : R) ^ (t - j - 1) *
      ((s.card - j - 1).choose (t - j - 1) : R)))
    (fun J => mono s J P I)).symm

/-- The A11 formula over all coordinates of `Fin k`. -/
theorem A11 (k t : ℕ) (_ht : 0 < t) (htk : t ≤ k) (P I : Fin k → R) :
    (∑ j ∈ range t, ((-1 : R) ^ (t - j - 1) *
        ((k - j - 1).choose (t - j - 1) : R)) *
      (∑ J ∈ (univ : Finset (Fin k)).powersetCard j,
        (∏ a ∈ J, I a) * (∏ a ∈ Jᶜ, P a))) =
    ∑ B ∈ (univ : Finset (Fin k)).powerset.filter (fun B => B.card < t),
      (∏ a ∈ B, (I a - P a)) * (∏ a ∈ Bᶜ, P a) := by
  simpa only [card_univ, Fintype.card_fin, ← compl_eq_univ_sdiff] using
    finite_binomial_transform (univ : Finset (Fin k)) t (by simpa using htk) P I

end ThinMatrix.BinomialPartition



/-!
Ordered boxes with a star prefix and a fixed private/ordinary suffix.

The list of physical positions is read from right to left. The recursive
box scan stops when it has encountered its `t`-th ordinary position.
Consequently all as-yet unread physical positions, which form a prefix in
the ordinary left-to-right order, are stars. No box is defined by subtraction.
-/

namespace ThinMatrix.OrderedBoxes

universe u v
variable {ι : Type v} {R : Type u} [CommRing R]

/-- Product of the star factor `I = P + O` at every position. -/
def starProduct (P O : ι → R) : List ι → R
  | [] => 1
  | a :: xs => (P a + O a) * starProduct P O xs

/-- Expansion terms with fewer than `t` ordinary factors. -/
def thresholdLow (P O : ι → R) : Nat → List ι → R
  | 0, _ => 0
  | _ + 1, [] => 1
  | t + 1, a :: xs =>
      P a * thresholdLow P O (t + 1) xs + O a * thresholdLow P O t xs

/-- Concrete last-`t` ordinary boxes, scanning from right to left. -/
def orderedBoxHigh (P O : ι → R) : Nat → List ι → R
  | 0, xs => starProduct P O xs
  | _ + 1, [] => 0
  | t + 1, a :: xs =>
      P a * orderedBoxHigh P O (t + 1) xs + O a * orderedBoxHigh P O t xs

/-- Exact product partition, valid for every threshold and every list. -/
theorem starProduct_partition (P O : ι → R) (xs : List ι) (t : Nat) :
    starProduct P O xs = thresholdLow P O t xs + orderedBoxHigh P O t xs := by
  induction xs generalizing t with
  | nil => cases t <;> simp [starProduct, thresholdLow, orderedBoxHigh]
  | cons a xs ih =>
      cases t with
      | zero => simp [thresholdLow, orderedBoxHigh]
      | succ t =>
          simp only [starProduct, thresholdLow, orderedBoxHigh]
          linear_combination P a * ih (t + 1) + O a * ih t

/-- `none` is a star, `some false` is private, `some true` is ordinary.
The masks, like the physical input list, are written from right to left. -/
def orderedBoxMasks : Nat → Nat → List (List (Option Bool))
  | 0, k => [List.replicate k none]
  | _ + 1, 0 => []
  | t + 1, k + 1 =>
      (orderedBoxMasks (t + 1) k).map (some false :: ·) ++
        (orderedBoxMasks t k).map (some true :: ·)

/-- Evaluation of one explicitly specified ordered box. A mismatched mask
has value zero; the generated masks all have the correct length. -/
def boxValue (P O : ι → R) : List ι → List (Option Bool) → R
  | [], [] => 1
  | a :: xs, none :: ms => (P a + O a) * boxValue P O xs ms
  | a :: xs, some false :: ms => P a * boxValue P O xs ms
  | a :: xs, some true :: ms => O a * boxValue P O xs ms
  | _, _ => 0

theorem boxValue_stars (P O : ι → R) (xs : List ι) :
    boxValue P O xs (List.replicate xs.length none) = starProduct P O xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp [List.replicate_succ, boxValue, starProduct, ih]

/-- The recursive high term is the sum of the concrete box masks. -/
theorem orderedBoxHigh_eq_sum (P O : ι → R) (xs : List ι) (t : Nat) :
    orderedBoxHigh P O t xs =
      ((orderedBoxMasks t xs.length).map (boxValue P O xs)).sum := by
  induction xs generalizing t with
  | nil => cases t <;> simp [orderedBoxHigh, orderedBoxMasks, boxValue, starProduct]
  | cons a xs ih =>
      cases t with
      | zero =>
          simp only [orderedBoxHigh, orderedBoxMasks, List.map_singleton, List.sum_singleton]
          exact (boxValue_stars P O (a :: xs)).symm
      | succ t =>
          simp only [orderedBoxHigh, List.length_cons, orderedBoxMasks,
            List.map_append, List.sum_append, List.map_map, Function.comp_def,
            boxValue]
          rw [List.sum_map_mul_left, List.sum_map_mul_left, ← ih (t + 1), ← ih t]

/-- The full product is its low threshold term plus explicitly evaluated
ordered boxes. This does not require distinct positions or `t ≤ length`. -/
theorem starProduct_eq_low_add_box_sum (P O : ι → R) (xs : List ι) (t : Nat) :
    starProduct P O xs = thresholdLow P O t xs +
      ((orderedBoxMasks t xs.length).map (boxValue P O xs)).sum := by
  rw [← orderedBoxHigh_eq_sum]
  exact starProduct_partition P O xs t

/-- The mask has the required length and ordinary count; every star lies
in one suffix in reverse physical order. -/
theorem orderedBoxMasks_shape {t k : Nat} {ms : List (Option Bool)}
    (h : ms ∈ orderedBoxMasks t k) :
    ms.length = k ∧ ms.count (some true) = t ∧
      ∃ bs : List Bool, ∃ r : Nat, ms = bs.map some ++ List.replicate r none := by
  induction k generalizing t ms with
  | zero =>
    cases t with
    | zero =>
      simp only [orderedBoxMasks, List.replicate_zero, List.mem_singleton] at h
      subst ms
      exact ⟨rfl, rfl, [], 0, rfl⟩
    | succ t => simp [orderedBoxMasks] at h
  | succ k ih =>
    cases t with
    | zero =>
      simp only [orderedBoxMasks, List.mem_singleton] at h
      subst ms
      exact ⟨by simp, by simp [List.count_replicate], [], k+1, by simp⟩
    | succ t =>
      simp only [orderedBoxMasks, List.mem_append, List.mem_map] at h
      rcases h with ⟨xs, hx, rfl⟩ | ⟨xs, hx, rfl⟩
      · rcases ih hx with ⟨hlen, hcount, bs, r, hshape⟩
        refine ⟨by simp [hlen], by simpa using hcount, false :: bs, r, ?_⟩
        simp [hshape]
      · rcases ih hx with ⟨hlen, hcount, bs, r, hshape⟩
        refine ⟨by simp [hlen], by simp [hcount],
          true :: bs, r, ?_⟩
        simp [hshape]

/-- There is one mask per choice of the last `t` ordinary positions. -/
theorem orderedBoxMasks_length (t k : Nat) :
    (orderedBoxMasks t k).length = k.choose t := by
  induction k generalizing t with
  | zero => cases t <;> simp [orderedBoxMasks]
  | succ k ih =>
    cases t with
    | zero => simp [orderedBoxMasks]
    | succ t =>
      simp only [orderedBoxMasks, List.length_append, List.length_map, ih]
      simpa [Nat.choose_succ_succ] using Nat.add_comm (k.choose (t+1)) (k.choose t)

/-- The generated masks have no duplicates. -/
theorem orderedBoxMasks_nodup (t k : Nat) :
    (orderedBoxMasks t k).Nodup := by
  induction k generalizing t with
  | zero => cases t <;> simp [orderedBoxMasks]
  | succ k ih =>
    cases t with
    | zero => simp [orderedBoxMasks]
    | succ t =>
      simp only [orderedBoxMasks]
      refine List.nodup_append.mpr ⟨?_, ?_, ?_⟩
      · exact (ih (t+1)).map (by intro a b hab; simpa using hab)
      · exact (ih t).map (by intro a b hab; simpa using hab)
      · intro a ha b hb
        simp only [List.mem_map] at ha hb
        rcases ha with ⟨as, _, rfl⟩
        rcases hb with ⟨bs, _, rfl⟩
        simp

/-- For a nonzero threshold the last nonstar label is ordinary: the
physical star prefix ends exactly at the `t+1`-st selected ordinary factor
seen while scanning from right to left. -/
theorem orderedBoxMasks_strong_boundary {t k : Nat} {ms : List (Option Bool)}
    (h : ms ∈ orderedBoxMasks (t+1) k) :
    ∃ bs : List Bool, ∃ r : Nat,
      ms = bs.map some ++ [some true] ++ List.replicate r none ∧
      bs.count true = t := by
  induction k generalizing t ms with
  | zero => simp [orderedBoxMasks] at h
  | succ k ih =>
    simp only [orderedBoxMasks, List.mem_append, List.mem_map] at h
    rcases h with ⟨xs, hx, rfl⟩ | ⟨xs, hx, rfl⟩
    · rcases ih hx with ⟨bs, r, hshape, hcount⟩
      exact ⟨false :: bs, r, by simp [hshape], by simpa using hcount⟩
    · cases t with
      | zero =>
        simp only [orderedBoxMasks, List.mem_singleton] at hx
        subst xs
        exact ⟨[], k, by simp, rfl⟩
      | succ t =>
        rcases ih hx with ⟨bs, r, hshape, hcount⟩
        exact ⟨true :: bs, r, by simp [hshape], by simp [hcount]⟩


end ThinMatrix.OrderedBoxes


open Finset

namespace ThinMatrix.PowersetBridge

variable {ι R : Type*} [DecidableEq ι] [CommRing R]

def low (s : Finset ι) (t : ℕ) (P O : ι → R) : R :=
  ∑ B ∈ s.powerset.filter (fun B => B.card < t),
    (∏ a ∈ B, O a) * ∏ a ∈ s \ B, P a

@[simp] theorem low_zero (s : Finset ι) (P O : ι → R) : low s 0 P O = 0 := by
  simp [low]

@[simp] theorem low_empty_succ (t : ℕ) (P O : ι → R) : low ∅ (t + 1) P O = 1 := by
  simp [low, filter_singleton]

theorem low_insert_succ (s : Finset ι) (a : ι) (ha : a ∉ s)
    (t : ℕ) (P O : ι → R) :
    low (insert a s) (t + 1) P O =
      P a * low s (t + 1) P O + O a * low s t P O := by
  simp only [low, sum_filter]
  rw [sum_powerset_insert ha, mul_sum, mul_sum]
  congr 1
  · apply sum_congr rfl
    intro B hB
    have haB : a ∉ B := notMem_of_mem_powerset_of_notMem hB ha
    have haDiff : a ∉ s \ B := fun h => ha (mem_sdiff.mp h).1
    rw [insert_sdiff_of_notMem s haB, prod_insert haDiff]
    split_ifs <;> ring
  · apply sum_congr rfl
    intro B hB
    have haB : a ∉ B := notMem_of_mem_powerset_of_notMem hB ha
    rw [card_insert_of_notMem haB, insert_sdiff_insert,
      sdiff_insert_of_notMem ha, prod_insert haB]
    simp only [Nat.add_lt_add_iff_right]
    split_ifs <;> ring

end ThinMatrix.PowersetBridge

namespace ThinMatrix.OrderedBoxes

universe u v
variable {ι : Type v} {R : Type u} [CommRing R]

theorem starProduct_eq_list_prod (P O : ι → R) (xs : List ι) :
    starProduct P O xs = (xs.map (fun i => P i + O i)).prod := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp [starProduct, ih]

theorem starProduct_eq_finset_prod [DecidableEq ι]
    (P O : ι → R) (xs : List ι) (hxs : xs.Nodup) :
    starProduct P O xs = ∏ i ∈ xs.toFinset, (P i + O i) := by
  rw [List.prod_toFinset _ hxs, starProduct_eq_list_prod]

end ThinMatrix.OrderedBoxes

namespace ThinMatrix.PowersetBridge

variable {ι R : Type*} [DecidableEq ι] [CommRing R]

theorem low_toFinset_eq_thresholdLow (xs : List ι) (hxs : xs.Nodup)
    (t : ℕ) (P O : ι → R) :
    low xs.toFinset t P O = OrderedBoxes.thresholdLow P O t xs := by
  induction xs generalizing t with
  | nil =>
      cases t <;> simp [OrderedBoxes.thresholdLow]
  | cons a xs ih =>
      have ha : a ∉ xs.toFinset := by simpa using hxs.notMem
      cases t with
      | zero => simp [OrderedBoxes.thresholdLow]
      | succ t =>
          rw [List.toFinset_cons, low_insert_succ xs.toFinset a ha t P O,
            ih hxs.of_cons (t + 1), ih hxs.of_cons t]
          rfl


end ThinMatrix.PowersetBridge

namespace ThinMatrix.PowersetBridge

variable {ι R : Type*} [DecidableEq ι] [CommRing R]

/-- The ordinary expansion terms of degree at least `t`. -/
def high (s : Finset ι) (t : ℕ) (P O : ι → R) : R :=
  ∑ B ∈ s.powerset.filter (fun B => t ≤ B.card),
    (∏ a ∈ B, O a) * ∏ a ∈ s \ B, P a

theorem product_eq_low_add_high (s : Finset ι) (t : ℕ) (P O : ι → R) :
    (∏ i ∈ s, (P i + O i)) = low s t P O + high s t P O := by
  calc
    (∏ i ∈ s, (P i + O i)) =
        ∑ B ∈ s.powerset, (∏ a ∈ B, O a) * ∏ a ∈ s \ B, P a := by
          simpa only [add_comm] using Finset.prod_add O P s
    _ = low s t P O + high s t P O := by
          symm
          simpa only [low, high, Nat.not_lt] using
            Finset.sum_filter_add_sum_filter_not s.powerset
              (fun B => B.card < t)
              (fun B => (∏ a ∈ B, O a) * ∏ a ∈ s \ B, P a)

/-- The high-degree powerset sum equals the explicitly evaluated boxes.
The list `xs` is in reverse physical order. -/
theorem high_toFinset_eq_box_sum (xs : List ι) (hxs : xs.Nodup)
    (t : ℕ) (P O : ι → R) :
    high xs.toFinset t P O =
      ((OrderedBoxes.orderedBoxMasks t xs.length).map
        (OrderedBoxes.boxValue P O xs)).sum := by
  have hp := OrderedBoxes.starProduct_eq_low_add_box_sum P O xs t
  rw [OrderedBoxes.starProduct_eq_finset_prod P O xs hxs,
    ← low_toFinset_eq_thresholdLow xs hxs t P O] at hp
  have hs := product_eq_low_add_high xs.toFinset t P O
  linear_combination hp - hs

/-- Ordered finite-index high-degree box decomposition. The natural
physical order is `0,...,k-1`, so the mask scan uses its reverse. -/
theorem fin_high_eq_box_sum (k t : ℕ) (P O : Fin k → R) :
    high Finset.univ t P O =
      ((OrderedBoxes.orderedBoxMasks t k).map
        (OrderedBoxes.boxValue P O (List.finRange k).reverse)).sum := by
  have hn : (List.finRange k).reverse.Nodup :=
    List.nodup_reverse.mpr (List.nodup_finRange k)
  simpa using high_toFinset_eq_box_sum (List.finRange k).reverse hn t P O

/-- Full finite-index product partition into the low ordinary expansion
and the last-`t` ordinary boxes. -/
theorem fin_product_eq_low_add_box_sum (k t : ℕ) (P O : Fin k → R) :
    (∏ i, (P i + O i)) = low Finset.univ t P O +
      ((OrderedBoxes.orderedBoxMasks t k).map
        (OrderedBoxes.boxValue P O (List.finRange k).reverse)).sum := by
  rw [← fin_high_eq_box_sum]
  exact product_eq_low_add_high Finset.univ t P O

end ThinMatrix.PowersetBridge


namespace ThinMatrix.TensorContraction

open scoped BigOperators
open Finset Polynomial

universe u v w
variable {R : Type u} [CommRing R]
variable {A : Type v} {B : Type w} [Fintype A] [Fintype B]

/-- The finite coefficient moments in the binomial low residual. -/
def lowMoments (k t : ℕ) (P I : Fin k → R) : R :=
  ∑ j ∈ Finset.range t, residualWeight k t j *
    ∑ J ∈ (Finset.univ : Finset (Fin k)).powersetCard j,
      (∏ i ∈ J, I i) * ∏ i ∈ Jᶜ, P i

/-- Explicit boxes, indexed by the last `t` ordinary positions.  The list
is scanned in reverse physical order. -/
def highBoxes (k t : ℕ) (P I : Fin k → R) : R :=
  ((OrderedBoxes.orderedBoxMasks t k).map
    (OrderedBoxes.boxValue P (fun i => I i - P i) (List.finRange k).reverse)).sum

/-- The A11 residual is exactly the low ordinary powerset expansion. -/
theorem lowMoments_eq_low (k t : ℕ) (ht : t ≤ k) (P I : Fin k → R) :
    lowMoments k t P I = PowersetBridge.low Finset.univ t P (fun i => I i-P i) := by
  simpa only [lowMoments, residualWeight, PowersetBridge.low,
    Finset.card_univ, Fintype.card_fin, ← Finset.compl_eq_univ_sdiff] using
    BinomialPartition.finite_binomial_transform
      (Finset.univ : Finset (Fin k)) t (by simpa using ht) P I

/-- Complete finite residual-plus-box identity.  It allows arbitrary ring
entries and any threshold `t ≤ k`, including the empty low residual. -/
theorem full_product_eq_lowMoments_add_highBoxes (k t : ℕ) (ht : t ≤ k)
    (P I : Fin k → R) :
    (∏ i, I i) = lowMoments k t P I + highBoxes k t P I := by
  rw [lowMoments_eq_low k t ht]
  simpa only [highBoxes, add_sub_cancel] using
    PowersetBridge.fin_product_eq_low_add_box_sum k t P (fun i => I i-P i)

/-- The paper uses `k=2m` inner physical positions. -/
theorem full_two_half_product (m t : ℕ) (ht : t ≤ 2*m)
    (P I : Fin (2*m) → R) :
    (∏ i, I i) = lowMoments (2*m) t P I + highBoxes (2*m) t P I :=
  full_product_eq_lowMoments_add_highBoxes (2*m) t ht P I

theorem bilinear_add (X : A → R) (Y : B → R) (K L : A → B → R) :
    bilinear X Y (fun a b => K a b+L a b) = bilinear X Y K+bilinear X Y L := by
  simp only [bilinear, mul_add, Finset.sum_add_distrib]

theorem bilinear_list_sum {κ : Type*} (xs : List κ)
    (X : A → R) (Y : B → R) (K : κ → A → B → R) :
    bilinear X Y (fun a b => (xs.map (fun c => K c a b)).sum) =
      (xs.map (fun c => bilinear X Y (K c))).sum := by
  induction xs with
  | nil => simp [bilinear]
  | cons c xs ih => simp only [List.map_cons, List.sum_cons, bilinear_add, ih]

/-- Full finite contraction: arbitrary raw arrays, the exact binomial
low residual, and the explicit ordered high boxes. -/
theorem residual_plus_boxes_contraction (k t : ℕ) (ht : t ≤ k)
    (X : A → R) (Y : B → R) (P I : Fin k → A → B → R) :
    bilinear X Y (fun a b => ∏ i, I i a b) =
      (∑ j ∈ Finset.range t, residualWeight k t j *
        bilinear X Y (fun a b =>
          ∑ J ∈ (Finset.univ : Finset (Fin k)).powersetCard j,
            (∏ i ∈ J, I i a b) * ∏ i ∈ Jᶜ, P i a b)) +
      ((OrderedBoxes.orderedBoxMasks t k).map (fun mask =>
        bilinear X Y (fun a b => OrderedBoxes.boxValue
          (fun i => P i a b) (fun i => I i a b-P i a b)
          (List.finRange k).reverse mask))).sum := by
  have hp (a : A) (b : B) :=
    full_product_eq_lowMoments_add_highBoxes k t ht (fun i => P i a b) (fun i => I i a b)
  simp_rw [hp]
  rw [bilinear_add]
  unfold lowMoments highBoxes
  rw [bilinear_sum, bilinear_list_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  exact bilinear_scale X Y _ _

end ThinMatrix.TensorContraction

namespace ThinMatrix.TensorContraction

open scoped BigOperators
open Finset Polynomial

universe u v w
variable {R : Type u} [CommRing R]
variable {A : Type v} {B : Type w} [Fintype A] [Fintype B]

/-- The polynomial query before applying the low binomial functional.
Raw-array coefficients are constant in this separate formal variable. -/
noncomputable def pencilQuery (k : ℕ) (X : A → R) (Y : B → R)
    (P I : Fin k → A → B → R) : Polynomial R :=
  bilinear (fun a => Polynomial.C (X a)) (fun b => Polynomial.C (Y b))
    (fun a b => ∏ i,
      (Polynomial.C (P i a b)+Polynomial.X*Polynomial.C (I i a b)))

/-- Exact aligned local pencil over the separate formal polynomial
variable.  It requires no inverse or characteristic assumption. -/
theorem aligned_polynomial_pencil (x₁ x₂ p₁ p₂ s w : R) :
    Polynomial.C ((-x₁-x₂)*(2*s))+
        Polynomial.X*Polynomial.C (2*p₁*s+p₂*w) =
      (Polynomial.C (-x₁-x₂)+Polynomial.X*Polynomial.C p₁)*Polynomial.C (2*s)+
        Polynomial.X*Polynomial.C p₂*Polynomial.C w := by
  simp only [map_mul, map_add]
  ring

/-- Exact channel formula for the genuine aligned polynomial query.
There is one common physical set `C` and one global `X^|C|` shift. -/
theorem aligned_pencil_channel_contraction (k : ℕ)
    (Xraw : A → R) (Yraw : B → R)
    (x₁ x₂ p₁ p₂ : Fin k → A → R) (s w : Fin k → B → R) :
    pencilQuery k Xraw Yraw
      (fun i a b => (-x₁ i a-x₂ i a)*(2*s i b))
      (fun i a b => 2*p₁ i a*s i b+p₂ i a*w i b) =
    ∑ C ∈ (Finset.univ : Finset (Fin k)).powerset,
      Polynomial.X ^ C.card *
        leftCache Finset.univ C (fun a => Polynomial.C (Xraw a))
          (fun i a => Polynomial.C (-x₁ i a-x₂ i a)+Polynomial.X*Polynomial.C (p₁ i a))
          (fun i a => Polynomial.C (p₂ i a)) *
        rightCache Finset.univ C (fun b => Polynomial.C (Yraw b))
          (fun i b => Polynomial.C (2*s i b)) (fun i b => Polynomial.C (w i b)) := by
  unfold pencilQuery
  simp_rw [aligned_polynomial_pencil]
  exact polynomial_channel_contraction Finset.univ _ _ _ _ _ _

/-- The low aligned polynomial query reads `j-|C|` only for `|C|<t`.
The same set `C` indexes both input caches. -/
theorem aligned_weighted_low_channel_formula (k t : ℕ)
    (Xraw : A → R) (Yraw : B → R)
    (x₁ x₂ p₁ p₂ : Fin k → A → R) (s w : Fin k → B → R) :
    weightedLow k t (pencilQuery k Xraw Yraw
      (fun i a b => (-x₁ i a-x₂ i a)*(2*s i b))
      (fun i a b => 2*p₁ i a*s i b+p₂ i a*w i b)) =
      ∑ C ∈ (Finset.univ : Finset (Fin k)).powerset.filter (fun C => C.card < t),
        ∑ j ∈ Finset.range t,
          if C.card ≤ j then residualWeight k t j *
            (leftCache Finset.univ C (fun a => Polynomial.C (Xraw a))
                (fun i a => Polynomial.C (-x₁ i a-x₂ i a)+Polynomial.X*Polynomial.C (p₁ i a))
                (fun i a => Polynomial.C (p₂ i a)) *
              rightCache Finset.univ C (fun b => Polynomial.C (Yraw b))
                (fun i b => Polynomial.C (2*s i b))
                (fun i b => Polynomial.C (w i b))).coeff (j-C.card)
          else 0 := by
  unfold pencilQuery
  simp_rw [aligned_polynomial_pencil]
  exact weighted_low_uses_small_channel_sets Finset.univ _ _ _ _ _ _ k t

end ThinMatrix.TensorContraction



open scoped BigOperators

namespace ThinMatrix.PencilCoefficients

theorem pencil_expansion {α R : Type*} [DecidableEq α] [CommSemiring R]
    (s : Finset α) (P I : α → R) :
    (∏ i ∈ s, (Polynomial.C (P i) + Polynomial.X * Polynomial.C (I i))) =
      ∑ J ∈ s.powerset,
        Polynomial.C ((∏ i ∈ J, I i) * (∏ i ∈ s \ J, P i)) *
          Polynomial.X ^ J.card := by
  classical
  simp_rw [add_comm (Polynomial.C (P _))]
  rw [Finset.prod_add]
  refine Finset.sum_congr rfl ?_
  intro J hJ
  have hI : (∏ i ∈ J, (Polynomial.X : Polynomial R) * Polynomial.C (I i)) =
      Polynomial.X ^ J.card * Polynomial.C (∏ i ∈ J, I i) := by
    simp only [Finset.prod_mul_distrib, Finset.prod_const, map_prod]
  rw [hI]
  simp only [map_prod, map_mul]
  ring

theorem pencil_coefficient {α R : Type*} [DecidableEq α] [CommSemiring R]
    (s : Finset α) (P I : α → R) (j : ℕ) :
    (∏ i ∈ s, (Polynomial.C (P i) + Polynomial.X * Polynomial.C (I i))).coeff j =
      ∑ J ∈ s.powersetCard j,
        (∏ i ∈ J, I i) * (∏ i ∈ s \ J, P i) := by
  classical
  rw [pencil_expansion]
  simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
  rw [Finset.powersetCard_eq_filter, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro J hJ
  simp [eq_comm]

theorem coefficient_raw_contraction {α β R : Type*} [CommSemiring R]
    (a : Finset α) (b : Finset β) (A : α → R) (B : β → R)
    (K : α → β → Polynomial R) (j : ℕ) :
    (∑ u ∈ a, ∑ v ∈ b,
      Polynomial.C (A u) * Polynomial.C (B v) * K u v).coeff j =
      ∑ u ∈ a, ∑ v ∈ b, A u * B v * (K u v).coeff j := by
  classical
  simp only [Polynomial.finsetSum_coeff, ← Polynomial.C_mul,
    Polynomial.coeff_C_mul]

theorem coefficient_contracted_pencil {α β ι R : Type*}
    [DecidableEq ι] [CommSemiring R]
    (a : Finset α) (b : Finset β) (s : Finset ι)
    (A : α → R) (B : β → R) (P I : α → β → ι → R) (j : ℕ) :
    (∑ u ∈ a, ∑ v ∈ b,
      Polynomial.C (A u) * Polynomial.C (B v) *
        ∏ i ∈ s, (Polynomial.C (P u v i) +
          Polynomial.X * Polynomial.C (I u v i))).coeff j =
      ∑ u ∈ a, ∑ v ∈ b, A u * B v *
        ∑ J ∈ s.powersetCard j,
          (∏ i ∈ J, I u v i) * (∏ i ∈ s \ J, P u v i) := by
  rw [coefficient_raw_contraction]
  simp_rw [pencil_coefficient]

end ThinMatrix.PencilCoefficients

namespace ThinMatrix.TensorContraction

open scoped BigOperators
open Finset Polynomial

universe u v w
variable {R : Type u} [CommRing R]
variable {A : Type v} {B : Type w} [Fintype A] [Fintype B]

/-- Polynomial coefficient extraction commutes with contraction of
arbitrary raw arrays that are constant in the formal variable. -/
theorem pencilQuery_coefficient (k j : ℕ) (X : A → R) (Y : B → R)
    (P I : Fin k → A → B → R) :
    (pencilQuery k X Y P I).coeff j =
      bilinear X Y (fun a b =>
        ∑ J ∈ (Finset.univ : Finset (Fin k)).powersetCard j,
          (∏ i ∈ J, I i a b) * ∏ i ∈ Jᶜ, P i a b) := by
  simpa only [pencilQuery, bilinear, ← Finset.compl_eq_univ_sdiff] using
    PencilCoefficients.coefficient_contracted_pencil
      Finset.univ Finset.univ Finset.univ X Y
      (fun a b i => P i a b) (fun a b i => I i a b) j

/-- The polynomial weighted-low query is exactly the contracted A11
residual, rather than a separate, unconnected coefficient formula. -/
theorem weightedLow_pencilQuery (k t : ℕ) (X : A → R) (Y : B → R)
    (P I : Fin k → A → B → R) :
    weightedLow k t (pencilQuery k X Y P I) =
      bilinear X Y (fun a b => lowMoments k t (fun i => P i a b) (fun i => I i a b)) := by
  unfold weightedLow lowMoments
  simp_rw [pencilQuery_coefficient]
  rw [bilinear_sum]
  apply Finset.sum_congr rfl
  intro j hj
  exact (bilinear_scale X Y _ _).symm

/-- The complete finite algebraic query identity: the low polynomial
functional plus the concrete high boxes equals the full tensor product
contracted against arbitrary raw input arrays. -/
theorem full_query_eq_weightedLow_add_boxes (k t : ℕ) (ht : t ≤ k)
    (X : A → R) (Y : B → R) (P I : Fin k → A → B → R) :
    bilinear X Y (fun a b => ∏ i, I i a b) =
      weightedLow k t (pencilQuery k X Y P I) +
      ((OrderedBoxes.orderedBoxMasks t k).map (fun mask =>
        bilinear X Y (fun a b => OrderedBoxes.boxValue
          (fun i => P i a b) (fun i => I i a b-P i a b)
          (List.finRange k).reverse mask))).sum := by
  rw [weightedLow_pencilQuery]
  have hp (a : A) (b : B) :=
    full_product_eq_lowMoments_add_highBoxes k t ht (fun i => P i a b) (fun i => I i a b)
  simp_rw [hp]
  rw [bilinear_add]
  unfold highBoxes
  rw [bilinear_list_sum]

/-- The canonical aligned contraction is exactly its shared-factor low
query plus the ordered high boxes, on `2m` physical positions. -/
theorem aligned_full_query_eq_weightedLow_add_boxes (m t : ℕ) (ht : t ≤ 2*m)
    (Xraw : A → R) (Yraw : B → R)
    (x₁ x₂ p₁ p₂ : Fin (2*m) → A → R) (s w : Fin (2*m) → B → R) :
    bilinear Xraw Yraw (fun a b => ∏ i, (2*p₁ i a*s i b+p₂ i a*w i b)) =
      weightedLow (2*m) t (pencilQuery (2*m) Xraw Yraw
        (fun i a b => (-x₁ i a-x₂ i a)*(2*s i b))
        (fun i a b => 2*p₁ i a*s i b+p₂ i a*w i b)) +
      ((OrderedBoxes.orderedBoxMasks t (2*m)).map (fun mask =>
        bilinear Xraw Yraw (fun a b => OrderedBoxes.boxValue
          (fun i => (-x₁ i a-x₂ i a)*(2*s i b))
          (fun i => (2*p₁ i a*s i b+p₂ i a*w i b)-(-x₁ i a-x₂ i a)*(2*s i b))
          (List.finRange (2*m)).reverse mask))).sum := by
  exact full_query_eq_weightedLow_add_boxes (2*m) t ht Xraw Yraw _ _

end ThinMatrix.TensorContraction

#print axioms ThinMatrix.TensorContraction.aligned_tensor_contraction
#print axioms ThinMatrix.TensorContraction.polynomial_channel_contraction
#print axioms ThinMatrix.TensorContraction.polynomial_channel_coefficient
#print axioms ThinMatrix.TensorContraction.weighted_low_uses_small_channel_sets
#print axioms ThinMatrix.BinomialPartition.finite_binomial_transform
#print axioms ThinMatrix.OrderedBoxes.orderedBoxMasks_shape
#print axioms ThinMatrix.OrderedBoxes.orderedBoxMasks_strong_boundary
#print axioms ThinMatrix.OrderedBoxes.orderedBoxMasks_length
#print axioms ThinMatrix.OrderedBoxes.orderedBoxMasks_nodup
#print axioms ThinMatrix.PowersetBridge.fin_high_eq_box_sum
#print axioms ThinMatrix.TensorContraction.full_product_eq_lowMoments_add_highBoxes
#print axioms ThinMatrix.TensorContraction.residual_plus_boxes_contraction
#print axioms ThinMatrix.TensorContraction.aligned_weighted_low_channel_formula
#print axioms ThinMatrix.TensorContraction.pencilQuery_coefficient
#print axioms ThinMatrix.TensorContraction.weightedLow_pencilQuery
#print axioms ThinMatrix.TensorContraction.full_query_eq_weightedLow_add_boxes
#print axioms ThinMatrix.TensorContraction.aligned_full_query_eq_weightedLow_add_boxes

namespace ThinMatrix.TensorContraction

open scoped BigOperators
open Finset Polynomial

universe u v w
variable {R : Type u} [CommRing R]
variable {A : Type v} {B : Type w} [Fintype A] [Fintype B]

/-- Fixed outside ordinary factors may be absorbed into the arbitrary
raw arrays before applying the inner-coordinate identities. -/
theorem bilinear_absorb_outside (X : A → R) (Y : B → R)
    (f : A → R) (g : B → R) (K : A → B → R) :
    bilinear X Y (fun a b => f a*g b*K a b) =
      bilinear (fun a => X a*f a) (fun b => Y b*g b) K := by
  unfold bilinear
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  ring

/-- Label four is exactly the canonical private form. -/
theorem aligned_private_label (x₁ x₂ p₁ p₂ s v w : R) :
    alignedLeft x₁ x₂ p₁ p₂ 4 * alignedRight s v w 4 = (-x₁-x₂)*(2*s) := by
  simp [alignedLeft, alignedRight]

/-- The four ordinary labels sum exactly to `I-P`, as used in the
ordered-box partition. -/
theorem aligned_ordinary_label_sum (x₁ x₂ p₁ p₂ s v w : R) :
    (∑ l : Fin 4,
      alignedLeft x₁ x₂ p₁ p₂ l.castSucc * alignedRight s v w l.castSucc) =
      (2*p₁*s+p₂*w)-(-x₁-x₂)*(2*s) := by
  simp [alignedLeft, alignedRight, Fin.sum_univ_succ]
  ring

end ThinMatrix.TensorContraction

#print axioms ThinMatrix.TensorContraction.bilinear_absorb_outside
#print axioms ThinMatrix.TensorContraction.aligned_ordinary_label_sum

namespace ThinMatrix.TensorContraction

open scoped BigOperators
open Finset Polynomial

universe u v w
variable {R : Type u} [CommRing R]
variable {A : Type v} {B : Type w} [Fintype A] [Fintype B]

/-- Complete aligned query partition with the high ordinary factor
spelled out as the four canonical rank-one ordinary labels. -/
theorem aligned_full_query_eq_weightedLow_add_ordinary_boxes
    (m t : ℕ) (ht : t ≤ 2*m) (Xraw : A → R) (Yraw : B → R)
    (x₁ x₂ p₁ p₂ : Fin (2*m) → A → R) (s v w : Fin (2*m) → B → R) :
    bilinear Xraw Yraw (fun a b => ∏ i, (2*p₁ i a*s i b+p₂ i a*w i b)) =
      weightedLow (2*m) t (pencilQuery (2*m) Xraw Yraw
        (fun i a b => (-x₁ i a-x₂ i a)*(2*s i b))
        (fun i a b => 2*p₁ i a*s i b+p₂ i a*w i b)) +
      ((OrderedBoxes.orderedBoxMasks t (2*m)).map (fun mask =>
        bilinear Xraw Yraw (fun a b => OrderedBoxes.boxValue
          (fun i => (-x₁ i a-x₂ i a)*(2*s i b))
          (fun i => ∑ l : Fin 4,
            alignedLeft (x₁ i a) (x₂ i a) (p₁ i a) (p₂ i a) l.castSucc *
              alignedRight (s i b) (v i b) (w i b) l.castSucc)
          (List.finRange (2*m)).reverse mask))).sum := by
  simpa only [aligned_ordinary_label_sum] using
    aligned_full_query_eq_weightedLow_add_boxes m t ht Xraw Yraw x₁ x₂ p₁ p₂ s w

end ThinMatrix.TensorContraction

#print axioms ThinMatrix.TensorContraction.aligned_full_query_eq_weightedLow_add_ordinary_boxes



/-! Exact expansion only of the selected ordinary positions in a box.
Star factors remain arbitrary; they are not included in the label domain. -/

namespace ThinMatrix.BoxOrdinaryExpansion

universe u v w
variable {ι : Type v} {R : Type u} [CommRing R]

/-- The selected ordinary positions, as opposed to star or private positions. -/
def ordinaryPositions [Fintype ι] [DecidableEq ι]
    (mask : ι → Option Bool) : Finset ι :=
  Finset.univ.filter (fun i => mask i = some true)

/-- Ordinary factor is set to one, leaving the fixed star/private kernel. -/
def fixedFactor (mask : ι → Option Bool) (I P : ι → R) (i : ι) : R :=
  match mask i with
  | none => I i
  | some false => P i
  | some true => 1

/-- One box with arbitrary stars, private factors, and ordinary factors. -/
def boxFactor (mask : ι → Option Bool) (I P O : ι → R) (i : ι) : R :=
  match mask i with
  | none => I i
  | some false => P i
  | some true => O i

def boxKernel [Fintype ι] (mask : ι → Option Bool) (I P O : ι → R) : R :=
  ∏ i, boxFactor mask I P O i

theorem boxKernel_split [Fintype ι] [DecidableEq ι]
    (mask : ι → Option Bool) (I P O : ι → R) :
    boxKernel mask I P O =
      (∏ i, fixedFactor mask I P i) * ∏ i ∈ ordinaryPositions mask, O i := by
  have hlocal (i : ι) : boxFactor mask I P O i =
      fixedFactor mask I P i * (if mask i = some true then O i else 1) := by
    cases hm : mask i with
    | none => simp [boxFactor, fixedFactor, hm]
    | some b => cases b <;> simp [boxFactor, fixedFactor, hm]
  simp only [boxKernel, hlocal, Finset.prod_mul_distrib]
  congr 1
  rw [Finset.prod_ite]
  simp [ordinaryPositions]

/-- Each selected ordinary factor chooses one of four common labels.
Stars and private positions contribute only to the fixed kernel. -/
theorem boxKernel_four_term_expansion [Fintype ι] [DecidableEq ι]
    (mask : ι → Option Bool) (I P : ι → R) (A B : ι → Fin 4 → R) :
    boxKernel mask I P (fun i => ∑ l, A i l * B i l) =
      ∑ label : (ordinaryPositions mask) → Fin 4,
        (∏ i, fixedFactor mask I P i) *
          ((∏ i : ordinaryPositions mask, A i (label i)) *
            ∏ i : ordinaryPositions mask, B i (label i)) := by
  calc
    boxKernel mask I P (fun i => ∑ l, A i l * B i l) =
        (∏ i, fixedFactor mask I P i) *
          ∏ i : ordinaryPositions mask, ∑ l, A i l * B i l := by
            rw [boxKernel_split]
            congr 1
            exact (Finset.prod_coe_sort (ordinaryPositions mask)
              (fun i => ∑ l, A i l * B i l)).symm
    _ = (∏ i, fixedFactor mask I P i) *
        ∑ label : (ordinaryPositions mask) → Fin 4,
          ∏ i : ordinaryPositions mask, A i (label i) * B i (label i) := by
            rw [Fintype.prod_sum]
    _ = _ := by
      simp only [Finset.prod_mul_distrib, Finset.mul_sum]

/-- In particular private factors may be rank one as well. The ordinary
label assignments are still indexed only by ordinary positions. -/
theorem boxKernel_private_rankone_four_term_expansion [Fintype ι] [DecidableEq ι]
    (mask : ι → Option Bool) (I pA pB : ι → R) (A B : ι → Fin 4 → R) :
    boxKernel mask I (fun i => pA i * pB i) (fun i => ∑ l, A i l * B i l) =
      ∑ label : (ordinaryPositions mask) → Fin 4,
        (∏ i, fixedFactor mask I (fun j => pA j * pB j) i) *
          ((∏ i : ordinaryPositions mask, A i (label i)) *
            ∏ i : ordinaryPositions mask, B i (label i)) :=
  boxKernel_four_term_expansion mask I (fun i => pA i * pB i) A B

theorem ordinary_label_count [Fintype ι] [DecidableEq ι]
    (mask : ι → Option Bool) :
    Fintype.card ((ordinaryPositions mask) → Fin 4) =
      4 ^ (ordinaryPositions mask).card := by
  simp

/-- List evaluator with arbitrary stars. Its specialization to `I=P+O`
is the ordered box evaluator from the partition file. -/
def listBoxValue (I P O : ι → R) : List ι → List (Option Bool) → R
  | [], [] => 1
  | a :: xs, none :: ms => I a * listBoxValue I P O xs ms
  | a :: xs, some false :: ms => P a * listBoxValue I P O xs ms
  | a :: xs, some true :: ms => O a * listBoxValue I P O xs ms
  | _, _ => 0

/-- The recursive list box is the finite-index masked product. `getD none`
does not affect any position because the two lists have the same length. -/
theorem listBoxValue_eq_boxKernel (I P O : ι → R)
    (xs : List ι) (ms : List (Option Bool)) (hlen : xs.length = ms.length) :
    listBoxValue I P O xs ms =
      boxKernel (fun i : Fin xs.length => ms[i.val]?.getD none)
        (fun i => I xs[i]) (fun i => P xs[i]) (fun i => O xs[i]) := by
  induction xs generalizing ms with
  | nil =>
      cases ms with
      | nil => simp [listBoxValue, boxKernel]
      | cons m ms => simp at hlen
  | cons a xs ih =>
      cases ms with
      | nil => simp at hlen
      | cons m ms =>
          have ht : xs.length = ms.length := Nat.succ.inj hlen
          cases m with
          | none =>
              simpa [listBoxValue, boxKernel, Fin.prod_univ_succ, boxFactor]
                using congrArg (I a * ·) (ih ms ht)
          | some b =>
              cases b with
              | false =>
                  simpa [listBoxValue, boxKernel, Fin.prod_univ_succ, boxFactor]
                    using congrArg (P a * ·) (ih ms ht)
              | true =>
                  simpa [listBoxValue, boxKernel, Fin.prod_univ_succ, boxFactor]
                    using congrArg (O a * ·) (ih ms ht)

end ThinMatrix.BoxOrdinaryExpansion


namespace ThinMatrix.OrderedBoxes

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]

/-- A star allows all five labels; a private factor uses label four;
an ordinary factor allows precisely the other four labels. -/
def full5Allowed : Option Bool → Finset (Fin 5)
  | none => Finset.univ
  | some false => {4}
  | some true => Finset.univ.erase 4

/-- Private, ordinary, and star scalar factors. -/
def full5LocalFactor (tag : Option Bool) (f : Fin 5 → R) : R :=
  match tag with
  | none => f 4 + ∑ l : Fin 4, f l.castSucc
  | some false => f 4
  | some true => ∑ l : Fin 4, f l.castSucc

lemma full5_ordinary_sum (f : Fin 5 → R) :
    (∑ l ∈ Finset.univ.erase (4 : Fin 5), f l) =
      ∑ l : Fin 4, f l.castSucc := by
  apply add_right_cancel (b := f 4)
  calc
    (∑ l ∈ Finset.univ.erase (4 : Fin 5), f l) + f 4 =
        ∑ l : Fin 5, f l := Finset.sum_erase_add Finset.univ f (Finset.mem_univ _)
    _ = (∑ l : Fin 4, f l.castSucc) + f 4 := by
      simpa using Fin.sum_univ_castSucc f

lemma full5_sum_allowed (tag : Option Bool) (f : Fin 5 → R) :
    (∑ l ∈ full5Allowed tag, f l) = full5LocalFactor tag f := by
  cases tag with
  | none =>
    simp only [full5Allowed, full5LocalFactor]
    rw [Fin.sum_univ_castSucc]
    exact add_comm _ _
  | some b =>
    cases b with
    | false => simp [full5Allowed, full5LocalFactor]
    | true => exact full5_ordinary_sum f

/-- Compatible full-five label assignments as an explicit finite set. -/
def full5CompatibleLabels (mask : ι → Option Bool) : Finset (ι → Fin 5) :=
  Finset.univ.filter (fun labels => ∀ i, labels i ∈ full5Allowed (mask i))

lemma full5CompatibleLabels_eq_piFinset (mask : ι → Option Bool) :
    full5CompatibleLabels mask = Fintype.piFinset (fun i => full5Allowed (mask i)) := by
  ext labels
  simp [full5CompatibleLabels, Fintype.mem_piFinset]

/-- Each box product is the sum of exactly its compatible five-label
products, in an arbitrary commutative ring. -/
theorem full5_compatible_expansion (mask : ι → Option Bool) (F : ι → Fin 5 → R) :
    (∏ i, full5LocalFactor (mask i) (F i)) =
      ∑ labels ∈ full5CompatibleLabels mask, ∏ i, F i (labels i) := by
  calc
    (∏ i, full5LocalFactor (mask i) (F i)) =
        ∏ i, ∑ l ∈ full5Allowed (mask i), F i l := by
      apply Finset.prod_congr rfl
      intro i _
      exact (full5_sum_allowed (mask i) (F i)).symm
    _ = ∑ labels ∈ Fintype.piFinset (fun i => full5Allowed (mask i)),
        ∏ i, F i (labels i) := Finset.prod_univ_sum _ _
    _ = ∑ labels ∈ full5CompatibleLabels mask, ∏ i, F i (labels i) := by
      rw [full5CompatibleLabels_eq_piFinset]

/-- The same expansion with the allowed-label filter displayed inline. -/
theorem full5_compatible_expansion_filter (mask : ι → Option Bool) (F : ι → Fin 5 → R) :
    (∏ i, full5LocalFactor (mask i) (F i)) =
      ∑ labels ∈ Finset.univ.filter (fun labels : ι → Fin 5 =>
        ∀ i, labels i ∈ full5Allowed (mask i)), ∏ i, F i (labels i) :=
  full5_compatible_expansion mask F


end ThinMatrix.OrderedBoxes



namespace ThinMatrix.OrderedBoxes

/-- The physical positions carrying an ordinary factor in a mask. -/
def ordinaryPositions (ms : List (Option Bool)) : Finset (Fin ms.length) :=
  Finset.univ.filter (fun i => ms[i] = some true)

lemma mask_count_eq_sum_fin (xs : List (Option Bool)) :
    xs.count (some true) = ∑ i : Fin xs.length, if xs[i] = some true then 1 else 0 := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    change List.count (some true) (x :: xs) =
      ∑ i : Fin (xs.length+1), if (x :: xs)[i.val] = some true then 1 else 0
    rw [Fin.sum_univ_succ]
    simp only [List.count_cons, Fin.val_zero, Fin.val_succ,
      List.getElem_cons_zero, List.getElem_cons_succ, beq_iff_eq]
    rw [ih]
    exact Nat.add_comm _ _

theorem ordinaryPositions_card (ms : List (Option Bool)) :
    (ordinaryPositions ms).card = ms.count (some true) := by
  rw [ordinaryPositions, Finset.card_filter]
  exact (mask_count_eq_sum_fin ms).symm

/-- Four choices independently at every ordinary position. -/
theorem ordinaryAssignments_card (ms : List (Option Bool)) :
    Fintype.card ((ordinaryPositions ms) → Fin 4) = 4 ^ ms.count (some true) := by
  simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_coe, ordinaryPositions_card]

theorem ordinaryAssignments_card_of_count {ms : List (Option Bool)} {t : Nat}
    (h : ms.count (some true) = t) :
    Fintype.card ((ordinaryPositions ms) → Fin 4) = 4 ^ t := by
  rw [ordinaryAssignments_card, h]

/-- Total number of labelled boxes in any finite mask family with the
same ordinary count. -/
theorem labelledMaskFamily_card (masks : Finset (List (Option Bool))) (t : Nat)
    (h : ∀ ms ∈ masks, ms.count (some true) = t) :
    Fintype.card (Σ ms : masks, (ordinaryPositions ms.val) → Fin 4) =
      masks.card * 4 ^ t := by
  rw [Fintype.card_sigma]
  simp only [ordinaryAssignments_card]
  have heach (ms : masks) : ms.val.count (some true) = t := h ms.val ms.property
  simp only [heach]
  simp


end ThinMatrix.OrderedBoxes

namespace ThinMatrix.OrderedBoxes

variable {ι R : Type*} [CommRing R]



end ThinMatrix.OrderedBoxes


namespace ThinMatrix.BoxOrdinaryExpansion

variable {ι R : Type*} [CommRing R]

/-- Bridge to the exact recursive evaluator already used by the partition. -/
theorem boxValue_eq_listBoxValue (P O : ι → R) (xs : List ι)
    (ms : List (Option Bool)) :
    OrderedBoxes.boxValue P O xs ms =
      listBoxValue (fun i => P i + O i) P O xs ms := by
  induction xs generalizing ms with
  | nil => cases ms <;> rfl
  | cons a xs ih =>
      cases ms with
      | nil => rfl
      | cons m ms =>
          cases m with
          | none => simp [OrderedBoxes.boxValue, listBoxValue, ih]
          | some b => cases b <;> simp [OrderedBoxes.boxValue, listBoxValue, ih]

/-- Full-five compatible-label expansion of the original ordered box.
The same full assignment labels both sides of every ordinary bilinear term. -/
theorem boxValue_full5_compatible_expansion (F : ι → Fin 5 → R)
    (xs : List ι) (ms : List (Option Bool)) (hlen : xs.length = ms.length) :
    OrderedBoxes.boxValue (fun a => F a 4)
        (fun a => ∑ l : Fin 4, F a l.castSucc) xs ms =
      ∑ labels ∈ OrderedBoxes.full5CompatibleLabels
        (fun i : Fin xs.length => ms[i.val]?.getD none),
          ∏ i : Fin xs.length, F xs[i] (labels i) := by
  rw [boxValue_eq_listBoxValue,
    listBoxValue_eq_boxKernel _ _ _ xs ms hlen]
  change (∏ i : Fin xs.length,
    OrderedBoxes.full5LocalFactor (ms[i.val]?.getD none) (F xs[i])) = _
  exact OrderedBoxes.full5_compatible_expansion _ _

/-- The finite-index ordinary subset has exactly the list's ordinary count. -/
theorem ordinaryPositions_getD_card (ms : List (Option Bool)) :
    (ordinaryPositions (fun i : Fin ms.length => ms[i.val]?.getD none)).card =
      ms.count (some true) := by
  have heq : ordinaryPositions (fun i : Fin ms.length => ms[i.val]?.getD none) =
      OrderedBoxes.ordinaryPositions ms := by
    ext i
    simp [ordinaryPositions, OrderedBoxes.ordinaryPositions]
  rw [heq, OrderedBoxes.ordinaryPositions_card]

theorem ordinaryPositions_getD_card_of_length
    (xs : List ι) (ms : List (Option Bool)) (hlen : xs.length = ms.length) :
    (ordinaryPositions (fun i : Fin xs.length => ms[i.val]?.getD none)).card =
      ms.count (some true) := by
  have aux (n : ℕ) (hn : n = ms.length) :
      (ordinaryPositions (fun i : Fin n => ms[i.val]?.getD none)).card =
        ms.count (some true) := by
    subst n
    exact ordinaryPositions_getD_card ms
  exact aux xs.length hlen

/-- A length-correct box with `t` ordinary positions has `4^t` common
ordinary-label assignments; neither stars nor private factors add labels. -/
theorem ordinary_label_count_of_list_count
    (xs : List ι) (ms : List (Option Bool)) (hlen : xs.length = ms.length)
    (t : ℕ) (hcount : ms.count (some true) = t) :
    Fintype.card ((ordinaryPositions
      (fun i : Fin xs.length => ms[i.val]?.getD none)) → Fin 4) = 4 ^ t := by
  rw [ordinary_label_count, ordinaryPositions_getD_card_of_length xs ms hlen, hcount]

end ThinMatrix.BoxOrdinaryExpansion


namespace ThinMatrix.TensorContraction

open scoped BigOperators
open Finset Polynomial

universe u v w x
variable {R : Type u} [CommRing R]
variable {A : Type v} {B : Type w} {ι : Type x} [Fintype A] [Fintype B]

/-- An ordered box contracts to the sum of exactly its compatible full
five-label leaves.  The raw input arrays are arbitrary and may be
entangled across all physical positions. -/
theorem box_contraction_compatible_leaves
    (X : A → R) (Y : B → R) (f : ι → Fin 5 → A → R) (g : ι → Fin 5 → B → R)
    (xs : List ι) (ms : List (Option Bool)) (hlen : xs.length = ms.length) :
    bilinear X Y (fun a b => OrderedBoxes.boxValue
      (fun i => f i 4 a*g i 4 b)
      (fun i => ∑ l : Fin 4, f i l.castSucc a*g i l.castSucc b) xs ms) =
      ∑ labels ∈ OrderedBoxes.full5CompatibleLabels
        (fun i : Fin xs.length => ms[i.val]?.getD none),
        (∑ a, X a*∏ i : Fin xs.length, f xs[i] (labels i) a) *
          (∑ b, Y b*∏ i : Fin xs.length, g xs[i] (labels i) b) := by
  classical
  have heq (a : A) (b : B) :=
    BoxOrdinaryExpansion.boxValue_full5_compatible_expansion
      (fun i l => f i l a*g i l b) xs ms hlen
  simp_rw [heq]
  rw [bilinear_sum]
  apply Finset.sum_congr rfl
  intro labels hlabels
  simp_rw [Finset.prod_mul_distrib]
  exact bilinear_separable X Y _ _

/-- Canonical box-to-leaf interface, including arbitrary raw-array
contraction.  Stars allow all five labels, private positions only label
four, and ordinary positions exactly the other four labels. -/
theorem aligned_box_contraction_compatible_leaves
    (Xraw : A → R) (Yraw : B → R)
    (x₁ x₂ p₁ p₂ : ι → A → R) (s v w : ι → B → R)
    (xs : List ι) (ms : List (Option Bool)) (hlen : xs.length = ms.length) :
    bilinear Xraw Yraw (fun a b => OrderedBoxes.boxValue
      (fun i => (-x₁ i a-x₂ i a)*(2*s i b))
      (fun i => (2*p₁ i a*s i b+p₂ i a*w i b)-(-x₁ i a-x₂ i a)*(2*s i b)) xs ms) =
      ∑ labels ∈ OrderedBoxes.full5CompatibleLabels
        (fun i : Fin xs.length => ms[i.val]?.getD none),
        (∑ a, Xraw a*∏ i : Fin xs.length,
          alignedLeft (x₁ xs[i] a) (x₂ xs[i] a) (p₁ xs[i] a) (p₂ xs[i] a) (labels i)) *
          (∑ b, Yraw b*∏ i : Fin xs.length,
            alignedRight (s xs[i] b) (v xs[i] b) (w xs[i] b) (labels i)) := by
  simpa only [aligned_private_label, aligned_ordinary_label_sum] using
    box_contraction_compatible_leaves Xraw Yraw
      (fun i l a => alignedLeft (x₁ i a) (x₂ i a) (p₁ i a) (p₂ i a) l)
      (fun i l b => alignedRight (s i b) (v i b) (w i b) l) xs ms hlen

/-- The exact number of ordinary-labelled ordered-box handles is
`choose k t * 4^t`.  Star expansion is a separate cached computation. -/
theorem labelled_ordered_box_count (k t : ℕ) :
    Fintype.card (Σ ms : (OrderedBoxes.orderedBoxMasks t k).toFinset,
      (OrderedBoxes.ordinaryPositions ms.val) → Fin 4) = k.choose t*4^t := by
  classical
  rw [OrderedBoxes.labelledMaskFamily_card
    (OrderedBoxes.orderedBoxMasks t k).toFinset t]
  · rw [List.toFinset_card_of_nodup (OrderedBoxes.orderedBoxMasks_nodup t k),
      OrderedBoxes.orderedBoxMasks_length]
  · intro ms hms
    exact (OrderedBoxes.orderedBoxMasks_shape (List.mem_toFinset.mp hms)).2.1

end ThinMatrix.TensorContraction

#print axioms ThinMatrix.OrderedBoxes.full5_compatible_expansion
#print axioms ThinMatrix.BoxOrdinaryExpansion.boxKernel_four_term_expansion
#print axioms ThinMatrix.BoxOrdinaryExpansion.boxValue_full5_compatible_expansion
#print axioms ThinMatrix.TensorContraction.box_contraction_compatible_leaves
#print axioms ThinMatrix.TensorContraction.aligned_box_contraction_compatible_leaves
#print axioms ThinMatrix.TensorContraction.labelled_ordered_box_count

namespace ThinMatrix.TensorContraction

open scoped BigOperators
open Finset Polynomial

universe u v w x
variable {R : Type u} [CommRing R]
variable {A : Type v} {B : Type w} {ι : Type x} [Fintype A] [Fintype B]

/-- A full aligned leaf is a product of two global raw-array transforms. -/
def alignedLeafValue (xs : List ι) (Xraw : A → R) (Yraw : B → R)
    (x₁ x₂ p₁ p₂ : ι → A → R) (s v w : ι → B → R)
    (labels : Fin xs.length → Fin 5) : R :=
  (∑ a, Xraw a*∏ i : Fin xs.length,
    alignedLeft (x₁ xs[i] a) (x₂ xs[i] a) (p₁ xs[i] a) (p₂ xs[i] a) (labels i)) *
    (∑ b, Yraw b*∏ i : Fin xs.length,
      alignedRight (s xs[i] b) (v xs[i] b) (w xs[i] b) (labels i))

/-- High boxes interpreted as sums of compatible full leaves.  This is
an algebraic meaning for an encoder's cached high-box handles. -/
noncomputable def alignedHighLeafBoxes (k t : ℕ) (Xraw : A → R) (Yraw : B → R)
    (x₁ x₂ p₁ p₂ : Fin k → A → R) (s v w : Fin k → B → R) : R :=
  ((OrderedBoxes.orderedBoxMasks t k).map (fun ms =>
    ∑ labels ∈ OrderedBoxes.full5CompatibleLabels
      (fun i : Fin (List.finRange k).reverse.length => ms[i.val]?.getD none),
      alignedLeafValue (List.finRange k).reverse Xraw Yraw x₁ x₂ p₁ p₂ s v w labels)).sum

/-- Complete aligned finite query, now with the high part expressed in
compatible transformed leaves, ready to instantiate an arbitrary-leaf
encoder recurrence. -/
theorem aligned_full_query_eq_weightedLow_add_leaf_boxes
    (k t : ℕ) (ht : t ≤ k) (Xraw : A → R) (Yraw : B → R)
    (x₁ x₂ p₁ p₂ : Fin k → A → R) (s v w : Fin k → B → R) :
    bilinear Xraw Yraw (fun a b => ∏ i, (2*p₁ i a*s i b+p₂ i a*w i b)) =
      weightedLow k t (pencilQuery k Xraw Yraw
        (fun i a b => (-x₁ i a-x₂ i a)*(2*s i b))
        (fun i a b => 2*p₁ i a*s i b+p₂ i a*w i b)) +
      alignedHighLeafBoxes k t Xraw Yraw x₁ x₂ p₁ p₂ s v w := by
  rw [full_query_eq_weightedLow_add_boxes k t ht Xraw Yraw
    (fun i a b => (-x₁ i a-x₂ i a)*(2*s i b))
    (fun i a b => 2*p₁ i a*s i b+p₂ i a*w i b)]
  congr 1
  unfold alignedHighLeafBoxes
  apply congrArg List.sum
  apply List.map_congr_left
  intro ms hms
  have hlen : (List.finRange k).reverse.length = ms.length := by
    rw [List.length_reverse, List.length_finRange, (OrderedBoxes.orderedBoxMasks_shape hms).1]
  simpa only [alignedLeafValue] using
    aligned_box_contraction_compatible_leaves Xraw Yraw x₁ x₂ p₁ p₂ s v w
      (List.finRange k).reverse ms hlen

end ThinMatrix.TensorContraction

#print axioms ThinMatrix.TensorContraction.aligned_full_query_eq_weightedLow_add_leaf_boxes
