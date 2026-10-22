import WalshEmbedding
import HalfSourcePotential

set_option autoImplicit false

/-!
# Affine half-weight coverage from strict small bias

Rows are binary characters. Only nonzero rows are required, so the result
applies in particular to invertible binary maps. The averaging is over list
indices, including repeats. Constructing the small-bias list and connecting
the selected masks to the cropped raw sources remain separate steps.
-/

namespace ThinMatrix.HalfSourceCoverage
open ThinMatrix.WalshEmbedding
open scoped BigOperators
noncomputable section

def SmallBias {m J : ℕ} (ds : Fin J → Cube m) (eps : ℝ) : Prop :=
  ∀ a : Cube m, a ≠ zeroBits m →
    |∑ j, character (R := ℝ) a (ds j)| < (J:ℝ)*eps

def rowMap {m : ℕ} (rows : Fin m → Cube m) (v : Cube m) : Cube m :=
  fun i => dotBits (rows i) v

theorem dot_zero_left {m : ℕ} (v : Cube m) : dotBits (zeroBits m) v = false := by
  have h : bitSign (R := ℤ) (dotBits (zeroBits m) v) = 1 := by
    rw [← character_eq_sign_dot,character_zero]
  cases hb : dotBits (zeroBits m) v <;> simp_all [bitSign]

theorem nonzero_rows_of_surjective {m : ℕ} (rows : Fin m → Cube m)
    (h : Function.Surjective (rowMap rows)) : ∀ i, rows i ≠ zeroBits m := by
  intro i hi
  obtain ⟨v,hv⟩ := h (fun _ => true)
  have he := congrFun hv i
  simp only [rowMap,hi,dot_zero_left] at he
  cases he

theorem character_right_xor {m : ℕ} (a h d : Cube m) :
    character (R := ℝ) a (xorBits h d) = character a h * character a d := by
  rw [character_symmetric a, character_xor,
    character_symmetric h a, character_symmetric d a]

theorem character_abs_one {m : ℕ} (a v : Cube m) :
    |character (R := ℝ) a v| = 1 := by
  rw [character_eq_sign_dot]
  cases dotBits a v <;> norm_num [bitSign]

theorem translated_bias {m J : ℕ} (ds : Fin J → Cube m) (eps : ℝ)
    (hb : SmallBias ds eps) (a h : Cube m) (ha : a ≠ zeroBits m) :
    |∑ j, character (R := ℝ) a (xorBits h (ds j))| < (J:ℝ)*eps := by
  simp_rw [character_right_xor, ← Finset.mul_sum]
  rw [abs_mul, character_abs_one, one_mul]
  exact hb a ha

theorem weight_character_identity {m : ℕ} (v : Cube m) :
    (m:ℝ)-2*(ones v:ℝ) = ∑ i, bitSign (R := ℝ) (v i) := by
  have he : ∀ i : Fin m, bitSign (R := ℝ) (v i) =
      1-2*(if v i then (1:ℝ) else 0) := by
    intro i
    cases v i <;> norm_num [bitSign]
  simp_rw [he, Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp [ones]

theorem mean_weight_strict {m J : ℕ} (hm : 0 < m)
    (ds : Fin J → Cube m) (eps : ℝ) (hb : SmallBias ds eps)
    (rows : Fin m → Cube m) (hr : ∀ i, rows i ≠ zeroBits m) (h : Cube m) :
    (∑ j, (ones (rowMap rows (xorBits h (ds j))):ℝ)) <
      (J:ℝ)*((m:ℝ)/2+eps*(m:ℝ)/2) := by
  have hlo : ∀ i : Fin m, -(J:ℝ)*eps <
      ∑ j, bitSign (R := ℝ) (rowMap rows (xorBits h (ds j)) i) := by
    intro i
    have hb' := (abs_lt.mp (translated_bias ds eps hb (rows i) h (hr i))).1
    simpa only [rowMap, character_eq_sign_dot, neg_mul] using hb'
  have hsum := Finset.sum_lt_sum_of_nonempty
    (s := Finset.univ) (f := fun _ : Fin m => -(J:ℝ)*eps)
    (g := fun i => ∑ j, bitSign (R := ℝ) (rowMap rows (xorBits h (ds j)) i))
    (show (Finset.univ : Finset (Fin m)).Nonempty from ⟨⟨0,hm⟩,Finset.mem_univ _⟩)
    (fun i _ => hlo i)
  have hid : (J:ℝ)*(m:ℝ)-2*(∑ j, (ones (rowMap rows (xorBits h (ds j))):ℝ)) =
      ∑ i, ∑ j, bitSign (R := ℝ) (rowMap rows (xorBits h (ds j)) i) := by
    rw [Finset.sum_comm]
    simp_rw [← weight_character_identity]
    simp [Finset.sum_sub_distrib, Finset.mul_sum]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  linarith

theorem half_mean {m J : ℕ} (hm : 0 < m)
    (ds : Fin J → Cube m) (hb : SmallBias ds (1/(2*(m:ℝ))))
    (rows : Fin m → Cube m) (hr : ∀ i, rows i ≠ zeroBits m) (h : Cube m) :
    (∑ j, (ones (rowMap rows (xorBits h (ds j))):ℝ)) <
      (J:ℝ)*((m:ℝ)/2+1/4) := by
  have hm0 : (m:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  have he : 1/(2*(m:ℝ))*(m:ℝ)/2 = 1/4 := by field_simp; norm_num
  simpa only [he] using mean_weight_strict hm ds (1/(2*(m:ℝ))) hb rows hr h

theorem affine_half_coverage {m J : ℕ} (hm : 0 < m) (hJ : 0 < J)
    (ds : Fin J → Cube m) (hb : SmallBias ds (1/(2*(m:ℝ))))
    (rows : Fin m → Cube m) (hr : ∀ i, rows i ≠ zeroBits m) (h : Cube m) :
    ∃ j, ones (rowMap rows (xorBits h (ds j))) ≤ m/2 :=
  HalfSourcePotential.exists_half_of_sum hJ _ (half_mean hm ds hb rows hr h)

def validIndices {m J : ℕ} (weight : Fin J → ℕ) : Finset (Fin J) :=
  Finset.univ.filter (fun j => weight j ≤ m/2)

def firstIndex {m J : ℕ} (weight : Fin J → ℕ)
    (h : ∃ j, weight j ≤ m/2) : Fin J :=
  (validIndices (m := m) weight).min' (by
    obtain ⟨j,hj⟩ := h
    exact ⟨j,by simp [validIndices,hj]⟩)

theorem firstIndex_valid {m J : ℕ} (weight : Fin J → ℕ)
    (h : ∃ j, weight j ≤ m/2) : weight (firstIndex weight h) ≤ m/2 := by
  have hc := Finset.min'_mem (validIndices (m := m) weight) (by
    obtain ⟨j,hj⟩ := h
    exact ⟨j,by simp [validIndices,hj]⟩)
  simpa only [firstIndex, validIndices, Finset.mem_filter, Finset.mem_univ, true_and] using hc

theorem firstIndex_minimal {m J : ℕ} (weight : Fin J → ℕ)
    (h : ∃ j, weight j ≤ m/2) (j : Fin J) (hj : j < firstIndex weight h) :
    m/2 < weight j := by
  by_contra! hw
  have hc : firstIndex weight h ≤ j :=
    Finset.min'_le _ j (by simp [validIndices,hw])
  exact (not_lt_of_ge hc) hj

#print axioms character_right_xor
#print axioms dot_zero_left
#print axioms nonzero_rows_of_surjective
#print axioms character_abs_one
#print axioms translated_bias
#print axioms weight_character_identity
#print axioms mean_weight_strict
#print axioms half_mean
#print axioms affine_half_coverage
#print axioms firstIndex_valid
#print axioms firstIndex_minimal

end
end ThinMatrix.HalfSourceCoverage
