import ExactHalfGoodMap
import HalfSourceMaskWork
import HalfSourceBinarySelection

set_option autoImplicit false

/-!
# Exact-half cropping for the constructed good maps

The inverse-map weights and selectors are constructed here. The public
embedding has no assumed weight identity, selector validity, or small-bias
oracle. The zero-dimensional case uses one empty translation. This is a
finite source identity, not a cost bound for the embedding or APSP.
-/

namespace ThinMatrix.ExactHalfCroppedEmbedding
open ThinMatrix.GoodSets ThinMatrix.GoodSetConstruction ThinMatrix.GoodMapEmbedding
open ThinMatrix.WalshEmbedding ThinMatrix.HalfSourceCoverage ThinMatrix.HalfSourceList
open ThinMatrix.ExactHalfGoodMap ThinMatrix.MaskedLightSources
open scoped BigOperators
noncomputable section

def rows {L m : ℕ} (Q : Finset (Fin L)) (hQ : Q ∈ goodSlots L m) : Fin m → Cube m :=
  inverseRows (constructGoodMaps L m).1 Q (goodSlots_size L m Q hQ)
    ((mem_goodSlots L m Q).mp hQ).2.1

theorem rows_surjective {L m : ℕ} (Q : Finset (Fin L)) (hQ : Q ∈ goodSlots L m) :
    Function.Surjective (rowMap (rows Q hQ)) :=
  inverseRows_surjective _ _ _ _

/-- Off the supported good sets the weight is irrelevant and set to zero. -/
def weight (L m : ℕ) (Q : Finset (Fin L)) (h : Cube m) : ℕ :=
  if hQ : Q ∈ goodSlots L m then
    inverseWeight (constructGoodMaps L m).1 Q (goodSlots_size L m Q hQ)
      ((mem_goodSlots L m Q).mp hQ).2.1 h
  else 0

theorem rows_weight {L m : ℕ} (Q : Finset (Fin L)) (hQ : Q ∈ goodSlots L m)
    (h : Cube m) : ones (rowMap (rows Q hQ) h) = weight L m Q h := by
  simp only [weight, dif_pos hQ, rows, inverseRows_weight]

theorem weight_le (L m : ℕ) (Q : Finset (Fin L)) (h : Cube m) : weight L m Q h ≤ m := by
  by_cases hQ : Q ∈ goodSlots L m
  · rw [← rows_weight Q hQ]
    exact ones_le _
  · simp [weight, hQ]

theorem normal_weight (L m : ℕ) (n : Fin L → NormalLetter)
    (hn : normalSupport n ∈ goodSlots L m) :
    weight L m (normalSupport n) (cubeMap (constructGoodMaps L m).1 (normalP2Bits n)) =
      ones (normalP2Bits n) := by
  let T : Subsets (normalSupport n) := ⟨RawWordBijection.p2Positions n, by
    intro i hi
    have hp := (RawWordBijection.mem_p2Positions n i).mp hi
    simp [normalSupport, normalIsP, hp]⟩
  have hbits : normalP2Bits n = setBits T.val := by
    funext i
    simp [normalP2Bits, setBits, T]
  rw [hbits, ones_setBits]
  simp only [weight, dif_pos hn]
  exact inverseWeight_supported _ _ _ _ T

/-- The list computed by binary score arithmetic for positive dimension; one empty vector at zero. -/
def shifts (m : ℕ) : List (Cube m) := if m = 0 then [zeroBits m] else (HalfSourceBinarySelection.translations m).value

theorem shifts_length (m : ℕ) : (shifts m).length = if m = 0 then 1 else 64*m^3 := by
  by_cases hm : m = 0
  · simp [shifts, hm]
  · simp [shifts, hm, HalfSourceBinarySelection.translations_value m (Nat.pos_of_ne_zero hm), translations_length]

theorem shifts_positive (m : ℕ) (hm : 0 < m) : shifts m = translations m := by
  simp [shifts, Nat.ne_of_gt hm, HalfSourceBinarySelection.translations_value m hm]

theorem pair_count (m : ℕ) :
    Fintype.card (Fin (shifts m).length × Fin (shifts m).length) =
      if m = 0 then 1 else 4096*m^6 := by
  simp only [Fintype.card_prod, Fintype.card_fin, shifts_length]
  split_ifs <;> ring

theorem shifts_nonempty (m : ℕ) : 0 < (shifts m).length := by
  rw [shifts_length]
  split_ifs with hm
  · omega
  · have : 0 < m := Nat.pos_of_ne_zero hm
    positivity

/-- The first valid translation index, with a harmless value off good sets. -/
def pick (L m : ℕ) (Q : Finset (Fin L)) (h : Cube m) : Fin (shifts m).length :=
  if hm : m = 0 then ⟨0, shifts_nonempty m⟩
  else if hQ : Q ∈ goodSlots L m then
    Fin.cast (by rw [shifts_positive m (Nat.pos_of_ne_zero hm)])
      (HalfSourceSelector.pick m (Nat.pos_of_ne_zero hm) (rows Q hQ)
        (nonzero_rows_of_surjective _ (rows_surjective Q hQ)) h)
  else ⟨0, shifts_nonempty m⟩

theorem pick_valid (L m : ℕ) (Q : Finset (Fin L)) (hQ : Q ∈ goodSlots L m)
    (h : Cube m) : weight L m Q (xorBits h ((shifts m).get (pick L m Q h))) ≤ m/2 := by
  by_cases hm : m = 0
  · subst m
    exact weight_le L 0 Q _
  · have hv := HalfSourceSelector.invertible_pick_valid m (Nat.pos_of_ne_zero hm)
      (rows Q hQ) (rows_surjective Q hQ) h
    rw [rows_weight Q hQ] at hv
    simpa [pick, shifts_positive m (Nat.pos_of_ne_zero hm), hm, hQ] using hv

/-- The weight callback evaluates the stored inverse rows, retaining its work. -/
def evaluate (L m : ℕ) (Q : Finset (Fin L)) (h : Cube m)
    (j : Fin (shifts m).length) : ℕ × ℕ :=
  if hQ : Q ∈ goodSlots L m then
    HalfSourceMaskWork.evaluate (rows Q hQ) h ((shifts m).get j)
  else (0, 1)

theorem evaluate_value (L m : ℕ) (Q : Finset (Fin L)) (h : Cube m)
    (j : Fin (shifts m).length) :
    (evaluate L m Q h j).1 = weight L m Q (xorBits h ((shifts m).get j)) := by
  by_cases hQ : Q ∈ goodSlots L m
  · simp only [evaluate, dif_pos hQ, HalfSourceMaskWork.evaluate_value, rows_weight Q hQ]
  · simp [evaluate, weight, hQ]

def scan (L m : ℕ) (Q : Finset (Fin L)) (h : Cube m) :
    Option (Fin (shifts m).length) × ℕ :=
  HalfSourceScan.run (m/2) (evaluate L m Q h)

theorem valid_exists (L m : ℕ) (Q : Finset (Fin L)) (h : Cube m) :
    ∃ j, weight L m Q (xorBits h ((shifts m).get j)) ≤ m/2 := by
  refine ⟨pick L m Q h, ?_⟩
  by_cases hQ : Q ∈ goodSlots L m
  · exact pick_valid L m Q hQ h
  · simp [weight, hQ]

theorem scan_result (L m : ℕ) (Q : Finset (Fin L)) (h : Cube m) :
    (scan L m Q h).1 = some (firstIndex
      (fun j => weight L m Q (xorBits h ((shifts m).get j))) (valid_exists L m Q h)) :=
  HalfSourceScan.run_eq_first _ _ (evaluate_value L m Q h) (valid_exists L m Q h)

/-- Retain the returned index; the fallback is proved unreachable. -/
def scanPick (L m : ℕ) (Q : Finset (Fin L)) (h : Cube m) : Fin (shifts m).length :=
  (scan L m Q h).1.getD ⟨0, shifts_nonempty m⟩

theorem scanPick_valid (L m : ℕ) (Q : Finset (Fin L)) (h : Cube m) :
    weight L m Q (xorBits h ((shifts m).get (scanPick L m Q h))) ≤ m/2 := by
  simp only [scanPick, scan_result, Option.getD_some]
  exact firstIndex_valid _ (valid_exists L m Q h)

theorem scanPick_first (L m : ℕ) (Q : Finset (Fin L)) (h : Cube m)
    (j : Fin (shifts m).length) (hj : j < scanPick L m Q h) :
    m/2 < weight L m Q (xorBits h ((shifts m).get j)) := by
  simp only [scanPick, scan_result, Option.getD_some] at hj
  exact firstIndex_minimal _ (valid_exists L m Q h) j hj

/-- Indexed Boolean/register work once the list and inverse rows are stored.
This callback counter excludes good-set lookup, input construction, and the
binary lowering of register operations. Only the stored-row scan is priced. -/
theorem scan_work (L m : ℕ) (Q : Finset (Fin L)) (h : Cube m) :
    (scan L m Q h).2 ≤ (shifts m).length*(m*(6*m+5)+4*m+5)+2 := by
  have hc : ∀ j, (evaluate L m Q h j).2 ≤ m*(6*m+5)+1+4*m := by
    intro j
    by_cases hQ : Q ∈ goodSlots L m
    · simp only [evaluate, dif_pos hQ, HalfSourceMaskWork.evaluate_work, le_refl]
    · simp only [evaluate, dif_neg hQ]
      omega
  have he := HalfSourceScan.run_work (m/2) (evaluate L m Q h) _ hc
  unfold scan
  convert he using 1
  ring

/-- Complete exact-half embedding for every dimension, including m=0.
All masks use the same explicitly constructed list and the actual inverse
of each good restriction. All translation-index pairs are retained. -/
theorem complete_embedding {R : Type*} [CommRing R]
    (L m : ℕ) (hm : m ≤ L)
    (X : RawLeftInput L m (L-m) R) (Y : RawRightInput L m (L-m) R)
    (QL QR : Finset (Fin L)) (hQL : QL ∈ goodSlots L m) (hQR : QR ∈ goodSlots L m)
    (iL iR : Cube L) (aL aR : Cube (L-m)) :
    (∑ r, ∑ s, CroppedSourceContraction.contraction (m/2)
      (leftInput X (scanPick L m) (shifts m).get r s)
      (rightInput Y (scanPick L m) (shifts m).get r s)
      (goodSlots L m) (cubeMap (constructGoodMaps L m).1) (cubeMap (constructGoodMaps L m).2)
      QL QR iL iR
      (transposeMap (boolColumns (constructGoodMaps L m).2) aR)
      (transposeMap (boolColumns (constructGoodMaps L m).2) aL)) =
      (4:R)^L * ∑ h, ∑ k,
        X QL (outsideBits QL iL) aL h k * Y QR (outsideBits QR iR) h k aR :=
  TranslatedCroppedEmbedding.complete_embedding L m (shifts m).length (m/2) hm X Y
    (shifts m).get (scanPick L m) (scanPick L m) (weight L m)
    (fun Q _ => scanPick_valid L m Q) (fun Q _ => scanPick_valid L m Q) (normal_weight L m)
    QL QR hQL hQR iL iR aL aR

#print axioms rows_surjective
#print axioms rows_weight
#print axioms weight_le
#print axioms normal_weight
#print axioms shifts_length
#print axioms shifts_positive
#print axioms pair_count
#print axioms shifts_nonempty
#print axioms pick_valid
#print axioms evaluate_value
#print axioms valid_exists
#print axioms scan_result
#print axioms scanPick_valid
#print axioms scanPick_first
#print axioms scan_work
#print axioms complete_embedding
end
end ThinMatrix.ExactHalfCroppedEmbedding
