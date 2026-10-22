import HalfSourceList
import TranslatedSourcePartition
import CroppedSourceContraction

set_option autoImplicit false

/-!
# Original-coordinate first-index masks produce light normal sources

The selector is indexed by each input's own good set. Its validity concerns
the inverse normal-coordinate weight after translation. Walsh transformation
acts only on the opposite outer coordinate, so it preserves these zeros.
-/

namespace ThinMatrix.MaskedLightSources
open ThinMatrix.WalshEmbedding
open scoped BigOperators
variable {R : Type*} [CommRing R]

def xorShift {m : ℕ} (d : Cube m) : Cube m ≃ Cube m where
  toFun h := xorBits h d
  invFun h := xorBits h d
  left_inv h := by funext i; simp [xorBits]
  right_inv h := by funext i; simp [xorBits]

def leftInput {L m k J : ℕ} (X : RawLeftInput L m k R)
    (pick : Finset (Fin L) → Cube m → Fin J) (ds : Fin J → Cube m)
    (r s : Fin J) : RawLeftInput L m k R :=
  fun Q outer other h k =>
    TranslatedSourcePartition.leftPiece (X Q outer other) (pick Q)
      (fun j => xorShift (ds j)) r s h k

def rightInput {L m k J : ℕ} (Y : RawRightInput L m k R)
    (pick : Finset (Fin L) → Cube m → Fin J) (ds : Fin J → Cube m)
    (r s : Fin J) : RawRightInput L m k R :=
  fun Q outer h k other =>
    TranslatedSourcePartition.rightPiece (fun h k => Y Q outer h k other) (pick Q)
      (fun j => xorShift (ds j)) r s h k

theorem translated_product {L m k J : ℕ}
    (X : RawLeftInput L m k R) (Y : RawRightInput L m k R)
    (pickL pickR : Finset (Fin L) → Cube m → Fin J) (ds : Fin J → Cube m)
    (QL QR : Finset (Fin L)) (iL iR : Cube L) (aL aR : Cube k) :
    (∑ r, ∑ s, ∑ h, ∑ k,
      leftInput X pickL ds r s QL iL aL h k * rightInput Y pickR ds r s QR iR h k aR) =
      ∑ h, ∑ k, X QL iL aL h k * Y QR iR h k aR :=
  TranslatedSourcePartition.translated_contraction (X QL iL aL)
    (fun h k => Y QR iR h k aR) (pickL QL) (pickR QR) (fun j => xorShift (ds j))

theorem left_zero_of_weight {L m k J : ℕ} (cap : ℕ) (X : RawLeftInput L m k R)
    (pick : Finset (Fin L) → Cube m → Fin J) (ds : Fin J → Cube m)
    (weight : Finset (Fin L) → Cube m → ℕ) (Q : Finset (Fin L))
    (hvalid : ∀ h, weight Q (xorBits h (ds (pick Q h))) ≤ cap)
    (r s : Fin J) (outer : Cube L) (other : Cube k) (h k : Cube m)
    (hlarge : cap < weight Q h) : leftInput X pick ds r s Q outer other h k = 0 := by
  have hp : pick Q (xorBits h (ds r)) ≠ r := by
    intro he
    have hv := hvalid (xorBits h (ds r))
    rw [he] at hv
    have hi : xorBits (xorBits h (ds r)) (ds r) = h := (xorShift (ds r)).left_inv h
    rw [hi] at hv
    omega
  simp [leftInput,TranslatedSourcePartition.leftPiece,xorShift,hp]

theorem right_zero_of_weight {L m k J : ℕ} (cap : ℕ) (Y : RawRightInput L m k R)
    (pick : Finset (Fin L) → Cube m → Fin J) (ds : Fin J → Cube m)
    (weight : Finset (Fin L) → Cube m → ℕ) (Q : Finset (Fin L))
    (hvalid : ∀ h, weight Q (xorBits h (ds (pick Q h))) ≤ cap)
    (r s : Fin J) (outer : Cube L) (other : Cube k) (h k : Cube m)
    (hlarge : cap < weight Q k) : rightInput Y pick ds r s Q outer h k other = 0 := by
  have hp : pick Q (xorBits k (ds s)) ≠ s := by
    intro he
    have hv := hvalid (xorBits k (ds s))
    rw [he] at hv
    have hi : xorBits (xorBits k (ds s)) (ds s) = k := (xorShift (ds s)).left_inv k
    rw [hi] at hv
    omega
  simp [rightInput,TranslatedSourcePartition.rightPiece,xorShift,hp]

theorem left_normal_cap {L m k J : ℕ} (cap : ℕ) (X : RawLeftInput L m k R)
    (pick : Finset (Fin L) → Cube m → Fin J) (ds : Fin J → Cube m)
    (weight : Finset (Fin L) → Cube m → ℕ) (good : Finset (Finset (Fin L)))
    (gamma : Cube L → Cube m) (delta : Cube L → Cube k)
    (hvalid : ∀ Q ∈ good, ∀ h, weight Q (xorBits h (ds (pick Q h))) ≤ cap)
    (hweight : ∀ n, normalSupport n ∈ good →
      weight (normalSupport n) (gamma (normalP2Bits n)) = ones (normalP2Bits n))
    (r s : Fin J) (run : ℤ) (n : Fin L → NormalLetter) (o : Fin L → OppositeLetter)
    (hlarge : cap < ones (normalP2Bits n)) :
    rawLeftSource (leftInput X pick ds r s) good gamma delta run n o = 0 := by
  by_cases hg : normalSupport n ∈ good
  · have hz : ∀ outer k, leftInput X pick ds r s (normalSupport n) (normalOuterBits n)
        outer (gamma (normalP2Bits n)) k = 0 := by
      intro outer k
      apply left_zero_of_weight cap X pick ds weight _ (hvalid _ hg)
      simpa only [hweight n hg] using hlarge
    simp [rawLeftSource,walsh,hz]
  · exact raw_left_nongood _ _ _ _ _ _ _ hg

theorem right_normal_cap {L m k J : ℕ} (cap : ℕ) (Y : RawRightInput L m k R)
    (pick : Finset (Fin L) → Cube m → Fin J) (ds : Fin J → Cube m)
    (weight : Finset (Fin L) → Cube m → ℕ) (good : Finset (Finset (Fin L)))
    (gamma : Cube L → Cube m) (delta : Cube L → Cube k)
    (hvalid : ∀ Q ∈ good, ∀ h, weight Q (xorBits h (ds (pick Q h))) ≤ cap)
    (hweight : ∀ n, normalSupport n ∈ good →
      weight (normalSupport n) (gamma (normalP2Bits n)) = ones (normalP2Bits n))
    (r s : Fin J) (run : ℤ) (n : Fin L → NormalLetter) (o : Fin L → OppositeLetter)
    (hlarge : cap < ones (normalP2Bits n)) :
    rawRightSource (rightInput Y pick ds r s) good gamma delta run n o = 0 := by
  by_cases hg : normalSupport n ∈ good
  · have hz : ∀ outer h, rightInput Y pick ds r s (normalSupport n) (normalOuterBits n)
        h (gamma (normalP2Bits n)) outer = 0 := by
      intro outer h
      apply right_zero_of_weight cap Y pick ds weight _ (hvalid _ hg)
      simpa only [hweight n hg] using hlarge
    simp [rawRightSource,walsh,hz]
  · exact raw_right_nongood _ _ _ _ _ _ _ hg

#print axioms xorShift
#print axioms translated_product
#print axioms left_zero_of_weight
#print axioms right_zero_of_weight
#print axioms left_normal_cap
#print axioms right_normal_cap

end ThinMatrix.MaskedLightSources
