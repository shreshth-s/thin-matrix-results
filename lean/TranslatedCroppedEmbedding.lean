import MaskedLightSources
import GoodMapEmbedding

set_option autoImplicit false

/-!
# Complete translated-and-cropped embedding

This composes the source-level lemmas with the repository's constructed good
maps and original transpose-Delta locators. The remaining interface is the
normal-coordinate weight and the validity of its selector. The conclusion
contains all translation pairs and the original factor 4^L; no division of
individual terms is used.
-/

namespace ThinMatrix.TranslatedCroppedEmbedding
open ThinMatrix.WalshEmbedding ThinMatrix.GoodMapEmbedding ThinMatrix.MaskedLightSources
open ThinMatrix.GoodSetConstruction
open scoped BigOperators
variable {R : Type*} [CommRing R]

theorem complete_embedding (L m J cap : ℕ) (hm : m ≤ L)
    (X : RawLeftInput L m (L-m) R) (Y : RawRightInput L m (L-m) R)
    (ds : Fin J → Cube m) (pickL pickR : Finset (Fin L) → Cube m → Fin J)
    (weight : Finset (Fin L) → Cube m → ℕ)
    (hL : ∀ Q ∈ goodSlots L m, ∀ h, weight Q (xorBits h (ds (pickL Q h))) ≤ cap)
    (hR : ∀ Q ∈ goodSlots L m, ∀ h, weight Q (xorBits h (ds (pickR Q h))) ≤ cap)
    (hw : ∀ n, normalSupport n ∈ goodSlots L m →
      weight (normalSupport n) (cubeMap (constructGoodMaps L m).1 (normalP2Bits n)) =
        ones (normalP2Bits n))
    (QL QR : Finset (Fin L)) (hQL : QL ∈ goodSlots L m) (hQR : QR ∈ goodSlots L m)
    (iL iR : Cube L) (aL aR : Cube (L-m)) :
    (∑ r, ∑ s, CroppedSourceContraction.contraction cap
      (leftInput X pickL ds r s) (rightInput Y pickR ds r s)
      (goodSlots L m) (cubeMap (constructGoodMaps L m).1) (cubeMap (constructGoodMaps L m).2)
      QL QR iL iR
      (transposeMap (boolColumns (constructGoodMaps L m).2) aR)
      (transposeMap (boolColumns (constructGoodMaps L m).2) aL)) =
      (4:R)^L * ∑ h, ∑ k,
        X QL (outsideBits QL iL) aL h k * Y QR (outsideBits QR iR) h k aR := by
  have hp (r s : Fin J) : CroppedSourceContraction.contraction cap
      (leftInput X pickL ds r s) (rightInput Y pickR ds r s)
      (goodSlots L m) (cubeMap (constructGoodMaps L m).1) (cubeMap (constructGoodMaps L m).2)
      QL QR iL iR
      (transposeMap (boolColumns (constructGoodMaps L m).2) aR)
      (transposeMap (boolColumns (constructGoodMaps L m).2) aL) =
      (4:R)^L * ∑ h, ∑ k,
        leftInput X pickL ds r s QL (outsideBits QL iL) aL h k *
        rightInput Y pickR ds r s QR (outsideBits QR iR) h k aR := by
    rw [CroppedSourceContraction.contraction_eq cap _ _ _ _ _ _ _ _ _ _ _
      (goodSlots_size L m QL hQL) (goodSlots_size L m QR hQR) (goodSlots_size L m)
      (left_normal_cap cap X pickL ds weight _ _ _ hL hw r s)
      (right_normal_cap cap Y pickR ds weight _ _ _ hR hw r s)]
    exact constructed_raw_embedding L m hm _ _ QL QR hQL hQR iL iR aL aR
  simp_rw [hp,← Finset.mul_sum]
  rw [translated_product]

#print axioms complete_embedding

end ThinMatrix.TranslatedCroppedEmbedding
