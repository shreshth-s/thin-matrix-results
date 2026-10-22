import Mathlib

set_option autoImplicit false

/-!
# Original-coordinate masks partition a matrix contraction

The indices of the translation list, not its values, are the mask labels.
Translations may repeat. Each input uses its own normal-side selector, and
both inputs in a piece use the same pair of translations. This module proves
the finite partition before Walsh transforms or any support crop.
-/

namespace ThinMatrix.TranslatedSourcePartition
open scoped BigOperators
universe u v w
variable {R : Type u} [CommRing R]
variable {H : Type v} [Fintype H]
variable {J : Type w} [Fintype J] [DecidableEq J]

def leftPiece (X : H → H → R) (pick : H → J) (shift : J → H ≃ H)
    (r s : J) (h k : H) : R :=
  if pick (shift r h) = r then X (shift r h) (shift s k) else 0

def rightPiece (Y : H → H → R) (pick : H → J) (shift : J → H ≃ H)
    (r s : J) (h k : H) : R :=
  if pick (shift s k) = s then Y (shift r h) (shift s k) else 0

omit [Fintype J] in
theorem reindex_piece (X Y : H → H → R) (pickL pickR : H → J)
    (shift : J → H ≃ H) (r s : J) :
    (∑ h, ∑ k, leftPiece X pickL shift r s h k *
      rightPiece Y pickR shift r s h k) =
    ∑ h, ∑ k, (if pickL h = r then X h k else 0) *
      (if pickR k = s then Y h k else 0) := by
  unfold leftPiece rightPiece
  calc
    _ = ∑ h, ∑ k, (if pickL (shift r h) = r then X (shift r h) k else 0) *
        (if pickR k = s then Y (shift r h) k else 0) := by
      apply Finset.sum_congr rfl
      intro h _
      exact (shift s).sum_comp (fun k =>
        (if pickL (shift r h) = r then X (shift r h) k else 0) *
        (if pickR k = s then Y (shift r h) k else 0))
    _ = _ := (shift r).sum_comp (fun h => ∑ k,
      (if pickL h = r then X h k else 0) * (if pickR k = s then Y h k else 0))

omit [Fintype H] in
theorem masks_partition (X Y : H → H → R) (pickL pickR : H → J)
    (h k : H) :
    (∑ r, ∑ s, (if pickL h = r then X h k else 0) *
      (if pickR k = s then Y h k else 0)) = X h k * Y h k := by
  classical
  simp [eq_comm]

theorem translated_contraction (X Y : H → H → R) (pickL pickR : H → J)
    (shift : J → H ≃ H) :
    (∑ r, ∑ s, ∑ h, ∑ k, leftPiece X pickL shift r s h k *
      rightPiece Y pickR shift r s h k) = ∑ h, ∑ k, X h k * Y h k := by
  simp_rw [reindex_piece]
  calc
    _ = ∑ r, ∑ h, ∑ k, ∑ s, (if pickL h = r then X h k else 0) *
        (if pickR k = s then Y h k else 0) := by
      apply Finset.sum_congr rfl
      intro r _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro h _
      exact Finset.sum_comm
    _ = ∑ h, ∑ k, ∑ r, ∑ s, (if pickL h = r then X h k else 0) *
        (if pickR k = s then Y h k else 0) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro h _
      exact Finset.sum_comm
    _ = _ := by simp_rw [masks_partition]

#print axioms reindex_piece
#print axioms masks_partition
#print axioms translated_contraction

end ThinMatrix.TranslatedSourcePartition
