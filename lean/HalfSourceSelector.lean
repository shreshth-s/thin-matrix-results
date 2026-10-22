import HalfSourceList
import MaskedLightSources

set_option autoImplicit false

/-!
# The concrete first-valid list-index selector

The list is the rational greedy construction, not an assumed small-bias
family. Selectors depend on each input's own normal map. Repeated vectors
remain distinct indices. `pair_count` counts the complete Cartesian list
of translation pairs; it is not an execution-time theorem.
-/

namespace ThinMatrix.HalfSourceSelector
open ThinMatrix.WalshEmbedding ThinMatrix.HalfSourceCoverage ThinMatrix.HalfSourceList

noncomputable def pick (m : ℕ) (hm : 0 < m)
    (rows : Fin m → Cube m) (hr : ∀ i, rows i ≠ zeroBits m) (h : Cube m) :
    Fin (translations m).length :=
  firstIndex (fun j => ones (rowMap rows (xorBits h ((translations m).get j))))
    (translations_half_coverage m hm rows hr h)

theorem pick_valid (m : ℕ) (hm : 0 < m)
    (rows : Fin m → Cube m) (hr : ∀ i, rows i ≠ zeroBits m) (h : Cube m) :
    ones (rowMap rows (xorBits h ((translations m).get (pick m hm rows hr h)))) ≤ m/2 :=
  firstIndex_valid (m := m)
    (fun j => ones (rowMap rows (xorBits h ((translations m).get j))))
    (translations_half_coverage m hm rows hr h)

theorem pick_first (m : ℕ) (hm : 0 < m)
    (rows : Fin m → Cube m) (hr : ∀ i, rows i ≠ zeroBits m) (h : Cube m)
    (j : Fin (translations m).length) (hj : j < pick m hm rows hr h) :
    m/2 < ones (rowMap rows (xorBits h ((translations m).get j))) :=
  firstIndex_minimal _ _ j hj

theorem pair_count (m : ℕ) :
    Fintype.card (Fin (translations m).length × Fin (translations m).length) = 4096*m^6 := by
  simp only [Fintype.card_prod,Fintype.card_fin,translations_length]
  ring

/-- Coordinate maps may differ between good sets; every selected index is
valid for the same good set that selected it. -/
theorem family_pick_valid {A : Type*} (m : ℕ) (hm : 0 < m)
    (rows : A → Fin m → Cube m) (hr : ∀ Q i, rows Q i ≠ zeroBits m)
    (Q : A) (h : Cube m) :
    ones (rowMap (rows Q) (xorBits h ((translations m).get (pick m hm (rows Q) (hr Q) h)))) ≤ m/2 :=
  pick_valid m hm (rows Q) (hr Q) h

theorem invertible_pick_valid (m : ℕ) (hm : 0 < m)
    (rows : Fin m → Cube m) (hs : Function.Surjective (rowMap rows)) (h : Cube m) :
    ones (rowMap rows (xorBits h ((translations m).get
      (pick m hm rows (nonzero_rows_of_surjective rows hs) h)))) ≤ m/2 :=
  pick_valid m hm rows (nonzero_rows_of_surjective rows hs) h

#print axioms pick_valid
#print axioms pick_first
#print axioms pair_count
#print axioms family_pick_valid
#print axioms invertible_pick_valid

end ThinMatrix.HalfSourceSelector
