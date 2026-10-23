import TranslatedCroppedEmbedding
import HalfSourceSelector

set_option autoImplicit false

/-!
# The actual inverse of a good binary restriction

Enumerate Q by Fin m, express its inverse as binary rows, and identify the
row Hamming weight with the cardinality of the inverse supported subset.
No independent invertibility or weight-identity assumption is introduced.
-/

namespace ThinMatrix.ExactHalfGoodMap
open ThinMatrix.GoodSets ThinMatrix.GoodSetConstruction ThinMatrix.GoodMapEmbedding
open ThinMatrix.WalshEmbedding ThinMatrix.HalfSourceCoverage
open scoped BigOperators
noncomputable section

lemma encodeBool_and (a b : Bool) : encodeBool (a && b) = encodeBool a * encodeBool b := by
  cases a <;> cases b <;> rfl

lemma encodeBool_parity (bs : List Bool) :
    encodeBool (parity bs) = (bs.map encodeBool).sum := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp only [parity, encodeBool_xor, List.map_cons, List.sum_cons, ih]

lemma encodeBool_dot {m : ℕ} (a b : Cube m) :
    encodeBool (dotBits a b) = ∑ i, encodeBool (a i) * encodeBool (b i) := by
  simp only [dotBits, encodeBool_parity, List.map_ofFn, List.sum_ofFn, Function.comp_def, encodeBool_and]

/-- Enumerate the supported coordinates without changing their membership. -/
def coordinates {L m : ℕ} (Q : Finset (Fin L)) (hQ : Q.card = m) : Fin m ≃ Q :=
  (Fintype.equivFinOfCardEq (by simpa using hQ)).symm

/-- The inverse of the genuine restricted finite-field column map. -/
def inverseLinear {L m : ℕ} (Γ : BinaryMap m L)
    (Q : Finset (Fin L)) (hQ : Q.card = m)
    (hΓ : LinearIndependent F₂ (fun i : Q => Γ i)) :
    (Fin m → F₂) ≃ₗ[F₂] (Q → F₂) :=
  (LinearEquiv.ofBijective (Fintype.linearCombination F₂ (fun i : Q => Γ i))
    (restricted_linearCombination_bijective Γ Q hQ hΓ)).symm

/-- Binary rows of the inverse, read in the enumerated supported coordinates. -/
def inverseRows {L m : ℕ} (Γ : BinaryMap m L)
    (Q : Finset (Fin L)) (hQ : Q.card = m)
    (hΓ : LinearIndependent F₂ (fun i : Q => Γ i)) : Fin m → Cube m :=
  fun i j => boolF2Equiv.symm (inverseLinear Γ Q hQ hΓ (Pi.single j 1) (coordinates Q hQ i))

lemma inverseLinear_eq {L m : ℕ} (Γ : BinaryMap m L)
    (Q : Finset (Fin L)) (hQ : Q.card = m)
    (hΓ : LinearIndependent F₂ (fun i : Q => Γ i)) (h : Cube m) :
    inverseLinear Γ Q hQ hΓ (cubeF2Equiv m h) =
      subsetCoefficients Q ((restrictedEquiv Γ Q hQ hΓ).symm h) := by
  apply (restricted_linearCombination_bijective Γ Q hQ hΓ).1
  change (inverseLinear Γ Q hQ hΓ).symm
    (inverseLinear Γ Q hQ hΓ (cubeF2Equiv m h)) = _
  rw [LinearEquiv.symm_apply_apply]
  symm
  rw [← restricted_cubeMap_encode, restrictedEquiv_spec Γ Q hQ hΓ]
  exact congrArg (cubeF2Equiv m) ((restrictedEquiv Γ Q hQ hΓ).apply_symm_apply h)

lemma inverseRows_spec {L m : ℕ} (Γ : BinaryMap m L)
    (Q : Finset (Fin L)) (hQ : Q.card = m)
    (hΓ : LinearIndependent F₂ (fun i : Q => Γ i)) (h : Cube m) :
    rowMap (inverseRows Γ Q hQ hΓ) h =
      fun i => subsetBitsEquiv Q ((restrictedEquiv Γ Q hQ hΓ).symm h) (coordinates Q hQ i) := by
  funext i
  apply boolF2Equiv.injective
  change encodeBool (dotBits _ _) = _
  rw [encodeBool_dot]
  simp only [inverseRows, show ∀ a, encodeBool (boolF2Equiv.symm a) = a from
    fun a => boolF2Equiv.apply_symm_apply a]
  have hexpand : cubeF2Equiv m h = ∑ j, encodeBool (h j) • (Pi.single j 1 : Fin m → F₂) := by
    funext j
    simp [Finset.sum_apply, Pi.single_apply]
  have he := congrFun (congrArg (inverseLinear Γ Q hQ hΓ) hexpand) (coordinates Q hQ i)
  rw [map_sum] at he
  simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at he
  rw [inverseLinear_eq] at he
  change _ = subsetCoefficients Q ((restrictedEquiv Γ Q hQ hΓ).symm h) (coordinates Q hQ i)
  simpa only [mul_comm] using he.symm

/-- Surjectivity is proved for the actual inverse rows. -/
theorem inverseRows_surjective {L m : ℕ} (Γ : BinaryMap m L)
    (Q : Finset (Fin L)) (hQ : Q.card = m)
    (hΓ : LinearIndependent F₂ (fun i : Q => Γ i)) :
    Function.Surjective (rowMap (inverseRows Γ Q hQ hΓ)) := by
  intro v
  refine ⟨restrictedEquiv Γ Q hQ hΓ ((subsetBitsEquiv Q).symm
    (fun q => v ((coordinates Q hQ).symm q))), ?_⟩
  rw [inverseRows_spec, Equiv.symm_apply_apply, Equiv.apply_symm_apply]
  simp only [Equiv.symm_apply_apply]

/-- Weight is exactly the cardinality of the inverse supported subset. -/
def inverseWeight {L m : ℕ} (Γ : BinaryMap m L)
    (Q : Finset (Fin L)) (hQ : Q.card = m)
    (hΓ : LinearIndependent F₂ (fun i : Q => Γ i)) (h : Cube m) : ℕ :=
  ((restrictedEquiv Γ Q hQ hΓ).symm h).val.card

theorem inverseRows_weight {L m : ℕ} (Γ : BinaryMap m L)
    (Q : Finset (Fin L)) (hQ : Q.card = m)
    (hΓ : LinearIndependent F₂ (fun i : Q => Γ i)) (h : Cube m) :
    ones (rowMap (inverseRows Γ Q hQ hΓ) h) = inverseWeight Γ Q hQ hΓ h := by
  rw [inverseRows_spec]
  let T := (restrictedEquiv Γ Q hQ hΓ).symm h
  change (Finset.univ.filter (fun i => subsetBitsEquiv Q T (coordinates Q hQ i))).card = T.val.card
  apply Finset.card_bij (fun i _ => (coordinates Q hQ i).val)
  · intro i hi
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and,
      subsetBitsEquiv_apply, decide_eq_true_eq] using hi
  · intro i _ j _ hij
    exact (coordinates Q hQ).injective (Subtype.ext hij)
  · intro q hq
    refine ⟨(coordinates Q hQ).symm ⟨q, T.property hq⟩, ?_, ?_⟩
    · simp [subsetBitsEquiv_apply, hq]
    · simp

theorem inverseWeight_supported {L m : ℕ} (Γ : BinaryMap m L)
    (Q : Finset (Fin L)) (hQ : Q.card = m)
    (hΓ : LinearIndependent F₂ (fun i : Q => Γ i)) (T : Subsets Q) :
    inverseWeight Γ Q hQ hΓ (cubeMap Γ (setBits T.val)) = T.val.card := by
  rw [restrictedEquiv_spec Γ Q hQ hΓ]
  simp [inverseWeight]

#print axioms encodeBool_and
#print axioms encodeBool_parity
#print axioms encodeBool_dot
#print axioms inverseLinear_eq
#print axioms inverseRows_spec
#print axioms inverseRows_surjective
#print axioms inverseRows_weight
#print axioms inverseWeight_supported
end
end ThinMatrix.ExactHalfGoodMap
