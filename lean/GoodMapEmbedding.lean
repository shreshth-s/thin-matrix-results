import GoodSetConstruction
import RawWordBijection

/-!
# Constructed binary good maps in the genuine raw Walsh source embedding

The restricted Boolean frequency/inner bijections are derived from the actual
constructed F₂ column maps and their proved linear independence. The output
locator is the original transpose Delta character map. Only the complete scaled
raw numerator is identified; division is not asserted over arbitrary rings.
-/

namespace ThinMatrix.GoodMapEmbedding
open scoped BigOperators
open GoodSets GoodSetConstruction WalshEmbedding

/-- Explicit Boolean bit encoding in the two-element field. -/
def encodeBool (b : Bool) : F₂ := if b then 1 else 0

def boolF2Equiv : Bool ≃ F₂ where
  toFun := encodeBool
  invFun := fun a => decide (a.val = 1)
  left_inv b := by cases b <;> rfl
  right_inv a := by
    fin_cases a
    · rfl
    · rfl

/-- Coordinatewise encoding; both directions are executable. -/
def cubeF2Equiv (k : ℕ) : Cube k ≃ (Fin k → F₂) where
  toFun := fun a i => encodeBool (a i)
  invFun := fun a i => boolF2Equiv.symm (a i)
  left_inv a := by
    funext i
    exact boolF2Equiv.left_inv (a i)
  right_inv a := by
    funext i
    exact boolF2Equiv.right_inv (a i)

@[simp] theorem cubeF2Equiv_apply {k : ℕ} (a : Cube k) (i : Fin k) :
    cubeF2Equiv k a i = encodeBool (a i) := rfl

@[simp] theorem encodeBool_false : encodeBool false = 0 := rfl
@[simp] theorem encodeBool_true : encodeBool true = 1 := rfl

lemma encodeBool_xor (a b : Bool) :
    encodeBool (Bool.xor a b) = encodeBool a + encodeBool b := by
  cases a <;> cases b <;> decide

@[simp] lemma cubeF2Equiv_zero (k : ℕ) :
    cubeF2Equiv k (zeroBits k) = 0 := by
  funext i
  rfl

lemma cubeF2Equiv_xor {k : ℕ} (a b : Cube k) :
    cubeF2Equiv k (xorBits a b) = cubeF2Equiv k a + cubeF2Equiv k b := by
  funext i
  exact encodeBool_xor (a i) (b i)

lemma cubeF2Equiv_xorFold {k : ℕ} (as : List (Cube k)) :
    cubeF2Equiv k (xorFold as) = (as.map (cubeF2Equiv k)).sum := by
  induction as with
  | nil => simp [xorFold]
  | cons a as ih =>
    rw [xorFold, cubeF2Equiv_xor, ih]
    rfl

/-- Boolean column action is the finite F₂ linear combination after encoding. -/
theorem columnMap_conjugacy {n k : ℕ} (columns : Fin n → Cube k) (bits : Cube n) :
    cubeF2Equiv k (columnMap columns bits) =
      ∑ i, encodeBool (bits i) • cubeF2Equiv k (columns i) := by
  rw [columnMap, cubeF2Equiv_xorFold, List.map_ofFn, List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro i _
  cases hb : bits i <;> simp [hb]

/-- The same statement with mathlib's actual finite linear-combination map. -/
theorem columnMap_linearCombination {n k : ℕ} (columns : Fin n → Cube k)
    (bits : Cube n) :
    cubeF2Equiv k (columnMap columns bits) =
      Fintype.linearCombination F₂ (fun i => cubeF2Equiv k (columns i))
        (cubeF2Equiv n bits) := by
  simpa only [Fintype.linearCombination_apply, cubeF2Equiv_apply] using
    columnMap_conjugacy columns bits

/-- A binary matrix decoded columnwise acts by its own linear-combination map. -/
theorem decodedColumns_linearCombination {n k : ℕ} (Γ : BinaryMap k n)
    (bits : Cube n) :
    cubeF2Equiv k (columnMap (fun i => (cubeF2Equiv k).symm (Γ i)) bits) =
      Fintype.linearCombination F₂ Γ (cubeF2Equiv n bits) := by
  simpa only [Equiv.apply_symm_apply] using
    columnMap_linearCombination (fun i => (cubeF2Equiv k).symm (Γ i)) bits

/-- Linear independence transfers to the actual Boolean xor-column program. -/
theorem columnMap_injective_of_linearIndependent {n k : ℕ}
    (columns : Fin n → Cube k)
    (hLI : LinearIndependent F₂ (fun i => cubeF2Equiv k (columns i))) :
    Function.Injective (columnMap columns) := by
  intro a b hab
  apply (cubeF2Equiv n).injective
  apply (linearIndependent_iff_injective_fintypeLinearCombination.mp hLI)
  rw [← columnMap_linearCombination, ← columnMap_linearCombination]
  exact congrArg (cubeF2Equiv k) hab

/-- A square independent restriction gives the frequency bijection needed by Walsh. -/
theorem columnMap_bijective_of_linearIndependent {k : ℕ}
    (columns : Fin k → Cube k)
    (hLI : LinearIndependent F₂ (fun i => cubeF2Equiv k (columns i))) :
    Function.Bijective (columnMap columns) :=
  Finite.injective_iff_bijective.mp (columnMap_injective_of_linearIndependent columns hLI)


/-- Independence of a square restriction makes its actual finite linear
combination map bijective. Surjectivity is derived from the finite equal-cardinality
argument, rather than assumed as a matrix-invertibility interface. -/
theorem square_linearCombination_bijective {I : Type*} [Fintype I]
    {r : ℕ} (v : I → (Fin r → F₂)) (hI : Fintype.card I = r)
    (hv : LinearIndependent F₂ v) :
    Function.Bijective (Fintype.linearCombination F₂ v) := by
  classical
  have hcard : Fintype.card (I → F₂) = Fintype.card (Fin r → F₂) := by
    simp [hI]
  let e : (I → F₂) ≃ (Fin r → F₂) := Fintype.equivOfCardEq hcard
  have hinj := hv.fintypeLinearCombination_injective
  exact ⟨hinj, (Finite.injective_iff_surjective_of_equiv e).mp hinj⟩

/-- The resulting equivalence has the genuine linear-combination map as its
forward function. Its inverse is only used after bijectivity has been proved. -/
noncomputable def square_linearCombination_equiv {I : Type*} [Fintype I]
    {r : ℕ} (v : I → (Fin r → F₂)) (hI : Fintype.card I = r)
    (hv : LinearIndependent F₂ v) :
    (I → F₂) ≃ (Fin r → F₂) :=
  Equiv.ofBijective (Fintype.linearCombination F₂ v)
    (square_linearCombination_bijective v hI hv)

@[simp] theorem square_linearCombination_equiv_apply {I : Type*} [Fintype I]
    {r : ℕ} (v : I → (Fin r → F₂)) (hI : Fintype.card I = r)
    (hv : LinearIndependent F₂ v) (c : I → F₂) :
    square_linearCombination_equiv v hI hv c = ∑ i, c i • v i := by
  simp [square_linearCombination_equiv, Fintype.linearCombination_apply]

/-- In particular, a good selected restriction has a bijective column map. -/
theorem restricted_linearCombination_bijective {L r : ℕ}
    (Γ : BinaryMap r L) (Q : Finset (Fin L)) (hQ : Q.card = r)
    (hΓ : LinearIndependent F₂ (fun i : Q => Γ i)) :
    Function.Bijective (Fintype.linearCombination F₂ (fun i : Q => Γ i)) := by
  apply square_linearCombination_bijective _ _ hΓ
  simpa using hQ

/-- The same result stated as the exact finite sum used by the embedding. -/
theorem square_sum_bijective {I : Type*} [Fintype I]
    {r : ℕ} (v : I → (Fin r → F₂)) (hI : Fintype.card I = r)
    (hv : LinearIndependent F₂ v) :
    Function.Bijective (fun c : I → F₂ => ∑ i, c i • v i) := by
  have hfun : (fun c : I → F₂ => ∑ i, c i • v i) =
      Fintype.linearCombination F₂ v := by
    funext c
    exact (Fintype.linearCombination_apply F₂ v c).symm
  rw [hfun]
  exact square_linearCombination_bijective v hI hv


/-- Extend Boolean coordinates on Q by false outside Q. -/
def extendBits {L : ℕ} (Q : Finset (Fin L)) (b : Q → Bool) : Cube L :=
  fun i => if h : i ∈ Q then b ⟨i, h⟩ else false

@[simp] theorem extendBits_mem {L : ℕ} (Q : Finset (Fin L)) (b : Q → Bool)
    (i : Q) : extendBits Q b i = b i := by
  simp [extendBits, i.property]

@[simp] theorem extendBits_not_mem {L : ℕ} (Q : Finset (Fin L)) (b : Q → Bool)
    (i : Fin L) (hi : i ∉ Q) : extendBits Q b i = false := by
  simp [extendBits, hi]

/-- A Boolean coordinate vector chooses exactly the corresponding subset. -/
def bitsSubset {L : ℕ} (Q : Finset (Fin L)) (b : Q → Bool) : Subsets Q :=
  ⟨Q.filter (fun i => extendBits Q b i), Finset.filter_subset _ _⟩

@[simp] theorem mem_bitsSubset {L : ℕ} (Q : Finset (Fin L)) (b : Q → Bool)
    (i : Q) : i.val ∈ (bitsSubset Q b).val ↔ b i = true := by
  simp [bitsSubset, i.property]

/-- Subsets of Q are in explicit bijection with Boolean membership coordinates. -/
def subsetBitsEquiv {L : ℕ} (Q : Finset (Fin L)) : Subsets Q ≃ (Q → Bool) where
  toFun T i := decide (i.val ∈ T.val)
  invFun := bitsSubset Q
  left_inv T := by
    apply Subtype.ext
    ext i
    by_cases hi : i ∈ Q
    · simp [bitsSubset, extendBits, hi]
    · have ht : i ∉ T.val := fun hit => hi (T.property hit)
      simp [bitsSubset, extendBits, hi, ht]
  right_inv b := by
    funext i
    simp [bitsSubset, i.property]

@[simp] theorem subsetBitsEquiv_apply {L : ℕ} (Q : Finset (Fin L))
    (T : Subsets Q) (i : Q) : subsetBitsEquiv Q T i = decide (i.val ∈ T.val) := rfl

@[simp] theorem subsetBitsEquiv_symm_apply {L : ℕ} (Q : Finset (Fin L))
    (b : Q → Bool) : (subsetBitsEquiv Q).symm b = bitsSubset Q b := rfl

/-- The full Boolean extension is exactly the existing global membership vector. -/
theorem extendBits_subsetBitsEquiv {L : ℕ} (Q : Finset (Fin L))
    (T : Subsets Q) : extendBits Q (subsetBitsEquiv Q T) = setBits T.val := by
  funext i
  by_cases hi : i ∈ Q
  · simp [extendBits, subsetBitsEquiv, setBits, hi]
  · have ht : i ∉ T.val := fun hit => hi (T.property hit)
    simp [extendBits, setBits, hi, ht]

/-- Filtering a coordinate vector and taking global membership recovers its extension. -/
theorem setBits_bitsSubset {L : ℕ} (Q : Finset (Fin L)) (b : Q → Bool) :
    setBits (bitsSubset Q b).val = extendBits Q b := by
  rw [← extendBits_subsetBitsEquiv Q (bitsSubset Q b)]
  rw [← subsetBitsEquiv_symm_apply Q b, Equiv.apply_symm_apply]

/-- Restriction of the existing global membership vector is the explicit equivalence. -/
theorem setBits_restrict {L : ℕ} (Q : Finset (Fin L)) (T : Subsets Q) :
    (fun i : Q => setBits T.val i) = subsetBitsEquiv Q T := rfl


/-- Boolean columns of the actual finite-field map. -/
def boolColumns {L r : ℕ} (Γ : BinaryMap r L) : Fin L → Cube r :=
  fun i => (cubeF2Equiv r).symm (Γ i)

@[simp] lemma boolColumns_encode {L r : ℕ} (Γ : BinaryMap r L) (i : Fin L) :
    cubeF2Equiv r (boolColumns Γ i) = Γ i := (cubeF2Equiv r).apply_symm_apply _

/-- The complete Boolean map acts by xor of the actual constructed columns. -/
def cubeMap {L r : ℕ} (Γ : BinaryMap r L) : Cube L → Cube r :=
  columnMap (boolColumns Γ)

/-- The actual deterministically chosen good-slot family. -/
def goodSlots (L m : ℕ) : Finset (Finset (Fin L)) :=
  (Finset.univ.powersetCard m).filter (fun Q =>
    restrictionTest (constructGoodMaps L m).1 Q &&
    restrictionTest (constructGoodMaps L m).2 Qᶜ)

lemma mem_goodSlots (L m : ℕ) (Q : Finset (Fin L)) :
    Q ∈ goodSlots L m ↔ Good (constructGoodMaps L m).1 (constructGoodMaps L m).2 Q := by
  classical
  simp [goodSlots, Good, restrictionTest_correct, Finset.mem_powersetCard]

lemma goodSlots_size (L m : ℕ) (Q : Finset (Fin L)) (hQ : Q ∈ goodSlots L m) :
    Q.card = m := ((mem_goodSlots L m Q).mp hQ).1

/-- Finite density is preserved when the candidate subtype is materialized. -/
def acceptedEquiv (L m : ℕ) :
    {Q : Candidate L m // Good (constructGoodMaps L m).1 (constructGoodMaps L m).2 Q} ≃
      ↥(goodSlots L m) where
  toFun Q := ⟨Q.1.1, (mem_goodSlots L m Q.1.1).mpr Q.2⟩
  invFun Q := ⟨⟨Q.1, Finset.mem_powersetCard.mpr
      ⟨Finset.subset_univ _, goodSlots_size L m Q.1 Q.2⟩⟩,
    (mem_goodSlots L m Q.1).mp Q.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem goodSlots_density (L m : ℕ) :
    Nat.choose L m ≤ 16 * (goodSlots L m).card := by
  have h := constructGoodMaps_correct L m
  rw [Nat.card_congr (acceptedEquiv L m)] at h
  simpa using h


/-- The subset's actual F₂ membership coefficients on its containing set. -/
def subsetCoefficients {L : ℕ} (Q : Finset (Fin L)) : Subsets Q ≃ (Q → F₂) :=
  (subsetBitsEquiv Q).trans (Equiv.arrowCongr (Equiv.refl Q) boolF2Equiv)

lemma restricted_cubeMap_encode {L r : ℕ} (Γ : BinaryMap r L)
    (Q : Finset (Fin L)) (T : Subsets Q) :
    cubeF2Equiv r (cubeMap Γ (setBits T.val)) =
      Fintype.linearCombination F₂ (fun i : Q => Γ i) (subsetCoefficients Q T) := by
  classical
  rw [cubeMap, columnMap_conjugacy]
  simp only [boolColumns_encode, Fintype.linearCombination_apply]
  calc
    _ = ∑ i ∈ Q, encodeBool (setBits T.val i) • Γ i := by
      symm
      apply Finset.sum_subset (Finset.subset_univ Q)
      intro i _ hi
      have ht : i ∉ T.val := fun h => hi (T.property h)
      simp [setBits, ht]
    _ = ∑ i : Q, encodeBool (setBits T.val i) • Γ i :=
      Finset.sum_subtype Q (by simp) _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      rfl

/-- Derive the restriction equivalence from the actual column independence.
The forward map is the original full-map action on a supported subset. -/
noncomputable def restrictedEquiv {L r : ℕ} (Γ : BinaryMap r L)
    (Q : Finset (Fin L)) (hQ : Q.card = r)
    (hΓ : LinearIndependent F₂ (fun i : Q => Γ i)) : Subsets Q ≃ Cube r :=
  (subsetCoefficients Q).trans
    ((square_linearCombination_equiv (fun i : Q => Γ i) (by simpa using hQ) hΓ).trans
      (cubeF2Equiv r).symm)

lemma restrictedEquiv_spec {L r : ℕ} (Γ : BinaryMap r L)
    (Q : Finset (Fin L)) (hQ : Q.card = r)
    (hΓ : LinearIndependent F₂ (fun i : Q => Γ i)) (T : Subsets Q) :
    cubeMap Γ (setBits T.val) = restrictedEquiv Γ Q hQ hΓ T := by
  apply (cubeF2Equiv r).injective
  rw [restricted_cubeMap_encode]
  simp only [restrictedEquiv, Equiv.trans_apply, Equiv.apply_symm_apply,
    square_linearCombination_equiv, Equiv.ofBijective_apply]

/-- Build the genuine Γ/Δ restriction interface without assumed bijections. -/
noncomputable def constructedRestrictedGoodMaps (L m : ℕ)
    (QL QR : Finset (Fin L)) (hQL : QL ∈ goodSlots L m) (hQR : QR ∈ goodSlots L m) :
    RestrictedGoodMaps QL QR
      (cubeMap (constructGoodMaps L m).1) (cubeMap (constructGoodMaps L m).2) := by
  have hL := (mem_goodSlots L m QL).mp hQL
  have hR := (mem_goodSlots L m QR).mp hQR
  have hcL : QLᶜ.card = L-m := by rw [Finset.card_compl]; simp [hL.1]
  have hcR : QRᶜ.card = L-m := by rw [Finset.card_compl]; simp [hR.1]
  exact {
    gammaL := restrictedEquiv _ QL hL.1 hL.2.1
    gammaR := restrictedEquiv _ QR hR.1 hR.2.1
    deltaL := restrictedEquiv _ QLᶜ hcL hL.2.2
    deltaR := restrictedEquiv _ QRᶜ hcR hR.2.2
    gammaL_spec := restrictedEquiv_spec _ QL hL.1 hL.2.1
    gammaR_spec := restrictedEquiv_spec _ QR hR.1 hR.2.1
    deltaL_spec := restrictedEquiv_spec _ QLᶜ hcL hL.2.2
    deltaR_spec := restrictedEquiv_spec _ QRᶜ hcR hR.2.2 }

/-- Unconditional raw A3--A4 embedding for the deterministically constructed maps.
The two outer locators remain the transpose Δ characters in A5. -/
theorem constructed_raw_embedding {R : Type*} [CommRing R]
    (L m : ℕ) (hm : m ≤ L)
    (X : RawLeftInput L m (L-m) R) (Y : RawRightInput L m (L-m) R)
    (QL QR : Finset (Fin L)) (hQL : QL ∈ goodSlots L m) (hQR : QR ∈ goodSlots L m)
    (iL iR : Cube L) (aL aR : Cube (L-m)) :
    rawContraction X Y (goodSlots L m)
      (cubeMap (constructGoodMaps L m).1) (cubeMap (constructGoodMaps L m).2)
      QL QR iL iR
      (transposeMap (boolColumns (constructGoodMaps L m).2) aR)
      (transposeMap (boolColumns (constructGoodMaps L m).2) aL) =
      (4:R)^L * ∑ h1, ∑ h2,
        X QL (outsideBits QL iL) aL h1 h2 * Y QR (outsideBits QR iR) h1 h2 aR := by
  rw [RawWordBijection.rawContraction_eq_survivingContraction X Y (goodSlots L m)
    (cubeMap (constructGoodMaps L m).1) (cubeMap (constructGoodMaps L m).2)
    QL QR iL iR _ _ (goodSlots_size L m QL hQL) (goodSlots_size L m QR hQR)
    (goodSlots_size L m)]
  have he := surviving_contraction_eq_scaled_product X Y (goodSlots L m)
    (cubeMap (constructGoodMaps L m).1) (boolColumns (constructGoodMaps L m).2)
    QL QR iL iR aL aR (goodSlots_size L m QL hQL) (goodSlots_size L m QR hQR)
    hQL hQR (constructedRestrictedGoodMaps L m QL QR hQL hQR)
  simpa only [cubeMap, Nat.add_sub_of_le hm] using he

#print axioms goodSlots_density
#print axioms restrictedEquiv_spec
#print axioms constructedRestrictedGoodMaps
#print axioms constructed_raw_embedding

end ThinMatrix.GoodMapEmbedding
