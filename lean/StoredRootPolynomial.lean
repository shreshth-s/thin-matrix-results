import RetainedChannelPowerset

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! Polynomial tensor contractions of actual stored complete root rows.
This changes only the proof representation; it creates no runtime polynomial
and drops no formal degree or cyclic coefficient. -/
namespace ThinMatrix.StoredRootPolynomial
open BinaryResidualPolynomial CroppedGroupedSuffix
open scoped BigOperators

noncomputable def query {N F q : ℕ} [NeZero q] (rows : Vector (Block F q) (3^N))
    (forms : Fin N → Fin 3 → ℤ) : Polynomial (CyclicRing.Cyclic q) :=
  ∑ w : Word N, ((∏ i, forms i (w i) : ℤ) : Polynomial (CyclicRing.Cyclic q))*
    ResidualPolynomialDegree.decode (rows.get (StoredGroupedCompletion.rawIndex N w))

theorem polynomialOf_query {N F q : ℕ} [NeZero q] (rows : Vector (Block F q) (3^N))
    (forms : Fin N → Fin 3 → ℤ) :
    CompletedRootProducts.polynomialOf (fun d r => EncoderCorrectness.tensorSum (fun _ : Fin N => 3) forms
      (fun w => cellView (rows.get (StoredGroupedCompletion.rawIndex N w)) d r))=query rows forms := by
  apply Polynomial.ext; intro n; funext r
  rw [CompletedRootProducts.polynomialOf_coeff]
  simp only [query,Polynomial.finsetSum_coeff,CyclicRing.sum_coeff,Polynomial.coeff_intCast_mul,
    CyclicRing.intCast_mul_coeff,ResidualPolynomialDegree.decode_coeff]
  split_ifs
  · unfold EncoderCorrectness.tensorSum
    apply Finset.sum_congr rfl; intro w _; ring
  · simp

theorem cast_decode {n k F G q : ℕ} [NeZero q] (hn : n=k) (hf : F=G)
    (rows : Vector (Block F q) (3^n)) (w : Word k) :
    ResidualPolynomialDegree.decode ((cast (by rw [hn,hf]) rows : Vector (Block G q) (3^k)).get
      (StoredGroupedCompletion.rawIndex k w))=
      ResidualPolynomialDegree.decode (rows.get (StoredGroupedCompletion.rawIndex n (fun i => w (Fin.cast hn i)))) := by
  cases hn; cases hf; rfl

theorem produced_row {L m q : ℕ} [NeZero q] (raw : BinarySourceFormation.RawStore L q)
    (a b : ResidualFamilyKeys.Mask L m) (c : ResidualFamilyKeys.Channel m)
    (w : Word (2*(L-m))) :
    ResidualPolynomialDegree.decode ((ResidualWindowSource.rows (RetainedResidualFamily.produce raw a b c).value).get
      (StoredGroupedCompletion.rawIndex _ w))=
      ResidualPolynomialDegree.polynomial (m/2) raw a.bits b.bits
        (RetainedResidualFamily.normalKey a c) (RetainedResidualFamily.oppositeKey b c)
        (Vector.ofFn (fun i => w (Fin.cast (by rw [ResidualFamilyKeys.remaining_size,ResidualFamilyKeys.remaining_size,two_mul]) (Fin.castAdd (ResidualLayout.remaining b.bits).length i))))
        (Vector.ofFn (fun i => w (Fin.cast (by rw [ResidualFamilyKeys.remaining_size,ResidualFamilyKeys.remaining_size,two_mul]) (Fin.natAdd (ResidualLayout.remaining a.bits).length i)))) := by
  calc
    _ = ResidualPolynomialDegree.decode ((RetainedResidualFamily.produce raw a b c).value.rows.get
        (StoredGroupedCompletion.rawIndex _ (fun i => w (Fin.cast (by rw [ResidualFamilyKeys.remaining_size,ResidualFamilyKeys.remaining_size,two_mul]) i)))) :=
      cast_decode (by rw [ResidualFamilyKeys.remaining_size,ResidualFamilyKeys.remaining_size,two_mul])
        (congrArg (·+1) (ResidualFamilyKeys.selected_size a)) (RetainedResidualFamily.produce raw a b c).value.rows w
    _ = _ := RetainedResidualFamily.produce_polynomial raw a b c _

#print axioms polynomialOf_query
#print axioms cast_decode
#print axioms produced_row
end ThinMatrix.StoredRootPolynomial
