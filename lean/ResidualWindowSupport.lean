import ResidualWindowSource

set_option autoImplicit false

/-! Transfer complete-polynomial rare support to every copied integer column.
No support hypothesis is required for a produced root. -/
namespace ThinMatrix.ResidualWindowSupport
open WalshEmbedding BinaryCell BinaryResidualPolynomial ResidualFamilyKeys RetainedResidualFamily
open ResidualWindowSource
open scoped BigOperators

theorem cast_bound {N M F G C : ℕ} (hn : N=M) (hf : F=G)
    (xs : Vector (Block F C) N) (A : ℕ) (ha : ∀ i, Bound A (xs.get i)) :
    ∀ i, Bound A ((cast (by rw [hn,hf]) xs : Vector (Block G C) M).get i) := by
  cases hn; cases hf; exact ha

theorem produce_bound {L m C : ℕ} (raw : BinarySourceFormation.RawStore L C)
    (a b : Mask L m) (c : Channel m) (A : ℕ) (ha : BinaryResidualLeaf.RawBound raw A) :
    BoundRows (produce raw a b c).value (2^m*(4^m*A)) := by
  exact cast_bound (by rw [remaining_size,remaining_size,two_mul])
    (congrArg (·+1) (selected_size a)) _ _ (RetainedResidualFamily.produce_bound raw a b c A ha)

theorem ones_cast {a b : ℕ} (h : a=b) (v : Vector Bool a) : ones (v.cast h).get=ones v.get := by
  cases h; rfl

theorem cast_raw_get {n k F C : ℕ} (h : n=k) (xs : Vector (Block F C) (3^n))
    (w : CroppedGroupedSuffix.Word k) :
    (cast (congrArg (fun n => Vector (Block F C) (3^n)) h) xs).get (StoredGroupedCompletion.rawIndex k w)=
      xs.get (StoredGroupedCompletion.rawIndex n (fun i => w (Fin.cast h i))) := by
  cases h
  rfl

/-- Cast only the dimensions; the word order is normal positions followed by
opposite positions. This lemma transports a coefficient support contract. -/
theorem cast_support {kN kO k F G C : ℕ} (hn : kN=k) (ho : kO=k) (hf : F=G)
    (xs : Vector (Block F C) (3^(kN+kO))) (cn co cap : ℕ)
    (hs : ∀ (w : CroppedGroupedSuffix.Word (kN+kO)) (d : Fin F) (r : Fin C),
      cellView (xs.get (StoredGroupedCompletion.rawIndex _ w)) d r≠0 →
      cn+DistinguishedResidualSupport.rareCount (fun i => w (Fin.castAdd _ i))≤cap ∧
      co+DistinguishedResidualSupport.rareCount (fun i => w (Fin.natAdd _ i))≤cap)
    (w : CroppedGroupedSuffix.Word (2*k)) (d : Fin G) (r : Fin C)
    (h : cellView ((cast (by rw [hn,ho,hf,two_mul]) xs : Vector (Block G C) (3^(2*k))).get
      (StoredGroupedCompletion.rawIndex _ w)) d r≠0) :
    cn+CyclicLightWindow.count (BinaryWindowPartition.bits true w)≤cap ∧
    co+CyclicLightWindow.count (BinaryWindowPartition.bits false w)≤cap := by
  cases hn; cases ho; cases hf
  let old : CroppedGroupedSuffix.Word (kN+kN) := fun i => w (Fin.cast (by omega) i)
  have hi : (cast (by rw [two_mul]) xs : Vector (Block F C) (3^(2*kN))).get
      (StoredGroupedCompletion.rawIndex _ w)=xs.get (StoredGroupedCompletion.rawIndex _ old) := by
    exact cast_raw_get (by omega) xs w
  rw [hi] at h
  have ht := hs old d r h
  have htN : DistinguishedResidualSupport.rareCount (fun i => old (Fin.castAdd kN i))=
      CyclicLightWindow.count (BinaryWindowPartition.bits true w) := by
    simp only [DistinguishedResidualSupport.rareCount,DistinguishedResidualSupport.ones_count]
    congr 1
  have htO : DistinguishedResidualSupport.rareCount (fun i => old (Fin.natAdd kN i))=
      CyclicLightWindow.count (BinaryWindowPartition.bits false w) := by
    simp only [DistinguishedResidualSupport.rareCount,DistinguishedResidualSupport.ones_count]
    congr 1
  simpa only [htN,htO] using ht

theorem produce_support {L m C : ℕ} [NeZero C] (raw : BinarySourceFormation.RawStore L C)
    (a b : Mask L m) (c : Channel m) (w : CroppedGroupedSuffix.Word (2*(L-m)))
    (d : Fin (m+1)) (r : Fin C)
    (h : cellView ((rows (produce raw a b c).value).get (StoredGroupedCompletion.rawIndex _ w)) d r≠0) :
    ones (normal c).get+CyclicLightWindow.count (BinaryWindowPartition.bits true w) ≤ m/2 ∧
    ones (opposite c).get+CyclicLightWindow.count (BinaryWindowPartition.bits false w) ≤ m/2 := by
  apply cast_support (remaining_size a) (remaining_size b) (congrArg (·+1) (selected_size a))
    (produce raw a b c).value.rows _ _ _ ?_ w d r h
  intro word degree residue hz
  have hp : ResidualPolynomialDegree.decode
      ((CompleteResidualArray.execute (m/2) raw a.bits b.bits (normalKey a c) (oppositeKey b c)).value.get
        (StoredGroupedCompletion.rawIndex _ word))≠0 := by
    intro he
    have hc := congrArg (fun p : Polynomial (CyclicRing.Cyclic C) => (p.coeff degree.val) residue) he
    simp only [ResidualPolynomialDegree.decode_coeff,degree.isLt,↓reduceDIte,Polynomial.coeff_zero] at hc
    exact hz hc
  have hs := CompleteResidualArray.execute_support (m/2) raw a.bits b.bits
    ((selected_size b).trans (selected_size a).symm) (normalKey a c) (oppositeKey b c) word hp
  simpa only [normalKey,oppositeKey,ones_cast] using hs

/-- A nonzero stored coefficient implies the selected remaining cap. -/
theorem selected_support {L m C : ℕ} [NeZero C] (raw : BinarySourceFormation.RawStore L C)
    (a b : Mask L m) (c : Channel m) (w : CroppedGroupedSuffix.Word (2*(L-m))) (col : Fin ((m+1)*C))
    (h : BinaryWindowPartition.sourceValue (execute (produce raw a b c).value).value w col≠0) :
    CyclicLightWindow.count (BinaryWindowPartition.bits
      (decide (ones (opposite c).get≤ones (normal c).get)) w)≤
        m/2-max (ones (normal c).get) (ones (opposite c).get) := by
  obtain ⟨⟨d,r⟩,rfl⟩ := finProdFinEquiv.surjective col
  have hz : cellView ((rows (produce raw a b c).value).get (StoredGroupedCompletion.rawIndex _ w)) d r≠0 := by
    simpa only [BinaryWindowPartition.sourceValue,ResidualWindowSource.execute_get] using h
  have hs := produce_support raw a b c w d r hz
  by_cases hn : ones (opposite c).get≤ones (normal c).get
  · simp only [hn,decide_true,Nat.max_eq_left hn]
    omega
  · simp only [hn,decide_false,Nat.max_eq_right (by omega : ones (normal c).get≤ones (opposite c).get)]
    omega

#print axioms cast_bound
#print axioms produce_bound
#print axioms ones_cast
#print axioms cast_raw_get
#print axioms cast_support
#print axioms produce_support
#print axioms selected_support
end ThinMatrix.ResidualWindowSupport
