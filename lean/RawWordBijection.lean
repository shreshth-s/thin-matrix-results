import WalshEmbedding

/-!
# Reindexing the actual raw aligned source contraction

The sum below starts with every four-letter normal and three-letter
opposite word in A3--A4. Nonzero summands force the queried normal supports,
the fixed outside normal bits, and empty outside-w populations. This is a
finite reindexing statement and assumes no matrix-product output equality.
-/

namespace ThinMatrix.RawWordBijection

open ThinMatrix.WalshEmbedding
open scoped BigOperators

def p2Positions {L : ℕ} (n : Fin L → NormalLetter) : Finset (Fin L) :=
  Finset.univ.filter fun i => n i = .p2

def vPositions {L : ℕ} (o : Fin L → OppositeLetter) : Finset (Fin L) :=
  Finset.univ.filter fun i => o i = .v

def wPositions {L : ℕ} (o : Fin L → OppositeLetter) : Finset (Fin L) :=
  Finset.univ.filter fun i => o i = .w

@[simp] theorem mem_p2Positions {L : ℕ} (n : Fin L → NormalLetter) (i : Fin L) :
    i ∈ p2Positions n ↔ n i = .p2 := by simp [p2Positions]

@[simp] theorem mem_vPositions {L : ℕ} (o : Fin L → OppositeLetter) (i : Fin L) :
    i ∈ vPositions o ↔ o i = .v := by simp [vPositions]

@[simp] theorem mem_wPositions {L : ℕ} (o : Fin L → OppositeLetter) (i : Fin L) :
    i ∈ wPositions o ↔ o i = .w := by simp [wPositions]

theorem ones_normalP2Bits {L : ℕ} (n : Fin L → NormalLetter) :
    ones (normalP2Bits n) = (p2Positions n).card := by
  simp [ones, normalP2Bits, p2Positions]

theorem ones_oppositeWBits {L : ℕ} (o : Fin L → OppositeLetter) :
    ones (oppositeWBits o) = (wPositions o).card := by
  simp [ones, oppositeWBits, wPositions]

private theorem ordinary_normal_classification {R : Type*} [CommRing R]
    (i j : Bool) (n : NormalLetter) (hP : ¬normalIsP n)
    (hn : ordinaryNormal (R := R) i j n ≠ 0) : n = normalX i := by
  cases i <;> cases j <;> cases n <;>
    simp_all [ordinaryNormal, normalIsP, normalX]

def HalfCompatible {L : ℕ} (Q : Finset (Fin L)) (bits : Cube L)
    (n : Fin L → NormalLetter) (o : Fin L → OppositeLetter) : Prop :=
  normalSupport n = Q ∧
    (∀ i ∈ Q, (n i = .p1 ∧ o i = .s) ∨ (n i = .p2 ∧ o i = .w)) ∧
    ∀ i ∉ Q, n i = normalX (bits i)

theorem compatible_of_kernel_nonzero {R : Type*} [CommRing R] {L m : ℕ}
    (Q : Finset (Fin L)) (bits locator : Cube L)
    (n : Fin L → NormalLetter) (o : Fin L → OppositeLetter)
    (hQ : Q.card = m) (hncard : (normalSupport n).card = m)
    (hkernel : rawHalfKernel (R := R) Q bits locator n o ≠ 0) :
    HalfCompatible Q bits n o := by
  have hinner : (∏ i ∈ Q, innerCoefficient (R := R) (n i) (o i)) ≠ 0 := by
    intro hz
    exact hkernel (by simp [rawHalfKernel, hz])
  have hs := raw_normal_support_eq_query Q n o hQ hncard hinner
  refine ⟨hs, ?_, ?_⟩
  · intro i hi
    apply inner_support (R := R) (n i) (o i)
    intro hz
    exact hinner (Finset.prod_eq_zero hi hz)
  · intro i hi
    have hP : ¬normalIsP (n i) := by
      intro hp
      have hm : i ∈ normalSupport n := by simp [normalSupport, hp]
      rw [hs] at hm
      exact hi hm
    have hc : ordinaryNormal (R := R) (bits i) (locator i) (n i) ≠ 0 := by
      intro hz
      have hout : (∏ j ∈ Qᶜ,
          ordinaryNormal (R := R) (bits j) (locator j) (n j) *
          ordinaryOpposite (R := R) (bits j) (locator j) (o j)) = 0 := by
        apply Finset.prod_eq_zero (by simpa using hi)
        simp [hz]
      exact hkernel (by simp [rawHalfKernel, hout])
    exact ordinary_normal_classification _ _ _ hP hc

theorem compatible_p2_subset {L : ℕ} {Q : Finset (Fin L)} {bits : Cube L}
    {n : Fin L → NormalLetter} {o : Fin L → OppositeLetter}
    (h : HalfCompatible Q bits n o) : p2Positions n ⊆ Q := by
  intro i hi
  have hp : normalIsP (n i) := Or.inr ((mem_p2Positions n i).mp hi)
  have hm : i ∈ normalSupport n := by simp [normalSupport, hp]
  simpa only [h.1] using hm

theorem compatible_p2_subset_w {L : ℕ} {Q : Finset (Fin L)} {bits : Cube L}
    {n : Fin L → NormalLetter} {o : Fin L → OppositeLetter}
    (h : HalfCompatible Q bits n o) : p2Positions n ⊆ wPositions o := by
  intro i hi
  have hiQ := compatible_p2_subset h hi
  have hp := (mem_p2Positions n i).mp hi
  rcases h.2.1 i hiQ with hcase | hcase
  · simp_all
  · exact (mem_wPositions o i).mpr hcase.2

theorem compatible_v_subset {L : ℕ} {Q : Finset (Fin L)} {bits : Cube L}
    {n : Fin L → NormalLetter} {o : Fin L → OppositeLetter}
    (h : HalfCompatible Q bits n o) : vPositions o ⊆ Qᶜ := by
  intro i hi
  simp only [Finset.mem_compl]
  intro hiQ
  have hv := (mem_vPositions o i).mp hi
  rcases h.2.1 i hiQ with hcase | hcase <;> simp_all

theorem compatible_normal_canonical {L : ℕ} {Q : Finset (Fin L)} {bits : Cube L}
    {n : Fin L → NormalLetter} {o : Fin L → OppositeLetter}
    (h : HalfCompatible Q bits n o) :
    n = canonicalNormal Q bits ⟨p2Positions n, compatible_p2_subset h⟩ := by
  funext i
  by_cases hi : i ∈ Q
  · rcases h.2.1 i hi with hcase | hcase <;>
      simp [canonicalNormal, hi, hcase.1]
  · simpa [canonicalNormal, hi] using h.2.2 i hi

theorem compatible_opposite_canonical {L : ℕ} {Q : Finset (Fin L)} {bits : Cube L}
    {n : Fin L → NormalLetter} {o : Fin L → OppositeLetter}
    (h : HalfCompatible Q bits n o) (hW : wPositions o = p2Positions n) :
    o = canonicalOpposite Q ⟨p2Positions n, compatible_p2_subset h⟩
      ⟨vPositions o, compatible_v_subset h⟩ := by
  funext i
  by_cases hi : i ∈ Q
  · rcases h.2.1 i hi with hcase | hcase <;>
      simp [canonicalOpposite, hi, hcase.1, hcase.2]
  · have hnow : o i ≠ .w := by
      intro hw
      have hp : i ∈ p2Positions n := by rw [← hW]; exact (mem_wPositions o i).mpr hw
      exact hi (compatible_p2_subset h hp)
    cases ho : o i <;> simp_all [canonicalOpposite, oppositeBit]

theorem canonicalNormal_injective {L : ℕ} (Q : Finset (Fin L)) (bits : Cube L) :
    Function.Injective (canonicalNormal Q bits) := by
  intro T U h
  apply Subtype.ext
  ext i
  by_cases hi : i ∈ Q
  · have hc := congrFun h i
    by_cases ht : i ∈ T.val <;> by_cases hu : i ∈ U.val <;>
      simp_all [canonicalNormal]
  · have ht : i ∉ T.val := fun hm => hi (T.property hm)
    have hu : i ∉ U.val := fun hm => hi (U.property hm)
    simp [ht, hu]

theorem canonicalOpposite_v_injective {L : ℕ} (Q : Finset (Fin L))
    (T U : Subsets Q) (V W : Subsets Qᶜ)
    (h : canonicalOpposite Q T V = canonicalOpposite Q U W) : V = W := by
  apply Subtype.ext
  ext i
  by_cases hi : i ∈ Q
  · have hv : i ∉ V.val := fun hm => (Finset.mem_compl.mp (V.property hm)) hi
    have hw : i ∉ W.val := fun hm => (Finset.mem_compl.mp (W.property hm)) hi
    simp [hv, hw]
  · have hc := congrFun h i
    by_cases hv : i ∈ V.val <;> by_cases hw : i ∈ W.val <;>
      simp_all [canonicalOpposite, oppositeBit]

theorem nonzero_rawPairTerm_survives {R : Type*} [CommRing R] {L m k : ℕ}
    (X : RawLeftInput L m k R) (Y : RawRightInput L m k R)
    (good : Finset (Finset (Fin L))) (gamma : Cube L → Cube m) (delta : Cube L → Cube k)
    (QL QR : Finset (Fin L)) (bitsL bitsR locatorL locatorR : Cube L)
    (hQL : QL.card = m) (hQR : QR.card = m) (hgood : ∀ S ∈ good, S.card = m)
    (run : ℤ) (nL nR : Fin L → NormalLetter) (oL oR : Fin L → OppositeLetter)
    (hterm : rawPairTerm X Y good gamma delta QL QR bitsL bitsR locatorL locatorR
      run nL nR oL oR ≠ 0) :
    ∃ tL : Subsets QL, ∃ tR : Subsets QR,
      ∃ vL : Subsets QLᶜ, ∃ vR : Subsets QRᶜ,
      nL = canonicalNormal QL bitsL tL ∧ nR = canonicalNormal QR bitsR tR ∧
      oL = canonicalOpposite QL tL vL ∧ oR = canonicalOpposite QR tR vR := by
  have hkL : rawHalfKernel (R := R) QL bitsL locatorL nL oL ≠ 0 := by
    intro hz
    exact hterm (by simp [rawPairTerm, hz])
  have hkR : rawHalfKernel (R := R) QR bitsR locatorR nR oR ≠ 0 := by
    intro hz
    exact hterm (by simp [rawPairTerm, hz])
  have hsL : rawLeftSource X good gamma delta run nL oR ≠ 0 := by
    intro hz
    exact hterm (by simp [rawPairTerm, hz])
  have hsR : rawRightSource Y good gamma delta run nR oL ≠ 0 := by
    intro hz
    exact hterm (by simp [rawPairTerm, hz])
  have hmL : normalSupport nL ∈ good ∧
      (ones (oppositeWBits oR) : ℤ) - (ones (normalP2Bits nL) : ℤ) = run := by
    by_contra hn
    exact hsL (by simp [rawLeftSource, hn])
  have hmR : normalSupport nR ∈ good ∧
      (ones (normalP2Bits nR) : ℤ) - (ones (oppositeWBits oL) : ℤ) = run := by
    by_contra hn
    exact hsR (by simp [rawRightSource, hn])
  have hcL := compatible_of_kernel_nonzero QL bitsL locatorL nL oL hQL
    (hgood _ hmL.1) hkL
  have hcR := compatible_of_kernel_nonzero QR bitsR locatorR nR oR hQR
    (hgood _ hmR.1) hkR
  have hsubL := compatible_p2_subset_w hcL
  have hsubR := compatible_p2_subset_w hcR
  have hcardL := Finset.card_le_card hsubL
  have hcardR := Finset.card_le_card hsubR
  have hrunL := hmL.2
  have hrunR := hmR.2
  simp only [ones_normalP2Bits, ones_oppositeWBits] at hrunL hrunR
  have hWL : wPositions oL = p2Positions nL :=
    (Finset.eq_of_subset_of_card_le hsubL (by omega)).symm
  have hWR : wPositions oR = p2Positions nR :=
    (Finset.eq_of_subset_of_card_le hsubR (by omega)).symm
  exact ⟨⟨p2Positions nL, compatible_p2_subset hcL⟩,
    ⟨p2Positions nR, compatible_p2_subset hcR⟩,
    ⟨vPositions oL, compatible_v_subset hcL⟩,
    ⟨vPositions oR, compatible_v_subset hcR⟩,
    compatible_normal_canonical hcL, compatible_normal_canonical hcR,
    compatible_opposite_canonical hcL hWL, compatible_opposite_canonical hcR hWR⟩

abbrev RawWords (L : ℕ) :=
  (Fin L → NormalLetter) × (Fin L → NormalLetter) ×
    (Fin L → OppositeLetter) × (Fin L → OppositeLetter)

abbrev SurvivorWords {L : ℕ} (QL QR : Finset (Fin L)) :=
  Subsets QL × Subsets QR × Subsets QLᶜ × Subsets QRᶜ

def encodeWords {L : ℕ} (QL QR : Finset (Fin L)) (bitsL bitsR : Cube L)
    (s : SurvivorWords QL QR) : RawWords L :=
  (canonicalNormal QL bitsL s.1, canonicalNormal QR bitsR s.2.1,
    canonicalOpposite QL s.1 s.2.2.1, canonicalOpposite QR s.2.1 s.2.2.2)

theorem encodeWords_injective {L : ℕ} (QL QR : Finset (Fin L)) (bitsL bitsR : Cube L) :
    Function.Injective (encodeWords QL QR bitsL bitsR) := by
  rintro ⟨tL, tR, vL, vR⟩ ⟨uL, uR, wL, wR⟩ h
  have hnL := congrArg (fun r : RawWords L => r.1) h
  have hnR := congrArg (fun r : RawWords L => r.2.1) h
  have hoL := congrArg (fun r : RawWords L => r.2.2.1) h
  have hoR := congrArg (fun r : RawWords L => r.2.2.2) h
  have htL : tL = uL := canonicalNormal_injective QL bitsL hnL
  have htR : tR = uR := canonicalNormal_injective QR bitsR hnR
  have hvL : vL = wL := canonicalOpposite_v_injective QL tL uL vL wL hoL
  have hvR : vR = wR := canonicalOpposite_v_injective QR tR uR vR wR hoR
  cases htL
  cases htR
  cases hvL
  cases hvR
  rfl

theorem raw_word_sum_eq_survivors {R : Type*} [CommRing R] {L m k : ℕ}
    (X : RawLeftInput L m k R) (Y : RawRightInput L m k R)
    (good : Finset (Finset (Fin L))) (gamma : Cube L → Cube m) (delta : Cube L → Cube k)
    (QL QR : Finset (Fin L)) (bitsL bitsR locatorL locatorR : Cube L)
    (hQL : QL.card = m) (hQR : QR.card = m) (hgood : ∀ S ∈ good, S.card = m)
    (run : ℤ) :
    (∑ nL, ∑ nR, ∑ oL, ∑ oR,
      rawPairTerm X Y good gamma delta QL QR bitsL bitsR locatorL locatorR run nL nR oL oR) =
    ∑ tL : Subsets QL, ∑ tR : Subsets QR,
      ∑ vL : Subsets QLᶜ, ∑ vR : Subsets QRᶜ,
      rawPairTerm X Y good gamma delta QL QR bitsL bitsR locatorL locatorR run
        (canonicalNormal QL bitsL tL) (canonicalNormal QR bitsR tR)
        (canonicalOpposite QL tL vL) (canonicalOpposite QR tR vR) := by
  classical
  let f : RawWords L → R := fun r => rawPairTerm X Y good gamma delta QL QR
    bitsL bitsR locatorL locatorR run r.1 r.2.1 r.2.2.1 r.2.2.2
  have hs : (∑ s : SurvivorWords QL QR, f (encodeWords QL QR bitsL bitsR s)) =
      ∑ r : RawWords L, f r := by
    apply Finset.sum_bij_ne_zero (fun s _ _ => encodeWords QL QR bitsL bitsR s)
    · intro s hs hn
      exact Finset.mem_univ _
    · intro s hs hns t ht hnt heq
      exact encodeWords_injective QL QR bitsL bitsR heq
    · intro r hr hnr
      rcases r with ⟨nL, nR, oL, oR⟩
      obtain ⟨tL, tR, vL, vR, hnL, hnR, hoL, hoR⟩ :=
        nonzero_rawPairTerm_survives X Y good gamma delta QL QR bitsL bitsR
          locatorL locatorR hQL hQR hgood run nL nR oL oR hnr
      have heq : encodeWords QL QR bitsL bitsR (tL, tR, vL, vR) = (nL,nR,oL,oR) := by
        simp only [encodeWords, hnL, hnR, hoL, hoR]
      refine ⟨(tL,tR,vL,vR), Finset.mem_univ _, ?_, heq⟩
      simpa only [heq] using hnr
    · intro s hs hns
      rfl
  simpa only [Fintype.sum_prod_type, f, encodeWords] using hs.symm

/-- The actual raw A3--A4 sum equals its canonical surviving-word sum. -/
theorem rawContraction_eq_survivingContraction {R : Type*} [CommRing R] {L m k : ℕ}
    (X : RawLeftInput L m k R) (Y : RawRightInput L m k R)
    (good : Finset (Finset (Fin L))) (gamma : Cube L → Cube m) (delta : Cube L → Cube k)
    (QL QR : Finset (Fin L)) (bitsL bitsR locatorL locatorR : Cube L)
    (hQL : QL.card = m) (hQR : QR.card = m) (hgood : ∀ S ∈ good, S.card = m) :
    rawContraction X Y good gamma delta QL QR bitsL bitsR locatorL locatorR =
      survivingContraction X Y good gamma delta QL QR bitsL bitsR locatorL locatorR := by
  classical
  unfold rawContraction survivingContraction
  simp_rw [raw_word_sum_eq_survivors X Y good gamma delta QL QR bitsL bitsR
    locatorL locatorR hQL hQR hgood]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro tL htL
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro tR htR
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro vL hvL
  rw [Finset.sum_comm]

end ThinMatrix.RawWordBijection

#print axioms ThinMatrix.RawWordBijection.nonzero_rawPairTerm_survives
#print axioms ThinMatrix.RawWordBijection.rawContraction_eq_survivingContraction
