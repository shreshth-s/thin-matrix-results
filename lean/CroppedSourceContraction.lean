import ShiftedSourceEmbedding
import RawWordBijection

set_option autoImplicit false

/-!
# Cropping both opposite sources before either encoder

Normal-cap hypotheses are properties of each individual source. Equal degree
runs and the nonzero raw-word classification then imply both opposite caps
on every surviving complete summand. The theorem does not assert equality
of individual encoded residuals or HIGH boxes before completion.
-/

namespace ThinMatrix.CroppedSourceContraction
open ThinMatrix.WalshEmbedding ThinMatrix.RawWordBijection
open scoped BigOperators
variable {R : Type*} [CommRing R]

def crop {L : ℕ} (cap : ℕ)
    (source : (Fin L → NormalLetter) → (Fin L → OppositeLetter) → R)
    (n : Fin L → NormalLetter) (o : Fin L → OppositeLetter) : R :=
  if ones (oppositeWBits o) ≤ cap then source n o else 0

def pairTerm {L m k : ℕ} (cap : ℕ)
    (X : RawLeftInput L m k R) (Y : RawRightInput L m k R)
    (good : Finset (Finset (Fin L))) (gamma : Cube L → Cube m) (delta : Cube L → Cube k)
    (QL QR : Finset (Fin L)) (bitsL bitsR locatorL locatorR : Cube L)
    (run : ℤ) (nL nR : Fin L → NormalLetter) (oL oR : Fin L → OppositeLetter) : R :=
  ShiftedSourceEmbedding.halfKernel QL bitsL locatorL nL oL *
    ShiftedSourceEmbedding.halfKernel QR bitsR locatorR nR oR *
    crop cap (rawLeftSource X good gamma delta run) nL oR *
    crop cap (rawRightSource Y good gamma delta run) nR oL

theorem pairTerm_mask {L m k : ℕ} (cap : ℕ)
    (X : RawLeftInput L m k R) (Y : RawRightInput L m k R)
    (good : Finset (Finset (Fin L))) (gamma : Cube L → Cube m) (delta : Cube L → Cube k)
    (QL QR : Finset (Fin L)) (bitsL bitsR locatorL locatorR : Cube L)
    (run : ℤ) (nL nR : Fin L → NormalLetter) (oL oR : Fin L → OppositeLetter) :
    pairTerm cap X Y good gamma delta QL QR bitsL bitsR locatorL locatorR run nL nR oL oR =
      if ones (oppositeWBits oR) ≤ cap ∧ ones (oppositeWBits oL) ≤ cap then
        ShiftedSourceEmbedding.pairTerm X Y good gamma delta QL QR bitsL bitsR locatorL locatorR
          run nL nR oL oR else 0 := by
  by_cases hl : ones (oppositeWBits oR) ≤ cap <;>
    by_cases hr : ones (oppositeWBits oL) ≤ cap <;>
    simp [pairTerm,crop,ShiftedSourceEmbedding.pairTerm,hl,hr]

theorem surviving_caps {L m k : ℕ} (cap : ℕ)
    (X : RawLeftInput L m k R) (Y : RawRightInput L m k R)
    (good : Finset (Finset (Fin L))) (gamma : Cube L → Cube m) (delta : Cube L → Cube k)
    (QL QR : Finset (Fin L)) (bitsL bitsR locatorL locatorR : Cube L)
    (hQL : QL.card = m) (hQR : QR.card = m) (hg : ∀ Q ∈ good, Q.card = m)
    (hleft : ∀ d n o, cap < ones (normalP2Bits n) → rawLeftSource X good gamma delta d n o = 0)
    (hright : ∀ d n o, cap < ones (normalP2Bits n) → rawRightSource Y good gamma delta d n o = 0)
    (run : ℤ) (nL nR : Fin L → NormalLetter) (oL oR : Fin L → OppositeLetter)
    (hne : rawPairTerm X Y good gamma delta QL QR bitsL bitsR locatorL locatorR
      run nL nR oL oR ≠ 0) :
    ones (oppositeWBits oR) ≤ cap ∧ ones (oppositeWBits oL) ≤ cap := by
  have hnL : ones (normalP2Bits nL) ≤ cap := by
    by_contra! hb
    exact hne (by simp [rawPairTerm,hleft run nL oR hb])
  have hnR : ones (normalP2Bits nR) ≤ cap := by
    by_contra! hb
    exact hne (by simp [rawPairTerm,hright run nR oL hb])
  obtain ⟨tL,tR,vL,vR,hnl,hnr,hol,hor⟩ := nonzero_rawPairTerm_survives X Y good gamma delta
    QL QR bitsL bitsR locatorL locatorR hQL hQR hg run nL nR oL oR hne
  rw [hnl,canonicalNormal_p2] at hnL
  rw [hnr,canonicalNormal_p2] at hnR
  simpa only [hol,hor,canonicalOpposite_w] using And.intro hnR hnL

theorem pairTerm_eq {L m k : ℕ} (cap : ℕ)
    (X : RawLeftInput L m k R) (Y : RawRightInput L m k R)
    (good : Finset (Finset (Fin L))) (gamma : Cube L → Cube m) (delta : Cube L → Cube k)
    (QL QR : Finset (Fin L)) (bitsL bitsR locatorL locatorR : Cube L)
    (hQL : QL.card = m) (hQR : QR.card = m) (hg : ∀ Q ∈ good, Q.card = m)
    (hleft : ∀ d n o, cap < ones (normalP2Bits n) → rawLeftSource X good gamma delta d n o = 0)
    (hright : ∀ d n o, cap < ones (normalP2Bits n) → rawRightSource Y good gamma delta d n o = 0)
    (run : ℤ) (nL nR : Fin L → NormalLetter) (oL oR : Fin L → OppositeLetter) :
    pairTerm cap X Y good gamma delta QL QR bitsL bitsR locatorL locatorR run nL nR oL oR =
      rawPairTerm X Y good gamma delta QL QR bitsL bitsR locatorL locatorR run nL nR oL oR := by
  rw [pairTerm_mask,ShiftedSourceEmbedding.pairTerm_eq X Y good gamma delta QL QR
    bitsL bitsR locatorL locatorR hQL hQR hg]
  by_cases hz : rawPairTerm X Y good gamma delta QL QR bitsL bitsR locatorL locatorR
      run nL nR oL oR = 0
  · simp [hz]
  · rw [if_pos (surviving_caps cap X Y good gamma delta QL QR bitsL bitsR locatorL locatorR
      hQL hQR hg hleft hright run nL nR oL oR hz)]

noncomputable def contraction {L m k : ℕ} (cap : ℕ)
    (X : RawLeftInput L m k R) (Y : RawRightInput L m k R)
    (good : Finset (Finset (Fin L))) (gamma : Cube L → Cube m) (delta : Cube L → Cube k)
    (QL QR : Finset (Fin L)) (bitsL bitsR locatorL locatorR : Cube L) : R :=
  ∑ run ∈ Finset.Icc (-(m:ℤ)) (m:ℤ), ∑ nL, ∑ nR, ∑ oL, ∑ oR,
    pairTerm cap X Y good gamma delta QL QR bitsL bitsR locatorL locatorR run nL nR oL oR

theorem contraction_eq {L m k : ℕ} (cap : ℕ)
    (X : RawLeftInput L m k R) (Y : RawRightInput L m k R)
    (good : Finset (Finset (Fin L))) (gamma : Cube L → Cube m) (delta : Cube L → Cube k)
    (QL QR : Finset (Fin L)) (bitsL bitsR locatorL locatorR : Cube L)
    (hQL : QL.card = m) (hQR : QR.card = m) (hg : ∀ Q ∈ good, Q.card = m)
    (hleft : ∀ d n o, cap < ones (normalP2Bits n) → rawLeftSource X good gamma delta d n o = 0)
    (hright : ∀ d n o, cap < ones (normalP2Bits n) → rawRightSource Y good gamma delta d n o = 0) :
    contraction cap X Y good gamma delta QL QR bitsL bitsR locatorL locatorR =
      rawContraction X Y good gamma delta QL QR bitsL bitsR locatorL locatorR := by
  unfold contraction rawContraction
  simp_rw [pairTerm_eq cap X Y good gamma delta QL QR bitsL bitsR locatorL locatorR hQL hQR hg hleft hright]

#print axioms pairTerm_mask
#print axioms surviving_caps
#print axioms pairTerm_eq
#print axioms contraction_eq

end ThinMatrix.CroppedSourceContraction
