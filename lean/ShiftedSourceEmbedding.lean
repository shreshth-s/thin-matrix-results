import WalshEmbedding

set_option autoImplicit false

/-!
# The shifted ordinary forms preserve the complete raw Walsh contraction

The source arrays, weights, degree runs and output locator are unchanged.
The normal-side private p1 term is moved out of the ordinary forms. Nonzero
inner factors force the normal support to the queried good set; thus there
is no outside p1 position on any contributing source word. The pointwise
argument works in commutative rings without an integral-domain assumption.
-/

namespace ThinMatrix.ShiftedSourceEmbedding
open ThinMatrix.WalshEmbedding
open scoped BigOperators
variable {R : Type*} [CommRing R]

def ordinaryNormal (i j : Bool) (n : NormalLetter) : R :=
  if n = .p1 then 0 else WalshEmbedding.ordinaryNormal i j n

def privateNormal : NormalLetter → R
  | .x1 | .x2 => -1
  | .p1 => 1
  | .p2 => 0

def privateOpposite : OppositeLetter → R
  | .s => 2
  | _ => 0

theorem local_identity (n : NormalLetter) (o : OppositeLetter) :
    (∑ i : Bool, ∑ j : Bool, ordinaryNormal (R := R) i j n *
      ordinaryOpposite (R := R) i j o) + privateNormal n * privateOpposite o =
      innerCoefficient n o := by
  cases n <;> cases o <;>
    norm_num [ordinaryNormal, WalshEmbedding.ordinaryNormal, ordinaryOpposite,
      privateNormal, privateOpposite, innerCoefficient, Fintype.sum_bool] <;>
    simp only [reduceCtorEq, ite_false, add_neg_cancel, neg_add_cancel, neg_neg]

def halfKernel {L : ℕ} (Q : Finset (Fin L)) (bits locator : Cube L)
    (n : Fin L → NormalLetter) (o : Fin L → OppositeLetter) : R :=
  (∏ i ∈ Q, innerCoefficient (R := R) (n i) (o i)) *
    ∏ i ∈ Qᶜ, ordinaryNormal (R := R) (bits i) (locator i) (n i) *
      ordinaryOpposite (R := R) (bits i) (locator i) (o i)

theorem halfKernel_eq {L m : ℕ} (Q : Finset (Fin L)) (bits locator : Cube L)
    (n : Fin L → NormalLetter) (o : Fin L → OppositeLetter)
    (hQ : Q.card = m) (hn : (normalSupport n).card = m) :
    halfKernel (R := R) Q bits locator n o = rawHalfKernel Q bits locator n o := by
  by_cases hz : (∏ i ∈ Q, innerCoefficient (R := R) (n i) (o i)) = 0
  · simp [halfKernel,rawHalfKernel,hz]
  · have he := raw_normal_support_eq_query Q n o hQ hn hz
    unfold halfKernel rawHalfKernel
    congr 1
    apply Finset.prod_congr rfl
    intro i hi
    have hnot : n i ≠ .p1 := by
      intro hp
      have hm : i ∈ normalSupport n := by simp [normalSupport,normalIsP,hp]
      rw [he] at hm
      exact (Finset.mem_compl.mp hi) hm
    simp [ordinaryNormal,hnot]

def pairTerm {L m k : ℕ}
    (X : RawLeftInput L m k R) (Y : RawRightInput L m k R)
    (good : Finset (Finset (Fin L))) (gamma : Cube L → Cube m) (delta : Cube L → Cube k)
    (QL QR : Finset (Fin L)) (bitsL bitsR locatorL locatorR : Cube L)
    (run : ℤ) (nL nR : Fin L → NormalLetter) (oL oR : Fin L → OppositeLetter) : R :=
  halfKernel QL bitsL locatorL nL oL * halfKernel QR bitsR locatorR nR oR *
    rawLeftSource X good gamma delta run nL oR * rawRightSource Y good gamma delta run nR oL

theorem pairTerm_eq {L m k : ℕ}
    (X : RawLeftInput L m k R) (Y : RawRightInput L m k R)
    (good : Finset (Finset (Fin L))) (gamma : Cube L → Cube m) (delta : Cube L → Cube k)
    (QL QR : Finset (Fin L)) (bitsL bitsR locatorL locatorR : Cube L)
    (hQL : QL.card = m) (hQR : QR.card = m) (hg : ∀ Q ∈ good, Q.card = m)
    (run : ℤ) (nL nR : Fin L → NormalLetter) (oL oR : Fin L → OppositeLetter) :
    pairTerm X Y good gamma delta QL QR bitsL bitsR locatorL locatorR run nL nR oL oR =
      rawPairTerm X Y good gamma delta QL QR bitsL bitsR locatorL locatorR run nL nR oL oR := by
  by_cases hl : normalSupport nL ∈ good
  · by_cases hr : normalSupport nR ∈ good
    · simp only [pairTerm,rawPairTerm,
        halfKernel_eq QL bitsL locatorL nL oL hQL (hg _ hl),
        halfKernel_eq QR bitsR locatorR nR oR hQR (hg _ hr)]
    · simp [pairTerm,rawPairTerm,raw_right_nongood Y good gamma delta run nR oL hr]
  · simp [pairTerm,rawPairTerm,raw_left_nongood X good gamma delta run nL oR hl]

noncomputable def contraction {L m k : ℕ}
    (X : RawLeftInput L m k R) (Y : RawRightInput L m k R)
    (good : Finset (Finset (Fin L))) (gamma : Cube L → Cube m) (delta : Cube L → Cube k)
    (QL QR : Finset (Fin L)) (bitsL bitsR locatorL locatorR : Cube L) : R :=
  ∑ run ∈ Finset.Icc (-(m:ℤ)) (m:ℤ), ∑ nL, ∑ nR, ∑ oL, ∑ oR,
    pairTerm X Y good gamma delta QL QR bitsL bitsR locatorL locatorR run nL nR oL oR

theorem contraction_eq {L m k : ℕ}
    (X : RawLeftInput L m k R) (Y : RawRightInput L m k R)
    (good : Finset (Finset (Fin L))) (gamma : Cube L → Cube m) (delta : Cube L → Cube k)
    (QL QR : Finset (Fin L)) (bitsL bitsR locatorL locatorR : Cube L)
    (hQL : QL.card = m) (hQR : QR.card = m) (hg : ∀ Q ∈ good, Q.card = m) :
    contraction X Y good gamma delta QL QR bitsL bitsR locatorL locatorR =
      rawContraction X Y good gamma delta QL QR bitsL bitsR locatorL locatorR := by
  unfold contraction rawContraction
  simp_rw [pairTerm_eq X Y good gamma delta QL QR bitsL bitsR locatorL locatorR hQL hQR hg]

#print axioms local_identity
#print axioms halfKernel_eq
#print axioms pairTerm_eq
#print axioms contraction_eq

end ThinMatrix.ShiftedSourceEmbedding
