import BinaryResidualDegreeSpace

set_option autoImplicit false

/-! Identify the binary residual program's complete polynomial with the
existing physical residual-root specification. Equal distinguished sizes
imply equal remaining sizes; the opposite layout is transported explicitly.
This connects existing support/window lemmas to the same polynomial instead
of introducing a parallel root specification. -/
namespace ThinMatrix.ResidualRootBridge
open WalshEmbedding DistinguishedResidualRoot DistinguishedResidualSupport
open ResidualPolynomialDegree
open scoped BigOperators

noncomputable def rawPolynomial {L C : ℕ} [NeZero C] (raw : BinarySourceFormation.RawStore L C)
    (n : Fin L → NormalLetter) (o : Fin L → OppositeLetter) : Polynomial (CyclicRing.Cyclic C) :=
  Polynomial.C (fun r => BinaryCell.view (BinarySourceFormation.readRaw raw n o r))

theorem sourcePolynomial_eq {L C : ℕ} [NeZero C] (cap : ℕ)
    (raw : BinarySourceFormation.RawStore L C) (n : Fin L → NormalLetter) (o : Fin L → OppositeLetter) :
    BinaryResidualRootProgram.sourcePolynomial cap raw n o=cropBoth cap (rawPolynomial raw) n o := by
  by_cases hn : ones (normalP2Bits n)≤cap <;> by_cases ho : ones (oppositeWBits o)≤cap
  all_goals simp only [BinaryResidualRootProgram.sourcePolynomial,cropBoth,CroppedSourceContraction.crop,hn,ho,↓reduceIte,rawPolynomial]
  all_goals change Polynomial.C (0 : CyclicRing.Cyclic C)=0
  all_goals exact map_zero Polynomial.C

theorem integerScale_cast {R : Type*} [CommRing R] {m : ℕ} (co : Vector Bool m) :
    (integerScale co : R)=∏ i, oppositeScale (R:=R) (co.get i) := by
  rw [integerScale,BinaryResidualDegreeSpace.toList_get,List.map_ofFn,List.prod_ofFn,Int.cast_prod]
  apply Finset.prod_congr rfl
  intro i _
  cases h : co.get i <;> simp [oppositeScale,h]

def transport {L m n k l : ℕ} (e : Layout L m k) (hm : m=n) (hk : k=l) : Layout L n l :=
  e.trans (Equiv.sumCongr (finCongr hm) (finCongr hk))

theorem assemble_transport {L m n k l : ℕ} {A : Type*} (e : Layout L m k)
    (hm : m=n) (hk : k=l) (a : Fin m → A) (b : Fin k → A) :
    assemble (transport e hm hk) (fun i => a ((finCongr hm).symm i))
      (fun i => b ((finCongr hk).symm i))=assemble e a b := by
  cases hm
  cases hk
  funext i
  cases he : e i <;> simp [assemble,transport,he]

theorem remaining_eq {L : ℕ} (maskN maskO : Vector Bool L)
    (h : (ResidualLayout.selected maskO).length=(ResidualLayout.selected maskN).length) :
    (ResidualLayout.remaining maskO).length=(ResidualLayout.remaining maskN).length := by
  have hn := ResidualLayout.lengths maskN
  have ho := ResidualLayout.lengths maskO
  omega

theorem ones_transport {m n : ℕ} (h : m=n) (b : Cube m) :
    ones (fun i => b ((finCongr h).symm i))=ones b := by
  cases h
  rfl

theorem rare_transport {m n : ℕ} (h : m=n) (w : CroppedGroupedSuffix.Word m) :
    rareCount (fun i => w ((finCongr h).symm i))=rareCount w := by
  cases h
  rfl

/-- Equality with the pre-existing physical root, not a new conditional oracle.
The casts only align equal-sized semantic coordinates; execution still uses
its original two retained layouts. -/
theorem polynomial_eq_root {L C : ℕ} [NeZero C] (cap : ℕ)
    (raw : BinarySourceFormation.RawStore L C) (maskN maskO : Vector Bool L)
    (he : (ResidualLayout.selected maskO).length=(ResidualLayout.selected maskN).length)
    (cn : Vector Bool (ResidualLayout.selected maskN).length)
    (co : Vector Bool (ResidualLayout.selected maskO).length)
    (wn : Vector (Fin 3) (ResidualLayout.remaining maskN).length)
    (wo : Vector (Fin 3) (ResidualLayout.remaining maskO).length) :
    polynomial cap raw maskN maskO cn co wn wo =
      root (ResidualLayout.equivalence maskN)
        (transport (ResidualLayout.equivalence maskO) he (remaining_eq maskN maskO he))
        cn.get (fun i => co.get ((finCongr he).symm i)) Polynomial.X cap (rawPolynomial raw)
        wn.get (fun i => wo.get ((finCongr (remaining_eq maskN maskO he)).symm i)) := by
  have hs : (integerScale co : Polynomial (CyclicRing.Cyclic C))=
      ∏ i, oppositeScale (R:=Polynomial (CyclicRing.Cyclic C)) (co.get ((finCongr he).symm i)) := by
    rw [integerScale_cast,← Equiv.prod_comp (finCongr he)]
    simp
  unfold polynomial root
  rw [hs]
  simp_rw [sourcePolynomial_eq]
  rw [assemble_transport (ResidualLayout.equivalence maskO) he (remaining_eq maskN maskO he)
    (fun i => oppositeLetter (co.get i)) (fun i => SourceCoordinates.oppositeEquiv (wo.get i))]

#print axioms sourcePolynomial_eq
#print axioms integerScale_cast
#print axioms assemble_transport
#print axioms remaining_eq
#print axioms ones_transport
#print axioms rare_transport
#print axioms polynomial_eq_root
end ThinMatrix.ResidualRootBridge
