import GraphLowHighJoin

set_option autoImplicit false
set_option maxRecDepth 6000
set_option maxHeartbeats 2400000

/-! The common physical contraction is exactly the cropped shifted source
contraction, with the original shared degree run and both physical halves. -/
namespace ThinMatrix.CroppedPhysicalContraction
open WalshEmbedding CompleteThinProduct PhysicalShiftedForms
open scoped BigOperators
variable {R : Type*} [CommRing R]

theorem normal_fixed (i j : Bool) (n : NormalLetter) :
    (PhysicalOrdinaryForms.normal (fixedLabel i j) n : R)=ShiftedSourceEmbedding.ordinaryNormal i j n := by
  have he : PhysicalOrdinaryForms.normal (fixedLabel i j) n=ShiftedSourceEmbedding.ordinaryNormal (R:=ℤ) i j n := by
    cases i <;> cases j <;> cases n <;> rfl
  rw [he]
  cases i <;> cases j <;> cases n <;>
    norm_num [ShiftedSourceEmbedding.ordinaryNormal,WalshEmbedding.ordinaryNormal,reduceCtorEq]

theorem opposite_fixed (i j : Bool) (o : OppositeLetter) :
    (PhysicalOrdinaryForms.opposite (fixedLabel i j) o : R)=ordinaryOpposite i j o := by
  cases i <;> cases j <;> cases o <;>
    norm_num [PhysicalOrdinaryForms.opposite,fixedLabel,ordinaryOpposite]

noncomputable def outsideF {L : ℕ} (QL QR : Finset (Fin L))
    (iL iR jL jR : Cube L) (a : SourceWord L) : R :=
  (∏ i∈QLᶜ, ShiftedSourceEmbedding.ordinaryNormal (iL i) (jL i) (a.1 i))*
    ∏ i∈QRᶜ, ordinaryOpposite (iR i) (jR i) (a.2 i)

noncomputable def outsideG {L : ℕ} (QL QR : Finset (Fin L))
    (iL iR jL jR : Cube L) (b : SourceWord L) : R :=
  (∏ i∈QLᶜ, ordinaryOpposite (iL i) (jL i) (b.2 i))*
    ∏ i∈QRᶜ, ShiftedSourceEmbedding.ordinaryNormal (iR i) (jR i) (b.1 i)

theorem physical_inner {L m : ℕ} (QL QR : Finset (Fin L))
    (hQL : QL.card=m) (hQR : QR.card=m) (a b : SourceWord L) :
    (∏ i, fullKernel (fun j => lift (R:=R) true (physicalEmbedding QL QR hQL hQR j))
      (fun j => lift false (physicalEmbedding QL QR hQL hQR j)) i a b)=sourceInner QL QR a b := by
  change (∏ i : Fin (2*m), fullKernel (lift true) (lift false) (physicalEmbedding QL QR hQL hQR i) a b)=_
  rw [←Finset.prod_image (s:=Finset.univ) (f:=fun i => fullKernel (lift (R:=R) true) (lift false) i a b)
    (g:=physicalEmbedding QL QR hQL hQR) (fun _ _ _ _ h => (physicalEmbedding QL QR hQL hQR).injective h)]
  change (∏ i∈HighBoxDP.embeddedSupport (physicalEmbedding QL QR hQL hQR), fullKernel (lift true) (lift false) i a b)=_
  rw [physicalEmbedding_support,prod_physical_support]
  simp only [full_left,full_right,sourceInner]

theorem physical_outsideF {L m : ℕ} (QL QR : Finset (Fin L))
    (hQL : QL.card=m) (hQR : QR.card=m) (iL iR jL jR : Cube L) (a : SourceWord L) :
    (∏ i∈(HighBoxDP.embeddedSupport (physicalEmbedding QL QR hQL hQR))ᶜ,
      lift (R:=R) true i ((sourceOutside iL iR jL jR i).castSucc) a)=outsideF QL QR iL iR jL jR a := by
  rw [physicalEmbedding_support,prod_physical_compl]
  simp only [sourceOutside,halfLift_left,halfLift_right,ordinary_left,ordinary_right,↓reduceIte,
    normal_fixed,opposite_fixed,outsideF]

theorem physical_outsideG {L m : ℕ} (QL QR : Finset (Fin L))
    (hQL : QL.card=m) (hQR : QR.card=m) (iL iR jL jR : Cube L) (b : SourceWord L) :
    (∏ i∈(HighBoxDP.embeddedSupport (physicalEmbedding QL QR hQL hQR))ᶜ,
      lift (R:=R) false i ((sourceOutside iL iR jL jR i).castSucc) b)=outsideG QL QR iL iR jL jR b := by
  rw [physicalEmbedding_support,prod_physical_compl]
  simp only [sourceOutside,halfLift_left,halfLift_right,ordinary_left,ordinary_right,Bool.false_eq_true,↓reduceIte,
    normal_fixed,opposite_fixed,outsideG]

theorem half_factor {L : ℕ} (QL QR : Finset (Fin L)) (iL iR jL jR : Cube L) (a b : SourceWord L) :
    ShiftedSourceEmbedding.halfKernel (R:=R) QL iL jL a.1 b.2 *
      ShiftedSourceEmbedding.halfKernel QR iR jR b.1 a.2=
      outsideF QL QR iL iR jL jR a*outsideG QL QR iL iR jL jR b*sourceInner QL QR a b := by
  simp only [ShiftedSourceEmbedding.halfKernel,outsideF,outsideG,sourceInner,Finset.prod_mul_distrib]
  ring

theorem contraction {L m k : ℕ} (cap : ℕ)
    (X : RawLeftInput L m k R) (Y : RawRightInput L m k R)
    (good : Finset (Finset (Fin L))) (gamma : Cube L → Cube m) (delta : Cube L → Cube k)
    (QL QR : Finset (Fin L)) (hQL : QL.card=m) (hQR : QR.card=m)
    (iL iR jL jR : Cube L) :
    (∑ run∈Finset.Icc (-(m:ℤ)) (m:ℤ),
      TensorContraction.bilinear
        (absorbedInput (physicalEmbedding QL QR hQL hQR) (sourceOutside iL iR jL jR)
          (fun a => CroppedSourceContraction.crop cap (rawLeftSource X good gamma delta run) a.1 a.2) (lift true))
        (absorbedInput (physicalEmbedding QL QR hQL hQR) (sourceOutside iL iR jL jR)
          (fun b => CroppedSourceContraction.crop cap (rawRightSource Y good gamma delta run) b.1 b.2) (lift false))
        (fun a b => ∏ i, fullKernel (fun j => lift true (physicalEmbedding QL QR hQL hQR j))
          (fun j => lift false (physicalEmbedding QL QR hQL hQR j)) i a b))=
      CroppedSourceContraction.contraction cap X Y good gamma delta QL QR iL iR jL jR := by
  unfold CroppedSourceContraction.contraction
  apply Finset.sum_congr rfl
  intro run _
  unfold TensorContraction.bilinear
  simp only [physical_inner,absorbedInput,physical_outsideF,physical_outsideG]
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro e _
  rw [CroppedSourceContraction.pairTerm,half_factor QL QR iL iR jL jR (a,e) (b,c)]
  ring

#print axioms normal_fixed
#print axioms opposite_fixed
#print axioms physical_inner
#print axioms physical_outsideF
#print axioms physical_outsideG
#print axioms half_factor
#print axioms contraction
end ThinMatrix.CroppedPhysicalContraction
