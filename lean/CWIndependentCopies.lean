import CWIsolatedCandidates

set_option autoImplicit false

/-! Actual coordinate zeroing of CW powers, followed by the already proved
exact separated decomposition. Copy labels come from the computed cleanup,
not an assumed family of isolated tensors. -/
namespace ThinMatrix.CWIndependentCopies
open scoped BigOperators
open FiniteTrilinear PolynomialDegeneration CWPolynomialCertificate CWSixBlocks CWBlockWords CWTypeCounts CWIsolatedCandidates

abbrev Copies (n : ℕ) (reference : Word n) (X Y Z : Finset (Colors n)) :=
  {w : Word n // w ∈ selected n reference X Y Z}

variable (n : ℕ) (reference : Word n) (X Y Z : Finset (Colors n))
abbrev XA := Σ w : Copies n reference X Y Z,Rows 16 n w.val×Inners 16 n w.val
abbrev YA := Σ w : Copies n reference X Y Z,Inners 16 n w.val×Cols 16 n w.val
abbrev ZA := Σ w : Copies n reference X Y Z,Cols 16 n w.val×Rows 16 n w.val

def embedX (a : XA n reference X Y Z) : CWPowerSpecialization.Index n := leftWord 16 n a.1.val a.2
def embedY (a : YA n reference X Y Z) : CWPowerSpecialization.Index n := middleWord 16 n a.1.val a.2
def embedZ (a : ZA n reference X Y Z) : CWPowerSpecialization.Index n := rightWord 16 n a.1.val a.2

theorem embedX_injective : Function.Injective (embedX n reference X Y Z) := by
  intro a b h
  have hc : wx n a.1.val=wx n b.1.val := by
    simpa only [embedX,leftWord_color] using congrArg (colors n) h
  have he := FiniteCollisionCleanup.unique_neighbor _ (wx n) (wy n) (wz n)
    a.1.val b.1.val a.1.property (selected_subset n reference X Y Z b.1.property) (Or.inl hc)
  have hi : a.1=b.1 := Subtype.ext he.symm
  obtain ⟨a,x⟩ := a;obtain ⟨b,y⟩ := b
  dsimp at hi
  subst b
  exact congrArg (Sigma.mk a) (leftWord_injective 16 n a.val h)

theorem embedY_injective : Function.Injective (embedY n reference X Y Z) := by
  intro a b h
  have hc : wy n a.1.val=wy n b.1.val := by
    simpa only [embedY,middleWord_color] using congrArg (colors n) h
  have he := FiniteCollisionCleanup.unique_neighbor _ (wx n) (wy n) (wz n)
    a.1.val b.1.val a.1.property (selected_subset n reference X Y Z b.1.property) (Or.inr (Or.inl hc))
  have hi : a.1=b.1 := Subtype.ext he.symm
  obtain ⟨a,x⟩ := a;obtain ⟨b,y⟩ := b
  dsimp at hi
  subst b
  exact congrArg (Sigma.mk a) (middleWord_injective 16 n a.val h)

theorem embedZ_injective : Function.Injective (embedZ n reference X Y Z) := by
  intro a b h
  have hc : wz n a.1.val=wz n b.1.val := by
    simpa only [embedZ,rightWord_color] using congrArg (colors n) h
  have he := FiniteCollisionCleanup.unique_neighbor _ (wx n) (wy n) (wz n)
    a.1.val b.1.val a.1.property (selected_subset n reference X Y Z b.1.property) (Or.inr (Or.inr hc))
  have hi : a.1=b.1 := Subtype.ext he.symm
  obtain ⟨a,x⟩ := a;obtain ⟨b,y⟩ := b
  dsimp at hi
  subst b
  exact congrArg (Sigma.mk a) (rightWord_injective 16 n a.val h)

def directSum : Tensor (XA n reference X Y Z) (YA n reference X Y Z) (ZA n reference X Y Z) ℚ :=
  fun a b c => if h : a.1=b.1 ∧ a.1=c.1 then
    FiniteMatrixTensor.coeff (Rows 16 n a.1.val) (Inners 16 n a.1.val) (Cols 16 n a.1.val) ℚ
      a.2 (h.1.symm ▸ b.2) (h.2.symm ▸ c.2) else 0

theorem restricted_tensor (a : XA n reference X Y Z) (b : YA n reference X Y Z) (c : ZA n reference X Y Z) :
    (tensorPower (target (R:=ℤ) 16) n (embedX n reference X Y Z a)
      (embedY n reference X Y Z b) (embedZ n reference X Y Z c):ℚ)=directSum n reference X Y Z a b c := by
  obtain ⟨u,x⟩ := a;obtain ⟨v,y⟩ := b;obtain ⟨w,z⟩ := c
  by_cases h : u=v ∧ u=w
  · obtain ⟨rfl,rfl⟩ := h
    simp only [directSum,embedX,embedY,embedZ,word_identity]
    simp [FiniteMatrixTensor.coeff]
  · have hh : ¬ (u.val=v.val ∧ u.val=w.val) := fun he => h ⟨Subtype.ext he.1,Subtype.ext he.2⟩
    have hz := tensor_cross_zero (R:=ℤ) 16 n reference u.val v.val w.val X Y Z
      u.property v.property w.property hh x y z
    simp only [directSum,h,↓reduceDIte,embedX,embedY,embedZ,hz,Int.cast_zero]

def terms (s : CWInterpolationProgram.Request n) :
    Term (XA n reference X Y Z) (YA n reference X Y Z) (ZA n reference X Y Z) ℚ :=
  (CWExactDecomposition.terms n s).restrict (embedX n reference X Y Z)
    (embedY n reference X Y Z) (embedZ n reference X Y Z)

theorem exact_decomposition : total (terms n reference X Y Z)=directSum n reference X Y Z := by
  unfold terms
  rw [total_restrict,CWExactDecomposition.terms_total]
  funext a b c
  exact restricted_tensor n reference X Y Z a b c

theorem term_count : Fintype.card (CWInterpolationProgram.Request n)=(10*n+1)*18^n :=
  CWExactDecomposition.term_count n

theorem copy_count : Fintype.card (Copies n reference X Y Z)=(selected n reference X Y Z).card :=
  Fintype.card_coe _

theorem dimensions (w : Copies n reference X Y Z) :
    Fintype.card (Rows 16 n w.val)=16^count Block.b101 n reference ∧
    Fintype.card (Inners 16 n w.val)=16^count Block.b110 n reference ∧
    Fintype.card (Cols 16 n w.val)=16^count Block.b011 n reference := by
  have h := selected_counts n reference w.val X Y Z w.property
  simp [rows_card,inners_card,cols_card,h]

#print axioms embedX_injective
#print axioms embedY_injective
#print axioms embedZ_injective
#print axioms restricted_tensor
#print axioms exact_decomposition
#print axioms term_count
#print axioms copy_count
#print axioms dimensions
end ThinMatrix.CWIndependentCopies
