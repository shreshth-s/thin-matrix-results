import CWFiniteBase
import FiniteMatrixPowers
import FiniteRationalCoefficients

set_option autoImplicit false
set_option maxRecDepth 4000
set_option exponentiation.threshold 1024

/-! A closed exact rational rank construction for rectangular matrix powers
of the required aspect. The term-count bound is not a full runtime bound:
evaluating the expanded dense forms separately would lose the exponent. -/
namespace ThinMatrix.CWRectangularRanks
open FiniteTrilinear PolynomialDegeneration FiniteMatrixPowers
open CWHomogeneousCopies CWTargetExtractionRate

abbrev A (s k : ℕ) := PowerIndex (Fin (rows s)) k
abbrev B (s k : ℕ) := PowerIndex (Fin (inners s)) k
abbrev C (s k : ℕ) := PowerIndex (Fin (cols s)) k

noncomputable def terms (s : ℕ) (h : Sample s) (ht : 0<copies s h) (k : ℕ)
    (j : EqualCopyRecursion.Budget (ranks s) (copies s h) k) :
    Term (C s k×A s k) (A s k×B s k) (B s k×C s k) ℚ :=
  rotate ((recursiveTerms s h ht k j).restrict (pair k) (pair k) (pair k))

theorem terms_total (s : ℕ) (h : Sample s) (ht : 0<copies s h) (k : ℕ) :
    total (terms s h ht k)=FiniteMatrixTensor.coeff (C s k) (A s k) (B s k) ℚ := by
  unfold terms
  rw [total_rotate]
  have hh := total_restrict (recursiveTerms s h ht k)
    (pair (A:=Fin (rows s)) (B:=Fin (inners s)) k)
    (pair (A:=Fin (inners s)) (B:=Fin (cols s)) k)
    (pair (A:=Fin (cols s)) (B:=Fin (rows s)) k)
  rw [recursive_total] at hh
  funext x y z
  change total (fun j => (recursiveTerms s h ht k j).restrict (pair k) (pair k) (pair k)) y z x=_
  rw [hh]
  change tensorPower (FiniteMatrixTensor.coeff _ _ _ ℚ) k (pair k y) (pair k z) (pair k x)=_
  rw [tensor_matrix]
  exact FiniteMatrixTensor.cyclic y z x

theorem dimensions (s k : ℕ) :
    Fintype.card (C s k)=(cols s)^k ∧ Fintype.card (A s k)=(rows s)^k ∧
      Fintype.card (B s k)=(inners s)^k := by
  simp only [A,B,C,powerIndex_card,Fintype.card_fin,and_self]

theorem aspect (s k : ℕ) :
    (Fintype.card (C s k))^500=(Fintype.card (A s k))^861 ∧
      Fintype.card (B s k)=(Fintype.card (A s k))^15 := by
  obtain ⟨hC,hA,hB⟩ := dimensions s k
  rw [hC,hA,hB]
  constructor
  · change ((16^(s*6888000000000))^k)^500=((16^(s*4000000000000))^k)^861
    rw [←pow_mul,←pow_mul,←pow_mul,←pow_mul]
    apply congrArg (fun n : ℕ => (16:ℕ)^n)
    ring
  · change (16^(s*60000000000000))^k=((16^(s*4000000000000))^k)^15
    rw [←pow_mul,←pow_mul,←pow_mul]
    apply congrArg (fun n : ℕ => (16:ℕ)^n)
    ring

theorem rows_pos (s : ℕ) : 0<rows s := by unfold rows;positivity

/-- Fixed finite rational coefficient data supply their own height and
denominator; neither is an assumption on the recursive family. -/
theorem coefficient_invariants (s : ℕ) (h : Sample s) (ht : 0<copies s h) (k : ℕ) :
    EqualCopyCoefficientGrowth.Bound (terms s h ht k)
      ((ranks s*FiniteRationalCoefficients.height (CWHomogeneousCopies.terms s h))^k) ∧
    EqualCopyCoefficientGrowth.Cleared
      ((FiniteRationalCoefficients.denominator (CWHomogeneousCopies.terms s h))^k)
      (terms s h ht k) := by
  have hh := FiniteRationalCoefficients.recursive_invariants ht (CWHomogeneousCopies.terms s h) k
  exact ⟨⟨fun j x => hh.1.2.2 j (⟨0,ht⟩,pair k x),
    fun j y => hh.1.1 j (⟨0,ht⟩,pair k y),
    fun j z => hh.1.2.1 j (⟨0,ht⟩,pair k z)⟩,
    ⟨fun j x => hh.2.2.2 j (⟨0,ht⟩,pair k x),
     fun j y => hh.2.1 j (⟨0,ht⟩,pair k y),
     fun j z => hh.2.2.1 j (⟨0,ht⟩,pair k z)⟩⟩

theorem growth_identity (s : ℕ) :
    Real.exp ((CWTargetMarginals.size s:ℝ)*CWFiniteBase.growth)=
      (rows s:ℝ)^CWFiniteBase.exponent := by
  rw [Real.rpow_def_of_pos (by exact_mod_cast rows_pos s)]
  congr 1
  rw [rows,Nat.cast_pow,Real.log_pow,CWTargetMarginals.size_eq]
  norm_num [CWCanonicalType.period,CWFiniteBase.growth]
  ring

/-- One fixed positive integral base, with explicit rational decompositions
for every tensor power, at arithmetic rank exponent 16.7220001. -/
theorem exists_fixed_base : ∃ s : ℕ, 0<s ∧ ∃ h : Sample s, ∃ ht : 0<copies s h,
    ∀ k : ℕ,
      total (terms s h ht k)=FiniteMatrixTensor.coeff (C s k) (A s k) (B s k) ℚ ∧
      (Fintype.card (EqualCopyRecursion.Budget (ranks s) (copies s h) k):ℝ)≤
        (copies s h:ℝ)*(rows s:ℝ)^(CWFiniteBase.exponent*(k:ℝ)) := by
  obtain ⟨s,hs,h,ht,hb⟩ := CWFiniteBase.exists_positive_base
  refine ⟨s,hs,h,ht,fun k => ⟨terms_total s h ht k,?_⟩⟩
  rw [growth_identity] at hb
  rw [recursive_count,Nat.cast_mul,Nat.cast_pow,
    Real.rpow_mul (by exact_mod_cast (rows_pos s).le),Real.rpow_natCast]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hb k) (by positivity)

#print axioms terms_total
#print axioms dimensions
#print axioms aspect
#print axioms coefficient_invariants
#print axioms growth_identity
#print axioms exists_fixed_base
end ThinMatrix.CWRectangularRanks
