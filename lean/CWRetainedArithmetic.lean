import CWRectangularRanks
import RetainedEqualCopyCosts

set_option autoImplicit false
set_option maxRecDepth 4000

/-! The extracted rectangular base now feeds a stored recursive arithmetic
program. This counts ring operations and indexed controls; binary lowering
and the arbitrary-size matrix adapter remain separate obligations. -/
namespace ThinMatrix.CWRetainedArithmetic
open scoped BigOperators
open FiniteTrilinear FiniteDirectSum CWHomogeneousCopies CWTargetExtractionRate
open RecursiveTable RetainedEqualCopy RetainedEqualCopyCosts

def leftLayout (s : ℕ) := prod (fin (cols s)) (fin (rows s))
def middleLayout (s : ℕ) := prod (fin (rows s)) (fin (inners s))
def rightLayout (s : ℕ) := prod (fin (inners s)) (fin (cols s))

noncomputable def base (s : ℕ) (h : Sample s) :
    Base (ranks s) (CWHomogeneousCopies.copies s h) (leftLayout s) (middleLayout s) (rightLayout s) ℚ :=
  let d := CWHomogeneousCopies.terms s h
  ⟨store _ (fun x => (d x.1).right x.2),
    store _ (fun x => (d x.1).left x.2),store _ (fun x => (d x.1).middle x.2)⟩

def matrix (s : ℕ) := FiniteMatrixTensor.coeff (Fin (cols s)) (Fin (rows s)) (Fin (inners s)) ℚ

theorem base_total (s : ℕ) (h : Sample s) :
    total (base s h).terms=diagonal (Fin (CWHomogeneousCopies.copies s h)) (matrix s) := by
  have ht := CWHomogeneousCopies.terms_total s h
  funext x y z
  have hv := congrFun (congrFun (congrFun ht y) z) x
  change (∑ j,((base s h).terms j).tensor x y z)=_
  simp only [Base.terms,base,read_store,Term.tensor]
  have hc : (∑ j,(CWHomogeneousCopies.terms s h j).right x *
      (CWHomogeneousCopies.terms s h j).left y * (CWHomogeneousCopies.terms s h j).middle z)=
      total (CWHomogeneousCopies.terms s h) y z x := by
    apply Finset.sum_congr rfl;intro j _
    simp only [Term.tensor];ring
  rw [hc,hv]
  simp only [diagonal,matrix,CWHomogeneousCopies.matrix]
  rw [FiniteMatrixTensor.cyclic]
  by_cases hxy : x.1=y.1
  · simp [←hxy]
  · have hyx : y.1≠x.1 := Ne.symm hxy
    simp [hxy,hyx]

theorem axis_bound (s m : ℕ) (hm : m≤66888000000000) :
    (16:ℝ)^(s*m)≤(rows s:ℝ)^CWFiniteBase.exponent := by
  rw [← CWRectangularRanks.growth_identity]
  have hl : (0:ℝ)≤Real.log 16 := (Real.log_pos (by norm_num)).le
  have hnum : (m:ℝ)≤(4000000000000:ℝ)*CWFiniteBase.exponent := by
    have hmr : (m:ℝ)≤66888000000000 := by exact_mod_cast hm
    norm_num [CWFiniteBase.exponent] at *
    linarith
  have he : (s*m:ℕ)*Real.log 16≤(CWTargetMarginals.size s:ℝ)*CWFiniteBase.growth := by
    have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hnum (Nat.cast_nonneg s)) hl
    calc
      _ = (s:ℝ)*m*Real.log 16 := by push_cast;ring
      _ ≤ (s:ℝ)*(4000000000000*CWFiniteBase.exponent)*Real.log 16 := hh
      _ = _ := by
        rw [CWTargetMarginals.size_eq]
        norm_num [CWCanonicalType.period,CWFiniteBase.growth]
        ring
  calc
    _ = Real.exp (((s*m:ℕ):ℝ)*Real.log 16) := by
      rw [Real.exp_nat_mul,Real.exp_log (by norm_num : (0:ℝ)<16)]
    _ ≤ _ := Real.exp_le_exp.mpr he

theorem axes_bounded (s : ℕ) :
    ((leftLayout s).size:ℝ)≤(rows s:ℝ)^CWFiniteBase.exponent ∧
    ((middleLayout s).size:ℝ)≤(rows s:ℝ)^CWFiniteBase.exponent ∧
    ((rightLayout s).size:ℝ)≤(rows s:ℝ)^CWFiniteBase.exponent := by
  have hp (u v : ℕ) : ((16^(s*u)*16^(s*v):ℕ):ℝ)=(16:ℝ)^(s*(u+v)) := by
    simp only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,mul_add,pow_add]
  constructor
  · simpa only [leftLayout,prod,fin,cols,rows,hp] using axis_bound s 10888000000000 (by decide)
  constructor
  · simpa only [middleLayout,prod,fin,inners,rows,hp] using axis_bound s 64000000000000 (by decide)
  · simpa only [rightLayout,prod,fin,cols,inners,hp] using axis_bound s 66888000000000 (by decide)

def growthBase (s : ℕ) (h : Sample s) : ℕ :=
  max ((ranks s+CWHomogeneousCopies.copies s h-1)/CWHomogeneousCopies.copies s h)
    (max 1 (max (leftLayout s).size (max (middleLayout s).size (rightLayout s).size)))

theorem growth_bounds (s : ℕ) (h : Sample s)
    (hg : (((ranks s+CWHomogeneousCopies.copies s h-1)/CWHomogeneousCopies.copies s h:ℕ):ℝ)
      ≤(rows s:ℝ)^CWFiniteBase.exponent) :
    (growthBase s h:ℝ)≤(rows s:ℝ)^CWFiniteBase.exponent := by
  have ha := axes_bounded s
  have h1 : (1:ℝ)≤(rows s:ℝ)^CWFiniteBase.exponent :=
    Real.one_le_rpow (by exact_mod_cast CWRectangularRanks.rows_pos s) (by norm_num [CWFiniteBase.exponent])
  simpa only [growthBase,Nat.cast_max,Nat.cast_one] using
    max_le hg (max_le h1 (max_le ha.1 (max_le ha.2.1 ha.2.2)))

theorem exists_arithmetic_program : ∃ s : ℕ, 0<s ∧ ∃ h : Sample s,
    ∃ ht : 0<CWHomogeneousCopies.copies s h, ∃ C : ℕ, ∀ k : ℕ,
    ∀ x : Table (RetainedEqualCopy.copies (CWHomogeneousCopies.copies s h) (leftLayout s) k) ℚ,
    ∀ y : Table (RetainedEqualCopy.copies (CWHomogeneousCopies.copies s h) (middleLayout s) k) ℚ,
      (∀ z,read (run (leftLayout s) (middleLayout s) (rightLayout s) ht (base s h) k x y).value z=
        bilinear (PolynomialDegeneration.tensorPower (matrix s) k)
          (fun i => read x (z.1,i)) (fun j => read y (z.1,j)) z.2) ∧
      (((run (leftLayout s) (middleLayout s) (rightLayout s) ht (base s h) k x y).arithmetic+
        (run (leftLayout s) (middleLayout s) (rightLayout s) ht (base s h) k x y).control:ℕ):ℝ)≤
          C*(k+1)*(rows s:ℝ)^(CWFiniteBase.exponent*(k:ℝ)) := by
  obtain ⟨s,hs,h,ht,hg⟩ := CWFiniteBase.exists_positive_base
  rw [CWRectangularRanks.growth_identity] at hg
  let C := levelConstant (ranks s) (CWHomogeneousCopies.copies s h)
    (leftLayout s).size (middleLayout s).size (rightLayout s).size
  refine ⟨s,hs,h,ht,C,fun k x y => ⟨fun z => run_correct _ _ _ ht _ _ (base_total s h) k x y z,?_⟩⟩
  have hM : 1≤growthBase s h := (le_max_left _ _).trans (le_max_right _ _)
  have hG : (ranks s+CWHomogeneousCopies.copies s h-1)/CWHomogeneousCopies.copies s h≤growthBase s h := le_max_left _ _
  have hi : (leftLayout s).size≤growthBase s h :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hj : (middleLayout s).size≤growthBase s h :=
    (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  have ho : (rightLayout s).size≤growthBase s h :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  have hn := run_work_bound _ _ _ ht (base s h) (growthBase s h) hM hG hi hj ho k x y
  have hnR := (Nat.cast_le (α:=ℝ)).mpr hn
  push_cast at hnR ⊢
  apply hnR.trans
  rw [Real.rpow_mul (by exact_mod_cast (CWRectangularRanks.rows_pos s).le),Real.rpow_natCast]
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (by positivity) (growth_bounds s h hg) k) (by positivity)

#print axioms base_total
#print axioms axis_bound
#print axioms axes_bounded
#print axioms growth_bounds
#print axioms exists_arithmetic_program
end ThinMatrix.CWRetainedArithmetic
