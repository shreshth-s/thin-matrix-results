import CWTargetExtractionRate
import EqualCopyRecursion
import FiniteDependentCopies

set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 2000000

/-! Reindex the actual extracted CW copies by fixed finite rectangular
coordinates, then apply the explicit equal-copy recursion. All bases and
coefficients remain rational; the noncomputable finite equivalences merely
choose fixed labels, not an input-dependent arithmetic oracle. -/
namespace ThinMatrix.CWHomogeneousCopies
open scoped BigOperators
open FiniteTrilinear FiniteDirectSum PolynomialDegeneration CWTargetExtractionRate

def rows (s : ℕ) := 16^(s*4000000000000)
def inners (s : ℕ) := 16^(s*60000000000000)
def cols (s : ℕ) := 16^(s*6888000000000)
def copies (s : ℕ) (h : Sample s) := Fintype.card (Copies s h)
def ranks (s : ℕ) := (10*CWTargetMarginals.size s+1)*18^(CWTargetMarginals.size s)

noncomputable def copyEquiv (s : ℕ) (h : Sample s) : Fin (copies s h) ≃ Copies s h :=
  (Fintype.equivFin _).symm

noncomputable def rowEquiv (s : ℕ) (h : Sample s) (w : Copies s h) :
    Fin (rows s) ≃ CWBlockWords.Rows 16 (CWTargetMarginals.size s) w.val :=
  (Equiv.cast (congrArg Fin (dimensions s h w).1.symm)).trans (Fintype.equivFin _).symm
noncomputable def innerEquiv (s : ℕ) (h : Sample s) (w : Copies s h) :
    Fin (inners s) ≃ CWBlockWords.Inners 16 (CWTargetMarginals.size s) w.val :=
  (Equiv.cast (congrArg Fin (dimensions s h w).2.1.symm)).trans (Fintype.equivFin _).symm
noncomputable def colEquiv (s : ℕ) (h : Sample s) (w : Copies s h) :
    Fin (cols s) ≃ CWBlockWords.Cols 16 (CWTargetMarginals.size s) w.val :=
  (Equiv.cast (congrArg Fin (dimensions s h w).2.2.symm)).trans (Fintype.equivFin _).symm

abbrev Left (s : ℕ) := Fin (rows s)×Fin (inners s)
abbrev Middle (s : ℕ) := Fin (inners s)×Fin (cols s)
abbrev Right (s : ℕ) := Fin (cols s)×Fin (rows s)

noncomputable def embedX (s : ℕ) (h : Sample s) (x : Fin (copies s h)×Left s) :
    CWIndependentCopies.XA (CWTargetMarginals.size s) (CWCanonicalType.reference s) (X s h) (Y s h) (Z s h) :=
  let w := copyEquiv s h x.1
  Sigma.mk w (rowEquiv s h w x.2.1,innerEquiv s h w x.2.2)
noncomputable def embedY (s : ℕ) (h : Sample s) (y : Fin (copies s h)×Middle s) :
    CWIndependentCopies.YA (CWTargetMarginals.size s) (CWCanonicalType.reference s) (X s h) (Y s h) (Z s h) :=
  let w := copyEquiv s h y.1
  Sigma.mk w (innerEquiv s h w y.2.1,colEquiv s h w y.2.2)
noncomputable def embedZ (s : ℕ) (h : Sample s) (z : Fin (copies s h)×Right s) :
    CWIndependentCopies.ZA (CWTargetMarginals.size s) (CWCanonicalType.reference s) (X s h) (Y s h) (Z s h) :=
  let w := copyEquiv s h z.1
  Sigma.mk w (colEquiv s h w z.2.1,rowEquiv s h w z.2.2)

def matrix (s : ℕ) : Tensor (Left s) (Middle s) (Right s) ℚ :=
  FiniteMatrixTensor.coeff _ _ _ ℚ

theorem directSum_reindex (s : ℕ) (h : Sample s) :
    restrict (CWIndependentCopies.directSum _ _ (X s h) (Y s h) (Z s h))
      (embedX s h) (embedY s h) (embedZ s h)=diagonal (Fin (copies s h)) (matrix s) := by
  exact FiniteDependentCopies.uniform
    (fun w : Copies s h => CWBlockWords.Rows 16 (CWTargetMarginals.size s) w.val)
    (fun w : Copies s h => CWBlockWords.Inners 16 (CWTargetMarginals.size s) w.val)
    (fun w : Copies s h => CWBlockWords.Cols 16 (CWTargetMarginals.size s) w.val)
    (copyEquiv s h) (rowEquiv s h) (innerEquiv s h) (colEquiv s h)

noncomputable def rankEquiv (s : ℕ) :
    Fin (ranks s) ≃ CWInterpolationProgram.Request (CWTargetMarginals.size s) :=
  (Equiv.cast (congrArg Fin (CWIndependentCopies.term_count _).symm)).trans (Fintype.equivFin _).symm

noncomputable def terms (s : ℕ) (h : Sample s) (j : Fin (ranks s)) :
    Term (Fin (copies s h)×Left s) (Fin (copies s h)×Middle s) (Fin (copies s h)×Right s) ℚ :=
  (CWIndependentCopies.terms (CWTargetMarginals.size s) (CWCanonicalType.reference s) (X s h) (Y s h) (Z s h) (rankEquiv s j)).restrict
    (embedX s h) (embedY s h) (embedZ s h)

theorem terms_total (s : ℕ) (h : Sample s) :
    total (terms s h)=diagonal (Fin (copies s h)) (matrix s) := by
  unfold terms
  rw [total_restrict]
  have hr : total (fun j => CWIndependentCopies.terms (CWTargetMarginals.size s) (CWCanonicalType.reference s) (X s h) (Y s h) (Z s h) (rankEquiv s j))=
      total (CWIndependentCopies.terms (CWTargetMarginals.size s) (CWCanonicalType.reference s) (X s h) (Y s h) (Z s h)) := by
    funext x y z
    exact (rankEquiv s).sum_comp (fun j =>
      (CWIndependentCopies.terms (CWTargetMarginals.size s) (CWCanonicalType.reference s) (X s h) (Y s h) (Z s h) j).tensor x y z)
  rw [hr,CWIndependentCopies.exact_decomposition,directSum_reindex]

noncomputable def recursiveTerms (s : ℕ) (h : Sample s) (ht : 0<copies s h) (k : ℕ) :=
  EqualCopyRecursion.single ht (terms s h) k

theorem recursive_total (s : ℕ) (h : Sample s) (ht : 0<copies s h) (k : ℕ) :
    total (recursiveTerms s h ht k)=tensorPower (matrix s) k :=
  EqualCopyRecursion.single_total ht (matrix s) (terms s h) (terms_total s h) k

theorem recursive_count (s : ℕ) (h : Sample s) (k : ℕ) :
    Fintype.card (EqualCopyRecursion.Budget (ranks s) (copies s h) k)=
      copies s h*((ranks s+copies s h-1)/copies s h)^k :=
  EqualCopyRecursion.budget_card _ _ _

#print axioms directSum_reindex
#print axioms terms_total
#print axioms recursive_total
#print axioms recursive_count
end ThinMatrix.CWHomogeneousCopies
