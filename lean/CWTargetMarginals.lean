import CWCanonicalType
import CWTypeCardinalities
import TernaryEntropy

set_option autoImplicit false
namespace ThinMatrix.CWTargetMarginals
open scoped BigOperators
open PolynomialDegeneration CWSixBlocks CWBlockWords CWTypeCounts CWCanonicalType CWTypeCardinalities

def color : Fin 3 → Block → Fin 3 := ![cx,cy,cz]
def counts : Fin 3 → Fin 3 → ℕ :=
  ![![11200343770853,64000000000000,48656229147],
    ![4180500000000,66888000000000,4180500000000],
    ![64229156229147,10888000000000,131843770853]]

def size (s : ℕ) : ℕ := (build (fun b => s*targetCounts b)).length

theorem size_eq (s : ℕ) : size s=s*period := reference_length s

theorem counts_total (axis : Fin 3) : counts axis 0+counts axis 1+counts axis 2=period := by
  fin_cases axis <;> decide

theorem counts_pos (axis a : Fin 3) : 0<counts axis a := by
  fin_cases axis <;> fin_cases a <;> norm_num [counts]

theorem color_total (n : ℕ) (w : Colors n) :
    count (0:Fin 3) n w+count (1:Fin 3) n w+count (2:Fin 3) n w=n := by
  induction n with
  | zero => simp [count]
  | succ n ih =>
      obtain ⟨a,w⟩ := w
      have h := ih w
      fin_cases a <;> simp [count] <;> omega

/-- The exact actual marginal histograms, with integral scaling and no rounding. -/
theorem reference_marginals (s : ℕ) (axis a : Fin 3) :
    count a (size s) (mapWord (color axis) (size s) (reference s))=s*counts axis a := by
  have hm := marginal_counts (size s) (reference s)
  simp only [size,reference_counts] at hm
  have hx := (color_total (size s) (wx (size s) (reference s))).trans (size_eq s)
  have hy := (color_total (size s) (wy (size s) (reference s))).trans (size_eq s)
  have hz := (color_total (size s) (wz (size s) (reference s))).trans (size_eq s)
  norm_num [targetCounts,period] at hm hx hy hz
  simp only [wx,wy,wz] at hm hx hy hz
  simp only [size] at *
  fin_cases axis <;> fin_cases a <;> simp [color,counts] <;> omega

theorem marginal_coefficient (s : ℕ) (axis : Fin 3) :
    marginalCount (size s) (reference s) (color axis)=
      TernaryEntropy.coefficient (s*counts axis 0) (s*counts axis 1) (s*counts axis 2) := by
  unfold marginalCount TernaryEntropy.coefficient
  congr 1
  funext a
  rw [reference_marginals]
  fin_cases a <;> rfl

noncomputable def entropy (axis : Fin 3) : ℝ :=
  TernaryEntropy.entropy (counts axis 0) (counts axis 1) (counts axis 2)

theorem entropy_shannon (axis : Fin 3) : entropy axis=
    -∑ a : Fin 3, ((counts axis a:ℝ)/period)*Real.log ((counts axis a:ℝ)/period) := by
  have hp (a : Fin 3) : (0:ℝ)<counts axis a := by exact_mod_cast counts_pos axis a
  have ht : (counts axis 0:ℝ)+counts axis 1+counts axis 2=period := by exact_mod_cast counts_total axis
  unfold entropy
  rw [TernaryEntropy.entropy_shannon _ _ _ (hp 0) (hp 1) (hp 2),ht]
  simp only [Fin.sum_univ_succ]
  simp
  ring

theorem marginal_bounds (s : ℕ) (axis : Fin 3) :
    Real.exp ((size s:ℝ)*entropy axis)/(size s+1)^2 ≤ marginalCount (size s) (reference s) (color axis) ∧
    (marginalCount (size s) (reference s) (color axis):ℝ)≤Real.exp ((size s:ℝ)*entropy axis) := by
  have h := TernaryEntropy.coefficient_bounds (s*counts axis 0) (s*counts axis 1) (s*counts axis 2)
  have ht : s*counts axis 0+s*counts axis 1+s*counts axis 2=size s := by
    rw [size_eq,← counts_total axis];ring
  rw [ht,← marginal_coefficient] at h
  by_cases hs : s=0
  · simpa [hs,size_eq] using h
  · have hr : (s:ℝ)≠0 := by exact_mod_cast hs
    simpa only [Nat.cast_mul,TernaryEntropy.entropy_scale _ _ _ _ hr,entropy] using h

#print axioms size_eq
#print axioms counts_total
#print axioms counts_pos
#print axioms color_total
#print axioms reference_marginals
#print axioms marginal_coefficient
#print axioms entropy_shannon
#print axioms marginal_bounds
end ThinMatrix.CWTargetMarginals
