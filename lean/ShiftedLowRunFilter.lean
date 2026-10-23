import RetainedDegreeRuns

set_option autoImplicit false
set_option maxHeartbeats 1200000

/-! Collapse a shared degree run before the LOW functional. Unequal source
degrees never pair; every equal degree inside the actual run interval occurs
once. No division, characteristic assumption or nonzero-source premise. -/
namespace ThinMatrix.ShiftedLowRunFilter
open TensorContraction ShiftedLowChannelFormula WalshEmbedding
open scoped BigOperators
variable {R A B : Type*} [CommRing R] [Fintype A] [Fintype B]

theorem weighted_sum {ι : Type*} (s : Finset ι) (F : ι → Polynomial R) (n t : ℕ) :
    weightedLow n t (∑ i∈s, F i)=∑ i∈s, weightedLow n t (F i) := by
  simp only [weightedLow,Polynomial.finsetSum_coeff,Finset.mul_sum]
  rw [Finset.sum_comm]

theorem weighted_zero (n t : ℕ) : weightedLow n t (0 : Polynomial R)=0 := by
  simp [weightedLow]

theorem run_filter (m n t : ℕ) (X : A → Polynomial R) (Y : B → Polynomial R)
    (dx : A → ℤ) (dy : B → ℤ) (K : A → B → Polynomial R) :
    (∑ d∈Finset.Icc (-(m:ℤ)) (m:ℤ), weightedLow n t
      (bilinear (fun a => if dx a=d then X a else 0) (fun b => if dy b=d then Y b else 0) K))=
      ∑ a, ∑ b, if dx a=dy b ∧ dx a∈Finset.Icc (-(m:ℤ)) (m:ℤ)
        then weightedLow n t (X a*Y b*K a b) else 0 := by
  classical
  simp only [bilinear,weighted_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro a _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro b _
  have term (d : ℤ) : weightedLow n t ((if dx a=d then X a else 0)*(if dy b=d then Y b else 0)*K a b)=
      if d=dx a then (if dx a=dy b then weightedLow n t (X a*Y b*K a b) else 0) else 0 := by
    by_cases hx : dx a=d <;> by_cases hy : dy b=d <;>
      simp_all [weighted_zero,eq_comm]
  simp_rw [term]
  by_cases he : dx a=dy b <;> by_cases hm : dx a∈Finset.Icc (-(m:ℤ)) (m:ℤ) <;> simp [he,hm]

#print axioms weighted_sum
#print axioms weighted_zero
#print axioms run_filter
end ThinMatrix.ShiftedLowRunFilter
