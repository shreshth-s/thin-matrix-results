import CWMultinomialSurvival

set_option autoImplicit false
namespace ThinMatrix.CWTypePrimeChoice
open CWSixBlocks CWTypeRegularity CWBlockWords CWTypeCollisionCount CWTypeCardinalities CWMultinomialSurvival CWQuantitativeCleanup

theorem exists_prime (D : ℕ) (hD : 3≤D) : ∃ M : ℕ,M.Prime ∧ 2*D<M ∧ M≤4*D := by
  obtain ⟨M,hp,hl,hu⟩ := Nat.exists_prime_lt_and_le_two_mul (2*D) (by omega)
  exact ⟨M,hp,hl,by omega⟩

def selected (n : ℕ) (reference : Word n) : ℕ :=
  Nat.find (exists_prime (degreeSum n reference) (by rw [degreeSum_eq];exact totalDegree_ge_three n reference))

theorem selected_spec (n : ℕ) (reference : Word n) :
    (selected n reference).Prime ∧ 2*degreeSum n reference<selected n reference ∧
      selected n reference≤4*degreeSum n reference :=
  Nat.find_spec (exists_prime (degreeSum n reference) (by rw [degreeSum_eq];exact totalDegree_ge_three n reference))

theorem selected_gt_two (n : ℕ) (reference : Word n) : 2<selected n reference := by
  have hd := totalDegree_ge_three n reference
  rw [← degreeSum_eq] at hd
  have hp := (selected_spec n reference).2.1
  omega

instance selected_prime (n : ℕ) (reference : Word n) : Fact (Nat.Prime (selected n reference)) :=
  ⟨(selected_spec n reference).1⟩

theorem selected_survival (n : ℕ) (hn : 0<n) (reference : Word n)
    (B : Finset (ZMod (selected n reference)))
    (hB : ThreeAPFree (B : Set (ZMod (selected n reference)))) :
    ∃ r : CWHashFibers.Sample (ZMod (selected n reference)) n,
      (jointCount n reference:ℚ)*B.card/(2*(selected n reference)^2)≤
        (survivors (selected n reference) n reference B r).card := by
  apply exists_survivors_half (selected n reference) (selected_gt_two n reference) n hn reference
  · have hp := (selected_spec n reference).2.1
    omega
  · exact hB

def smallestMarginal (n : ℕ) (reference : Word n) : ℕ :=
  min (marginalCount n reference cx) (min (marginalCount n reference cy) (marginalCount n reference cz))

theorem smallest_times_degree (n : ℕ) (reference : Word n) :
    smallestMarginal n reference*degreeSum n reference≤3*jointCount n reference := by
  have hx : smallestMarginal n reference≤ marginalCount n reference cx := min_le_left _ _
  have hy : smallestMarginal n reference≤ marginalCount n reference cy := (min_le_right _ _).trans (min_le_left _ _)
  have hz : smallestMarginal n reference≤ marginalCount n reference cz := (min_le_right _ _).trans (min_le_right _ _)
  have hx' := Nat.mul_le_mul_right (degree n reference cx) hx
  have hy' := Nat.mul_le_mul_right (degree n reference cy) hy
  have hz' := Nat.mul_le_mul_right (degree n reference cz) hz
  rw [x_factorization] at hx'
  rw [y_factorization] at hy'
  rw [z_factorization] at hz'
  rw [degreeSum_eq,totalDegree,Nat.mul_add,Nat.mul_add]
  omega

theorem smallest_times_selected (n : ℕ) (reference : Word n) :
    smallestMarginal n reference*selected n reference≤12*jointCount n reference := by
  have h := Nat.mul_le_mul_left (smallestMarginal n reference) (selected_spec n reference).2.2
  have hd := smallest_times_degree n reference
  nlinarith

theorem density_bound (S T B M : ℕ) (hM : 0<M) (h : S*M≤12*T) :
    (S:ℚ)*B/(24*M)≤(T:ℚ)*B/(2*M^2) := by
  have hm : (0:ℚ)<M := by exact_mod_cast hM
  have hh : (S:ℚ)*M≤12*T := by exact_mod_cast h
  have he : (T:ℚ)*B/(2*M^2)-(S:ℚ)*B/(24*M)=
      ((12:ℚ)*T-S*M)*B/(24*M^2) := by field_simp;ring
  apply sub_nonneg.mp
  rw [he]
  exact div_nonneg (mul_nonneg (sub_nonneg.mpr hh) (Nat.cast_nonneg B)) (by positivity)

/-- The actual selected prime and cleanup retain at least one twenty-fourth
of the smallest marginal type class times the supplied bucket-set density.
Constructing a dense progression-free set and proving its asymptotic density
are separate, still-missing obligations. -/
theorem selected_density_survival (n : ℕ) (hn : 0<n) (reference : Word n)
    (B : Finset (ZMod (selected n reference)))
    (hB : ThreeAPFree (B : Set (ZMod (selected n reference)))) :
    ∃ r : CWHashFibers.Sample (ZMod (selected n reference)) n,
      (smallestMarginal n reference:ℚ)*B.card/(24*selected n reference)≤
        (survivors (selected n reference) n reference B r).card := by
  obtain ⟨r,hr⟩ := selected_survival n hn reference B hB
  exact ⟨r,(density_bound _ _ _ _ (by have := selected_gt_two n reference;omega)
    (smallest_times_selected n reference)).trans hr⟩

#print axioms selected
#print axioms exists_prime
#print axioms selected_spec
#print axioms selected_gt_two
#print axioms selected_prime
#print axioms selected_survival
#print axioms smallest_times_degree
#print axioms smallest_times_selected
#print axioms density_bound
#print axioms selected_density_survival
end ThinMatrix.CWTypePrimeChoice
