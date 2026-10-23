import CWTypeCardinalities

set_option autoImplicit false
namespace ThinMatrix.CWMultinomialSurvival
open CWSixBlocks CWBlockWords CWTypeCounts CWTypeRegularity CWTypeCollisionCount CWTypeCardinalities
open CWFilteredHashCounts CWQuantitativeCleanup

def degreeSum (n : ℕ) (reference : Word n) : ℕ :=
  jointCount n reference/marginalCount n reference cx+
  jointCount n reference/marginalCount n reference cy+
  jointCount n reference/marginalCount n reference cz

theorem degreeSum_eq (n : ℕ) (reference : Word n) : degreeSum n reference=totalDegree n reference := by
  simp only [degreeSum,totalDegree,x_degree,y_degree,z_degree]

theorem exact_collision_count (n : ℕ) (reference : Word n) :
    (allCollisions n reference).card=jointCount n reference*(degreeSum n reference-3) := by
  rw [degreeSum_eq,collision_identity,fullClass_card]
  rfl

theorem exists_survivors (M : ℕ) [Fact (Nat.Prime M)] (hM : 2<M) (n : ℕ) (hn : 0<n)
    (reference : Word n) (B : Finset (ZMod M)) (hB : ThreeAPFree (B : Set (ZMod M))) :
    ∃ r : CWHashFibers.Sample (ZMod M) n,
      (jointCount n reference:ℚ)*B.card/M^2-
        (jointCount n reference:ℚ)*(degreeSum n reference-3:ℕ)*B.card/M^3≤
        (survivors M n reference B r).card := by
  obtain ⟨r,hr⟩ := exists_survivors_regular M hM n hn reference B hB
  rw [fullClass_card,← degreeSum_eq] at hr
  exact ⟨r,hr⟩

theorem half_bound (T B M D : ℕ) (hM : 0<M) (hD : 2*(D-3)≤M) :
    (T:ℚ)*B/(2*M^2)≤(T:ℚ)*B/M^2-(T:ℚ)*(D-3:ℕ)*B/M^3 := by
  have hm : (0:ℚ)<M := by exact_mod_cast hM
  have hd : (2:ℚ)*(D-3:ℕ)≤M := by exact_mod_cast hD
  have he : (T:ℚ)*B/M^2-(T:ℚ)*(D-3:ℕ)*B/M^3-(T:ℚ)*B/(2*M^2)=
      (T:ℚ)*B*((M:ℚ)-2*(D-3:ℕ))/(2*M^3) := by field_simp;ring
  apply sub_nonneg.mp
  rw [he]
  exact div_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg T) (Nat.cast_nonneg B))
    (sub_nonneg.mpr hd)) (by positivity)

theorem exists_survivors_half (M : ℕ) [Fact (Nat.Prime M)] (hM : 2<M) (n : ℕ) (hn : 0<n)
    (reference : Word n) (hD : 2*(degreeSum n reference-3)≤M)
    (B : Finset (ZMod M)) (hB : ThreeAPFree (B : Set (ZMod M))) :
    ∃ r : CWHashFibers.Sample (ZMod M) n,
      (jointCount n reference:ℚ)*B.card/(2*M^2)≤(survivors M n reference B r).card := by
  obtain ⟨r,hr⟩ := exists_survivors M hM n hn reference B hB
  exact ⟨r,(half_bound _ _ _ _ (by omega) hD).trans hr⟩

#print axioms degreeSum_eq
#print axioms exact_collision_count
#print axioms exists_survivors
#print axioms half_bound
#print axioms exists_survivors_half
end ThinMatrix.CWMultinomialSurvival
