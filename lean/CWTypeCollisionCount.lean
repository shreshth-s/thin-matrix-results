import CWTypeRegularity
import FiniteRegularCollisions
import CWFiniteSurvival

set_option autoImplicit false
namespace ThinMatrix.CWTypeCollisionCount
open CWSixBlocks CWBlockWords CWFilteredHashCounts CWQuantitativeCleanup CWTypeRegularity

def totalDegree (n : ℕ) (reference : Word n) : ℕ :=
  degree n reference cx+degree n reference cy+degree n reference cz

theorem totalDegree_ge_three (n : ℕ) (reference : Word n) : 3≤totalDegree n reference := by
  have hx := degree_pos n reference cx
  have hy := degree_pos n reference cy
  have hz := degree_pos n reference cz
  unfold totalDegree
  omega

theorem collision_identity (n : ℕ) (reference : Word n) :
    (allCollisions n reference).card=(fullClass n reference).card*(totalDegree n reference-3) := by
  exact FiniteRegularCollisions.regular_collisions_card (fullClass n reference) (wx n) (wy n) (wz n)
    (CWWordCollisions.xy_injective n) (CWWordCollisions.xz_injective n) (CWWordCollisions.yz_injective n)
    _ _ _ (degree_pos n reference cx) (degree_pos n reference cy) (degree_pos n reference cz)
    (fun w hw => x_regular n reference w hw) (fun w hw => y_regular n reference w hw)
    (fun w hw => z_regular n reference w hw)

theorem exists_survivors_regular (M : ℕ) [Fact (Nat.Prime M)] (hM : 2<M) (n : ℕ) (hn : 0<n)
    (reference : Word n) (B : Finset (ZMod M)) (hB : ThreeAPFree (B : Set (ZMod M))) :
    ∃ r : CWHashFibers.Sample (ZMod M) n,
      ((fullClass n reference).card:ℚ)*B.card/M^2-
        ((fullClass n reference).card:ℚ)*(totalDegree n reference-3:ℕ)*B.card/M^3≤
        (survivors M n reference B r).card := by
  obtain ⟨r,hr⟩ := CWFiniteSurvival.exists_survivors_rational M hM n hn reference B hB
  rw [collision_identity,Nat.cast_mul] at hr
  exact ⟨r,hr⟩

#print axioms totalDegree_ge_three
#print axioms collision_identity
#print axioms exists_survivors_regular
end ThinMatrix.CWTypeCollisionCount
