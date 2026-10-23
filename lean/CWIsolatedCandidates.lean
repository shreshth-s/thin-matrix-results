import CWTypeCounts
import FiniteCollisionCleanup

set_option autoImplicit false

namespace ThinMatrix.CWIsolatedCandidates
open scoped BigOperators
open PolynomialDegeneration CWPolynomialCertificate CWSixBlocks CWBlockWords CWTypeCounts

def Marginals (n : ℕ) (u v : Word n) : Prop :=
  (∀ a : Fin 3,count a n (wx n u)=count a n (wx n v)) ∧
  (∀ a : Fin 3,count a n (wy n u)=count a n (wy n v)) ∧
  (∀ a : Fin 3,count a n (wz n u)=count a n (wz n v))
instance (n : ℕ) (u v : Word n) : Decidable (Marginals n u v) :=
  inferInstanceAs (Decidable ((_ : Prop) ∧ _ ∧ _))

def candidates (n : ℕ) (reference : Word n) (X Y Z : Finset (Colors n)) : Finset (Word n) :=
  Finset.univ.filter (fun w => Marginals n w reference ∧ wx n w ∈ X ∧ wy n w ∈ Y ∧ wz n w ∈ Z)
def selected (n : ℕ) (reference : Word n) (X Y Z : Finset (Colors n)) : Finset (Word n) :=
  FiniteCollisionCleanup.keep (candidates n reference X Y Z) (wx n) (wy n) (wz n)

theorem mem_candidates (n : ℕ) (reference w : Word n) (X Y Z : Finset (Colors n)) :
    w ∈ candidates n reference X Y Z ↔
      Marginals n w reference ∧ wx n w ∈ X ∧ wy n w ∈ Y ∧ wz n w ∈ Z := by
  simp [candidates]

theorem selected_subset (n : ℕ) (reference : Word n) (X Y Z : Finset (Colors n)) :
    selected n reference X Y Z⊆candidates n reference X Y Z := FiniteCollisionCleanup.keep_subset _ _ _ _

theorem selected_counts (n : ℕ) (reference w : Word n) (X Y Z : Finset (Colors n))
    (hw : w ∈ selected n reference X Y Z) : ∀ b : Block,count b n w=count b n reference := by
  have h := ((mem_candidates n reference w X Y Z).mp (selected_subset n reference X Y Z hw)).1
  exact joint_counts_unique n w reference h.1 h.2.1 h.2.2

theorem cross_candidate (n : ℕ) (reference u v w : Word n) (X Y Z : Finset (Colors n))
    (hu : u ∈ candidates n reference X Y Z) (hv : v ∈ candidates n reference X Y Z)
    (hw : w ∈ candidates n reference X Y Z)
    (hc : Compatible n (wx n u) (wy n v) (wz n w)) :
    decodeWord n (wx n u) (wy n v) (wz n w) ∈ candidates n reference X Y Z := by
  have hu := (mem_candidates n reference u X Y Z).mp hu
  have hv := (mem_candidates n reference v X Y Z).mp hv
  have hw := (mem_candidates n reference w X Y Z).mp hw
  have h := decodeWord_colors n (wx n u) (wy n v) (wz n w) hc
  apply (mem_candidates n reference _ X Y Z).mpr
  exact ⟨⟨by simpa only [h.1] using hu.1.1,by simpa only [h.2.1] using hv.1.2.1,
    by simpa only [h.2.2] using hw.1.2.2⟩,by simpa only [h.1] using hu.2.1,
    by simpa only [h.2.1] using hv.2.2.1,by simpa only [h.2.2] using hw.2.2.2⟩

theorem no_cross (n : ℕ) (reference u v w : Word n) (X Y Z : Finset (Colors n))
    (hu : u ∈ selected n reference X Y Z) (hv : v ∈ selected n reference X Y Z)
    (hw : w ∈ selected n reference X Y Z)
    (hc : Compatible n (wx n u) (wy n v) (wz n w)) : u=v ∧ u=w := by
  have ht := cross_candidate n reference u v w X Y Z
    (selected_subset n reference X Y Z hu) (selected_subset n reference X Y Z hv)
    (selected_subset n reference X Y Z hw) hc
  have he := decodeWord_colors n (wx n u) (wy n v) (wz n w) hc
  exact FiniteCollisionCleanup.no_cross _ _ _ _ u v w _ hu hv hw ht he.1 he.2.1 he.2.2

theorem tensor_cross_zero {R : Type*} [CommRing R] (q n : ℕ) (reference u v w : Word n)
    (X Y Z : Finset (Colors n)) (hu : u ∈ selected n reference X Y Z)
    (hv : v ∈ selected n reference X Y Z) (hw : w ∈ selected n reference X Y Z)
    (hd : ¬ (u=v ∧ u=w)) (x : Rows q n u×Inners q n u)
    (y : Inners q n v×Cols q n v) (z : Cols q n w×Rows q n w) :
    tensorPower (target (R:=R) q) n (leftWord q n u x) (middleWord q n v y) (rightWord q n w z)=0 := by
  apply tensor_zero_of_incompatible
  rw [leftWord_color,middleWord_color,rightWord_color]
  exact fun hc => hd (no_cross n reference u v w X Y Z hu hv hw hc)

theorem retained_card (n : ℕ) (reference : Word n) (X Y Z : Finset (Colors n)) :
    (candidates n reference X Y Z).card ≤ (selected n reference X Y Z).card+
      (FiniteCollisionCleanup.collisions (candidates n reference X Y Z) (wx n) (wy n) (wz n)).card :=
  FiniteCollisionCleanup.retained_card _ _ _ _

#print axioms mem_candidates
#print axioms selected_subset
#print axioms selected_counts
#print axioms cross_candidate
#print axioms no_cross
#print axioms tensor_cross_zero
#print axioms retained_card
end ThinMatrix.CWIsolatedCandidates
