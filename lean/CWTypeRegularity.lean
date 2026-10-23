import CWCoordinatePermutations
import CWFilteredHashCounts

set_option autoImplicit false
namespace ThinMatrix.CWTypeRegularity
open scoped BigOperators
open CWSixBlocks CWBlockWords CWTypeCounts CWCoordinatePermutations CWIsolatedCandidates CWFilteredHashCounts

def fiber (n : ℕ) (reference : Word n) (k : Block → Fin 3) (x : Colors n) : Finset (Word n) :=
  (fullClass n reference).filter (fun w => mapWord k n w=x)
def degree (n : ℕ) (reference : Word n) (k : Block → Fin 3) : ℕ :=
  (fiber n reference k (mapWord k n reference)).card

theorem reference_mem (n : ℕ) (reference : Word n) : reference ∈ fullClass n reference := by
  simp [fullClass,Marginals]

theorem mem_permute (n : ℕ) (reference w : Word n) (e : Equiv.Perm (Fin n)) :
    permute n e w ∈ fullClass n reference ↔ w ∈ fullClass n reference := by
  simp only [fullClass,Finset.mem_filter,Finset.mem_univ,true_and,Marginals,wx,wy,wz,
    map_permute,count_permute]

theorem fiber_card_eq (n : ℕ) (reference : Word n) (k : Block → Fin 3) (x y : Colors n)
    (h : ∀ a,count a n x=count a n y) :
    (fiber n reference k x).card=(fiber n reference k y).card := by
  obtain ⟨e,he⟩ := exists_permute n x y h
  rw [← Fintype.card_coe,← Fintype.card_coe]
  apply Fintype.card_congr (Equiv.subtypeEquiv (permute n e) ?_)
  intro w
  simp only [fiber,Finset.mem_filter,mem_permute,map_permute,← he]
  exact and_congr Iff.rfl (permute n e).injective.eq_iff.symm

theorem x_regular (n : ℕ) (reference w : Word n) (hw : w ∈ fullClass n reference) :
    (fiber n reference cx (wx n w)).card=degree n reference cx := by
  exact fiber_card_eq n reference cx _ _ (Finset.mem_filter.mp hw).2.1

theorem y_regular (n : ℕ) (reference w : Word n) (hw : w ∈ fullClass n reference) :
    (fiber n reference cy (wy n w)).card=degree n reference cy := by
  exact fiber_card_eq n reference cy _ _ (Finset.mem_filter.mp hw).2.2.1

theorem z_regular (n : ℕ) (reference w : Word n) (hw : w ∈ fullClass n reference) :
    (fiber n reference cz (wz n w)).card=degree n reference cz := by
  exact fiber_card_eq n reference cz _ _ (Finset.mem_filter.mp hw).2.2.2

theorem degree_pos (n : ℕ) (reference : Word n) (k : Block → Fin 3) : 0<degree n reference k := by
  exact Finset.card_pos.mpr ⟨reference,Finset.mem_filter.mpr ⟨reference_mem n reference,rfl⟩⟩

#print axioms reference_mem
#print axioms mem_permute
#print axioms fiber_card_eq
#print axioms x_regular
#print axioms y_regular
#print axioms z_regular
#print axioms degree_pos
end ThinMatrix.CWTypeRegularity
