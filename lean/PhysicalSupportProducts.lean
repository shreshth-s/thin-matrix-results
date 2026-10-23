import ShiftedPhysicalHigh

set_option autoImplicit false
set_option maxRecDepth 6000
set_option maxHeartbeats 2000000

/-! Reindex retained mask positions to the exact physical support and its
complement. These products are the common geometry of executed LOW and HIGH. -/
namespace ThinMatrix.PhysicalSupportProducts
open PhysicalWordReindex ResidualFamilyKeys SourceFormation
open scoped BigOperators

variable {L m : ℕ}

def support (a : Mask L m) : Finset (Fin L) := cubeSupport a.bits.get

theorem selected_get (a : Mask L m) (i : Fin m) :
    selectedPosition a i=(ResidualLayout.selected a.bits).get (Fin.cast (selected_size a).symm i) := rfl

theorem remaining_get (a : Mask L m) (i : Fin (L-m)) :
    remainingPosition a i=(ResidualLayout.remaining a.bits).get (Fin.cast (remaining_size a).symm i) := rfl

theorem selected_mem (a : Mask L m) (i : Fin m) : selectedPosition a i∈support a := by
  rw [selected_get]
  simpa [support,cubeSupport] using (ResidualLayout.mem_selected a.bits _).mp (List.get_mem (ResidualLayout.selected a.bits) (Fin.cast (selected_size a).symm i))

theorem remaining_mem (a : Mask L m) (i : Fin (L-m)) : remainingPosition a i∈(support a)ᶜ := by
  rw [remaining_get]
  have h := (ResidualLayout.mem_remaining a.bits _).mp (List.get_mem (ResidualLayout.remaining a.bits) (Fin.cast (remaining_size a).symm i))
  simpa [support,cubeSupport,h]

theorem prod_selected {R : Type*} [CommMonoid R] (a : Mask L m) (F : Fin L → R) :
    (∏ i, F (selectedPosition a i))=∏ j∈support a, F j := by
  apply Finset.prod_bij (fun i _ => selectedPosition a i)
  · intro i _; exact selected_mem a i
  · intro i _ j _ he
    exact Sum.inl.inj ((layout a).symm.injective he)
  · intro j hj
    have hj' : j∈ResidualLayout.selected a.bits := (ResidualLayout.mem_selected a.bits j).mpr (by simpa [support,cubeSupport] using hj)
    obtain ⟨k,hk⟩ := List.get_of_mem hj'
    refine ⟨Fin.cast (selected_size a) k,Finset.mem_univ _,?_⟩
    simpa only [selected_get,Fin.cast_cast,Fin.cast_eq_self] using hk
  · intro i _; rfl

theorem prod_remaining {R : Type*} [CommMonoid R] (a : Mask L m) (F : Fin L → R) :
    (∏ i, F (remainingPosition a i))=∏ j∈(support a)ᶜ, F j := by
  apply Finset.prod_bij (fun i _ => remainingPosition a i)
  · intro i _; exact remaining_mem a i
  · intro i _ j _ he
    exact Sum.inr.inj ((layout a).symm.injective he)
  · intro j hj
    have hj' : j∈ResidualLayout.remaining a.bits := by
      simpa [support,cubeSupport,ResidualLayout.mem_remaining] using hj
    obtain ⟨k,hk⟩ := List.get_of_mem hj'
    refine ⟨Fin.cast (remaining_size a) k,Finset.mem_univ _,?_⟩
    simpa only [remaining_get,Fin.cast_cast,Fin.cast_eq_self] using hk
  · intro i _; rfl

#print axioms selected_get
#print axioms remaining_get
#print axioms selected_mem
#print axioms remaining_mem
#print axioms prod_selected
#print axioms prod_remaining
end ThinMatrix.PhysicalSupportProducts
