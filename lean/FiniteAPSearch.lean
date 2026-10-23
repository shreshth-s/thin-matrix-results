import Mathlib

set_option autoImplicit false

/-! An executable exhaustive reference construction. This file proves the
returned set's properties, not an efficient generation-cost bound. -/
namespace ThinMatrix.FiniteAPSearch

def Good (s : Finset ℕ) : Prop := ∀ a ∈ s,∀ b ∈ s,∀ c ∈ s,a+c=b+b → a=b
instance (s : Finset ℕ) : Decidable (Good s) := inferInstanceAs (Decidable (∀ a ∈ s,∀ b ∈ s,∀ c ∈ s,_))

theorem good_iff (s : Finset ℕ) : Good s ↔ ThreeAPFree (s : Set ℕ) := Iff.rfl

def subsets : ℕ → List (Finset ℕ)
  | 0 => [∅]
  | n+1 => subsets n ++ (subsets n).map (insert n)

theorem mem_subsets (N : ℕ) (s : Finset ℕ) : s ∈ subsets N ↔ s ⊆ Finset.range N := by
  induction N generalizing s with
  | zero => simp [subsets]
  | succ N ih =>
      simp only [subsets,List.mem_append,List.mem_map]
      constructor
      · rintro (hs | ⟨t,ht,rfl⟩)
        · exact (ih s).mp hs |>.trans (Finset.range_mono (by omega))
        · exact Finset.insert_subset_iff.mpr ⟨Finset.mem_range.mpr (by omega),
            ((ih t).mp ht).trans (Finset.range_mono (by omega))⟩
      · intro hs
        by_cases hn : N ∈ s
        · right
          refine ⟨s.erase N,(ih _).mpr ?_,Finset.insert_erase hn⟩
          intro a ha
          obtain ⟨hne,ha⟩ := Finset.mem_erase.mp ha
          have hb := Finset.mem_range.mp (hs ha)
          exact Finset.mem_range.mpr (by omega)
        · left
          apply (ih s).mpr
          intro a ha
          have hb := Finset.mem_range.mp (hs ha)
          have hne : a≠N := fun h => hn (h ▸ ha)
          exact Finset.mem_range.mpr (by omega)

theorem subsets_length (N : ℕ) : (subsets N).length=2^N := by
  induction N with
  | zero => rfl
  | succ N ih => simp [subsets,List.length_append,List.length_map,ih,pow_succ];omega

def pick : List (Finset ℕ) → Finset ℕ
  | [] => ∅
  | s::ss => let t := pick ss; if Good s ∧ t.card<s.card then s else t

theorem pick_good (ss : List (Finset ℕ)) : Good (pick ss) := by
  induction ss with
  | nil => simp [pick,Good]
  | cons s ss ih =>
      simp only [pick]
      split_ifs with h
      · exact h.1
      · exact ih

theorem pick_subset (ss : List (Finset ℕ)) (N : ℕ) (h : ∀ s ∈ ss,s ⊆ Finset.range N) :
    pick ss ⊆ Finset.range N := by
  induction ss with
  | nil => exact Finset.empty_subset _
  | cons s ss ih =>
      simp only [pick]
      split_ifs
      · exact h s (List.mem_cons_self ..)
      · exact ih (fun t ht => h t (List.mem_cons_of_mem _ ht))

theorem pick_card_ge (ss : List (Finset ℕ)) (s : Finset ℕ) (hs : s ∈ ss) (hg : Good s) :
    s.card≤(pick ss).card := by
  induction ss with
  | nil => simp at hs
  | cons t ts ih =>
      simp only [pick]
      split_ifs with h
      · rcases List.mem_cons.mp hs with rfl | hs
        · rfl
        · exact (ih hs).trans h.2.le
      · rcases List.mem_cons.mp hs with rfl | hs
        · exact le_of_not_gt (fun ht => h ⟨hg,ht⟩)
        · exact ih hs

def chosen (N : ℕ) : Finset ℕ := pick (subsets N)

theorem chosen_subset (N : ℕ) : chosen N ⊆ Finset.range N :=
  pick_subset _ N (fun s hs => (mem_subsets N s).mp hs)

theorem chosen_free (N : ℕ) : ThreeAPFree (chosen N : Set ℕ) := (good_iff _).mp (pick_good _)

theorem chosen_card (N : ℕ) : (chosen N).card=rothNumberNat N := by
  apply le_antisymm
  · exact ThreeAPFree.le_rothNumberNat _ (chosen_free N)
      (fun x hx => Finset.mem_range.mp (chosen_subset N hx)) rfl
  · obtain ⟨s,hs,hcard,hfree⟩ := rothNumberNat_spec N
    rw [← hcard]
    exact pick_card_ge _ s ((mem_subsets N s).mpr hs) ((good_iff s).mpr hfree)

theorem chosen_bound (N : ℕ) :
    (N:ℝ)*Real.exp (-4*Real.sqrt (Real.log N))≤(chosen N).card := by
  rw [chosen_card]
  exact Behrend.roth_lower_bound

#print axioms good_iff
#print axioms mem_subsets
#print axioms subsets_length
#print axioms pick_good
#print axioms pick_subset
#print axioms pick_card_ge
#print axioms chosen_subset
#print axioms chosen_free
#print axioms chosen_card
#print axioms chosen_bound
end ThinMatrix.FiniteAPSearch
