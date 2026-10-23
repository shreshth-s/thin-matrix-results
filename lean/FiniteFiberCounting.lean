import Mathlib

set_option autoImplicit false

namespace ThinMatrix.FiniteFiberCounting
open scoped BigOperators
variable {Ω A B : Type*} [Fintype Ω]

theorem card_by_fibers (P : Ω → Prop) [DecidablePred P] [DecidableEq B]
    (f : Ω → B) (S : Finset B) (h : ∀ r,P r → f r ∈ S) :
    Fintype.card {r : Ω // P r}=∑ b ∈ S,Fintype.card {r : Ω // P r ∧ f r=b} := by
  classical
  have he := Finset.card_eq_sum_card_fiberwise (s:=Finset.univ.filter P) (t:=S) (f:=f)
    (fun r hr => h r (Finset.mem_filter.mp hr).2)
  simpa [Fintype.card_subtype,Finset.filter_filter] using he

theorem transpose_card [DecidableEq A] (E : Finset A) (S : Ω → Finset A)
    (hs : ∀ r,S r⊆E) :
    (∑ r,(S r).card)=∑ a ∈ E,Fintype.card {r : Ω // a ∈ S r} := by
  classical
  have he (r : Ω) : S r=E.filter (fun a => a ∈ S r) := by
    ext a
    simp only [Finset.mem_filter]
    exact ⟨fun ha => ⟨hs r ha,ha⟩,fun ha => ha.2⟩
  have hc (r : Ω) : (S r).card=∑ a ∈ E,if a ∈ S r then 1 else 0 := by
    conv_lhs => rw [he]
    simp only [Finset.card_eq_sum_ones,Finset.sum_filter]
  simp_rw [hc]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp only [Fintype.card_subtype,Finset.card_eq_sum_ones,Finset.sum_filter]

theorem exists_survival [Nonempty Ω] (before kept collisions : Ω → ℕ)
    (h : ∀ r,before r≤kept r+collisions r) :
    ∃ r,Fintype.card Ω*kept r+∑ s,collisions s ≥ ∑ s,before s := by
  classical
  obtain ⟨r,_,hr⟩ := Finset.exists_max_image Finset.univ kept Finset.univ_nonempty
  refine ⟨r,?_⟩
  have hb := Finset.sum_le_sum (s:=Finset.univ) (fun s _ => h s)
  rw [Finset.sum_add_distrib] at hb
  have hk : (∑ s,kept s)≤Fintype.card Ω*kept r := by
    calc
      _ ≤ ∑ _s : Ω,kept r := Finset.sum_le_sum (fun s hs => hr s hs)
      _ = _ := by simp
  omega

#print axioms card_by_fibers
#print axioms transpose_card
#print axioms exists_survival
end ThinMatrix.FiniteFiberCounting
