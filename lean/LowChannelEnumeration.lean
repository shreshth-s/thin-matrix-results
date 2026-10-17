import CacheCardinality
import Mathlib.Data.List.Sublists
import Mathlib.Data.List.Sort

/-!
# Direct capped channel member-list enumeration

The executable recursion visits only the capped subset branches. Each returned
channel is a list of its members, preserving the physical finRange order.
The joint counter pays recursive calls, list append/map visits and branch work;
no full powerset or noncomputable finite-set-to-list conversion is executed.
Counters are finite list/coordinate operation sites; integer/address bit pricing
and compilation to a machine remain separate.
-/

namespace ThinMatrix.LowChannelEnumeration
open scoped BigOperators

structure Result (α : Type*) where
  members : List (List α)
  work : ℕ

/-- The empty channel survives every cap. Positive caps branch on including
or omitting the next physical position; zero caps stop immediately. -/
def generate {α : Type*} : List α → ℕ → Result α
  | [], _ => ⟨[[]], 1⟩
  | _ :: _, 0 => ⟨[[]], 1⟩
  | a :: tail, t+1 =>
      let without :=  generate tail (t+1)
      let take := generate tail t
      ⟨without.members ++ take.members.map (List.cons a),
        without.work + take.work + without.members.length + take.members.length + 6⟩

theorem nil_mem_generate {α : Type*} (input : List α) (t : ℕ) :
    [] ∈ (generate input t).members := by
  induction input generalizing t with
  | nil => simp [generate]
  | cons a tail ih =>
      cases t with
      | zero => simp [generate]
      | succ t => simpa only [generate] using List.mem_append_left ((generate tail t).members.map (List.cons a)) (ih (t+1))

theorem mem_generate {α : Type*} (input : List α) (t : ℕ) (xs : List α) :
    xs ∈ (generate input t).members ↔ xs.Sublist input ∧ xs.length ≤ t := by
  induction input generalizing t xs with
  | nil => cases xs <;> simp [generate]
  | cons a tail ih =>
      cases t with
      | zero =>
          simp only [generate, List.mem_singleton]
          constructor
          · intro h; subst xs; simp
          · intro h
            exact List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero h.2)
      | succ t =>
          simp only [generate, List.mem_append, List.mem_map]
          constructor
          · rintro (h | ⟨ys, hy, rfl⟩)
            · obtain ⟨hs, hl⟩ := (ih (t+1) xs).mp h
              exact ⟨hs.cons a, hl⟩
            · obtain ⟨hs, hl⟩ := (ih t ys).mp hy
              exact ⟨hs.cons_cons a, by simp only [List.length_cons]; omega⟩
          · rintro ⟨hs, hl⟩
            cases xs with
            | nil => exact Or.inl (nil_mem_generate tail (t+1))
            | cons b bs =>
                rcases List.cons_sublist_cons'.mp hs with hskip | ⟨he, htail⟩
                · exact Or.inl ((ih (t+1) (b::bs)).mpr ⟨hskip, hl⟩)
                · subst b
                  exact Or.inr ⟨bs, (ih t bs).mpr ⟨htail, by simp only [List.length_cons] at hl; omega⟩, rfl⟩

theorem generated_member_nodup {α : Type*} (input : List α) (hn : input.Nodup)
    (t : ℕ) (xs : List α) (hx : xs ∈ (generate input t).members) : xs.Nodup :=
  hn.sublist ((mem_generate input t xs).mp hx).1

theorem generate_nodup {α : Type*} (input : List α) (hn : input.Nodup) (t : ℕ) :
    (generate input t).members.Nodup := by
  induction input generalizing t with
  | nil => simp [generate]
  | cons a tail ih =>
      obtain ⟨ha, ht⟩ := List.nodup_cons.mp hn
      cases t with
      | zero => simp [generate]
      | succ t =>
          simp only [generate]
          apply List.nodup_append'.mpr
          refine ⟨ih ht (t+1), (ih ht t).map (by
            intro xs ys he; exact (List.cons.inj he).2), ?_⟩
          apply List.disjoint_left.mpr
          intro xs hx hy
          obtain ⟨ys, hy, rfl⟩ := List.mem_map.mp hy
          exact ha (((mem_generate tail (t+1) (a::ys)).mp hx).1.subset (by simp))

/-- Every actual list operation belongs to the same recursion that returns
the channels. The bound includes all internal branches and list construction. -/
theorem generate_work_le {α : Type*} (input : List α) (t : ℕ) :
    (generate input t).work ≤ 8*(input.length+1)*(generate input t).members.length := by
  induction input generalizing t with
  | nil => simp [generate]
  | cons a tail ih =>
      cases t with
      | zero => simp [generate]; omega
      | succ t =>
          have ho := ih (t+1)
          have hi := ih t
          have hp : 1 ≤ (generate tail (t+1)).members.length :=
            List.length_pos_iff.mpr (List.ne_nil_of_mem (nil_mem_generate tail (t+1)))
          simp only [generate, List.length_append, List.length_map, List.length_cons]
          nlinarith

/-- Actual physical channel member lists. -/
def members (k t : ℕ) : List (List (Fin k)) := (generate (List.finRange k) t).members

/-- The initial physical-position list is charged in addition to the joint recursion. -/
def work (k t : ℕ) : ℕ := 8*k + (generate (List.finRange k) t).work

@[simp] theorem mem_members (k t : ℕ) (xs : List (Fin k)) :
    xs ∈ members k t ↔ xs.Sublist (List.finRange k) ∧ xs.length ≤ t :=
  mem_generate _ _ _

theorem members_nodup (k t : ℕ) : (members k t).Nodup :=
  generate_nodup _ (List.nodup_finRange k) t

theorem member_nodup (k t : ℕ) (xs : List (Fin k)) (hx : xs ∈ members k t) : xs.Nodup :=
  generated_member_nodup _ (List.nodup_finRange k) t xs hx

theorem member_length_le (k t : ℕ) (xs : List (Fin k)) (hx : xs ∈ members k t) :
    xs.length ≤ t := ((mem_members k t xs).mp hx).2

theorem member_length_le_dimension (k t : ℕ) (xs : List (Fin k)) (hx : xs ∈ members k t) :
    xs.length ≤ k := by
  simpa using ((mem_members k t xs).mp hx).1.length_le

/-- Finite sets are formed from the already enumerated member lists. -/
def sets (k t : ℕ) : List (Finset (Fin k)) := (members k t).map List.toFinset

theorem sets_nodup (k t : ℕ) : (sets k t).Nodup := by
  apply List.Nodup.map_on _ (members_nodup k t)
  intro xs hx ys hy heq
  have hsx := ((List.sortedLT_finRange k).pairwise).sublist ((mem_members k t xs).mp hx).1
  have hsy := ((List.sortedLT_finRange k).pairwise).sublist ((mem_members k t ys).mp hy).1
  apply hsx.eq_of_mem_iff hsy
  intro i
  simpa using Finset.ext_iff.mp heq i

theorem mem_sets (k t : ℕ) (C : Finset (Fin k)) : C ∈ sets k t ↔ C.card ≤ t := by
  constructor
  · intro h
    obtain ⟨xs, hx, rfl⟩ := List.mem_map.mp h
    rw [List.toFinset_card_of_nodup (member_nodup k t xs hx)]
    exact member_length_le k t xs hx
  · intro hC
    let xs := (List.finRange k).filter (fun i => i ∈ C)
    have hxs : xs.toFinset = C := by
      ext i
      simp [xs]
    have hnd : xs.Nodup := (List.nodup_finRange k).filter _
    have hlen : xs.length ≤ t := by
      rw [← List.toFinset_card_of_nodup hnd, hxs]
      exact hC
    apply List.mem_map.mpr
    exact ⟨xs, (mem_members k t xs).mpr ⟨List.filter_sublist, hlen⟩, hxs⟩

theorem sets_toFinset (k t : ℕ) :
    (sets k t).toFinset = Finset.univ.filter (fun C : Finset (Fin k) => C.card ≤ t) := by
  ext C
  simp [mem_sets]

theorem members_length (k t : ℕ) : (members k t).length = CacheCardinality.channelBall k t := by
  have hc := CacheCardinality.capped_subsets_card (Fin k) t
  have hsets : (sets k t).length = CacheCardinality.channelBall k t := by
    rw [← List.toFinset_card_of_nodup (sets_nodup k t), sets_toFinset]
    simpa only [CacheCardinality.CappedSubsets, Fintype.card_subtype, Fintype.card_fin] using hc
  simpa only [sets, List.length_map] using hsets

theorem member_card_le (k t : ℕ) (xs : List (Fin k)) (hx : xs ∈ members k t) :
    xs.toFinset.card ≤ t ∧ xs.toFinset.card ≤ k := by
  rw [List.toFinset_card_of_nodup (member_nodup k t xs hx)]
  exact ⟨member_length_le k t xs hx, member_length_le_dimension k t xs hx⟩

@[simp] theorem sets_length (k t : ℕ) : (sets k t).length = CacheCardinality.channelBall k t := by
  simp only [sets, List.length_map, members_length]

/-- Physical position formation and every recursive/list site fit a linear
factor in k times the exact capped channel count. -/
theorem work_le (k t : ℕ) : work k t ≤ 16*(k+1)*CacheCardinality.channelBall k t := by
  have h := generate_work_le (List.finRange k) t
  have hp : 1 ≤ (members k t).length :=
    List.length_pos_iff.mpr (List.ne_nil_of_mem (nil_mem_generate (List.finRange k) t))
  rw [members_length] at hp
  have hgen : (generate (List.finRange k) t).work ≤ 8*(k+1)*CacheCardinality.channelBall k t := by
    simpa only [List.length_finRange, ← members_length, members] using h
  unfold work
  nlinarith

def memberCells (k t : ℕ) : ℕ := ((members k t).map List.length).sum

theorem memberCells_le (k t : ℕ) : memberCells k t ≤ k*CacheCardinality.channelBall k t := by
  have h := List.sum_le_sum (fun xs hx => member_length_le_dimension k t xs hx)
  change ((members k t).map List.length).sum ≤ _
  calc
    _ ≤ ((members k t).map (fun _ => k)).sum := h
    _ = (members k t).length * k := by simp
    _ = _ := by rw [members_length, Nat.mul_comm]

#print axioms mem_members
#print axioms members_nodup
#print axioms member_nodup
#print axioms sets_nodup
#print axioms mem_sets
#print axioms members_length
#print axioms work_le
#print axioms memberCells_le

end ThinMatrix.LowChannelEnumeration
