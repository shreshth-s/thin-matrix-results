import HalfSourceBinarySelection
import Mathlib.Data.List.Sublists

set_option autoImplicit false

/-!
# Direct capped subset lists for grouped suffix coordinates

Generate each cardinality by the standard recursive fixed-length sublist
generator. No Cartesian family of Boolean words is generated and filtered.
The returned list contains each capped subset exactly once. Its exact length
is the binomial sum used by the grouped suffix layout. This file proves
enumeration and storage counts, not a binary execution bound for generation.
-/
namespace ThinMatrix.CappedSubsetList
open scoped BigOperators

def sized (n j : ℕ) : List (Finset (Fin n)) :=
  ((List.finRange n).sublistsLen j).map List.toFinset

theorem sized_length (n j : ℕ) : (sized n j).length = n.choose j := by
  simp [sized]

theorem mem_sized (n j : ℕ) (J : Finset (Fin n)) : J ∈ sized n j ↔ J.card = j := by
  constructor
  · intro h
    obtain ⟨xs,hxs,rfl⟩ := List.mem_map.mp h
    have h := List.mem_sublistsLen.mp hxs
    rw [List.toFinset_card_of_nodup (List.nodup_finRange n |>.sublist h.1),h.2]
  · intro h
    let xs := (List.finRange n).filter (fun i => decide (i ∈ J))
    have hset : xs.toFinset = J := by ext i; simp [xs]
    have hlen : xs.length = j := by
      rw [← List.toFinset_card_of_nodup ((List.nodup_finRange n).filter _),hset,h]
    exact List.mem_map.mpr ⟨xs,List.mem_sublistsLen.mpr ⟨List.filter_sublist,hlen⟩,hset⟩

theorem sized_toFinset (n j : ℕ) :
    (sized n j).toFinset = (Finset.univ : Finset (Fin n)).powersetCard j := by
  ext J
  simp [mem_sized]

theorem sized_nodup (n j : ℕ) : (sized n j).Nodup := by
  have h : (↑(sized n j) : Multiset (Finset (Fin n))).toFinset.card =
      (↑(sized n j) : Multiset (Finset (Fin n))).card := by
    change (sized n j).toFinset.card = (sized n j).length
    rw [sized_toFinset,Finset.card_powersetCard,sized_length,Finset.card_univ,Fintype.card_fin]
  simpa using Multiset.toFinset_card_eq_card_iff_nodup.mp h

def generate (n r : ℕ) : List (Finset (Fin n)) :=
  (List.range (r+1)).flatMap (sized n)

def count (n r : ℕ) : ℕ := ∑ j ∈ Finset.range (r+1), n.choose j

theorem mem_generate (n r : ℕ) (J : Finset (Fin n)) : J ∈ generate n r ↔ J.card ≤ r := by
  simp only [generate,List.mem_flatMap,List.mem_range,mem_sized]
  constructor
  · rintro ⟨j,hj,hJ⟩
    omega
  · intro h
    exact ⟨J.card,by omega,rfl⟩

theorem generate_nodup (n r : ℕ) : (generate n r).Nodup := by
  apply List.nodup_flatMap.mpr
  constructor
  · intro j _
    exact sized_nodup n j
  · apply (show (List.range (r+1)).Pairwise (· ≠ ·) from List.nodup_range).imp
    intro i j hij J hi hj
    have := (mem_sized n i J).mp hi
    have := (mem_sized n j J).mp hj
    exact hij (by omega)

theorem generate_length (n r : ℕ) : (generate n r).length = count n r := by
  simp only [generate,List.length_flatMap,sized_length,count]
  have he : (List.range (r+1)).toFinset = Finset.range (r+1) := by
    ext j
    simp
  rw [← he]
  exact (List.sum_toFinset (l := List.range (r+1))
    (fun j => n.choose j) List.nodup_range).symm

theorem generate_toFinset (n r : ℕ) :
    (generate n r).toFinset = Finset.univ.filter (fun J : Finset (Fin n) => J.card ≤ r) := by
  ext J
  simp [mem_generate]

theorem count_pos (n r : ℕ) : 0 < count n r := by
  rw [← generate_length]
  exact List.length_pos_iff.mpr (fun h => by
    have he := (mem_generate n r ∅).mpr (by simp)
    simp [h] at he)

/-- The enumeration may be retained as an array, with no hidden padding. -/
def array (n r : ℕ) : Array (Finset (Fin n)) := (generate n r).toArray

theorem array_size (n r : ℕ) : (array n r).size = count n r := by
  simp [array,generate_length]

theorem sum_array {R : Type*} [AddCommMonoid R] (n r : ℕ) (f : Finset (Fin n) → R) :
    ((array n r).toList.map f).sum =
      ∑ J ∈ Finset.univ.filter (fun J : Finset (Fin n) => J.card ≤ r), f J := by
  rw [← generate_toFinset, List.sum_toFinset f (generate_nodup n r)]
  simp only [array,List.toList_toArray]

#print axioms sized_length
#print axioms mem_sized
#print axioms sized_toFinset
#print axioms sized_nodup
#print axioms mem_generate
#print axioms generate_nodup
#print axioms generate_length
#print axioms generate_toFinset
#print axioms count_pos
#print axioms array_size
#print axioms sum_array
end ThinMatrix.CappedSubsetList
