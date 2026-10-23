import HalfSourceScan
import CroppedGroupedSuffix

set_option autoImplicit false

/-! Cyclic averaging and the first light window. All raw coordinates are
assigned before any transform. The finite identity works for arbitrary
entangled sources; it does not assert equality of individual components. -/
namespace ThinMatrix.CyclicLightWindow
open scoped BigOperators

def count {k : ℕ} (b : Fin k → Bool) : ℕ := ∑ i, if b i then 1 else 0

def weight {k : ℕ} [NeZero k] (ell : ℕ) (b : Fin k → Bool) (s : Fin k) : ℕ :=
  ∑ j : Fin ell, if b (s+(⟨j.val%k,Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne k))⟩ : Fin k)) then 1 else 0

theorem count_le {k : ℕ} (b : Fin k → Bool) : count b ≤ k := by
  calc
    _ ≤ ∑ _i : Fin k, 1 := Finset.sum_le_sum (fun i _ => by split <;> omega)
    _ = _ := by simp

theorem total_weight {k : ℕ} [NeZero k] (ell : ℕ) (b : Fin k → Bool) :
    (∑ s, weight ell b s) = ell*count b := by
  unfold weight
  rw [Finset.sum_comm]
  have h (j : Fin ell) : (∑ s : Fin k, if b (s+(⟨j.val%k,Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne k))⟩ : Fin k)) then 1 else 0) = count b :=
    Equiv.sum_comp (Equiv.addRight (⟨j.val%k,Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne k))⟩ : Fin k)) (fun s => if b s then (1 : ℕ) else 0)
  simp only [h,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul]

theorem exists_light {k : ℕ} [NeZero k] (ell r : ℕ) (b : Fin k → Bool) (hb : count b ≤ r) :
    ∃ s, weight ell b s ≤ r*ell/k := by
  by_contra! h
  have hk : 0<k := Nat.pos_of_ne_zero (NeZero.ne k)
  have hs : k*(r*ell/k+1) ≤ ∑ s, weight ell b s := by
    calc
      _ = ∑ _s : Fin k, (r*ell/k+1) := by simp
      _ ≤ _ := Finset.sum_le_sum (fun s _ => by have hh := h s; omega)
  rw [total_weight] at hs
  have he : ell*count b ≤ r*ell := by nlinarith
  have hd := Nat.mod_lt (r*ell) hk
  have hm := Nat.mod_add_div (r*ell) k
  nlinarith

noncomputable def first {k : ℕ} [NeZero k] (ell r : ℕ) (b : Fin k → Bool) (hb : count b ≤ r) : Fin k :=
  HalfSourceCoverage.firstIndex (m:=2*(r*ell/k)) (weight ell b) (by
    simpa using exists_light ell r b hb)

theorem first_valid {k : ℕ} [NeZero k] (ell r : ℕ) (b : Fin k → Bool) (hb : count b ≤ r) :
    weight ell b (first ell r b hb) ≤ r*ell/k := by
  simpa only [first,Nat.mul_div_cancel_left _ (by decide : 0<2)] using
    (HalfSourceCoverage.firstIndex_valid (m:=2*(r*ell/k)) (weight ell b)
      (by simpa using exists_light ell r b hb))

theorem first_minimal {k : ℕ} [NeZero k] (ell r : ℕ) (b : Fin k → Bool) (hb : count b ≤ r)
    (s : Fin k) (hs : s<first ell r b hb) : r*ell/k < weight ell b s := by
  simpa using HalfSourceCoverage.firstIndex_minimal (m:=2*(r*ell/k)) (weight ell b)
    (by simpa using exists_light ell r b hb) s hs

noncomputable def component {k : ℕ} [NeZero k] {R : Type*} [Zero R] (ell r : ℕ)
    (b : Fin k → Bool) (s : Fin k) (x : R) : R :=
  if h : count b ≤ r then if s=first ell r b h then x else 0 else 0

theorem component_sum {k : ℕ} [NeZero k] {R : Type*} [AddCommMonoid R]
    (ell r : ℕ) (b : Fin k → Bool) (x : R) :
    (∑ s, component ell r b s x) = if count b≤r then x else 0 := by
  by_cases h : count b≤r <;> simp [component,h]

theorem component_zero {k : ℕ} [NeZero k] {R : Type*} [Zero R]
    (ell r : ℕ) (b : Fin k → Bool) (s : Fin k) (x : R)
    (h : r*ell/k < weight ell b s) : component ell r b s x = 0 := by
  unfold component
  split
  · split
    · subst s
      have hv := first_valid ell r b ‹count b≤r›
      omega
    · rfl
  · rfl

/-- Disjoint source partition commutes with any finite linear contraction.
All windows must be summed on each input before multiplying residuals. -/
theorem contraction_sum {k : ℕ} [NeZero k] {W R : Type*} [Fintype W] [CommRing R]
    (ell r : ℕ) (bits : W → Fin k → Bool) (X K : W → R) :
    (∑ s : Fin k, ∑ w, K w*component ell r (bits w) s (X w)) =
      ∑ w, K w*(if count (bits w)≤r then X w else 0) := by
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum,component_sum]

#print axioms count_le
#print axioms total_weight
#print axioms exists_light
#print axioms first_valid
#print axioms first_minimal
#print axioms component_sum
#print axioms component_zero
#print axioms contraction_sum
end ThinMatrix.CyclicLightWindow
