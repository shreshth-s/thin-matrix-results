import CWTypeCollisionCount
import FiniteHistogramCounts

set_option autoImplicit false
namespace ThinMatrix.CWTypeCardinalities
open scoped BigOperators
open PolynomialDegeneration CWSixBlocks CWBlockWords CWTypeCounts CWCoordinatePermutations
open CWIsolatedCandidates CWFilteredHashCounts CWTypeRegularity

theorem word_type_card {A : Type*} [Fintype A] [DecidableEq A] (n : ℕ) (reference : PowerIndex A n) :
    Nat.card {w : PowerIndex A n // ∀ a,count a n w=count a n reference}=
      Nat.multinomial Finset.univ (fun a => count a n reference) := by
  rw [Nat.card_eq_fintype_card]
  calc
    _ = (FiniteHistogramCounts.typeClass (toFn n reference)).card := by
      rw [← Fintype.card_coe]
      apply Fintype.card_congr (Equiv.subtypeEquiv (funEquiv A n) ?_)
      intro w
      simp only [FiniteHistogramCounts.typeClass,Finset.mem_filter,Finset.mem_univ,true_and,count_hist]
      rfl
    _ = _ := by
      rw [FiniteHistogramCounts.typeClass_multinomial]
      congr 1
      funext a
      exact (count_hist n reference a).symm

theorem mem_full_iff_counts (n : ℕ) (reference w : Word n) :
    w ∈ fullClass n reference ↔ ∀ b,count b n w=count b n reference := by
  constructor
  · intro hw
    have h := (Finset.mem_filter.mp hw).2
    exact joint_counts_unique n w reference h.1 h.2.1 h.2.2
  · intro h
    obtain ⟨e,he⟩ := exists_permute n reference w (fun b => (h b).symm)
    rw [← he]
    exact (mem_permute n reference reference e).mpr (reference_mem n reference)

theorem fullClass_card (n : ℕ) (reference : Word n) :
    (fullClass n reference).card=Nat.multinomial Finset.univ (fun b => count b n reference) := by
  rw [← Fintype.card_coe,← Nat.card_eq_fintype_card]
  exact (Nat.card_congr (Equiv.subtypeEquivRight (fun w => mem_full_iff_counts n reference w))).trans
    (word_type_card n reference)

def marginalClass (n : ℕ) (x : Colors n) : Finset (Colors n) :=
  Finset.univ.filter (fun y => ∀ a,count a n y=count a n x)

theorem marginalClass_card (n : ℕ) (x : Colors n) :
    (marginalClass n x).card=Nat.multinomial Finset.univ (fun a => count a n x) := by
  rw [← Fintype.card_coe,← Nat.card_eq_fintype_card]
  exact (Nat.card_congr (Equiv.subtypeEquivRight (fun y => by simp only
    [marginalClass,Finset.mem_filter,Finset.mem_univ,true_and]))).trans (word_type_card n x)

theorem image_eq_marginal (n : ℕ) (reference : Word n) (k : Block → Fin 3)
    (hk : ∀ w ∈ fullClass n reference,∀ a,count a n (mapWord k n w)=count a n (mapWord k n reference)) :
    (fullClass n reference).image (mapWord k n)=marginalClass n (mapWord k n reference) := by
  ext x
  constructor
  · rintro hx
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hk w hw⟩
  · intro hx
    have h := (Finset.mem_filter.mp hx).2
    obtain ⟨e,he⟩ := exists_permute n (mapWord k n reference) x (fun a => (h a).symm)
    exact Finset.mem_image.mpr ⟨permute n e reference,
      (mem_permute n reference reference e).mpr (reference_mem n reference),
      (map_permute k n e reference).trans he⟩

theorem x_image (n : ℕ) (reference : Word n) :
    (fullClass n reference).image (wx n)=marginalClass n (wx n reference) :=
  image_eq_marginal n reference cx (fun _ hw => (Finset.mem_filter.mp hw).2.1)
theorem y_image (n : ℕ) (reference : Word n) :
    (fullClass n reference).image (wy n)=marginalClass n (wy n reference) :=
  image_eq_marginal n reference cy (fun _ hw => (Finset.mem_filter.mp hw).2.2.1)
theorem z_image (n : ℕ) (reference : Word n) :
    (fullClass n reference).image (wz n)=marginalClass n (wz n reference) :=
  image_eq_marginal n reference cz (fun _ hw => (Finset.mem_filter.mp hw).2.2.2)

theorem class_card_eq_image_mul_degree (n : ℕ) (reference : Word n) (k : Block → Fin 3)
    (hk : ∀ w ∈ fullClass n reference,(fiber n reference k (mapWord k n w)).card=degree n reference k) :
    (fullClass n reference).card=((fullClass n reference).image (mapWord k n)).card*degree n reference k := by
  rw [Finset.card_eq_sum_card_image (mapWord k n) (fullClass n reference)]
  calc
    _ = ∑ _x ∈ (fullClass n reference).image (mapWord k n),degree n reference k := by
      apply Finset.sum_congr rfl
      intro x hx
      obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hx
      exact hk w hw
    _ = _ := by simp

theorem marginalClass_pos (n : ℕ) (x : Colors n) : 0<(marginalClass n x).card := by
  apply Finset.card_pos.mpr
  exact ⟨x,Finset.mem_filter.mpr ⟨Finset.mem_univ _,fun _ => rfl⟩⟩

def jointCount (n : ℕ) (reference : Word n) : ℕ := Nat.multinomial Finset.univ (fun b => count b n reference)
def marginalCount (n : ℕ) (reference : Word n) (k : Block → Fin 3) : ℕ :=
  Nat.multinomial Finset.univ (fun a => count a n (mapWord k n reference))

theorem x_degree (n : ℕ) (reference : Word n) : degree n reference cx=jointCount n reference/marginalCount n reference cx := by
  apply Nat.eq_div_of_mul_eq_left
  · exact Nat.ne_of_gt (show 0 < marginalCount n reference cx from
      (marginalClass_pos n (wx n reference)).trans_eq (marginalClass_card n _))
  · have h := class_card_eq_image_mul_degree n reference cx (x_regular n reference)
    change (fullClass n reference).card=((fullClass n reference).image (wx n)).card*degree n reference cx at h
    rw [x_image,marginalClass_card,fullClass_card] at h
    exact (mul_comm _ _).trans h.symm

theorem y_degree (n : ℕ) (reference : Word n) : degree n reference cy=jointCount n reference/marginalCount n reference cy := by
  apply Nat.eq_div_of_mul_eq_left
  · exact Nat.ne_of_gt (show 0 < marginalCount n reference cy from
      (marginalClass_pos n (wy n reference)).trans_eq (marginalClass_card n _))
  · have h := class_card_eq_image_mul_degree n reference cy (y_regular n reference)
    change (fullClass n reference).card=((fullClass n reference).image (wy n)).card*degree n reference cy at h
    rw [y_image,marginalClass_card,fullClass_card] at h
    exact (mul_comm _ _).trans h.symm

theorem z_degree (n : ℕ) (reference : Word n) : degree n reference cz=jointCount n reference/marginalCount n reference cz := by
  apply Nat.eq_div_of_mul_eq_left
  · exact Nat.ne_of_gt (show 0 < marginalCount n reference cz from
      (marginalClass_pos n (wz n reference)).trans_eq (marginalClass_card n _))
  · have h := class_card_eq_image_mul_degree n reference cz (z_regular n reference)
    change (fullClass n reference).card=((fullClass n reference).image (wz n)).card*degree n reference cz at h
    rw [z_image,marginalClass_card,fullClass_card] at h
    exact (mul_comm _ _).trans h.symm

theorem x_factorization (n : ℕ) (reference : Word n) :
    marginalCount n reference cx*degree n reference cx=jointCount n reference := by
  have h := class_card_eq_image_mul_degree n reference cx (x_regular n reference)
  change (fullClass n reference).card=((fullClass n reference).image (wx n)).card*degree n reference cx at h
  rw [x_image,marginalClass_card,fullClass_card] at h
  exact h.symm

theorem y_factorization (n : ℕ) (reference : Word n) :
    marginalCount n reference cy*degree n reference cy=jointCount n reference := by
  have h := class_card_eq_image_mul_degree n reference cy (y_regular n reference)
  change (fullClass n reference).card=((fullClass n reference).image (wy n)).card*degree n reference cy at h
  rw [y_image,marginalClass_card,fullClass_card] at h
  exact h.symm

theorem z_factorization (n : ℕ) (reference : Word n) :
    marginalCount n reference cz*degree n reference cz=jointCount n reference := by
  have h := class_card_eq_image_mul_degree n reference cz (z_regular n reference)
  change (fullClass n reference).card=((fullClass n reference).image (wz n)).card*degree n reference cz at h
  rw [z_image,marginalClass_card,fullClass_card] at h
  exact h.symm

#print axioms word_type_card
#print axioms mem_full_iff_counts
#print axioms fullClass_card
#print axioms marginalClass_card
#print axioms image_eq_marginal
#print axioms x_image
#print axioms y_image
#print axioms z_image
#print axioms class_card_eq_image_mul_degree
#print axioms marginalClass_pos
#print axioms x_degree
#print axioms y_degree
#print axioms z_degree
#print axioms x_factorization
#print axioms y_factorization
#print axioms z_factorization
end ThinMatrix.CWTypeCardinalities
