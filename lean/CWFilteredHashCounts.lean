import CWPrimeHashCounts
import CWHashedCandidates
import FiniteFiberCounting

set_option autoImplicit false

namespace ThinMatrix.CWFilteredHashCounts
open scoped BigOperators
open PolynomialDegeneration CWBlockWords CWIsolatedCandidates CWHashedCandidates
open CWHashSeparation CWHashFibers CWPairHashFibers CWPrimeHashCounts

def fullClass (n : ℕ) (reference : Word n) : Finset (Word n) :=
  Finset.univ.filter (fun u => Marginals n u reference)

variable (M : ℕ) [Fact (Nat.Prime M)]
def filtered (n : ℕ) (reference : Word n) (B : Finset (ZMod M)) (r : Sample (ZMod M) n) : Finset (Word n) :=
  candidates n reference (allowedX n r.1 r.2.2 B) (allowedY n r.1 r.2.1 r.2.2 B)
    (allowedZ n r.1 r.2.1 r.2.2 B)

theorem mem_filtered (n : ℕ) (reference u : Word n) (B : Finset (ZMod M)) (r : Sample (ZMod M) n) :
    u ∈ filtered M n reference B r ↔ Marginals n u reference ∧
      hx n r.1 r.2.2 (wx n u) ∈ B ∧ hy n r.1 r.2.1 r.2.2 (wy n u) ∈ B ∧
      hz n r.1 r.2.1 r.2.2 (wz n u) ∈ B := by
  simp [filtered,mem_candidates,allowedX,allowedY,allowedZ]

theorem filtered_subset (n : ℕ) (reference : Word n) (B : Finset (ZMod M)) (r : Sample (ZMod M) n) :
    filtered M n reference B r⊆fullClass n reference := by
  intro u hu
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ u,((mem_filtered M n reference u B r).mp hu).1⟩

theorem fixed_bucket_iff (hM : 2<M) (n : ℕ) (reference u : Word n) (hu : u ∈ fullClass n reference)
    (B : Finset (ZMod M)) (hB : ThreeAPFree (B : Set (ZMod M))) (c : ZMod M) (hc : c ∈ B)
    (r : Sample (ZMod M) n) :
    (u ∈ filtered M n reference B r ∧ hx n r.1 r.2.2 (wx n u)=c) ↔ WordEvent n u c r := by
  constructor
  · intro h
    have he := candidate_same_bucket (two_nonzero M hM) n reference u r.1 r.2.1 r.2.2 B hB h.1
    exact ⟨h.2,he.2.trans (he.1.symm.trans h.2),he.1.symm.trans h.2⟩
  · intro h
    refine ⟨(mem_filtered M n reference u B r).mpr ⟨(Finset.mem_filter.mp hu).2,?_,?_,?_⟩,h.1⟩
    · rw [h.1];exact hc
    · rw [h.2.1];exact hc
    · rw [h.2.2];exact hc

theorem pair_fixed_bucket_iff (hM : 2<M) (n : ℕ) (reference u v : Word n)
    (hu : u ∈ fullClass n reference) (hv : v ∈ fullClass n reference)
    (hs : wx n u=wx n v ∨ wy n u=wy n v ∨ wz n u=wz n v)
    (B : Finset (ZMod M)) (hB : ThreeAPFree (B : Set (ZMod M))) (c : ZMod M) (hc : c ∈ B)
    (r : Sample (ZMod M) n) :
    ((u ∈ filtered M n reference B r ∧ v ∈ filtered M n reference B r) ∧ hx n r.1 r.2.2 (wx n u)=c) ↔
      WordEvent n u c r ∧ WordEvent n v c r := by
  constructor
  · rintro ⟨⟨hfu,hfv⟩,huc⟩
    have heu := (fixed_bucket_iff M hM n reference u hu B hB c hc r).mp ⟨hfu,huc⟩
    have hvB := ((mem_filtered M n reference v B r).mp hfv).2.1
    have hev := (fixed_bucket_iff M hM n reference v hv B hB _ hvB r).mp ⟨hfv,rfl⟩
    have hvc : hx n r.1 r.2.2 (wx n v)=c := by
      rcases hs with hX | hY | hZ
      · simpa only [← hX] using huc
      · calc
          _ = hy n r.1 r.2.1 r.2.2 (wy n v) := hev.2.1.symm
          _ = hy n r.1 r.2.1 r.2.2 (wy n u) := congrArg _ hY.symm
          _ = c := heu.2.1
      · calc
          _ = hz n r.1 r.2.1 r.2.2 (wz n v) := hev.2.2.symm
          _ = hz n r.1 r.2.1 r.2.2 (wz n u) := congrArg _ hZ.symm
          _ = c := heu.2.2
    exact ⟨heu,(fixed_bucket_iff M hM n reference v hv B hB c hc r).mp ⟨hfv,hvc⟩⟩
  · rintro ⟨heu,hev⟩
    have hfu := (fixed_bucket_iff M hM n reference u hu B hB c hc r).mpr heu
    have hfv := (fixed_bucket_iff M hM n reference v hv B hB c hc r).mpr hev
    exact ⟨⟨hfu.1,hfv.1⟩,hfu.2⟩

theorem candidate_samples_card (hM : 2<M) (n : ℕ) (reference u : Word n)
    (hu : u ∈ fullClass n reference) (B : Finset (ZMod M)) (hB : ThreeAPFree (B : Set (ZMod M))) :
    Fintype.card {r : Sample (ZMod M) n // u ∈ filtered M n reference B r}=B.card*M^n := by
  rw [FiniteFiberCounting.card_by_fibers (fun r : Sample (ZMod M) n => u ∈ filtered M n reference B r)
    (fun r => hx n r.1 r.2.2 (wx n u)) B
    (fun r hr => ((mem_filtered M n reference u B r).mp hr).2.1)]
  calc
    _ = ∑ _c ∈ B,M^n := by
      apply Finset.sum_congr rfl
      intro c hc
      rw [Fintype.card_congr (Equiv.subtypeEquivRight (fixed_bucket_iff M hM n reference u hu B hB c hc))]
      exact single_bucket_card M hM n u c
    _ = _ := by simp

theorem pair_samples_card (hM : 2<M) (n : ℕ) (reference u v : Word n)
    (hu : u ∈ fullClass n reference) (hv : v ∈ fullClass n reference) (hne : u≠v)
    (hs : wx n u=wx n v ∨ wy n u=wy n v ∨ wz n u=wz n v)
    (B : Finset (ZMod M)) (hB : ThreeAPFree (B : Set (ZMod M))) :
    Fintype.card {r : Sample (ZMod M) n // u ∈ filtered M n reference B r ∧ v ∈ filtered M n reference B r}=
      B.card*M^(n-1) := by
  rw [FiniteFiberCounting.card_by_fibers (fun r : Sample (ZMod M) n =>
    u ∈ filtered M n reference B r ∧ v ∈ filtered M n reference B r)
    (fun r => hx n r.1 r.2.2 (wx n u)) B
    (fun r hr => ((mem_filtered M n reference u B r).mp hr.1).2.1)]
  calc
    _ = ∑ _c ∈ B,M^(n-1) := by
      apply Finset.sum_congr rfl
      intro c hc
      rw [Fintype.card_congr (Equiv.subtypeEquivRight (pair_fixed_bucket_iff M hM n reference u v hu hv hs B hB c hc))]
      exact shared_pair_bucket_card M hM n u v hne hs c
    _ = _ := by simp

#print axioms mem_filtered
#print axioms filtered_subset
#print axioms fixed_bucket_iff
#print axioms pair_fixed_bucket_iff
#print axioms candidate_samples_card
#print axioms pair_samples_card
end ThinMatrix.CWFilteredHashCounts
