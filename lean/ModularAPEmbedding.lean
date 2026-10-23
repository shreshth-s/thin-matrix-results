import FiniteAPSearch

set_option autoImplicit false
namespace ThinMatrix.ModularAPEmbedding

def embed (M : ℕ) (s : Finset ℕ) : Finset (ZMod M) := s.image (fun x : ℕ => (x:ZMod M))

theorem cast_inj_below (M a b : ℕ) (ha : a<M) (hb : b<M) (h : (a:ZMod M)=b) : a=b := by
  have he := (ZMod.natCast_eq_natCast_iff' a b M).mp h
  simpa only [Nat.mod_eq_of_lt ha,Nat.mod_eq_of_lt hb] using he

theorem embed_card (M N : ℕ) (hNM : N≤M) (s : Finset ℕ) (hs : s ⊆ Finset.range N) :
    (embed M s).card=s.card := by
  apply Finset.card_image_of_injOn
  intro a ha b hb hab
  exact cast_inj_below M a b ((Finset.mem_range.mp (hs ha)).trans_le hNM)
    ((Finset.mem_range.mp (hs hb)).trans_le hNM) hab

theorem no_wrap (M N : ℕ) (hNM : 2*N≤M) (a b c : ℕ) (ha : a<N) (hb : b<N) (hc : c<N)
    (h : (a:ZMod M)+c=b+b) : a+c=b+b := by
  apply cast_inj_below M (a+c) (b+b) (by omega) (by omega)
  simpa only [Nat.cast_add] using h

theorem embed_free (M N : ℕ) (hNM : 2*N≤M) (s : Finset ℕ) (hs : s ⊆ Finset.range N)
    (hf : ThreeAPFree (s : Set ℕ)) : ThreeAPFree (embed M s : Set (ZMod M)) := by
  intro a ha b hb c hc h
  change a ∈ s.image (fun x : ℕ => (x:ZMod M)) at ha
  change b ∈ s.image (fun x : ℕ => (x:ZMod M)) at hb
  change c ∈ s.image (fun x : ℕ => (x:ZMod M)) at hc
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hb
  obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hc
  exact congrArg (fun t : ℕ => (t:ZMod M)) (hf hx hy hz
    (no_wrap M N hNM x y z (Finset.mem_range.mp (hs hx))
      (Finset.mem_range.mp (hs hy)) (Finset.mem_range.mp (hs hz)) h))

#print axioms cast_inj_below
#print axioms embed_card
#print axioms no_wrap
#print axioms embed_free
end ThinMatrix.ModularAPEmbedding
