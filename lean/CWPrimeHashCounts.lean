import CWPairHashFibers

set_option autoImplicit false

namespace ThinMatrix.CWPrimeHashCounts
open CWBlockWords CWHashFibers CWPairHashFibers
variable (M : ℕ) [Fact (Nat.Prime M)]

theorem color_cast_injective (hM : 2<M) : Function.Injective (fun a : Fin 3 => (a.val:ZMod M)) := by
  intro a b hab
  apply Fin.ext
  have he := (ZMod.natCast_eq_natCast_iff' a.val b.val M).mp hab
  have ha : a.val<M := lt_of_lt_of_le a.isLt hM
  have hb : b.val<M := lt_of_lt_of_le b.isLt hM
  simpa only [Nat.mod_eq_of_lt ha,Nat.mod_eq_of_lt hb] using he

theorem two_nonzero (hM : 2<M) : (2:ZMod M)≠0 := by
  intro h
  have he := (ZMod.natCast_eq_natCast_iff' 2 0 M).mp (by simpa only [Nat.cast_ofNat,Nat.cast_zero] using h)
  norm_num [Nat.mod_eq_of_lt hM] at he

theorem random_space_card (n : ℕ) : Fintype.card (Sample (ZMod M) n)=M^(n+2) := by
  rw [sample_card,ZMod.card]

theorem single_bucket_card (hM : 2<M) (n : ℕ) (u : Word n) (c : ZMod M) :
    Fintype.card {r : Sample (ZMod M) n // WordEvent n u c r}=M^n := by
  rw [event_card (two_nonzero M hM) n _ _ _ (word_compatible n u) c,ZMod.card]

theorem shared_pair_bucket_card (hM : 2<M) (n : ℕ) (u v : Word n) (hne : u≠v)
    (hs : wx n u=wx n v ∨ wy n u=wy n v ∨ wz n u=wz n v) (c : ZMod M) :
    Fintype.card {r : Sample (ZMod M) n // WordEvent n u c r ∧ WordEvent n v c r}=M^(n-1) := by
  rw [pair_card (two_nonzero M hM) (color_cast_injective M hM) n u v hne hs c,ZMod.card]

#print axioms color_cast_injective
#print axioms two_nonzero
#print axioms random_space_card
#print axioms single_bucket_card
#print axioms shared_pair_bucket_card
end ThinMatrix.CWPrimeHashCounts
