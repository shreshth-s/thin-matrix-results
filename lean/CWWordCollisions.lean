import CWIsolatedCandidates

set_option autoImplicit false

namespace ThinMatrix.CWWordCollisions
open PolynomialDegeneration CWSixBlocks CWBlockWords

theorem block_xy : Function.Injective (fun b : Block => (cx b,cy b)) := by
  intro a b h
  cases a <;> cases b <;> simp_all [cx,cy]
theorem block_xz : Function.Injective (fun b : Block => (cx b,cz b)) := by
  intro a b h
  cases a <;> cases b <;> simp_all [cx,cz]
theorem block_yz : Function.Injective (fun b : Block => (cy b,cz b)) := by
  intro a b h
  cases a <;> cases b <;> simp_all [cy,cz]

theorem map_pair_injective {A B C : Type*} (f : A → B) (g : A → C)
    (hfg : Function.Injective (fun a => (f a,g a))) (n : ℕ) :
    Function.Injective (fun w : PowerIndex A n => (mapWord f n w,mapWord g n w)) := by
  induction n with
  | zero =>
      intro a b _
      exact @Subsingleton.elim PUnit inferInstance a b
  | succ n ih =>
      intro a b h
      have hf := congrArg Prod.fst h
      have hg := congrArg Prod.snd h
      have hf1 : f a.1=f b.1 := congrArg (fun w : PowerIndex B (n+1) => w.1) hf
      have hg1 : g a.1=g b.1 := congrArg (fun w : PowerIndex C (n+1) => w.1) hg
      have hf2 : mapWord f n a.2=mapWord f n b.2 := congrArg (fun w : PowerIndex B (n+1) => w.2) hf
      have hg2 : mapWord g n a.2=mapWord g n b.2 := congrArg (fun w : PowerIndex C (n+1) => w.2) hg
      have hh := hfg (Prod.ext hf1 hg1)
      have ht := ih (Prod.ext hf2 hg2)
      exact Prod.ext hh ht

theorem xy_injective (n : ℕ) : Function.Injective (fun w : Word n => (wx n w,wy n w)) :=
  map_pair_injective cx cy block_xy n
theorem xz_injective (n : ℕ) : Function.Injective (fun w : Word n => (wx n w,wz n w)) :=
  map_pair_injective cx cz block_xz n
theorem yz_injective (n : ℕ) : Function.Injective (fun w : Word n => (wy n w,wz n w)) :=
  map_pair_injective cy cz block_yz n

#print axioms block_xy
#print axioms block_xz
#print axioms block_yz
#print axioms map_pair_injective
#print axioms xy_injective
#print axioms xz_injective
#print axioms yz_injective
end ThinMatrix.CWWordCollisions
