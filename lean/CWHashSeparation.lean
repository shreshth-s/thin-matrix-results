import CWBlockWords

set_option autoImplicit false

/-! The arithmetic part of level-one Salem-Spencer hashing. No random-hash
survival estimate or large progression-free set is assumed to have been built. -/
namespace ThinMatrix.CWHashSeparation
open PolynomialDegeneration CWBlockWords
variable {R : Type*} [CommRing R]

def weighted : (n : ℕ) → PowerIndex R n → Colors n → R
  | 0 => fun _ _ => 0
  | n+1 => fun weights a => weights.1*(a.1.val:R)+weighted n weights.2 a.2
def weightSum : (n : ℕ) → PowerIndex R n → R
  | 0 => fun _ => 0
  | n+1 => fun weights => weights.1+weightSum n weights.2

theorem weighted_compatible (n : ℕ) (weights : PowerIndex R n) (x y z : Colors n)
    (h : Compatible n x y z) : weighted n weights x+weighted n weights y+weighted n weights z=2*weightSum n weights := by
  induction n with
  | zero => simp [weighted,weightSum]
  | succ n ih =>
      have ht := ih weights.2 x.2 y.2 z.2 h.2
      have hh : (x.1.val:R)+(y.1.val:R)+(z.1.val:R)=2 := by
        simpa only [Nat.cast_add,Nat.cast_ofNat] using congrArg (fun a : ℕ => (a:R)) h.1
      simp only [weighted,weightSum]
      calc
        _ = weights.1*((x.1.val:R)+(y.1.val:R)+(z.1.val:R))+
          (weighted n weights.2 x.2+weighted n weights.2 y.2+weighted n weights.2 z.2) := by ring
        _ = _ := by rw [hh,ht];ring

section Field
variable {F : Type*} [Field F]
def hx (n : ℕ) (b : F) (weights : PowerIndex F n) (x : Colors n) : F := b+weighted n weights x
def hy (n : ℕ) (b w0 : F) (weights : PowerIndex F n) (y : Colors n) : F := b+w0+weighted n weights y
def hz (n : ℕ) (b w0 : F) (weights : PowerIndex F n) (z : Colors n) : F :=
  b+(w0+2*weightSum n weights-weighted n weights z)/2

theorem hash_relation (h2 : (2:F)≠0) (n : ℕ) (b w0 : F) (weights : PowerIndex F n)
    (x y z : Colors n) (h : Compatible n x y z) :
    hx n b weights x+hy n b w0 weights y=hz n b w0 weights z+hz n b w0 weights z := by
  have ht := weighted_compatible n weights x y z h
  unfold hx hy hz
  rw [← ht]
  field_simp [h2]
  ring

theorem same_bucket (h2 : (2:F)≠0) (n : ℕ) (b w0 : F) (weights : PowerIndex F n)
    (B : Set F) (hB : ThreeAPFree B) (x y z : Colors n) (h : Compatible n x y z)
    (hxB : hx n b weights x ∈ B) (hyB : hy n b w0 weights y ∈ B) (hzB : hz n b w0 weights z ∈ B) :
    hx n b weights x=hz n b w0 weights z ∧ hy n b w0 weights y=hz n b w0 weights z := by
  have he := hash_relation h2 n b w0 weights x y z h
  have hleft := hB hxB hzB hyB he
  exact ⟨hleft,hB hyB hzB hxB (by simpa only [add_comm] using he)⟩
end Field

#print axioms weighted_compatible
#print axioms hash_relation
#print axioms same_bucket
end ThinMatrix.CWHashSeparation
