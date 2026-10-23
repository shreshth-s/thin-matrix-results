import CWSixBlocks

set_option autoImplicit false

namespace ThinMatrix.CWBlockWords
open scoped BigOperators
open FiniteTrilinear PolynomialDegeneration CWPolynomialCertificate CWSixBlocks
abbrev Word (n : ℕ) := PowerIndex Block n
abbrev Colors (n : ℕ) := PowerIndex (Fin 3) n

instance (n : ℕ) : DecidableEq (Word n) := by
  induction n with
  | zero => exact inferInstanceAs (DecidableEq PUnit)
  | succ n ih => exact inferInstanceAs (DecidableEq (Block×Word n))
instance (n : ℕ) : DecidableEq (Colors n) := by
  induction n with
  | zero => exact inferInstanceAs (DecidableEq PUnit)
  | succ n ih => exact inferInstanceAs (DecidableEq (Fin 3×Colors n))

def mapWord {A B : Type*} (f : A → B) : (n : ℕ) → PowerIndex A n → PowerIndex B n
  | 0 => fun _ => PUnit.unit
  | n+1 => fun w => (f w.1,mapWord f n w.2)
def wx (n : ℕ) := mapWord cx n
def wy (n : ℕ) := mapWord cy n
def wz (n : ℕ) := mapWord cz n
def colors {q : ℕ} (n : ℕ) := mapWord (@color q) n

abbrev Rows (q : ℕ) : (n : ℕ) → Word n → Type
  | 0 => fun _ => PUnit
  | n+1 => fun w => Row q w.1×Rows q n w.2
abbrev Inners (q : ℕ) : (n : ℕ) → Word n → Type
  | 0 => fun _ => PUnit
  | n+1 => fun w => Inner q w.1×Inners q n w.2
abbrev Cols (q : ℕ) : (n : ℕ) → Word n → Type
  | 0 => fun _ => PUnit
  | n+1 => fun w => Col q w.1×Cols q n w.2
instance (q n : ℕ) (w : Word n) : Fintype (Rows q n w) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype PUnit)
  | succ n ih => letI := ih w.2;exact inferInstanceAs (Fintype (Row q w.1×Rows q n w.2))
instance (q n : ℕ) (w : Word n) : Fintype (Inners q n w) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype PUnit)
  | succ n ih => letI := ih w.2;exact inferInstanceAs (Fintype (Inner q w.1×Inners q n w.2))
instance (q n : ℕ) (w : Word n) : Fintype (Cols q n w) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype PUnit)
  | succ n ih => letI := ih w.2;exact inferInstanceAs (Fintype (Col q w.1×Cols q n w.2))
instance (q n : ℕ) (w : Word n) : DecidableEq (Rows q n w) := by
  induction n with
  | zero => exact inferInstanceAs (DecidableEq PUnit)
  | succ n ih => letI := ih w.2;exact inferInstanceAs (DecidableEq (Row q w.1×Rows q n w.2))
instance (q n : ℕ) (w : Word n) : DecidableEq (Inners q n w) := by
  induction n with
  | zero => exact inferInstanceAs (DecidableEq PUnit)
  | succ n ih => letI := ih w.2;exact inferInstanceAs (DecidableEq (Inner q w.1×Inners q n w.2))
instance (q n : ℕ) (w : Word n) : DecidableEq (Cols q n w) := by
  induction n with
  | zero => exact inferInstanceAs (DecidableEq PUnit)
  | succ n ih => letI := ih w.2;exact inferInstanceAs (DecidableEq (Col q w.1×Cols q n w.2))

def leftWord (q : ℕ) : (n : ℕ) → (w : Word n) → Rows q n w×Inners q n w → PowerIndex (Axis q) n
  | 0 => fun _ _ => PUnit.unit
  | n+1 => fun w x => (left q w.1 (x.1.1,x.2.1),leftWord q n w.2 (x.1.2,x.2.2))
def middleWord (q : ℕ) : (n : ℕ) → (w : Word n) → Inners q n w×Cols q n w → PowerIndex (Axis q) n
  | 0 => fun _ _ => PUnit.unit
  | n+1 => fun w x => (middle q w.1 (x.1.1,x.2.1),middleWord q n w.2 (x.1.2,x.2.2))
def rightWord (q : ℕ) : (n : ℕ) → (w : Word n) → Cols q n w×Rows q n w → PowerIndex (Axis q) n
  | 0 => fun _ _ => PUnit.unit
  | n+1 => fun w x => (right q w.1 (x.1.1,x.2.1),rightWord q n w.2 (x.1.2,x.2.2))

theorem word_identity {R : Type*} [CommRing R] (q n : ℕ) (w : Word n)
    (x : Rows q n w×Inners q n w) (y : Inners q n w×Cols q n w) (z : Cols q n w×Rows q n w) :
    tensorPower (target (R:=R) q) n (leftWord q n w x) (middleWord q n w y) (rightWord q n w z)=
      FiniteMatrixTensor.coeff (Rows q n w) (Inners q n w) (Cols q n w) R x y z := by
  induction n with
  | zero => simp [tensorPower,FiniteMatrixTensor.coeff,Rows,Inners,Cols]
  | succ n ih =>
      simp only [leftWord,middleWord,rightWord,tensorPower,FiniteTrilinear.product,CWSixBlocks.identity,ih]
      exact FiniteMatrixTensor.product_coeff x y z

theorem word_colors (q n : ℕ) (w : Word n)
    (x : Rows q n w×Inners q n w) (y : Inners q n w×Cols q n w) (z : Cols q n w×Rows q n w) :
    colors n (leftWord q n w x)=wx n w ∧ colors n (middleWord q n w y)=wy n w ∧
      colors n (rightWord q n w z)=wz n w := by
  induction n with
  | zero => exact ⟨rfl,rfl,rfl⟩
  | succ n ih =>
      have h := CWSixBlocks.colors q w.1 (x.1.1,x.2.1) (y.1.1,y.2.1) (z.1.1,z.2.1)
      have ht := ih w.2 (x.1.2,x.2.2) (y.1.2,y.2.2) (z.1.2,z.2.2)
      exact ⟨Prod.ext h.1 ht.1,Prod.ext h.2.1 ht.2.1,Prod.ext h.2.2 ht.2.2⟩

def Compatible : (n : ℕ) → Colors n → Colors n → Colors n → Prop
  | 0 => fun _ _ _ => True
  | n+1 => fun x y z => x.1.val+y.1.val+z.1.val=2 ∧ Compatible n x.2 y.2 z.2
instance (n : ℕ) (x y z : Colors n) : Decidable (Compatible n x y z) := by
  induction n with
  | zero => exact inferInstanceAs (Decidable True)
  | succ n ih => letI := ih x.2 y.2 z.2;exact inferInstanceAs (Decidable (_ ∧ _))

def decodeWord : (n : ℕ) → Colors n → Colors n → Colors n → Word n
  | 0 => fun _ _ _ => PUnit.unit
  | n+1 => fun x y z => (decode x.1 y.1 z.1,decodeWord n x.2 y.2 z.2)

theorem decodeWord_colors (n : ℕ) (x y z : Colors n) (h : Compatible n x y z) :
    wx n (decodeWord n x y z)=x ∧ wy n (decodeWord n x y z)=y ∧ wz n (decodeWord n x y z)=z := by
  induction n with
  | zero => cases x;cases y;cases z;exact ⟨rfl,rfl,rfl⟩
  | succ n ih =>
      have hh := decode_colors x.1 y.1 z.1 h.1
      have ht := ih x.2 y.2 z.2 h.2
      exact ⟨Prod.ext hh.1 ht.1,Prod.ext hh.2.1 ht.2.1,Prod.ext hh.2.2 ht.2.2⟩

theorem word_compatible (n : ℕ) (w : Word n) : Compatible n (wx n w) (wy n w) (wz n w) := by
  induction n with
  | zero => trivial
  | succ n ih => exact ⟨color_sum w.1,ih w.2⟩

theorem tensor_zero_of_incompatible {R : Type*} [CommRing R] (q n : ℕ)
    (x y z : PowerIndex (Axis q) n) (h : ¬ Compatible n (colors n x) (colors n y) (colors n z)) :
    tensorPower (target (R:=R) q) n x y z=0 := by
  induction n with
  | zero => exact (h trivial).elim
  | succ n ih =>
      by_cases hh : (color x.1).val+(color y.1).val+(color z.1).val=2
      · have ht : ¬ Compatible n (colors n x.2) (colors n y.2) (colors n z.2) := fun ht => h ⟨hh,ht⟩
        change target q x.1 y.1 z.1*tensorPower (target q) n x.2 y.2 z.2=0
        rw [ih x.2 y.2 z.2 ht,mul_zero]
      · change target q x.1 y.1 z.1*tensorPower (target q) n x.2 y.2 z.2=0
        rw [zero_outside q x.1 y.1 z.1 hh,zero_mul]

theorem leftWord_color (q n : ℕ) (w : Word n) (x : Rows q n w×Inners q n w) :
    colors n (leftWord q n w x)=wx n w := by
  induction n with
  | zero => rfl
  | succ n ih =>
      apply Prod.ext
      · obtain ⟨b,w⟩ := w;cases b <;> rfl
      · exact ih w.2 (x.1.2,x.2.2)

theorem leftWord_injective (q n : ℕ) (w : Word n) : Function.Injective (leftWord q n w) := by
  induction n with
  | zero => intro x y _;exact Subsingleton.elim x y
  | succ n ih =>
      intro x y h
      have hh := CWSixBlocks.left_injective q w.1 (congrArg Prod.fst h)
      have ht := ih w.2 (congrArg Prod.snd h)
      have hh1 := congrArg Prod.fst hh
      have hh2 := congrArg Prod.snd hh
      have ht1 := congrArg Prod.fst ht
      have ht2 := congrArg Prod.snd ht
      apply Prod.ext
      · change (x.1.1,x.1.2)=(y.1.1,y.1.2)
        exact Prod.ext hh1 ht1
      · change (x.2.1,x.2.2)=(y.2.1,y.2.2)
        exact Prod.ext hh2 ht2

#print axioms leftWord_color
#print axioms leftWord_injective
theorem middleWord_color (q n : ℕ) (w : Word n) (x : Inners q n w×Cols q n w) :
    colors n (middleWord q n w x)=wy n w := by
  induction n with
  | zero => rfl
  | succ n ih =>
      apply Prod.ext
      · obtain ⟨b,w⟩ := w;cases b <;> rfl
      · exact ih w.2 (x.1.2,x.2.2)

theorem middleWord_injective (q n : ℕ) (w : Word n) : Function.Injective (middleWord q n w) := by
  induction n with
  | zero => intro x y _;exact Subsingleton.elim x y
  | succ n ih =>
      intro x y h
      have hh := CWSixBlocks.middle_injective q w.1 (congrArg Prod.fst h)
      have ht := ih w.2 (congrArg Prod.snd h)
      have hh1 := congrArg Prod.fst hh
      have hh2 := congrArg Prod.snd hh
      have ht1 := congrArg Prod.fst ht
      have ht2 := congrArg Prod.snd ht
      apply Prod.ext
      · change (x.1.1,x.1.2)=(y.1.1,y.1.2)
        exact Prod.ext hh1 ht1
      · change (x.2.1,x.2.2)=(y.2.1,y.2.2)
        exact Prod.ext hh2 ht2

#print axioms middleWord_color
#print axioms middleWord_injective
theorem rightWord_color (q n : ℕ) (w : Word n) (x : Cols q n w×Rows q n w) :
    colors n (rightWord q n w x)=wz n w := by
  induction n with
  | zero => rfl
  | succ n ih =>
      apply Prod.ext
      · obtain ⟨b,w⟩ := w;cases b <;> rfl
      · exact ih w.2 (x.1.2,x.2.2)

theorem rightWord_injective (q n : ℕ) (w : Word n) : Function.Injective (rightWord q n w) := by
  induction n with
  | zero => intro x y _;exact Subsingleton.elim x y
  | succ n ih =>
      intro x y h
      have hh := CWSixBlocks.right_injective q w.1 (congrArg Prod.fst h)
      have ht := ih w.2 (congrArg Prod.snd h)
      have hh1 := congrArg Prod.fst hh
      have hh2 := congrArg Prod.snd hh
      have ht1 := congrArg Prod.fst ht
      have ht2 := congrArg Prod.snd ht
      apply Prod.ext
      · change (x.1.1,x.1.2)=(y.1.1,y.1.2)
        exact Prod.ext hh1 ht1
      · change (x.2.1,x.2.2)=(y.2.1,y.2.2)
        exact Prod.ext hh2 ht2

#print axioms rightWord_color
#print axioms rightWord_injective
theorem cyclic_word_identity {R : Type*} [CommRing R] (q n : ℕ) (w : Word n)
    (x : Rows q n w×Inners q n w) (y : Inners q n w×Cols q n w) (z : Cols q n w×Rows q n w) :
    tensorPower (target (R:=R) q) n (leftWord q n w x) (middleWord q n w y) (rightWord q n w z)=
      FiniteMatrixTensor.coeff (Cols q n w) (Rows q n w) (Inners q n w) R z x y := by
  rw [word_identity]
  exact FiniteMatrixTensor.cyclic x y z

#print axioms cyclic_word_identity
#print axioms word_identity
#print axioms word_colors
#print axioms decodeWord_colors
#print axioms word_compatible
#print axioms tensor_zero_of_incompatible
end ThinMatrix.CWBlockWords
