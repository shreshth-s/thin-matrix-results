import BinaryRetainedEqualCopy

set_option autoImplicit false
set_option maxRecDepth 3000

namespace ThinMatrix.BinaryRetainedBounds
open scoped BigOperators
open PolynomialDegeneration FiniteDirectSum
open RecursiveTable (Layout Table prod fin power read)
open RetainedEqualCopy (Base copies)
open BinaryCell BinaryRecursiveDot BinaryRetainedEqualCopy
variable {I J K : Type} {r t : ℕ}

def Bounded {A : Type} {a : Layout A} (x : Table a Cell) (B : ℕ) : Prop :=
  ∀ i,(view (read x i)).natAbs≤B

theorem tabulate_bits_le {A V : Type} [Fintype A] (a : Layout A) (f : A → Run V) (N : ℕ)
    (hf : ∀ i,(f i).bitSteps≤N) : (tabulate a f).bitSteps≤a.size*N := by
  rw [tabulate_bits,RecursiveTable.size_eq_card a]
  simpa using Finset.sum_le_sum (fun i (_ : i∈(Finset.univ : Finset A)) => hf i)

theorem padded_bits {A : Type} [Fintype A] (a : Layout A) (g : ℕ)
    (x : Table (prod (fin r) a) Cell) : (padded (t:=t) a g x).bitSteps=0 := by
  rw [padded,tabulate_bits]
  apply Finset.sum_eq_zero;intro i _;split_ifs <;> rfl

theorem padded_bound {A : Type} (a : Layout A) (g B : ℕ)
    (x : Table (prod (fin r) a) Cell) (hx : Bounded x B) :
    Bounded (padded (t:=t) a g x).value B := by
  intro i
  simp only [padded,tabulate_read]
  split_ifs
  · exact hx _
  · simp

theorem forms_bounds {A : Type} [Fintype A] (a : Layout I) (tail : Layout A)
    (coeff : Table (prod (fin r) (prod (fin t) a)) Cell)
    (x : Fin t×(I×A) → Cell) (H B W : ℕ)
    (hH : H.size≤W) (hB : B.size≤W) (hP : (t*a.size*H*B).size≤W)
    (hc : Bounded coeff H) (hx : ∀ i,(view (x i)).natAbs≤B) :
    Bounded (forms a tail coeff x).value (t*a.size*H*B) ∧
    (forms a tail coeff x).bitSteps≤2*r*t*a.size*tail.size*BackendScalarBits.backendScalarUnit W := by
  have hd (sp : Fin r×A) := dot_bounds (prod (fin t) a)
    (fun i => read coeff (sp.1,i)) (fun i => x (i.1,(i.2,sp.2))) H B W hH hB hP
      (fun i => hc _) (fun i => hx _)
  refine ⟨fun sp => ?_,?_⟩
  · simpa only [forms,tabulate_read,prod,fin] using (hd sp).1
  · have h := tabulate_bits_le (prod (fin r) tail)
      (fun sp => dot (prod (fin t) a) (fun i => read coeff (sp.1,i)) (fun i => x (i.1,(i.2,sp.2))))
      (2*(t*a.size)*BackendScalarBits.backendScalarUnit W) (fun sp => (hd sp).2)
    simpa only [forms,prod,fin,Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using h

/-- A uniform magnitude cap for all retained partial sums in a subtree.
The extra factor F in the bit cap also covers the fixed coefficients. -/
def cap (F B k : ℕ) := F^(4*k)*B^2
def bitCap (F B k : ℕ) := F^(4*k+1)*B^2

theorem cap_step (F B k : ℕ) : F*cap F (F*B) k≤cap F B (k+1) := by
  by_cases hf : F=0
  · simp [hf,cap]
  · have hF : 1≤F := Nat.one_le_iff_ne_zero.mpr hf
    have hh := Nat.le_mul_of_pos_right (F*cap F (F*B) k) hF
    convert hh using 1
    simp only [cap,pow_mul,mul_pow,pow_add,pow_one]
    ring

theorem bitCap_child (F B k : ℕ) (hF : 1≤F) : bitCap F (F*B) k≤bitCap F B (k+1) := by
  have hh := Nat.le_mul_of_pos_right (bitCap F (F*B) k) (one_le_pow₀ hF : 1≤F^2)
  convert hh using 1
  simp only [bitCap,pow_add,mul_pow,pow_one,pow_mul]
  ring

theorem local_caps (F B k : ℕ) (hF : 1≤F) (hB : 1≤B) :
    F≤bitCap F B (k+1) ∧ B≤bitCap F B (k+1) ∧
    F*B≤bitCap F B (k+1) ∧ cap F B (k+1)≤bitCap F B (k+1) := by
  have hp : 1≤F^(4*(k+1)) := one_le_pow₀ hF
  have hb : B≤B^2 := by nlinarith
  have hh : 1≤B^2 := one_le_pow₀ hB
  simp only [bitCap,pow_succ,cap]
  constructor
  · nlinarith [Nat.mul_le_mul_right F hp,Nat.mul_le_mul_left (F^(4*(k+1))*F) hh]
  constructor
  · exact hb.trans (Nat.le_mul_of_pos_left (B^2) (lt_of_lt_of_le Nat.zero_lt_one (Nat.mul_le_mul hp hF)))
  constructor
  · calc
      F*B≤F*B^2 := Nat.mul_le_mul_left F hb
      _ ≤ _ := by nlinarith [Nat.mul_le_mul_right (F*B^2) hp]
  · exact Nat.mul_le_mul_right (B^2) (Nat.le_mul_of_pos_right _ hF)

set_option backward.isDefEq.respectTransparency false in
theorem run_bounds [Fintype I] [Fintype J] [Fintype K]
    (a : Layout I) (b : Layout J) (c : Layout K) (ht : 0<t)
    (d : Base r t a b c Cell) (F H : ℕ) (hF : 1≤F) (hH : H≤F)
    (hL : t*a.size*H≤F) (hR : t*b.size*H≤F) (hO : r*H≤F)
    (hdL : Bounded d.left H) (hdR : Bounded d.middle H) (hdO : Bounded d.right H)
    (k B W : ℕ) (hB : 1≤B) (hW : (bitCap F B k).size≤W)
    (x : Table (copies t a k) Cell) (y : Table (copies t b k) Cell)
    (hx : Bounded x B) (hy : Bounded y B) :
    Bounded (run a b c ht d k x y).value (cap F B k) ∧
    (run a b c ht d k x y).bitSteps≤
      RetainedEqualCopyCosts.arithmetic r t a.size b.size c.size k*BackendScalarBits.backendScalarUnit W := by
  induction k generalizing B W with
  | zero =>
    have hbw : B.size≤W := (Nat.size_le_size (show B≤bitCap F B 0 by
      simp only [bitCap,pow_one,zero_add,mul_zero]
      nlinarith [Nat.le_mul_of_pos_left (B^2) hF])).trans hW
    constructor
    · intro z
      simpa only [run,tabulate_read,mul_view,Int.natAbs_mul,cap,mul_zero,pow_zero,one_mul,pow_two]
        using Nat.mul_le_mul (hx (z.1,PUnit.unit)) (hy (z.1,PUnit.unit))
    · have hh := tabulate_bits_le (copies t c 0) (fun z =>
          let p := mul (read x (z.1,PUnit.unit)) (read y (z.1,PUnit.unit)); (⟨p.value,p.bitSteps,8⟩ : Run Cell))
          (BackendScalarBits.backendScalarUnit W) (fun z => mul_price W _ _
            ((Nat.size_le_size (hx _)).trans hbw) ((Nat.size_le_size (hy _)).trans hbw))
      simpa only [run,copies,prod,fin,RecursiveTable.power_size,pow_zero,mul_one,
        RetainedEqualCopyCosts.arithmetic] using hh
  | succ k ih =>
    let lx := forms a (power a k) d.left (read x)
    let ry := forms b (power b k) d.middle (read y)
    have caps := local_caps F B k hF hB
    have toWidth (N : ℕ) (h : N≤bitCap F B (k+1)) : N.size≤W := (Nat.size_le_size h).trans hW
    have hl := forms_bounds a (power a k) d.left (read x) H B W
      (toWidth H (hH.trans caps.1)) (toWidth B caps.2.1)
      (toWidth _ ((Nat.mul_le_mul_right B hL).trans caps.2.2.1)) hdL hx
    have hr := forms_bounds b (power b k) d.middle (read y) H B W
      (toWidth H (hH.trans caps.1)) (toWidth B caps.2.1)
      (toWidth _ ((Nat.mul_le_mul_right B hR).trans caps.2.2.1)) hdR hy
    have hxl : Bounded lx.value (F*B) := fun i => (hl.1 i).trans (Nat.mul_le_mul_right B hL)
    have hyr : Bounded ry.value (F*B) := fun i => (hr.1 i).trans (Nat.mul_le_mul_right B hR)
    let child (g : Fin ((r+t-1)/t)) := run a b c ht d k
      (padded (t:=t) (power a k) g.val lx.value).value
      (padded (t:=t) (power b k) g.val ry.value).value
    have hc (g : Fin ((r+t-1)/t)) := ih (F*B) W (by nlinarith)
      (toWidth _ (bitCap_child F B k hF)) _ _
      (padded_bound (power a k) g.val (F*B) lx.value hxl)
      (padded_bound (power b k) g.val (F*B) ry.value hyr)
    have outcap : r*H*cap F (F*B) k≤cap F B (k+1) :=
      (Nat.mul_le_mul_right _ hO).trans (cap_step F B k)
    have hcw : (cap F (F*B) k).size≤W := toWidth _
      ((Nat.le_mul_of_pos_left _ hF).trans ((cap_step F B k).trans caps.2.2.2))
    have hout (z : Fin t×PowerIndex K (k+1)) := dot_bounds (fin r)
      (fun s => read d.right (s,(z.1,z.2.1)))
      (fun s => read (child (slot r t ht s).1).value ((slot r t ht s).2,z.2.2))
      H (cap F (F*B) k) W (toWidth H (hH.trans caps.1)) hcw
      (toWidth _ (outcap.trans caps.2.2.2)) (fun s => hdO _) (fun s => (hc _).1 _)
    constructor
    · intro z
      simp only [run,tabulate_read]
      exact (hout z).1.trans outcap
    · have hchildren := tabulate_bits_le (fin ((r+t-1)/t)) (fun g =>
          let px := padded (t:=t) (power a k) g.val lx.value
          let py := padded (t:=t) (power b k) g.val ry.value
          let v := child g
          (⟨v.value,px.bitSteps+py.bitSteps+v.bitSteps,px.control+py.control+v.control+8⟩ : Run _))
          (RetainedEqualCopyCosts.arithmetic r t a.size b.size c.size k*BackendScalarBits.backendScalarUnit W)
          (fun g => by simpa only [padded_bits,zero_add] using (hc g).2)
      have houtput := tabulate_bits_le (copies t c (k+1)) (fun z =>
          dot (fin r) (fun s => read d.right (s,(z.1,z.2.1)))
            (fun s => read (child (slot r t ht s).1).value ((slot r t ht s).2,z.2.2)))
          (2*r*BackendScalarBits.backendScalarUnit W) (fun z => (hout z).2)
      have hh := Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hl.2 hr.2) hchildren) houtput
      dsimp only [lx,ry,child] at hh
      simp only [run,tabulate_read]
      apply hh.trans
      simp only [copies,prod,fin,RecursiveTable.power_size,RetainedEqualCopyCosts.arithmetic,pow_succ']
      exact le_of_eq (by ring)

#print axioms tabulate_bits_le
#print axioms padded_bits
#print axioms padded_bound
#print axioms forms_bounds
#print axioms cap_step
#print axioms bitCap_child
#print axioms local_caps
#print axioms run_bounds

theorem size_power (a k : ℕ) : (a^k).size≤k*a.size+1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ]
    exact (BinaryMultiplierAdapter.size_mul _ _).trans (by nlinarith)

theorem bitCap_size (F B k : ℕ) : (bitCap F B k).size≤(4*k+1)*F.size+2*B.size+2 := by
  have hh := BinaryMultiplierAdapter.size_mul (F^(4*k+1)) (B^2)
  have hf := size_power F (4*k+1)
  have hb := size_power B 2
  unfold bitCap
  omega

/-- The bit budget is derived from the original input magnitude and fixed
base data. No intermediate width is an input premise. -/
theorem run_linear_bits [Fintype I] [Fintype J] [Fintype K]
    (a : Layout I) (b : Layout J) (c : Layout K) (ht : 0<t)
    (d : Base r t a b c Cell) (F H : ℕ) (hF : 1≤F) (hH : H≤F)
    (hL : t*a.size*H≤F) (hR : t*b.size*H≤F) (hO : r*H≤F)
    (hdL : Bounded d.left H) (hdR : Bounded d.middle H) (hdO : Bounded d.right H)
    (k B : ℕ) (hB : 1≤B)
    (x : Table (copies t a k) Cell) (y : Table (copies t b k) Cell)
    (hx : Bounded x B) (hy : Bounded y B) :
    (run a b c ht d k x y).bitSteps≤
      RetainedEqualCopyCosts.arithmetic r t a.size b.size c.size k*
        BackendScalarBits.backendScalarUnit ((4*k+1)*F.size+2*B.size+2) :=
  (run_bounds a b c ht d F H hF hH hL hR hO hdL hdR hdO k B _ hB
    (bitCap_size F B k) x y hx hy).2

#print axioms size_power
#print axioms bitCap_size
#print axioms run_linear_bits
end ThinMatrix.BinaryRetainedBounds
