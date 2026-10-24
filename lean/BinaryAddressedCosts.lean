import BinaryAddressedRecursion

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

/-! Binary address cost for the retained matrix recurrence. Width hypotheses
refer to explicit finite table dimensions, never to scalar input values. -/
namespace ThinMatrix.BinaryAddressedCosts
open scoped BigOperators
open BinaryCell BinaryGroupedCoordinates
open PolynomialDegeneration RetainedEqualCopy FiniteDirectSum
open RecursiveTable (Table prod fin power)
open BinaryAddressedRecursion
variable {a b c r t : ℕ}

structure Fits (a b r t K W : ℕ) : Prop where
  first : a.size≤W
  second : b.size≤W
  pair : (a*b).size≤W
  rank : r.size≤W
  copies : t.size≤W
  coefficient : (t*(a*b)).size≤W
  group : ((r+t-1)/t).size≤W
  paddedIndex : (((r+t-1)/t)*t).size≤W
  words : ∀ k≤K,((a*b)^k).size≤W
  rankCells : ∀ k≤K,(r*(a*b)^k).size≤W
  copyCells : ∀ k≤K,(t*(a*b)^k).size≤W

def unit (K W : ℕ) := 131072*(K+1)^2*(W+1)^2

theorem unit_pos (K W : ℕ) : 0<unit K W := by unfold unit;positivity

theorem read_unit (ha : 0<a) (hb : 0<b) (K W k : ℕ) (h : Fits a b r t K W) (hk : k≤K)
    (x : Cells t a b k) (i : Fin t×PowerIndex (Fin a×Fin b) k) :
    (BinaryRecursiveTable.read k x i).bitSteps≤unit K W := by
  have hh := BinaryRecursiveTable.read_bits k W ha hb h.pair (h.words k hk) h.copies x i
  have he := Nat.pow_le_pow_left (Nat.add_le_add_right hk 1) 2
  unfold unit
  nlinarith [Nat.mul_le_mul_right ((W+1)^2) he]

theorem rank_read_unit (ha : 0<a) (hb : 0<b) (K W k : ℕ) (h : Fits a b r t K W) (hk : k≤K)
    (x : Cells r a b k) (i : Fin r×PowerIndex (Fin a×Fin b) k) :
    (BinaryRecursiveTable.read k x i).bitSteps≤unit K W := by
  have hh := BinaryRecursiveTable.read_bits k W ha hb h.pair (h.words k hk) h.rank x i
  have he := Nat.pow_le_pow_left (Nat.add_le_add_right hk 1) 2
  unfold unit
  nlinarith [Nat.mul_le_mul_right ((W+1)^2) he]

theorem coefficient_unit (K W : ℕ) (h : Fits a b r t K W)
    (coeff : Table (prod (fin r) (prod (fin t) (prod (fin a) (fin b)))) Cell)
    (s : Fin r) (copy : Fin t) (i : Fin a×Fin b) :
    (BinaryAddressedDot.coefficient coeff s copy i).bitSteps≤unit K W := by
  have hh := BinaryAddressedDot.coefficient_bits coeff s copy i W
    h.first h.second h.pair h.copies h.rank h.coefficient
  have he : 1≤(K+1)^2 := one_le_pow₀ (by omega)
  unfold unit
  nlinarith [Nat.mul_le_mul_right ((W+1)^2) he]

theorem tabulate_unit (ha : 0<a) (hb : 0<b) (K W k : ℕ) (h : Fits a b r t K W) (hk : k≤K)
    (f : Fin t×PowerIndex (Fin a×Fin b) k → Run Cell) :
    (BinaryRecursiveTable.tabulate ha hb k f).bitSteps≤
      (∑ i,(f i).bitSteps)+t*(a*b)^k*unit K W := by
  have hh := BinaryRecursiveTable.tabulate_bits ha hb k W h.pair (h.words k hk) (h.copyCells k hk) f
  rw [BinaryRecursiveDot.tabulate_bits] at hh
  have he := Nat.pow_le_pow_left (Nat.add_le_add_right hk 1) 2
  have hu : 32768*(k+1)^2*(W+1)^2≤unit K W := by
    unfold unit
    nlinarith [Nat.mul_le_mul_right ((W+1)^2) he]
  exact hh.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ hu) _)

theorem rank_tabulate_unit (ha : 0<a) (hb : 0<b) (K W k : ℕ) (h : Fits a b r t K W) (hk : k≤K)
    (f : Fin r×PowerIndex (Fin a×Fin b) k → Run Cell) :
    (BinaryRecursiveTable.tabulate ha hb k f).bitSteps≤
      (∑ i,(f i).bitSteps)+r*(a*b)^k*unit K W := by
  have hh := BinaryRecursiveTable.tabulate_bits ha hb k W h.pair (h.words k hk) (h.rankCells k hk) f
  rw [BinaryRecursiveDot.tabulate_bits] at hh
  have he := Nat.pow_le_pow_left (Nat.add_le_add_right hk 1) 2
  have hu : 32768*(k+1)^2*(W+1)^2≤unit K W := by
    unfold unit
    nlinarith [Nat.mul_le_mul_right ((W+1)^2) he]
  exact hh.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ hu) _)

theorem forms_bits (ha : 0<a) (hb : 0<b) (K W k : ℕ) (h : Fits a b r t K W) (hk : k+1≤K)
    (coeff : Table (prod (fin r) (prod (fin t) (prod (fin a) (fin b)))) Cell)
    (x : Cells t a b (k+1)) :
    (forms ha hb k coeff x).bitSteps≤
      (BinaryRetainedEqualCopy.forms (prod (fin a) (fin b)) (power (prod (fin a) (fin b)) k)
        coeff (RecursiveTable.read x)).bitSteps+
        r*(a*b)^k*(2*t*(a*b)+1)*unit K W := by
  let f := fun (sp : Fin r×PowerIndex (Fin a×Fin b) k) =>
    BinaryAddressedDot.dot (prod (fin t) (prod (fin a) (fin b)))
      (fun i => BinaryAddressedDot.coefficient coeff sp.1 i.1 i.2)
      (fun i => BinaryRecursiveTable.read (k+1) x (i.1,(i.2,sp.2)))
  let old := fun (sp : Fin r×PowerIndex (Fin a×Fin b) k) =>
    BinaryRecursiveDot.dot (prod (fin t) (prod (fin a) (fin b)))
      (fun i => RecursiveTable.read coeff (sp.1,i)) (fun i => RecursiveTable.read x (i.1,(i.2,sp.2)))
  have point (sp : Fin r×PowerIndex (Fin a×Fin b) k) :
      (f sp).bitSteps≤(old sp).bitSteps+2*t*(a*b)*unit K W := by
    dsimp only [f]
    rw [BinaryAddressedDot.dot_bits]
    simp only [BinaryAddressedDot.coefficient_value,BinaryRecursiveTable.read_value]
    have hh := Finset.sum_le_sum (fun (i : Fin t×(Fin a×Fin b)) (_ : i∈Finset.univ) =>
      Nat.add_le_add (coefficient_unit K W h coeff sp.1 i.1 i.2)
        (read_unit ha hb K W (k+1) h hk x (i.1,(i.2,sp.2))))
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_prod,Fintype.card_fin,smul_eq_mul] at hh
    change (old sp).bitSteps+_≤_
    nlinarith
  have hh := rank_tabulate_unit ha hb K W k h (by omega) f
  have hs := Finset.sum_le_sum (fun sp (_ : sp∈Finset.univ) => point sp)
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_prod,
    Fintype.card_fin,powerIndex_card,smul_eq_mul] at hs
  change (BinaryRecursiveTable.tabulate ha hb k f).bitSteps≤_
  change _≤(BinaryRecursiveDot.tabulate (prod (fin r) (power (prod (fin a) (fin b)) k)) old).bitSteps+_
  rw [BinaryRecursiveDot.tabulate_bits]
  nlinarith

theorem padded_bits (ha : 0<a) (hb : 0<b) (K W k : ℕ) (h : Fits a b r t K W) (hk : k≤K)
    (g : Fin ((r+t-1)/t)) (x : Cells r a b k) :
    (padded (t:=t) ha hb k g.val x).bitSteps≤4*t*(a*b)^k*unit K W := by
  let f := fun (i : Fin t×PowerIndex (Fin a×Fin b) k) =>
    let address := BinaryMatrixAddress.join t g.val i.1.val
    let active := BinaryChunkAddress.less address.value r
    if hh : active.value=true then
      let out := BinaryRecursiveTable.read k x (⟨address.value,(BinaryChunkAddress.less_true _ _).mp hh⟩,i.2)
      (⟨out.value,address.bitSteps+active.bitSteps+out.bitSteps,16⟩ : Run Cell)
    else ⟨zero,address.bitSteps+active.bitSteps,16⟩
  have point (i : Fin t×PowerIndex (Fin a×Fin b) k) : (f i).bitSteps≤3*unit K W := by
    have hj := BinaryMatrixAddress.join_bits t g.val i.1.val W h.copies
      ((Nat.size_le_size g.isLt.le).trans h.group) ((Nat.size_le_size i.1.isLt.le).trans h.copies)
    have hindex : (BinaryMatrixAddress.join t g.val i.1.val).value<((r+t-1)/t)*t := by
      rw [BinaryMatrixAddress.join_layout (g,i.1)]
      exact (finProdFinEquiv (g,i.1)).isLt
    have hl := BinaryChunkAddress.less_bits (BinaryMatrixAddress.join t g.val i.1.val).value r W
      ((Nat.size_le_size hindex.le).trans h.paddedIndex) h.rank
    have he : 1≤(K+1)^2 := one_le_pow₀ (by omega)
    have hsmall : 4096*(W+1)^2+64*(W+1)^2≤2*unit K W := by
      unfold unit
      nlinarith [Nat.mul_le_mul_right ((W+1)^2) he]
    dsimp only [f]
    split_ifs with hh
    · have hr := rank_read_unit ha hb K W k h hk x
        (⟨(BinaryMatrixAddress.join t g.val i.1.val).value,(BinaryChunkAddress.less_true _ _).mp hh⟩,i.2)
      dsimp only
      omega
    · dsimp only
      omega
  have hh := tabulate_unit ha hb K W k h hk f
  have hs := Finset.sum_le_sum (fun i (_ : i∈Finset.univ) => point i)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_prod,Fintype.card_fin,powerIndex_card,smul_eq_mul] at hs
  change (BinaryRecursiveTable.tabulate ha hb k f).bitSteps≤_
  nlinarith

theorem childRead_bits (ha : 0<a) (hb : 0<b) (ht : 0<t) (K W k : ℕ)
    (h : Fits a b r t K W) (hk : k≤K)
    (children : Table (fin ((r+t-1)/t)) (Cells t a b k))
    (s : Fin r) (word : PowerIndex (Fin a×Fin b) k) :
    (childRead ht k children s word).bitSteps≤2*unit K W := by
  have hs := BinaryMatrixAddress.split_bits t s.val W h.copies
    ((Nat.size_le_size s.isLt.le).trans h.rank)
  have hr := read_unit ha hb K W k h hk
    (children.get ⟨(BinaryMatrixAddress.split t s.val).value.1,by
      rw [BinaryMatrixAddress.split_value _ _ ht];exact (slot r t ht s).1.isLt⟩)
    (⟨(BinaryMatrixAddress.split t s.val).value.2,by
      rw [BinaryMatrixAddress.split_value _ _ ht];exact Nat.mod_lt _ ht⟩,word)
  have he : 1≤(K+1)^2 := one_le_pow₀ (by omega)
  have hsmall : 132*(W+1)^2+8≤unit K W := by
    unfold unit
    have hw : 1≤(W+1)^2 := one_le_pow₀ (by omega)
    nlinarith [Nat.mul_le_mul_right ((W+1)^2) he]
  simp only [childRead]
  omega

def output (ha : 0<a) (hb : 0<b) (ht : 0<t) (k : ℕ)
    (coeff : Table (prod (fin r) (prod (fin t) (prod (fin a) (fin b)))) Cell)
    (children : Table (fin ((r+t-1)/t)) (Cells t a b k)) : Run (Cells t a b (k+1)) :=
  BinaryRecursiveTable.tabulate ha hb (k+1) (fun z =>
    BinaryAddressedDot.dot (fin r) (fun s => BinaryAddressedDot.coefficient coeff s z.1 z.2.1)
      (fun s => childRead ht k children s z.2.2))

def oldOutput (ht : 0<t) (k : ℕ)
    (coeff : Table (prod (fin r) (prod (fin t) (prod (fin a) (fin b)))) Cell)
    (children : Table (fin ((r+t-1)/t)) (Cells t a b k)) : Run (Cells t a b (k+1)) :=
  BinaryRecursiveDot.tabulate (copies t (prod (fin a) (fin b)) (k+1)) (fun z =>
    BinaryRecursiveDot.dot (fin r) (fun s => RecursiveTable.read coeff (s,(z.1,z.2.1)))
      (fun s => RecursiveTable.read (RecursiveTable.read children (slot r t ht s).1) ((slot r t ht s).2,z.2.2)))

theorem output_bits (ha : 0<a) (hb : 0<b) (ht : 0<t) (K W k : ℕ) (h : Fits a b r t K W) (hk : k+1≤K)
    (coeff : Table (prod (fin r) (prod (fin t) (prod (fin a) (fin b)))) Cell)
    (children : Table (fin ((r+t-1)/t)) (Cells t a b k)) :
    (output ha hb ht k coeff children).bitSteps≤(oldOutput ht k coeff children).bitSteps+
      t*(a*b)^(k+1)*(3*r+1)*unit K W := by
  let f := fun (z : Fin t×PowerIndex (Fin a×Fin b) (k+1)) =>
    BinaryAddressedDot.dot (fin r) (fun s => BinaryAddressedDot.coefficient coeff s z.1 z.2.1)
      (fun s => childRead ht k children s z.2.2)
  let old := fun (z : Fin t×PowerIndex (Fin a×Fin b) (k+1)) =>
    BinaryRecursiveDot.dot (fin r) (fun s => RecursiveTable.read coeff (s,(z.1,z.2.1)))
      (fun s => RecursiveTable.read (RecursiveTable.read children (slot r t ht s).1) ((slot r t ht s).2,z.2.2))
  have point (z : Fin t×PowerIndex (Fin a×Fin b) (k+1)) :
      (f z).bitSteps≤(old z).bitSteps+3*r*unit K W := by
    dsimp only [f]
    rw [BinaryAddressedDot.dot_bits]
    simp only [BinaryAddressedDot.coefficient_value,childRead_value]
    have hs := Finset.sum_le_sum (fun (i : Fin r) (_ : i∈Finset.univ) =>
      Nat.add_le_add (coefficient_unit K W h coeff i z.1 z.2.1)
        (childRead_bits ha hb ht K W k h (by omega) children i z.2.2))
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] at hs
    change (old z).bitSteps+_≤_
    nlinarith
  have hh := tabulate_unit ha hb K W (k+1) h hk f
  have hs := Finset.sum_le_sum (fun z (_ : z∈Finset.univ) => point z)
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_prod,
    Fintype.card_fin,powerIndex_card,smul_eq_mul] at hs
  change (BinaryRecursiveTable.tabulate ha hb (k+1) f).bitSteps≤
    (BinaryRecursiveDot.tabulate (copies t (prod (fin a) (fin b)) (k+1)) old).bitSteps+_
  rw [BinaryRecursiveDot.tabulate_bits]
  nlinarith

/-- Every recursive arithmetic operation remains exactly the earlier one.
The added binary address work is dominated by the already-present complete
retained-control recurrence times a polynomial unit. -/
theorem run_bits (ha : 0<a) (hb : 0<b) (hc : 0<c) (ht : 0<t)
    (K W : ℕ) (hAB : Fits a b r t K W) (hBC : Fits b c r t K W) (hCA : Fits c a r t K W)
    (d : Base r t (prod (fin a) (fin b)) (prod (fin b) (fin c)) (prod (fin c) (fin a)) Cell)
    (k : ℕ) (hk : k≤K) (x : Cells t a b k) (y : Cells t b c k) :
    (run ha hb hc ht d k x y).bitSteps≤
      (BinaryRetainedEqualCopy.run (prod (fin a) (fin b)) (prod (fin b) (fin c))
        (prod (fin c) (fin a)) ht d k x y).bitSteps+
        RetainedEqualCopyCosts.control r t (a*b) (b*c) (c*a) k*unit K W := by
  induction k with
  | zero =>
    let f := fun (z : Fin t×PowerIndex (Fin c×Fin a) 0) =>
      let left := BinaryRecursiveTable.read 0 x (z.1,PUnit.unit)
      let right := BinaryRecursiveTable.read 0 y (z.1,PUnit.unit)
      let out := mul left.value right.value
      (⟨out.value,left.bitSteps+right.bitSteps+out.bitSteps,16⟩ : Run Cell)
    let old := fun (z : Fin t×PowerIndex (Fin c×Fin a) 0) =>
      let out := mul (RecursiveTable.read x (z.1,PUnit.unit)) (RecursiveTable.read y (z.1,PUnit.unit))
      (⟨out.value,out.bitSteps,8⟩ : Run Cell)
    have point (z : Fin t×PowerIndex (Fin c×Fin a) 0) : (f z).bitSteps≤(old z).bitSteps+2*unit K W := by
      have hx := read_unit ha hb K W 0 hAB hk x (z.1,PUnit.unit)
      have hy := read_unit hb hc K W 0 hBC hk y (z.1,PUnit.unit)
      simp only [f,old,BinaryRecursiveTable.read_value]
      omega
    have hh := tabulate_unit hc ha K W 0 hCA hk f
    have hs := Finset.sum_le_sum (fun z (_ : z∈Finset.univ) => point z)
    simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_prod,
      Fintype.card_fin,powerIndex_card,smul_eq_mul,pow_zero,mul_one] at hs hh
    change (BinaryRecursiveTable.tabulate hc ha 0 f).bitSteps≤
      (BinaryRecursiveDot.tabulate (copies t (prod (fin c) (fin a)) 0) old).bitSteps+_
    rw [BinaryRecursiveDot.tabulate_bits]
    simp only [RetainedEqualCopyCosts.control]
    nlinarith
  | succ k ih =>
    let left := forms ha hb k d.left x
    let right := forms hb hc k d.middle y
    let oldLeft := BinaryRetainedEqualCopy.forms (prod (fin a) (fin b)) (power (prod (fin a) (fin b)) k) d.left (RecursiveTable.read x)
    let oldRight := BinaryRetainedEqualCopy.forms (prod (fin b) (fin c)) (power (prod (fin b) (fin c)) k) d.middle (RecursiveTable.read y)
    have hlval : left.value=oldLeft.value := forms_value ha hb k d.left x
    have hrval : right.value=oldRight.value := forms_value hb hc k d.middle y
    let child := fun (g : Fin ((r+t-1)/t)) =>
      let px := padded (t:=t) ha hb k g.val left.value
      let py := padded (t:=t) hb hc k g.val right.value
      let out := run ha hb hc ht d k px.value py.value
      (⟨out.value,px.bitSteps+py.bitSteps+out.bitSteps,px.control+py.control+out.control+8⟩ : Run (Cells t c a k))
    let oldChild := fun (g : Fin ((r+t-1)/t)) =>
      let px := BinaryRetainedEqualCopy.padded (t:=t) (power (prod (fin a) (fin b)) k) g.val oldLeft.value
      let py := BinaryRetainedEqualCopy.padded (t:=t) (power (prod (fin b) (fin c)) k) g.val oldRight.value
      let out := BinaryRetainedEqualCopy.run (prod (fin a) (fin b)) (prod (fin b) (fin c)) (prod (fin c) (fin a)) ht d k px.value py.value
      (⟨out.value,px.bitSteps+py.bitSteps+out.bitSteps,px.control+py.control+out.control+8⟩ : Run (Cells t c a k))
    have childval (g) : (child g).value=(oldChild g).value := by
      simp only [child,oldChild,run_value,padded_value,hlval,hrval]
    have childbits (g) : (child g).bitSteps≤(oldChild g).bitSteps+
        (4*t*((a*b)^k+(b*c)^k)+RetainedEqualCopyCosts.control r t (a*b) (b*c) (c*a) k)*unit K W := by
      have hp := padded_bits ha hb K W k hAB (by omega) g left.value
      have hq := padded_bits hb hc K W k hBC (by omega) g right.value
      have hs := ih (by omega) (padded (t:=t) ha hb k g.val left.value).value (padded (t:=t) hb hc k g.val right.value).value
      rw [padded_value,padded_value,hlval,hrval] at hs
      dsimp only [child,oldChild]
      rw [BinaryRetainedBounds.padded_bits,BinaryRetainedBounds.padded_bits]
      simp only [padded_value,hlval,hrval] at hp hq ⊢
      nlinarith
    let children := BinaryRecursiveDot.tabulate (fin ((r+t-1)/t)) child
    let oldChildren := BinaryRecursiveDot.tabulate (fin ((r+t-1)/t)) oldChild
    have childrenval : children.value=oldChildren.value := by
      apply table_ext (fin ((r+t-1)/t))
      intro g
      simp only [children,oldChildren,BinaryRecursiveDot.tabulate_read,childval]
    have hchildren : children.bitSteps≤oldChildren.bitSteps+
        ((r+t-1)/t)*(4*t*((a*b)^k+(b*c)^k)+RetainedEqualCopyCosts.control r t (a*b) (b*c) (c*a) k)*unit K W := by
      have hs := Finset.sum_le_sum (fun g (_ : g∈Finset.univ) => childbits g)
      simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] at hs
      simpa only [children,oldChildren,BinaryRecursiveDot.tabulate_bits,mul_assoc] using hs
    have hl := forms_bits ha hb K W k hAB hk d.left x
    have hr := forms_bits hb hc K W k hBC hk d.middle y
    have hout := output_bits hc ha ht K W k hCA hk d.right children.value
    rw [childrenval] at hout
    change left.bitSteps+right.bitSteps+children.bitSteps+
      (output hc ha ht k d.right children.value).bitSteps≤
      oldLeft.bitSteps+oldRight.bitSteps+oldChildren.bitSteps+
      (oldOutput ht k d.right oldChildren.value).bitSteps+_
    rw [childrenval]
    change left.bitSteps≤oldLeft.bitSteps+_ at hl
    change right.bitSteps≤oldRight.bitSteps+_ at hr
    simp only [RetainedEqualCopyCosts.control]
    ring_nf at hl hr hchildren hout ⊢
    omega

#print axioms output_bits
#print axioms run_bits

#print axioms padded_bits
#print axioms childRead_bits

#print axioms read_unit
#print axioms rank_read_unit
#print axioms coefficient_unit
#print axioms tabulate_unit
#print axioms rank_tabulate_unit
#print axioms forms_bits
end ThinMatrix.BinaryAddressedCosts
