import BinaryAddressedDot

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 5000

/-! Retained equal-copy recurrence consuming binary table addresses. The
algorithm keeps complete child arrays and reads the binary-computed child
slot and tensor-word address. This is the executable address refinement;
whole-program recurrence domination is proved separately. -/
namespace ThinMatrix.BinaryAddressedRecursion
open scoped BigOperators
open BinaryCell BinaryGroupedCoordinates
open RecursiveTable (Table prod fin power)
open PolynomialDegeneration RetainedEqualCopy FiniteDirectSum
variable {a b c r t : ℕ}

theorem table_ext {I V : Type} (layout : RecursiveTable.Layout I) (x y : Table layout V)
    (h : ∀ i, RecursiveTable.read x i=RecursiveTable.read y i) : x=y := by
  apply Vector.ext
  intro i hi
  simpa only [RecursiveTable.read,Equiv.apply_symm_apply,Vector.get_eq_getElem] using
    h (layout.index.symm ⟨i,hi⟩)

abbrev Cells (t a b k : ℕ) := Table (BinaryRecursiveTable.layout t a b k) Cell

def forms (ha : 0<a) (hb : 0<b) (k : ℕ)
    (coeff : Table (prod (fin r) (prod (fin t) (prod (fin a) (fin b)))) Cell)
    (x : Cells t a b (k+1)) : Run (Cells r a b k) :=
  BinaryRecursiveTable.tabulate ha hb k (fun sp =>
    BinaryAddressedDot.dot (prod (fin t) (prod (fin a) (fin b)))
      (fun i => BinaryAddressedDot.coefficient coeff sp.1 i.1 i.2)
      (fun i => BinaryRecursiveTable.read (k+1) x (i.1,(i.2,sp.2))))

set_option backward.isDefEq.respectTransparency false in
theorem forms_value (ha : 0<a) (hb : 0<b) (k : ℕ)
    (coeff : Table (prod (fin r) (prod (fin t) (prod (fin a) (fin b)))) Cell)
    (x : Cells t a b (k+1)) :
    (forms ha hb k coeff x).value=
      (BinaryRetainedEqualCopy.forms (prod (fin a) (fin b)) (power (prod (fin a) (fin b)) k) coeff
        (RecursiveTable.read x)).value := by
  simp only [forms,BinaryRecursiveTable.tabulate_value,BinaryRecursiveTable.layout,copies,
    BinaryRetainedEqualCopy.forms]
  apply table_ext (prod (fin r) (power (prod (fin a) (fin b)) k))
  intro sp
  simp only [BinaryRecursiveDot.tabulate_read,BinaryAddressedDot.dot_value,
    BinaryAddressedDot.coefficient_value,BinaryRecursiveTable.read_value]


def padded (ha : 0<a) (hb : 0<b) (k g : ℕ) (x : Cells r a b k) : Run (Cells t a b k) :=
  BinaryRecursiveTable.tabulate ha hb k (fun i =>
    let address := BinaryMatrixAddress.join t g i.1.val
    let active := BinaryChunkAddress.less address.value r
    if h : active.value=true then
      let out := BinaryRecursiveTable.read k x (⟨address.value,(BinaryChunkAddress.less_true _ _).mp h⟩,i.2)
      ⟨out.value,address.bitSteps+active.bitSteps+out.bitSteps,16⟩
    else ⟨zero,address.bitSteps+active.bitSteps,16⟩)

set_option backward.isDefEq.respectTransparency false in
theorem padded_value (ha : 0<a) (hb : 0<b) (k g : ℕ) (x : Cells r a b k) :
    (padded (t:=t) ha hb k g x).value=
      (BinaryRetainedEqualCopy.padded (t:=t) (power (prod (fin a) (fin b)) k) g x).value := by
  simp only [padded,BinaryRecursiveTable.tabulate_value,BinaryRecursiveTable.layout,copies,
    BinaryRetainedEqualCopy.padded]
  apply table_ext (prod (fin t) (power (prod (fin a) (fin b)) k))
  intro j
  simp only [BinaryRecursiveDot.tabulate_read]
  split_ifs with hx hy hy
  · rw [BinaryRecursiveTable.read_value]
    apply congrArg (fun z : Fin r => RecursiveTable.read x (z,j.2))
    apply Fin.ext
    change (BinaryMatrixAddress.join t g j.1.val).value = g*t+j.1.val
    rw [BinaryMatrixAddress.join_value]
    ring
  · apply False.elim
    apply hy
    have he := (BinaryChunkAddress.less_true _ _).mp hx
    rw [BinaryMatrixAddress.join_value] at he
    simpa only [Nat.mul_comm,Nat.add_comm] using he
  · apply False.elim
    apply hx
    apply (BinaryChunkAddress.less_true _ _).mpr
    rw [BinaryMatrixAddress.join_value]
    simpa only [Nat.mul_comm,Nat.add_comm] using hy
  · rfl


def childRead (ht : 0<t) (k : ℕ)
    (children : Table (fin ((r+t-1)/t)) (Cells t a b k))
    (s : Fin r) (word : PowerIndex (Fin a×Fin b) k) : Result Cell :=
  let address := BinaryMatrixAddress.split t s.val
  have hv := BinaryMatrixAddress.split_value t s.val ht
  let group : Fin ((r+t-1)/t) := ⟨address.value.1,by rw [hv];exact (slot r t ht s).1.isLt⟩
  let copy : Fin t := ⟨address.value.2,by rw [hv];exact Nat.mod_lt _ ht⟩
  let out := BinaryRecursiveTable.read k (children.get group) (copy,word)
  ⟨out.value,address.bitSteps+out.bitSteps+8⟩

theorem childRead_value (ht : 0<t) (k : ℕ)
    (children : Table (fin ((r+t-1)/t)) (Cells t a b k))
    (s : Fin r) (word : PowerIndex (Fin a×Fin b) k) :
    (childRead ht k children s word).value=
      RecursiveTable.read (RecursiveTable.read children (slot r t ht s).1) ((slot r t ht s).2,word) := by
  simp only [childRead,BinaryRecursiveTable.read_value]
  have hg : (⟨(BinaryMatrixAddress.split t s.val).value.1,by rw [BinaryMatrixAddress.split_value _ _ ht];exact (slot r t ht s).1.isLt⟩ : Fin ((r+t-1)/t))=(slot r t ht s).1 := by
    apply Fin.ext
    change (BinaryMatrixAddress.split t s.val).value.1=s.val/t
    rw [BinaryMatrixAddress.split_value _ _ ht]
  have hc : (⟨(BinaryMatrixAddress.split t s.val).value.2,by rw [BinaryMatrixAddress.split_value _ _ ht];exact Nat.mod_lt _ ht⟩ : Fin t)=(slot r t ht s).2 := by
    apply Fin.ext
    change (BinaryMatrixAddress.split t s.val).value.2=s.val%t
    rw [BinaryMatrixAddress.split_value _ _ ht]
  rw [hg,hc]
  rfl

def run (ha : 0<a) (hb : 0<b) (hc : 0<c) (ht : 0<t)
    (d : Base r t (prod (fin a) (fin b)) (prod (fin b) (fin c)) (prod (fin c) (fin a)) Cell) :
    (k : ℕ) → Cells t a b k → Cells t b c k → Run (Cells t c a k)
  | 0,x,y => BinaryRecursiveTable.tabulate hc ha 0 (fun z =>
      let left := BinaryRecursiveTable.read 0 x (z.1,PUnit.unit)
      let right := BinaryRecursiveTable.read 0 y (z.1,PUnit.unit)
      let out := mul left.value right.value
      ⟨out.value,left.bitSteps+right.bitSteps+out.bitSteps,16⟩)
  | k+1,x,y =>
      let left := forms ha hb k d.left x
      let right := forms hb hc k d.middle y
      let children := BinaryRecursiveDot.tabulate (fin ((r+t-1)/t)) (fun g =>
        let px := padded ha hb k g.val left.value
        let py := padded hb hc k g.val right.value
        let child := run ha hb hc ht d k px.value py.value
        ⟨child.value,px.bitSteps+py.bitSteps+child.bitSteps,px.control+py.control+child.control+8⟩)
      let output := BinaryRecursiveTable.tabulate hc ha (k+1) (fun z =>
        BinaryAddressedDot.dot (fin r) (fun s => BinaryAddressedDot.coefficient d.right s z.1 z.2.1)
          (fun s => childRead ht k children.value s z.2.2))
      ⟨output.value,left.bitSteps+right.bitSteps+children.bitSteps+output.bitSteps,
        left.control+right.control+children.control+output.control+16⟩

set_option backward.isDefEq.respectTransparency false in
theorem run_value (ha : 0<a) (hb : 0<b) (hc : 0<c) (ht : 0<t)
    (d : Base r t (prod (fin a) (fin b)) (prod (fin b) (fin c)) (prod (fin c) (fin a)) Cell)
    (k : ℕ) (x : Cells t a b k) (y : Cells t b c k) :
    (run ha hb hc ht d k x y).value=
      (BinaryRetainedEqualCopy.run (prod (fin a) (fin b)) (prod (fin b) (fin c))
        (prod (fin c) (fin a)) ht d k x y).value := by
  induction k with
  | zero =>
    apply table_ext (BinaryRecursiveTable.layout t c a 0)
    intro z
    simp only [run,BinaryRetainedEqualCopy.run,BinaryRecursiveTable.tabulate_read,
      BinaryRecursiveDot.tabulate_read,BinaryRecursiveTable.read_value]
  | succ k ih =>
    apply table_ext (BinaryRecursiveTable.layout t c a (k+1))
    intro z
    simp only [run,BinaryRetainedEqualCopy.run,BinaryRecursiveTable.tabulate_read,
      BinaryRecursiveDot.tabulate_read,BinaryAddressedDot.dot_value,
      BinaryAddressedDot.coefficient_value,childRead_value,ih,padded_value,forms_value]

def control (r t A B C : ℕ) : ℕ → ℕ
  | 0 => 56*t+8
  | k+1 => ((r+t-1)/t)*control r t A B C k+
      r*A^k*(20*t*A+44)+r*B^k*(20*t*B+44)+
      ((r+t-1)/t)*(56*t*(A^k+B^k)+56)+t*C^(k+1)*(20*r+44)+48

set_option backward.isDefEq.respectTransparency false in
theorem run_control (ha : 0<a) (hb : 0<b) (hc : 0<c) (ht : 0<t)
    (d : Base r t (prod (fin a) (fin b)) (prod (fin b) (fin c)) (prod (fin c) (fin a)) Cell)
    (k : ℕ) (x : Cells t a b k) (y : Cells t b c k) :
    (run ha hb hc ht d k x y).control=control r t (a*b) (b*c) (c*a) k := by
  have hp {u v : ℕ} (hu : 0<u) (hv : 0<v) (l g : ℕ) (x : Cells r u v l) :
      (padded (t:=t) hu hv l g x).control=56*t*(u*v)^l+8 := by
    simp only [padded,BinaryRecursiveTable.tabulate_control,BinaryRecursiveDot.tabulate_control]
    have hh (i : Fin t×PowerIndex (Fin u×Fin v) l) :
        (if h : (BinaryChunkAddress.less (BinaryMatrixAddress.join t g i.1.val).value r).value=true then
          (let out := BinaryRecursiveTable.read l x (⟨(BinaryMatrixAddress.join t g i.1.val).value,
            (BinaryChunkAddress.less_true _ _).mp h⟩,i.2)
           ⟨out.value,(BinaryMatrixAddress.join t g i.1.val).bitSteps+
             (BinaryChunkAddress.less (BinaryMatrixAddress.join t g i.1.val).value r).bitSteps+out.bitSteps,16⟩ : Run Cell)
        else ⟨zero,(BinaryMatrixAddress.join t g i.1.val).bitSteps+
          (BinaryChunkAddress.less (BinaryMatrixAddress.join t g i.1.val).value r).bitSteps,16⟩).control=16 := by
      split_ifs <;> rfl
    simp only [hh,Finset.sum_const,Finset.card_univ,Fintype.card_prod,Fintype.card_fin,
      powerIndex_card,smul_eq_mul,BinaryRecursiveTable.layout_size]
    ring
  have hf {u v : ℕ} (hu : 0<u) (hv : 0<v) (l : ℕ)
      (coeff : Table (prod (fin r) (prod (fin t) (prod (fin u) (fin v)))) Cell)
      (x : Cells t u v (l+1)) :
      (forms hu hv l coeff x).control=r*(u*v)^l*(20*t*(u*v)+44)+8 := by
    simp only [forms,BinaryRecursiveTable.tabulate_control,BinaryRecursiveDot.tabulate_control,
      BinaryAddressedDot.dot_control,Finset.sum_const,Finset.card_univ,Fintype.card_prod,
      Fintype.card_fin,powerIndex_card,smul_eq_mul,BinaryRecursiveTable.layout_size,prod,fin]
    ring
  induction k with
  | zero =>
    simp only [run,BinaryRecursiveTable.tabulate_control,BinaryRecursiveDot.tabulate_control,
      Finset.sum_const,Finset.card_univ,Fintype.card_prod,Fintype.card_fin,powerIndex_card,
      smul_eq_mul,BinaryRecursiveTable.layout_size,control,pow_zero,mul_one]
    ring
  | succ k ih =>
    simp only [run,BinaryRecursiveTable.tabulate_control,BinaryRecursiveDot.tabulate_control,
      hf,hp,ih,BinaryAddressedDot.dot_control,Finset.sum_const,Finset.card_univ,Fintype.card_prod,
      Fintype.card_fin,powerIndex_card,smul_eq_mul,BinaryRecursiveTable.layout_size,fin,control]
    ring

theorem control_bound (r t A B C k : ℕ) :
    control r t A B C k≤2*RetainedEqualCopyCosts.control r t A B C k := by
  induction k with
  | zero => simp only [control,RetainedEqualCopyCosts.control];omega
  | succ k ih =>
    have hh := Nat.mul_le_mul_left ((r+t-1)/t) ih
    simp only [control,RetainedEqualCopyCosts.control]
    ring_nf at hh ⊢
    omega

#print axioms run_control
#print axioms control_bound

#print axioms run_value

#print axioms forms_value
#print axioms padded_value
#print axioms childRead_value
end ThinMatrix.BinaryAddressedRecursion
