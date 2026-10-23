import BinaryMatrixPowers

set_option autoImplicit false

/-! Pad one ordinary matrix product into a retained simultaneous product,
then crop its original output coordinates. Depth is selected by natural
ceiling logarithms; their binary cost and address lowering remain separate.
Copies retain signed cells and their indexed-control charges. -/
namespace ThinMatrix.PaddedMatrix
open scoped BigOperators
open RecursiveTable (Layout Table prod fin power read)
open BinaryCell BinaryRecursiveDot

variable {A : Type}

def embed (a : Layout A) {n : ℕ} (h : n≤a.size) (i : Fin n) : A :=
  a.index.symm ⟨i.val,i.isLt.trans_le h⟩

@[simp] theorem embed_index (a : Layout A) {n : ℕ} (h : n≤a.size) (i : Fin n) :
    (a.index (embed a h i)).val=i.val := by simp [embed]

theorem sum_padding {R : Type} [AddCommMonoid R] (n N : ℕ) (h : n≤N) (f : Fin n → R) :
    (∑ i : Fin N, if hi : i.val < n then f ⟨i.val,hi⟩ else 0)=∑ i,f i := by
  induction n generalizing N with
  | zero => simp
  | succ n ih =>
    obtain ⟨N,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : N≠0)
    rw [Fin.sum_univ_succ,Fin.sum_univ_succ]
    simp only [Fin.val_zero,Nat.zero_lt_succ,↓reduceDIte,Fin.val_succ,Nat.succ_lt_succ_iff]
    congr 1
    exact ih N (by omega) (fun i => f i.succ)

def matrix (n m : ℕ) := prod (fin n) (fin m)

def pad {A B : Type} (a : Layout A) (b : Layout B) (t n m : ℕ)
    (x : Table (matrix n m) Cell) : Run (Table (prod (fin t) (prod a b)) Cell) :=
  tabulate (prod (fin t) (prod a b)) (fun p =>
    if p.1.val = 0 then
      if hi : (a.index p.2.1).val < n then
        if hj : (b.index p.2.2).val < m then
          ⟨read x (⟨_,hi⟩,⟨_,hj⟩),0,16⟩
        else ⟨zero,0,16⟩
      else ⟨zero,0,16⟩
    else ⟨zero,0,16⟩)

@[simp] theorem pad_value {A B : Type} (a : Layout A) (b : Layout B) (t n m : ℕ)
    (x : Table (matrix n m) Cell) (p : Fin t×(A×B)) :
    read (pad a b t n m x).value p=
      if p.1.val = 0 then
        if hi : (a.index p.2.1).val < n then
          if hj : (b.index p.2.2).val < m then read x (⟨_,hi⟩,⟨_,hj⟩) else zero
        else zero
      else zero := by
  simp only [pad,tabulate_read]
  split_ifs <;> rfl

def crop {A C : Type} (a : Layout A) (c : Layout C) {t n p : ℕ}
    (ht : 0<t) (ha : n≤a.size) (hc : p≤c.size)
    (z : Table (prod (fin t) (prod c a)) Cell) : Run (Table (matrix n p) Cell) :=
  tabulate (matrix n p) (fun i => ⟨read z (⟨0,ht⟩,(embed c hc i.2,embed a ha i.1)),0,8⟩)

@[simp] theorem crop_value {A C : Type} (a : Layout A) (c : Layout C) {t n p : ℕ}
    (ht : 0<t) (ha : n≤a.size) (hc : p≤c.size)
    (z : Table (prod (fin t) (prod c a)) Cell) (i : Fin n×Fin p) :
    read (crop a c ht ha hc z).value i=read z (⟨0,ht⟩,(embed c hc i.2,embed a ha i.1)) := by
  simp only [crop,tabulate_read]

theorem pad_costs {A B : Type} [Fintype A] [Fintype B]
    (a : Layout A) (b : Layout B) (t n m : ℕ) (x : Table (matrix n m) Cell) :
    (pad a b t n m x).bitSteps=0 ∧ (pad a b t n m x).control=48*t*a.size*b.size+8 := by
  have hv (z : Fin t×(A×B)) :
      (if z.1.val=0 then
        if hi : (a.index z.2.1).val < n then
          if hj : (b.index z.2.2).val < m then
            (⟨read x (⟨_,hi⟩,⟨_,hj⟩),0,16⟩ : Run Cell)
          else ⟨zero,0,16⟩
        else ⟨zero,0,16⟩
      else ⟨zero,0,16⟩).bitSteps=0 ∧
      (if z.1.val=0 then
        if hi : (a.index z.2.1).val < n then
          if hj : (b.index z.2.2).val < m then
            (⟨read x (⟨_,hi⟩,⟨_,hj⟩),0,16⟩ : Run Cell)
          else ⟨zero,0,16⟩
        else ⟨zero,0,16⟩
      else ⟨zero,0,16⟩).control=16 := by split_ifs <;> exact ⟨rfl,rfl⟩
  constructor
  · simp only [pad,tabulate_bits,(hv _).1,Finset.sum_const_zero]
  · simp only [pad,tabulate_control,(hv _).2,Finset.sum_const,Finset.card_univ,
      Fintype.card_prod,Fintype.card_fin,smul_eq_mul]
    rw [←RecursiveTable.size_eq_card a,←RecursiveTable.size_eq_card b]
    simp only [prod,fin];ring

theorem crop_costs {A C : Type} (a : Layout A) (c : Layout C) {t n p : ℕ}
    (ht : 0<t) (ha : n≤a.size) (hc : p≤c.size)
    (z : Table (prod (fin t) (prod c a)) Cell) :
    (crop a c ht ha hc z).bitSteps=0 ∧ (crop a c ht ha hc z).control=40*n*p+8 := by
  simp only [crop,tabulate_bits,tabulate_control,Finset.sum_const_zero,Finset.sum_const,
    Finset.card_univ,Fintype.card_prod,Fintype.card_fin,smul_eq_mul,matrix,prod,fin]
  constructor
  · trivial
  · ring

theorem pad_bound {A B : Type} (a : Layout A) (b : Layout B) (t n m H : ℕ)
    (x : Table (matrix n m) Cell) (hx : BinaryRetainedBounds.Bounded x H) :
    BinaryRetainedBounds.Bounded (pad a b t n m x).value H := by
  intro z
  simp only [pad_value]
  split_ifs
  · exact hx _
  all_goals simp

variable {I J K : Type} [Fintype I] [Fintype J] [Fintype K]
  [DecidableEq I] [DecidableEq J] [DecidableEq K] {r t n m p : ℕ}

def execute (a : Layout I) (b : Layout J) (c : Layout K) (ht : 0<t)
    (d : RetainedEqualCopy.Base r t (prod a b) (prod b c) (prod c a) ℚ)
    (k : ℕ) (ha : n≤a.size^k) (hc : p≤c.size^k)
    (x : Table (matrix n m) Cell) (y : Table (matrix m p) Cell) : Run (Table (matrix n p) Cell) :=
  let left := pad (power a k) (power b k) t n m x
  let right := pad (power b k) (power c k) t m p y
  let answer := BinaryMatrixPowers.execute a b c ht d k left.value right.value
  let output := crop (power a k) (power c k) ht (by simpa using ha) (by simpa using hc) answer.value
  ⟨output.value,left.bitSteps+right.bitSteps+answer.bitSteps+output.bitSteps,
    left.control+right.control+answer.control+output.control+16⟩

set_option backward.isDefEq.respectTransparency false in
theorem execute_correct (a : Layout I) (b : Layout J) (c : Layout K) (ht : 0<t)
    (d : RetainedEqualCopy.Base r t (prod a b) (prod b c) (prod c a) ℚ)
    (hd : FiniteTrilinear.total d.terms=FiniteDirectSum.diagonal (Fin t)
      (FiniteMatrixTensor.coeff I J K ℚ))
    (k : ℕ) (ha : n≤a.size^k) (hb : m≤b.size^k) (hc : p≤c.size^k)
    (x : Table (matrix n m) Cell) (y : Table (matrix m p) Cell) (i : Fin n×Fin p) :
    view (read (execute a b c ht d k ha hc x y).value i)=
      ∑ j : Fin m,view (read x (i.1,j))*view (read y (j,i.2)) := by
  simp only [execute,crop_value]
  rw [BinaryMatrixPowers.execute_correct a b c ht d hd]
  let ap := power a k
  let bp := power b k
  let cp := power c k
  have han : n≤ap.size := by simpa [ap] using ha
  have hcn : p≤cp.size := by simpa [cp] using hc
  have hbn : m≤bp.size := by simpa [bp] using hb
  change (∑ v : PolynomialDegeneration.PowerIndex J k,
      view (read (pad ap bp t n m x).value (⟨0,ht⟩,(embed ap han i.1,v)))*
      view (read (pad bp cp t m p y).value (⟨0,ht⟩,(v,embed cp hcn i.2))))=_
  rw [←bp.index.symm.sum_comp]
  simp only [pad_value,↓reduceDIte,embed_index,i.1.isLt,i.2.isLt,
    Equiv.apply_symm_apply]
  have hh := sum_padding m bp.size hbn
    (fun j => view (read x (i.1,j))*view (read y (j,i.2)))
  apply Eq.trans _ hh
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> simp


set_option backward.isDefEq.respectTransparency false in
omit [DecidableEq I] [DecidableEq J] [DecidableEq K] in
theorem power_matrix_bits (a : Layout I) (b : Layout J) (c : Layout K) (ht : 0<t)
    (d : RetainedEqualCopy.Base r t (prod a b) (prod b c) (prod c a) ℚ) (k H : ℕ) (hH : 1≤H)
    (x : Table (BinaryMatrixPowers.matrixLayout t a b k) Cell)
    (y : Table (BinaryMatrixPowers.matrixLayout t b c k) Cell)
    (hx : BinaryRetainedBounds.Bounded x H) (hy : BinaryRetainedBounds.Bounded y H) :
    (BinaryMatrixPowers.execute a b c ht d k x y).bitSteps≤BinaryRecursiveCost.bits d k H := by
  have hxl : BinaryRetainedBounds.Bounded (BinaryMatrixPowers.toWords a b k x).value H := by
    intro i;simpa only [BinaryMatrixPowers.toWords,tabulate_read] using hx (i.1,MatrixPowerReindex.unpair k i.2)
  have hyl : BinaryRetainedBounds.Bounded (BinaryMatrixPowers.toWords b c k y).value H := by
    intro i;simpa only [BinaryMatrixPowers.toWords,tabulate_read] using hy (i.1,MatrixPowerReindex.unpair k i.2)
  have hh := BinaryRecursiveCost.execute_bits ht d k H hH _ _ hxl hyl
  simpa only [BinaryMatrixPowers.execute,BinaryMatrixPowers.toWords,BinaryMatrixPowers.fromWords,
    tabulate_bits,Finset.sum_const_zero,zero_add,add_zero] using hh

set_option backward.isDefEq.respectTransparency false in
omit [DecidableEq I] [DecidableEq J] [DecidableEq K] in
theorem execute_bits (a : Layout I) (b : Layout J) (c : Layout K) (ht : 0<t)
    (d : RetainedEqualCopy.Base r t (prod a b) (prod b c) (prod c a) ℚ)
    (k H : ℕ) (ha : n≤a.size^k) (hc : p≤c.size^k) (hH : 1≤H)
    (x : Table (matrix n m) Cell) (y : Table (matrix m p) Cell)
    (hx : BinaryRetainedBounds.Bounded x H) (hy : BinaryRetainedBounds.Bounded y H) :
    (execute a b c ht d k ha hc x y).bitSteps≤BinaryRecursiveCost.bits d k H := by
  have hh := power_matrix_bits a b c ht d k H hH _ _
    (pad_bound (power a k) (power b k) t n m H x hx)
    (pad_bound (power b k) (power c k) t m p H y hy)
  simpa only [execute,(pad_costs _ _ _ _ _ _).1,(crop_costs _ _ _ _ _ _).1,
    zero_add,add_zero] using hh


set_option backward.isDefEq.respectTransparency false in
omit [DecidableEq I] [DecidableEq J] [DecidableEq K] in
theorem execute_control (a : Layout I) (b : Layout J) (c : Layout K) (ht : 0<t)
    (d : RetainedEqualCopy.Base r t (prod a b) (prod b c) (prod c a) ℚ)
    (k : ℕ) (ha : n≤a.size^k) (hc : p≤c.size^k)
    (x : Table (matrix n m) Cell) (y : Table (matrix m p) Cell) :
    (execute a b c ht d k ha hc x y).control=
      (BinaryMatrixPowers.execute a b c ht d k
        (pad (power a k) (power b k) t n m x).value
        (pad (power b k) (power c k) t m p y).value).control+
      48*t*(a.size^k*b.size^k+b.size^k*c.size^k)+40*n*p+40 := by
  simp only [execute,(pad_costs _ _ _ _ _ _).2,(crop_costs _ _ _ _ _ _).2,RecursiveTable.power_size]
  ring

def depth (a b c n m p : ℕ) : ℕ :=
  max (Nat.clog a n) (max (Nat.clog b m) (Nat.clog c p))

theorem depth_fits (a b c n m p : ℕ) (ha : 1<a) (hb : 1<b) (hc : 1<c) :
    n≤a^depth a b c n m p ∧ m≤b^depth a b c n m p ∧ p≤c^depth a b c n m p := by
  refine ⟨?_,?_,?_⟩
  · exact (Nat.le_pow_clog ha n).trans (Nat.pow_le_pow_right ha.le (le_max_left _ _))
  · exact (Nat.le_pow_clog hb m).trans (Nat.pow_le_pow_right hb.le
      ((le_max_left _ _).trans (le_max_right _ _)))
  · exact (Nat.le_pow_clog hc p).trans (Nat.pow_le_pow_right hc.le
      ((le_max_right _ _).trans (le_max_right _ _)))

def atSize (a : Layout I) (b : Layout J) (c : Layout K) (ht : 0<t)
    (ha : 1<a.size) (hb : 1<b.size) (hc : 1<c.size)
    (d : RetainedEqualCopy.Base r t (prod a b) (prod b c) (prod c a) ℚ)
    (x : Table (matrix n m) Cell) (y : Table (matrix m p) Cell) : Run (Table (matrix n p) Cell) :=
  let fits := depth_fits a.size b.size c.size n m p ha hb hc
  execute a b c ht d (depth a.size b.size c.size n m p) fits.1 fits.2.2 x y

theorem atSize_correct (a : Layout I) (b : Layout J) (c : Layout K) (ht : 0<t)
    (ha : 1<a.size) (hb : 1<b.size) (hc : 1<c.size)
    (d : RetainedEqualCopy.Base r t (prod a b) (prod b c) (prod c a) ℚ)
    (hd : FiniteTrilinear.total d.terms=FiniteDirectSum.diagonal (Fin t)
      (FiniteMatrixTensor.coeff I J K ℚ))
    (x : Table (matrix n m) Cell) (y : Table (matrix m p) Cell) (i : Fin n×Fin p) :
    view (read (atSize a b c ht ha hb hc d x y).value i)=
      ∑ j : Fin m,view (read x (i.1,j))*view (read y (j,i.2)) :=
  execute_correct a b c ht d hd _ (depth_fits _ _ _ _ _ _ ha hb hc).1
    (depth_fits _ _ _ _ _ _ ha hb hc).2.1 (depth_fits _ _ _ _ _ _ ha hb hc).2.2 x y i

#print axioms execute_control
#print axioms power_matrix_bits
#print axioms execute_bits
#print axioms embed_index
#print axioms pad_costs
#print axioms crop_costs
#print axioms pad_bound
#print axioms depth_fits
#print axioms atSize_correct
#print axioms sum_padding
#print axioms execute_correct
end ThinMatrix.PaddedMatrix
