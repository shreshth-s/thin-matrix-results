import PrefixCellTree

set_option autoImplicit false

/-! One ordinary four-form prefix contraction on retained binary trees. All
three input rows and each intermediate/output cell are copied and charged.
Tree lookups and allocation are separately annotated indexed operations. -/
namespace ThinMatrix.BinaryPrefixContraction
open BinaryCell BinaryGroupedCoordinates BinaryGroupedPreparation CroppedGroupedSuffix PrefixCellTree
open scoped BigOperators

def form : Fin 4 → Fin 3 → ℤ := ![![1,0,1],![1,0,0],![0,1,-1],![0,1,0]]
def label (p active : Bool) : Fin 4 := if p then (if active then 2 else 3) else (if active then 0 else 1)

theorem form_label (p active : Bool) (a : Fin 3) : form (label p active) a=localForm p active a := by
  cases p <;> cases active <;> fin_cases a <;> decide

def cell (q : Fin 4) (a b c : Cell) : Run Cell :=
  let aa := copy a
  let bb := copy b
  let cc := copy c
  let op := if q=0 then add aa.value cc.value else if q=1 then copy aa.value
    else if q=2 then sub bb.value cc.value else copy bb.value
  let out := copy op.value
  ⟨out.value,aa.bitSteps+bb.bitSteps+cc.bitSteps+op.bitSteps+out.bitSteps,80⟩

theorem cell_value (q : Fin 4) (a b c : Cell) :
    view (cell q a b c).value=∑ j, form q j*(![view a,view b,view c] j) := by
  fin_cases q <;> simp [cell,form,Fin.sum_univ_succ,sub_eq_add_neg]

theorem cell_bound (q : Fin 4) (a b c : Cell) (A : ℕ)
    (ha : (view a).natAbs≤A) (hb : (view b).natAbs≤A) (hc : (view c).natAbs≤A) :
    (view (cell q a b c).value).natAbs≤2*A := by
  fin_cases q
  · have h : (view a+view c).natAbs≤2*A := (Int.natAbs_add_le _ _).trans (by omega)
    simpa [cell] using h
  · simpa [cell] using (show (view a).natAbs≤2*A by omega)
  · have h : (view b-view c).natAbs≤2*A := (Int.natAbs_sub_le _ _).trans (by omega)
    simpa [cell] using h
  · simpa [cell] using (show (view b).natAbs≤2*A by omega)

theorem cell_bits (q : Fin 4) (a b c : Cell) (A : ℕ)
    (ha : (view a).natAbs≤A) (hb : (view b).natAbs≤A) (hc : (view c).natAbs≤A) :
    (cell q a b c).bitSteps≤5*BackendScalarBits.backendScalarUnit (2*A).size := by
  have wa := Nat.size_le_size (show (view a).natAbs≤2*A by omega)
  have wb := Nat.size_le_size (show (view b).natAbs≤2*A by omega)
  have wc := Nat.size_le_size (show (view c).natAbs≤2*A by omega)
  have ca := copy_price _ a wa; have cb := copy_price _ b wb; have cc := copy_price _ c wc
  let op := if q=0 then add (copy a).value (copy c).value else if q=1 then copy (copy a).value
    else if q=2 then sub (copy b).value (copy c).value else copy (copy b).value
  have ho : op.bitSteps≤BackendScalarBits.backendScalarUnit (2*A).size := by
    dsimp only [op]; split
    · exact add_price _ _ _ (by simpa using wa) (by simpa using wc)
    · split
      · exact copy_price _ _ (by simpa using wa)
      · split
        · exact sub_price _ _ _ (by simpa using wb) (by simpa using wc)
        · exact copy_price _ _ (by simpa using wb)
  have hm : (view op.value).natAbs≤2*A := by
    simpa only [cell,copy_view] using cell_bound q a b c A ha hb hc
  have hd := copy_price _ op.value (Nat.size_le_size hm)
  change _+_+_+op.bitSteps+(copy op.value).bitSteps≤_
  omega

def leafRow {C : ℕ} : {n : ℕ} → Data C n → Word n → Vector Cell C
  | 0, X, _ => X
  | _+1, X, w => leafRow (X.get (w 0)) (fun i => w i.succ)

theorem leafRow_get {C n : ℕ} (X : Data C n) (w : Word n) (c : Fin C) :
    (leafRow X w).get c=read X w c := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih _ _

/-- The quadratic indexed allowance includes the generated word closures
traversed during the three hoisted leaf-row lookups. -/
def row {C n : ℕ} (q : Fin 4) (X : Data C (n+1)) (w : Word n) : Run (Vector Cell C) :=
  let a := leafRow (X.get 0) w
  let b := leafRow (X.get 1) w
  let c := leafRow (X.get 2) w
  let out := tabulate a (fun j => cell q (a.get j) (b.get j) (c.get j))
  ⟨out.value,out.bitSteps,out.control+12*(n+1)^2+24⟩

theorem row_value {C n : ℕ} (q : Fin 4) (X : Data C (n+1)) (w : Word n) (c : Fin C) :
    view ((row q X w).value.get c)=∑ a, form q a*view (read X (Fin.cons a w) c) := by
  simp only [row,tabulate_get,cell_value,leafRow_get,PrefixCellTree.read,Fin.cons_zero,Fin.cons_succ]
  congr 1
  funext a
  fin_cases a <;> rfl

def execute {C n : ℕ} (q : Fin 4) (X : Data C (n+1)) : Run (Data C n) := build n (row q X)

theorem execute_value {C n : ℕ} (q : Fin 4) (X : Data C (n+1)) (w : Word n) (c : Fin C) :
    view (read (execute q X).value w c)=∑ a, form q a*view (read X (Fin.cons a w) c) := by
  rw [execute,build_read,row_value]

theorem execute_bound {C n : ℕ} (q : Fin 4) (X : Data C (n+1)) (A : ℕ) (ha : Bound X A) :
    Bound (execute q X).value (2*A) := by
  apply build_bound
  intro w c
  simp only [row,tabulate_get,leafRow_get]
  apply cell_bound q _ _ _ A
  · exact ha (Fin.cons 0 w) c
  · exact ha (Fin.cons 1 w) c
  · exact ha (Fin.cons 2 w) c

theorem row_bits {C n : ℕ} (q : Fin 4) (X : Data C (n+1)) (A : ℕ) (ha : Bound X A) (w : Word n) :
    (row q X w).bitSteps≤C*(5*BackendScalarBits.backendScalarUnit (2*A).size) := by
  apply tabulate_bits
  intro c
  apply cell_bits q _ _ _ A
  · simpa only [leafRow_get,PrefixCellTree.read,Fin.cons_zero,Fin.cons_succ] using ha (Fin.cons 0 w) c
  · simpa only [leafRow_get,PrefixCellTree.read,Fin.cons_zero,Fin.cons_succ] using ha (Fin.cons 1 w) c
  · simpa only [leafRow_get,PrefixCellTree.read,Fin.cons_zero,Fin.cons_succ] using ha (Fin.cons 2 w) c

theorem row_control {C n : ℕ} (q : Fin 4) (X : Data C (n+1)) (w : Word n) :
    (row q X w).control≤112*C+12*(n+1)^2+32 := by
  have h := tabulate_control (leafRow (X.get 0) w)
    (fun c => cell q ((leafRow (X.get 0) w).get c) ((leafRow (X.get 1) w).get c) ((leafRow (X.get 2) w).get c))
    (W:=80) (by intro c; rfl)
  simp only [row]
  omega

def bitBudget (n C A : ℕ) : ℕ := 3^n*(C*(5*BackendScalarBits.backendScalarUnit (2*A).size))
def controlBudget (n C : ℕ) : ℕ := 3^n*(112*C+12*(n+1)^2+32+200*(n+1))

theorem execute_bits {C n : ℕ} (q : Fin 4) (X : Data C (n+1)) (A : ℕ) (ha : Bound X A) :
    (execute q X).bitSteps≤bitBudget n C A := build_bits _ (row_bits q X A ha)

theorem execute_control {C n : ℕ} (q : Fin 4) (X : Data C (n+1)) :
    (execute q X).control≤controlBudget n C := build_control _ (row_control q X)

#print axioms form_label
#print axioms cell_value
#print axioms cell_bound
#print axioms cell_bits
#print axioms leafRow_get
#print axioms row_value
#print axioms execute_value
#print axioms execute_bound
#print axioms row_bits
#print axioms row_control
#print axioms execute_bits
#print axioms execute_control
end ThinMatrix.BinaryPrefixContraction
