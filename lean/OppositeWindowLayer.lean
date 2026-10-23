import TernaryWindowAddress

set_option autoImplicit false

/-! One full retained layer of the forward integer opposite-basis map.
Addresses use binary ternary scans. Every coefficient is copied and written;
no inverse, division by two or coefficient re-encoding is used. -/
namespace ThinMatrix.OppositeWindowLayer
open BinaryCell BinaryGroupedCoordinates BinaryGroupedPreparation CroppedGroupedSuffix
open scoped BigOperators

abbrev Source (N C : ℕ) := Vector (Vector Cell C) (3^N)
def value {N C : ℕ} (X : Source N C) (w : Word N) (c : Fin C) : ℤ :=
  view ((X.get (StoredGroupedCompletion.rawIndex N w)).get c)
def Bound {N C : ℕ} (X : Source N C) (A : ℕ) : Prop := ∀ i c, (view ((X.get i).get c)).natAbs≤A

def matrix : Fin 3 → Fin 3 → ℤ := ![![1,1,0],![1,-1,0],![0,0,-1]]

theorem ordinary_local (normalBit oppositeBit : Bool) (a : Fin 3) :
    (∑ b, localForm oppositeBit normalBit b*matrix b a)=
      WalshEmbedding.ordinaryOpposite normalBit oppositeBit (SourceCoordinates.oppositeEquiv a) := by
  cases normalBit <;> cases oppositeBit <;> fin_cases a <;> decide

def localStep {N : ℕ} (axis : Fin N) (X : Word N → ℤ) (w : Word N) : ℤ :=
  if w axis=0 then X (Function.update w axis 0)+X (Function.update w axis 1)
  else if w axis=1 then X (Function.update w axis 0)-X (Function.update w axis 1)
  else -X (Function.update w axis 2)

theorem localStep_sum {N : ℕ} (axis : Fin N) (X : Word N → ℤ) (w : Word N) :
    localStep axis X w=∑ a, matrix (w axis) a*X (Function.update w axis a) := by
  have h : w axis=0 ∨ w axis=1 ∨ w axis=2 := by have := (w axis).isLt; omega
  rcases h with h | h | h <;> simp [localStep,matrix,h,Fin.sum_univ_succ,sub_eq_add_neg]

def cell (digit : Fin 3) (a b c : Cell) : Run Cell :=
  let aa := copy a
  let bb := copy b
  let cc := copy c
  let arithmetic := if digit=0 then add aa.value bb.value else if digit=1 then sub aa.value bb.value else neg cc.value
  let out := copy arithmetic.value
  ⟨out.value,aa.bitSteps+bb.bitSteps+cc.bitSteps+arithmetic.bitSteps+out.bitSteps,80⟩

theorem cell_value (digit : Fin 3) (a b c : Cell) :
    view (cell digit a b c).value=if digit=0 then view a+view b else if digit=1 then view a-view b else -view c := by
  unfold cell
  split <;> simp_all
  split <;> simp_all

theorem cell_bound (digit : Fin 3) (a b c : Cell) (A : ℕ)
    (ha : (view a).natAbs≤A) (hb : (view b).natAbs≤A) (hc : (view c).natAbs≤A) :
    (view (cell digit a b c).value).natAbs≤2*A := by
  rw [cell_value]
  split
  · exact (Int.natAbs_add_le _ _).trans (by omega)
  · split
    · exact (Int.natAbs_sub_le _ _).trans (by omega)
    · simp only [Int.natAbs_neg]; omega

theorem cell_bits (digit : Fin 3) (a b c : Cell) (A : ℕ)
    (ha : (view a).natAbs≤A) (hb : (view b).natAbs≤A) (hc : (view c).natAbs≤A) :
    (cell digit a b c).bitSteps≤5*BackendScalarBits.backendScalarUnit (2*A).size := by
  have wa : (view a).natAbs.size≤(2*A).size := Nat.size_le_size (by omega)
  have wb : (view b).natAbs.size≤(2*A).size := Nat.size_le_size (by omega)
  have wc : (view c).natAbs.size≤(2*A).size := Nat.size_le_size (by omega)
  have ca := copy_price _ a wa
  have cb := copy_price _ b wb
  have cc := copy_price _ c wc
  let ar := if digit=0 then add (copy a).value (copy b).value else
    if digit=1 then sub (copy a).value (copy b).value else neg (copy c).value
  have hw : ar.bitSteps≤BackendScalarBits.backendScalarUnit (2*A).size := by
    dsimp only [ar]; split
    · exact add_price _ _ _ (by simpa using wa) (by simpa using wb)
    · split
      · exact sub_price _ _ _ (by simpa using wa) (by simpa using wb)
      · exact sub_price _ _ _ (by simp) (by simpa using wc)
  have hm : (view ar.value).natAbs≤2*A := by
    have hh := cell_bound digit a b c A ha hb hc
    simpa only [cell,copy_view] using hh
  have hd := copy_price _ ar.value (Nat.size_le_size hm)
  change _+_+_+ar.bitSteps+(copy ar.value).bitSteps≤_
  omega

def row {N C : ℕ} (axis : Fin N) (X : Source N C) (i : Fin (3^N)) : Run (Vector Cell C) :=
  let word := WindowSelection.decode N i.val
  let a := TernaryWindowAddress.locateReplacement word.value axis 0
  let b := TernaryWindowAddress.locateReplacement word.value axis 1
  let c := TernaryWindowAddress.locateReplacement word.value axis 2
  let out := tabulate (X.get i) (fun col => cell (word.value.get axis)
    ((X.get a.value).get col) ((X.get b.value).get col) ((X.get c.value).get col))
  ⟨out.value,a.bitSteps+b.bitSteps+c.bitSteps+out.bitSteps,
    word.work+a.control+b.control+c.control+out.control+8*N+24⟩

theorem row_value {N C : ℕ} (axis : Fin N) (X : Source N C) (w : Word N) (col : Fin C) :
    view ((row axis X (StoredGroupedCompletion.rawIndex N w)).value.get col)=localStep axis (fun w => value X w col) w := by
  simp only [row,tabulate_get,cell_value,TernaryWindowAddress.locateReplacement_value,
    WindowSelection.decode_index,Equiv.symm_apply_apply,localStep,value]

def execute {N C : ℕ} (axis : Fin N) (X : Source N C) : Run (Source N C) := tabulate X (fun i => row axis X i)

theorem execute_value {N C : ℕ} (axis : Fin N) (X : Source N C) (w : Word N) (col : Fin C) :
    value (execute axis X).value w col=localStep axis (fun w => value X w col) w := by
  simp only [execute,value,tabulate_get,row_value]

def rowBitBudget (N C A : ℕ) : ℕ := 3*addressBudget N+C*(5*BackendScalarBits.backendScalarUnit (2*A).size)
def rowControlBudget (N C : ℕ) : ℕ := N*(6*N+16)+2+3*(48*N+26)+(C*112+8)+8*N+24

theorem row_bits {N C : ℕ} (axis : Fin N) (X : Source N C) (i : Fin (3^N))
    (A : ℕ) (ha : Bound X A) : (row axis X i).bitSteps≤rowBitBudget N C A := by
  have h (a : Fin 3) := TernaryWindowAddress.locateReplacement_bits (WindowSelection.decode N i.val).value axis a
  have hc := tabulate_bits (X.get i) (fun col => cell ((WindowSelection.decode N i.val).value.get axis)
    ((X.get (TernaryWindowAddress.locateReplacement (WindowSelection.decode N i.val).value axis 0).value).get col)
    ((X.get (TernaryWindowAddress.locateReplacement (WindowSelection.decode N i.val).value axis 1).value).get col)
    ((X.get (TernaryWindowAddress.locateReplacement (WindowSelection.decode N i.val).value axis 2).value).get col))
    (fun col => cell_bits _ _ _ _ A (ha _ col) (ha _ col) (ha _ col))
  have h0 := h 0; have h1 := h 1; have h2 := h 2
  simp only [row,rowBitBudget]
  omega

theorem row_control {N C : ℕ} (axis : Fin N) (X : Source N C) (i : Fin (3^N)) :
    (row axis X i).control≤rowControlBudget N C := by
  have hd := WindowSelection.decode_work N i.val
  have hc := tabulate_control (X.get i) (fun col => cell ((WindowSelection.decode N i.val).value.get axis)
    ((X.get (TernaryWindowAddress.locateReplacement (WindowSelection.decode N i.val).value axis 0).value).get col)
    ((X.get (TernaryWindowAddress.locateReplacement (WindowSelection.decode N i.val).value axis 1).value).get col)
    ((X.get (TernaryWindowAddress.locateReplacement (WindowSelection.decode N i.val).value axis 2).value).get col))
    (W:=80) (by intro col; rfl)
  simp only [row,rowControlBudget,TernaryWindowAddress.locateReplacement_control]
  omega

def bitBudget (N C A : ℕ) : ℕ := 3^N*rowBitBudget N C A
def controlBudget (N C : ℕ) : ℕ := 3^N*(rowControlBudget N C+32)+8

theorem execute_bits {N C : ℕ} (axis : Fin N) (X : Source N C) (A : ℕ) (ha : Bound X A) :
    (execute axis X).bitSteps≤bitBudget N C A := tabulate_bits _ _ (fun i => row_bits axis X i A ha)

theorem execute_control {N C : ℕ} (axis : Fin N) (X : Source N C) :
    (execute axis X).control≤controlBudget N C := tabulate_control _ _ (fun i => row_control axis X i)

theorem execute_bound {N C : ℕ} (axis : Fin N) (X : Source N C) (A : ℕ) (ha : Bound X A) :
    Bound (execute axis X).value (2*A) := by
  intro i c
  simp only [execute,tabulate_get,row]
  exact cell_bound _ _ _ _ A (ha _ c) (ha _ c) (ha _ c)

def indicator {N : ℕ} (w : Word N) : Fin N → Bool := fun i => decide (w i=2)

theorem indicator_update {N : ℕ} (w : Word N) (axis : Fin N) (a : Fin 3)
    (h : (a=2) ↔ w axis=2) : indicator (Function.update w axis a)=indicator w := by
  funext i
  by_cases hi : i=axis
  · subst i; simp only [indicator,Function.update_self,h]
  · simp only [indicator,Function.update_of_ne hi]

def Supported {N C : ℕ} (P : (Fin N → Bool) → Prop) (X : Source N C) : Prop :=
  ∀ w c, ¬P (indicator w) → value X w c=0

theorem execute_supported {N C : ℕ} (axis : Fin N) (X : Source N C)
    (P : (Fin N → Bool) → Prop) (hs : Supported P X) : Supported P (execute axis X).value := by
  intro w c hp
  rw [execute_value]
  have hz (a : Fin 3) (h : (a=2) ↔ w axis=2) : value X (Function.update w axis a) c=0 := by
    apply hs
    simpa only [indicator_update w axis a h] using hp
  have h : w axis=0 ∨ w axis=1 ∨ w axis=2 := by have := (w axis).isLt; omega
  rcases h with h | h | h
  · simp [localStep,h,hz 0 (by simp [h]),hz 1 (by simp [h])]
  · simp [localStep,h,hz 0 (by simp [h]),hz 1 (by simp [h])]
  · simp [localStep,h,hz 2 (by simp [h])]

#print axioms row_bits
#print axioms row_control
#print axioms execute_bits
#print axioms execute_control
#print axioms execute_bound
#print axioms indicator_update
#print axioms execute_supported
#print axioms ordinary_local
#print axioms localStep_sum
#print axioms cell_value
#print axioms cell_bound
#print axioms cell_bits
#print axioms row_value
#print axioms execute_value
end ThinMatrix.OppositeWindowLayer
