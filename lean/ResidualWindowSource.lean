import GraphResidualFamilies

set_option autoImplicit false

/-! Retained complete root blocks are copied into degree-major window rows.
The representation change preserves every degree and cyclic coefficient. Binary
copy work and indexed-register allocation/control are separate counters. -/
namespace ThinMatrix.ResidualWindowSource
open BinaryCell BinaryGroupedCoordinates BinaryGroupedPreparation
open BinaryResidualPolynomial ResidualFamilyKeys RetainedResidualFamily
open scoped BigOperators

/-- Copy all binary cells before flattening retained degree rows. Flattening
moves references. Its conservative charge includes copying every retained
prefix on every append, without relying on in-place append optimization. -/
def flatten {F C : ℕ} (block : Block F C) : Run (Vector Cell (F*C)) :=
  let copied := tabulate block (fun d => tabulate (block.get d) (fun r =>
    let out := copy ((block.get d).get r)
    (⟨out.value,out.bitSteps,8⟩ : Run Cell)))
  ⟨copied.value.flatten,copied.bitSteps,copied.control+8*F*(F*C)+8*F+8⟩

theorem flatten_get {F C : ℕ} (block : Block F C) (d : Fin F) (r : Fin C) :
    view ((flatten block).value.get (finProdFinEquiv (d,r))) = cellView block d r := by
  let copied := tabulate block (fun d => tabulate (block.get d) (fun r =>
    (⟨(copy ((block.get d).get r)).value,(copy ((block.get d).get r)).bitSteps,8⟩ : Run Cell)))
  change view (copied.value.flatten[(finProdFinEquiv (d,r)).val]) = _
  rw [Vector.getElem_flatten]
  have hc : 0<C := by have := r.isLt; omega
  have hd : (finProdFinEquiv (d,r)).val/C=d.val := by
    simp only [finProdFinEquiv,Equiv.coe_fn_mk]
    rw [Nat.add_mul_div_left _ _ hc,Nat.div_eq_of_lt r.isLt,zero_add]
  have hr : (finProdFinEquiv (d,r)).val%C=r.val := by
    simp [finProdFinEquiv,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt r.isLt]
  simp only [hd,hr]
  change view ((copied.value.get d).get r)=_
  simp only [copied,tabulate_get,copy_view,cellView]

theorem flatten_bits {F C : ℕ} (block : Block F C) (A : ℕ) (ha : Bound A block) :
    (flatten block).bitSteps≤F*(C*BackendScalarBits.backendScalarUnit A.size) := by
  apply tabulate_bits; intro d
  apply tabulate_bits; intro r
  exact copy_price _ _ (Nat.size_le_size (ha d r))

theorem flatten_control {F C : ℕ} (block : Block F C) :
    (flatten block).control≤F*(40*C+48)+8*F*(F*C)+16 := by
  have h := tabulate_control block (fun d => tabulate (block.get d) (fun r =>
    (⟨(copy ((block.get d).get r)).value,(copy ((block.get d).get r)).bitSteps,8⟩ : Run Cell)))
    (fun d => tabulate_control (block.get d) _ (W:=8) (by intro r; rfl))
  simp only [flatten]
  nlinarith

/-- Both casts erase at runtime; the retained array is not re-enumerated. -/
def rows {L m C : ℕ} (e : Entry L m C) : Vector (Block (m+1) C) (3^(2*(L-m))) :=
  cast (by simp only [CompleteResidualArray.Rows,selected_size,remaining_size,two_mul]) e.rows

def execute {L m C : ℕ} (e : Entry L m C) : Run (BinaryWindowPartition.Source (L-m) ((m+1)*C)) :=
  tabulate (rows e) (fun i => flatten ((rows e).get i))

theorem execute_get {L m C : ℕ} (e : Entry L m C) (i : Fin (3^(2*(L-m)))) (d : Fin (m+1)) (r : Fin C) :
    view (((execute e).value.get i).get (finProdFinEquiv (d,r))) = cellView ((rows e).get i) d r := by
  simp only [execute,tabulate_get,flatten_get]

def BoundRows {L m C : ℕ} (e : Entry L m C) (A : ℕ) : Prop := ∀ i, Bound A ((rows e).get i)

theorem execute_bound {L m C : ℕ} (e : Entry L m C) (A : ℕ) (ha : BoundRows e A) :
    BinaryWindowPartition.InputBound (execute e).value A := by
  intro i c
  obtain ⟨⟨d,r⟩,rfl⟩ := finProdFinEquiv.surjective c
  rw [execute_get]
  exact ha i d r

def bitBudget (L m C A : ℕ) : ℕ := 3^(2*(L-m))*((m+1)*(C*BackendScalarBits.backendScalarUnit A.size))
def controlBudget (L m C : ℕ) : ℕ := 3^(2*(L-m))*((m+1)*(40*C+48)+8*(m+1)*((m+1)*C)+48)+8

theorem execute_bits {L m C : ℕ} (e : Entry L m C) (A : ℕ) (ha : BoundRows e A) :
    (execute e).bitSteps≤bitBudget L m C A := tabulate_bits _ _ (fun i => flatten_bits _ A (ha i))

theorem execute_control {L m C : ℕ} (e : Entry L m C) :
    (execute e).control≤controlBudget L m C := tabulate_control _ _ (fun _ => flatten_control _)

#print axioms flatten_get
#print axioms flatten_bits
#print axioms flatten_control
#print axioms execute_get
#print axioms execute_bound
#print axioms execute_bits
#print axioms execute_control
end ThinMatrix.ResidualWindowSource
