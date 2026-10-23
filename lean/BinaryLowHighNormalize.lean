import BinaryGroupedPreparation

set_option autoImplicit false
set_option maxRecDepth 6000
set_option maxHeartbeats 2000000

/-! Construct the normalization divisor in binary, add stored LOW/HIGH
cells and divide their complete numerator. Arithmetic and indexed-control
counters remain separate. No intermediate integer-to-bits conversion. -/
namespace ThinMatrix.BinaryLowHighNormalize
open BinaryCell BinaryGroupedCoordinates BinaryGroupedPreparation
open scoped BigOperators

def four : Cell := ⟨⟨false,[false,false,true]⟩,by decide⟩
@[simp] theorem four_view : view four=4 := rfl

def power4 : ℕ → Run Cell
  | 0 => ⟨BinaryModularCell.one,0,1⟩
  | L+1 =>
    let prev := power4 L
    let out := mul four prev.value
    ⟨out.value,prev.bitSteps+out.bitSteps,prev.control+8⟩

theorem power4_view (L : ℕ) : view (power4 L).value=(4:ℤ)^L := by
  induction L with
  | zero => rfl
  | succ L ih => simp only [power4,mul_view,four_view,ih,pow_succ,mul_comm]

theorem power4_size (L : ℕ) : (view (power4 L).value).natAbs.size=2*L+1 := by
  rw [power4_view,Int.natAbs_pow]
  change (4^L : ℕ).size=_
  rw [show (4:ℕ)=2^2 by decide,←pow_mul,Nat.size_pow]

theorem scalar_mono {B C : ℕ} (h : B≤C) : BackendScalarBits.backendScalarUnit B≤BackendScalarBits.backendScalarUnit C := by
  unfold BackendScalarBits.backendScalarUnit BackendScalarBits.scalarUnit
  exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2))

theorem power4_bits (L : ℕ) : (power4 L).bitSteps≤L*BackendScalarBits.backendScalarUnit (2*L+3) := by
  induction L with
  | zero => simp [power4]
  | succ L ih =>
    have hm := mul_price (2*L+3) four (power4 L).value (by simp only [four_view]; change 3≤_;omega)
      (by rw [power4_size];omega)
    have hmono := scalar_mono (show 2*L+3≤2*(L+1)+3 by omega)
    change (power4 L).bitSteps+(mul four (power4 L).value).bitSteps≤_
    calc
      _ ≤ (L+1)*BackendScalarBits.backendScalarUnit (2*L+3) := by nlinarith
      _ ≤ _ := Nat.mul_le_mul_left _ hmono

theorem power4_control (L : ℕ) : (power4 L).control=8*L+1 := by
  induction L with
  | zero => rfl
  | succ L ih => simp only [power4,ih];omega

structure CellOutput where
  numerator : Result Cell
  quotient : Result Cell

def cell (divisor low high : Cell) : Run CellOutput :=
  let numerator := add low high
  let quotient := BinaryModularCell.floor divisor numerator.value
  ⟨⟨numerator,quotient⟩,numerator.bitSteps+quotient.bitSteps,12⟩

def cellValue (out : CellOutput) : Cell := out.quotient.value

theorem cell_value (L : ℕ) (low high : Cell) :
    view (cellValue (cell (power4 L).value low high).value)=(view low+view high)/(4:ℤ)^L := by
  unfold cellValue cell
  rw [BinaryModularCell.floor_view (power4 L).value _ (by rw [power4_view]; positivity),add_view,power4_view]

def width (L A B : ℕ) : ℕ := (A+B).size+2*L+3

def cellBudget (L A B : ℕ) : ℕ :=
  BackendScalarBits.backendScalarUnit (width L A B)+1024*(width L A B+1)^2

theorem cell_bits (L A B : ℕ) (low high : Cell)
    (hl : (view low).natAbs≤A) (hh : (view high).natAbs≤B) :
    (cell (power4 L).value low high).bitSteps≤cellBudget L A B := by
  have ha : (view low).natAbs.size≤width L A B := (Nat.size_le_size (hl.trans (Nat.le_add_right A B))).trans (by unfold width;omega)
  have hb : (view high).natAbs.size≤width L A B := (Nat.size_le_size (hh.trans (Nat.le_add_left B A))).trans (by unfold width;omega)
  have hn : (view (add low high).value).natAbs≤A+B := by
    rw [add_view]
    exact (Int.natAbs_add_le _ _).trans (Nat.add_le_add hl hh)
  have hp := BinaryModularCell.floor_price_square (width L A B) (power4 L).value (add low high).value
    (by rw [power4_size];unfold width;omega) ((Nat.size_le_size hn).trans (by unfold width;omega))
  have hs := add_price (width L A B) low high ha hb
  change (add low high).bitSteps+(BinaryModularCell.floor (power4 L).value (add low high).value).bitSteps≤_
  exact Nat.add_le_add hs hp

def row {q : ℕ} (divisor : Cell) (low high : Vector Cell q) : Run (Vector CellOutput q) :=
  tabulate low (fun i => cell divisor (low.get i) (high.get i))

def table {M q : ℕ} (L : ℕ) (low high : Vector (Vector Cell q) M) :=
  let divisor := power4 L
  let rows := tabulate low (fun i => row divisor.value (low.get i) (high.get i))
  (divisor,rows)

def output {M q : ℕ} (out : Vector (Vector CellOutput q) M) (i : Fin M) (r : Fin q) : Cell :=
  cellValue ((out.get i).get r)

theorem table_value {M q : ℕ} (L : ℕ) (low high : Vector (Vector Cell q) M) (i : Fin M) (r : Fin q) :
    view (output (table L low high).2.value i r)=
      (view ((low.get i).get r)+view ((high.get i).get r))/(4:ℤ)^L := by
  simp only [table,output,row,tabulate_get,cell_value]

theorem table_bits {M q : ℕ} (L A B : ℕ) (low high : Vector (Vector Cell q) M)
    (hl : ∀ i r, (view ((low.get i).get r)).natAbs≤A)
    (hh : ∀ i r, (view ((high.get i).get r)).natAbs≤B) :
    (table L low high).1.bitSteps+(table L low high).2.bitSteps≤
      L*BackendScalarBits.backendScalarUnit (2*L+3)+M*(q*cellBudget L A B) := by
  have hr : ∀ i, (row (power4 L).value (low.get i) (high.get i)).bitSteps≤q*cellBudget L A B := by
    intro i
    exact tabulate_bits _ _ (fun r => cell_bits L A B _ _ (hl i r) (hh i r))
  exact Nat.add_le_add (power4_bits L) (tabulate_bits low _ hr)

theorem table_control {M q : ℕ} (L : ℕ) (low high : Vector (Vector Cell q) M) :
    (table L low high).1.control+(table L low high).2.control≤8*L+1+M*(44*q+40)+8 := by
  have hr : ∀ i, (row (power4 L).value (low.get i) (high.get i)).control≤44*q+8 := by
    intro i
    have he := tabulate_control (low.get i) (fun j => cell (power4 L).value ((low.get i).get j) ((high.get i).get j)) (W:=12) (fun _ => le_refl _)
    simpa only [row,Nat.reduceAdd,Nat.mul_comm] using he
  have he := tabulate_control low _ hr
  simp only [table,power4_control]
  simpa only [Nat.add_assoc,Nat.reduceAdd] using Nat.add_le_add_left he (8*L+1)

#print axioms four_view
#print axioms power4_view
#print axioms power4_size
#print axioms scalar_mono
#print axioms power4_bits
#print axioms power4_control
#print axioms cell_value
#print axioms cell_bits
#print axioms table_value
#print axioms table_bits
#print axioms table_control
end ThinMatrix.BinaryLowHighNormalize
