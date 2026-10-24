import HalfSourceSuffixChoice
import BinaryControllerExecution

set_option autoImplicit false
set_option maxHeartbeats 1200000

/-! Binary Pascal prefix rows for exact suffix support tests. Every row
entry is stored as canonical bits; no subset enumeration or native choose
computation occurs in the producer. All rows are retained. -/
namespace ThinMatrix.HalfSourcePascal
open scoped BigOperators
open BinaryGroupedCoordinates BinaryGroupedPreparation
open BinaryControllerExecution (NatCell nview)

abbrev Row (K : ℕ) := Vector NatCell (K+1)

theorem count_zero (n : ℕ) : CappedSubsetList.count n 0=1 := by simp [CappedSubsetList.count]

theorem count_succ (n r : ℕ) : CappedSubsetList.count n (r+1)=CappedSubsetList.count n r+n.choose (r+1) := by
  simp only [CappedSubsetList.count,Finset.sum_range_succ]

theorem count_zero_left (r : ℕ) : CappedSubsetList.count 0 r=1 := by
  induction r with
  | zero => exact count_zero 0
  | succ r ih => rw [count_succ,ih]; simp

theorem count_pascal (n r : ℕ) :
    CappedSubsetList.count (n+1) (r+1)=CappedSubsetList.count n (r+1)+CappedSubsetList.count n r := by
  induction r with
  | zero => simp [count_succ,count_zero,Nat.choose_succ_succ]; omega
  | succ r ih =>
    rw [count_succ,ih,Nat.choose_succ_succ,count_succ n (r+1),count_succ n r]
    simp only [Nat.succ_eq_add_one]
    omega

theorem count_le_power (n r : ℕ) : CappedSubsetList.count n r ≤ 2^n := by
  rw [← CappedSubsetList.generate_length,← List.toFinset_card_of_nodup (CappedSubsetList.generate_nodup n r)]
  exact (Finset.card_le_univ _).trans_eq (by simp)

def initial (K : ℕ) : Run (Row K) := ⟨Vector.replicate (K+1) BinaryControllerExecution.one,0,8*(K+1)+8⟩

def next {K : ℕ} (row : Row K) : Run (Row K) :=
  tabulate row (fun j =>
    if hj : j.val=0 then
      let out := BinaryControllerExecution.copy (row.get j)
      ⟨out.value,out.bitSteps,8⟩
    else
      let out := BinaryControllerExecution.add (row.get j) (row.get ⟨j.val-1,by omega⟩)
      ⟨out.value,out.bitSteps,16⟩)

theorem next_value {K n : ℕ} (row : Row K)
    (hr : ∀ j, nview (row.get j)=CappedSubsetList.count n j.val) (j : Fin (K+1)) :
    nview ((next row).value.get j)=CappedSubsetList.count (n+1) j.val := by
  simp only [next,tabulate_get]
  split_ifs with hj
  · rw [BinaryControllerExecution.copy_nview,hr,hj,count_zero,count_zero]
  · rw [BinaryControllerExecution.add_nview,hr,hr]
    obtain ⟨r,heq⟩ := Nat.exists_eq_succ_of_ne_zero hj
    change CappedSubsetList.count n j.val + CappedSubsetList.count n (j.val-1) = _
    simp only [heq,Nat.succ_eq_add_one,Nat.add_sub_cancel,count_pascal]

/-- All previously computed rows remain in this finite retained tree. -/
def History (K : ℕ) : ℕ → Type
  | 0 => Row K
  | n+1 => History K n × Row K

def current {K : ℕ} : {n : ℕ} → History K n → Row K
  | 0,row => row
  | _+1,rows => rows.2

def build (K : ℕ) : (n : ℕ) → Run (History K n)
  | 0 => initial K
  | n+1 =>
      let rows := build K n
      let out := next (current rows.value)
      ⟨(rows.value,out.value),rows.bitSteps+out.bitSteps,rows.control+out.control+8⟩

theorem build_value (K n : ℕ) (j : Fin (K+1)) :
    nview ((current (build K n).value).get j)=CappedSubsetList.count n j.val := by
  induction n generalizing j with
  | zero => simp [build,current,initial,BinaryControllerExecution.one_nview,count_zero_left]
  | succ n ih => exact next_value _ ih j

theorem build_width (K n : ℕ) (j : Fin (K+1)) :
    (nview ((current (build K n).value).get j)).size ≤ n+1 := by
  rw [build_value]
  simpa only [Nat.size_pow] using Nat.size_le_size (count_le_power n j.val)

theorem next_bits {K B : ℕ} (row : Row K) (hr : ∀ j, (nview (row.get j)).size ≤ B) :
    (next row).bitSteps ≤ (K+1)*BackendScalarBits.backendScalarUnit B := by
  apply tabulate_bits
  intro j
  split_ifs
  · exact BinaryControllerExecution.copy_price B _ (hr j)
  · exact BinaryControllerExecution.add_price B _ _ (hr j) (hr _)

theorem next_control {K : ℕ} (row : Row K) : (next row).control ≤ 48*(K+1)+8 := by
  have h := tabulate_control row (fun j =>
    if hj : j.val=0 then
      let out := BinaryControllerExecution.copy (row.get j)
      (⟨out.value,out.bitSteps,8⟩ : Run NatCell)
    else
      let out := BinaryControllerExecution.add (row.get j) (row.get ⟨j.val-1,by omega⟩)
      (⟨out.value,out.bitSteps,16⟩ : Run NatCell)) (W:=16) (by intro j; split_ifs <;> simp)
  simpa only [next,Nat.mul_comm] using h

theorem build_bits (K n : ℕ) (hn : n ≤ K) :
    (build K n).bitSteps ≤ n*(K+1)*BackendScalarBits.backendScalarUnit (K+1) := by
  induction n with
  | zero => simp [build,initial]
  | succ n ih =>
    have hb := next_bits (current (build K n).value) (B:=K+1)
      (fun j => (build_width K n j).trans (by omega))
    have hi := ih (by omega)
    simp only [build]
    nlinarith

theorem build_control (K n : ℕ) : (build K n).control ≤ (n+1)*(64*(K+1)+16) := by
  induction n with
  | zero => simp [build,initial]; omega
  | succ n ih =>
    have hn := next_control (current (build K n).value)
    simp only [build]
    nlinarith

/-- Exact retained cardinality, including every predecessor row. -/
def cells (K : ℕ) : (n : ℕ) → History K n → ℕ
  | 0,_ => K+1
  | n+1,rows => cells K n rows.1+(K+1)

theorem retained_cells (K n : ℕ) : cells K n (build K n).value=(n+1)*(K+1) := by
  induction n with
  | zero => simp [cells]
  | succ n ih => simp only [cells,build,ih]; ring

#print axioms count_zero
#print axioms count_succ
#print axioms count_zero_left
#print axioms count_pascal
#print axioms count_le_power
#print axioms next_value
#print axioms build_value
#print axioms build_width
#print axioms next_bits
#print axioms next_control
#print axioms build_bits
#print axioms build_control
#print axioms retained_cells
end ThinMatrix.HalfSourcePascal
