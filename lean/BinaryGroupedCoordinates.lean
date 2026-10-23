import PreparedGroupedProgram
import BinaryModularCell
import BinarySourceFormation

set_option autoImplicit false

/-! Binary ternary-address construction. Coefficient/address bit operations
and Boolean/indexed-control annotations remain separate counters. The scan
never converts semantic integers back to bits; decoding the final nonnegative
address is a charged boundary traversal. -/
namespace ThinMatrix.BinaryGroupedCoordinates
open BinaryCell CappedBitPreparation GroupedPreparation
open scoped BigOperators

structure Run (A : Type) where
  value : A
  bitSteps : ℕ
  control : ℕ

structure Position where
  cell : Cell
  negative : Bool

structure Located where
  index : ℕ
  negative : Bool

def three : Cell := ⟨⟨false,[true,true]⟩,by decide⟩
def digitCell (p k : Bool) : Cell :=
  if k then ⟨⟨false,[false,true]⟩,by decide⟩
  else if p then ⟨⟨false,[true]⟩,by decide⟩ else zero

@[simp] theorem three_view : view three = 3 := rfl
@[simp] theorem digitCell_view (p k : Bool) :
    view (digitCell p k) = (GroupedCoordinates.digit p k : ℤ) := by
  cases p <;> cases k <;> rfl

theorem digitCell_width (p k : Bool) : (view (digitCell p k)).natAbs.size ≤ 2 := by
  cases p <;> cases k <;> decide

def scan : List (Bool × Bool) → Run Position
  | [] => ⟨⟨zero,false⟩,0,2⟩
  | (p,k)::xs =>
      let rest := scan xs
      let tripled := mul three rest.value.cell
      let added := add (digitCell p k) tripled.value
      ⟨⟨added.value,Bool.xor (p && k) rest.value.negative⟩,
        rest.bitSteps+tripled.bitSteps+added.bitSteps,rest.control+12⟩

theorem scan_view (xs : List (Bool × Bool)) :
    view (scan xs).value.cell = (GroupedCoordinates.scan xs).index := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rcases x with ⟨p,k⟩
    simp only [scan,add_view,mul_view,three_view,digitCell_view,ih,GroupedCoordinates.scan]
    norm_cast

theorem scan_negative (xs : List (Bool × Bool)) :
    (scan xs).value.negative = (GroupedCoordinates.scan xs).negative := by
  induction xs with
  | nil => rfl
  | cons x xs ih => rcases x with ⟨p,k⟩; simp only [scan,GroupedCoordinates.scan,ih]

theorem scan_control (xs : List (Bool × Bool)) : (scan xs).control = 12*xs.length+2 := by
  induction xs with
  | nil => rfl
  | cons x xs ih => rcases x with ⟨p,k⟩; simp only [scan,ih,List.length_cons]; omega

theorem ternary_width (a N : ℕ) (ha : a < 3^N) : a.size ≤ 2*N+2 := by
  have hp : 3^N ≤ 2^(2*N) := by
    calc
      _ ≤ 4^N := Nat.pow_le_pow_left (by decide) _
      _ = _ := by rw [pow_mul]; norm_num
  have h := Nat.size_le.mpr (ha.trans_le hp)
  omega

theorem scan_width (xs : List (Bool × Bool)) (N : ℕ) (h : xs.length ≤ N) :
    (view (scan xs).value.cell).natAbs.size ≤ 2*N+2 := by
  rw [scan_view,Int.natAbs_natCast]
  exact ternary_width _ N ((GroupedCoordinates.scan_index_lt xs).trans_le
    (Nat.pow_le_pow_right (by decide) h))

theorem tripled_width (xs : List (Bool × Bool)) (N : ℕ) (h : xs.length+1 ≤ N) :
    (view (mul three (scan xs).value.cell).value).natAbs.size ≤ 2*N+2 := by
  rw [mul_view,three_view,scan_view]
  have he : (3*(GroupedCoordinates.scan xs).index : ℤ) =
      ((3*(GroupedCoordinates.scan xs).index : ℕ) : ℤ) := by push_cast; rfl
  rw [he,Int.natAbs_natCast]
  apply ternary_width _ N
  calc
    _ < 3*3^xs.length := Nat.mul_lt_mul_of_pos_left (GroupedCoordinates.scan_index_lt xs) (by decide)
    _ = 3^(xs.length+1) := (pow_succ' _ _).symm
    _ ≤ _ := Nat.pow_le_pow_right (by decide) h

theorem scan_bits (xs : List (Bool × Bool)) (N : ℕ) (hlen : xs.length ≤ N) :
    (scan xs).bitSteps ≤ xs.length*(2*BackendScalarBits.backendScalarUnit (2*N+2)) := by
  induction xs with
  | nil => simp [scan]
  | cons x xs ih =>
    rcases x with ⟨p,k⟩
    have ht := ih (by simpa only [List.length_cons] using Nat.le_of_succ_le hlen)
    have hw := scan_width xs N (by simp only [List.length_cons] at hlen; omega)
    have hm := mul_price (2*N+2) three (scan xs).value.cell
      (by
        have hc : (view three).natAbs.size = 2 := by decide
        rw [hc]
        omega) hw
    have ha := add_price (2*N+2) (digitCell p k) (mul three (scan xs).value.cell).value
      ((digitCell_width p k).trans (by omega))
      (tripled_width xs N (by simpa only [List.length_cons] using hlen))
    simp only [scan,List.length_cons]
    nlinarith

def locate {n : ℕ} (p k : Key n) : Run Located :=
  let out := scan (List.ofFn (fun i => (p.get i,k.get i)))
  let decoded := BinaryModularCell.decodeUnsigned out.value.cell
  ⟨⟨decoded.value,out.value.negative⟩,out.bitSteps+decoded.bitSteps+16,out.control+16*n+8⟩

theorem locate_index {n : ℕ} (p k : Key n) : (locate p k).value.index = (GroupedCoordinates.coordinates p k).index := by
  simp only [locate,BinaryModularCell.decodeUnsigned_value,scan_view,Int.natAbs_natCast,
    GroupedCoordinates.coordinates]

theorem locate_negative {n : ℕ} (p k : Key n) :
    (locate p k).value.negative = (GroupedCoordinates.coordinates p k).negative := by
  simp only [locate,scan_negative,GroupedCoordinates.coordinates]

theorem locate_lt {n : ℕ} (p k : Key n) : (locate p k).value.index < 3^n := by
  rw [locate_index]
  exact GroupedCoordinates.coordinates_lt p k

def addressBudget (n : ℕ) : ℕ := n*(2*BackendScalarBits.backendScalarUnit (2*n+2))+8*(2*n+3)^2+16

theorem locate_bits {n : ℕ} (p k : Key n) : (locate p k).bitSteps ≤ addressBudget n := by
  have hs := scan_bits (List.ofFn (fun i => (p.get i,k.get i))) n (by simp)
  have hd := BinaryModularCell.decodeUnsigned_price (2*n+2)
    (scan (List.ofFn (fun i => (p.get i,k.get i)))).value.cell (scan_width _ n (by simp))
  simp only [List.length_ofFn] at hs
  rw [show 2*n+2+1 = 2*n+3 by omega] at hd
  simp only [locate,addressBudget]
  omega

theorem locate_control {n : ℕ} (p k : Key n) : (locate p k).control = 28*n+10 := by
  simp only [locate,scan_control,List.length_ofFn]
  omega

#print axioms three_view
#print axioms digitCell_view
#print axioms digitCell_width
#print axioms scan_view
#print axioms scan_negative
#print axioms scan_control
#print axioms ternary_width
#print axioms scan_width
#print axioms tripled_width
#print axioms scan_bits
#print axioms locate_index
#print axioms locate_negative
#print axioms locate_lt
#print axioms locate_bits
#print axioms locate_control
end ThinMatrix.BinaryGroupedCoordinates
