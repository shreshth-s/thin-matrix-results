import HalfSourceSuffixChoice
import ParameterExecution

set_option autoImplicit false
set_option maxHeartbeats 1800000

/-! Shared support-cap setup through the existing binary power/root circuits.
The exact root scan costs O(4^m poly(m+size(k))); it runs once per public shape,
not once per root, query or block. The returned integer is the exact cap used
by the suffix selector. No logarithm or real-root oracle occurs at runtime. -/
namespace ThinMatrix.HalfSourceCapSetup
open ParameterExecution

def dimension (m : ℕ) : Run Word := power (input 4) m

theorem dimension_value (m : ℕ) : (dimension m).value.view=4^m := by simp [dimension]

def root (m : ℕ) : Run Word :=
  let d := dimension m
  let size := decode d.value
  let root := rootLoop 11 50 d.value (size.value+1) (input 0)
  ⟨root.value,d.bitSteps+size.bitSteps+root.bitSteps+8⟩

theorem root_value (m : ℕ) : (root m).value.view=ComputableParameters.rootScan 11 50 (4^m) := by
  simp only [root,rootLoop_view,decode_value,dimension_value,input_view]
  rw [rootSpec_scan,←List.range_eq_range']
  exact ComputableParameters.rootProgram_value 11 50 (4^m)

def execute (m k : ℕ) : Run ℕ :=
  let r := root m
  let rounded := add r.value (input 1)
  let factor := serialize (k+1)
  let cap := mul factor.value rounded.value
  let out := decode cap.value
  ⟨out.value,r.bitSteps+rounded.bitSteps+factor.bitSteps+cap.bitSteps+out.bitSteps+16⟩

theorem execute_value (m k : ℕ) : (execute m k).value=HalfSourceSuffixChoice.limit m k := by
  simp only [execute,decode_value,mul_view,add_view,root_value,input_view,serialize_eq_input,
    HalfSourceSuffixChoice.limit,ComputableParameters.roundedPower]

def width (m k : ℕ) : ℕ := 63*(2*m+3)+k.size+10

theorem four_size (m : ℕ) : (4^m).size=2*m+1 := by
  rw [show (4:ℕ)=2^2 by decide,←pow_mul,Nat.size_pow]

theorem dimension_price (m k : ℕ) :
    (dimension m).bitSteps ≤ m*(unit (width m k)+1)+1 := by
  apply power_price
  · simp only [input_view]
    change 3  ≤  width m k
    unfold width
    omega
  · intro j hj
    rw [input_view,four_size]
    unfold width
    omega

theorem root_loop_price (m k : ℕ) :
    (rootLoop 11 50 (dimension m).value ((decode (dimension m).value).value+1) (input 0)).bitSteps  ≤ 
      (4^m+2)*71*(unit (width m k)+1) := by
  have hf : ∀ z  ≤  4^m+1, z.size ≤ width m k := by
    intro z hz
    have hs := (Nat.size_le_size hz).trans (size_succ (4^m))
    rw [four_size] at hs
    unfold width
    omega
  have hp : ∀ z  ≤  4^m+1, ∀ j  ≤  11+50+1, (z^j).size ≤ width m k := by
    intro z hz j hj
    have hs := (Nat.size_le_size hz).trans (size_succ (4^m))
    rw [four_size] at hs
    have hw := size_pow z j
    have hm := Nat.mul_le_mul hj hs
    unfold width
    nlinarith
  have hr := rootLoop_price (width m k) (4^m+1) 11 50 (4^m+1) (dimension m).value (input 0)
    (by exact Nat.succ_pos _) (by rw [dimension_value]; exact Nat.le_succ _) (by simp) hf hp
  simpa only [decode_value,dimension_value,show 11+50+10=71 by decide,Nat.add_assoc,show 1+1=2 by decide] using hr

theorem root_price (m k : ℕ) :
    (root m).bitSteps  ≤  (m+1+(4^m+2)*71)*(unit (width m k)+1)+9 := by
  have hd := dimension_price m k
  have he := decode_price (width m k) (dimension m).value (by rw [dimension_value,four_size]; unfold width; omega)
  have hr := root_loop_price m k
  unfold root
  nlinarith

theorem rounded_width (m k : ℕ) :
    (add (root m).value (input 1)).value.view.size  ≤  width m k := by
  rw [add_view,root_value,input_view]
  have hr := ParameterExecution.rootScan_le 11 50 (4^m)
  have hh := (Nat.size_le_size (Nat.add_le_add_right hr 1)).trans (size_succ (4^m))
  rw [four_size] at hh
  unfold width
  omega

def bitBudget (m k : ℕ) : ℕ := (m+5+(4^m+2)*71)*(unit (width m k)+1)+25

theorem execute_bits (m k : ℕ) : (execute m k).bitSteps  ≤  bitBudget m k := by
  have hr := root_price m k
  have hrw : (root m).value.view.size  ≤  width m k := by
    rw [root_value]
    have hh := Nat.size_le_size (ParameterExecution.rootScan_le 11 50 (4^m))
    rw [four_size] at hh
    unfold width
    omega
  have ha := add_price (width m k) (root m).value (input 1) hrw (by simp only [input_view]; change 1 ≤ width m k; unfold width; omega)
  have hf := serialize_price (width m k) (k+1) ((size_succ k).trans (by unfold width; omega))
  have hfw : (serialize (k+1)).value.view.size ≤ width m k := by
    rw [serialize_eq_input,input_view]
    exact (size_succ k).trans (by unfold width; omega)
  have hm := mul_price (width m k) (serialize (k+1)).value (add (root m).value (input 1)).value hfw (rounded_width m k)
  have hout : (mul (serialize (k+1)).value (add (root m).value (input 1)).value).value.view.size  ≤  width m k := by
    rw [mul_view,serialize_eq_input,input_view,add_view,root_value,input_view]
    have hr := ParameterExecution.rootScan_le 11 50 (4^m)
    have hs := (Nat.size_le_size (Nat.add_le_add_right hr 1)).trans (size_succ (4^m))
    rw [four_size] at hs
    have hk := size_succ k
    have hh := size_mul (k+1) (ComputableParameters.rootScan 11 50 (4^m)+1)
    unfold width
    omega
  have hd := decode_price (width m k) _ hout
  unfold execute bitBudget
  nlinarith

#print axioms dimension_value
#print axioms root_value
#print axioms execute_value
#print axioms four_size
#print axioms dimension_price
#print axioms root_loop_price
#print axioms root_price
#print axioms rounded_width
#print axioms execute_bits
end ThinMatrix.HalfSourceCapSetup
