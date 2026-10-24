import ComputableParameters
import ParameterExecution
import SharedCompletionRate

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option exponentiation.threshold 2048
namespace ThinMatrix.SharedCompletionTile
open ParameterExecution

def row (s : ℕ) := ComputableParameters.roundedPower 861 1000 (s^2)
def col (s : ℕ) := s^15

def execute (s : ℕ) : Run (ℕ×ℕ) :=
  let x := serialize s
  let sq := power x.value 2
  let size := decode sq.value
  let rt := rootLoop 861 1000 sq.value (size.value+1) (input 0)
  let rounded := add rt.value (input 1)
  let last := power x.value 15
  let a := decode rounded.value
  let z := decode last.value
  ⟨(a.value,z.value),x.bitSteps+sq.bitSteps+size.bitSteps+rt.bitSteps+
    rounded.bitSteps+last.bitSteps+a.bitSteps+z.bitSteps+16⟩

theorem root_value (s : ℕ) :
    (rootLoop 861 1000 (power (serialize s).value 2).value
      ((decode (power (serialize s).value 2).value).value+1) (input 0)).value.view=
      ComputableParameters.rootScan 861 1000 (s^2) := by
  simp only [rootLoop_view,decode_value,power_view,serialize_eq_input,input_view]
  rw [rootSpec_scan,←List.range_eq_range']
  exact ComputableParameters.rootProgram_value 861 1000 (s^2)

theorem execute_value (s : ℕ) : (execute s).value=(row s,col s) := by
  have hv := root_value s
  simp only [decode_value,power_view,serialize_eq_input,input_view] at hv
  simp only [execute,decode_value,add_view,input_view,power_view,serialize_eq_input,
    hv,row,col,ComputableParameters.roundedPower]

theorem row_bounds (s : ℕ) (hs : 1 ≤ s) :
    (s:ℝ)^SharedCompletionRate.a ≤ (row s:ℝ) ∧
      (row s:ℝ) ≤ 2*(s:ℝ)^SharedCompletionRate.a := by
  have hh := ComputableParameters.roundedPower_bounds 861 1000 (s^2) (by decide) (by decide) (one_le_pow₀ hs)
  have he : ((s^2:ℕ):ℝ)^((861:ℝ)/1000)=(s:ℝ)^SharedCompletionRate.a := by
    push_cast
    rw [←Real.rpow_natCast_mul (by positivity)]
    congr 1
    norm_num [SharedCompletionRate.a]
  norm_num only [Nat.cast_ofNat] at hh
  simpa only [row,he] using hh

theorem integer_fit (s : ℕ) (hs : 1 ≤ s) : (row s-1)^500 ≤ s^861 := by
  have hr := Nat.pow_nthRoot_le (n:=1000) (a:=(s^2)^861) (Or.inl (by decide : (1000:ℕ)≠0))
  rw [←ComputableParameters.rootScan_eq_nthRoot 861 1000 (s^2) (by omega) (by omega) (one_le_pow₀ hs)] at hr
  have hh : ((row s-1)^500)^2 ≤ (s^861)^2 := by
    simpa only [row,ComputableParameters.roundedPower,Nat.add_sub_cancel,←pow_mul,
      show 500*2=1000 by decide,show 2*861=861*2 by decide] using hr
  exact (Nat.pow_le_pow_iff_left (by decide : (2:ℕ)≠0)).mp hh

theorem dimensions (s : ℕ) (hs : 1 ≤ s) :
    0 < row s ∧ 0 < col s ∧ s ≤ row s ∧ s ≤ col s := by
  have hr := (row_bounds s hs).1
  have hsr : (s:ℝ) ≤ (s:ℝ)^SharedCompletionRate.a := by
    conv_lhs => rw [←Real.rpow_one (s:ℝ)]
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hs) (by norm_num [SharedCompletionRate.a])
  have hra : s ≤ row s := by exact_mod_cast hsr.trans hr
  have hc : s ≤ s^15 := by simpa using Nat.pow_le_pow_right hs (by decide : 1 ≤ 15)
  exact ⟨by omega,by dsimp [col];omega,hra,hc⟩

def width (s : ℕ) := 4000*(s.size+2)
def bitBudget (s : ℕ) := 1900*(s^2+2)*(unit (width s)+1)

theorem root_price (s : ℕ) :
    (rootLoop 861 1000 (power (serialize s).value 2).value
      ((decode (power (serialize s).value 2).value).value+1) (input 0)).bitSteps ≤
      (s^2+2)*1871*(unit (width s)+1) := by
  have hf : ∀ z ≤ s^2+1,z.size ≤ width s := by
    intro z hz
    have hh := (Nat.size_le_size hz).trans (size_succ (s^2))
    have hp := size_pow s 2
    unfold width
    omega
  have hp : ∀ z ≤ s^2+1,∀ j ≤ 861+1000+1,(z^j).size ≤ width s := by
    intro z hz j hj
    have hh := (Nat.size_le_size hz).trans (size_succ (s^2))
    have hs := size_pow s 2
    have hw := size_pow z j
    have hm := Nat.mul_le_mul hj hh
    unfold width
    nlinarith
  have hr := rootLoop_price (width s) (s^2+1) 861 1000 (s^2+1)
    (power (serialize s).value 2).value (input 0) (by omega)
    (by simp only [power_view,serialize_eq_input,input_view];omega) (by simp) hf hp
  simpa only [decode_value,power_view,serialize_eq_input,input_view,
    show 861+1000+10=1871 by decide,Nat.add_assoc,show 1+1=2 by decide] using hr

theorem execute_bits (s : ℕ) : (execute s).bitSteps ≤ bitBudget s := by
  have hs : s.size ≤ width s := by unfold width;omega
  have hx := serialize_price (width s) s hs
  have hxw : (serialize s).value.view.size ≤ width s := by simpa only [serialize_eq_input,input_view] using hs
  have hp : ∀ j ≤ 15,(s^j).size ≤ width s := by
    intro j hj
    have hh := size_pow s j
    have hm := Nat.mul_le_mul_right s.size hj
    unfold width
    omega
  have hsq := power_price (width s) (serialize s).value 2 hxw
    (by intro j hj;simpa only [serialize_eq_input,input_view] using hp j (by omega))
  have hlast := power_price (width s) (serialize s).value 15 hxw
    (by intro j hj;simpa only [serialize_eq_input,input_view] using hp j hj)
  have hsqd := decode_price (width s) (power (serialize s).value 2).value (by simpa only [power_view,serialize_eq_input,input_view] using hp 2 (by decide))
  have hrt := root_price s
  have hrootw : (ComputableParameters.rootScan 861 1000 (s^2)).size ≤ width s := by
    have hh := Nat.size_le_size (ParameterExecution.rootScan_le 861 1000 (s^2))
    exact hh.trans (hp 2 (by decide))
  have hrounded : (ComputableParameters.rootScan 861 1000 (s^2)+1).size ≤ width s := by
    have hh := (Nat.size_le_size (Nat.add_le_add_right (ParameterExecution.rootScan_le 861 1000 (s^2)) 1)).trans (size_succ (s^2))
    have hs' := size_pow s 2
    unfold width
    omega
  have hadd := add_price (width s)
    (rootLoop 861 1000 (power (serialize s).value 2).value
      ((decode (power (serialize s).value 2).value).value+1) (input 0)).value (input 1)
    (by rw [root_value];exact hrootw) (by simp only [input_view];change 1 ≤ width s;unfold width;omega)
  have ha := decode_price (width s) (add
    (rootLoop 861 1000 (power (serialize s).value 2).value
      ((decode (power (serialize s).value 2).value).value+1) (input 0)).value (input 1)).value (by
    rw [add_view,root_value,input_view]
    exact hrounded)
  have hz := decode_price (width s) (power (serialize s).value 15).value (by simpa only [power_view,serialize_eq_input,input_view] using hp 15 (by decide))
  unfold execute bitBudget
  nlinarith


theorem setup_absorbed (s Q : ℕ) (hs : 1 ≤ s) (hfit : col s ≤ Q) :
    (execute s).bitSteps ≤ 1000000000000000*Q*(s.size+2)^2 := by
  have h1 : 1 ≤ s^2 := one_le_pow₀ hs
  have hsq : s^2 ≤ Q := (Nat.pow_le_pow_right hs (by decide : 2 ≤ 15)).trans hfit
  have hb : s^2+2 ≤ 3*Q := by omega
  have hw : width s+1 ≤ 4001*(s.size+2) := by unfold width;omega
  have hp := Nat.pow_le_pow_left hw 2
  have hpoly : 1 ≤ (s.size+2)^2 := one_le_pow₀ (by omega)
  have hunit : unit (width s)+1 ≤ 16024010001*(s.size+2)^2 := by
    unfold unit
    nlinarith
  have hh := Nat.mul_le_mul hb hunit
  apply (execute_bits s).trans
  unfold bitBudget
  nlinarith

#print axioms setup_absorbed
#print axioms root_value
#print axioms execute_value
#print axioms row_bounds
#print axioms integer_fit
#print axioms dimensions
#print axioms root_price
#print axioms execute_bits
end ThinMatrix.SharedCompletionTile
