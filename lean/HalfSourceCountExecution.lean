import ExactHalfSourcePlan
import ParameterExecution

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-! Binary execution of the public translation-list cardinality. No list
construction is used to decode a translation family index. -/
namespace ThinMatrix.HalfSourceCountExecution
open ParameterExecution

def width (m : ℕ) : ℕ := 3*m.size+8

/-- Both fixed multipliers and the branch are explicit; the result is decoded
only after all binary arithmetic has been charged. -/
def execute (m : Word) : Run ℕ :=
  let zero := isZero m.bits
  let cubed := power m 3
  let scaled := mul (input 64) cubed.value
  let chosen := if zero.value then input 1 else scaled.value
  let decoded := decode chosen
  ⟨decoded.value,zero.bitSteps+cubed.bitSteps+scaled.bitSteps+decoded.bitSteps+128⟩

theorem value (m : Word) : (execute m).value=ExactHalfSourcePlan.count m.view := by
  simp only [execute,decode_value,ExactHalfSourcePlan.count]
  split <;> rename_i h
  · have hz : m.view=0 := (isZero_view m.bits).mp h
    simp only [hz,ite_true,input_view]
  · have hz : m.view≠0 := by
      intro he
      exact h ((isZero_view m.bits).mpr he)
    simp only [hz,ite_false,mul_view,input_view,power_view]

theorem count_width (m : ℕ) : (ExactHalfSourcePlan.count m).size≤width m := by
  unfold ExactHalfSourcePlan.count
  split
  · simp only [width]; change 1 ≤ _; omega
  · have hs := size_mul 64 (m^3)
    have hp := size_pow m 3
    have h64 : (64:ℕ).size=7 := by decide
    rw [h64] at hs
    unfold width
    omega

theorem price (m : Word) : (execute m).bitSteps≤500000*(m.view.size+1)^2 := by
  let B := width m.view
  have hm : m.view.size≤B := by unfold B width;omega
  have h64 : (64:ℕ).size≤B := by
    have hh : (64:ℕ).size=7 := by decide
    unfold B width
    omega
  have hp (j : ℕ) (hj : j≤3) : (m.view^j).size≤B := by
    have hs := size_pow m.view j
    have hm := Nat.mul_le_mul_right m.view.size hj
    unfold B width
    omega
  have hc := power_price B m 3 hm hp
  have hs := mul_price B (input 64) (power m 3).value
    (by simpa only [input_view] using h64) (by simpa only [power_view] using hp 3 (by omega))
  have hchosen : (if (isZero m.bits).value then input 1 else
      (mul (input 64) (power m 3).value).value).view.size≤B := by
    split
    · simp only [input_view];unfold B width;change 1 ≤ _;omega
    · simp only [mul_view,input_view,power_view]
      have hh := size_mul 64 (m.view^3)
      have hh2 := size_pow m.view 3
      have he : (64:ℕ).size=7 := by decide
      rw [he] at hh
      unfold B width
      omega
  have hd := decode_price B _ hchosen
  simp only [execute,isZero_steps,word_width]
  unfold unit B width at hc hs hd
  nlinarith

#print axioms value
#print axioms count_width
#print axioms price
end ThinMatrix.HalfSourceCountExecution
