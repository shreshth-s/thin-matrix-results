import SharedFullyPrefixPrices
import SharedCompletionRate

set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace ThinMatrix.RootCompletionRate
open SharedFullyPrefixPrices

theorem root_extra_bound (W M Q : ℕ) (hQ : 1 ≤ Q) :
    rootExtra W M Q ≤ 256*(W+1)*Q*(M+1) := by
  have hMW := Nat.mul_le_mul_left (M*W) hQ
  have hM := Nat.mul_le_mul_left M hQ
  have hW := Nat.mul_le_mul_left W hQ
  unfold rootExtra
  nlinarith

theorem sum_width (W D H L : ℕ) (h : W.size+D.size+H.size+1 ≤ L) :
    (W*(D*H)).size+1 ≤ L := by
  have h1 := BinaryMultiplierAdapter.size_mul W (D*H)
  have h2 := BinaryMultiplierAdapter.size_mul D H
  omega

theorem scalar_budget (W D H M Q L : ℕ) (h : W.size+D.size+H.size+1 ≤ L) :
    M*(W*(Q*BackendScalarBits.backendScalarUnit (W*(D*H)).size)) ≤
      800*W*L^2*M*Q := by
  have hs := sum_width W D H L h
  have hh := Nat.pow_le_pow_left hs 2
  unfold BackendScalarBits.backendScalarUnit BackendScalarBits.scalarUnit
  nlinarith [Nat.mul_le_mul_left (M*W*Q) hh]

theorem extras (W D H M G Q L price : ℕ) (hW : 1 ≤ W) (hG : 1 ≤ G)
    (hQ : 1 ≤ Q) (hL : 1 ≤ L) (hw : W.size+D.size+H.size+1 ≤ L) :
    M*(W*(Q*BackendScalarBits.backendScalarUnit (W*(D*H)).size))+price*rootExtra W M Q ≤
      2000*(price+1)*W*L^2*Q*(M+G) := by
  have hs := scalar_budget W D H M Q L hw
  have he := root_extra_bound W M Q hQ
  have hWM : (W+1)*(M+1) ≤ 2*W*(M+G) := Nat.mul_le_mul (by omega) (by omega)
  have he' : rootExtra W M Q ≤ 512*W*Q*(M+G) := by
    nlinarith [Nat.mul_le_mul_right (256*Q) hWM]
  have hp := Nat.mul_le_mul_left price he'
  have hL2 : 1 ≤ L^2 := one_le_pow₀ hL
  have hbase := Nat.mul_le_mul_left (512*price*W*Q*(M+G)) hL2
  have hplus : M ≤ M+G := Nat.le_add_right _ _
  have hsum := Nat.mul_le_mul_left (800*W*L^2*Q) hplus
  nlinarith

theorem extras_rate (s : ℝ) (W D H M G Q L price : ℕ) (hs : 1 ≤ s)
    (hW : 1 ≤ W) (hG : 1 ≤ G) (hQ : 1 ≤ Q) (hL : 1 ≤ L)
    (hw : W.size+D.size+H.size+1 ≤ L) :
    (M*(W*(Q*BackendScalarBits.backendScalarUnit (W*(D*H)).size))+price*rootExtra W M Q:ℝ) ≤
      2000*(price+1)*W*(L:ℝ)^5*((M:ℝ)*Q*s^SharedCompletionRate.beta+
        (G:ℝ)*Q*s^SharedCompletionRate.gamma) := by
  have hn := extras W D H M G Q L price hW hG hQ hL hw
  have hNR : (M*(W*(Q*BackendScalarBits.backendScalarUnit (W*(D*H)).size))+price*rootExtra W M Q:ℝ) ≤
      2000*((price:ℝ)+1)*W*(L:ℝ)^2*Q*((M:ℝ)+G) := by exact_mod_cast hn
  have hb : 1 ≤ s^SharedCompletionRate.beta := Real.one_le_rpow hs (by norm_num [SharedCompletionRate.beta])
  have hg : 1 ≤ s^SharedCompletionRate.gamma := Real.one_le_rpow hs (by norm_num [SharedCompletionRate.gamma])
  have hm' := mul_le_mul_of_nonneg_left hb (show 0 ≤ (M:ℝ)*Q by positivity)
  have hg' := mul_le_mul_of_nonneg_left hg (show 0 ≤ (G:ℝ)*Q by positivity)
  have htar : (Q:ℝ)*(M+G) ≤ (M:ℝ)*Q*s^SharedCompletionRate.beta+(G:ℝ)*Q*s^SharedCompletionRate.gamma := by nlinarith
  have hl : (L:ℝ)^2 ≤ (L:ℝ)^5 := pow_le_pow_right₀ (by exact_mod_cast hL) (by decide)
  have hh := mul_le_mul hl htar (by positivity) (by positivity)
  have hx := mul_le_mul_of_nonneg_left hh (show 0 ≤ (2000:ℝ)*(price+1)*W by positivity)
  nlinarith

#print axioms root_extra_bound
#print axioms sum_width
#print axioms scalar_budget
#print axioms extras
#print axioms extras_rate
end ThinMatrix.RootCompletionRate
