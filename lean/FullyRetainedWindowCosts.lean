import FullyRetainedWindowBatch
import SharedCompletionRate

set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace ThinMatrix.FullyRetainedWindowCosts
open BinaryCell BinaryGroupedCoordinates
open RectangularBatch (Scheme)
variable {k ell total cn co C B A Z : ℕ}

def overhead (k P ell M Q : ℕ) :=
  M*(48*k+56)+8+12*2^(P+(P+ell))+
  M*(16*(P+(P+ell)+1)^2+64*(P+ell+1)+36)+36+
  128*M+32*2^ell*(4^P+1)+32*Q+52+16

theorem control (scheme : Scheme) (hD : 0 < WindowSharedCompletion.D k ell total cn co)
    (hA : 0 < A) (hZ : 0 < Z)
    (hf : (A-1)^scheme.den ≤ (WindowSharedCompletion.D k ell total cn co)^scheme.num)
    (hl : Z ≤ (WindowSharedCompletion.D k ell total cn co)^scheme.z)
    (xs : Vector (CappedPrefixProgram.Prepared (WindowPrefixProgram.prefixLength k ell)
      (WindowPrefixProgram.length k ell) (WindowPrefixProgram.cap k ell total cn co) C) B)
    (layout : RetainedWindowPermutation.Layout (2*k)) (labels : Array (Vector (Fin 4) (2*k))) :
    (FullyRetainedWindowBatch.execute scheme hD hA hZ hf hl (SharedPrefixSourceBank.prepare xs).value layout labels).control ≤
      (SharedFullyPrefixSchedule.execute scheme hD hA hZ hf hl
        (WindowCompletionRequests.requests ell layout labels).value
        (RoutedPrefixBatch.prepare xs (WindowCompletionRequests.requests ell layout labels).value).value).control+
      overhead k (WindowPrefixProgram.prefixLength k ell) (WindowPrefixProgram.length k ell) labels.size (B*C) := by
  have hr := WindowCompletionRequests.requests_work ell layout labels
  have ht := SharedPrefixSourceBank.route_control (SharedPrefixSourceBank.prepare xs).value
    (WindowCompletionRequests.requests ell layout labels).value
  have hs := SharedFullyPrefixScatter.control scheme hD hA hZ hf hl xs
    (WindowCompletionRequests.requests ell layout labels).value
  simp only [WindowCompletionRequests.requests_size] at ht hs
  simp only [FullyRetainedWindowBatch.execute,SharedPrefixSourceBank.route_value]
  unfold overhead
  omega

theorem overhead_bound (k P ell M Q L : ℕ) (hQ : 1 ≤ Q) (hL : 1 ≤ L)
    (hk : k+1 ≤ L) (hlen : P+ell+1 ≤ L) :
    overhead k P ell M Q ≤ 512*L^2*Q*(M+2^ell*4^P) := by
  have hid : 2^(P+(P+ell))=2^ell*4^P := by
    rw [show (4:ℕ)=2^2 by decide,←pow_mul,←pow_add]
    congr 1
    omega
  have hG : 1 ≤ 2^ell*4^P := Nat.mul_pos (show 1 ≤ 2^ell from one_le_pow₀ (by decide)) (show 1 ≤ 4^P from one_le_pow₀ (by decide))
  have he : 2^ell ≤ 2^ell*4^P := Nat.le_mul_of_pos_right _ (show 1 ≤ 4^P from one_le_pow₀ (by decide))
  have hl : L ≤ L^2 := by nlinarith
  have hpow : 1 ≤ L^2 := one_le_pow₀ hL
  have hk' : 48*k+56 ≤ 56*L^2 := by nlinarith
  have hspan : (P+(P+ell)+1)^2 ≤ 4*L^2 := by
    have hh := Nat.pow_le_pow_left (show P+(P+ell)+1 ≤ 2*L by omega) 2
    nlinarith
  have hr : 16*(P+(P+ell)+1)^2+64*(P+ell+1)+36 ≤ 164*L^2 := by nlinarith
  have hm1 := Nat.mul_le_mul_left M hk'
  have hm2 := Nat.mul_le_mul_left M hr
  have hm3 : M ≤ L^2*Q*M := by
    have hh := Nat.mul_le_mul_right M (Nat.mul_pos hpow hQ)
    simpa using hh
  have hMG : M*L^2 ≤ L^2*Q*M := by nlinarith [Nat.mul_le_mul_right (M*L^2) hQ]
  have hGQ : 2^ell*4^P ≤ L^2*Q*(2^ell*4^P) := Nat.le_mul_of_pos_left _ (Nat.mul_pos hpow hQ)
  have hQG : Q ≤ L^2*Q*(2^ell*4^P) := by nlinarith [Nat.mul_le_mul_left Q (Nat.mul_pos hpow hG)]
  unfold overhead
  rw [hid]
  nlinarith

theorem overhead_rate (s M G Q L price : ℝ) (hs : 1 ≤ s)
    (hM : 0 ≤ M) (hG : 0 ≤ G) (hQ : 0 ≤ Q) (hL : 1 ≤ L) (hp : 0 ≤ price) :
    price*(512*L^2*Q*(M+G)) ≤
      512*(price+1)*L^5*(M*Q*s^SharedCompletionRate.beta+G*Q*s^SharedCompletionRate.gamma) := by
  have hb : 1 ≤ s^SharedCompletionRate.beta := Real.one_le_rpow hs (by norm_num [SharedCompletionRate.beta])
  have hg : 1 ≤ s^SharedCompletionRate.gamma := Real.one_le_rpow hs (by norm_num [SharedCompletionRate.gamma])
  have hmr := mul_le_mul_of_nonneg_left hb (show 0 ≤ M*Q by positivity)
  have hgr := mul_le_mul_of_nonneg_left hg (show 0 ≤ G*Q by positivity)
  have hs' : Q*(M+G) ≤ M*Q*s^SharedCompletionRate.beta+G*Q*s^SharedCompletionRate.gamma := by nlinarith
  have hl : L^2 ≤ L^5 := pow_le_pow_right₀ hL (by decide)
  have hh := mul_le_mul hl hs' (by positivity) (by positivity)
  have hp' := mul_le_mul_of_nonneg_left hh (show 0 ≤ 512*price by positivity)
  have ht : 0 ≤ L^5*(M*Q*s^SharedCompletionRate.beta+G*Q*s^SharedCompletionRate.gamma) :=
    (mul_nonneg (by positivity) ((show 0 ≤ Q*(M+G) by positivity).trans hs'))
  nlinarith


theorem priced_from_schedule (scheme : Scheme) (hD : 0 < WindowSharedCompletion.D k ell total cn co)
    (hA : 0 < A) (hZ : 0 < Z)
    (hf : (A-1)^scheme.den ≤ (WindowSharedCompletion.D k ell total cn co)^scheme.num)
    (hl : Z ≤ (WindowSharedCompletion.D k ell total cn co)^scheme.z)
    (xs : Vector (CappedPrefixProgram.Prepared (WindowPrefixProgram.prefixLength k ell)
      (WindowPrefixProgram.length k ell) (WindowPrefixProgram.cap k ell total cn co) C) B)
    (layout : RetainedWindowPermutation.Layout (2*k)) (labels : Array (Vector (Fin 4) (2*k)))
    (price L : ℕ) (hQ : 1 ≤ B*C) (hL : 1 ≤ L) (hk : k+1 ≤ L)
    (hlen : WindowPrefixProgram.prefixLength k ell+WindowPrefixProgram.length k ell+1 ≤ L) :
    (FullyRetainedWindowBatch.execute scheme hD hA hZ hf hl (SharedPrefixSourceBank.prepare xs).value layout labels).bitSteps+
      price*(FullyRetainedWindowBatch.execute scheme hD hA hZ hf hl (SharedPrefixSourceBank.prepare xs).value layout labels).control ≤
      (SharedFullyPrefixSchedule.execute scheme hD hA hZ hf hl
        (WindowCompletionRequests.requests ell layout labels).value
        (RoutedPrefixBatch.prepare xs (WindowCompletionRequests.requests ell layout labels).value).value).bitSteps+
      price*(SharedFullyPrefixSchedule.execute scheme hD hA hZ hf hl
        (WindowCompletionRequests.requests ell layout labels).value
        (RoutedPrefixBatch.prepare xs (WindowCompletionRequests.requests ell layout labels).value).value).control+
      price*(512*L^2*(B*C)*(labels.size+2^(WindowPrefixProgram.length k ell)*4^(WindowPrefixProgram.prefixLength k ell))) := by
  have hc := control scheme hD hA hZ hf hl xs layout labels
  have ho := overhead_bound k (WindowPrefixProgram.prefixLength k ell)
    (WindowPrefixProgram.length k ell) labels.size (B*C) L hQ hL hk hlen
  have hb := FullyRetainedWindowBatch.bits scheme hD hA hZ hf hl (SharedPrefixSourceBank.prepare xs).value layout labels
  rw [SharedPrefixSourceBank.route_value] at hb
  rw [hb]
  nlinarith

#print axioms priced_from_schedule
#print axioms control
#print axioms overhead_bound
#print axioms overhead_rate
end ThinMatrix.FullyRetainedWindowCosts
