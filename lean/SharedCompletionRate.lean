import SharedCompletionExtras
import ComputableParameters

set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace ThinMatrix.SharedCompletionRate
open scoped BigOperators
open BinaryCell

noncomputable def a : ℝ := 861/500
noncomputable def beta : ℝ := 1/5000000
noncomputable def gamma : ℝ := 861/500+1/5000000

noncomputable def w : ℝ := 83610001/5000000

theorem power_identities {s : ℝ} (hs : 0 < s) :
    s^w=s^beta*s^a*s^(15:ℝ) ∧
    s^w=s^gamma*s^(15:ℝ) := by
  constructor
  · rw [← Real.rpow_add hs,← Real.rpow_add hs]
    congr 1
    norm_num [w,a,beta]
  · rw [← Real.rpow_add hs]
    congr 1
    norm_num [w,gamma]

theorem padded_volume (s M G Q A : ℝ) (hs : 1 ≤ s) (hM : 0 ≤ M) (hG : 0 ≤ G)
    (hQ : 0 ≤ Q) (hA : s^a ≤ A) :
    (M+G*A)*Q*s^CWFiniteBase.exponent ≤
      (M*Q*s^beta+G*Q*s^gamma)*A*s^(15:ℝ) := by
  have hp := power_identities (by linarith : 0 < s)
  have hpos : 0 ≤ s^beta := Real.rpow_nonneg (by linarith) _
  have h15 : 0 ≤ s^(15:ℝ) := Real.rpow_nonneg (by linarith) _
  have hh := mul_le_mul_of_nonneg_left hA (show 0 ≤ M*Q*s^beta*s^(15:ℝ) by positivity)
  have he1 : M*Q*s^w=M*Q*s^beta*s^a*s^(15:ℝ) := by rw [hp.1];ring
  have he2 : G*A*Q*s^w=G*Q*s^gamma*A*s^(15:ℝ) := by rw [hp.2];ring
  have hA0 : 0 ≤ A := (Real.rpow_nonneg (by linarith) a).trans hA
  have hw : s^CWFiniteBase.exponent ≤ s^w :=
    Real.rpow_le_rpow_of_exponent_le hs (by norm_num [CWFiniteBase.exponent,w])
  have hbudget := mul_le_mul_of_nonneg_left hw (show 0 ≤ (M+G*A)*Q by positivity)
  nlinarith

theorem extra_rate (s M G Q A L : ℝ) (hs : 1 ≤ s) (hM : 0 ≤ M) (hG : 0 ≤ G)
    (hQ : 0 ≤ Q) (hA : A ≤ 2*s^a) (hL : 1 ≤ L) :
    50000*L^3*Q*(M+G*A) ≤
      100000*L^5*(M*Q*s^beta+G*Q*s^gamma) := by
  have hb : 1 ≤ s^beta := Real.one_le_rpow hs (by norm_num [beta])
  have ha : s^a ≤ s^gamma := Real.rpow_le_rpow_of_exponent_le hs (by norm_num [a,gamma])
  have hreq := mul_le_mul_of_nonneg_left hb (show 0 ≤ M*Q by positivity)
  have hgrp := mul_le_mul_of_nonneg_left (hA.trans (mul_le_mul_of_nonneg_left ha (by norm_num)))
    (show 0 ≤ G*Q by positivity)
  have hsum : Q*(M+G*A) ≤ 2*(M*Q*s^beta+G*Q*s^gamma) := by nlinarith
  have hl : L^3 ≤ L^5 := pow_le_pow_right₀ hL (by decide)
  have ht : 0 ≤ M*Q*s^beta+G*Q*s^gamma := by
    have hb0 := Real.rpow_nonneg (show 0 ≤ s by linarith) beta
    have hg0 := Real.rpow_nonneg (show 0 ≤ s by linarith) gamma
    positivity
  have hp := mul_le_mul_of_nonneg_left hsum (show 0 ≤ L^3 by positivity)
  have hp2 := mul_le_mul_of_nonneg_right hl (show 0 ≤ 2*(M*Q*s^beta+G*Q*s^gamma) by positivity)
  nlinarith

/-- The two exponents arise by dividing the actual padded chunk volume by
both tile dimensions. The positive algorithm allowance is retained. -/
theorem volume_to_rate (s M G Q A Z L K price T E V : ℝ)
    (hs : 1 ≤ s) (hM : 0 ≤ M) (hG : 0 ≤ G) (hQ : 0 ≤ Q)
    (hAlo : s^a ≤ A) (hAhi : A ≤ 2*s^a) (hZ : Z=s^(15:ℝ))
    (hL : 1 ≤ L) (hK : 0 ≤ K) (hp : 0 ≤ price)
    (hE : E ≤ 50000*L^3*Q*(M+G*A))
    (hV : V ≤ K*L^5*s^CWFiniteBase.exponent)
    (hT : T*A*Z ≤ (price+1)*(E*A*Z+2*(M+G*A)*Q*V)) :
    T ≤ (100000+2*K)*(price+1)*L^5*(M*Q*s^beta+G*Q*s^gamma) := by
  have hs0 : 0 < s := by linarith
  have hA : 0 < A := (Real.rpow_pos_of_pos hs0 a).trans_le hAlo
  have hZ0 : 0 < Z := by rw [hZ];exact Real.rpow_pos_of_pos hs0 _
  have hvol := padded_volume s M G Q A hs hM hG hQ hAlo
  have hextra := hE.trans (extra_rate s M G Q A L hs hM hG hQ hAhi hL)
  have hscalar := mul_le_mul_of_nonneg_left hV (show 0 ≤ 2*(M+G*A)*Q by positivity)
  have hscalar' := mul_le_mul_of_nonneg_left hvol (show 0 ≤ 2*K*L^5 by positivity)
  rw [← hZ] at hscalar'
  have hE' := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hextra hA.le) hZ0.le
  have hsum : E*A*Z+2*(M+G*A)*Q*V ≤
      (100000+2*K)*L^5*(M*Q*s^beta+G*Q*s^gamma)*A*Z := by nlinarith
  have hh := hT.trans (mul_le_mul_of_nonneg_left hsum (by linarith))
  have hfinal : T*(A*Z) ≤
      ((100000+2*K)*(price+1)*L^5*(M*Q*s^beta+G*Q*s^gamma))*(A*Z) := by nlinarith
  exact (mul_le_mul_iff_left₀ (mul_pos hA hZ0)).mp hfinal

#print axioms power_identities
#print axioms padded_volume
#print axioms extra_rate
#print axioms volume_to_rate
end ThinMatrix.SharedCompletionRate
