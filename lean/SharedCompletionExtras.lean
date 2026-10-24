import SharedFullyPrefixPrices

set_option autoImplicit false
set_option maxHeartbeats 2400000

namespace ThinMatrix.SharedCompletionExtras
open SharedFullyPrefixWork

theorem request_bound (D Q ell W L : ℕ) (hQ : 1 ≤ Q) (hD : D ≤ Q)
    (hL : 1 ≤ L) (hell : ell+1 ≤ L) (hW : W+1 ≤ L) :
    requestUnit D Q ell W ≤ 20000*Q*L^2 := by
  have hw := Nat.pow_le_pow_left hW 2
  have hl : L ≤ L^2 := by nlinarith
  have hq : Q ≤ Q*L^2 := Nat.le_mul_of_pos_right _ (one_le_pow₀ hL)
  have hd : D ≤ Q*L^2 := hD.trans hq
  have hdp := Nat.mul_le_mul hD hw
  have hqp := Nat.mul_le_mul_left Q hw
  have he : 26*ell+24 ≤ 26*L := by omega
  have hde : D*(26*ell+24) ≤ 26*Q*L^2 := by
    have hh := Nat.mul_le_mul hD he
    nlinarith [Nat.mul_le_mul_left (26*Q) hl]
  have hell' : 16*ell+16 ≤ 16*Q*L^2 := by
    have hh : ell+1 ≤ Q*L^2 := hell.trans (hl.trans (Nat.le_mul_of_pos_left _ hQ))
    nlinarith
  unfold requestUnit
  nlinarith

theorem group_bound (D B Q A P ell W L : ℕ) (hQ : 1 ≤ Q) (hA : 1 ≤ A)
    (hDQ : D ≤ Q) (hDA : D ≤ A) (hB : B ≤ Q)
    (hL : 1 ≤ L) (hlen : P+ell+1 ≤ L) (hW : W+1 ≤ L) :
    groupUnit D B Q A P ell W ≤ 40000*Q*A*L^2 := by
  have hw := Nat.pow_le_pow_left hW 2
  have hspan : A*D+2*Q*D ≤ 3*Q*A := by
    nlinarith [Nat.mul_le_mul_left A hDQ,Nat.mul_le_mul_left (2*Q) hDA]
  have hspanP := Nat.mul_le_mul hspan hw
  have hqa : 1 ≤ Q*A := Nat.mul_pos hQ hA
  have hpow : 1 ≤ L^2 := one_le_pow₀ hL
  have hqa' : Q*A ≤ Q*A*L^2 := Nat.le_mul_of_pos_right _ hpow
  have hq : Q ≤ Q*A*L^2 := (Nat.le_mul_of_pos_right Q hA).trans hqa'
  have hdq : D*Q ≤ Q*A*L^2 := by nlinarith [Nat.mul_le_mul_right Q hDA]
  have hd : D ≤ Q*A*L^2 := hDQ.trans hq
  have hb : B*(16*(P+1)^2+40) ≤ 56*Q*A*L^2 := by
    have hp : (P+1)^2 ≤ L^2 := Nat.pow_le_pow_left (by omega) 2
    have hh : 16*(P+1)^2+40 ≤ 56*L^2 := by nlinarith
    have hh' := Nat.mul_le_mul hB hh
    have ha' := Nat.mul_le_mul_left (56*Q*L^2) hA
    nlinarith
  have hp : (P+(P+ell)+1)^2 ≤ 4*L^2 := by
    have hh := Nat.pow_le_pow_left (show P+(P+ell)+1 ≤ 2*L by omega) 2
    nlinarith
  have hl : P+ell+1 ≤ L^2 := hlen.trans (by nlinarith)
  have hpoly : 16*(P+(P+ell)+1)^2+32*(P+ell+1)+16 ≤ 112*Q*A*L^2 := by
    have hh := Nat.mul_le_mul_right (L^2) hqa
    nlinarith
  unfold groupUnit
  nlinarith

theorem schedule_bound (P ell L : ℕ) (hL : 1 ≤ L) (hlen : P+ell+1 ≤ L) :
    scheduleControl P ell ≤ 200*(2^ell*4^P)*L^3 := by
  have he : 1 ≤ 2^ell := one_le_pow₀ (by decide)
  have hp : 1 ≤ 4^P := one_le_pow₀ (by decide)
  have hG : 1 ≤ 2^ell*4^P := Nat.mul_pos he hp
  have hpow : 1 ≤ L^3 := one_le_pow₀ hL
  have hprefix : (P+1)^3 ≤ L^3 := Nat.pow_le_pow_left (by omega) 3
  have hbase : 4^P ≤ 2^ell*4^P := Nat.le_mul_of_pos_left _ he
  have hexp : 2^ell ≤ 2^ell*4^P := Nat.le_mul_of_pos_right _ hp
  have ha := Nat.mul_le_mul hbase hprefix
  have hb := Nat.mul_le_mul_right (L^3) hbase
  have hc := Nat.mul_le_mul_right (L^3) hexp
  have hd : 2^ell*4^P ≤ (2^ell*4^P)*L^3 := Nat.le_mul_of_pos_right _ hpow
  unfold scheduleControl
  nlinarith

theorem setup_bound (scheme : RectangularBatch.Scheme) {D A Z : ℕ}
    (hD : 0 < D) (hf : (A-1)^scheme.den ≤ D^scheme.num) (hl : Z ≤ D^scheme.z)
    (L : ℕ) (hL : 1 ≤ L) (hd : D.size+3 ≤ L) (hq : scheme.q.size+D.size+6 ≤ L) :
    (SharedMatrixSetup.prepare scheme hD hf hl).bitSteps ≤ 1404*L^3 := by
  have hh := SharedMatrixSetup.prepare_bits scheme hD hf hl
  have hp := Nat.mul_le_mul hd (Nat.pow_le_pow_left hq 2)
  have h1 : 1 ≤ L^3 := one_le_pow₀ hL
  nlinarith

theorem all_extras (scheme : RectangularBatch.Scheme) {D A Z : ℕ}
    (hD : 0 < D) (hf : (A-1)^scheme.den ≤ D^scheme.num) (hl : Z ≤ D^scheme.z)
    (M B Q P ell W L : ℕ) (hQ : 1 ≤ Q) (hA : 1 ≤ A)
    (hDQ : D ≤ Q) (hDA : D ≤ A) (hB : B ≤ Q)
    (hL : 1 ≤ L) (hlen : P+ell+1 ≤ L) (hW : W+1 ≤ L)
    (hd : D.size+3 ≤ L) (hq : scheme.q.size+D.size+6 ≤ L) :
    (SharedMatrixSetup.prepare scheme hD hf hl).bitSteps+scheduleControl P ell+
      M*requestUnit D Q ell W+(2^ell*4^P)*groupUnit D B Q A P ell W ≤
      50000*L^3*Q*(M+(2^ell*4^P)*A) := by
  have hr := request_bound D Q ell W L hQ hDQ hL (by omega) hW
  have hg := group_bound D B Q A P ell W L hQ hA hDQ hDA hB hL hlen hW
  have hs := schedule_bound P ell L hL hlen
  have ht := setup_bound scheme hD hf hl L hL hd hq
  have h23 : L^2 ≤ L^3 := Nat.pow_le_pow_right hL (by decide)
  have hr' := Nat.mul_le_mul_left M hr
  have hg' := Nat.mul_le_mul_left (2^ell*4^P) hg
  have hbase : 1 ≤ (2^ell*4^P)*A*Q := Nat.mul_pos (Nat.mul_pos
    (Nat.mul_pos (show 1 ≤ 2^ell from one_le_pow₀ (by decide)) (show 1 ≤ 4^P from one_le_pow₀ (by decide))) hA) hQ
  have ht' := Nat.mul_le_mul_left (L^3) hbase
  have hs' := Nat.mul_le_mul_left ((2^ell*4^P)*L^3)
    (Nat.mul_pos hQ hA : 1 ≤ Q*A)
  have hr23 := Nat.mul_le_mul_left (M*Q) h23
  have hg23 := Nat.mul_le_mul_left ((2^ell*4^P)*Q*A) h23
  nlinarith

#print axioms request_bound
#print axioms group_bound
#print axioms schedule_bound
#print axioms setup_bound
#print axioms all_extras
end ThinMatrix.SharedCompletionExtras
