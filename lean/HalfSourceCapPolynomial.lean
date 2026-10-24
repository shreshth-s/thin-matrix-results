import HalfSourceDirectSetup

namespace ThinMatrix.HalfSourceCapPolynomial
open HalfSourceParameters
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section

theorem budget_bound (L m : ℕ) (hm : m ≤ L) :
    HalfSourceCapSetup.bitBudget m (L-m) ≤ 100000000000*(L+m+1)^3*4^m := by
  let P := L+m+1
  let D := 4^m
  have hP : 1 ≤ P := by dsimp[P];omega
  have hD : 1 ≤ D := Nat.one_le_pow _ _ (by decide)
  have hmP : m+1 ≤ P := by dsimp[P];omega
  have hw : HalfSourceCapSetup.width m (L-m)+1 ≤ 300*P := by
    have hs := HalfSourceAdaptivePolynomials.size_le (L-m)
    unfold HalfSourceCapSetup.width
    dsimp[P]
    omega
  have hu : ParameterExecution.unit (HalfSourceCapSetup.width m (L-m))+1 ≤ 100000000*P^2 := by
    unfold ParameterExecution.unit
    have hh := Nat.pow_le_pow_left hw 2
    have hP2 : 1 ≤ P^2 := Nat.one_le_pow 2 P hP
    nlinarith only[hh,hP2]
  have hf : m+5+(D+2)*71 ≤ 220*P*D := by
    have h1 : m+1 ≤ P*D := hmP.trans (Nat.le_mul_of_pos_right _ hD)
    have h2 : D ≤ P*D := Nat.le_mul_of_pos_left _ hP
    have h3 : 1 ≤ P*D := Nat.mul_pos hP hD
    nlinarith only[h1,h2,h3]
  have hp : 1 ≤ P^3*D := Nat.mul_pos (Nat.one_le_pow 3 P hP) hD
  unfold HalfSourceCapSetup.bitBudget
  change (m+5+(D+2)*71)*(ParameterExecution.unit (HalfSourceCapSetup.width m (L-m))+1)+25 ≤ 100000000000*P^3*D
  have hh := Nat.mul_le_mul hf hu
  nlinarith only[hh,hp]

theorem budget_direct (L m q : ℕ) (hm : m ≤ L) (hq : 1 ≤ q) :
    HalfSourceCapSetup.bitBudget m (L-m) ≤ HalfSourceDirectSetup.budget L m q := by
  have hb := budget_bound L m hm
  have hp : (L+m+1)^3 ≤ (L+m+1)^14 := Nat.pow_le_pow_right (by omega) (by decide)
  have hd : 4^m ≤ 12^L := by
    calc
      _ ≤12^m := Nat.pow_le_pow_left (by decide) _
      _ ≤12^L := Nat.pow_le_pow_right (by decide) hm
  have he : 1 ≤ 2^(L-m) := Nat.one_le_pow _ _ (by decide)
  calc
    _ ≤100000000000*(L+m+1)^3*4^m := hb
    _ ≤100000000000*(L+m+1)^14*12^L := by gcongr
    _ ≤300000000000000000000*(L+m+1)^14*q*12^L*2^(L-m) := by
      have hq' := Nat.mul_le_mul_left (100000000000*(L+m+1)^14*12^L) hq
      have he' := Nat.mul_le_mul_left (300000000000000000000*(L+m+1)^14*q*12^L) he
      nlinarith only[hq',he',show 0 ≤ (L+m+1)^14*q*12^L by omega]
    _ =_ := rfl

#print axioms budget_bound
#print axioms budget_direct
end
end ThinMatrix.HalfSourceCapPolynomial
