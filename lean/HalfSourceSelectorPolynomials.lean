import HalfSourceBinarySourceCosts

/-! Explicit polynomial prices for exact-half translation and selector
metadata. Exponential factors are the actual enumerated tables. -/
namespace ThinMatrix.HalfSourceSelectorPolynomials
set_option autoImplicit false
set_option maxHeartbeats 5000000
open HalfSourceBinaryScores HalfSourceIntegerScores

 theorem score_width (m P : ℕ) (hP : 1≤P) (hm : m+1≤P) : width m+1≤1000*P^4 := by
  have hm' : m≤P := by omega
  have hA : A m≤5*P := by unfold A;omega
  have hK : K m≤65*P^3 := by
    unfold K
    have hp := Nat.one_le_pow 3 P hP
    have hpow := Nat.pow_le_pow_left hm' 3
    omega
  unfold width
  have hmul := Nat.mul_le_mul hA (Nat.mul_le_mul_left 2 hK)
  have h14 := (show P≤P^4 from (by simpa only[pow_one] using Nat.pow_le_pow_right hP (show 1≤4 by decide)))
  nlinarith

 theorem score_unit (m P : ℕ) (hP : 1≤P) (hm : m+1≤P) : unit m≤1000000000*P^8 := by
  have hw := score_width m P hP hm
  unfold unit BackendScalarBits.backendScalarUnit BackendScalarBits.scalarUnit
  calc
    _ =800*(width m+1)^2 := by ring
    _ ≤800*(1000*P^4)^2 := by gcongr
    _ ≤1000000000*P^8 := by nlinarith

 theorem update_unit (m P : ℕ) (hP : 1≤P) (hm : m+1≤P) :
    HalfSourceBinaryState.updateBudget (64*m^3)≤100000000*P^6 := by
  have hs : (64*m^3+1).size≤64*m^3+1 := Nat.size_le.mpr Nat.lt_two_pow_self
  have hm' : m≤P := by omega
  have hp := Nat.one_le_pow 3 P hP
  have hpow := Nat.pow_le_pow_left hm' 3
  have hb : (64*m^3+1).size+1≤66*P^3 := by omega
  unfold HalfSourceBinaryState.updateBudget BackendScalarBits.backendScalarUnit BackendScalarBits.scalarUnit
  calc
    _ =800*((64*m^3+1).size+1)^2+10*((64*m^3+1).size+1)^2 := by ring
    _ ≤800*(66*P^3)^2+10*(66*P^3)^2 := by gcongr
    _ ≤100000000*P^6 := by nlinarith

 theorem choice (m P : ℕ) (hP : 1≤P) (hm : m+1≤P) :
    HalfSourceBinarySelection.choiceBound m≤25000000000*P^8*2^m := by
  have hu := score_unit m P hP hm
  have hp := Nat.one_le_pow 8 P hP
  have he := Nat.two_pow_pos m
  unfold HalfSourceBinarySelection.choiceBound
  have hh : unit m≤1000000000*P^8*2^m := by nlinarith only [hu, Nat.mul_le_mul_left (1000000000*P^8) he]
  nlinarith

 theorem translation_bits (m P : ℕ) (hP : 1≤P) (hm : m+1≤P) :
    HalfSourceRetainedTranslations.arithmeticBudget m≤100000000000000000000*P^14*2^m := by
  have hw := score_width m P hP hm
  have hu := score_unit m P hP hm
  have hc := choice m P hP hm
  have hd := update_unit m P hP hm
  have hm' : m≤P := by omega
  have he : 1≤2^m := Nat.two_pow_pos m
  have hK : K m≤65*P^3 := by
    unfold K
    have hp := Nat.one_le_pow 3 P hP
    have hpow := Nat.pow_le_pow_left hm' 3
    omega
  have h3 : P^3≤P^14 := Nat.pow_le_pow_right hP (by decide)
  have h4 : P^4≤P^14 := Nat.pow_le_pow_right hP (by decide)
  have h6 : P^6≤P^14 := Nat.pow_le_pow_right hP (by decide)
  have h9 : P^9≤P^14 := Nat.pow_le_pow_right hP (by decide)
  have h12 : P^12≤P^14 := Nat.pow_le_pow_right hP (by decide)
  have h0 : 1≤P^14 := Nat.one_le_pow _ _ hP
  unfold HalfSourceRetainedTranslations.arithmeticBudget
  calc
    _ ≤2*(1000*P^4+2)+2*((2*(65*P^3)+1)*(2*(65*P^3)*(1000000000*P^8)+1))+
      64*P^3*(P*(25000000000*P^8*2^m)+1+2^m*(100000000*P^6))+1 := by gcongr; omega
    _ ≤100000000000000000000*P^14*2^m := by
      have hp3 := Nat.mul_le_mul_right (2^m) h3
      have hp4 := Nat.mul_le_mul_right (2^m) h4
      have hp6 := Nat.mul_le_mul_right (2^m) h6
      have hp9 := Nat.mul_le_mul_right (2^m) h9
      have hp12 := Nat.mul_le_mul_right (2^m) h12
      have hp0 := Nat.mul_le_mul_right (2^m) h0
      have hscale := Nat.mul_le_mul_left (P^14) he
      have h11 : P^11≤P^14 := Nat.pow_le_pow_right hP (by decide)
      nlinarith

#print axioms score_width
#print axioms score_unit
#print axioms update_unit
#print axioms choice
#print axioms translation_bits
end ThinMatrix.HalfSourceSelectorPolynomials
