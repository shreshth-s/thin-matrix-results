import HalfSourceSelectorSetup

namespace ThinMatrix.HalfSourceSelectorTotal
open ExactHalfSourcePlan ExactHalfWeightTable HalfSourceSelectorPolynomials HalfSourceSelectorSetup
set_option autoImplicit false
set_option maxHeartbeats 5000000

 theorem translation_control (m P : ℕ) (hP : 1≤P) (hm : m≤P) :
    HalfSourceRetainedTranslations.indexedControlBudget m≤10000000*P^4*2^m := by
  have h1 : P≤P^4 := by simpa only[pow_one] using Nat.pow_le_pow_right hP (show 1≤4 by decide)
  have h2 : P^2≤P^4 := Nat.pow_le_pow_right hP (by decide)
  have h3 : P^3≤P^4 := Nat.pow_le_pow_right hP (by decide)
  have h0 := Nat.one_le_pow 4 P hP
  have he := Nat.two_pow_pos m
  unfold HalfSourceRetainedTranslations.indexedControlBudget
  calc
    _ ≤2^m*(4*P*P+20*P+50)+4*P+17+8*2^m+8+64*P^3*(2^m*(6*P+45)+20)+16 := by gcongr
    _ ≤_ := by
      have hp0 := Nat.mul_le_mul_right (2^m) h0
      have hp1 := Nat.mul_le_mul_right (2^m) h1
      have hp2 := Nat.mul_le_mul_right (2^m) h2
      have hp3 := Nat.mul_le_mul_right (2^m) h3
      have hx := Nat.mul_le_mul_left (P^4) he
      nlinarith

 theorem budget (L m : ℕ) (hm : m≤L) :
    HalfSourceRetainedTranslations.arithmeticBudget m+2^L*candidateBitBudget L+
      retainedControlBudget L m≤
        200000000000000000000*(L+m+1)^14*12^L*2^(L-m) := by
  let P := L+m+1
  let U := 12^L*2^(L-m)
  let V := P^14*U
  have hP : 1≤P := by dsimp[P];omega
  have ha : 1≤2^L := Nat.two_pow_pos L
  have hb : 1≤2^m := Nat.two_pow_pos m
  have htab := raw_tables L m hm
  have hLa : 2^L≤U := by
    have h1 : 2^L≤2^L*2^m := Nat.le_mul_of_pos_right _ hb
    have h2 : 2^L*2^m≤2^L*2^m*2^L := Nat.le_mul_of_pos_right _ ha
    exact (h1.trans h2).trans htab
  have hma : 2^m≤U := by
    have h1 : 2^m≤2^L*2^m := Nat.le_mul_of_pos_left _ ha
    have h2 : 2^L*2^m≤2^L*2^m*2^L := Nat.le_mul_of_pos_right _ ha
    exact (h1.trans h2).trans htab
  have hU : 1≤U := hb.trans hma
  have hV : 1≤V := one_le_mul (Nat.one_le_pow _ _ hP) hU
  have hpow (k : ℕ) (hk : k≤14) : P^k≤P^14 := Nat.pow_le_pow_right hP hk
  have hbits : HalfSourceRetainedTranslations.arithmeticBudget m≤100000000000000000000*V := by
    calc
      _ ≤100000000000000000000*P^14*2^m := translation_bits m P hP (by dsimp[P];omega)
      _ ≤100000000000000000000*P^14*U := Nat.mul_le_mul_left _ hma
      _ =_ := by dsimp[V];ring
  have hcan : 2^L*candidateBitBudget L≤10000*V := by
    have hc := candidate L m
    calc
      _ ≤2^L*(10000*P^3) := Nat.mul_le_mul_left _ hc
      _ ≤U*(10000*P^14) := by gcongr;decide
      _ =_ := by dsimp[V];ring
  have hctrl : HalfSourceRetainedTranslations.indexedControlBudget m≤10000000*V := by
    have hc := translation_control m P hP (by dsimp[P];omega)
    calc
      _ ≤10000000*P^4*2^m := hc
      _ ≤10000000*P^14*U := by gcongr;decide
      _ =_ := by dsimp[V];ring
  have hscan : (100*(L+m+1)^3+4*L+12)*2^L+1≤200*V := by
    have hL : L≤P^3 := (show L≤P by dsimp[P];omega).trans
      (by simpa only[pow_one] using Nat.pow_le_pow_right hP (show 1≤3 by decide))
    have hp3 := Nat.one_le_pow 3 P hP
    have hh : 100*(L+m+1)^3+4*L+12≤120*P^3 := by change 100*P^3+4*L+12≤_;omega
    have hs : (100*(L+m+1)^3+4*L+12)*2^L≤120*V := by
      calc
        _≤(120*P^3)*U := Nat.mul_le_mul hh hLa
        _≤120*P^14*U := by gcongr;decide
        _=_ := by dsimp[V];ring
    omega
  have hbuild : buildBudget L m≤100*V := by
    have h := build L m hm
    calc
      _ ≤100*P*U := by simpa only[P,U,mul_assoc] using h
      _ ≤100*P^14*U := by gcongr;simpa only[pow_one] using hpow 1 (by decide)
      _ =_ := by dsimp[V];ring
  have hpicks : picksBudget L m≤3000*V := by
    have h := picks L m hm
    calc
      _ ≤3000*P^4*U := by simpa only[P,U,mul_assoc] using h
      _ ≤3000*P^14*U := by gcongr;decide
      _ =_ := by dsimp[V];ring
  have hj : (4*m+8)*J m+16≤1000*V := by
    have hmP : 4*m+8≤8*P := by dsimp[P];omega
    have hh := Nat.mul_le_mul hmP (J_bound L m)
    have hp4 : P^4≤V := (hpow 4 (by decide)).trans (Nat.le_mul_of_pos_right _ hU)
    change _≤8*P*(64*P^3) at hh
    nlinarith
  unfold retainedControlBudget
  change _ ≤200000000000000000000*P^14*12^L*2^(L-m)
  have hvEq : P^14*12^L*2^(L-m)=V := by dsimp[V,U];ring
  calc
    _ ≤200000000000000000000*V := by omega
    _ =_ := by dsimp[V,U];ring

 theorem actual {L m : ℕ} (shape : ThinMatrixBackend.ShapePlan L m) (hm : m≤L) :
    (prepare shape).bitSteps+(prepare shape).control≤
      200000000000000000000*(L+m+1)^14*12^L*2^(L-m) :=
    (Nat.add_le_add (prepare_bits shape) (prepare_retained_control shape)).trans (budget L m hm)

#print axioms translation_control
#print axioms budget
#print axioms actual
end ThinMatrix.HalfSourceSelectorTotal
