import HalfSourceSelectorPolynomials

namespace ThinMatrix.HalfSourceSelectorSetup
open ExactHalfSourcePlan ExactHalfWeightTable HalfSourceSelectorPolynomials
set_option autoImplicit false
set_option maxHeartbeats 5000000

 theorem J_bound (L m : ℕ) : J m≤64*(L+m+1)^3 := by
  rw [←count_eq]
  unfold count
  split_ifs
  · have hp := Nat.one_le_pow 3 (L+m+1) (by omega)
    omega
  · gcongr;omega

 theorem candidate (L m : ℕ) : candidateBitBudget L≤10000*(L+m+1)^3 := by
  have hs : L.size+1≤L+m+1 := by have := Nat.size_le.mpr (Nat.lt_two_pow_self (n:=L));omega
  have hp : 1≤L+m+1 := by omega
  unfold candidateBitBudget BackendScalarBits.backendScalarUnit BackendScalarBits.scalarUnit
  have h2 : (L+m+1)^2≤(L+m+1)^3 := Nat.pow_le_pow_right hp (by decide)
  have h0 := Nat.one_le_pow 3 (L+m+1) hp
  have hL : L≤L+m+1 := by omega
  calc
    _ =L*(800*(L.size+2)^2+4)+1+8*(L.size+1)^2 := by ring
    _ ≤(L+m+1)*(800*(2*(L+m+1))^2+4)+1+8*(L+m+1)^2 := by gcongr;omega
    _ ≤_ := by nlinarith

 theorem select (L m : ℕ) : selectBudget L m≤2000*(L+m+1)^4 := by
  have hJ := J_bound L m
  have hh : 2*L+10*m+14≤14*(L+m+1) := by omega
  have hp := Nat.one_le_pow 4 (L+m+1) (by omega)
  unfold selectBudget
  calc
    _ ≤64*(L+m+1)^3*(14*(L+m+1))+4 := by gcongr
    _ ≤_ := by nlinarith

 theorem raw_tables (L m : ℕ) (hm : m≤L) :
    2^L*2^m*2^L≤12^L*2^(L-m) := by
  calc
    _ =2^(L+m+L) := by rw[pow_add,pow_add]
    _ ≤2^(3*L) := Nat.pow_le_pow_right (by decide) (by omega)
    _ =8^L := by rw[pow_mul];congr 1
    _ ≤12^L := Nat.pow_le_pow_left (by decide) _
    _ ≤_ := Nat.le_mul_of_pos_right _ (Nat.one_le_pow _ _ (by decide))

 theorem build (L m : ℕ) (hm : m≤L) :
    buildBudget L m≤100*(L+m+1)*12^L*2^(L-m) := by
  let P := L+m+1
  let a := 2^L
  let b := 2^m
  have ha : 1≤a := Nat.two_pow_pos L
  have hb : 1≤b := Nat.two_pow_pos m
  have hp : 1≤P := by dsimp[P];omega
  have h1 : 2*L+6+2^L*(8*(L+m+1))+16*m≤40*P*a := by
    dsimp only[P,a] at *
    nlinarith only[Nat.mul_le_mul_left (32*(L+m+1)) ha]
  have h2 : (2*L+6+2^L*(8*(L+m+1))+16*m)*2^m+16*L≤60*P*a*b := by
    have h := Nat.mul_le_mul_right b h1
    have hpa : P≤P*a := Nat.le_mul_of_pos_right _ ha
    have hpb : P*a≤P*a*b := Nat.le_mul_of_pos_right _ hb
    have hL : L≤P := by dsimp[P];omega
    change _≤60*P*a*b
    dsimp only[b] at *
    nlinarith only[h,hpa,hpb,hL]
  unfold buildBudget
  calc
    _ ≤(60*P*a*b)*a := Nat.mul_le_mul_right a h2
    _ =60*P*(2^L*2^m*2^L) := by dsimp[a,b];ring
    _ ≤60*P*(12^L*2^(L-m)) := Nat.mul_le_mul_left _ (raw_tables L m hm)
    _ ≤_ := by
      calc
        _ ≤100*P*(12^L*2^(L-m)) := by gcongr;norm_num
        _ =_ := by dsimp[P];ring

 theorem picks (L m : ℕ) (hm : m≤L) : picksBudget L m≤3000*(L+m+1)^4*12^L*2^(L-m) := by
  let P := L+m+1
  let a := 2^L
  let b := 2^m
  have ha : 1≤a := Nat.two_pow_pos L
  have hb : 1≤b := Nat.two_pow_pos m
  have hP : 1≤P := by dsimp[P];omega
  have hPL : L≤P^4 := (show L≤P by dsimp[P];omega).trans
    (by simpa only[pow_one] using Nat.pow_le_pow_right hP (show 1≤4 by decide))
  have hPm : m≤P^4 := (show m≤P by dsimp[P];omega).trans
    (by simpa only[pow_one] using Nat.pow_le_pow_right hP (show 1≤4 by decide))
  have hs : selectBudget L m≤2000*P^4 := select L m
  have hbound : (selectBudget L m+16*m)*2^m+16*L≤2100*P^4*b := by
    have hp := Nat.mul_le_mul_right b (show selectBudget L m+16*m≤2016*P^4 by omega)
    have hbP : P^4≤P^4*b := Nat.le_mul_of_pos_right _ hb
    dsimp only[b] at *
    nlinarith
  unfold picksBudget
  calc
    _ ≤(2100*P^4*b)*a := Nat.mul_le_mul_right a hbound
    _ ≤2100*P^4*(a*b*a) := by nlinarith only[Nat.mul_le_mul_left (2100*P^4*b*a) ha]
    _ ≤2100*P^4*(12^L*2^(L-m)) := Nat.mul_le_mul_left _ (raw_tables L m hm)
    _ ≤_ := by
      calc
        _ ≤3000*P^4*(12^L*2^(L-m)) := by gcongr;norm_num
        _ =_ := by dsimp[P];ring

#print axioms J_bound
#print axioms candidate
#print axioms select
#print axioms raw_tables
#print axioms build
#print axioms picks
end ThinMatrix.HalfSourceSelectorSetup
