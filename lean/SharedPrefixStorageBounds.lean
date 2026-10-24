import SharedPrefixStorage

set_option autoImplicit false
set_option maxHeartbeats 2200000

/-! Whole-root address pricing from explicit shape bounds. The scale U is a
bound on original shape bit lengths and prefix lengths, not on a desired
running time. All window banks and completed product trees remain present. -/
namespace ThinMatrix.SharedPrefixStorageBounds
open SharedPrefixStorage

def scale (U : ℕ) := 2^(U+1)

theorem scale_facts (P ell U : ℕ) (hlen : P+ell ≤ U) :
    1 ≤ scale U ∧ P+ell+1 ≤ scale U ∧ 2^ell ≤ scale U ∧
    4^P ≤ (scale U)^2 ∧ 3^P ≤ (scale U)^2 ∧ 3^(P+ell) ≤ (scale U)^2 := by
  have h1 : 1 ≤ scale U := one_le_pow₀ (by decide)
  have hu : U+1 ≤ scale U := Nat.lt_two_pow_self.le
  have hlen' : P+ell+1 ≤ scale U := (by omega : P+ell+1 ≤ U+1).trans hu
  have hp : (4:ℕ)^P ≤ (scale U)^2 := by
    unfold scale
    rw [show (4:ℕ)=2^2 by decide,←pow_mul,←pow_mul]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have hpell : (4:ℕ)^(P+ell) ≤ (scale U)^2 := by
    unfold scale
    rw [show (4:ℕ)=2^2 by decide,←pow_mul,←pow_mul]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  exact ⟨h1,hlen',Nat.pow_le_pow_right (by decide) (by omega),hp,
    (Nat.pow_le_pow_left (by decide : 3 ≤ 4) P).trans hp,
    (Nat.pow_le_pow_left (by decide : 3 ≤ 4) (P+ell)).trans hpell⟩

theorem bank_bound (P ell D B C U : ℕ) (hlen : P+ell ≤ U)
    (hD : D ≤ 2^U) (hB : B ≤ 2^U) (hC : C ≤ 2^U) :
    bankBudget P ell D B C ≤ 8*(scale U)^7 := by
  let X := scale U
  have hf := scale_facts P ell U hlen
  have h2 : 2^U ≤ X := Nat.pow_le_pow_right (by decide) (by omega)
  have hd : D ≤ X := hD.trans h2
  have hb : B ≤ X := hB.trans h2
  have hc : C ≤ X := hC.trans h2
  have hp : 2^ell ≤ X := hf.2.2.1
  have hfour : 4^P ≤ X^2 := hf.2.2.2.1
  have hthree : 3^P ≤ X^2 := hf.2.2.2.2.1
  have hboth : 3^(P+ell) ≤ X^2 := hf.2.2.2.2.2
  have hlen' : P+1 ≤ X := by have hh:=hf.2.1;omega
  have hell : ell+1 ≤ X := by have hh:=hf.2.1;omega
  have h1 : 1 ≤ X := hf.1
  have ha : B*2^ell*D*3^P*C ≤ X^6 := by
    calc
      _ ≤ X*X*X*X^2*X := Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul hb hp) hd) hthree) hc
      _=_ := by ring
  have ht : B*2^ell*D*(P+1)*4^P*C ≤ X^7 := by
    calc
      _ ≤ X*X*X*X*X^2*X := Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul hb hp) hd) hlen') hfour) hc
      _=_ := by ring
  have hm : B*2^ell*4^P*D*C ≤ X^6 := by
    calc
      _ ≤ X*X*X^2*X*X := Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul hb hp) hfour) hd) hc
      _=_ := by ring
  have ho : B*C*3^(P+ell) ≤ X^4 := by
    calc
      _ ≤ X*X*X^2 := Nat.mul_le_mul (Nat.mul_le_mul hb hc) hboth
      _=_ := by ring
  have hmeta : (B+1)*(D+2^ell)*(ell+1) ≤ 4*X^3 := by
    calc
      _ ≤ (2*X)*(2*X)*X := Nat.mul_le_mul (Nat.mul_le_mul (by omega) (by omega)) hell
      _=_ := by ring
  have h67 : X^6 ≤ X^7 := Nat.pow_le_pow_right h1 (by decide)
  have h47 : X^4 ≤ X^7 := Nat.pow_le_pow_right h1 (by decide)
  have h37 : X^3 ≤ X^7 := Nat.pow_le_pow_right h1 (by decide)
  unfold bankBudget
  change _ ≤ 8*X^7
  nlinarith

theorem window_bound (P ell M D Q A Z R U : ℕ) (hlen : P+ell ≤ U)
    (hA : 0 < A) (hZ : 0 < Z) (hM : M ≤ 2^U) (hD : D ≤ 2^U) (hQ : Q ≤ 2^U)
    (ha : A ≤ 2^U) (hz : Z ≤ 2^U) (hR : R ≤ 2^U) :
    windowBudget P ell M D Q A Z R ≤ 2048*(scale U)^8 := by
  let X := scale U
  have hf := scale_facts P ell U hlen
  have h2 : 2^U ≤ X := Nat.pow_le_pow_right (by decide) (by omega)
  have hm := hM.trans h2
  have hd := hD.trans h2
  have hq := hQ.trans h2
  have hr := hR.trans h2
  have h1 : 1 ≤ X := hf.1
  have hlen' : P+ell+1 ≤ X := hf.2.1
  have hg : 2^ell*4^P ≤ X^3 := by
    calc
      _ ≤ X*X^2 := Nat.mul_le_mul hf.2.2.1 hf.2.2.2.1
      _=_ := by ring
  have hb := SharedAddressedStorage.batch_bound M D Q A Z R X h1 hA hZ hm hd hq (ha.trans h2) (hz.trans h2)
  have hbatch : BinaryAddressedStorage.batchCells M D Q A Z R ≤ 16*X^5 := by
    apply hb.trans
    have hh := Nat.mul_le_mul_left (8*X^4) (show R+1 ≤ 2*X by omega)
    exact hh.trans_eq (by ring)
  have hmeta : 64*(M+1)*(D+1)*(Q+1)*(P+ell+1) ≤ 512*X^4 := by
    calc
      _ ≤ 64*(2*X)*(2*X)*(2*X)*X := Nat.mul_le_mul
        (Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left 64 (by omega)) (by omega)) (by omega)) hlen'
      _=_ := by ring
  have h45 : X^4 ≤ X^5 := Nat.pow_le_pow_right h1 (by decide)
  have hfirst : (2^ell*4^P)*(BinaryAddressedStorage.batchCells M D Q A Z R+
      64*(M+1)*(D+1)*(Q+1)*(P+ell+1)) ≤ 528*X^8 := by
    have hsum : BinaryAddressedStorage.batchCells M D Q A Z R+
        64*(M+1)*(D+1)*(Q+1)*(P+ell+1) ≤ 528*X^5 := by nlinarith
    have hh := Nat.mul_le_mul hg hsum
    exact hh.trans_eq (by ring)
  have hsecond : 64*(2^ell*4^P+1)*(M+1)*(Q+1)*(P+ell+1) ≤ 512*X^6 := by
    have hpow : 1 ≤ X^3 := one_le_pow₀ h1
    calc
      _ ≤ 64*(2*X^3)*(2*X)*(2*X)*X := Nat.mul_le_mul
        (Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left 64 (by omega)) (by omega)) (by omega)) hlen'
      _=_ := by ring
  have h68 : X^6 ≤ X^8 := Nat.pow_le_pow_right h1 (by decide)
  unfold windowBudget
  change _ ≤ 2048*X^8
  nlinarith

theorem root_bound (windows P ell M D B C A Z R U : ℕ) (hlen : P+ell ≤ U)
    (hA : 0 < A) (hZ : 0 < Z) (hW : windows ≤ 2^U) (hM : M ≤ 2^U) (hD : D ≤ 2^U)
    (hB : B ≤ 2^U) (hC : C ≤ 2^U) (hQ : B*C ≤ 2^U)
    (ha : A ≤ 2^U) (hz : Z ≤ 2^U) (hR : R ≤ 2^U) :
    rootBudget windows P ell M D B C A Z R ≤ 2^(9*U+21) := by
  let X := scale U
  have hf := scale_facts P ell U hlen
  have h2 : 2^U ≤ X := Nat.pow_le_pow_right (by decide) (by omega)
  have hw := hW.trans h2
  have hm := hM.trans h2
  have hq := hQ.trans h2
  have h1 : 1 ≤ X := hf.1
  have hlen' : P+ell+1 ≤ X := hf.2.1
  have hb := bank_bound P ell D B C U hlen hD hB hC
  have hc := window_bound P ell M D (B*C) A Z R U hlen hA hZ hM hD hQ ha hz hR
  have h78 : X^7 ≤ X^8 := Nat.pow_le_pow_right h1 (by decide)
  have hsum : bankBudget P ell D B C+windowBudget P ell M D (B*C) A Z R ≤ 2056*X^8 := by
    change _ ≤ 8*X^7 at hb
    change _ ≤ 2048*X^8 at hc
    nlinarith
  have hchildren : windows*(bankBudget P ell D B C+windowBudget P ell M D (B*C) A Z R) ≤ 2056*X^9 := by
    exact (Nat.mul_le_mul hw hsum).trans_eq (by ring)
  have houtputs : 64*(windows+1)*(M+1)*(B*C+1)*(P+ell+1) ≤ 512*X^4 := by
    calc
      _ ≤ 64*(2*X)*(2*X)*(2*X)*X := Nat.mul_le_mul
        (Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left 64 (by omega)) (by omega)) (by omega)) hlen'
      _=_ := by ring
  have h49 : X^4 ≤ X^9 := Nat.pow_le_pow_right h1 (by decide)
  have htotal : rootBudget windows P ell M D B C A Z R ≤ 4096*X^9 := by
    unfold rootBudget
    nlinarith
  apply htotal.trans_eq
  dsimp [X,scale]
  rw [show (4096:ℕ)=2^12 by decide,←pow_mul,←pow_add]
  congr 1
  ring

theorem heap_width (windows P ell M D B C A Z R U fields j : ℕ) (hlen : P+ell ≤ U)
    (hA : 0 < A) (hZ : 0 < Z) (hW : windows ≤ 2^U) (hM : M ≤ 2^U) (hD : D ≤ 2^U)
    (hB : B ≤ 2^U) (hC : C ≤ 2^U) (hQ : B*C ≤ 2^U)
    (ha : A ≤ 2^U) (hz : Z ≤ 2^U) (hR : R ≤ 2^U) (hF : fields ≤ 2^U)
    (hj : j < BinaryAddressedStorage.bitCells (rootBudget windows P ell M D B C A Z R) fields) :
    j.size ≤ 10*U+29 := by
  have hr := root_bound windows P ell M D B C A Z R U hlen hA hZ hW hM hD hB hC hQ ha hz hR
  have hsucc : rootBudget windows P ell M D B C A Z R+1 ≤ 2^(9*U+22) := by
    have h1 : 1 ≤ 2^(9*U+21) := one_le_pow₀ (by decide)
    rw [show 9*U+22=(9*U+21)+1 by omega,pow_succ];omega
  have hfields : fields+1 ≤ 2^(U+1) := by
    have h1 : 1 ≤ 2^U := one_le_pow₀ (by decide)
    rw [pow_succ];omega
  have hheap : BinaryAddressedStorage.bitCells (rootBudget windows P ell M D B C A Z R) fields ≤ 2^(10*U+28) := by
    unfold BinaryAddressedStorage.bitCells
    calc
      _ ≤ 32*2^(9*U+22)*2^(U+1) := Nat.mul_le_mul (Nat.mul_le_mul_left _ hsucc) hfields
      _=_ := by rw [show (32:ℕ)=2^5 by decide,←pow_add,←pow_add];congr 1;ring
  have hh := (Nat.size_le_size (hj.le.trans hheap)).trans_eq Nat.size_pow
  omega

def addressPrice (U : ℕ) := BackendScalarBits.addressedUnit U (10*U+29)

theorem price_polynomial (U : ℕ) : addressPrice U ≤ 102400*(U+1)^2 := by
  unfold addressPrice BackendScalarBits.addressedUnit BackendScalarBits.scalarUnit
  have hh : U+(10*U+29)+1+1 ≤ 32*(U+1) := by omega
  have hp := Nat.mul_le_mul_left 100 (Nat.pow_le_pow_left hh 2)
  nlinarith

#print axioms scale_facts
#print axioms bank_bound
#print axioms window_bound
#print axioms root_bound
#print axioms heap_width
#print axioms price_polynomial
end ThinMatrix.SharedPrefixStorageBounds
