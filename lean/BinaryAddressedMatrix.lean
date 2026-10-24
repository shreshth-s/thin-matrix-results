import BinaryAddressedPaddingCosts

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 5000
set_option backward.isDefEq.respectTransparency false

/-! Complete ordinary matrix products with binary padding, tensor-word
addresses, recursive coefficient/child addresses, exact scalar recovery and
binary output cropping. Shape selection remains external and reusable. -/
namespace ThinMatrix.BinaryAddressedMatrix
open scoped BigOperators
open BinaryCell BinaryGroupedCoordinates
open RecursiveTable (Table prod fin power)
open PolynomialDegeneration RetainedEqualCopy
open BinaryAddressedRecursion
variable {a b c r t n m p : ℕ}

def execute (ha : 0<a) (hb : 0<b) (hc : 0<c) (ht : 0<t)
    (d : Base r t (prod (fin a) (fin b)) (prod (fin b) (fin c)) (prod (fin c) (fin a)) ℚ)
    (k : ℕ) (hn : n≤a^k) (hp : p≤c^k)
    (x : Table (PaddedMatrix.matrix n m) Cell) (y : Table (PaddedMatrix.matrix m p) Cell) :
    Run (Table (PaddedMatrix.matrix n p) Cell) :=
  let left := BinaryAddressedPadding.pad (t:=t) ha hb k x
  let right := BinaryAddressedPadding.pad (t:=t) hb hc k y
  let answer := BinaryAddressedRecovery.execute ha hb hc ht d k left.value right.value
  let output := BinaryAddressedPadding.crop ha hc ht k hn hp answer.value
  ⟨output.value,left.bitSteps+right.bitSteps+answer.bitSteps+output.bitSteps,
    left.control+right.control+answer.control+output.control+16⟩

theorem execute_value (ha : 0<a) (hb : 0<b) (hc : 0<c) (ht : 0<t)
    (d : Base r t (prod (fin a) (fin b)) (prod (fin b) (fin c)) (prod (fin c) (fin a)) ℚ)
    (k : ℕ) (hn : n≤a^k) (hp : p≤c^k)
    (x : Table (PaddedMatrix.matrix n m) Cell) (y : Table (PaddedMatrix.matrix m p) Cell) :
    (execute ha hb hc ht d k hn hp x y).value=
      (PaddedMatrix.execute (fin a) (fin b) (fin c) ht d k hn hp x y).value := by
  simp only [execute,PaddedMatrix.execute,BinaryMatrixPowers.execute,
    BinaryAddressedPadding.crop_value,BinaryAddressedRecovery.execute_value,BinaryAddressedPadding.pad_value]

theorem execute_correct (ha : 0<a) (hb : 0<b) (hc : 0<c) (ht : 0<t)
    (d : Base r t (prod (fin a) (fin b)) (prod (fin b) (fin c)) (prod (fin c) (fin a)) ℚ)
    (hd : FiniteTrilinear.total d.terms=FiniteDirectSum.diagonal (Fin t)
      (FiniteMatrixTensor.coeff (Fin a) (Fin b) (Fin c) ℚ))
    (k : ℕ) (hn : n≤a^k) (hm : m≤b^k) (hp : p≤c^k)
    (x : Table (PaddedMatrix.matrix n m) Cell) (y : Table (PaddedMatrix.matrix m p) Cell) (i : Fin n×Fin p) :
    view (RecursiveTable.read (execute ha hb hc ht d k hn hp x y).value i)=
      ∑ j : Fin m,view (RecursiveTable.read x (i.1,j))*view (RecursiveTable.read y (j,i.2)) := by
  rw [execute_value]
  exact PaddedMatrix.execute_correct (fin a) (fin b) (fin c) ht d hd k hn hm hp x y i

theorem pad_bound (ha : 0<a) (hb : 0<b) (k B : ℕ)
    (x : Table (PaddedMatrix.matrix n m) Cell) (hx : BinaryRetainedBounds.Bounded x B) :
    BinaryRetainedBounds.Bounded (BinaryAddressedPadding.pad (t:=t) ha hb k x).value B := by
  intro z
  simp only [BinaryAddressedPadding.pad,BinaryRecursiveTable.tabulate_read,BinaryAddressedPadding.padEntry_value]
  exact PaddedMatrix.pad_bound (power (fin a) k) (power (fin b) k) t n m B x hx _

def constant (d : Base r t (prod (fin a) (fin b)) (prod (fin b) (fin c)) (prod (fin c) (fin a)) ℚ) :=
  BinaryAddressedUniform.constant d+131072*(2*t+1)*(BinaryAddressedWidth.slope a b c r t+1)^2

theorem execute_bits (ha : 0<a) (hb : 0<b) (hc : 0<c) (ht : 0<t)
    (d : Base r t (prod (fin a) (fin b)) (prod (fin b) (fin c)) (prod (fin c) (fin a)) ℚ)
    (M : ℕ) (hM : 1≤M) (hg : (r+t-1)/t≤M) (hAB : a*b≤M) (hBC : b*c≤M) (hCA : c*a≤M)
    (k B : ℕ) (hB : 1≤B) (hn : n≤a^k) (hm : m≤b^k) (hp : p≤c^k)
    (x : Table (PaddedMatrix.matrix n m) Cell) (y : Table (PaddedMatrix.matrix m p) Cell)
    (hx : BinaryRetainedBounds.Bounded x B) (hy : BinaryRetainedBounds.Bounded y B) :
    (execute ha hb hc ht d k hn hp x y).bitSteps≤constant d*(k+B.size+2)^5*M^k := by
  let W := BinaryAddressedWidth.commonWidth a b c r t k
  let P := k+B.size+2
  let S := BinaryAddressedWidth.slope a b c r t+1
  let left := BinaryAddressedPadding.pad (t:=t) ha hb k x
  let right := BinaryAddressedPadding.pad (t:=t) hb hc k y
  let answer := BinaryAddressedRecovery.execute ha hb hc ht d k left.value right.value
  have hfit := BinaryAddressedWidth.common_fits a b c r t k
  have hl := BinaryAddressedPaddingCosts.pad_bits ha hb k W hfit.1 hn hm x
  have hr := BinaryAddressedPaddingCosts.pad_bits hb hc k W hfit.2.1 hm hp y
  have ho := BinaryAddressedPaddingCosts.crop_bits ha hc ht k W hfit.2.2 hn hp answer.value
  have haa := BinaryAddressedUniform.execute_bits ha hb hc ht d M hM hg hAB hBC hCA k B hB
    left.value right.value (pad_bound ha hb k B x hx) (pad_bound hb hc k B y hy)
  have hna : n*p≤(c*a)^k := by simpa only [mul_pow,mul_comm] using Nat.mul_le_mul hn hp
  have hnn : n*p≤M^k := hna.trans (Nat.pow_le_pow_left hCA k)
  have hpa := Nat.pow_le_pow_left hAB k
  have hpb := Nat.pow_le_pow_left hBC k
  have hvol : t*(a*b)^k+t*(b*c)^k+n*p≤(2*t+1)*M^k := by
    nlinarith [Nat.mul_le_mul_left t hpa,Nat.mul_le_mul_left t hpb]
  have hu := BinaryAddressedWidth.unit_bound a b c r t k
  change BinaryAddressedCosts.unit k W≤131072*S^2*(k+2)^4 at hu
  have hP : 1≤P := by dsimp [P];omega
  have hp45 : (k+2)^4≤P^5 :=
    (Nat.pow_le_pow_left (by dsimp [P];omega) 4).trans (Nat.pow_le_pow_right hP (by decide))
  have hextra := Nat.mul_le_mul hvol hu
  have hextra' : (t*(a*b)^k+t*(b*c)^k+n*p)*BinaryAddressedCosts.unit k W≤
      131072*(2*t+1)*S^2*P^5*M^k := by
    calc
      _≤((2*t+1)*M^k)*(131072*S^2*(k+2)^4) := hextra
      _=131072*(2*t+1)*S^2*(k+2)^4*M^k := by ring
      _≤_ := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hp45)
  change left.bitSteps≤_ at hl
  change right.bitSteps≤_ at hr
  change answer.bitSteps≤BinaryAddressedUniform.constant d*P^5*M^k at haa
  change left.bitSteps+right.bitSteps+answer.bitSteps+_≤constant d*P^5*M^k
  dsimp only [constant]
  change _≤(BinaryAddressedUniform.constant d+131072*(2*t+1)*S^2)*P^5*M^k
  nlinarith

theorem legacy_control (ht : 0<t)
    (d : Base r t (prod (fin a) (fin b)) (prod (fin b) (fin c)) (prod (fin c) (fin a)) ℚ)
    (k : ℕ) (hn : n≤a^k) (hp : p≤c^k)
    (x : Table (PaddedMatrix.matrix n m) Cell) (y : Table (PaddedMatrix.matrix m p) Cell) :
    (PaddedMatrix.execute (fin a) (fin b) (fin c) ht d k hn hp x y).control=
      (BinaryRecursiveRecovery.execute ht d k
        (BinaryMatrixPowers.toWords (fin a) (fin b) k
          (PaddedMatrix.pad (power (fin a) k) (power (fin b) k) t n m x).value).value
        (BinaryMatrixPowers.toWords (fin b) (fin c) k
          (PaddedMatrix.pad (power (fin b) k) (power (fin c) k) t m p y).value).value).control+
      88*t*((a*b)^k+(b*c)^k)+40*t*(c*a)^k+40*n*p+80 := by
  rw [PaddedMatrix.execute_control]
  simp only [BinaryMatrixPowers.execute,BinaryMatrixPowers.toWords,BinaryMatrixPowers.fromWords,
    BinaryRecursiveDot.tabulate_control,Finset.sum_const,Finset.card_univ,Fintype.card_prod,
    Fintype.card_fin,powerIndex_card,smul_eq_mul,BinaryMatrixPowers.matrixLayout,copies,
    prod,fin,RecursiveTable.power_size,mul_pow]
  ring

theorem execute_control (ha : 0<a) (hb : 0<b) (hc : 0<c) (ht : 0<t)
    (d : Base r t (prod (fin a) (fin b)) (prod (fin b) (fin c)) (prod (fin c) (fin a)) ℚ)
    (k : ℕ) (hn : n≤a^k) (hp : p≤c^k)
    (x : Table (PaddedMatrix.matrix n m) Cell) (y : Table (PaddedMatrix.matrix m p) Cell) :
    (execute ha hb hc ht d k hn hp x y).control≤
      2*(k+2)*(PaddedMatrix.execute (fin a) (fin b) (fin c) ht d k hn hp x y).control := by
  have hh := BinaryAddressedRecovery.execute_control ha hb hc ht d k
    (BinaryAddressedPadding.pad (t:=t) ha hb k x).value (BinaryAddressedPadding.pad (t:=t) hb hc k y).value
  simp only [BinaryAddressedPadding.pad_value] at hh
  simp only [execute,BinaryAddressedPaddingCosts.pad_control,BinaryAddressedPaddingCosts.crop_control,legacy_control]
  simp only [BinaryAddressedPadding.pad_value]
  ring_nf at hh ⊢
  omega

#print axioms legacy_control
#print axioms execute_control

#print axioms execute_value
#print axioms execute_correct
#print axioms pad_bound
#print axioms execute_bits
end ThinMatrix.BinaryAddressedMatrix
