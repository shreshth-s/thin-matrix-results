import BinaryAddressedWidth

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

/-! Denominator recovery and the complete rational-base recursive evaluator,
with binary table addresses consumed by the recovery pass as well. -/
namespace ThinMatrix.BinaryAddressedRecovery
open scoped BigOperators
open BinaryCell BinaryGroupedCoordinates
open PolynomialDegeneration RetainedEqualCopy
open RecursiveTable (Table prod fin)
open BinaryAddressedRecursion BinaryAddressedCosts
variable {a b c r t : ℕ}

def recover (ha : 0<a) (hb : 0<b) (k : ℕ) (d : Cell) (x : Cells t a b k) : Run (Cells t a b k) :=
  BinaryRecursiveTable.tabulate ha hb k (fun i =>
    let input := BinaryRecursiveTable.read k x i
    let quotient := BinaryModularCell.floor d input.value
    ⟨quotient.value,input.bitSteps+quotient.bitSteps,8⟩)

theorem recover_value (ha : 0<a) (hb : 0<b) (k : ℕ) (d : Cell) (x : Cells t a b k) :
    (recover ha hb k d x).value=(BinaryRecursiveRecovery.recover (BinaryRecursiveTable.layout t a b k) d x).value := by
  apply table_ext (BinaryRecursiveTable.layout t a b k)
  intro i
  simp only [recover,BinaryRecursiveTable.tabulate_read,BinaryRecursiveRecovery.recover,
    BinaryRecursiveDot.tabulate_read,BinaryRecursiveTable.read_value]

theorem recover_bits (ha : 0<a) (hb : 0<b) (K W k : ℕ) (h : Fits a b r t K W) (hk : k≤K)
    (d : Cell) (x : Cells t a b k) :
    (recover ha hb k d x).bitSteps≤
      (BinaryRecursiveRecovery.recover (BinaryRecursiveTable.layout t a b k) d x).bitSteps+
        2*t*(a*b)^k*unit K W := by
  let f := fun (i : Fin t×PowerIndex (Fin a×Fin b) k) =>
    let input := BinaryRecursiveTable.read k x i
    let quotient := BinaryModularCell.floor d input.value
    (⟨quotient.value,input.bitSteps+quotient.bitSteps,8⟩ : Run Cell)
  have hh := tabulate_unit ha hb K W k h hk f
  have point (i) : (f i).bitSteps≤(BinaryModularCell.floor d (RecursiveTable.read x i)).bitSteps+unit K W := by
    have hr := read_unit ha hb K W k h hk x i
    simp only [f,BinaryRecursiveTable.read_value]
    omega
  have hs := Finset.sum_le_sum (fun i (_ : i∈Finset.univ) => point i)
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_prod,
    Fintype.card_fin,powerIndex_card,smul_eq_mul] at hs
  change (BinaryRecursiveTable.tabulate ha hb k f).bitSteps≤_
  rw [BinaryRecursiveRecovery.recover,BinaryRecursiveDot.tabulate_bits]
  nlinarith

theorem recover_control (ha : 0<a) (hb : 0<b) (k : ℕ) (d : Cell) (x : Cells t a b k) :
    (recover ha hb k d x).control=48*t*(a*b)^k+8 := by
  simp only [recover,BinaryRecursiveTable.tabulate_control,BinaryRecursiveDot.tabulate_control,
    Finset.sum_const,Finset.card_univ,Fintype.card_prod,Fintype.card_fin,powerIndex_card,
    smul_eq_mul,BinaryRecursiveTable.layout_size]
  ring

def execute (ha : 0<a) (hb : 0<b) (hc : 0<c) (ht : 0<t)
    (d : Base r t (prod (fin a) (fin b)) (prod (fin b) (fin c)) (prod (fin c) (fin a)) ℚ)
    (k : ℕ) (x : Cells t a b k) (y : Cells t b c k) : Run (Cells t c a k) :=
  let prepared := ClearedRecursiveBase.encode d
  let baseDenom := BinaryMultiplierAdapter.encodeInteger ((ClearedRecursiveBase.common d:ℤ)^3)
  let denom := BinaryRecursiveRecovery.power baseDenom.value k
  let product := run ha hb hc ht prepared.value k x y
  let output := recover hc ha k denom.value product.value
  ⟨output.value,prepared.bitSteps+baseDenom.bitSteps+denom.bitSteps+product.bitSteps+output.bitSteps,
    prepared.control+denom.control+product.control+output.control+16⟩

theorem execute_value (ha : 0<a) (hb : 0<b) (hc : 0<c) (ht : 0<t)
    (d : Base r t (prod (fin a) (fin b)) (prod (fin b) (fin c)) (prod (fin c) (fin a)) ℚ)
    (k : ℕ) (x : Cells t a b k) (y : Cells t b c k) :
    (execute ha hb hc ht d k x y).value=(BinaryRecursiveRecovery.execute ht d k x y).value := by
  simp only [execute,BinaryRecursiveRecovery.execute,recover_value,run_value]

theorem execute_overhead (ha : 0<a) (hb : 0<b) (hc : 0<c) (ht : 0<t)
    (d : Base r t (prod (fin a) (fin b)) (prod (fin b) (fin c)) (prod (fin c) (fin a)) ℚ)
    (k : ℕ) (x : Cells t a b k) (y : Cells t b c k) :
    (execute ha hb hc ht d k x y).bitSteps≤(BinaryRecursiveRecovery.execute ht d k x y).bitSteps+
      (RetainedEqualCopyCosts.control r t (a*b) (b*c) (c*a) k+2*t*(c*a)^k)*
        unit k (BinaryAddressedWidth.commonWidth a b c r t k) := by
  let W := BinaryAddressedWidth.commonWidth a b c r t k
  have h := BinaryAddressedWidth.common_fits a b c r t k
  have hp := BinaryAddressedCosts.run_bits ha hb hc ht k W h.1 h.2.1 h.2.2
    (ClearedRecursiveBase.encode d).value k (by rfl) x y
  have hr := recover_bits hc ha k W k h.2.2 (by rfl)
    (BinaryRecursiveRecovery.power (BinaryMultiplierAdapter.encodeInteger ((ClearedRecursiveBase.common d:ℤ)^3)).value k).value
    (run ha hb hc ht (ClearedRecursiveBase.encode d).value k x y).value
  rw [run_value] at hr
  simp only [execute,BinaryRecursiveRecovery.execute]
  rw [run_value]
  change _≤_+_*unit k W
  nlinarith

theorem execute_control (ha : 0<a) (hb : 0<b) (hc : 0<c) (ht : 0<t)
    (d : Base r t (prod (fin a) (fin b)) (prod (fin b) (fin c)) (prod (fin c) (fin a)) ℚ)
    (k : ℕ) (x : Cells t a b k) (y : Cells t b c k) :
    (execute ha hb hc ht d k x y).control≤2*(BinaryRecursiveRecovery.execute ht d k x y).control := by
  have hh := control_bound r t (a*b) (b*c) (c*a) k
  simp only [execute,BinaryRecursiveRecovery.execute,recover_control,BinaryRecursiveRecovery.recover_control,
    BinaryAddressedRecursion.run_control,BinaryRetainedEqualCopy.run_control,
    copies,prod,fin,RecursiveTable.power_size]
  ring_nf at hh ⊢
  omega

#print axioms recover_value
#print axioms recover_bits
#print axioms recover_control
#print axioms execute_value
#print axioms execute_overhead
#print axioms execute_control
end ThinMatrix.BinaryAddressedRecovery
