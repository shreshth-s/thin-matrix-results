import SelectedRootRows
import HalfSourceAdaptivePolynomials

/-! Requested-coefficient contraction has a single cyclic factor, including
all formal degrees, row reads, binary multiplication and control actions. -/
namespace ThinMatrix.HalfSourceSelectedRootCost
open ParameterExecution
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000

def width (F q t W A : ℕ) : ℕ := F+t+q.size+W.size+A.size+3

theorem add_size (a b : ℕ) : (a+b).size≤a.size+b.size+1 := by
  apply Nat.size_le.mpr
  have ha := Nat.lt_size_self a
  have hb := Nat.lt_size_self b
  have h1 : 2^a.size≤2^(a.size+b.size) := Nat.pow_le_pow_right (by decide) (by omega)
  have h2 : 2^b.size≤2^(a.size+b.size) := Nat.pow_le_pow_right (by decide) (by omega)
  rw[pow_succ]
  omega

theorem product_size (q t A : ℕ) :
    (SelectedRootProduct.productMagnitude q t A).size≤t.size+q.size+2*A.size+2 := by
  have h1 := size_mul ((t+1)*q) (A^2)
  have h2 := size_mul (t+1) q
  have h3 := size_succ t
  have h4 := size_pow A 2
  unfold SelectedRootProduct.productMagnitude
  omega

theorem dot_width (F q t W A : ℕ) : CompletedRootProducts.width q t A+1≤8*width F q t W A := by
  have h1 := size_pow A 2
  have h2 := size_mul q (A^2)
  have h3 := size_mul (t+1) (q*A^2)
  have h4 := size_succ t
  have h5 := size_le_self t
  unfold CompletedRootProducts.width width
  omega

theorem scalar_budget (F q t W A : ℕ) (hq : 1≤q) :
    SelectedRootProduct.bitBudget q t W A≤100000*q*(width F q t W A)^4 := by
  let P := width F q t W A
  have hP : 1≤P := by dsimp[P,width];omega
  have ht : t≤P := by dsimp[P,width];omega
  have ht1 : t+1≤P := by dsimp[P,width];omega
  have hd := dot_width F q t W A
  have hprod := product_size q t A
  have htS := size_le_self t
  have hadd := add_size W (SelectedRootProduct.productMagnitude q t A)
  have hmul1 := size_mul t (W*SelectedRootProduct.productMagnitude q t A)
  have hmul2 := size_mul W (SelectedRootProduct.productMagnitude q t A)
  have hsum : (W+SelectedRootProduct.productMagnitude q t A).size+1≤3*P := by dsimp[P,width];omega
  have hsum' : (t*(W*SelectedRootProduct.productMagnitude q t A)).size+1≤3*P := by dsimp[P,width];omega
  have hu1 : BackendScalarBits.backendScalarUnit (W+SelectedRootProduct.productMagnitude q t A).size≤7200*P^2 := by
    unfold BackendScalarBits.backendScalarUnit BackendScalarBits.scalarUnit
    calc
      _ ≤8*(100*(3*P)^2) := by gcongr
      _ = _ := by ring
  have hu2 : BackendScalarBits.backendScalarUnit (t*(W*SelectedRootProduct.productMagnitude q t A)).size≤7200*P^2 := by
    unfold BackendScalarBits.backendScalarUnit BackendScalarBits.scalarUnit
    calc
      _ ≤8*(100*(3*P)^2) := by gcongr
      _ = _ := by ring
  have hb : SelectedRootProduct.bitBudget q t W A≤P*(600*P*q*(8*P)^2+7200*P^2)+P*(7200*P^2) := by
    unfold SelectedRootProduct.bitBudget SelectedRootProduct.termBudget
    gcongr
  have h3 : P^3≤P^4 := Nat.pow_le_pow_right hP (by decide)
  have h3q : P^3≤q*P^4 := h3.trans (Nat.le_mul_of_pos_left _ hq)
  change _≤100000*q*P^4
  nlinarith only [hb,h3q]

theorem scalar_control (F q t W A : ℕ) (hq : 1≤q) :
    SelectedRootProduct.controlBudget q t≤200*q*(width F q t W A)^2 := by
  let P := width F q t W A
  have hP : 1≤P := by dsimp[P,width];omega
  have ht : t≤P := by dsimp[P,width];omega
  have ht1 : t+1≤P := by dsimp[P,width];omega
  have hq1 : q+1≤2*q := by omega
  have hb : SelectedRootProduct.controlBudget q t≤P*(8*P*(2*q)+72)+8+(64*P+7)+3*P+16 := by
    unfold SelectedRootProduct.controlBudget
    gcongr
  have h1 : P≤q*P^2 := (le_self_pow₀ hP (by decide : 2≠0)).trans (Nat.le_mul_of_pos_left _ hq)
  have h0 : 1≤q*P^2 := one_le_mul hq (Nat.one_le_pow _ _ hP)
  change _≤200*q*P^2
  nlinarith only [hb,h1,h0]

theorem rows_budget (F q t B M W A : ℕ) (hq : 1≤q) (hB : 1≤B) :
    M*(B*SelectedRootProduct.bitBudget q t W A)+SelectedRootRows.controlBudget F q t B M≤
      102000*M*B*q*(width F q t W A)^4+8 := by
  let P := width F q t W A
  have hP : 1≤P := by dsimp[P,width];omega
  have hF : F≤P := by dsimp[P,width];omega
  have hb := scalar_budget F q t W A hq
  have hc := scalar_control F q t W A hq
  have hbits : M*(B*SelectedRootProduct.bitBudget q t W A)≤100000*M*B*q*P^4 := by
    calc
      _ ≤M*(B*(100000*q*P^4)) := by gcongr
      _ = _ := by ring
  have hrow : 2*(16*(F*q)+8*F+8)+SelectedRootProduct.controlBudget q t+48≤1000*q*P^4 := by
    have hp1 : P≤q*P^4 := (le_self_pow₀ hP (by decide : 4≠0)).trans (Nat.le_mul_of_pos_left _ hq)
    have hp0 : 1≤q*P^4 := one_le_mul hq (Nat.one_le_pow _ _ hP)
    have hp2 : q*P^2≤q*P^4 := Nat.mul_le_mul_left q (Nat.pow_le_pow_right hP (by decide))
    have hpF : F*q≤q*P^4 := by calc
      _ ≤P*q := Nat.mul_le_mul_right q hF
      _ ≤q*P^4 := by rw[mul_comm];gcongr;exact le_self_pow₀ hP (by decide : 4≠0)
    change _≤1000*q*P^4
    nlinarith only [hc,hp1,hp0,hp2,hpF,hF]
  have hbase : 1≤B*q*P^4 := one_le_mul (one_le_mul hB hq) (Nat.one_le_pow _ _ hP)
  have hcontrol : SelectedRootRows.controlBudget F q t B M≤1040*M*B*q*P^4+8 := by
    unfold SelectedRootRows.controlBudget
    have hmul := Nat.mul_le_mul_left B hrow
    have hh : B*(2*(16*(F*q)+8*F+8)+SelectedRootProduct.controlBudget q t+48)+40≤1040*B*q*P^4 := by nlinarith only [hmul,hbase]
    have := Nat.mul_le_mul_left M hh
    nlinarith only [this]
  change _≤102000*M*B*q*P^4+8
  nlinarith only [hbits,hcontrol,Nat.zero_le (M*B*q*P^4)]

#print axioms add_size
#print axioms product_size
#print axioms dot_width
#print axioms scalar_budget
#print axioms scalar_control
#print axioms rows_budget
end ThinMatrix.HalfSourceSelectedRootCost
