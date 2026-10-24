import HalfSourceHighCounters
import HalfSourceAdaptivePolynomials

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace ThinMatrix.HalfSourceHighPolynomials
open HalfSourceHighCounters

 theorem encoder_unit (L cap A P : ℕ) (hP : 1≤P) (hL : L+1≤P)
    (hc : cap.size+1≤P) (ha : A.size+1≤P) : encoderUnit L cap A≤1000000000000000000*P^7 := by
  have hl : L.size+1≤P := (Nat.add_le_add_right (HalfSourceAdaptivePolynomials.size_le L) 1).trans hL
  have hb : encoderUnit L cap A≤
      10*P^2+2+(P*(8*(100*(2*P)^2)+4)+1+100000*(4*P)^3+8*P+8)+
      8*(100*P^2)+14*P+14+(10000*(3*P)^2*(8*(100*(17*P)^2))*(4*P)+8*(100*(17*P)^2)+5)*
      (70*(3*P)+5*(2*P)*(9*P)+8*(2*P)+7) := by
    unfold encoderUnit BinaryCroppedHighInput.testBudget BinaryHighCost.storedFactor
      BinaryHighCost.encoderFactor BinaryHighCost.runFactor BinaryHighCost.commonWidth
      BinaryCroppedHighEncoder.encoderShape BackendScalarBits.backendScalarUnit BackendScalarBits.scalarUnit
    gcongr <;> omega
  have h0 : 1≤P^7 := Nat.one_le_pow _ _ hP
  have h1 : P≤P^7 := le_self_pow₀ hP (by decide)
  have h2 : P^2≤P^7 := Nat.pow_le_pow_right hP (by decide)
  have h3 : P^3≤P^7 := Nat.pow_le_pow_right hP (by decide)
  have h4 : P^4≤P^7 := Nat.pow_le_pow_right hP (by decide)
  have h5 : P^5≤P^7 := Nat.pow_le_pow_right hP (by decide)
  have h6 : P^6≤P^7 := Nat.pow_le_pow_right hP (by decide)
  nlinarith only [hb,h0,h1,h2,h3,h4,h5,h6]

 theorem box_unit (L q A P : ℕ) (hP : 1≤P) (hL : L+1≤P)
    (hq : q.size+1≤P) (ha : A.size+1≤P) : boxUnit L q A≤10^50*P^13 := by
  have ht := table_width L q A
  have hqlog := BinaryMultiplierAdapter.log2_le_size q
  have halog := BinaryMultiplierAdapter.log2_le_size A
  have hb : boxUnit L q A≤(3*P)^2*((2*P+(2*P)*(6*(2*P+(3*(2*P)+2*(2*P)^2)+1))+(3*P)+
      (5*(3*P)+10+7*(2*P)+9*(2*P)+7+1))*(8*(100*(15*P)^2)+8)+
      295147905179352825856*(4*P)*(104*P)^10+12*P+5+(3*(2*P)+(2*P)^2)) := by
    unfold boxUnit ArrayKeys.highLayerFactor BinaryHighTable.arithmeticUnit fftUnit
      StoredHighDP.guardTests BackendScalarBits.backendScalarUnit BackendScalarBits.scalarUnit
    gcongr <;> omega
  have h0 : 1≤P^13 := Nat.one_le_pow _ _ hP
  have h1 : P≤P^13 := le_self_pow₀ hP (by decide)
  have h2 : P^2≤P^13 := Nat.pow_le_pow_right hP (by decide)
  have h3 : P^3≤P^13 := Nat.pow_le_pow_right hP (by decide)
  have h4 : P^4≤P^13 := Nat.pow_le_pow_right hP (by decide)
  have h5 : P^5≤P^13 := Nat.pow_le_pow_right hP (by decide)
  have h6 : P^6≤P^13 := Nat.pow_le_pow_right hP (by decide)
  have h7 : P^7≤P^13 := Nat.pow_le_pow_right hP (by decide)
  nlinarith only [hb,h0,h1,h2,h3,h4,h5,h6,h7]

 theorem setup_unit (L A P : ℕ) (hP : 1≤P) (hL : L+1≤P) (ha : A.size+1≤P) :
    BinaryCroppedHighBoxes.setupBudget L A≤10000000*P^3 := by
  have halog := BinaryMultiplierAdapter.log2_le_size A
  have hb : BinaryCroppedHighBoxes.setupBudget L A≤10*P^2+6*P*(200*(9*P)^2)+8*(100*(10*P)^2)+8*(10*P)^2+6*P+32 := by
    unfold BinaryCroppedHighBoxes.setupBudget BinaryCroppedHighBoxes.setupWidth
      BackendScalarBits.backendScalarUnit BackendScalarBits.scalarUnit
    gcongr <;> omega
  have h0 : 1≤P^3 := Nat.one_le_pow _ _ hP
  have h1 : P≤P^3 := le_self_pow₀ hP (by decide)
  have h2 : P^2≤P^3 := Nat.pow_le_pow_right hP (by decide)
  nlinarith only [hb,h0,h1,h2]

 def width (L m q : ℕ) := 20*(L+m+q.size+2)

 theorem width_inputs (L m q : ℕ) :
    1≤width L m q ∧ L+1≤width L m q ∧ (m/2).size+1≤width L m q ∧
    (2^(L+m)).size+1≤width L m q ∧ q.size+1≤width L m q ∧
    (BinaryCroppedHighBoxes.magnitude L (2^(L+m))).size+1≤width L m q := by
  have hc := HalfSourceAdaptivePolynomials.size_le (m/2)
  have hm := Nat.div_le_self m 2
  have ha : (2^(L+m)).size=L+m+1 := Nat.size_pow
  have hb := magnitude_width L (2^(L+m))
  unfold width
  omega

 theorem canonical_units (L m q : ℕ) :
    encoderUnit L (m/2) (2^(L+m))≤10^18*(width L m q)^7 ∧
    boxUnit L q (BinaryCroppedHighBoxes.magnitude L (2^(L+m)))≤10^50*(width L m q)^13 ∧
    BinaryCroppedHighBoxes.setupBudget L (2^(L+m))≤10^7*(width L m q)^3 := by
  have hp := width_inputs L m q
  exact ⟨encoder_unit _ _ _ _ hp.1 hp.2.1 hp.2.2.1 hp.2.2.2.1,
    box_unit _ _ _ _ hp.1 hp.2.1 hp.2.2.2.2.1 hp.2.2.2.2.2,
    setup_unit _ _ _ hp.1 hp.2.1 hp.2.2.2.1⟩

#print axioms encoder_unit
#print axioms box_unit
#print axioms setup_unit
#print axioms width_inputs
#print axioms canonical_units
end ThinMatrix.HalfSourceHighPolynomials
