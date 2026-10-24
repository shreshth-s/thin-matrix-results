import HalfSourceBandVolume
import GraphResidualFamilies

/-! Normalize the concrete distinguished-root binary and control counters.
All cyclic coefficients are charged once through C; only logarithmic shape
and scalar-width factors remain in the explicit polynomial. -/
namespace ThinMatrix.HalfSourceRootCounters
open scoped BigOperators
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def width (L m A : ℕ) : ℕ := L+3*m+A.size+4
def unit (L m A : ℕ) : ℕ := 800*(width L m A+1)^2
def test (L m A : ℕ) : ℕ := L*(unit L m A+4)+1+100000*(2*width L m A+2)^3+8*L+8
def locate (L m A : ℕ) : ℕ := L*unit L m A+8*(width L m A)^2
def degree (L m A : ℕ) : ℕ := L*(unit L m A+4)+1+unit L m A+8*(width L m A)^2
def rowPolynomial (L m A : ℕ) : ℕ :=
  2*(L*locate L m A)+10*(width L m A)^2+2*test L m A+
    (m+1)*unit L m A+m*(m+1)*(9*unit L m A)+m*(m+1)*(2*unit L m A)
def bitPolynomial (L m A : ℕ) : ℕ := degree L m A+rowPolynomial L m A

theorem scalar_unit_bound (L m A B : ℕ) (hB : B≤width L m A) :
    BackendScalarBits.backendScalarUnit B≤unit L m A := by
  unfold BackendScalarBits.backendScalarUnit BackendScalarBits.scalarUnit unit
  rw [← Nat.mul_assoc]
  norm_num
  gcongr

theorem powered_size (m A : ℕ) : (4^m*A).size≤2*m+A.size ∧ (2^m*(4^m*A)).size≤3*m+A.size := by
  have h1 := BinaryWalshBounds.natAbs_size_of_le_power_mul ((4^m*A:ℕ):ℤ) (2*m) A
    (by simp only [Int.natAbs_natCast]; rw [pow_mul]; norm_num)
  have h2 := BinaryWalshBounds.natAbs_size_of_le_power_mul ((2^m*(4^m*A):ℕ):ℤ) (3*m) A
    (by simp only [Int.natAbs_natCast]; rw [show 3*m=m+2*m by omega,pow_add,pow_mul]; norm_num; ring_nf; exact le_rfl)
  simpa only [Int.natAbs_natCast] using And.intro h1 h2

theorem small_widths (L m A : ℕ) :
    L.size+1≤width L m A ∧ (m/2).size+1≤width L m A ∧
    (L+1).size+1≤width L m A ∧ (m/2).size+L.size+2≤2*width L m A+2 := by
  have h1 : L.size≤L := Nat.size_le.mpr Nat.lt_two_pow_self
  have h2 : (m/2).size≤ m/2 := Nat.size_le.mpr Nat.lt_two_pow_self
  have h3 : (L+1).size≤L+1 := Nat.size_le.mpr Nat.lt_two_pow_self
  unfold width
  omega

theorem test_bound (L m A : ℕ) : BinaryCroppedHighInput.testBudget L (m/2)≤test L m A := by
  have hw := small_widths L m A
  have hu := scalar_unit_bound L m A (L.size+1) hw.1
  unfold BinaryCroppedHighInput.testBudget test
  gcongr
  omega

theorem locate_bound (L m A : ℕ) : ResidualLayout.locateBudget L≤locate L m A := by
  have hw := (small_widths L m A).1
  have hu := scalar_unit_bound L m A (L.size+1) hw
  unfold ResidualLayout.locateBudget locate
  gcongr

theorem degree_bound (L m A : ℕ) : BinaryResidualDegreeSpace.bitBudget L≤degree L m A := by
  have hw := small_widths L m A
  have hu := scalar_unit_bound L m A (L.size+1) hw.1
  have hu' := scalar_unit_bound L m A ((L+1).size+1) hw.2.2.1
  unfold BinaryResidualDegreeSpace.bitBudget degree
  gcongr
  exact hw.2.2.1

private theorem factor_bound (p C a b x y : ℕ) (hp : 1≤p) (hC : 1≤C) :
    a+p*(b+C*x)+C*y ≤p*C*(a+b+x+y) := by
  have hpc : 1≤p*C := by nlinarith
  have ha : a≤p*C*a := by nlinarith only [Nat.mul_le_mul_right a hpc]
  have hb : p*b≤p*C*b := by nlinarith only [Nat.mul_le_mul_right (p*b) hC]
  have hy : C*y≤p*C*y := by nlinarith only [Nat.mul_le_mul_right (C*y) hp]
  nlinarith only [ha,hb,hy]

theorem row_bits (L m C A : ℕ) (hC : 1≤C) :
    BinaryResidualRootProgram.bitBudget L m m C (m+1) (m/2) A≤
      3^m*C*rowPolynomial L m A := by
  have hw := small_widths L m A
  have hs := powered_size m A
  have hbase := scalar_unit_bound L m A A.size (by unfold width;omega)
  have hn := scalar_unit_bound L m A (4^m*A).size (by unfold width;omega)
  have ho := scalar_unit_bound L m A (2^m*(4^m*A)).size (by unfold width;omega)
  have hl := locate_bound L m A
  have ht := test_bound L m A
  unfold BinaryResidualRootProgram.bitBudget BinaryResidualRootProgram.normalBits
    BinaryResidualLeaf.bitBudget BinaryResidualContraction.nodeBits
  calc
    _ ≤2*(L*locate L m A)+10*(width L m A)^2+
      3^m*(2*test L m A+(m+1)*(C*unit L m A)+m*((m+1)*(C*(9*unit L m A))))+
      m*((m+1)*(C*(2*unit L m A))) := by gcongr; exact hw.2.1
    _ = (2*(L*locate L m A)+10*(width L m A)^2)+
      3^m*(2*test L m A+C*((m+1)*unit L m A+m*(m+1)*(9*unit L m A)))+
      C*(m*(m+1)*(2*unit L m A)) := by ring
    _ ≤3^m*C*((2*(L*locate L m A)+10*(width L m A)^2)+2*test L m A+
      ((m+1)*unit L m A+m*(m+1)*(9*unit L m A))+m*(m+1)*(2*unit L m A)) :=
        factor_bound _ _ _ _ _ _ (Nat.one_le_pow _ _ (by decide)) hC
    _ = _ := by unfold rowPolynomial; ring

theorem entry_bits (L m C A : ℕ) (hC : 1≤C) :
    RetainedResidualFamily.entryBitBudget L m C A≤
      3^(2*(L-m)+m)*C*bitPolynomial L m A := by
  have hd := degree_bound L m A
  have hr := row_bits L m C A hC
  have hp : 1≤3^(2*(L-m)+m)*C := by have := Nat.one_le_pow (2*(L-m)+m) 3 (by decide);nlinarith
  have hdegree : degree L m A≤3^(2*(L-m)+m)*C*degree L m A := by
    simpa using Nat.mul_le_mul_right (degree L m A) hp
  unfold RetainedResidualFamily.entryBitBudget CompleteResidualArray.bitBudget BinaryResidualArray.bitBudget
  calc
    _ ≤degree L m A+3^((L-m)+(L-m))*(3^m*C*rowPolynomial L m A) := by gcongr
    _ = degree L m A+3^(2*(L-m)+m)*C*rowPolynomial L m A := by rw [pow_add];ring
    _ ≤3^(2*(L-m)+m)*C*degree L m A+3^(2*(L-m)+m)*C*rowPolynomial L m A := Nat.add_le_add_right hdegree _
    _ = _ := by unfold bitPolynomial;ring

def controlOutside (L m : ℕ) : ℕ :=
  2*(L*(8*L+66)+20)+38*L+8+(m*((m+1)*(44+40)+12)+2)+24*L+24
def controlInside (L m : ℕ) : ℕ :=
  BinaryResidualLeaf.controlBudget L 1 (m+1)+38*L+14+m*BinaryResidualContraction.nodeControl (m+1) 1 m
def controlPolynomial (L m : ℕ) : ℕ :=
  8*L+16+(controlOutside L m+controlInside L m)+(2*L)*(6*(2*L)+16)+6*(2*L)+54+8+16*m+16

theorem node_control (F C m : ℕ) (hC : 1≤C) :
    BinaryResidualContraction.nodeControl F C m≤C*BinaryResidualContraction.nodeControl F 1 m := by
  have h := Nat.mul_le_mul_right (2*(6*(m+1)+4)+(F*40+8)+20) hC
  unfold BinaryResidualContraction.nodeControl
  nlinarith only [h]

theorem leaf_control (L C F : ℕ) (hC : 1≤C) :
    BinaryResidualLeaf.controlBudget L C F≤C*BinaryResidualLeaf.controlBudget L 1 F := by
  have h := Nat.mul_le_mul_right (12*L+24+16*(L+1)^2+F*41) hC
  unfold BinaryResidualLeaf.controlBudget
  nlinarith only [h]

theorem row_control (L m C : ℕ) (hC : 1≤C) :
    BinaryResidualRootProgram.controlBudget L m m C (m+1)≤
      3^m*C*(controlOutside L m+controlInside L m) := by
  have hl := leaf_control L C (m+1) hC
  have hn := node_control (m+1) C m hC
  have hscale := Nat.mul_le_mul_right (m*((m+1)*40+12)+2) hC
  have houter := Nat.mul_le_mul_right (2*(L*(8*L+66)+20)+38*L+8+24*L+24) hC
  have hinner := Nat.mul_le_mul_right (38*L+14) hC
  have hnormal : BinaryResidualRootProgram.normalControl L m C (m+1)≤
      3^m*C*controlInside L m := by
    unfold BinaryResidualRootProgram.normalControl controlInside
    have hm := Nat.mul_le_mul_left m hn
    have hb : BinaryResidualLeaf.controlBudget L C (m+1)+38*L+14+
        m*BinaryResidualContraction.nodeControl (m+1) C m≤
        C*(BinaryResidualLeaf.controlBudget L 1 (m+1)+38*L+14+
          m*BinaryResidualContraction.nodeControl (m+1) 1 m) := by nlinarith only [hl,hm,hinner]
    exact (Nat.mul_le_mul_left (3^m) hb).trans_eq (by ring)
  have hout : 2*(L*(8*L+66)+20)+38*L+8+
      (m*((m+1)*(C*44+40)+12)+2)+24*L+24≤C*controlOutside L m := by
    unfold controlOutside
    nlinarith only [hscale,houter]
  have hpow := Nat.one_le_pow m 3 (by decide)
  have hp := Nat.mul_le_mul_right (C*controlOutside L m) hpow
  unfold BinaryResidualRootProgram.controlBudget
  nlinarith only [hnormal,hout,hp]

theorem entry_control (L m C : ℕ) (hC : 1≤C) :
    RetainedResidualFamily.entryControlBudget L m C≤
      3^(2*(L-m)+m)*C*controlPolynomial L m := by
  let p := 3^(2*(L-m)+m)*C
  have hp0 : 1≤p := by have := Nat.one_le_pow (2*(L-m)+m) 3 (by decide);dsimp[p];nlinarith
  have hpow1 : 1≤3^m*C := by have := Nat.one_le_pow m 3 (by decide);nlinarith
  have hrow := row_control L m C hC
  have hk : L-m≤L := Nat.sub_le L m
  have hindex : ((L-m)+(L-m))*(6*((L-m)+(L-m))+16)+6*((L-m)+(L-m))+54≤
      (2*L)*(6*(2*L)+16)+6*(2*L)+54 := by nlinarith only [hk]
  have hindex' : ((L-m)+(L-m))*(6*((L-m)+(L-m))+16)+6*((L-m)+(L-m))+54≤
      3^m*C*((2*L)*(6*(2*L)+16)+6*(2*L)+54) :=
    hindex.trans (by simpa only [one_mul] using Nat.mul_le_mul_right ((2*L)*(6*(2*L)+16)+6*(2*L)+54) hpow1)
  have houter := Nat.mul_le_mul_right (8*L+16+8+16*m+16) hp0
  have hinner := Nat.mul_le_mul_left (3^((L-m)+(L-m))) (Nat.add_le_add hrow hindex')
  have he : 3^((L-m)+(L-m))*(3^m*C)=p := by dsimp[p];rw[pow_add];ring
  rw [show 3^((L-m)+(L-m))*(3^m*C*(controlOutside L m+controlInside L m)+
      3^m*C*((2*L)*(6*(2*L)+16)+6*(2*L)+54))=
      (3^((L-m)+(L-m))*(3^m*C))*((controlOutside L m+controlInside L m)+
        ((2*L)*(6*(2*L)+16)+6*(2*L)+54)) by ring,he] at hinner
  unfold RetainedResidualFamily.entryControlBudget CompleteResidualArray.controlBudget BinaryResidualArray.controlBudget
  change _≤p*controlPolynomial L m
  unfold controlPolynomial
  nlinarith only [hinner,houter]

#print axioms node_control
#print axioms leaf_control
#print axioms row_control
#print axioms entry_control

#print axioms scalar_unit_bound
#print axioms powered_size
#print axioms small_widths
#print axioms test_bound
#print axioms locate_bound
#print axioms degree_bound
#print axioms row_bits
#print axioms entry_bits
end ThinMatrix.HalfSourceRootCounters
