import HalfSourceRootFamilyCosts

/-! Fixed-degree polynomial overheads for the actual binary root budgets.
The source magnitude is a proved power of two, so it contributes only its
linear bit width to these estimates. -/
namespace ThinMatrix.HalfSourceRootPolynomials
open HalfSourceRootCounters HalfSourceRootFamilyCosts
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

 theorem bit_polynomial (L m A : ℕ) : bitPolynomial L m A≤100000000*(width L m A)^4 := by
  let W := width L m A
  have hW : 1≤W := by dsimp[W,width];omega
  have hL : L≤W := by dsimp[W,width];omega
  have hm : m≤W := by dsimp[W,width];omega
  have hm1 : m+1≤W := by dsimp[W,width];omega
  have hW1 : W+1≤2*W := by omega
  have hW2 : 2*W+2≤4*W := by omega
  have hbound : bitPolynomial L m A≤
    (W*(800*(2*W)^2+4)+1+800*(2*W)^2+8*W^2)+
    (2*(W*(W*(800*(2*W)^2)+8*W^2))+10*W^2+
    2*(W*(800*(2*W)^2+4)+1+100000*(4*W)^3+8*W+8)+
    W*(800*(2*W)^2)+W*W*(9*(800*(2*W)^2))+W*W*(2*(800*(2*W)^2))) := by
    unfold bitPolynomial rowPolynomial degree locate test unit
    gcongr
  have h1 : W≤W^4 := le_self_pow₀ hW (by decide)
  have h2 : W^2≤W^4 := Nat.pow_le_pow_right hW (by decide)
  have h3 : W^3≤W^4 := Nat.pow_le_pow_right hW (by decide)
  have h0 : 1≤W^4 := Nat.one_le_pow 4 W hW
  change _≤100000000*W^4
  nlinarith only [hbound,h1,h2,h3,h0]

theorem control_polynomial (L m : ℕ) : controlPolynomial L m≤100000*(L+m+1)^3 := by
  let W := L+m+1
  have hW : 1≤W := by dsimp[W];omega
  have hL : L≤W := by dsimp[W];omega
  have hL1 : L+1≤W := by dsimp[W];omega
  have hm : m≤W := by dsimp[W];omega
  have hm1 : m+1≤W := by dsimp[W];omega
  have hbound : controlPolynomial L m≤
    8*W+16+
    ((2*(W*(8*W+66)+20)+38*W+8+(W*(W*(44+40)+12)+2)+24*W+24)+
    ((12*W+24+16*W^2+W*(36+41))+38*W+14+
      W*(2*(6*W+4)+(W*(116+40)+8)+20)))+
    (2*W)*(6*(2*W)+16)+6*(2*W)+54+8+16*W+16 := by
    unfold controlPolynomial controlOutside controlInside BinaryResidualLeaf.controlBudget BinaryResidualContraction.nodeControl
    norm_num
    gcongr
  have h1 : W≤W^3 := le_self_pow₀ hW (by decide)
  have h2 : W^2≤W^3 := Nat.pow_le_pow_right hW (by decide)
  have h0 : 1≤W^3 := Nat.one_le_pow 3 W hW
  change _≤100000*W^3
  nlinarith only [hbound,h1,h2,h0]

theorem ordinary_bound (m : ℕ) : OptimizedFoldedPlan.ordinaryLength m≤12*(m+1) := by
  have h := (OptimizedFoldedPlan.rounded_bounds m).2.1
  have hm : (0:ℝ)≤ m := Nat.cast_nonneg m
  have h' : (OptimizedFoldedPlan.ordinaryLength m:ℝ)≤12*((m:ℝ)+1) := by
    norm_num [OptimizedFoldedPlan.c] at h
    linarith
  exact_mod_cast h'

theorem source_polynomial (m : ℕ) :
    polynomial (OptimizedFoldedPlan.ordinaryLength m) m (2^(OptimizedFoldedPlan.ordinaryLength m+m))≤
      100000000000000000000*(m+1)^12 := by
  let L := OptimizedFoldedPlan.ordinaryLength m
  let A := 2^(L+m)
  let W := m+1
  have hW : 1≤W := by dsimp[W];omega
  have hL : L≤12*W := ordinary_bound m
  have hm : m≤W := by dsimp[W];omega
  have hwidth : width L m A≤34*W := by
    unfold width
    dsimp[A]
    rw[Nat.size_pow]
    dsimp[W] at *
    omega
  have hshape : L+m+1≤14*W := by dsimp[W] at *;omega
  have hb := bit_polynomial L m A
  have hc := control_polynomial L m
  have hmult := multiplicity_bound m
  have hrun : 2*m+1≤3*W := by dsimp[W];omega
  have hbound : polynomial L m A≤
      (64*W^3)^2*(3*W)*(2*(100000000*(34*W)^4)+2*(100000*(14*W)^3)+400) := by
    unfold polynomial
    gcongr
    · exact hmult.trans (by gcongr)
    · exact hb.trans (by gcongr)
    · exact hc.trans (by gcongr)
  have h10 : W^10≤W^12 := Nat.pow_le_pow_right hW (by decide)
  have h11 : W^11≤W^12 := Nat.pow_le_pow_right hW (by decide)
  have h7 : W^7≤W^12 := Nat.pow_le_pow_right hW (by decide)
  change polynomial L m A≤100000000000000000000*W^12
  nlinarith only [hbound,h10,h11,h7]

#print axioms bit_polynomial
#print axioms control_polynomial
#print axioms ordinary_bound
#print axioms source_polynomial
end ThinMatrix.HalfSourceRootPolynomials
