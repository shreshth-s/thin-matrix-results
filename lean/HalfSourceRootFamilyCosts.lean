import HalfSourceRootCounters
import HalfSourceActualVolumes

/-! Concrete root-family counters, including every translation pair,
matching degree run, good-mask pair and channel key. -/
namespace ThinMatrix.HalfSourceRootFamilyCosts
open HalfSourceParameters HalfSourceRootCounters
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
attribute [local irreducible] GoodMapEmbedding.goodSlots OptimizedFoldedPlan.ordinaryLength ExactHalfCroppedEmbedding.shifts

theorem family_bits (L m C t G A : ℕ) (hC : 1≤C) :
    RetainedResidualFamily.bitBudget L m C t G A≤
      G^2*ResidualFamilyKeys.channelCount m t*3^(2*(L-m)+m)*C*bitPolynomial L m A := by
  have h := Nat.mul_le_mul_left (G*G*ResidualFamilyKeys.channelCount m t) (entry_bits L m C A hC)
  unfold RetainedResidualFamily.bitBudget
  simpa only [pow_two,mul_assoc] using h

theorem family_control (L m C t G : ℕ) (hC : 1≤C) (hG : 1≤G)
    (ht : 1≤ResidualFamilyKeys.channelCount m t) :
    RetainedResidualFamily.controlBudget L m C t G≤
      G^2*ResidualFamilyKeys.channelCount m t*3^(2*(L-m)+m)*C*(controlPolynomial L m+128) := by
  let H := ResidualFamilyKeys.channelCount m t
  let p := 3^(2*(L-m)+m)*C
  let base := G^2*H*p
  have hp : 1≤p := by have := Nat.one_le_pow (2*(L-m)+m) 3 (by decide);dsimp[p];nlinarith
  have hG2 : 1≤G^2 := Nat.one_le_pow 2 G hG
  have hGH : 1≤G^2*H := one_le_mul hG2 ht
  have hb : 1≤base := one_le_mul hGH hp
  have h0 : G^2*H≤base := by dsimp[base];nlinarith only [Nat.mul_le_mul_left (G^2*H) hp]
  have h1 : G^2≤base := (show G^2≤G^2*H by nlinarith only [Nat.mul_le_mul_left (G^2) ht]).trans h0
  have h2 : G≤base := (show G≤G^2 by nlinarith only [hG]).trans h1
  have he := Nat.mul_le_mul_left (G*G*H) (entry_control L m C hC)
  unfold RetainedResidualFamily.controlBudget
  change G*(G*(H*(RetainedResidualFamily.entryControlBudget L m C+32)+40)+40)+8≤_
  have he' : G*G*H*RetainedResidualFamily.entryControlBudget L m C≤base*controlPolynomial L m := by
    simpa only [base,p,pow_two,mul_assoc] using he
  have hid : G^2*ResidualFamilyKeys.channelCount m t*3^(2*(L-m)+m)*C=base := by dsimp[base,p,H];ring
  rw [hid]
  nlinarith only [he',h0,h1,h2,hb]

def multiplicity (m : ℕ) : ℕ := (ExactHalfSourcePlan.J m)^2*(2*m+1)
def polynomial (L m A : ℕ) : ℕ := multiplicity m*(2*bitPolynomial L m A+2*controlPolynomial L m+400)

theorem multiplicity_positive (m : ℕ) : 1≤ multiplicity m := by
  have h : 1≤ExactHalfSourcePlan.J m := ExactHalfCroppedEmbedding.shifts_nonempty m
  unfold multiplicity
  exact one_le_mul (Nat.one_le_pow 2 _ h) (by omega)

theorem multiplicity_bound (m : ℕ) : multiplicity m≤(64*(m+1)^3)^2*(2*m+1) := by
  have hj : ExactHalfSourcePlan.J m≤64*(m+1)^3 := by
    rw [← ExactHalfSourcePlan.count_eq]
    unfold ExactHalfSourcePlan.count
    split_ifs with hm
    · subst m;norm_num
    · gcongr;omega
  unfold multiplicity
  gcongr

theorem graph_bits (L m C t G A : ℕ) (hC : 1≤C) :
    GraphResidualFamilies.bitBudget L m C t G A≤
      G^2*ResidualFamilyKeys.channelCount m t*3^(2*(L-m)+m)*C*(multiplicity m*(2*bitPolynomial L m A)) := by
  have h := family_bits L m C t G A hC
  unfold GraphResidualFamilies.bitBudget multiplicity
  calc
    _ ≤ExactHalfSourcePlan.J m*(ExactHalfSourcePlan.J m*((2*m+1)*
      (2*(G^2*ResidualFamilyKeys.channelCount m t*3^(2*(L-m)+m)*C*bitPolynomial L m A)))) := by gcongr
    _ = _ := by ring

theorem graph_control (L m C t G : ℕ) (hC : 1≤C) (hG : 1≤G)
    (ht : 1≤ResidualFamilyKeys.channelCount m t) :
    GraphResidualFamilies.controlBudget L m C t G≤
      G^2*ResidualFamilyKeys.channelCount m t*3^(2*(L-m)+m)*C*(multiplicity m*(2*controlPolynomial L m+400)) := by
  let base := G^2*ResidualFamilyKeys.channelCount m t*3^(2*(L-m)+m)*C
  let j := ExactHalfSourcePlan.J m
  let r := 2*m+1
  have hb : 1≤base := by
    apply one_le_mul
    · apply one_le_mul
      · exact one_le_mul (Nat.one_le_pow 2 G hG) ht
      · exact Nat.one_le_pow _ _ (by decide)
    · exact hC
  have hj : 1≤j := ExactHalfCroppedEmbedding.shifts_nonempty m
  have hr : 1≤r := by dsimp[r];omega
  have he := family_control L m C t G hC hG ht
  have hconst : j*(j*(r*40+40)+40)+8≤j^2*r*base*144 := by
    have h0 : j≤j^2*r*base := by
      have hjr : 1≤j*r*base := one_le_mul (one_le_mul hj hr) hb
      nlinarith only [Nat.mul_le_mul_left j hjr]
    have h1 : j^2≤j^2*r*base := by
      have hrb : 1≤r*base := one_le_mul hr hb
      nlinarith only [Nat.mul_le_mul_left (j^2) hrb]
    have h2 : j^2*r≤j^2*r*base := by nlinarith only [Nat.mul_le_mul_left (j^2*r) hb]
    have h3 : 1≤j^2*r*base := one_le_mul (one_le_mul (Nat.one_le_pow 2 j hj) hr) hb
    nlinarith only [h0,h1,h2,h3]
  have hprod := Nat.mul_le_mul_left (j*j*r*2) he
  unfold GraphResidualFamilies.controlBudget GraphResidualFamilies.pairControl
  change j*(j*(r*(2*RetainedResidualFamily.controlBudget L m C t G+40)+8+32)+40)+8≤_
  change _≤base*(multiplicity m*(2*controlPolynomial L m+400))
  have hm : multiplicity m=j^2*r := rfl
  rw [hm]
  change j*j*r*2*RetainedResidualFamily.controlBudget L m C t G≤j*j*r*2*(base*(controlPolynomial L m+128)) at hprod
  nlinarith only [hprod,hconst]

theorem channel_positive (m : ℕ) (hm : 0 < m) :
    1≤ResidualFamilyKeys.channelCount m (OptimizedFoldedPlan.channelLength m) := by
  have ht : 0 < OptimizedFoldedPlan.channelLength m := by
    rw [OptimizedFoldedPlan.channelLength_eq,Nat.ceil_pos]
    have hmR : (0:ℝ)< m := by exact_mod_cast hm
    have htheta : 0<OptimizedFoldedPlan.theta := by norm_num [OptimizedFoldedPlan.theta]
    positivity
  rw [ResidualFamilyKeys.channelCount_sum]
  have h := Finset.single_le_sum (f := fun j => (2*m).choose j) (a:=0)
    (fun j _ => Nat.zero_le _) (Finset.mem_range.mpr ht)
  simpa only [Nat.choose_zero_right] using h

theorem actual_graph (m C A : ℕ) (hm : 0 < m) (hC : 1≤C) :
    GraphResidualFamilies.bitBudget (OptimizedFoldedPlan.ordinaryLength m) m C (OptimizedFoldedPlan.channelLength m)
      (GoodMapEmbedding.goodSlots (OptimizedFoldedPlan.ordinaryLength m) m).card A+
    GraphResidualFamilies.controlBudget (OptimizedFoldedPlan.ordinaryLength m) m C (OptimizedFoldedPlan.channelLength m)
      (GoodMapEmbedding.goodSlots (OptimizedFoldedPlan.ordinaryLength m) m).card≤
      HalfSourceActualVolumes.roots m*C*polynomial (OptimizedFoldedPlan.ordinaryLength m) m A := by
  have hG : 1≤(GoodMapEmbedding.goodSlots (OptimizedFoldedPlan.ordinaryLength m) m).card := by
    have hc := Nat.choose_pos (OptimizedFoldedPlan.ordinaryLength_lower m)
    have hd := GoodMapEmbedding.goodSlots_density (OptimizedFoldedPlan.ordinaryLength m) m
    omega
  have hb := graph_bits (OptimizedFoldedPlan.ordinaryLength m) m C (OptimizedFoldedPlan.channelLength m)
    (GoodMapEmbedding.goodSlots (OptimizedFoldedPlan.ordinaryLength m) m).card A hC
  have hc := graph_control (OptimizedFoldedPlan.ordinaryLength m) m C (OptimizedFoldedPlan.channelLength m)
    (GoodMapEmbedding.goodSlots (OptimizedFoldedPlan.ordinaryLength m) m).card hC hG (channel_positive m hm)
  rw [HalfSourceActualVolumes.roots_eq]
  unfold polynomial
  exact (Nat.add_le_add hb hc).trans_eq (by ring)

#print axioms family_bits
#print axioms family_control
#print axioms multiplicity_positive
#print axioms multiplicity_bound
#print axioms graph_bits
#print axioms graph_control
#print axioms channel_positive
#print axioms actual_graph
end
end ThinMatrix.HalfSourceRootFamilyCosts
