import GraphHighPreparation
import HalfSourceHighPolynomials
import HalfSourceRootFamilyCosts

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace ThinMatrix.HalfSourceHighGraphCost
open ExactHalfSourcePlan RetainedHighSources HalfSourceHighCounters HalfSourceHighPolynomials
noncomputable section

 theorem side_budget (L m t q cap A : ℕ) (hq : 1≤q) :
    2*sideBudget L m t q cap A+16≤
      100*(J m)^2*(2*m+1)*q*HighBaseEncoder.baseCount L m t*(encoderUnit L cap A+1) := by
  let F := q*HighBaseEncoder.baseCount L m t*(encoderUnit L cap A+1)
  let r := 2*m+1
  have hF : 1≤F := one_le_mul (one_le_mul hq (base_pos L m t)) (by omega)
  have hc : BinaryCroppedHighEncoder.totalBudget L m t q cap A≤F := by
    have hh := encoder_budget L m t q cap A hq
    dsimp[F]
    nlinarith
  have hJ := ExactHalfCroppedEmbedding.shifts_nonempty m
  have hr : 1≤r := by dsimp[r];omega
  have h1 : 1≤(J m)^2*r*F := one_le_mul (one_le_mul (Nat.one_le_pow 2 (J m) hJ) hr) hF
  have h2 : (J m)^2≤(J m)^2*r*F := by
    simpa only [Nat.mul_assoc] using Nat.le_mul_of_pos_right _ (one_le_mul hr hF)
  have h3 : J m≤(J m)^2*r*F := by
    have hh := Nat.mul_le_mul_left (J m) (one_le_mul (one_le_mul hJ hr) hF)
    nlinarith only[hh]
  have h4 : (J m)^2*r≤(J m)^2*r*F := Nat.le_mul_of_pos_right _ hF
  have hb := Nat.mul_le_mul_left ((J m)^2*r) hc
  unfold sideBudget
  dsimp only[F,r] at *
  nlinarith only[hb,h1,h2,h3,h4]

 theorem tables_budget (L m t q K A : ℕ) (hq : 1≤q) (hK : 1≤K) :
    GraphHighPreparation.tablesBudget L m t q K A≤
      100*K^2*(J m)^2*(2*m+1)*q*HighBaseEncoder.baseCount L m t*
        (boxUnit L q (BinaryCroppedHighBoxes.magnitude L A)+1) := by
  let F := q*HighBaseEncoder.baseCount L m t*(boxUnit L q (BinaryCroppedHighBoxes.magnitude L A)+1)
  let r := 2*m+1
  have hF : 1≤F := one_le_mul (one_le_mul hq (base_pos L m t)) (by omega)
  have hc : BinaryHighTable.preparationBudget L m t q (BinaryCroppedHighBoxes.magnitude L A)≤F := by
    have hh := box_budget L m t q (BinaryCroppedHighBoxes.magnitude L A) hq
    dsimp[F]
    nlinarith
  have hJ := ExactHalfCroppedEmbedding.shifts_nonempty m
  have hr : 1≤r := by dsimp[r];omega
  have h1 : K≤K^2*(J m)^2*r*F := by
    have hh := Nat.mul_le_mul_left K (one_le_mul (one_le_mul (one_le_mul hK (Nat.one_le_pow 2 (J m) hJ)) hr) hF)
    nlinarith only[hh]
  have h2 : K^2≤K^2*(J m)^2*r*F := by
    simpa only [Nat.mul_assoc] using Nat.le_mul_of_pos_right _ (one_le_mul (one_le_mul (Nat.one_le_pow 2 (J m) hJ) hr) hF)
  have h3 : K^2*J m≤K^2*(J m)^2*r*F := by
    have hh := Nat.mul_le_mul_left (K^2*J m) (one_le_mul (one_le_mul hJ hr) hF)
    nlinarith only[hh]
  have h4 : K^2*(J m)^2≤K^2*(J m)^2*r*F := by
    nlinarith only [Nat.le_mul_of_pos_right (K^2*(J m)^2) (one_le_mul hr hF)]
  have h5 : K^2*(J m)^2*r≤K^2*(J m)^2*r*F := Nat.le_mul_of_pos_right _ hF
  have hb := Nat.mul_le_mul_left (K^2*(J m)^2*r) hc
  unfold GraphHighPreparation.tablesBudget
  dsimp only[F,r] at *
  nlinarith only[hb,h1,h2,h3,h4,h5]

 theorem budget_polynomial (L m t q K : ℕ) (hq : 1≤q) (hK : 1≤K) :
    GraphHighPreparation.budget L m t q K≤
      10^60*q*(m+1)^7*(width L m q)^13*
        (K*HighBaseEncoder.baseCount L m t+K^2*HighBaseEncoder.baseCount L m t) := by
  have hs := side_budget L m t q (m/2) (2^(L+m)) hq
  have ht := tables_budget L m t q K (2^(L+m)) hq hK
  have hu := canonical_units L m q
  have hj := HalfSourceRootFamilyCosts.multiplicity_bound m
  have hp := (width_inputs L m q).1
  have hpow7 : (width L m q)^7≤(width L m q)^13 := Nat.pow_le_pow_right hp (by decide)
  have hpow3 : (width L m q)^3≤(width L m q)^13 := Nat.pow_le_pow_right hp (by decide)
  have hpow0 : 1≤(width L m q)^13 := Nat.one_le_pow _ _ hp
  have he : encoderUnit L (m/2) (2^(L+m))+1≤(10^18+1)*(width L m q)^13 := by nlinarith[hu.1]
  have hb : boxUnit L q (BinaryCroppedHighBoxes.magnitude L (2^(L+m)))+1≤(10^50+1)*(width L m q)^13 := by nlinarith[hu.2.1]
  have hm : (J m)^2*(2*m+1)≤8192*(m+1)^7 := by
    have hh := HalfSourceRootFamilyCosts.multiplicity_bound m
    have hr : 2*m+1≤2*(m+1) := by omega
    calc
      _ ≤(64*(m+1)^3)^2*(2*(m+1)) := by
        exact hh.trans (by gcongr)
      _ = _ := by ring
  have hse : K*(2*sideBudget L m t q (m/2) (2^(L+m))+16)≤
      K*100*(8192*(m+1)^7)*q*HighBaseEncoder.baseCount L m t*((10^18+1)*(width L m q)^13) := by
    have hh := Nat.mul_le_mul_left K hs
    have hh2 := Nat.mul_le_mul (Nat.mul_le_mul_left (K*100*q*HighBaseEncoder.baseCount L m t) hm) he
    nlinarith only[hh,hh2]
  have htb : GraphHighPreparation.tablesBudget L m t q K (2^(L+m))≤
      100*K^2*(8192*(m+1)^7)*q*HighBaseEncoder.baseCount L m t*((10^50+1)*(width L m q)^13) := by
    have hh2 := Nat.mul_le_mul (Nat.mul_le_mul_left (100*K^2*q*HighBaseEncoder.baseCount L m t) hm) hb
    nlinarith only[ht,hh2]
  have hset : BinaryCroppedHighBoxes.setupBudget L (2^(L+m))≤10^7*(width L m q)^13 := hu.2.2.trans (by gcongr)
  let Z := q*(m+1)^7*(width L m q)^13*(K*HighBaseEncoder.baseCount L m t+K^2*HighBaseEncoder.baseCount L m t)
  have hZ : (width L m q)^13≤Z := by
    have hb0 : 1≤K*HighBaseEncoder.baseCount L m t+K^2*HighBaseEncoder.baseCount L m t := by nlinarith[base_pos L m t]
    have hmult := one_le_mul (one_le_mul hq (Nat.one_le_pow 7 (m+1) (by omega))) hb0
    dsimp[Z]
    nlinarith[Nat.mul_le_mul_left ((width L m q)^13) hmult]
  have hZ1 : 1≤Z := hpow0.trans hZ
  unfold GraphHighPreparation.budget
  dsimp only[Z] at hZ hZ1 ⊢
  nlinarith only[hse,htb,hset,hZ,hZ1]

#print axioms side_budget
#print axioms tables_budget
#print axioms budget_polynomial
end
end ThinMatrix.HalfSourceHighGraphCost
