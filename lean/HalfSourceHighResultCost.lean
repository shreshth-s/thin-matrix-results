import GraphHighScalarResult
import HalfSourceHighScheduleCost

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
namespace ThinMatrix.HalfSourceHighResultCost
open HalfSourceParameters HalfSourceHighScheduleCost
open HalfSourceAdaptiveFamilyCost (L t)
open GraphHighScalarCollection (H)
noncomputable section

theorem budget_polynomial (K L m t M q : ℕ) (ht : t≤2*m) :
    GraphHighScalarResult.budget K L m t M (HalfSourceHighQueryCost.table L m q) ≤
      100000000000000000000*(width K L m q)^30*
        (K*K+1+M*(SelectedHighQueries.rowBudget L m t (HalfSourceHighQueryCost.table L m q)+32)) := by
  let P := width K L m q
  let A := HalfSourceHighQueryCost.table L m q
  let U := SelectedHighQueries.rowBudget L m t A+32
  let Z := K*K+1+M*U
  have hP : 1≤P := by dsimp[P,width];omega
  have hU : 1≤U := by dsimp[U];omega
  have hZ : 1≤Z := by dsimp[Z];omega
  have hM : M≤Z := by dsimp[Z];nlinarith only[hU]
  have hK : K*K≤Z := by dsimp[Z];omega
  have hpow (a b : ℕ) (hab : a≤b) : P^a≤P^b := Nat.pow_le_pow_right hP hab
  have h0 : 1≤P^30 := one_le_pow₀ hP
  have h1 : P≤P^7 := by simpa using hpow 1 7 (by decide)
  have h07 : 1≤P^7 := one_le_pow₀ hP
  have hmP : m+1≤P := by dsimp[P,width];omega
  have hj := HalfSourceRootFamilyCosts.multiplicity_bound m
  have hH : H m≤8192*P^7 := by
    change (ExactHalfSourcePlan.J m)^2*(2*m+1)≤_ at hj
    calc
      _ = (ExactHalfSourcePlan.J m)^2*(2*m+1) := by unfold H;ring
      _ ≤ (64*(m+1)^3)^2*(2*m+1) := hj
      _ ≤ (64*P^3)^2*(2*P) := by gcongr;omega
      _ = _ := by ring
  have hw := HalfSourceHighQueryCost.query_width L m t q ht
  have hsmall : HalfSourceHighQueryCost.width L m q≤P := by dsimp[P,width,HalfSourceHighQueryCost.width];omega
  have hsize : (H m*CroppedHighQueries.queryMagnitude m t A).size+1≤8213*P^7 := by
    have hh := ParameterExecution.size_mul (H m) (CroppedHighQueries.queryMagnitude m t A)
    have hs := ParameterExecution.size_le_self (H m)
    change (CroppedHighQueries.queryMagnitude m t A).size≤_ at hw
    nlinarith only[hh,hs,hw,hH,hsmall,h1,h07]
  have hunit : BackendScalarBits.backendScalarUnit (H m*CroppedHighQueries.queryMagnitude m t A).size≤
      100000000000*P^14 := by
    unfold BackendScalarBits.backendScalarUnit BackendScalarBits.scalarUnit
    calc
      _ ≤ 8*(100*(8213*P^7)^2) := by gcongr
      _ = 53962695200*P^14 := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ (by decide)
  have hHU : H m*BackendScalarBits.backendScalarUnit (H m*CroppedHighQueries.queryMagnitude m t A).size≤
      1000000000000000*P^30 := by
    calc
      _ ≤ (8192*P^7)*(100000000000*P^14) := Nat.mul_le_mul hH hunit
      _ = 819200000000000*P^21 := by ring
      _ ≤ 1000000000000000*P^30 := Nat.mul_le_mul (by decide) (hpow 21 30 (by decide))
  have hread : GraphHighScalarSchedule.readBudget K≤100*P^3 := by
    have hh : GraphHighScalarSchedule.readBudget K≤16*P^2+64*P^3 := by
      unfold GraphHighScalarSchedule.readBudget;gcongr <;> dsimp[P,width] <;> omega
    nlinarith only[hh,hpow 2 3 (by decide)]
  have hmc : 112*H m+143≤1000000*P^30 := by
    have hh := hpow 7 30 (by decide)
    omega
  have hpc : 48*H m+72+(H m+4)*GraphHighScalarSchedule.readBudget K≤10000000*P^30 := by
    have hh : (H m+4)*GraphHighScalarSchedule.readBudget K≤(8192*P^7+4*P^7)*(100*P^3) := by
      exact Nat.mul_le_mul (by omega) hread
    have he : (8192*P^7+4*P^7)*(100*P^3)=819600*P^10 := by ring
    rw[he] at hh
    have h7 := hpow 7 30 (by decide)
    have h10 := hpow 10 30 (by decide)
    omega
  have hold := HalfSourceHighScheduleCost.budget_polynomial K L m t M A q
  have hold' : GraphHighScalarSchedule.budget K L m t M A≤100000000*P^30*Z := by
    change GraphHighScalarSchedule.budget K L m t M A≤100000000*P^10*Z at hold
    exact hold.trans (Nat.mul_le_mul_right Z (Nat.mul_le_mul_left 100000000 (hpow 10 30 (by decide))))
  have hquery : M*(H m*BackendScalarBits.backendScalarUnit (H m*CroppedHighQueries.queryMagnitude m t A).size)≤
      1000000000000000*P^30*Z := by
    calc
      _ ≤ Z*(1000000000000000*P^30) := Nat.mul_le_mul hM hHU
      _ = _ := by ring
  have hcontrol : M*(112*H m+143)≤1000000*P^30*Z := by
    calc
      _ ≤ Z*(1000000*P^30) := Nat.mul_le_mul hM hmc
      _ = _ := by ring
  have hpairs : (K*K)*(48*H m+72+(H m+4)*GraphHighScalarSchedule.readBudget K)≤10000000*P^30*Z := by
    calc
      _ ≤ Z*(10000000*P^30) := Nat.mul_le_mul hK hpc
      _ = _ := by ring
  have hbase : 1≤P^30*Z := one_le_mul h0 hZ
  change GraphHighScalarResult.budget K L m t M A≤100000000000000000000*P^30*Z
  unfold GraphHighScalarResult.budget
  nlinarith only[hold',hquery,hcontrol,hpairs,hbase]

def constant : ℝ := 800000000000000000000*(1+HalfSourceHighQueryCost.constant)

theorem budget_bound (N m M q : ℕ) (hm : 0 < m)
    (hfit : ThinProductCosts.gridSide (L m) m ≤ N) :
    let K := TilingCosts.bandCount N (ThinMatrixBackend.tileWidth (L m) m)
    (GraphHighScalarResult.budget K (L m) m (t m) M (HalfSourceHighQueryCost.table (L m) m q):ℝ) ≤
      constant*(width K (L m) m q:ℝ)^37*
        ((N:ℝ)^2*(((4:ℝ)^m)^(-G))+(M:ℝ)*(((4:ℝ)^m)^q2)) := by
  let K := TilingCosts.bandCount N (ThinMatrixBackend.tileWidth (L m) m)
  let P := (width K (L m) m q:ℝ)
  let U := (SelectedHighQueries.rowBudget (L m) m (t m) (HalfSourceHighQueryCost.table (L m) m q)+32:ℕ)
  have hP : 1 ≤ P := by dsimp[P];exact_mod_cast (show 1 ≤ width K (L m) m q by unfold width;omega)
  have hmP : (m+1:ℝ) ≤ P := by dsimp[P,width];push_cast;have := Nat.cast_nonneg (α:=ℝ) (L m);have := Nat.cast_nonneg (α:=ℝ) q.size;have := Nat.cast_nonneg (α:=ℝ) ((K*K).size);linarith
  have hw : (HalfSourceHighQueryCost.width (L m) m q:ℝ) ≤ P := by dsimp[P];exact_mod_cast (show HalfSourceHighQueryCost.width (L m) m q ≤ width K (L m) m q by unfold width HalfSourceHighQueryCost.width;omega)
  have hc : 0 ≤ HalfSourceHighQueryCost.constant := by unfold HalfSourceHighQueryCost.constant;positivity
  have hrow := HalfSourceHighQueryCost.row_bound m q hm
  have hrow' : (U:ℝ) ≤ HalfSourceHighQueryCost.constant*P^6*(((4:ℝ)^m)^q2) := by
    calc
      _ ≤ HalfSourceHighQueryCost.constant*(m+1:ℝ)*(HalfSourceHighQueryCost.width (L m) m q:ℝ)^5*(((4:ℝ)^m)^q2) := hrow
      _ ≤ HalfSourceHighQueryCost.constant*P*P^5*(((4:ℝ)^m)^q2) := by gcongr
      _ = _ := by ring
  have hpairs := band_pairs N m hm hfit
  have hbudget := budget_polynomial K (L m) m (t m) M q ((OptimizedFoldedPlan.channelLength_upper m).trans (by omega))
  have hbudgetR : (GraphHighScalarResult.budget K (L m) m (t m) M (HalfSourceHighQueryCost.table (L m) m q):ℝ) ≤
    100000000000000000000*P^30*((K:ℝ)^2+1+(M:ℝ)*(U:ℝ)) := by
    dsimp[P]
    exact_mod_cast (show GraphHighScalarResult.budget K (L m) m (t m) M (HalfSourceHighQueryCost.table (L m) m q) ≤ 100000000000000000000*(width K (L m) m q)^30*(K^2+1+M*U) by simpa only[pow_two,U] using hbudget)
  have h31 : P^31 ≤ P^37 := pow_le_pow_right₀ hP (by decide)
  have h36 : P^36 ≤ P^37 := pow_le_pow_right₀ hP (by decide)
  have hleft : 100000000000000000000*P^30*(8*(N:ℝ)^2*(m+1:ℝ)*(((4:ℝ)^m)^(-G))) ≤
      800000000000000000000*P^37*((N:ℝ)^2*(((4:ℝ)^m)^(-G))) := by
    calc
      _ ≤ 100000000000000000000*P^30*(8*(N:ℝ)^2*P*(((4:ℝ)^m)^(-G))) := by gcongr
      _ = 800000000000000000000*P^31*((N:ℝ)^2*(((4:ℝ)^m)^(-G))) := by ring
      _ ≤ _ := by gcongr
  have hright : 100000000000000000000*P^30*((M:ℝ)*(HalfSourceHighQueryCost.constant*P^6*(((4:ℝ)^m)^q2))) ≤
      100000000000000000000*HalfSourceHighQueryCost.constant*P^37*((M:ℝ)*(((4:ℝ)^m)^q2)) := by
    calc
      _ = 100000000000000000000*HalfSourceHighQueryCost.constant*P^36*((M:ℝ)*(((4:ℝ)^m)^q2)) := by ring
      _ ≤ _ := by gcongr
  calc
    _ ≤ 100000000000000000000*P^30*((K:ℝ)^2+1+(M:ℝ)*(U:ℝ)) := hbudgetR
    _ ≤ 100000000000000000000*P^30*(8*(N:ℝ)^2*(m+1:ℝ)*(((4:ℝ)^m)^(-G))+(M:ℝ)*(HalfSourceHighQueryCost.constant*P^6*(((4:ℝ)^m)^q2))) := by gcongr
    _ = 100000000000000000000*P^30*(8*(N:ℝ)^2*(m+1:ℝ)*(((4:ℝ)^m)^(-G)))+100000000000000000000*P^30*((M:ℝ)*(HalfSourceHighQueryCost.constant*P^6*(((4:ℝ)^m)^q2))) := by ring
    _ ≤ 800000000000000000000*P^37*((N:ℝ)^2*(((4:ℝ)^m)^(-G)))+100000000000000000000*HalfSourceHighQueryCost.constant*P^37*((M:ℝ)*(((4:ℝ)^m)^q2)) := add_le_add hleft hright
    _ ≤ _ := by
      change _ ≤ constant*P^37*_
      unfold constant
      nlinarith only [mul_nonneg hc (show 0 ≤ P^37*((N:ℝ)^2*(((4:ℝ)^m)^(-G))) by positivity),
        show 0 ≤ P^37*((M:ℝ)*(((4:ℝ)^m)^q2)) by positivity,
        mul_nonneg hc (show 0 ≤ P^37*((M:ℝ)*(((4:ℝ)^m)^q2)) by positivity)]

#print axioms budget_bound
#print axioms budget_polynomial
end
end ThinMatrix.HalfSourceHighResultCost
