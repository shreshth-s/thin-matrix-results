import HalfSourceBatchFit
import OptimizedFoldedPlan
import HalfSourcePhaseCosts

set_option autoImplicit false
set_option maxHeartbeats 1500000

/-! The exact-half witness's full original-grid fit, for the executable
rounded block/prime programs and every actual prime candidate. This retains
the original T geometry; the smaller encoders never replace T here. -/
namespace ThinMatrix.HalfSourceBatchGeometry
open Filter Real
open HalfSourceBatchFit

 theorem witness_bridge :
    b=HalfSourceParameters.b ∧ eta=HalfSourceParameters.eta ∧
    zeta=HalfSourceParameters.zeta ∧ R=HalfSourceParameters.R ∧ S=HalfSourceParameters.S ∧
    OptimizedFoldedPlan.c=HalfSourceParameters.c ∧
    OptimizedFoldedPlan.theta=HalfSourceParameters.theta := by
  norm_num [b,bNumerator,bDenominator,eta,R,S,zeta,OptimizedFoldedPlan.c,
    OptimizedFoldedPlan.theta,HalfSourceParameters.b,HalfSourceParameters.eta,
    HalfSourceParameters.zeta,HalfSourceParameters.R,HalfSourceParameters.S,
    HalfSourceParameters.c,HalfSourceParameters.theta]

noncomputable def foldExponent (j : ℕ) : ℝ := ((min S j:ℕ):ℝ)*eta
noncomputable def overhead (n : ℕ) : ℝ := (8192:ℝ)^R*(Real.log (n:ℝ))^(4*R)

theorem foldExponent_range (j : ℕ) :
    0 ≤ foldExponent j ∧ foldExponent j ≤ HalfSourceParameters.u := by
  have he : 0 ≤ eta := by norm_num [eta,b,bNumerator,bDenominator,R]
  constructor
  · exact mul_nonneg (Nat.cast_nonneg _) he
  · have h := mul_le_mul_of_nonneg_right
      (show ((min S j:ℕ):ℝ) ≤ (S:ℝ) by exact_mod_cast Nat.min_le_left S j) he
    have hu : (S:ℝ)*eta=HalfSourceParameters.u := by
      norm_num [S,eta,b,bNumerator,bDenominator,R,HalfSourceParameters.u]
    exact h.trans_eq hu

theorem product_bounds (n j d : ℕ) (hn : 3 ≤ n) (hj : j ≤ R)
    (hd : (scale n)^j ≤ d ∧ d ≤ (8*scale n)^j) :
    (n:ℝ)^((j:ℝ)*eta) ≤ d ∧ (d:ℝ) ≤ overhead n*(n:ℝ)^((j:ℝ)*eta) := by
  have hs := scale_bounds n hn
  have hlog := PhaseGeometry.one_le_log_nat n hn
  have hlog0 : 0 ≤ Real.log (n:ℝ) := by linarith
  have hscale : (n:ℝ)^eta ≤ (scale n:ℝ) := by
    exact (le_mul_of_one_le_right (Real.rpow_nonneg (Nat.cast_nonneg n) eta)
      (one_le_pow₀ hlog)).trans hs.1
  have hdR : (scale n:ℝ)^j ≤ (d:ℝ) ∧ (d:ℝ) ≤ (8*(scale n:ℝ))^j := by exact_mod_cast hd
  have h8 : 8*(scale n:ℝ) ≤ 8192*((n:ℝ)^eta*(Real.log (n:ℝ))^4) := by
    nlinarith [mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) eta) (pow_nonneg hlog0 4)]
  have heq : (n:ℝ)^((j:ℝ)*eta)=((n:ℝ)^eta)^j := by
    rw [mul_comm,Real.rpow_mul_natCast (Nat.cast_nonneg n)]
  constructor
  · rw [heq]
    exact (pow_le_pow_left₀ (Real.rpow_nonneg (Nat.cast_nonneg n) eta) hscale j).trans hdR.1
  · calc
      (d:ℝ) ≤ (8*(scale n:ℝ))^j := hdR.2
      _ ≤ (8192*((n:ℝ)^eta*(Real.log (n:ℝ))^4))^j := by gcongr
      _ = (8192:ℝ)^j*(Real.log (n:ℝ))^(4*j)*(n:ℝ)^((j:ℝ)*eta) := by
        rw [heq,mul_pow,mul_pow,pow_mul]; ring
      _ ≤ overhead n*(n:ℝ)^((j:ℝ)*eta) := by
        unfold overhead
        have hc := pow_le_pow_right₀ (show (1:ℝ) ≤ 8192 by norm_num) hj
        have hl := pow_le_pow_right₀ hlog (Nat.mul_le_mul_left 4 hj)
        exact mul_le_mul_of_nonneg_right (mul_le_mul hc hl (by positivity) (by positivity)) (by positivity)

theorem folded_bounds (n : ℕ) (hn : 3 ≤ n) (call : Call n) :
    (n:ℝ)^(foldExponent call.factors.length) ≤ call.folded S ∧
      (call.folded S:ℝ) ≤ overhead n*(n:ℝ)^(foldExponent call.factors.length) :=
  product_bounds n (min S call.factors.length) (call.folded S) hn
    ((Nat.min_le_right _ _).trans call.length_le) (call.folded_bounds S)

theorem dimension_bound (n : ℕ) (hn : 3 ≤ n) (call : Call n) :
    (dimension n call:ℝ) ≤ overheadConstant*(Real.log (n:ℝ))^(4*R)*
      (n:ℝ)^(b+foldExponent call.factors.length) := by
  have hp := PhaseGeometry.pad4_upper (block n*(3*call.folded S))
    (by have := block_pos n; have := folded_pos n hn call; positivity)
  have hpR : (dimension n call:ℝ) ≤ 4*((block n:ℝ)*(3*(call.folded S:ℝ))) := by exact_mod_cast hp
  have hh := (block_bounds n (by omega)).2
  have hd := (folded_bounds n hn call).2
  calc
    (dimension n call:ℝ) ≤ 4*((block n:ℝ)*(3*(call.folded S:ℝ))) := hpR
    _ ≤ 4*((2*(n:ℝ)^b)*(3*(overhead n*(n:ℝ)^(foldExponent call.factors.length)))) := by gcongr
    _ = _ := by
      rw [Real.rpow_add (by exact_mod_cast (show 0<n by omega))]
      unfold overhead overheadConstant
      ring

noncomputable def ringExponent (j : ℕ) : ℝ := ((j-S:ℕ):ℝ)*eta

def outer (n : ℕ) (call : Call n) : ℕ := n*FoldedCounts.foldWidth (3*call.folded S)

theorem ringExponent_range (j : ℕ) (hj : j ≤ R) :
    0 ≤ ringExponent j ∧ ringExponent j ≤ HalfSourceParameters.v := by
  have he : 0 ≤ eta := by norm_num [eta,b,bNumerator,bDenominator,R]
  constructor
  · exact mul_nonneg (Nat.cast_nonneg _) he
  · have h := mul_le_mul_of_nonneg_right
      (show ((j-S:ℕ):ℝ) ≤ ((R-S:ℕ):ℝ) by exact_mod_cast Nat.sub_le_sub_right hj S) he
    have hv : ((R-S:ℕ):ℝ)*eta=HalfSourceParameters.v := by
      norm_num [S,eta,b,bNumerator,bDenominator,R,HalfSourceParameters.v]
    exact h.trans_eq hv

theorem cyclic_bounds (n : ℕ) (hn : 3 ≤ n) (call : Call n) :
    (n:ℝ)^(ringExponent call.factors.length) ≤ call.cyclic S ∧
      (call.cyclic S:ℝ) ≤ overhead n*(n:ℝ)^(ringExponent call.factors.length) :=
  product_bounds n (call.factors.length-S) (call.cyclic S) hn
    ((Nat.sub_le _ _).trans call.length_le) (call.cyclic_bounds S)

theorem dimension_lower_refined (n : ℕ) (hn : 3 ≤ n) (call : Call n) :
    (n:ℝ)^(b+foldExponent call.factors.length) ≤ (dimension n call:ℝ) := by
  have hh := (block_bounds n (by omega)).1
  have hd := (folded_bounds n hn call).1
  have hp := PhaseGeometry.pad4_lower (block n*(3*call.folded S))
  have hmul : block n*call.folded S ≤ dimension n call := by
    have h : block n*call.folded S ≤ block n*(3*call.folded S) := Nat.mul_le_mul_left _ (by omega)
    exact h.trans hp
  rw [Real.rpow_add (by exact_mod_cast (show 0<n by omega))]
  exact (mul_le_mul hh hd (by positivity) (by positivity)).trans (by exact_mod_cast hmul)

theorem overhead_ge_one (n : ℕ) (hn : 3 ≤ n) : 1 ≤ overhead n := by
  exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num))
    (one_le_pow₀ (PhaseGeometry.one_le_log_nat n hn))

theorem outer_bounds (n : ℕ) (hn : 3 ≤ n) (call : Call n) :
    (n:ℝ)^(1+foldExponent call.factors.length/2) ≤ (outer n call:ℝ) ∧
      (outer n call:ℝ) ≤ 4*overhead n*(n:ℝ)^(1+foldExponent call.factors.length/2) := by
  have hd := folded_bounds n hn call
  constructor
  · apply PhaseGeometry.foldedOuterLower n (3*call.folded S) _ (by omega)
    have hr : (call.folded S:ℝ) ≤ (3*call.folded S:ℕ) := by
      push_cast
      nlinarith [show (0:ℝ) ≤ (call.folded S:ℝ) from Nat.cast_nonneg _]
    exact hd.1.trans hr
  · simpa only [outer,Nat.cast_mul] using
      PhaseGeometry.foldedOuter_upper n (call.folded S) (overhead n)
        (foldExponent call.factors.length) hn (folded_pos n hn call)
        (overhead_ge_one n hn) (foldExponent_range _).1 hd.2

theorem block_le_n (n : ℕ) (hn : 2 ≤ n) : block n ≤ n := by
  unfold block ComputableParameters.roundedPower
  rw [ComputableParameters.rootScan_eq_nthRoot bNumerator bDenominator n
    (by norm_num [bDenominator]) (by norm_num [bNumerator,bDenominator]) (by omega)]
  have hp : n^bNumerator < n^bDenominator :=
    Nat.pow_lt_pow_right (by omega) (by norm_num [bNumerator,bDenominator])
  have hr := (Nat.nthRoot_lt_iff (show bDenominator≠0 by norm_num [bDenominator])).mpr hp
  omega

theorem blocks_upper (n : ℕ) (hn : 2 ≤ n) : (blocks n:ℝ) ≤ 2*(n:ℝ)^(1-b) := by
  have hn0 : 0 < (n:ℝ) := by exact_mod_cast (show 0<n by omega)
  have hdiv : (n:ℝ)/(block n:ℝ) ≤ (n:ℝ)^(1-b) := by
    calc
      (n:ℝ)/(block n:ℝ) ≤ (n:ℝ)/(n:ℝ)^b :=
        div_le_div_of_nonneg_left hn0.le (Real.rpow_pos_of_pos hn0 b)
          (block_bounds n (by omega)).1
      _ = _ := by rw [Real.rpow_sub hn0,Real.rpow_one]
  have hb := PhaseGeometry.ceilDiv_cast_le_two_mul_div n (block n) (block_pos n) (block_le_n n hn)
  change (blocks n:ℝ) ≤ _ at hb
  calc
    (blocks n:ℝ) ≤ 2*(n:ℝ)/(block n:ℝ) := hb
    _ = 2*((n:ℝ)/(block n:ℝ)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hdiv (by norm_num)

theorem tileExponent_eq : EntropyBounds.tileExponent OptimizedFoldedPlan.c=HalfSourceParameters.T := by
  rw [witness_bridge.2.2.2.2.2.1]
  unfold EntropyBounds.tileExponent HalfSourceParameters.T HalfSourceParameters.CK
    HalfSourceParameters.entropy RealCertificate.entropy Real.binEntropy
  simp only [Real.log_inv]
  ring

theorem geometry_gap (j : ℕ) :
    (b+foldExponent j)*EntropyBounds.tileExponent OptimizedFoldedPlan.c < 1+foldExponent j/2 := by
  have h := HalfSourcePhaseCosts.geometryAllStages (foldExponent j)
    (foldExponent_range j).1 (foldExponent_range j).2
  unfold HalfSourcePhaseCosts.geometry at h
  rw [tileExponent_eq,witness_bridge.1]
  linarith [HalfSourcePhaseCosts.slack_pos]

/-- The actual rounded L,m grid fits the folded outer dimension, uniformly
over all candidate lists. The fixed signed-window factor three is retained. -/
theorem full_grid_fit : ∀ᶠ n : ℕ in atTop, ∀ call : Call n,
    let m := Nat.clog 4 (block n*(3*call.folded S))
    (OptimizedFoldedPlan.ordinaryLength m).choose m *
      4^(OptimizedFoldedPlan.ordinaryLength m-m) ≤
        n*FoldedCounts.foldWidth (3*call.folded S) := by
  have hfit : ∀ᶠ n : ℕ in atTop, ∀ j : Fin (R+1), ∀ m d : ℕ,
      (4:ℝ)^m ≤ overheadConstant*(Real.log (n:ℝ))^(4*R)*(n:ℝ)^(b+foldExponent j.val) →
      (n:ℝ)^(foldExponent j.val) ≤ d →
      (Nat.ceil (OptimizedFoldedPlan.c*(m:ℝ))).choose m *
        4^(Nat.ceil (OptimizedFoldedPlan.c*(m:ℝ))-m) ≤ n*FoldedCounts.foldWidth d := by
    apply Filter.eventually_all.mpr
    intro j
    apply PhaseGeometry.actualFoldedGridFitsUniformlyEventually OptimizedFoldedPlan.c
      (b+foldExponent j.val) (foldExponent j.val) overheadConstant (4*R)
      (by norm_num [OptimizedFoldedPlan.c]) _ _ (geometry_gap j.val)
    · rw [tileExponent_eq]
      linarith [HalfSourceParameters.TEnclosure.1]
    · unfold overheadConstant; positivity
  filter_upwards [hfit,eventually_ge_atTop (3:ℕ)] with n hfitn hn
  intro call
  let j : Fin (R+1) := ⟨call.factors.length,by have := call.length_le; omega⟩
  have h := hfitn j (Nat.clog 4 (block n*(3*call.folded S))) (3*call.folded S)
  simp only [OptimizedFoldedPlan.ordinaryLength_eq]
  apply h
  · simpa only [dimension,PhaseGeometry.pad4,Nat.cast_pow,Nat.cast_ofNat,j] using dimension_bound n hn call
  · have hf := (folded_bounds n hn call).1
    have hf0 : 0 ≤ (call.folded S:ℝ) := Nat.cast_nonneg _
    simpa only [j,Nat.cast_mul,Nat.cast_ofNat] using hf.trans (show (call.folded S:ℝ) ≤ 3*(call.folded S:ℝ) by linarith)

#print axioms witness_bridge
#print axioms foldExponent_range
#print axioms product_bounds
#print axioms folded_bounds
#print axioms dimension_bound
#print axioms ringExponent_range
#print axioms cyclic_bounds
#print axioms dimension_lower_refined
#print axioms overhead_ge_one
#print axioms outer_bounds
#print axioms block_le_n
#print axioms blocks_upper
#print axioms tileExponent_eq
#print axioms geometry_gap
#print axioms full_grid_fit
end ThinMatrix.HalfSourceBatchGeometry
