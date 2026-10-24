import HalfSourceBatchGeometry
import ComputedPhaseGeometry

/-! Uniform logarithmic metadata for the actual exact-half candidate calls.
The computed block and prime scale are those of the new witness throughout. -/
namespace ThinMatrix.HalfSourceLogGeometry
open Filter Real HalfSourceBatchFit HalfSourceBatchGeometry
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 5000
noncomputable section

def innerPower (n : ℕ) (call : Call n) : ℕ :=
  Nat.clog 4 (block n*(3*call.folded S))

@[simp] theorem dimension_eq (n : ℕ) (call : Call n) :
    dimension n call=4^(innerPower n call) := rfl

def indexConstant : ℝ :=
  (Real.log overheadConstant+(4*R:ℕ)+2*b)/Real.log 4+1

theorem indexConstant_pos : 0 < indexConstant := by
  have hc : 1 ≤ overheadConstant := by
    unfold overheadConstant
    nlinarith [one_le_pow₀ (show (1:ℝ) ≤ 8192 by norm_num) (n:=R)]
  have hlog := Real.log_nonneg hc
  have hb : 0 < b := by norm_num[b,bNumerator,bDenominator]
  have hr : 0 ≤ (4*R:ℕ) := Nat.zero_le _
  unfold indexConstant
  positivity

theorem innerPower_bound (n : ℕ) (hn : 3 ≤ n) (call : Call n) :
    (innerPower n call+1:ℝ) ≤ indexConstant*Real.log (n:ℝ) := by
  have hc : 1 ≤ overheadConstant := by
    unfold overheadConstant
    nlinarith [one_le_pow₀ (show (1:ℝ) ≤ 8192 by norm_num) (n:=R)]
  have hu := dimension_upper n hn call
  rw[dimension_eq,Nat.cast_pow,Nat.cast_ofNat] at hu
  have hh := ComputedPhaseGeometry.logarithmicIndex_bound (innerPower n call)
    (4*R) n overheadConstant (2*b) hn hc hu
  have hl := PhaseGeometry.one_le_log_nat n hn
  dsimp[indexConstant]
  nlinarith

def cyclicLogConstant : ℝ := |Real.log ((8192:ℝ)^R)|+(4*R:ℕ)+HalfSourceParameters.v

theorem cyclic_bound (n : ℕ) (hn : 3 ≤ n) (call : Call n) :
    (call.cyclic S:ℝ) ≤ (8192:ℝ)^R*(Real.log (n:ℝ))^(4*R)*(n:ℝ)^HalfSourceParameters.v := by
  have hu := (cyclic_bounds n hn call).2
  have he := (ringExponent_range call.factors.length call.length_le).2
  have hp := Real.rpow_le_rpow_of_exponent_le
    (show (1:ℝ) ≤ n by exact_mod_cast (show 1 ≤ n by omega)) he
  have hh := mul_le_mul_of_nonneg_left hp (show 0 ≤ overhead n by linarith [overhead_ge_one n hn])
  change (call.cyclic S:ℝ) ≤ overhead n*(n:ℝ)^HalfSourceParameters.v
  exact hu.trans hh

theorem cyclic_log (n : ℕ) (hn : 3 ≤ n) (call : Call n) :
    Real.log (call.cyclic S:ℝ) ≤ cyclicLogConstant*Real.log (n:ℝ) :=
  ComputedPhaseGeometry.generic_scale_log_upper n (call.cyclic S) (4*R)
    ((8192:ℝ)^R) HalfSourceParameters.v hn (by positivity) (cyclic_pos n hn call)
    (cyclic_bound n hn call)

theorem size_from_log (n d : ℕ) (C : ℝ) (hn : 3 ≤ n)
    (hlog : Real.log (d:ℝ) ≤ C*Real.log (n:ℝ)) :
    (d.size:ℝ) ≤ (C/Real.log 2+1)*Real.log (n:ℝ) := by
  have hh := CertificationParameters.size_le_log d
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl := PhaseGeometry.one_le_log_nat n hn
  have hd := div_le_div_of_nonneg_right hlog h2.le
  have he : C*Real.log (n:ℝ)/Real.log 2=(C/Real.log 2)*Real.log (n:ℝ) := by ring
  rw[he] at hd
  nlinarith

theorem cyclic_size (n : ℕ) (hn : 3 ≤ n) (call : Call n) :
    ((call.cyclic S).size:ℝ) ≤ (cyclicLogConstant/Real.log 2+1)*Real.log (n:ℝ) :=
  size_from_log n _ _ hn (cyclic_log n hn call)

def outerLogConstant : ℝ :=
  |Real.log (4*(8192:ℝ)^R)|+(4*R:ℕ)+(1+HalfSourceParameters.u/2)

theorem outer_bound (n : ℕ) (hn : 3 ≤ n) (call : Call n) :
    (outer n call:ℝ) ≤ (4*(8192:ℝ)^R)*(Real.log (n:ℝ))^(4*R)*(n:ℝ)^(1+HalfSourceParameters.u/2) := by
  have hu := (outer_bounds n hn call).2
  have he := (foldExponent_range call.factors.length).2
  have hp := Real.rpow_le_rpow_of_exponent_le
    (show (1:ℝ) ≤ n by exact_mod_cast (show 1 ≤ n by omega)) (show 1+foldExponent call.factors.length/2 ≤ 1+HalfSourceParameters.u/2 by linarith)
  calc
    _  ≤ 4*overhead n*(n:ℝ)^(1+foldExponent call.factors.length/2) := hu
    _  ≤ 4*overhead n*(n:ℝ)^(1+HalfSourceParameters.u/2) := mul_le_mul_of_nonneg_left hp (by unfold overhead; positivity)
    _ = _ := by unfold overhead;ring

theorem outer_log (n : ℕ) (hn : 3 ≤ n) (call : Call n) :
    Real.log (outer n call:ℝ) ≤ outerLogConstant*Real.log (n:ℝ) := by
  have hlo := (outer_bounds n hn call).1
  have hn0 : 0 < (n:ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hpos : 0 < outer n call := by exact_mod_cast (Real.rpow_pos_of_pos hn0 _).trans_le hlo
  exact ComputedPhaseGeometry.generic_scale_log_upper n (outer n call) (4*R)
    (4*(8192:ℝ)^R) (1+HalfSourceParameters.u/2) hn (by positivity) hpos
    (outer_bound n hn call)

theorem outer_size (n : ℕ) (hn : 3 ≤ n) (call : Call n) :
    ((outer n call).size:ℝ) ≤ (outerLogConstant/Real.log 2+1)*Real.log (n:ℝ) :=
  size_from_log n _ _ hn (outer_log n hn call)

theorem uniformly_large (M : ℕ) :
    ∀ᶠ n : ℕ in atTop,∀ call : Call n,M ≤ innerPower n call := by
  have hb : 0 < b := by norm_num[b,bNumerator,bDenominator]
  have ht := (tendsto_rpow_atTop hb).comp tendsto_natCast_atTop_atTop
  have hlarge := ht.eventually (eventually_gt_atTop ((4:ℝ)^M))
  filter_upwards [hlarge,eventually_ge_atTop (3:ℕ)] with n hn hn3
  intro call
  have hD := dimension_lower n hn3 call
  rw[dimension_eq,Nat.cast_pow,Nat.cast_ofNat] at hD
  by_contra hnot
  have hm : innerPower n call ≤ M := by omega
  have hf : (4:ℝ)^(innerPower n call) ≤ (4:ℝ)^M := pow_le_pow_right₀ (by norm_num) hm
  change (4:ℝ)^M < (n:ℝ)^b at hn
  exact (not_lt_of_ge (hD.trans hf)) hn

#print axioms dimension_eq
#print axioms indexConstant_pos
#print axioms innerPower_bound
#print axioms cyclic_bound
#print axioms cyclic_log
#print axioms size_from_log
#print axioms cyclic_size
#print axioms outer_bound
#print axioms outer_log
#print axioms outer_size
#print axioms uniformly_large
end
end ThinMatrix.HalfSourceLogGeometry
