import PipelineBitBounds
import ReductionCosts
import ComputedPhaseGeometry
import ThinMatrixBackend
import BinaryArrayFFT
import AdaptiveQueryBitBounds
import BackendNumeratorBounds
import BinaryMultiplierAdapter

/-!
# Binary widths propagated from the original polynomially bounded inputs

The natural binary length of n is the logarithmic size parameter. Actual
rounded tensor parameters and every trial cyclic modulus are bounded from
the proved phase geometry. The retained HIGH multiplication operands are
read from their actual materialized encoder, with bounds propagated from
the original arrays through unnormalized Walsh sources. Factorial setup
registers receive a quadratic, rather than linear, logarithmic budget.
-/
namespace ThinMatrix.AdaptiveBitBounds
open scoped BigOperators
open CyclicRing CoefficientBounds WalshEmbedding ThinMatrixBackend GoodMapEmbedding
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

theorem nat_le_pow_size (n : ℕ) : n ≤ 2^n.size := (Nat.lt_size_self n).le

theorem original_power_bound (n degree A : ℕ) (hA : A ≤ n^degree) :
    A ≤ 2^(degree*n.size) := by
  calc
    _ ≤ (2^n.size)^degree := hA.trans (Nat.pow_le_pow_left (nat_le_pow_size n) degree)
    _ = _ := by rw [←pow_mul]; congr 1; exact Nat.mul_comm _ _

theorem natAbs_size_of_pow_bound (z : ℤ) (B : ℕ) (hz : z.natAbs ≤ 2^B) :
    z.natAbs.size ≤ B+1 := by
  exact (Nat.size_le_size hz).trans_eq Nat.size_pow

theorem real_log_le_size (n : ℕ) (hn : 0<n) : Real.log (n:ℝ) ≤ n.size := by
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  have hp : (n:ℝ) ≤ (2:ℝ)^n.size := by exact_mod_cast nat_le_pow_size n
  have hlog := Real.log_le_log hnR hp
  rw [Real.log_pow] at hlog
  have htwo : Real.log (2:ℝ) ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at h ⊢
    exact h
  exact hlog.trans (by nlinarith [show (0:ℝ) ≤ n.size from Nat.cast_nonneg n.size])

/-- Fixed constants are allowed to depend on the prime padding degree. -/
def indexConstant (k : ℕ) : ℕ := Nat.ceil (ReductionCosts.Overhead.indexMajor k)
def lengthConstant (k : ℕ) : ℕ :=
  Nat.ceil ((RealCertificate.c+2)*ReductionCosts.Overhead.indexMajor k)
def cyclicConstant (k : ℕ) : ℕ :=
  4*AlignedCertificate.R+k*AlignedCertificate.R+1

theorem actual_innerPower_le_size (n k : ℕ) (hn : 3 ≤ n)
    (call : PhaseGeometry.PhaseCall AlignedCertificate.R
      (PhaseGeometry.primeScale n AsymptoticCosts.eta k)) :
    PhaseGeometry.innerPower n call AlignedCertificate.S ≤ indexConstant k*n.size := by
  have h := ReductionCosts.Overhead.actual_innerPower_add_one_le_log n k hn call
  have hlog := real_log_le_size n (by omega)
  have hM : (0:ℝ) ≤ ReductionCosts.Overhead.indexMajor k := by
    unfold ReductionCosts.Overhead.indexMajor
    positivity
  have hceil : ReductionCosts.Overhead.indexMajor k ≤ (indexConstant k:ℝ) := by
    exact Nat.le_ceil _
  have h' : (PhaseGeometry.innerPower n call AlignedCertificate.S:ℝ) ≤ (indexConstant k:ℝ)*(n.size:ℝ) := by
    have hmul := mul_le_mul_of_nonneg_left hlog hM
    have hc := mul_le_mul_of_nonneg_right hceil (Nat.cast_nonneg n.size)
    linarith
  exact_mod_cast h'

theorem actual_roundedLength_le_size (n k : ℕ) (hn : 3 ≤ n)
    (call : PhaseGeometry.PhaseCall AlignedCertificate.R
      (PhaseGeometry.primeScale n AsymptoticCosts.eta k)) :
    Nat.ceil (RealCertificate.c*(PhaseGeometry.innerPower n call AlignedCertificate.S:ℝ)) ≤ lengthConstant k*n.size := by
  have h := ReductionCosts.Overhead.actual_roundedLength_le_log n k hn call
  have hlog := real_log_le_size n (by omega)
  have hM : (0:ℝ) ≤ (RealCertificate.c+2)*ReductionCosts.Overhead.indexMajor k := by
    have hc : 0 ≤ RealCertificate.c := by norm_num [RealCertificate.c]
    have hm : 0 ≤ ReductionCosts.Overhead.indexMajor k := by
      unfold ReductionCosts.Overhead.indexMajor
      positivity
    positivity
  have hceil : (RealCertificate.c+2)*ReductionCosts.Overhead.indexMajor k ≤ (lengthConstant k:ℝ) := Nat.le_ceil _
  have h' : (Nat.ceil (RealCertificate.c*(PhaseGeometry.innerPower n call AlignedCertificate.S:ℝ)):ℝ) ≤ (lengthConstant k:ℝ)*(n.size:ℝ) := by
    have hmul := mul_le_mul_of_nonneg_left hlog hM
    have hc := mul_le_mul_of_nonneg_right hceil (Nat.cast_nonneg n.size)
    linarith
  exact_mod_cast h'

/-- The actual ceiling cutoff satisfies the required physical bound. -/
theorem rounded_cutoff_le (m : ℕ) : Nat.ceil (2*RealCertificate.theta*(m:ℝ)) ≤ 2*m := by
  apply Nat.ceil_le.mpr
  have ht : RealCertificate.theta ≤ 1 := by norm_num [RealCertificate.theta]
  have hm : (0:ℝ) ≤ m := Nat.cast_nonneg m
  push_cast
  nlinarith

/-- Every adaptive cyclic modulus is polynomially bounded uniformly over
all candidate choices. This loose polynomial is used only for bit sizes. -/
theorem actual_cyclic_le_pow_size (n k : ℕ) (hn : 3 ≤ n)
    (call : PhaseGeometry.PhaseCall AlignedCertificate.R
      (PhaseGeometry.primeScale n AsymptoticCosts.eta k)) :
    call.cyclic AlignedCertificate.S ≤ 2^(cyclicConstant k*n.size) := by
  have h := PhaseGeometry.actual_cyclic_terminal_bound n k hn call
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hn0 : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hlog : Real.log (n:ℝ) ≤ n := by
    have hl := Real.log_le_sub_one_of_pos hn0
    linarith
  have hlog0 : 0 ≤ Real.log (n:ℝ) := Real.log_nonneg hn1
  have hv : AsymptoticCosts.v ≤ 1 := by norm_num [AsymptoticCosts.v,AlignedCertificate.v,AlignedCertificate.eta,AlignedCertificate.b,AlignedCertificate.S,AlignedCertificate.R]
  have hpow : (n:ℝ)^AsymptoticCosts.v ≤ n := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hn1 hv
  have hpoly : (call.cyclic AlignedCertificate.S:ℝ) ≤ (16:ℝ)^AlignedCertificate.R*(n:ℝ)^(k*AlignedCertificate.R+1) := by
    apply h.trans
    unfold PhaseGeometry.phaseOverhead
    calc
      _ ≤ (16:ℝ)^AlignedCertificate.R*(n:ℝ)^(k*AlignedCertificate.R)*(n:ℝ) := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlog0 hlog _) (by positivity)
        · exact hpow
        · positivity
        · positivity
      _ = _ := by rw [pow_succ]; ring
  have hnat : call.cyclic AlignedCertificate.S ≤ 16^AlignedCertificate.R*n^(k*AlignedCertificate.R+1) := by exact_mod_cast hpoly
  have hs : 1 ≤ n.size := Nat.size_pos.mpr (by omega)
  calc
    _ ≤ 16^AlignedCertificate.R*n^(k*AlignedCertificate.R+1) := hnat
    _ ≤ 16^AlignedCertificate.R*(2^n.size)^(k*AlignedCertificate.R+1) :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (nat_le_pow_size n) _)
    _ = 2^(4*AlignedCertificate.R+n.size*(k*AlignedCertificate.R+1)) := by
      rw [show (16:ℕ)=2^4 by norm_num,←pow_mul,←pow_mul,←pow_add]
    _ ≤ _ := by
      apply Nat.pow_le_pow_right (by norm_num)
      unfold cyclicConstant
      nlinarith only [hs]

/-- Polynomially many original values and every retained coefficient have
an explicit power-of-two cap, without a premise asserting final widths. -/
theorem uniformBudget_le_pow_size (n degree L m t q A cL cm cq : ℕ)
    (hL : L ≤ cL*n.size) (hm : m ≤ cm*n.size) (hq : q ≤ 2^(cq*n.size))
    (hA : A ≤ n^degree) (ht : t ≤ 2*m) :
    uniformBudget L m t q A ≤ 2^(CoefficientBudget.budgetConstant cL cm cq degree*(n.size+1)) := by
  exact CoefficientBudget.full_budget L m t q A n.size cL cm cq degree hL hm hq
    (original_power_bound n degree A hA) ht

/-- Factorial setup intermediates use quadratic logarithmic storage.
Final choose/residual weights have the smaller linear budget separately. -/
theorem factorial_size_bound (h r C : ℕ) (hh : h ≤ C*r) :
    h.factorial.size ≤ C^2*r^2+1 := by
  have hcap : h.factorial ≤ 2^(h*h) := by
    calc
      _ ≤ h^h := Nat.factorial_le_pow h
      _ ≤ (2^h)^h := Nat.pow_le_pow_left (CoefficientBudget.nat_le_two_pow h) h
      _ = _ := (pow_mul _ _ _).symm
  have hs := (Nat.size_le_size hcap).trans_eq Nat.size_pow
  have hsq : h*h ≤ C^2*r^2 := by nlinarith
  omega


/-- The executable computed geometry has a different fixed overhead from
the historical primeScale geometry. Its own constants are used below. -/
def computedIndexReal : ℝ :=
  (Real.log (24*(8192:ℝ)^AlignedCertificate.R)+(4*AlignedCertificate.R:ℕ)+
    AsymptoticCosts.b+AsymptoticCosts.u)/Real.log 4

def computedIndexConstant : ℕ := Nat.ceil (max computedIndexReal 0)
def computedLengthConstant : ℕ := 11*computedIndexConstant
def computedCyclicConstant : ℕ := 17*AlignedCertificate.R+1

theorem computed_innerPower_le_size (n : ℕ) (hn : 3 ≤ n)
    (call : ComputedPhaseGeometry.Call AlignedCertificate.R n) :
    ComputedPhaseGeometry.innerPower n call AlignedCertificate.S ≤ computedIndexConstant*n.size := by
  have hdim := (ComputedPhaseGeometry.actual_inner_bounds
    AlignedCertificate.R AlignedCertificate.S n hn call).2
  have hs := (PhaseGeometry.aligned_fold_exponent_range call.factors.length).2
  have hp : (n:ℝ)^(AsymptoticCosts.b+PhaseGeometry.foldExponent AlignedCertificate.S call.factors.length) ≤ (n:ℝ)^(AsymptoticCosts.b+AsymptoticCosts.u) :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ n by omega)) (by linarith)
  have hdim' := hdim.trans (mul_le_mul_of_nonneg_left hp (by positivity))
  rw [ComputedPhaseGeometry.innerDimension_eq_power,Nat.cast_pow,Nat.cast_ofNat] at hdim'
  have hC : (1:ℝ) ≤ 24*(8192:ℝ)^AlignedCertificate.R := by
    have hp : (1:ℝ) ≤ 8192^AlignedCertificate.R := one_le_pow₀ (by norm_num)
    linarith
  have hi := ReductionCosts.Overhead.logarithmicIndex_bound _ _ _ _ _ hn hC hdim'
  have hi' : (ComputedPhaseGeometry.innerPower n call AlignedCertificate.S:ℝ) ≤ computedIndexReal*Real.log (n:ℝ) := by
    simpa only [computedIndexReal,add_assoc] using hi
  have hlog0 : 0 ≤ Real.log (n:ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
  have hmajor := mul_le_mul_of_nonneg_right (le_max_left computedIndexReal 0) hlog0
  have hmax : (0:ℝ) ≤ max computedIndexReal 0 := le_max_right _ _
  have hlog := mul_le_mul_of_nonneg_left (real_log_le_size n (by omega)) hmax
  have hceil : max computedIndexReal 0 ≤ (computedIndexConstant:ℝ) := Nat.le_ceil _
  have hc := mul_le_mul_of_nonneg_right hceil (Nat.cast_nonneg n.size)
  have hout : (ComputedPhaseGeometry.innerPower n call AlignedCertificate.S:ℝ) ≤ (computedIndexConstant:ℝ)*(n.size:ℝ) := by linarith
  exact_mod_cast hout

theorem rounded_length_le_eleven (m : ℕ) :
    Nat.ceil (RealCertificate.c*(m:ℝ)) ≤ 11*m := by
  apply Nat.ceil_le.mpr
  have hc : RealCertificate.c ≤ 11 := by norm_num [RealCertificate.c]
  push_cast
  nlinarith [show (0:ℝ) ≤ m from Nat.cast_nonneg m]

theorem computed_roundedLength_le_size (n : ℕ) (hn : 3 ≤ n)
    (call : ComputedPhaseGeometry.Call AlignedCertificate.R n) :
    Nat.ceil (RealCertificate.c*(ComputedPhaseGeometry.innerPower n call AlignedCertificate.S:ℝ)) ≤ computedLengthConstant*n.size := by
  have h := (rounded_length_le_eleven _).trans
    (Nat.mul_le_mul_left 11 (computed_innerPower_le_size n hn call))
  simpa only [computedLengthConstant,Nat.mul_assoc] using h

theorem computed_cyclic_le_pow_size (n : ℕ) (hn : 3 ≤ n)
    (call : ComputedPhaseGeometry.Call AlignedCertificate.R n) :
    call.cyclic AlignedCertificate.S ≤ 2^(computedCyclicConstant*n.size) := by
  have h := ComputedPhaseGeometry.actual_cyclic_terminal_bound n hn call
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hn0 : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hlog : Real.log (n:ℝ) ≤ n := by linarith [Real.log_le_sub_one_of_pos hn0]
  have hlog0 : 0 ≤ Real.log (n:ℝ) := Real.log_nonneg hn1
  have hv : AsymptoticCosts.v ≤ 1 := by
    norm_num [AsymptoticCosts.v,AlignedCertificate.v,AlignedCertificate.eta,
      AlignedCertificate.b,AlignedCertificate.S,AlignedCertificate.R]
  have hpow : (n:ℝ)^AsymptoticCosts.v ≤ n := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hn1 hv
  have hpoly : (call.cyclic AlignedCertificate.S:ℝ) ≤ (8192:ℝ)^AlignedCertificate.R*(n:ℝ)^(4*AlignedCertificate.R+1) := by
    apply h.trans
    unfold ComputedPhaseGeometry.phaseOverhead
    calc
      _ ≤ (8192:ℝ)^AlignedCertificate.R*(n:ℝ)^(4*AlignedCertificate.R)*(n:ℝ) := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlog0 hlog _) (by positivity)
        · exact hpow
        · positivity
        · positivity
      _ = _ := by rw [pow_succ]; ring
  have hnat : call.cyclic AlignedCertificate.S ≤ 8192^AlignedCertificate.R*n^(4*AlignedCertificate.R+1) := by exact_mod_cast hpoly
  have hs : 1 ≤ n.size := Nat.size_pos.mpr (by omega)
  calc
    _ ≤ 8192^AlignedCertificate.R*n^(4*AlignedCertificate.R+1) := hnat
    _ ≤ 8192^AlignedCertificate.R*(2^n.size)^(4*AlignedCertificate.R+1) :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (nat_le_pow_size n) _)
    _ = 2^(13*AlignedCertificate.R+n.size*(4*AlignedCertificate.R+1)) := by
      rw [show (8192:ℕ)=2^13 by norm_num,←pow_mul,←pow_mul,←pow_add]
    _ ≤ _ := by
      apply Nat.pow_le_pow_right (by norm_num)
      unfold computedCyclicConstant
      nlinarith only [hs]

/-- Operand size after the actual source and HIGH linear encoder. -/
def highInputBudget (L m A : ℕ) : ℕ := 2^(7*L+m)*A

theorem highInputBudget_le_pow_size (n degree L m A cL cm : ℕ)
    (hL : L ≤ cL*n.size) (hm : m ≤ cm*n.size) (hA : A ≤ n^degree) :
    highInputBudget L m A ≤ 2^((7*cL+cm+degree)*n.size) := by
  unfold highInputBudget
  calc
    _ ≤ 2^(7*L+m)*2^(degree*n.size) := Nat.mul_le_mul_left _ (original_power_bound n degree A hA)
    _ = 2^(7*L+m+degree*n.size) := (pow_add _ _ _).symm
    _ ≤ _ := by apply Nat.pow_le_pow_right (by norm_num); nlinarith only [hL,hm]

theorem high_left_operand_bound {q L m t A : ℕ} [NeZero q]
    (X : CompleteThinProduct.SourceWord L→Cyclic q)
    (hX : ∀ a, CoeffBound (X a) A) (w : HighBoxDP.BaseStates L m t) (r : Fin q) :
    |(HighBaseEncoder.readBase (HighBaseEncoder.encodeLeftSource (m:=m) (t:=t) X) w).get r| ≤ (2^(6*L)*A:ℕ) := by
  rw [HighBaseEncoder.encodeLeftSource_read]
  have h := PipelineBitBounds.source_transform_bound X hX
    (CompleteThinProduct.sourceF (R:=ℤ)) PipelineBitBounds.sourceF_abs
    (HighBoxDP.baseLeaf w.val w.property.2)
  simp only [←PipelineBitBounds.sourceF_intCast] at h
  exact h r

theorem high_right_operand_bound {q L m t A : ℕ} [NeZero q]
    (Y : CompleteThinProduct.SourceWord L→Cyclic q)
    (hY : ∀ a, CoeffBound (Y a) A) (w : HighBoxDP.BaseStates L m t) (r : Fin q) :
    |(HighBaseEncoder.readBase (HighBaseEncoder.encodeRightSource (m:=m) (t:=t) Y) w).get r| ≤ (2^(6*L)*A:ℕ) := by
  rw [HighBaseEncoder.encodeRightSource_read]
  have h := PipelineBitBounds.source_transform_bound Y hY
    (CompleteThinProduct.sourceG (R:=ℤ)) PipelineBitBounds.sourceG_abs
    (HighBoxDP.baseLeaf w.val w.property.2)
  simp only [←PipelineBitBounds.sourceG_intCast] at h
  exact h r

theorem rawLeft_bound {q L m A : ℕ} [NeZero q]
    (data : StoredLeftMatrix L m q)
    (hd : ∀ i r, |(data.get i).get r| ≤ (A:ℤ)) :
    ∀ Q bits outer h1 h2, CoeffBound (rawLeft (readLeftMatrix data) Q bits outer h1 h2) A := by
  intro Q bits outer h1 h2 r
  unfold rawLeft
  split
  · exact hd _ _
  · simp only [CyclicRing.zero_coeff,abs_zero]
    positivity

theorem rawRight_bound {q L m A : ℕ} [NeZero q]
    (data : StoredRightMatrix L m q)
    (hd : ∀ i r, |(data.get i).get r| ≤ (A:ℤ)) :
    ∀ Q bits h1 h2 outer, CoeffBound (rawRight (readRightMatrix data) Q bits h1 h2 outer) A := by
  intro Q bits h1 h2 outer r
  unfold rawRight
  split
  · exact hd _ _
  · simp only [CyclicRing.zero_coeff,abs_zero]
    positivity

theorem prepared_left_source_bound {q L m t A : ℕ} [NeZero q]
    (shape : ShapePlan L m) (data : StoredLeftMatrix L m q)
    (hd : ∀ i r, |(data.get i).get r| ≤ (A:ℤ)) (run : Fin (2*m+1)) :
    ∀ a, CoeffBound (sourceValue ((prepareLeftBand (t:=t) shape data).runs.get run).source a)
      (2^(L+m)*A) := by
  rw [prepareLeftBand_source]
  intro a
  exact (PipelineBitBounds.rawLeftSource_bound _ _ _ _ _
    (fun Q hQ => goodSlots_size L m Q hQ) (rawLeft_bound data hd) a.1 a.2).mono
    (Nat.mul_le_mul_right A (Nat.pow_le_pow_right (by norm_num) (by omega)))

theorem prepared_right_source_bound {q L m t A : ℕ} [NeZero q]
    (shape : ShapePlan L m) (data : StoredRightMatrix L m q)
    (hd : ∀ i r, |(data.get i).get r| ≤ (A:ℤ)) (run : Fin (2*m+1)) :
    ∀ a, CoeffBound (sourceValue ((prepareRightBand (t:=t) shape data).runs.get run).source a)
      (2^(L+m)*A) := by
  rw [prepareRightBand_source]
  intro a
  exact (PipelineBitBounds.rawRightSource_bound _ _ _ _ _
    (fun Q hQ => goodSlots_size L m Q hQ) (rawRight_bound data hd) a.1 a.2).mono
    (Nat.mul_le_mul_right A (Nat.pow_le_pow_right (by norm_num) (by omega)))

theorem prepared_left_operand_bound {q L m t A : ℕ} [NeZero q]
    (shape : ShapePlan L m) (data : StoredLeftMatrix L m q)
    (hd : ∀ i r, |(data.get i).get r| ≤ (A:ℤ)) (run : Fin (2*m+1))
    (w : HighBoxDP.BaseStates L m t) (r : Fin q) :
    ((HighBaseEncoder.readBase (HighBaseEncoder.encodeLeftSource (m:=m) (t:=t)
      (sourceValue ((prepareLeftBand (t:=t) shape data).runs.get run).source)) w).get r).natAbs ≤ highInputBudget L m A := by
  have h := high_left_operand_bound _ (prepared_left_source_bound (t:=t) shape data hd run) w r
  have he : 2^(6*L)*(2^(L+m)*A)=highInputBudget L m A := by
    unfold highInputBudget
    rw [←mul_assoc,←pow_add]
    congr 2
    omega
  rw [he] at h
  exact_mod_cast (show (((HighBaseEncoder.readBase
    (HighBaseEncoder.encodeLeftSource (m:=m) (t:=t)
      (sourceValue ((prepareLeftBand (t:=t) shape data).runs.get run).source)) w).get r).natAbs:ℤ) ≤ highInputBudget L m A by simpa only [Int.natCast_natAbs] using h)

theorem prepared_right_operand_bound {q L m t A : ℕ} [NeZero q]
    (shape : ShapePlan L m) (data : StoredRightMatrix L m q)
    (hd : ∀ i r, |(data.get i).get r| ≤ (A:ℤ)) (run : Fin (2*m+1))
    (w : HighBoxDP.BaseStates L m t) (r : Fin q) :
    ((HighBaseEncoder.readBase (HighBaseEncoder.encodeRightSource (m:=m) (t:=t)
      (sourceValue ((prepareRightBand (t:=t) shape data).runs.get run).source)) w).get r).natAbs ≤ highInputBudget L m A := by
  have h := high_right_operand_bound _ (prepared_right_source_bound (t:=t) shape data hd run) w r
  have he : 2^(6*L)*(2^(L+m)*A)=highInputBudget L m A := by
    unfold highInputBudget
    rw [←mul_assoc,←pow_add]
    congr 2
    omega
  rw [he] at h
  exact_mod_cast (show (((HighBaseEncoder.readBase
    (HighBaseEncoder.encodeRightSource (m:=m) (t:=t)
      (sourceValue ((prepareRightBand (t:=t) shape data).runs.get run).source)) w).get r).natAbs:ℤ) ≤ highInputBudget L m A by simpa only [Int.natCast_natAbs] using h)

/-- A uniform polylogarithmic replacement for the concrete binary backend
allowance. Only magnitude caps are assumed, never a running-time cap. -/
theorem binaryAllowance_polylog (q A r cq cA : ℕ)
    (hq : q ≤ 2^(cq*r)) (hA : A ≤ 2^(cA*r)) :
    2^70*q*(q.size+A.size+102)^11 ≤ 2^70*(cq+cA+104)^11*q*(r+1)^11 := by
  have hqsize := (Nat.size_le_size hq).trans_eq Nat.size_pow
  have hAsize := (Nat.size_le_size hA).trans_eq Nat.size_pow
  have hs : q.size+A.size+102 ≤ (cq+cA+104)*(r+1) := by nlinarith
  calc
    _ ≤ 2^70*q*((cq+cA+104)*(r+1))^11 := by gcongr
    _ = _ := by rw [mul_pow]; ring


/-- A single explicit polynomial-logarithmic width for data arithmetic,
normalization, metadata and factorial temporary products. -/
def commonBitWidth (n degree cL cm cq : ℕ) : ℕ :=
  (CoefficientBudget.budgetConstant cL cm cq degree+2*(4*cm+2)^2+20)*(n.size+1)^2

theorem coefficient_size_le_common (n degree L m t q A cL cm cq : ℕ)
    (hL : L ≤ cL*n.size) (hm : m ≤ cm*n.size) (hq : q ≤ 2^(cq*n.size))
    (hA : A ≤ n^degree) (ht : t ≤ 2*m) (z : ℤ)
    (hz : z.natAbs ≤ uniformBudget L m t q A) :
    z.natAbs.size ≤ commonBitWidth n degree cL cm cq := by
  have h := natAbs_size_of_pow_bound z _ (hz.trans
    (uniformBudget_le_pow_size n degree L m t q A cL cm cq hL hm hq hA ht))
  have hp : n.size+1 ≤ (n.size+1)^2 := by nlinarith
  unfold commonBitWidth
  nlinarith

theorem factorial_temporary_width_le_common (n degree m t cL cm cq : ℕ)
    (hm : m ≤ cm*n.size) (ht : t ≤ 2*m) :
    2*(2*m+t+2)^2+2 ≤ commonBitWidth n degree cL cm cq := by
  have hcap : 2*m+t+2 ≤ (4*cm+2)*(n.size+1) := by nlinarith
  have hp := Nat.pow_le_pow_left hcap 2
  rw [mul_pow] at hp
  unfold commonBitWidth
  have hpos : 1 ≤ (n.size+1)^2 := by
    have hp : 0 < (n.size+1)^2 := by positivity
    omega
  nlinarith

theorem normalization_width_le_common (n degree L m q A cL cm cq : ℕ)
    (hL : L ≤ cL*n.size) (hm : m ≤ cm*n.size) (hq : q ≤ 2^(cq*n.size))
    (hA : A ≤ n^degree) :
    BackendNumeratorBounds.numeratorBitBudget L m q A ≤ commonBitWidth n degree cL cm cq := by
  have hqsize := (Nat.size_le_size hq).trans_eq Nat.size_pow
  have hAsize := (Nat.size_le_size (original_power_bound n degree A hA)).trans_eq Nat.size_pow
  have hp : n.size+1 ≤ (n.size+1)^2 := by nlinarith
  unfold BackendNumeratorBounds.numeratorBitBudget commonBitWidth CoefficientBudget.budgetConstant
  nlinarith

/-- A deliberately dense combinatorial majorant for keys and array
addresses; it is used for widths, never to allocate an uncapped encoder. -/
def metadataCells (L m q : ℕ) : ℕ := q*(2*L+1)*(2*m+1)*2^(10*L)

theorem metadataCells_le_pow (n L m q cL cm cq : ℕ)
    (hL : L ≤ cL*n.size) (hm : m ≤ cm*n.size) (hq : q ≤ 2^(cq*n.size)) :
    metadataCells L m q ≤ 2^((cq+12*cL+2*cm+2)*(n.size+1)) := by
  unfold metadataCells
  calc
    _ ≤ 2^(cq*n.size)*2^(2*L+1)*2^(2*m+1)*2^(10*L) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul
        (Nat.mul_le_mul hq (CoefficientBudget.nat_le_two_pow _))
        (CoefficientBudget.nat_le_two_pow _))
    _ = 2^(cq*n.size+(2*L+1)+(2*m+1)+10*L) := by
      rw [←pow_add,←pow_add,←pow_add]
    _ ≤ _ := by
      apply Nat.pow_le_pow_right (by norm_num)
      nlinarith only [hL,hm]

theorem metadata_size_le_common (n degree L m q cL cm cq j : ℕ)
    (hL : L ≤ cL*n.size) (hm : m ≤ cm*n.size) (hq : q ≤ 2^(cq*n.size))
    (hj : j ≤ metadataCells L m q) :
    j.size ≤ commonBitWidth n degree cL cm cq := by
  have hs := (Nat.size_le_size (hj.trans (metadataCells_le_pow n L m q cL cm cq hL hm hq))).trans_eq Nat.size_pow
  have hp : n.size+1 ≤ (n.size+1)^2 := by nlinarith
  unfold commonBitWidth CoefficientBudget.budgetConstant
  nlinarith

/-- The current computed phase supplies every parameter hypothesis of
both the coefficient and full binary multiplication bounds. -/
theorem computed_uniformBudget_le_pow (n degree A : ℕ) (hn : 3 ≤ n)
    (call : ComputedPhaseGeometry.Call AlignedCertificate.R n) (hA : A ≤ n^degree) :
    let m:=ComputedPhaseGeometry.innerPower n call AlignedCertificate.S
    let L:=Nat.ceil (RealCertificate.c*(m:ℝ))
    let t:=Nat.ceil (2*RealCertificate.theta*(m:ℝ))
    uniformBudget L m t (call.cyclic AlignedCertificate.S) A ≤
      2^(CoefficientBudget.budgetConstant computedLengthConstant computedIndexConstant
        computedCyclicConstant degree*(n.size+1)) := by
  exact uniformBudget_le_pow_size n degree _ _ _ _ A _ _ _
    (computed_roundedLength_le_size n hn call) (computed_innerPower_le_size n hn call)
    (computed_cyclic_le_pow_size n hn call) hA (rounded_cutoff_le _)

theorem computed_highInputBudget_le_pow (n degree A : ℕ) (hn : 3 ≤ n)
    (call : ComputedPhaseGeometry.Call AlignedCertificate.R n) (hA : A ≤ n^degree) :
    let m:=ComputedPhaseGeometry.innerPower n call AlignedCertificate.S
    let L:=Nat.ceil (RealCertificate.c*(m:ℝ))
    highInputBudget L m A ≤
      2^((7*computedLengthConstant+computedIndexConstant+degree)*n.size) := by
  exact highInputBudget_le_pow_size n degree _ _ A _ _
    (computed_roundedLength_le_size n hn call) (computed_innerPower_le_size n hn call) hA

/-- Original band copies preserve the coefficient bound, including every
padded row, column, middle label and zero cyclic slot. -/
theorem makeLeftBand_bound {N D L m q A : ℕ} (X : OriginalLeft N D q)
    (hX : ∀ i r, |(X.get i).get r| ≤ (A:ℤ))
    (b : Fin (TilingCosts.bandCount N (tileWidth L m))) :
    ∀ i r, |((makeLeftBand (L:=L) (m:=m) X b).get i).get r| ≤ (A:ℤ) := by
  intro i r
  simp only [makeLeftBand,Vector.get_ofFn]
  split
  · split
    · exact hX _ _
    · simp only [Vector.get_replicate,abs_zero]
      positivity
  · simp only [Vector.get_replicate,abs_zero]
    positivity

theorem makeRightBand_bound {N D L m q A : ℕ} (Y : OriginalRight N D q)
    (hY : ∀ i r, |(Y.get i).get r| ≤ (A:ℤ))
    (b : Fin (TilingCosts.bandCount N (tileWidth L m))) :
    ∀ i r, |((makeRightBand (L:=L) (m:=m) Y b).get i).get r| ≤ (A:ℤ) := by
  intro i r
  simp only [makeRightBand,Vector.get_ofFn]
  split
  · split
    · exact hY _ _
    · simp only [Vector.get_replicate,abs_zero]
      positivity
  · simp only [Vector.get_replicate,abs_zero]
    positivity

theorem highInputBudget_pos (L m A : ℕ) (hA : 1 ≤ A) : 1 ≤ highInputBudget L m A := by
  unfold highInputBudget
  have hp : 0 < 2^(7*L+m)*A := mul_pos (by positivity) (by omega)
  omega

/-- All full-vector multiplications inside the SAME global preparation
are bounded from the original backing input cells. -/
theorem actual_binary_globalMultiplierBudget {N D L m t q A : ℕ} [NeZero q]
    (X : OriginalLeft N D q) (Y : OriginalRight N D q) (hA : 1 ≤ A)
    (hX : ∀ i r, |(X.get i).get r| ≤ (A:ℤ))
    (hY : ∀ i r, |(Y.get i).get r| ≤ (A:ℤ)) :
    let M:=BinaryMultiplierAdapter.boundedBinaryFullMultiplier q (highInputBudget L m A)
      (highInputBudget_pos L m A hA)
    BackendCostRefinement.GlobalMultiplierBudget M
      (prepareGlobal (L:=L) (m:=m) (t:=t) M X Y)
      (BinaryMultiplierAdapter.workBound q (highInputBudget L m A)) := by
  intro M b c run w
  apply BinaryMultiplierAdapter.bounded_run_work
  · intro r
    simp only [prepareGlobal_refines,prepareGlobalReference,prepareGlobalShapeReference,Vector.get_map,Vector.get_ofFn]
    exact prepared_left_operand_bound _ _ (makeLeftBand_bound X hX b) run w r
  · intro r
    simp only [prepareGlobal_refines,prepareGlobalReference,prepareGlobalShapeReference,Vector.get_map,Vector.get_ofFn]
    exact prepared_right_operand_bound _ _ (makeRightBand_bound Y hY c) run w r

/-- The actual binary multiplier allowance is q times a fixed polynomial
of the original instance's logarithmic size, uniformly over all computed
adaptive candidate phases. -/
theorem computed_binary_workBound_polylog (n degree A : ℕ) (hn : 3 ≤ n)
    (call : ComputedPhaseGeometry.Call AlignedCertificate.R n) (hA : A ≤ n^degree) :
    let m:=ComputedPhaseGeometry.innerPower n call AlignedCertificate.S
    let L:=Nat.ceil (RealCertificate.c*(m:ℝ))
    let q:=call.cyclic AlignedCertificate.S
    BinaryMultiplierAdapter.workBound q (highInputBudget L m A) ≤
      2^70*(computedCyclicConstant+7*computedLengthConstant+computedIndexConstant+degree+104)^11*
        q*(n.size+1)^11 := by
  have h := binaryAllowance_polylog _ _ n.size computedCyclicConstant
    (7*computedLengthConstant+computedIndexConstant+degree)
    (computed_cyclic_le_pow_size n hn call) (computed_highInputBudget_le_pow n degree A hn call hA)
  simpa only [BinaryMultiplierAdapter.workBound,BinaryMultiplierAdapter.width,
    show (2:ℕ)^70=1180591620717411303424 by norm_num,Nat.add_assoc] using h

end
end ThinMatrix.AdaptiveBitBounds

#print axioms ThinMatrix.AdaptiveBitBounds.computed_innerPower_le_size
#print axioms ThinMatrix.AdaptiveBitBounds.computed_roundedLength_le_size
#print axioms ThinMatrix.AdaptiveBitBounds.computed_cyclic_le_pow_size
#print axioms ThinMatrix.AdaptiveBitBounds.uniformBudget_le_pow_size
#print axioms ThinMatrix.AdaptiveBitBounds.factorial_size_bound
#print axioms ThinMatrix.AdaptiveBitBounds.prepared_left_operand_bound
#print axioms ThinMatrix.AdaptiveBitBounds.prepared_right_operand_bound
#print axioms ThinMatrix.AdaptiveBitBounds.binaryAllowance_polylog
#print axioms ThinMatrix.AdaptiveBitBounds.coefficient_size_le_common
#print axioms ThinMatrix.AdaptiveBitBounds.factorial_temporary_width_le_common
#print axioms ThinMatrix.AdaptiveBitBounds.normalization_width_le_common
#print axioms ThinMatrix.AdaptiveBitBounds.metadata_size_le_common
#print axioms ThinMatrix.AdaptiveBitBounds.computed_uniformBudget_le_pow
#print axioms ThinMatrix.AdaptiveBitBounds.computed_highInputBudget_le_pow
#print axioms ThinMatrix.AdaptiveBitBounds.actual_binary_globalMultiplierBudget
#print axioms ThinMatrix.AdaptiveBitBounds.computed_binary_workBound_polylog
