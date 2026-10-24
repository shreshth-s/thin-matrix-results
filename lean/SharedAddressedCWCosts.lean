import SharedFullyAddressedBatch
import BinaryAddressedControl
import CWBinaryAddressedBound

set_option autoImplicit false
set_option maxHeartbeats 1800000

/-! The shared product budget includes the actual binary arithmetic and
address operations, plus the separately explicit indexed-control counter.
One extracted fixed CW base bounds this budget uniformly at every admissible
matrix size. -/
namespace ThinMatrix.SharedAddressedCWCosts
open scoped BigOperators
open RecursiveTable (Table fin prod)
open BinaryCell RectangularBatch CWHomogeneousCopies CWRetainedArithmetic
open SharedFullyAddressedBatch
open CompactBlocks (blockCount)
variable {N D P A C : ℕ}

def workCost (scheme : Scheme) (k H : ℕ) :=
  BinaryAddressedControl.workConstant scheme.base*(k+H.size+2)^5*(growth scheme)^k

theorem product_work (scheme : Scheme) (shape : SharedMatrixSetup.Shape scheme D A C)
    (H : ℕ) (hH : 1≤H) (x : Table (PaddedMatrix.matrix A D) Cell) (y : Table (PaddedMatrix.matrix D C) Cell)
    (hx : BinaryRetainedBounds.Bounded x H) (hy : BinaryRetainedBounds.Bounded y H) :
    (product scheme shape x y).bitSteps+(product scheme shape x y).control≤workCost scheme shape.depth H := by
  have hg := growth_properties scheme
  exact BinaryAddressedControl.execute_work (first_pos scheme) (middle_pos scheme) (last_pos scheme)
    scheme.ht scheme.base (growth scheme) hg.1 hg.2.1 hg.2.2.1 hg.2.2.2.1 hg.2.2.2.2 shape.depth H hH
    shape.first_fit shape.middle_fit shape.last_fit x y hx hy

def controlCost (scheme : Scheme) (k H : ℕ) :=
  BinaryAddressedControl.constant scheme.base*(k+H.size+2)^5*(growth scheme)^k

theorem product_control (scheme : Scheme) (shape : SharedMatrixSetup.Shape scheme D A C)
    (H : ℕ) (x : Table (PaddedMatrix.matrix A D) Cell) (y : Table (PaddedMatrix.matrix D C) Cell) :
    (product scheme shape x y).control≤controlCost scheme shape.depth H := by
  have hg := growth_properties scheme
  have hh := BinaryAddressedControl.execute_control (first_pos scheme) (middle_pos scheme) (last_pos scheme)
    scheme.ht scheme.base (growth scheme) hg.1 hg.2.1 hg.2.2.1 hg.2.2.2.1 hg.2.2.2.2 shape.depth
    shape.first_fit shape.last_fit x y
  have hp : (shape.depth+2)^2≤(shape.depth+H.size+2)^5 :=
    (Nat.pow_le_pow_left (by omega) 2).trans (Nat.pow_le_pow_right (by omega) (by decide))
  exact hh.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hp))

def outerControl (N D P A C : ℕ) :=
  blockCount N A*(56*A*D+40)+blockCount P C*(56*D*C+40)+
      32*blockCount N A*blockCount P C+56*N*P+48

theorem run_work (scheme : Scheme) (shape : SharedMatrixSetup.Shape scheme D A C) (hA : 0<A) (hC : 0<C)
    (H W : ℕ) (hH : 1≤H) (hW : AddressFits N D P A C W)
    (x : Table (PaddedMatrix.matrix N D) Cell) (y : Table (PaddedMatrix.matrix D P) Cell)
    (hx : BinaryRetainedBounds.Bounded x H) (hy : BinaryRetainedBounds.Bounded y H) :
    (run scheme shape hA hC x y).bitSteps+(run scheme shape hA hC x y).control≤
      blockCount N A*blockCount P C*workCost scheme shape.depth H+
        addressBudget N D P A C W+outerControl N D P A C := by
  have hb := run_bits scheme shape hA hC H W hH hW x y hx hy
  have hc := run_control scheme shape hA hC x y
  have hsum : (∑ i : Fin (blockCount N A),∑ j : Fin (blockCount P C),
      (product scheme shape (RectangularBatch.leftChunk x i).value
        (RectangularBatch.rightChunk y j).value).control)≤
      blockCount N A*blockCount P C*controlCost scheme shape.depth H := by
    calc
      _ ≤ ∑ _i : Fin (blockCount N A),∑ _j : Fin (blockCount P C),controlCost scheme shape.depth H := by
        apply Finset.sum_le_sum;intro i _
        apply Finset.sum_le_sum;intro j _
        exact product_control scheme shape H _ _
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul];ring
  have hc' : (run scheme shape hA hC x y).control≤
      blockCount N A*blockCount P C*controlCost scheme shape.depth H+outerControl N D P A C := by
    apply hc.trans
    unfold outerControl
    omega
  have hid : workCost scheme shape.depth H=productCost scheme shape.depth H+controlCost scheme shape.depth H := by
    unfold workCost productCost controlCost BinaryAddressedControl.workConstant
    ring
  rw [hid]
  nlinarith

theorem cw_growth (s : ℕ) (hs : 0<s) (h : CWTargetExtractionRate.Sample s)
    (ht : 0<CWHomogeneousCopies.copies s h) :
    growth (ofCW s hs h ht)=growthBase s h := rfl

/-- The public workCost, rather than only a separate theoretical recurrence,
obeys the required CW rate at the single shared selected depth. -/
theorem exists_uniform_work_budget : ∃ scheme : Scheme, scheme.Valid ∧
    scheme.num=861 ∧ scheme.den=500 ∧ scheme.z=15 ∧
    ∃ K : ℝ, 0<K ∧ ∀ D A C : ℕ, ∀ hD : 0<D,
      ∀ hf : (A-1)^scheme.den≤D^scheme.num, ∀ hl : C≤D^scheme.z, ∀ H : ℕ,
      (workCost scheme (SharedMatrixSetup.prepare scheme hD hf hl).value.depth H:ℝ)≤
        K*(D.size+H.size+6)^5*(D:ℝ)^CWFiniteBase.exponent := by
  obtain ⟨s,hs,h,ht,hg⟩ := CWFiniteBase.exists_positive_base
  rw [CWRectangularRanks.growth_identity] at hg
  let scheme := ofCW s hs h ht
  let K : ℝ := (BinaryAddressedControl.workConstant (base s h)+1)*(rows s:ℝ)^CWFiniteBase.exponent
  have hrow : (0:ℝ)<rows s := by exact_mod_cast CWRectangularRanks.rows_pos s
  have hK : 0<K := mul_pos (by exact_mod_cast Nat.zero_lt_succ (BinaryAddressedControl.workConstant (base s h)))
    (Real.rpow_pos_of_pos hrow _)
  refine ⟨scheme,ofCW_valid s hs h ht,rfl,rfl,rfl,K,hK,?_⟩
  intro D A C hD hf hl H
  let k := (BinaryMatrixSetup.select (rows s) D).value.2
  have hq := (PaddedMatrixScale.bases_gt_one s hs).2.1
  have hk := BinaryMatrixSetup.select_bounds (rows s) D hq hD
  have hsize : ((rows s)^k:ℝ)≤(rows s:ℝ)*D := by exact_mod_cast hk.2.1
  have hpow : (growthBase s h:ℝ)^k≤(rows s:ℝ)^CWFiniteBase.exponent*(D:ℝ)^CWFiniteBase.exponent := by
    calc
      _≤((rows s:ℝ)^CWFiniteBase.exponent)^k :=
        pow_le_pow_left₀ (by positivity) (growth_bounds s h hg) k
      _=((rows s:ℝ)^k)^CWFiniteBase.exponent := by
        rw [←Real.rpow_mul_natCast (by positivity),←Real.rpow_natCast_mul (by positivity)]
        rw [mul_comm]
      _≤((rows s:ℝ)*D)^CWFiniteBase.exponent :=
        Real.rpow_le_rpow (by positivity) hsize (by norm_num [CWFiniteBase.exponent])
      _=_ := Real.mul_rpow (by positivity) (by positivity)
  have hp : k+H.size+2≤D.size+H.size+6 := by dsimp [k];omega
  have hpR : ((k+H.size+2:ℕ):ℝ)^5≤((D.size+H.size+6:ℕ):ℝ)^5 := by
    exact_mod_cast Nat.pow_le_pow_left hp 5
  change (workCost (ofCW s hs h ht) k H:ℝ)≤_
  simp only [workCost,cw_growth,Nat.cast_mul,Nat.cast_pow]
  have hcost := mul_le_mul hpR hpow (by positivity) (by positivity)
  calc
    _≤(BinaryAddressedControl.workConstant (base s h):ℝ)*
        (((D.size+H.size+6:ℕ):ℝ)^5*((rows s:ℝ)^CWFiniteBase.exponent*(D:ℝ)^CWFiniteBase.exponent)) := by
      simpa only [mul_assoc,ofCW] using mul_le_mul_of_nonneg_left hcost
        (show (0:ℝ)≤BinaryAddressedControl.workConstant (base s h) by positivity)
    _≤((BinaryAddressedControl.workConstant (base s h):ℝ)+1)*
        (((D.size+H.size+6:ℕ):ℝ)^5*((rows s:ℝ)^CWFiniteBase.exponent*(D:ℝ)^CWFiniteBase.exponent)) := by gcongr;linarith
    _=_ := by dsimp [K];push_cast;ring

#print axioms product_work
#print axioms product_control
#print axioms run_work
#print axioms cw_growth
#print axioms exists_uniform_work_budget
end ThinMatrix.SharedAddressedCWCosts
