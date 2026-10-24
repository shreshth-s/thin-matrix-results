import BinaryAddressedMatrix
import CWBinaryScalarBound

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! A fixed extracted CW base supplies the actual addressed ordinary-matrix
program. Binary shape selection, all recursive addresses and output recovery
are charged. Bounded indexed loads/counters remain the separate control model;
this is not a compiler or machine-heap certification. -/
namespace ThinMatrix.CWBinaryAddressedBound
open scoped BigOperators
open CWHomogeneousCopies CWRetainedArithmetic
open RecursiveTable (Table fin read)
open BinaryCell

noncomputable def run (s : ℕ) (hs : 0 < s) (h : CWTargetExtractionRate.Sample s)
    (ht : 0 < CWHomogeneousCopies.copies s h) {n D p : ℕ} (hD : 0 < D)
    (hn : (n-1)^500 ≤ D^861) (hp : p ≤ D^15)
    (x : Table (PaddedMatrix.matrix n D) Cell) (y : Table (PaddedMatrix.matrix D p) Cell) :=
  let selection := BinaryMatrixSetup.select (rows s) D
  let fit := BinaryMatrixSetup.selected_fits (cols s) (rows s) (inners s) D n p 861 500 15
    (PaddedMatrixScale.bases_gt_one s hs).2.1 hD (by decide) (by decide)
    (PaddedMatrixScale.aspect s).1 (PaddedMatrixScale.aspect s).2 hn hp
  let out := BinaryAddressedMatrix.execute
    (PaddedMatrixScale.bases_gt_one s hs).1.le (PaddedMatrixScale.bases_gt_one s hs).2.1.le
    (PaddedMatrixScale.bases_gt_one s hs).2.2.le ht (base s h) selection.value.2 fit.1 fit.2.2 x y
  (⟨out.value,selection.operations+out.bitSteps,out.control+8⟩ : BinaryGroupedCoordinates.Run _)

theorem run_value (s : ℕ) (hs : 0 < s) (h : CWTargetExtractionRate.Sample s)
    (ht : 0 < CWHomogeneousCopies.copies s h) {n D p : ℕ} (hD : 0 < D)
    (hn : (n-1)^500 ≤ D^861) (hp : p ≤ D^15)
    (x : Table (PaddedMatrix.matrix n D) Cell) (y : Table (PaddedMatrix.matrix D p) Cell) :
    (run s hs h ht hD hn hp x y).value=(CWBinaryScalarBound.run s hs h ht hD hn hp x y).value := by
  simp only [run,CWBinaryScalarBound.run,BinaryMatrixSetup.execute,BinaryAddressedMatrix.execute_value]

theorem run_correct (s : ℕ) (hs : 0 < s) (h : CWTargetExtractionRate.Sample s)
    (ht : 0 < CWHomogeneousCopies.copies s h) {n D p : ℕ} (hD : 0 < D)
    (hn : (n-1)^500 ≤ D^861) (hp : p ≤ D^15)
    (x : Table (PaddedMatrix.matrix n D) Cell) (y : Table (PaddedMatrix.matrix D p) Cell)
    (i : Fin n × Fin p) :
    view (read (run s hs h ht hD hn hp x y).value i)=
      ∑ j : Fin D,view (read x (i.1,j))*view (read y (j,i.2)) := by
  rw [run_value]
  exact CWBinaryScalarBound.run_correct s hs h ht hD hn hp x y i

theorem growth_properties (s : ℕ) (h : CWTargetExtractionRate.Sample s) :
    1 ≤ growthBase s h ∧
    (ranks s+CWHomogeneousCopies.copies s h-1)/CWHomogeneousCopies.copies s h ≤ growthBase s h ∧
    (leftLayout s).size ≤ growthBase s h ∧
    (middleLayout s).size ≤ growthBase s h ∧ (rightLayout s).size ≤ growthBase s h := by
  dsimp only [growthBase]
  exact ⟨(le_max_left _ _).trans (le_max_right _ _),le_max_left _ _,
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _)),
    (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))),
    (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))⟩

noncomputable def constant (s : ℕ) (h : CWTargetExtractionRate.Sample s) :=
  1400*((rows s).size+6)^2+BinaryAddressedMatrix.constant (base s h)

theorem run_bits (s : ℕ) (hs : 0 < s) (h : CWTargetExtractionRate.Sample s)
    (ht : 0 < CWHomogeneousCopies.copies s h) {n D p : ℕ} (hD : 0 < D)
    (hn : (n-1)^500 ≤ D^861) (hp : p ≤ D^15)
    (H : ℕ) (hH : 1 ≤ H)
    (x : Table (PaddedMatrix.matrix n D) Cell) (y : Table (PaddedMatrix.matrix D p) Cell)
    (hx : BinaryRetainedBounds.Bounded x H) (hy : BinaryRetainedBounds.Bounded y H) :
    (run s hs h ht hD hn hp x y).bitSteps ≤
      constant s h*(D.size+H.size+6)^5*(growthBase s h)^(BinaryMatrixSetup.select (rows s) D).value.2 := by
  let k := (BinaryMatrixSetup.select (rows s) D).value.2
  let P := D.size+H.size+6
  have hq := (PaddedMatrixScale.bases_gt_one s hs).2.1
  have hfit := BinaryMatrixSetup.selected_fits (cols s) (rows s) (inners s) D n p 861 500 15 hq hD
    (by decide) (by decide) (PaddedMatrixScale.aspect s).1 (PaddedMatrixScale.aspect s).2 hn hp
  have hg := growth_properties s h
  have hb := BinaryAddressedMatrix.execute_bits
    (PaddedMatrixScale.bases_gt_one s hs).1.le hq.le (PaddedMatrixScale.bases_gt_one s hs).2.2.le ht
    (base s h) (growthBase s h) hg.1 hg.2.1 hg.2.2.1 hg.2.2.2.1 hg.2.2.2.2
    k H hH hfit.1 hfit.2.1 hfit.2.2 x y hx hy
  have hk := (BinaryMatrixSetup.select_bounds (rows s) D hq hD).2.2
  have hP : k+H.size+2 ≤ P := by dsimp [P,k];omega
  have heval := hb.trans (Nat.mul_le_mul_right _
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hP 5)))
  have hsetup := BinaryMatrixSetup.select_bits (rows s) D hq hD
  have hsize : (rows s).size+D.size+6 ≤ ((rows s).size+6)*P := by dsimp [P];nlinarith
  have hfactor : D.size+3 ≤ P := by dsimp [P];omega
  have hsetup' : (BinaryMatrixSetup.select (rows s) D).operations ≤
      1400*((rows s).size+6)^2*P^3 := by
    have hh := Nat.mul_le_mul (Nat.mul_le_mul_left 1400 hfactor) (Nat.pow_le_pow_left hsize 2)
    apply hsetup.trans
    exact hh.trans_eq (by ring)
  have hm : 1 ≤ growthBase s h^k := one_le_pow₀ hg.1
  have hP35 : P^3≤P^5 := Nat.pow_le_pow_right (by dsimp [P];omega) (by decide)
  have hsetup'' := (hsetup'.trans (Nat.mul_le_mul_left _ hP35)).trans (Nat.le_mul_of_pos_right _ hm)
  change _ ≤ constant s h*P^5*growthBase s h^k
  simp only [run,constant]
  nlinarith

attribute [local irreducible] run constant

/-- One fixed base works at every size. The exponent applies to scalar and address bit
operations, with a fifth-degree factor in input/address binary lengths.
It is not a claim about the complete graph algorithm or compiler memory costs. -/
theorem exists_uniform_addressed_program : ∃ s : ℕ, ∃ hs : 0 < s, ∃ h : CWTargetExtractionRate.Sample s,
    ∃ ht : 0 < CWHomogeneousCopies.copies s h, ∃ C : ℝ, 0 < C ∧
    ∀ n D p : ℕ, ∀ hD : 0 < D, ∀ hn : (n-1)^500 ≤ D^861, ∀ hp : p ≤ D^15,
    ∀ H : ℕ, 1 ≤ H → ∀ x : Table (PaddedMatrix.matrix n D) Cell,
    ∀ y : Table (PaddedMatrix.matrix D p) Cell,
    BinaryRetainedBounds.Bounded x H → BinaryRetainedBounds.Bounded y H →
    ((run s hs h ht hD hn hp x y).bitSteps:ℝ) ≤
      C*(D.size+H.size+6)^5*(D:ℝ)^CWFiniteBase.exponent := by
  obtain ⟨s,hs,h,ht,hg⟩ := CWFiniteBase.exists_positive_base
  rw [CWRectangularRanks.growth_identity] at hg
  let C : ℝ := (constant s h+1)*(rows s:ℝ)^CWFiniteBase.exponent
  have hrow : (0:ℝ) < rows s := by exact_mod_cast CWRectangularRanks.rows_pos s
  have hC : 0 < C := mul_pos (by exact_mod_cast Nat.zero_lt_succ (constant s h))
    (Real.rpow_pos_of_pos hrow _)
  refine ⟨s,hs,h,ht,C,hC,?_⟩
  intro n D p hD hn hp H hH x y hx hy
  let k := (BinaryMatrixSetup.select (rows s) D).value.2
  have hb := run_bits s hs h ht hD hn hp H hH x y hx hy
  have hq := (PaddedMatrixScale.bases_gt_one s hs).2.1
  have hsize : ((rows s)^k:ℝ) ≤ (rows s:ℝ)*D := by
    exact_mod_cast (BinaryMatrixSetup.select_bounds (rows s) D hq hD).2.1
  have hpow : (growthBase s h:ℝ)^k ≤ (rows s:ℝ)^CWFiniteBase.exponent*(D:ℝ)^CWFiniteBase.exponent := by
    calc
      _ ≤ ((rows s:ℝ)^CWFiniteBase.exponent)^k :=
        pow_le_pow_left₀ (by positivity) (growth_bounds s h hg) k
      _ = ((rows s:ℝ)^k)^CWFiniteBase.exponent := by
        rw [←Real.rpow_mul_natCast (by positivity),←Real.rpow_natCast_mul (by positivity)]
        rw [mul_comm]
      _ ≤ ((rows s:ℝ)*D)^CWFiniteBase.exponent :=
        Real.rpow_le_rpow (by positivity) hsize (by norm_num [CWFiniteBase.exponent])
      _ = _ := Real.mul_rpow (by positivity) (by positivity)
  have hbR : ((run s hs h ht hD hn hp x y).bitSteps:ℝ) ≤
      (constant s h:ℝ)*(D.size+H.size+6)^5*(growthBase s h:ℝ)^k := by exact_mod_cast hb
  have htotal := hbR.trans (mul_le_mul_of_nonneg_left hpow (by positivity))
  calc
    _ ≤ (constant s h:ℝ)*(D.size+H.size+6)^5*
        ((rows s:ℝ)^CWFiniteBase.exponent*(D:ℝ)^CWFiniteBase.exponent) := htotal
    _ ≤ ((constant s h:ℝ)+1)*(D.size+H.size+6)^5*
        ((rows s:ℝ)^CWFiniteBase.exponent*(D:ℝ)^CWFiniteBase.exponent) := by gcongr; linarith
    _ = _ := by dsimp [C]; ring

#print axioms run_value
#print axioms run_correct
#print axioms growth_properties
#print axioms run_bits
#print axioms exists_uniform_addressed_program
end ThinMatrix.CWBinaryAddressedBound
