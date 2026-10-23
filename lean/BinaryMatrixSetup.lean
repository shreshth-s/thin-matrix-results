import PaddedMatrixScale
import ToomExecutionBound

set_option autoImplicit false

/-! Charged depth selection for the retained rectangular program. The existing
binary padding loop finds the first power strictly larger than the middle
size. Strictness also absorbs the upward-rounded first dimension, without
an unpriced logarithm or an additional variable-size search. -/
namespace ThinMatrix.BinaryMatrixSetup
open scoped BigOperators
open RecursiveTable (Table fin read)
open BinaryCell

def select (q D : ℕ) := ToomExecutionBound.choosePadding q D

theorem select_value (q D : ℕ) (hq : 2 ≤ q) (hD : 0 < D) :
    (select q D).value = (q^(Nat.log q D+1),Nat.log q D+1) :=
  ToomExecutionBound.choosePadding_value q D hq hD

theorem select_bits (q D : ℕ) (hq : 2 ≤ q) (hD : 0 < D) :
    (select q D).operations ≤ 1400*(D.size+3)*(q.size+D.size+6)^2 :=
  ToomExecutionBound.choosePadding_operations_bound q D hq hD

theorem select_bounds (q D : ℕ) (hq : 2 ≤ q) (hD : 0 < D) :
    D < q^(select q D).value.2 ∧ q^(select q D).value.2 ≤ q*D ∧
    (select q D).value.2 ≤ D.size+1 := by
  rw [select_value q D hq hD]
  exact ⟨(ToomCook.padded_length_bounds q D hq hD).1,
    (ToomCook.padded_length_bounds q D hq hD).2,
    ToomExecutionBound.padded_depth_le_size q D hq hD⟩

/-- An integer shape contract, valid also for an empty outer dimension. -/
theorem selected_fits (a q c D n p num den z : ℕ) (hq : 2 ≤ q) (hD : 0 < D)
    (hnz : 0 < num) (hdz : 0 < den) (ha : a^den=q^num) (hc : c=q^z)
    (hn : (n-1)^den ≤ D^num) (hp : p ≤ D^z) :
    n ≤ a^(select q D).value.2 ∧ D ≤ q^(select q D).value.2 ∧
    p ≤ c^(select q D).value.2 := by
  let k := (select q D).value.2
  have hb := select_bounds q D hq hD
  have he : (q^k)^num=(a^k)^den := by
    rw [←pow_mul, Nat.mul_comm k num, pow_mul, ←ha, ←pow_mul,
      Nat.mul_comm den k, pow_mul]
  have hlt : (n-1)^den < (a^k)^den := by
    rw [←he]
    exact hn.trans_lt (Nat.pow_lt_pow_left hb.1 (Nat.ne_of_gt hnz))
  have hfirst : n-1 < a^k := (Nat.pow_lt_pow_iff_left (Nat.ne_of_gt hdz)).mp hlt
  have hapos : 0 < a := by
    by_contra h
    have az : a=0 := by omega
    rw [az, zero_pow (Nat.ne_of_gt hdz)] at ha
    have : 0 < q^num := pow_pos (by omega) _
    omega
  change n ≤ a^k ∧ D ≤ q^k ∧ p ≤ c^k
  refine ⟨by have := pow_pos hapos k; omega,hb.1.le,?_⟩
  have h := hp.trans (Nat.pow_le_pow_left hb.1.le z)
  simpa only [hc,←pow_mul,k,Nat.mul_comm] using h

variable {n D p : ℕ}

def execute (a q c num den z : ℕ) (hq : 2 ≤ q) (hD : 0 < D)
    (hnz : 0 < num) (hdz : 0 < den) (ha : a^den=q^num) (hc : c=q^z)
    {r t : ℕ} (ht : 0 < t)
    (d : RetainedEqualCopy.Base r t
      (RecursiveTable.prod (fin a) (fin q))
      (RecursiveTable.prod (fin q) (fin c))
      (RecursiveTable.prod (fin c) (fin a)) ℚ)
    (hn : (n-1)^den ≤ D^num) (hp : p ≤ D^z)
    (x : Table (PaddedMatrix.matrix n D) Cell) (y : Table (PaddedMatrix.matrix D p) Cell) :=
  let shape := select q D
  let hf := selected_fits a q c D n p num den z hq hD hnz hdz ha hc hn hp
  let out := PaddedMatrix.execute (fin a) (fin q) (fin c) ht d shape.value.2 hf.1 hf.2.2 x y
  (⟨out.value,shape.operations+out.bitSteps,out.control+8⟩ : BinaryGroupedCoordinates.Run _)

theorem execute_correct (a q c num den z : ℕ) (hq : 2 ≤ q) (hD : 0 < D)
    (hnz : 0 < num) (hdz : 0 < den) (ha : a^den=q^num) (hc : c=q^z)
    {r t : ℕ} (ht : 0 < t)
    (d : RetainedEqualCopy.Base r t
      (RecursiveTable.prod (fin a) (fin q))
      (RecursiveTable.prod (fin q) (fin c))
      (RecursiveTable.prod (fin c) (fin a)) ℚ)
    (hd : FiniteTrilinear.total d.terms = FiniteDirectSum.diagonal (Fin t)
      (FiniteMatrixTensor.coeff (Fin a) (Fin q) (Fin c) ℚ))
    (hn : (n-1)^den ≤ D^num) (hp : p ≤ D^z)
    (x : Table (PaddedMatrix.matrix n D) Cell) (y : Table (PaddedMatrix.matrix D p) Cell)
    (i : Fin n × Fin p) :
    view (read (execute a q c num den z hq hD hnz hdz ha hc ht d hn hp x y).value i) =
      ∑ j : Fin D,view (read x (i.1,j))*view (read y (j,i.2)) :=
  PaddedMatrix.execute_correct _ _ _ ht d hd _
    (selected_fits a q c D n p num den z hq hD hnz hdz ha hc hn hp).1
    (selected_fits a q c D n p num den z hq hD hnz hdz ha hc hn hp).2.1
    (selected_fits a q c D n p num den z hq hD hnz hdz ha hc hn hp).2.2 x y i

#print axioms select_value
#print axioms select_bits
#print axioms select_bounds
#print axioms selected_fits
#print axioms execute_correct
end ThinMatrix.BinaryMatrixSetup
