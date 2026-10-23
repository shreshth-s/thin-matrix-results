import ClearedRecursiveBase
import BinaryModularCell

set_option autoImplicit false

namespace ThinMatrix.BinaryRecursiveRecovery
open scoped BigOperators
open RecursiveTable (Layout Table read)
open RetainedEqualCopy (Base copies)
open FiniteTrilinear FiniteDirectSum PolynomialDegeneration
open BinaryCell BinaryRecursiveDot
variable {I J K : Type} [Fintype I] [Fintype J] [Fintype K] {r t : ℕ}

def power (d : Cell) : ℕ → Run Cell
  | 0 => ⟨BinaryModularCell.one,0,2⟩
  | k+1 =>
      let previous := power d k
      let next := mul d previous.value
      ⟨next.value,previous.bitSteps+next.bitSteps,previous.control+8⟩

theorem power_view (d : Cell) (k : ℕ) : view (power d k).value=(view d)^k := by
  induction k with
  | zero => simp [power]
  | succ k ih => simp [power,ih,pow_succ']

theorem power_control (d : Cell) (k : ℕ) : (power d k).control=8*k+2 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [power,ih];omega

theorem power_bits (d : Cell) (k W : ℕ) (hd : 1≤(view d).natAbs)
    (hW : ((view d).natAbs^k).size≤W) :
    (power d k).bitSteps≤k*BackendScalarBits.backendScalarUnit W := by
  induction k with
  | zero => simp [power]
  | succ k ih =>
    have hprev := Nat.pow_le_pow_right hd (Nat.le_succ k)
    have hbase : (view d).natAbs≤(view d).natAbs^(k+1) := by
      simpa using Nat.pow_le_pow_right hd (show 1≤k+1 by omega)
    have ht := ih ((Nat.size_le_size hprev).trans hW)
    have hm := mul_price W d (power d k).value
      ((Nat.size_le_size hbase).trans hW) (by
        rw [power_view,Int.natAbs_pow]
        exact (Nat.size_le_size hprev).trans hW)
    simp only [power]
    nlinarith

def recover {A : Type} (a : Layout A) (d : Cell) (x : Table a Cell) : Run (Table a Cell) :=
  tabulate a (fun i => let q := BinaryModularCell.floor d (read x i); ⟨q.value,q.bitSteps,8⟩)

theorem recover_view {A : Type} (a : Layout A) (d : Cell) (x : Table a Cell)
    (hd : 0≤view d) (i : A) :
    view (read (recover a d x).value i)=view (read x i)/view d := by
  simp only [recover,tabulate_read,BinaryModularCell.floor_view d _ hd]

theorem recover_bits {A : Type} [Fintype A] (a : Layout A) (d : Cell) (x : Table a Cell)
    (W : ℕ) (hd : (view d).natAbs.size≤W) (hx : ∀ i,(view (read x i)).natAbs.size≤W) :
    (recover a d x).bitSteps≤a.size*(1024*(W+1)^2) :=
  BinaryRetainedBounds.tabulate_bits_le a _ _ (fun i => BinaryModularCell.floor_price_square W d (read x i) hd (hx i))

theorem recover_control {A : Type} [Fintype A] (a : Layout A) (d : Cell) (x : Table a Cell) :
    (recover a d x).control=40*a.size+8 := by
  rw [recover,tabulate_control]
  simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul,←RecursiveTable.size_eq_card a]
  ring

def execute {a : Layout I} {b : Layout J} {c : Layout K} (ht : 0<t)
    (d : Base r t a b c ℚ) (k : ℕ)
    (x : Table (copies t a k) Cell) (y : Table (copies t b k) Cell) : Run (Table (copies t c k) Cell) :=
  let prepared := ClearedRecursiveBase.encode d
  let baseDenom := BinaryMultiplierAdapter.encodeInteger ((ClearedRecursiveBase.common d:ℤ)^3)
  let denom := power baseDenom.value k
  let product := BinaryRetainedEqualCopy.run a b c ht prepared.value k x y
  let output := recover (copies t c k) denom.value product.value
  ⟨output.value,prepared.bitSteps+baseDenom.bitSteps+denom.bitSteps+product.bitSteps+output.bitSteps,
    prepared.control+denom.control+product.control+output.control+16⟩

theorem execute_correct {a : Layout I} {b : Layout J} {c : Layout K} (ht : 0<t)
    (d : Base r t a b c ℚ) (u : Tensor I J K ℤ)
    (hd : total d.terms=diagonal (Fin t) (fun i j k => (u i j k:ℚ)))
    (k : ℕ) (x : Table (copies t a k) Cell) (y : Table (copies t b k) Cell)
    (z : Fin t×PowerIndex K k) :
    view (read (execute ht d k x y).value z)=bilinear (tensorPower u k)
      (fun i => view (read x (z.1,i))) (fun j => view (read y (z.1,j))) z.2 := by
  have hp : 0<ClearedRecursiveBase.common d := FiniteRationalCoefficients.denominator_pos d.terms
  have hdv : view (power (BinaryMultiplierAdapter.encodeInteger ((ClearedRecursiveBase.common d:ℤ)^3)).value k).value=
      (ClearedRecursiveBase.common d:ℤ)^(3*k) := by
    rw [power_view]
    change ((BinaryMultiplierAdapter.encodeInteger _).value.view)^k=_
    rw [BinaryMultiplierAdapter.encodeInteger_view,←pow_mul]
  have hd0 : 0≤view (power (BinaryMultiplierAdapter.encodeInteger ((ClearedRecursiveBase.common d:ℤ)^3)).value k).value := by
    rw [hdv];positivity
  simp only [execute,recover_view _ _ _ hd0,hdv]
  exact ClearedRecursiveBase.exact_recovery ht d u hd k x y z

#print axioms power_view
#print axioms power_control
#print axioms power_bits
#print axioms recover_view
#print axioms recover_bits
#print axioms recover_control
#print axioms execute_correct
end ThinMatrix.BinaryRecursiveRecovery
