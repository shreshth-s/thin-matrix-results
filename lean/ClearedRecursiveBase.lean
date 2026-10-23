import BinaryRetainedBounds
import FiniteRationalCoefficients

set_option autoImplicit false

/-! Clear one fixed rational base before recursion. All three forms are
scaled, so the complete depth-k output has the single factor d^(3*k).
Only that complete output is divided. -/
namespace ThinMatrix.ClearedRecursiveBase
open scoped BigOperators
open FiniteTrilinear FiniteDirectSum PolynomialDegeneration RecursiveTable
open RetainedEqualCopy (Base copies)
variable {I J K : Type} [Fintype I] [Fintype J] [Fintype K] {r t : ℕ}

def common {a : Layout I} {b : Layout J} {c : Layout K} (d : Base r t a b c ℚ) :=
  FiniteRationalCoefficients.denominator d.terms

def numerator (d : ℕ) (q : ℚ) : ℤ := ((d:ℚ)*q).num

theorem numerator_cast (d : ℕ) (q : ℚ) (hq : ∃ z : ℤ,(d:ℚ)*q=z) :
    (numerator d q:ℚ)=(d:ℚ)*q := by
  obtain ⟨z,hz⟩ := hq
  simp [numerator,hz]

def cleared {a : Layout I} {b : Layout J} {c : Layout K} (d : Base r t a b c ℚ) : Base r t a b c ℤ :=
  ⟨d.left.map (numerator (common d)),d.middle.map (numerator (common d)),d.right.map (numerator (common d))⟩

theorem cleared_coefficients {a : Layout I} {b : Layout J} {c : Layout K} (d : Base r t a b c ℚ) :
    (∀ s i, (((cleared d).terms s).left i:ℚ)=(common d:ℚ)*(d.terms s).left i) ∧
    (∀ s j, (((cleared d).terms s).middle j:ℚ)=(common d:ℚ)*(d.terms s).middle j) ∧
    (∀ s k, (((cleared d).terms s).right k:ℚ)=(common d:ℚ)*(d.terms s).right k) := by
  have hh := FiniteRationalCoefficients.cleared d.terms
  refine ⟨fun s i => ?_,fun s j => ?_,fun s k => ?_⟩
  · simpa only [Base.terms,cleared,common,RecursiveTable.read,Vector.get_map] using numerator_cast _ _ (hh.1 s i)
  · simpa only [Base.terms,cleared,common,RecursiveTable.read,Vector.get_map] using numerator_cast _ _ (hh.2.1 s j)
  · simpa only [Base.terms,cleared,common,RecursiveTable.read,Vector.get_map] using numerator_cast _ _ (hh.2.2 s k)

theorem cleared_total {a : Layout I} {b : Layout J} {c : Layout K}
    (d : Base r t a b c ℚ) (u : Tensor I J K ℤ)
    (hd : total d.terms=diagonal (Fin t) (fun i j k => (u i j k:ℚ))) :
    total (cleared d).terms=diagonal (Fin t) (fun i j k => (common d:ℤ)^3*u i j k) := by
  have hcoef := cleared_coefficients d
  funext x y z
  apply Rat.intCast_injective
  have hsum : ((total (cleared d).terms x y z:ℤ):ℚ)=(common d:ℚ)^3*total d.terms x y z := by
    simp only [total,Term.tensor,Int.cast_sum,Int.cast_mul,hcoef.1,hcoef.2.1,hcoef.2.2,Finset.mul_sum]
    apply Finset.sum_congr rfl;intro s _;ring
  rw [hsum,hd]
  simp only [diagonal]
  split_ifs <;> push_cast <;> ring

omit [Fintype I] [Fintype J] [Fintype K] in
theorem tensorPower_scale {R : Type} [CommRing R] (d : R) (u : Tensor I J K R) (k : ℕ) :
    tensorPower (fun i j z => d*u i j z) k=fun i j z => d^k*tensorPower u k i j z := by
  induction k with
  | zero => funext i j z;simp [tensorPower]
  | succ k ih =>
    funext i j z
    simp only [tensorPower,product,ih,pow_succ]
    ring

theorem bilinear_scale {A B C R : Type} [Fintype A] [Fintype B] [CommRing R]
    (d : R) (u : Tensor A B C R) (x : A → R) (y : B → R) (z : C) :
    bilinear (fun i j k => d*u i j k) x y z=d*bilinear u x y z := by
  simp only [bilinear,Finset.mul_sum]
  apply Finset.sum_congr rfl;intro i _
  apply Finset.sum_congr rfl;intro j _
  ring

def encode {a : Layout I} {b : Layout J} {c : Layout K} (d : Base r t a b c ℚ) :
    BinaryGroupedCoordinates.Run (Base r t a b c BinaryCell.Cell) :=
  let v := cleared d
  let left := BinaryMultiplierAdapter.encodeVector v.left
  let right := BinaryMultiplierAdapter.encodeVector v.middle
  let output := BinaryMultiplierAdapter.encodeVector v.right
  ⟨⟨left.value,right.value,output.value⟩,left.bitSteps+right.bitSteps+output.bitSteps,
    16*(v.left.toArray.size+v.middle.toArray.size+v.right.toArray.size)+16⟩

theorem encode_denote {a : Layout I} {b : Layout J} {c : Layout K} (d : Base r t a b c ℚ) :
    BinaryRetainedEqualCopy.denoteBase (encode d).value=cleared d := by
  have hv {n : ℕ} (v : Vector ℤ n) :
      (BinaryMultiplierAdapter.encodeVector v).value.map BinaryCell.view=v := by
    apply Vector.ext;intro i hi
    have hh := BinaryMultiplierAdapter.encodeVector_get v ⟨i,hi⟩
    rw [Vector.getElem_map]
    exact hh
  dsimp only [BinaryRetainedEqualCopy.denoteBase,encode]
  rw [hv,hv,hv]

theorem binary_numerator {a : Layout I} {b : Layout J} {c : Layout K} (ht : 0<t)
    (d : Base r t a b c ℚ) (u : Tensor I J K ℤ)
    (hd : total d.terms=diagonal (Fin t) (fun i j k => (u i j k:ℚ)))
    (k : ℕ) (x : Table (copies t a k) BinaryCell.Cell) (y : Table (copies t b k) BinaryCell.Cell)
    (z : Fin t×PowerIndex K k) :
    BinaryCell.view (read (BinaryRetainedEqualCopy.run a b c ht (encode d).value k x y).value z)=
      (common d:ℤ)^(3*k)*bilinear (tensorPower u k)
        (fun i => BinaryCell.view (read x (z.1,i))) (fun j => BinaryCell.view (read y (z.1,j))) z.2 := by
  have hh := BinaryRetainedEqualCopy.run_correct a b c ht (encode d).value
    (fun i j l => (common d:ℤ)^3*u i j l)
    (by rw [encode_denote];exact cleared_total d u hd) k x y z
  rw [tensorPower_scale,bilinear_scale,←pow_mul] at hh
  exact hh

theorem exact_recovery {a : Layout I} {b : Layout J} {c : Layout K} (ht : 0<t)
    (d : Base r t a b c ℚ) (u : Tensor I J K ℤ)
    (hd : total d.terms=diagonal (Fin t) (fun i j k => (u i j k:ℚ)))
    (k : ℕ) (x : Table (copies t a k) BinaryCell.Cell) (y : Table (copies t b k) BinaryCell.Cell)
    (z : Fin t×PowerIndex K k) :
    BinaryCell.view (read (BinaryRetainedEqualCopy.run a b c ht (encode d).value k x y).value z) /
      (common d:ℤ)^(3*k)=bilinear (tensorPower u k)
        (fun i => BinaryCell.view (read x (z.1,i))) (fun j => BinaryCell.view (read y (z.1,j))) z.2 := by
  rw [binary_numerator ht d u hd]
  have hp : 0<common d := FiniteRationalCoefficients.denominator_pos d.terms
  have hn : (common d:ℤ)^(3*k)≠0 := pow_ne_zero _ (by exact_mod_cast (ne_of_gt hp))
  exact Int.mul_ediv_cancel_left _ hn

#print axioms numerator_cast
#print axioms cleared_coefficients
#print axioms cleared_total
#print axioms tensorPower_scale
#print axioms bilinear_scale
#print axioms encode_denote
#print axioms binary_numerator
#print axioms exact_recovery
end ThinMatrix.ClearedRecursiveBase
