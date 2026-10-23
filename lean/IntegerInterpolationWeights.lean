import IntegerInterpolationRows
import RationalInterpolation

set_option autoImplicit false

/-! A single retained denominator for all interpolation weights. No repeated
rational addition multiplies denominators across tensor terms. -/
namespace ThinMatrix.IntegerInterpolationWeights
open scoped BigOperators
open Polynomial IntegerInterpolationRows

noncomputable def numerator (d : ℕ) (i : Fin (d+1)) : ℤ[X] :=
  ∏ j : Fin (d+1), if j=i then 1 else X-C (j.val:ℤ)

def delta (d : ℕ) (i : Fin (d+1)) : ℤ :=
  ∏ j : Fin (d+1), if j=i then 1 else (i.val:ℤ)-j.val

theorem row_coeff (d : ℕ) (i k : Fin (d+1)) :
    (row d i).coeff.get k=(numerator d i).coeff k.val := by
  rw [row,build_coeff]
  simp only [poly,List.map_ofFn,Function.comp_def,id_eq,List.prod_ofFn,numerator]

theorem row_den (d : ℕ) (i : Fin (d+1)) : (row d i).den=delta d i := by
  rw [row,build_den]
  simp only [denom,List.map_ofFn,Function.comp_def,id_eq,List.prod_ofFn,delta]

theorem delta_ne_zero (d : ℕ) (i : Fin (d+1)) : delta d i≠0 := by
  rw [← row_den,row,build_den]
  exact denom_ne_zero _ _

theorem skip_product {M : Type*} [CommMonoid M] (d : ℕ) (i : Fin (d+1)) (f : Fin (d+1) → M) :
    (∏ j, if j=i then 1 else f j)=∏ j ∈ Finset.univ.erase i,f j := by
  rw [Finset.prod_ite]
  simp only [Finset.prod_const_one,one_mul]
  congr 1
  ext j
  simp

theorem lagrange_basis (d : ℕ) (i : Fin (d+1)) :
    Lagrange.basis Finset.univ RationalInterpolation.node i =
      C ((delta d i:ℚ)⁻¹)*(numerator d i).map (Int.castRingHom ℚ) := by
  simp only [numerator,delta,skip_product,Lagrange.basis,Lagrange.basisDivisor,
    RationalInterpolation.node,Finset.prod_mul_distrib,Polynomial.map_prod,
    Polynomial.map_sub,Polynomial.map_X,Polynomial.map_C]
  simp [← map_prod,Finset.prod_inv_distrib]

structure Table (d : ℕ) where
  rows : Vector (Row d) (d+1)
  weights : Vector ℤ (d+1)
  denominator : ℤ
  operations : ℕ
  control : ℕ

/-- Counted multiplication; every factor and intermediate integer is stored. -/
def product : List ℤ → ℤ × ℕ
  | [] => (1,0)
  | z::xs => let child := product xs;(z*child.1,child.2+1)

theorem product_value (xs : List ℤ) : (product xs).1=xs.prod := by
  induction xs with
  | nil => rfl
  | cons z xs ih => simp [product,ih]

theorem product_operations (xs : List ℤ) : (product xs).2=xs.length := by
  induction xs with
  | nil => rfl
  | cons z xs ih => simp [product,ih]

def prepare (d : ℕ) (k : Fin (d+1)) : Table d :=
  let rows := Vector.ofFn (row d)
  let weights := Vector.ofFn (fun i : Fin (d+1) =>
    let p := product (List.ofFn (fun j : Fin (d+1) => if j=i then 1 else (rows.get j).den))
    ((rows.get i).coeff.get k*p.1,p.2+1))
  let den := product (List.ofFn (fun j : Fin (d+1) => (rows.get j).den))
  ⟨rows,weights.map Prod.fst,den.1,
    (rows.toList.map Row.operations).sum+(weights.toList.map Prod.snd).sum+den.2,
    (rows.toList.map Row.control).sum+10*(d+1)^2+10*(d+1)⟩

def commonDen (d : ℕ) : ℤ := ∏ i : Fin (d+1),delta d i

def weightNumerator (d : ℕ) (k i : Fin (d+1)) : ℤ :=
  (row d i).coeff.get k*(∏ j : Fin (d+1),if j=i then 1 else delta d j)

theorem prepare_weight (d : ℕ) (k i : Fin (d+1)) :
    (prepare d k).weights.get i=weightNumerator d k i := by
  simp only [prepare,weightNumerator,Vector.get_map,Vector.get_ofFn,product_value,List.prod_ofFn,row_den]

theorem prepare_den (d : ℕ) (k : Fin (d+1)) :
    (prepare d k).denominator=commonDen d := by
  simp only [prepare,commonDen,Vector.get_ofFn,product_value,List.prod_ofFn,row_den]

theorem commonDen_ne_zero (d : ℕ) : commonDen d≠0 :=
  Finset.prod_ne_zero_iff.mpr (fun i _ => delta_ne_zero d i)

theorem commonDen_factor (d : ℕ) (i : Fin (d+1)) :
    commonDen d=delta d i*(∏ j,if j=i then 1 else delta d j) := by
  rw [skip_product]
  exact (Finset.mul_prod_erase Finset.univ (delta d) (Finset.mem_univ i)).symm

theorem weight_value (d : ℕ) (k i : Fin (d+1)) :
    (weightNumerator d k i:ℚ)/(commonDen d:ℚ)=RationalInterpolation.weight d k.val i := by
  rw [RationalInterpolation.weight,lagrange_basis,coeff_C_mul,coeff_map]
  simp only [weightNumerator,row_coeff,Int.cast_mul]
  rw [commonDen_factor d i]
  have hd : (delta d i:ℚ)≠0 := by exact_mod_cast delta_ne_zero d i
  have ho : ((∏ j : Fin (d+1),if j=i then 1 else delta d j:ℤ):ℚ)≠0 := by
    have hz : (∏ j : Fin (d+1),if j=i then 1 else delta d j : ℤ)≠0 := by
      apply Finset.prod_ne_zero_iff.mpr
      intro j _
      split_ifs
      · exact one_ne_zero
      · exact delta_ne_zero d j
    exact_mod_cast hz
  simp only [Int.cast_mul]
  field_simp
  rfl

def rowBound (d : ℕ) : ℕ := envelope d^(d+1)
def coefficientBound (d : ℕ) : ℕ := rowBound d^(d+2)

theorem row_magnitude (d : ℕ) (i : Fin (d+1)) :
    (∀ k,((row d i).coeff.get k).natAbs≤rowBound d) ∧ (row d i).den.natAbs≤rowBound d := by
  simpa only [row,rowBound,List.length_ofFn] using build_magnitude d i (List.ofFn id)

theorem delta_magnitude (d : ℕ) (i : Fin (d+1)) : (delta d i).natAbs≤rowBound d := by
  rw [← row_den]
  exact (row_magnitude d i).2

theorem product_magnitude {a : Type*} [Fintype a] (f : a → ℤ) (H : ℕ)
    (h : ∀ i,(f i).natAbs≤H) : (∏ i,f i).natAbs≤H^Fintype.card a := by
  change Int.natAbsHom (∏ i,f i) ≤ _
  rw [map_prod]
  exact (Finset.prod_le_pow_card Finset.univ _ H (fun i _ => h i)).trans_eq (by simp)

theorem commonDen_magnitude (d : ℕ) : (commonDen d).natAbs≤rowBound d^(d+1) := by
  simpa only [commonDen,Fintype.card_fin] using product_magnitude (delta d) (rowBound d) (delta_magnitude d)

theorem weight_magnitude (d : ℕ) (k i : Fin (d+1)) :
    (weightNumerator d k i).natAbs≤coefficientBound d := by
  have hp : 0<rowBound d := by unfold rowBound envelope;positivity
  have hh := product_magnitude (fun j : Fin (d+1) => if j=i then 1 else delta d j)
    (rowBound d) (fun j => by
      split_ifs
      · simpa only [Int.natAbs_one] using (show 1≤rowBound d by omega)
      · exact delta_magnitude d j)
  simp only [Fintype.card_fin] at hh
  unfold weightNumerator coefficientBound
  rw [Int.natAbs_mul]
  calc
    _ ≤ rowBound d*(rowBound d^(d+1)) := Nat.mul_le_mul ((row_magnitude d i).1 k) hh
    _ = _ := (pow_succ' (rowBound d) (d+1)).symm

theorem prepare_operations (d : ℕ) (k : Fin (d+1)) :
    (prepare d k).operations ≤ (d+1)^2*(2*(d+1)+2)+(d+1)*(d+2)+(d+1) := by
  simp only [prepare,Vector.toList_ofFn,List.map_ofFn,Function.comp_def,
    List.sum_ofFn,product_operations,List.length_ofFn,Finset.sum_const,
    Finset.card_univ,Fintype.card_fin,smul_eq_mul]
  have h : (∑ i : Fin (d+1),(row d i).operations) ≤ (d+1)*((d+1)*(2*(d+1)+2)) := by
    calc
      _ ≤ ∑ _ : Fin (d+1),(d+1)*(2*(d+1)+2) := Finset.sum_le_sum (fun i _ => by
        simpa only [row,List.length_ofFn] using build_operations d i (List.ofFn id))
      _ = _ := by simp
  nlinarith

theorem prepare_control (d : ℕ) (k : Fin (d+1)) :
    (prepare d k).control ≤ (d+1)*((d+1)+(d+1)*(8*(d+1)+8))+10*(d+1)^2+10*(d+1) := by
  simp only [prepare,Vector.toList_ofFn,List.map_ofFn,Function.comp_def,List.sum_ofFn]
  apply Nat.add_le_add_right
  apply Nat.add_le_add_right
  calc
    _ ≤ ∑ _ : Fin (d+1),((d+1)+(d+1)*(8*(d+1)+8)) := Finset.sum_le_sum (fun i _ => by
      simpa only [row,List.length_ofFn] using build_control d i (List.ofFn id))
    _ = _ := by simp

def bitEnvelope (d : ℕ) : ℕ := envelope d*((d+1)*(d+2))+1

theorem coefficientBound_bits (d : ℕ) {z : ℤ} (hz : z.natAbs≤coefficientBound d) :
    z.natAbs.size≤bitEnvelope d := by
  apply Nat.size_le.mpr
  have hb : coefficientBound d≤2^(envelope d*((d+1)*(d+2))) := by
    unfold coefficientBound rowBound
    rw [← pow_mul]
    calc
      _ ≤ (2^(envelope d))^((d+1)*(d+2)) := Nat.pow_le_pow_left (Nat.lt_two_pow_self).le _
      _ = _ := (pow_mul _ _ _).symm
  unfold bitEnvelope
  exact (hz.trans hb).trans_lt (by
    rw [pow_succ]
    have := Nat.two_pow_pos (envelope d*((d+1)*(d+2)))
    omega)

theorem prepare_weight_bits (d : ℕ) (k i : Fin (d+1)) :
    ((prepare d k).weights.get i).natAbs.size≤bitEnvelope d := by
  rw [prepare_weight]
  exact coefficientBound_bits d (weight_magnitude d k i)

theorem prepare_den_bits (d : ℕ) (k : Fin (d+1)) :
    (prepare d k).denominator.natAbs.size≤bitEnvelope d := by
  rw [prepare_den]
  apply coefficientBound_bits d
  exact (commonDen_magnitude d).trans (Nat.pow_le_pow_right (by
    have : 0<rowBound d := by unfold rowBound envelope;positivity
    omega) (by omega))

#print axioms coefficientBound_bits
#print axioms prepare_weight_bits
#print axioms prepare_den_bits
#print axioms row_magnitude
#print axioms delta_magnitude
#print axioms product_magnitude
#print axioms commonDen_magnitude
#print axioms weight_magnitude
#print axioms prepare_operations
#print axioms prepare_control
#print axioms commonDen_factor
#print axioms weight_value
#print axioms row_coeff
#print axioms row_den
#print axioms delta_ne_zero
#print axioms skip_product
#print axioms lagrange_basis
#print axioms product_value
#print axioms product_operations
#print axioms prepare_weight
#print axioms prepare_den
#print axioms commonDen_ne_zero
end ThinMatrix.IntegerInterpolationWeights
