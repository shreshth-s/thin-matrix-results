import ToomBitCost
import ToomDotCost

/-!
Local coefficient-register budgets for the actual finite Toom--Cook loops.
Partial evaluation and interpolation sums use the existing polynomial
coefficient bounds. Recombination uses actual shifted array reads, including
out-of-bounds zero coefficients. The suffix lemmas apply to every recursive
tail of a nodup index list; they do not rely on cancellation in a completed
sum. These are register-size obligations for the separate operation-counter
proofs, not a global running-time or machine-simulation theorem.
-/

namespace ThinMatrix.ToomLocalBudget
open scoped BigOperators
open Polynomial Finset
open ThinMatrix.ToomCook hiding dotCounted dotCounted_value
open ThinMatrix.ToomBitCost
noncomputable section

theorem evaluation_dot_partial_eq (P : Primitives) (hP : PrimitivesCorrect P)
    (k h : ℕ) (a : Array ℤ) (r : Fin (2*k-1)) (j : ℕ) (hj : j<h)
    (xs : List (Fin k)) (hxs : xs.Nodup) :
    (dotCounted P (fun i : Fin k => (r.val:ℤ)^i.val)
      (fun i => indexedRead P a i.val h j) xs).value =
      (∑ i ∈ xs.toFinset.image Fin.val,
        C ((r.val:ℤ)^i)*chunk h i (arrayPolynomial a)).coeff j := by
  rw [dotCounted_value P hP, ← List.sum_toFinset _ hxs]
  simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, chunk_coeff, if_pos hj]
  rw [Finset.sum_image (by intro i hi d hd heq; exact Fin.ext heq)]
  apply Finset.sum_congr rfl
  intro i hi
  rw [indexedRead_value P hP, arrayPolynomial_coeff]

theorem evaluation_dot_partial_bound (P : Primitives) (hP : PrimitivesCorrect P)
    (k h : ℕ) (a : Array ℤ) (r : Fin (2*k-1)) (j : ℕ) (hj : j<h)
    (xs : List (Fin k)) (hxs : xs.Nodup) (A : ℤ) (hA : 0≤A)
    (ha : CoeffBound (arrayPolynomial a) A) :
    |(dotCounted P (fun i : Fin k => (r.val:ℤ)^i.val)
      (fun i => indexedRead P a i.val h j) xs).value| ≤ (growthConstant k:ℤ)*A := by
  rw [evaluation_dot_partial_eq P hP k h a r j hj xs hxs]
  apply partialEvaluation_bound k h (arrayPolynomial a) r
    (xs.toFinset.image Fin.val) _ A hA ha j
  intro i hi
  obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hi
  exact Finset.mem_range.mpr d.isLt

theorem interpolation_dot_partial_bound (P : Primitives) (hP : PrimitivesCorrect P)
    (k h : ℕ) (p : Fin (2*k-1) → ℤ[X])
    (hp : ∀d, (p d).natDegree<2*h) (d : Fin (2*k-1)) (j : ℕ)
    (xs : List (Fin (2*k-1))) (hxs : xs.Nodup) (A : ℤ) (hA : 0≤A)
    (hv : ∀r, CoeffBound (p r) A) :
    |(dotCounted P (integerWeight (2*k-1) d)
      (fun r => readChild (Array.ofFn (fun r : Fin (2*k-1) =>
        Array.ofFn (fun j : Fin (2*h) => (p r).coeff j.val))) r.val j) xs).value| ≤
      (growthConstant k:ℤ)*A := by
  rw [dotCounted_value P hP, ← List.sum_toFinset _ hxs]
  simp only [readChild_ofFn_coeff (2*k-1) h p hp]
  have hb := partialInterpolation_bound k p d xs.toFinset A hA hv j
  simpa only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul] using hb

theorem read_evaluation_bound (P : Primitives) (hP : PrimitivesCorrect P)
    (k h : ℕ) (a : Array ℤ) (i : Fin k) (j : ℕ) (A : ℤ)
    (ha : CoeffBound (arrayPolynomial a) A) :
    |(indexedRead P a i.val h j).value| ≤ A := by
  rw [indexedRead_value P hP, ← arrayPolynomial_coeff]
  exact ha _

theorem read_interpolation_bound (k h : ℕ) (p : Fin (2*k-1) → ℤ[X])
    (hp : ∀d, (p d).natDegree<2*h) (r : Fin (2*k-1)) (j : ℕ) (A : ℤ)
    (hv : ∀r, CoeffBound (p r) A) :
    |(readChild (Array.ofFn (fun r : Fin (2*k-1) =>
      Array.ofFn (fun j : Fin (2*h) => (p r).coeff j.val))) r.val j).value| ≤ A := by
  rw [readChild_ofFn_coeff (2*k-1) h p hp]
  exact hv r j

theorem unweighted_dot_partial_bound (P : Primitives) (hP : PrimitivesCorrect P)
    (M : ℕ) (read : Fin M → ToomCook.Counted ℤ)
    (xs : List (Fin M)) (hxs : xs.Nodup) (A : ℤ) (hA : 0≤A)
    (hread : ∀d, |(read d).value| ≤ A) :
    |(dotCounted P (fun _ : Fin M => 1) read xs).value| ≤ (M:ℤ)*A := by
  rw [dotCounted_value P hP, ← List.sum_toFinset _ hxs]
  calc
    |∑i∈xs.toFinset, (1:ℤ)*(read i).value| ≤
        (∑_i∈xs.toFinset, |(1:ℤ)|)*A :=
      integer_linear_combination_bound _ _ _ A (fun i _ => hread i)
    _ = (xs.toFinset.card:ℤ)*A := by simp
    _ ≤ (M:ℤ)*A := mul_le_mul_of_nonneg_right
      (by
        have hc : xs.toFinset.card ≤ M := by simpa using Finset.card_le_univ xs.toFinset
        exact_mod_cast hc) hA

theorem recombination_dot_partial_bound (P : Primitives) (hP : PrimitivesCorrect P)
    (k h : ℕ) (p : Fin (2*k-1) → ℤ[X])
    (hp : ∀d, (p d).natDegree<2*h) (j : ℕ)
    (xs : List (Fin (2*k-1))) (hxs : xs.Nodup) (A : ℤ) (hA : 0≤A)
    (hv : ∀r, CoeffBound (p r) A) :
    |(dotCounted P (fun _ : Fin (2*k-1) => 1)
      (fun d => if h*d.val≤j then
        readChild (Array.ofFn (fun r : Fin (2*k-1) =>
          Array.ofFn (fun j : Fin (2*h) => (p r).coeff j.val))) d.val (j-h*d.val)
        else ⟨0,d.val.size+j.size+1⟩) xs).value| ≤ ((2*k-1:ℕ):ℤ)*A := by
  apply unweighted_dot_partial_bound P hP (2*k-1) _ xs hxs A hA
  intro d
  split_ifs
  · exact read_interpolation_bound k h p hp d _ A hv
  · simpa using hA

theorem register_bits_of_abs_le (z : ℤ) (N : ℕ) (hz : |z|≤(N:ℤ)) :
    z.natAbs.size ≤ N.size := by
  apply Nat.size_le_size
  exact_mod_cast (show (z.natAbs:ℤ)≤(N:ℤ) by
    simpa only [Int.natCast_natAbs] using hz)

theorem fixed_product_bits (C A : ℕ) :
    (C*A).size ≤ C.size+A.size+1 := by
  simpa using size_powerProduct_bound 1 C A 0 1 1

theorem evaluation_dot_suffix_bits (P : Primitives) (hP : PrimitivesCorrect P)
    (k h : ℕ) (a : Array ℤ) (r : Fin (2*k-1)) (j : ℕ) (hj : j<h)
    (xs : List (Fin k)) (hxs : xs.Nodup) (t A : ℕ)
    (ha : CoeffBound (arrayPolynomial a) (A:ℤ)) :
    (dotCounted P (fun i : Fin k => (r.val:ℤ)^i.val)
      (fun i => indexedRead P a i.val h j) (xs.drop t)).value.natAbs.size ≤
        (growthConstant k).size + A.size + 1 := by
  have hb := evaluation_dot_partial_bound P hP k h a r j hj
    (xs.drop t) ((List.drop_sublist t xs).nodup hxs) (A:ℤ) (by positivity) ha
  have hn := register_bits_of_abs_le _ (growthConstant k*A) (by
    simpa only [Nat.cast_mul] using hb)
  exact hn.trans (fixed_product_bits _ _)

theorem interpolation_dot_suffix_bits (P : Primitives) (hP : PrimitivesCorrect P)
    (k h : ℕ) (p : Fin (2*k-1) → ℤ[X])
    (hp : ∀d, (p d).natDegree<2*h) (d : Fin (2*k-1)) (j : ℕ)
    (xs : List (Fin (2*k-1))) (hxs : xs.Nodup) (t A : ℕ)
    (hv : ∀r, CoeffBound (p r) (A:ℤ)) :
    (dotCounted P (integerWeight (2*k-1) d)
      (fun r => readChild (Array.ofFn (fun r : Fin (2*k-1) =>
        Array.ofFn (fun j : Fin (2*h) => (p r).coeff j.val))) r.val j)
      (xs.drop t)).value.natAbs.size ≤ (growthConstant k).size+A.size+1 := by
  have hb := interpolation_dot_partial_bound P hP k h p hp d j
    (xs.drop t) ((List.drop_sublist t xs).nodup hxs) (A:ℤ) (by positivity) hv
  have hn := register_bits_of_abs_le _ (growthConstant k*A) (by
    simpa only [Nat.cast_mul] using hb)
  exact hn.trans (fixed_product_bits _ _)

theorem recombination_dot_suffix_bits (P : Primitives) (hP : PrimitivesCorrect P)
    (k h : ℕ) (p : Fin (2*k-1) → ℤ[X])
    (hp : ∀d, (p d).natDegree<2*h) (j : ℕ)
    (xs : List (Fin (2*k-1))) (hxs : xs.Nodup) (t A : ℕ)
    (hv : ∀r, CoeffBound (p r) (A:ℤ)) :
    (dotCounted P (fun _ : Fin (2*k-1) => 1)
      (fun d => if h*d.val≤j then
        readChild (Array.ofFn (fun r : Fin (2*k-1) =>
          Array.ofFn (fun j : Fin (2*h) => (p r).coeff j.val))) d.val (j-h*d.val)
        else ⟨0,d.val.size+j.size+1⟩) (xs.drop t)).value.natAbs.size ≤
          (2*k-1).size+A.size+1 := by
  have hb := recombination_dot_partial_bound P hP k h p hp j
    (xs.drop t) ((List.drop_sublist t xs).nodup hxs) (A:ℤ) (by positivity) hv
  have hn := register_bits_of_abs_le _ ((2*k-1)*A) (by
    simpa only [Nat.cast_mul] using hb)
  exact hn.trans (fixed_product_bits _ _)

theorem shifted_read_bound (P : Primitives) (hP : PrimitivesCorrect P)
    (k h : ℕ) (p : Fin (2*k-1) → ℤ[X])
    (hp : ∀d, (p d).natDegree<2*h) (d : Fin (2*k-1)) (j : ℕ) (A : ℤ)
    (hA : 0≤A) (hv : ∀r, CoeffBound (p r) A) :
    |(shiftedRead P (Array.ofFn (fun r : Fin (2*k-1) =>
      Array.ofFn (fun j : Fin (2*h) => (p r).coeff j.val))) d.val h j).value| ≤ A := by
  rw [shiftedRead_value P hP]
  split_ifs
  · exact read_interpolation_bound k h p hp d _ A hv
  · simpa using hA

theorem shifted_dot_suffix_bits (P : Primitives) (hP : PrimitivesCorrect P)
    (k h : ℕ) (p : Fin (2*k-1) → ℤ[X])
    (hp : ∀d, (p d).natDegree<2*h) (j : ℕ)
    (xs : List (Fin (2*k-1))) (hxs : xs.Nodup) (t A : ℕ)
    (hv : ∀r, CoeffBound (p r) (A:ℤ)) :
    (dotCounted P (fun _ : Fin (2*k-1) => 1)
      (fun d => shiftedRead P (Array.ofFn (fun r : Fin (2*k-1) =>
        Array.ofFn (fun j : Fin (2*h) => (p r).coeff j.val))) d.val h j)
      (xs.drop t)).value.natAbs.size ≤ (2*k-1).size+A.size+1 := by
  have hb := unweighted_dot_partial_bound P hP (2*k-1)
    (fun d => shiftedRead P (Array.ofFn (fun r : Fin (2*k-1) =>
      Array.ofFn (fun j : Fin (2*h) => (p r).coeff j.val))) d.val h j)
    (xs.drop t) ((List.drop_sublist t xs).nodup hxs) (A:ℤ) (by positivity)
    (fun d => shifted_read_bound P hP k h p hp d j A (by positivity) hv)
  have hn := register_bits_of_abs_le _ ((2*k-1)*A) (by
    simpa only [Nat.cast_mul] using hb)
  exact hn.trans (fixed_product_bits _ _)

theorem evaluation_weight_bound (k : ℕ) (r : Fin (2*k-1)) (i : Fin k) :
    |(r.val:ℤ)^i.val| ≤ (growthConstant k:ℤ) := by
  apply le_trans _ (evaluation_row_le_growth k r)
  exact Finset.single_le_sum (f := fun i : ℕ => |(r.val:ℤ)^i|)
    (a := i.val) (fun i _ => abs_nonneg _) (Finset.mem_range.mpr i.isLt)

theorem interpolation_weight_bound (k : ℕ) (d r : Fin (2*k-1)) :
    |integerWeight (2*k-1) d r| ≤ (growthConstant k:ℤ) := by
  apply le_trans _ (interpolation_row_le_growth k d)
  exact Finset.single_le_sum (f := fun r : Fin (2*k-1) => |integerWeight (2*k-1) d r|)
    (a := r) (fun r _ => abs_nonneg _) (Finset.mem_univ r)

theorem product_register_bits (w z : ℤ) (W A : ℕ)
    (hw : |w|≤(W:ℤ)) (hz : |z|≤(A:ℤ)) :
    (w*z).natAbs.size ≤ W.size+A.size+1 := by
  have hp : |w*z|≤((W*A:ℕ):ℤ) := by
    rw [abs_mul, Nat.cast_mul]
    exact mul_le_mul hw hz (abs_nonneg z) (by positivity)
  exact (register_bits_of_abs_le _ _ hp).trans (fixed_product_bits _ _)

theorem exact_division_register_bits (P : Primitives) (hP : PrimitivesCorrect P)
    (D : ℕ) (hD : 0<D) (z w : ℤ) (hz : z=(D:ℤ)*w) :
    (P.divide D z).value.natAbs.size ≤ z.natAbs.size := by
  rw [hP.divide D z w hD hz]
  have he : w=z/(D:ℤ) := by
    rw [hz, Int.mul_ediv_cancel_left _ (Int.natCast_ne_zero.mpr (Nat.ne_of_gt hD))]
  have hab : |w|≤|z| := by
    rw [he]
    exact Int.abs_ediv_le_abs _ _
  apply register_bits_of_abs_le w z.natAbs
  simpa only [Int.natCast_natAbs] using hab

end
end ThinMatrix.ToomLocalBudget


namespace ThinMatrix.ToomLocalBudget
open scoped BigOperators
open Polynomial Finset
open ThinMatrix.ToomCook hiding dotCounted dotCounted_value
open ThinMatrix.ToomBitCost

theorem index_size_le_budget (k S A n : ℕ) (hn : n≤4*k^S) :
    n.size ≤ bitBudget k S A := by
  apply (Nat.size_le_size hn).trans
  have h := size_powerProduct_bound k 4 1 S 1 0
  simp only [pow_one,pow_zero,mul_one,mul_zero,add_zero,
    show (4:ℕ).size=3 by decide] at h
  have h' : (4*k^S).size ≤ k.size*S+4 := by
    rw [Nat.mul_comm] at h
    omega
  apply h'.trans
  unfold bitBudget bitSlope
  nlinarith

theorem evaluation_DotCaps (k h A W : ℕ) (hk : 1≤k) (hh : 1≤h)
    (a : Array ℤ) (ha : CoeffBound (arrayPolynomial a) (A:ℤ))
    (r : Fin (2*k-1)) (j : Fin h)
    (hwidth : (growthConstant k).size+A.size+1≤W)
    (hindex : ∀n≤2*k*h,n.size≤W) :
    DotCaps (fun i : Fin k => (r.val:ℤ)^i.val)
      (fun i => indexedRead bitPrimitives a i.val h j.val)
      (List.ofFn (id : Fin k → Fin k)) (180*(W+1)^2) W := by
  have haW : A.size≤W := by omega
  have hcW : (growthConstant k).size≤W := by omega
  have hread : ∀i : Fin k,
      (indexedRead bitPrimitives a i.val h j.val).value.natAbs.size≤A.size := by
    intro i
    exact register_bits_of_abs_le _ A
      (read_evaluation_bound bitPrimitives bitPrimitives_correct k h a i j.val A ha)
  constructor
  · intro i hi
    exact (register_bits_of_abs_le _ (growthConstant k)
      (evaluation_weight_bound k r i)).trans hcW
  · intro i hi
    exact (hread i).trans haW
  · intro i hi
    apply indexedRead_bit_cost
    · apply hindex;have hi:=i.isLt;nlinarith
    · apply hindex;nlinarith
    · apply hindex;have hj:=j.isLt;nlinarith
    · apply hindex;have hi:=i.isLt;nlinarith
    · apply hindex;have hi:=i.isLt;have hj:=j.isLt;nlinarith
    · simpa only [indexedRead_value bitPrimitives bitPrimitives_correct] using
        (hread i).trans haW
  · intro i hi
    exact (product_register_bits _ _ (growthConstant k) A
      (evaluation_weight_bound k r i)
      (read_evaluation_bound bitPrimitives bitPrimitives_correct k h a i j.val A ha)).trans hwidth
  · intro ys hys
    have hyn : ys.Nodup := hys.sublist.nodup (List.nodup_ofFn.mpr Function.injective_id)
    have hb := evaluation_dot_suffix_bits bitPrimitives bitPrimitives_correct k h a r
      j.val j.isLt ys hyn 0 A ha
    have hb' : (dotCounted bitPrimitives (fun i : Fin k => (r.val:ℤ)^i.val)
        (fun i => indexedRead bitPrimitives a i.val h j.val) ys).value.natAbs.size ≤
          (growthConstant k).size+A.size+1 := by simpa only [List.drop_zero] using hb
    exact hb'.trans hwidth

theorem evaluation_counted_cost (k s A : ℕ) (hk : 2≤k)
    (a : Array ℤ) (ha : CoeffBound (arrayPolynomial a) (A:ℤ))
    (r : Fin (2*k-1)) :
    (evaluateCounted bitPrimitives k (k^s) a r).operations ≤
      (k^s)*(k*330*(bitBudget k (s+1) A+1)^2+2*bitBudget k (s+1) A+4) := by
  let W := bitBudget k (s+1) A
  have hW : 1≤W := by unfold W bitBudget;omega
  have hc : (growthConstant k).size+A.size+1≤W := by
    unfold W bitBudget bitSlope
    nlinarith
  have hindex : ∀n≤2*k*(k^s),n.size≤W := by
    intro n hn
    apply index_size_le_budget k (s+1) A n
    rw [pow_succ]
    nlinarith
  have hd : ∀j : Fin (k^s),
      DotCaps (fun i : Fin k => (r.val:ℤ)^i.val)
        (fun i => indexedRead bitPrimitives a i.val (k^s) j.val)
        (List.ofFn (id : Fin k → Fin k)) (180*(W+1)^2) W := by
    intro j
    exact evaluation_DotCaps k (k^s) A W (by omega) (by
      have hh : 0<k^s := pow_pos (by omega) _
      omega) a ha r j hc hindex
  have h := evaluateCounted_operations_le k (k^s) (180*(W+1)^2) W a r hW hd
    (fun j => hindex j.val (by
      have hj:=j.isLt
      have hh : 0<k^s := pow_pos (by omega) _
      have hkh : k^s ≤ 2*k*(k^s) := by nlinarith
      omega))
  simpa only [← add_mul, show 180+150=330 by decide, Nat.mul_assoc, W] using h
end ThinMatrix.ToomLocalBudget

namespace ThinMatrix.ToomLocalBudget
open ThinMatrix.ToomCook hiding dotCounted dotCounted_value
open ThinMatrix.ToomBitCost

theorem evaluation_counted_cost_cubic (k s A : ℕ) (hk : 2≤k)
    (a : Array ℤ) (ha : CoeffBound (arrayPolynomial a) (A:ℤ))
    (r : Fin (2*k-1)) :
    (evaluateCounted bitPrimitives k (k^s) a r).operations ≤
      336*k^(s+1)*(bitBudget k (s+1) A+1)^3 := by
  let W := bitBudget k (s+1) A
  have h := evaluation_counted_cost k s A hk a ha r
  change (evaluateCounted bitPrimitives k (k^s) a r).operations ≤
    336*k^(s+1)*(W+1)^3
  have hlow : 2*W+4≤6*(W+1)^2 := by nlinarith
  have hlocal : k*330*(W+1)^2+2*W+4≤336*k*(W+1)^2 := by
    calc
      _ ≤ k*330*(W+1)^2+6*(W+1)^2 := by omega
      _ ≤ k*330*(W+1)^2+(6*k)*(W+1)^2 :=
        Nat.add_le_add_left (Nat.mul_le_mul_right _ (by omega : 6≤6*k)) _
      _ = _ := by ring
  have hquad : (evaluateCounted bitPrimitives k (k^s) a r).operations ≤
      336*k^(s+1)*(W+1)^2 := by
    calc
      _ ≤ k^s*(k*330*(W+1)^2+2*W+4) := h
      _ ≤ k^s*(336*k*(W+1)^2) := Nat.mul_le_mul_left _ hlocal
      _ = _ := by rw [pow_succ];ring
  exact hquad.trans (Nat.mul_le_mul_left _
    (Nat.pow_le_pow_right (by omega : 1≤W+1) (by decide : 2≤3)))
end ThinMatrix.ToomLocalBudget

#print axioms ThinMatrix.ToomLocalBudget.evaluation_DotCaps
#print axioms ThinMatrix.ToomLocalBudget.evaluation_counted_cost
#print axioms ThinMatrix.ToomLocalBudget.evaluation_counted_cost_cubic
