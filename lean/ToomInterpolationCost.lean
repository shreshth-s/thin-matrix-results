import ToomLocalBudget
import ToomDotCost
import ToomBitCost

/-!
# Actual interpolation and recombination costs

These lemmas specialize the finite kernel bounds to the materialized recursive
child products. All coefficient, fixed-weight, product, suffix, quotient, and
signed-address register bounds are derived from the genuine node polynomials.
The only input hypotheses are the fixed arity condition and actual coefficient
bounds; no kernel-cost or width hypothesis is supplied by the caller.
-/

namespace ThinMatrix.ToomBitCost
open scoped BigOperators
open Polynomial Finset
open ThinMatrix.ToomCook
open ThinMatrix.ToomLocalBudget
noncomputable section
set_option maxHeartbeats 2000000

theorem interpolation_table_DotCaps (k h N W : ℕ)
    (p : Fin (2*k-1)→ℤ[X]) (hp : ∀r,(p r).natDegree<2*h)
    (hv : ∀r,CoeffBound (p r) (N:ℤ))
    (hwidth : (growthConstant k).size+N.size+1≤W)
    (d : Fin (2*k-1)) (j : ℕ)
    (hrow : ∀r : Fin (2*k-1),r.val.size≤W) (hj : j.size≤W) :
    DotCaps (integerWeight (2*k-1) d)
      (fun r : Fin (2*k-1)=>readChild (Array.ofFn (fun r : Fin (2*k-1)=>
        Array.ofFn (fun j : Fin (2*h)=>(p r).coeff j.val))) r.val j)
      (List.ofFn (id : Fin (2*k-1)→Fin (2*k-1))) (3*W+2) W := by
  have hrabs (r : Fin (2*k-1)) :=
    read_interpolation_bound k h p hp r j (N:ℤ) hv
  have hrbits (r : Fin (2*k-1)) :
      (readChild (Array.ofFn (fun r : Fin (2*k-1)=>
        Array.ofFn (fun j : Fin (2*h)=>(p r).coeff j.val))) r.val j).value.natAbs.size≤W :=
    (register_bits_of_abs_le _ N (hrabs r)).trans (by omega)
  have hwabs (r : Fin (2*k-1)) := interpolation_weight_bound k d r
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro r _
    exact (register_bits_of_abs_le _ (growthConstant k) (hwabs r)).trans (by omega)
  · intro r _
    exact hrbits r
  · intro r _
    exact readChild_cost _ _ _ W (hrbits r) (hrow r) hj
  · intro r _
    exact (product_register_bits _ _ (growthConstant k) N (hwabs r) (hrabs r)).trans hwidth
  · intro ys hys
    have hnodup : (List.ofFn (id : Fin (2*k-1)→Fin (2*k-1))).Nodup :=
      List.nodup_ofFn.mpr Function.injective_id
    have hab:=interpolation_dot_partial_bound bitPrimitives bitPrimitives_correct
      k h p hp d j ys (hys.sublist.nodup hnodup) (N:ℤ) (by positivity) hv
    have hb := register_bits_of_abs_le _ (growthConstant k*N)
      (by simpa only [Nat.cast_mul] using hab)
    exact hb.trans ((fixed_product_bits _ _).trans hwidth)

theorem interpolation_childProducts_DotCaps (k s A : ℕ) (hk : 2≤k)
    (a b : Array ℤ) (ha : CoeffBound (arrayPolynomial a) (A:ℤ))
    (hb : CoeffBound (arrayPolynomial b) (A:ℤ))
    (d : Fin (2*k-1)) (j : Fin (2*(k^s))) :
    DotCaps (integerWeight (2*k-1) d)
      (fun r : Fin (2*k-1)=>readChild (childProducts bitPrimitives k s a b) r.val j.val)
      (List.ofFn (id : Fin (2*k-1)→Fin (2*k-1)))
      (3*bitBudget k (s+1) A+2) (bitBudget k (s+1) A) := by
  let N:=k^s*(growthConstant k)^2*A^2
  let p:=fun r : Fin (2*k-1)=>
    (nodePolynomial k s (arrayPolynomial a) (arrayPolynomial b)).eval (C (r.val:ℤ))
  have hp : ∀r,(p r).natDegree<2*(k^s) :=
    fun r=>nodeEvaluation_natDegree k s hk _ _ r
  have hv : ∀r,CoeffBound (p r) (N:ℤ) := by
    intro r
    simpa only [p,N,Nat.cast_mul,Nat.cast_pow,mul_pow,mul_assoc] using
      nodeEvaluation_bound k s hk (arrayPolynomial a) (arrayPolynomial b) A ha hb r
  have hwidth : (growthConstant k).size+N.size+1≤bitBudget k (s+1) A := by
    have hn:=size_powerProduct_bound k (growthConstant k) A s 2 2
    change N.size≤_ at hn
    unfold bitBudget bitSlope
    nlinarith
  have hrow (r : Fin (2*k-1)) : r.val.size≤bitBudget k (s+1) A := by
    apply index_size_le_budget k (s+1) A r.val
    have hpk : k≤k^(s+1) := Nat.le_self_pow (by omega) k
    have hr:=r.isLt
    omega
  have hj : j.val.size≤bitBudget k (s+1) A := by
    apply index_size_le_budget k (s+1) A j.val
    have hpow : k^s≤k^(s+1) := Nat.pow_le_pow_right (by omega) (by omega)
    have hj:=j.isLt
    omega
  rw [childProducts_value bitPrimitives bitPrimitives_correct k s hk a b]
  exact interpolation_table_DotCaps k (k^s) N (bitBudget k (s+1) A)
    p hp hv hwidth d j.val hrow hj

theorem interpolation_childProducts_scalar_value (k s : ℕ) (hk : 2≤k)
    (a b : Array ℤ) (d : Fin (2*k-1)) (j : Fin (2*(k^s))) :
    (bitPrimitives.divide (commonDenominator (2*k-1))
      (dotCounted bitPrimitives (integerWeight (2*k-1) d)
        (fun r : Fin (2*k-1)=>readChild (childProducts bitPrimitives k s a b) r.val j.val)
        (List.ofFn (id : Fin (2*k-1)→Fin (2*k-1)))).value).value =
      ((nodePolynomial k s (arrayPolynomial a) (arrayPolynomial b)).coeff d.val).coeff j.val := by
  have he:=interpolate_childProducts_value bitPrimitives bitPrimitives_correct k s hk a b
  have hcell:=congrArg (fun arr : Array (Array ℤ)=>
    (((arr[d.val]?).getD #[])[j.val]?).getD 0) he
  simpa [interpolateCounted,tabulateCounted_value,tabulateInteger_value,Counted.bind,
    Array.getElem?_ofFn,d.isLt,j.isLt] using hcell



theorem actual_interpolate_cost (k s A : ℕ) (hk : 2≤k)
    (a b : Array ℤ) (ha : CoeffBound (arrayPolynomial a) (A:ℤ))
    (hb : CoeffBound (arrayPolynomial b) (A:ℤ)) :
    (interpolateCounted bitPrimitives (2*k-1) (k^s)
      (childProducts bitPrimitives k s a b)).operations ≤
      (2*k-1)*((2*(k^s))*((2*k-1)*
        ((3*bitBudget k (s+1) A+2)+150*(bitBudget k (s+1) A+1)^2)+
          80*(bitBudget k (s+1) A+1)^2+2*bitBudget k (s+1) A+8)+2) := by
  apply interpolateCounted_bit_cost_uniform (2*k-1) (k^s)
    (3*bitBudget k (s+1) A+2) (bitBudget k (s+1) A)
  · unfold bitBudget
    omega
  · exact fun d j=>interpolation_childProducts_DotCaps k s A hk a b ha hb d j
  · unfold bitBudget bitSlope
    nlinarith
  · intro d j
    rw [interpolation_childProducts_scalar_value k s hk a b d j]
    have hz:=nodeCoefficient_bound k s hk (arrayPolynomial a) (arrayPolynomial b) A ha hb d j.val
    have hbits:=register_bits_of_abs_le _ (k^s*(growthConstant k)^3*A^2) hz
    apply hbits.trans
    have hn:=size_powerProduct_bound k (growthConstant k) A s 3 2
    unfold bitBudget bitSlope
    nlinarith
  · intro j
    apply index_size_le_budget k (s+1) A j.val
    have hpow : k^s≤k^(s+1) := Nat.pow_le_pow_right (by omega) (by omega)
    have hj:=j.isLt
    omega

theorem actual_recombination_DotCaps (k s A : ℕ) (hk : 2≤k)
    (a b : Array ℤ)
    (ha : CoeffBound (arrayPolynomial a) (A:ℤ))
    (hb : CoeffBound (arrayPolynomial b) (A:ℤ))
    (j : Fin (2*k*(k^s))) :
    DotCaps (fun _ : Fin (2*k-1) => 1)
      (fun d => shiftedRead bitPrimitives
        (interpolateCounted bitPrimitives (2*k-1) (k^s)
          (childProducts bitPrimitives k s a b)).value d.val (k^s) j.val)
      (List.ofFn (id : Fin (2*k-1) → Fin (2*k-1)))
      (190*(bitBudget k (s+1) A+1)^2) (bitBudget k (s+1) A) := by
  rw [interpolate_childProducts_value bitPrimitives bitPrimitives_correct k s hk a b]
  let p : Fin (2*k-1) → ℤ[X] := fun d =>
    (nodePolynomial k s (arrayPolynomial a) (arrayPolynomial b)).coeff d.val
  let N := k^s*(growthConstant k)^3*A^2
  let W := bitBudget k (s+1) A
  have hp : ∀d, (p d).natDegree<2*(k^s) :=
    fun d => nodeCoefficient_natDegree k s hk _ _ d
  have hv : ∀d, CoeffBound (p d) (N:ℤ) :=
    fun d => nodeCoefficient_bound k s hk _ _ A ha hb d
  have hN : N.size ≤ s*k.size+3*(growthConstant k).size+2*A.size+1 := by
    simpa only [N,Nat.mul_comm] using
      size_powerProduct_bound k (growthConstant k) A s 3 2
  have h2 : (2*k-1).size ≤ k.size+3 := by
    have h := size_powerProduct_bound k 2 1 1 1 0
    simp only [pow_one,pow_zero,mul_one,mul_zero,add_zero,
      show (2:ℕ).size=2 by decide] at h
    apply (Nat.size_le_size (Nat.sub_le (2*k) 1)).trans
    simpa only [Nat.mul_comm] using h
  have hTail : (2*k-1).size+N.size+1 ≤ W := by
    dsimp [W]
    unfold bitBudget bitSlope
    nlinarith
  have hNW : N.size≤W := by omega
  have hlen : 1≤k^s := by
    have := pow_pos (show 0<k by omega) s
    omega
  have hpow : k^(s+1)=k*(k^s) := by rw [pow_succ']
  have hRead (d : Fin (2*k-1)) (t : ℕ) :
      (readChild (Array.ofFn (fun r : Fin (2*k-1) =>
        Array.ofFn (fun z : Fin (2*(k^s)) => (p r).coeff z.val)))
        d.val t).value.natAbs.size≤W := by
    apply (register_bits_of_abs_le _ N
      (read_interpolation_bound k (k^s) p hp d t N hv)).trans hNW
  have hShift (d : Fin (2*k-1)) :
      (shiftedRead bitPrimitives (Array.ofFn (fun r : Fin (2*k-1) =>
        Array.ofFn (fun z : Fin (2*(k^s)) => (p r).coeff z.val)))
        d.val (k^s) j.val).value.natAbs.size≤W := by
    apply (register_bits_of_abs_le _ N
      (shifted_read_bound bitPrimitives bitPrimitives_correct
        k (k^s) p hp d j.val N (by positivity) hv)).trans hNW
  constructor
  · intro d hd
    change (1:ℤ).natAbs.size≤W
    norm_num
    dsimp [W]
    unfold bitBudget
    omega
  · intro d hd
    exact hShift d
  · intro d hd
    have hdv : d.val≤2*k := by omega
    have hjv : j.val≤2*k*(k^s) := by omega
    have hprod : k^s*d.val≤2*k*(k^s) := by nlinarith
    have haddr :
        ((j.val:ℤ)-((k^s*d.val:ℕ):ℤ)).natAbs≤4*k^(s+1) := by
      have h := Int.natAbs_sub_le (j.val:ℤ) ((k^s*d.val:ℕ):ℤ)
      simp only [Int.natAbs_natCast] at h
      rw [hpow]
      nlinarith
    apply shiftedRead_bit_cost _ _ _ _ W
    · exact index_size_le_budget k (s+1) A _ (by rw [hpow];nlinarith)
    · exact index_size_le_budget k (s+1) A _ (by rw [hpow];nlinarith)
    · exact index_size_le_budget k (s+1) A _ (by rw [hpow];nlinarith)
    · exact index_size_le_budget k (s+1) A _ (by rw [hpow];nlinarith)
    · exact index_size_le_budget k (s+1) A _ haddr
    · exact hRead d _
  · intro d hd
    simpa using hShift d
  · intro ys hys
    rw [List.suffix_iff_eq_drop.mp hys]
    exact (shifted_dot_suffix_bits bitPrimitives bitPrimitives_correct
      k (k^s) p hp j.val
      (List.ofFn (id : Fin (2*k-1) → Fin (2*k-1)))
      (List.nodup_ofFn.mpr Function.injective_id) _ N hv).trans hTail

theorem actual_recombine_cost (k s A : ℕ) (hk : 2≤k)
    (a b : Array ℤ)
    (ha : CoeffBound (arrayPolynomial a) (A:ℤ))
    (hb : CoeffBound (arrayPolynomial b) (A:ℤ)) :
    (recombineCounted bitPrimitives k (k^s)
      (interpolateCounted bitPrimitives (2*k-1) (k^s)
        (childProducts bitPrimitives k s a b)).value).operations ≤
      (2*k*(k^s))*((2*k-1)*
        (190*(bitBudget k (s+1) A+1)^2+
          150*(bitBudget k (s+1) A+1)^2)
        +2*bitBudget k (s+1) A+4) := by
  apply recombineCounted_operations_le k (k^s)
    (190*(bitBudget k (s+1) A+1)^2) (bitBudget k (s+1) A) _
  · unfold bitBudget
    omega
  · intro j
    exact actual_recombination_DotCaps k s A hk a b ha hb j
  · intro j
    apply index_size_le_budget k (s+1) A _
    rw [pow_succ']
    have := j.isLt
    nlinarith

#print axioms interpolation_table_DotCaps
#print axioms interpolation_childProducts_DotCaps
#print axioms interpolation_childProducts_scalar_value
#print axioms actual_interpolate_cost
#print axioms actual_recombination_DotCaps
#print axioms actual_recombine_cost

end
end ThinMatrix.ToomBitCost
