import IntegerInterpolationWeights

set_option autoImplicit false

/-! Executable shared-denominator coefficient recovery from integer node
values. The node values are inputs here, not assumed free polynomial
execution. Work counts the displayed integer arithmetic and indexed control. -/
namespace ThinMatrix.IntegerCoefficientExtraction
open scoped BigOperators
open Polynomial IntegerInterpolationRows IntegerInterpolationWeights

structure Result where
  numerator : ℤ
  denominator : ℤ
  operations : ℕ
  control : ℕ

def dot : List (ℤ×ℤ) → ℤ×ℕ
  | [] => (0,0)
  | (a,b)::xs => let child := dot xs;(a*b+child.1,child.2+2)

theorem dot_value (xs : List (ℤ×ℤ)) : (dot xs).1=(xs.map (fun p => p.1*p.2)).sum := by
  induction xs with
  | nil => rfl
  | cons p xs ih => cases p;simp [dot,ih]

theorem dot_operations (xs : List (ℤ×ℤ)) : (dot xs).2=2*xs.length := by
  induction xs with
  | nil => rfl
  | cons p xs ih => cases p;simp [dot,ih];omega

def applyTable {d : ℕ} (table : Table d) (values : Vector ℤ (d+1)) : Result :=
  let result := dot (List.ofFn (fun i => (table.weights.get i,values.get i)))
  ⟨result.1,table.denominator,table.operations+result.2,table.control+8*(d+1)+2⟩

def extract (d : ℕ) (k : Fin (d+1)) (values : Vector ℤ (d+1)) : Result :=
  applyTable (prepare d k) values

theorem extract_numerator (d : ℕ) (k : Fin (d+1)) (values : Vector ℤ (d+1)) :
    (extract d k values).numerator=∑ i,weightNumerator d k i*values.get i := by
  simp only [extract,applyTable,dot_value,List.map_ofFn,Function.comp_def,List.sum_ofFn,prepare_weight]

theorem extract_denominator (d : ℕ) (k : Fin (d+1)) (values : Vector ℤ (d+1)) :
    (extract d k values).denominator=commonDen d := prepare_den d k

theorem extract_value (d : ℕ) (k : Fin (d+1)) (p : ℤ[X]) (hp : p.natDegree≤d)
    (values : Vector ℤ (d+1)) (hv : ∀ i,values.get i=p.eval (i.val:ℤ)) :
    ((extract d k values).numerator:ℚ)/(extract d k values).denominator=(p.coeff k.val:ℚ) := by
  rw [extract_numerator,extract_denominator,Int.cast_sum,Finset.sum_div]
  have h := RationalInterpolation.coefficient d k.val (p.map (Int.castRingHom ℚ))
    ((natDegree_map_le).trans hp)
  rw [coeff_map] at h
  convert h.symm using 1
  · apply Finset.sum_congr rfl
    intro i _
    rw [Int.cast_mul,← div_mul_eq_mul_div,weight_value,hv]
    simp [eval_map,RationalInterpolation.node]
  · rfl

theorem extract_exact (d : ℕ) (k : Fin (d+1)) (p : ℤ[X]) (hp : p.natDegree≤d)
    (values : Vector ℤ (d+1)) (hv : ∀ i,values.get i=p.eval (i.val:ℤ)) :
    (extract d k values).numerator=(extract d k values).denominator*p.coeff k.val := by
  have hd : (extract d k values).denominator≠0 := by
    rw [extract_denominator];exact commonDen_ne_zero d
  have h := extract_value d k p hp values hv
  have hdq : ((extract d k values).denominator:ℚ)≠0 := by exact_mod_cast hd
  have hh := (div_eq_iff hdq).mp h
  exact_mod_cast (hh.trans (mul_comm _ _))

theorem extract_operations (d : ℕ) (k : Fin (d+1)) (values : Vector ℤ (d+1)) :
    (extract d k values).operations ≤
      (d+1)^2*(2*(d+1)+2)+(d+1)*(d+2)+3*(d+1) := by
  simp only [extract,applyTable,dot_operations,List.length_ofFn]
  have := prepare_operations d k
  omega

theorem dot_magnitude (xs : List (ℤ×ℤ)) (H V : ℕ)
    (h : ∀ p ∈ xs,p.1.natAbs≤H ∧ p.2.natAbs≤V) :
    (dot xs).1.natAbs≤xs.length*(H*V) := by
  induction xs with
  | nil => simp [dot]
  | cons p xs ih =>
      have hh := h p (by simp)
      have ht := ih (fun q hq => h q (by simp [hq]))
      calc
        _ ≤ (p.1*p.2).natAbs+(dot xs).1.natAbs := by cases p;exact Int.natAbs_add_le _ _
        _ ≤ H*V+xs.length*(H*V) := Nat.add_le_add (by
          rw [Int.natAbs_mul];exact Nat.mul_le_mul hh.1 hh.2) ht
        _ = _ := by simp only [List.length_cons];ring

theorem extract_magnitude (d : ℕ) (k : Fin (d+1)) (values : Vector ℤ (d+1)) (V : ℕ)
    (hv : ∀ i,(values.get i).natAbs≤V) :
    (extract d k values).numerator.natAbs≤(d+1)*(coefficientBound d*V) := by
  simpa only [extract,applyTable,List.length_ofFn] using
    dot_magnitude (List.ofFn (fun i => ((prepare d k).weights.get i,values.get i)))
      (coefficientBound d) V (by
        intro p hp
        obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hp
        exact ⟨by rw [prepare_weight];exact weight_magnitude d k i,hv i⟩)

theorem extract_zero (v : Vector ℤ 1) :
    (extract 0 0 v).numerator=v.get 0 ∧ (extract 0 0 v).denominator=1 := by
  simp [extract_numerator,extract_denominator,weightNumerator,commonDen,row,build,delta]

#print axioms dot_value
#print axioms dot_operations
#print axioms extract_numerator
#print axioms extract_denominator
#print axioms extract_value
#print axioms extract_exact
#print axioms extract_operations
#print axioms dot_magnitude
#print axioms extract_magnitude
#print axioms extract_zero
end ThinMatrix.IntegerCoefficientExtraction
