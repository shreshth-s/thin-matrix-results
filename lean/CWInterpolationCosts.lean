import CWInterpolationProgram

set_option autoImplicit false

namespace ThinMatrix.CWInterpolationCosts
open scoped BigOperators
open CWPowerSpecialization CWFiniteKeys CountedCWCoefficients CWInterpolationProgram
open IntegerInterpolationWeights

theorem scalar_sum_work (xs : List Scalar) (W : ℕ) (h : ∀ a ∈ xs,a.2≤W) :
    (sum xs).2≤xs.length*(W+1) := by
  induction xs with
  | nil => simp [sum,lit]
  | cons a xs ih =>
      have ha := h a (by simp)
      have ht := ih (fun b hb => h b (by simp [hb]))
      simp only [sum,add,List.length_cons]
      nlinarith

theorem nat_sum_bound {A : Type*} (xs : List A) (f : A → ℕ) (W : ℕ)
    (h : ∀ a ∈ xs,f a≤W) : (xs.map f).sum≤xs.length*W := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
      have ha := h a (by simp)
      have ht := ih (fun b hb => h b (by simp [hb]))
      simp only [List.map_cons,List.sum_cons,List.length_cons]
      nlinarith

theorem dot_work (side : Fin 3) (n : ℕ) (t : ℤ) (s : TermIndex n) (x : Index n → ℤ) :
    (dot side n t s x).2≤18^n*(25*n+2) := by
  unfold dot
  have h := scalar_sum_work ((axisKeys n).map (fun i => mul (evaluate side t n s i) (lit (x i))))
    (25*n+1) (by
      intro a ha
      obtain ⟨i,_,rfl⟩ := List.mem_map.mp ha
      simp only [mul,lit]
      have := evaluate_work side t n s i
      omega)
  simpa only [List.length_map,axisKeys_length] using h

theorem products_work (n : ℕ) (x y : Index n → ℤ) :
    ((products n x y).map (fun p => p.2.2)).sum ≤
      ((10*n+1)*18^n)*(2*(18^n*(25*n+2))+1) := by
  have h := nat_sum_bound (products n x y) (fun p => p.2.2) (2*(18^n*(25*n+2))+1) (by
    intro p hp
    obtain ⟨s,_,rfl⟩ := List.mem_map.mp hp
    simp only [mul]
    have := dot_work 0 n s.1.val s.2 x
    have := dot_work 1 n s.1.val s.2 y
    omega)
  simpa only [products,List.length_map,requests_length] using h

theorem collect_work (n : ℕ) (table : Table (10*n)) (rows : List (Request n × Scalar)) (k : Index n) :
    (collect n table rows k).2≤rows.length*(25*n+3) := by
  unfold collect
  have h := scalar_sum_work (rows.map (fun p =>
    mul (lit (table.weights.get p.1.1)) (mul (evaluate 2 p.1.1.val n p.1.2 k) (lit p.2.1))))
    (25*n+2) (by
      intro a ha
      obtain ⟨p,_,rfl⟩ := List.mem_map.mp ha
      simp only [mul,lit]
      have := evaluate_work 2 p.1.1.val n p.1.2 k
      omega)
  simpa only [List.length_map] using h

def setupWork (d : ℕ) : ℕ := (d+1)^2*(2*(d+1)+2)+(d+1)*(d+2)+(d+1)
def workBound (n : ℕ) : ℕ := setupWork (10*n)+
  ((10*n+1)*18^n)*(2*(18^n*(25*n+2))+1)+18^n*(((10*n+1)*18^n)*(25*n+3)+1)

theorem execute_work (n : ℕ) (x y : Index n → ℤ) : (execute n x y).operations≤workBound n := by
  simp only [execute,workBound]
  apply Nat.add_le_add
  · exact Nat.add_le_add (prepare_operations (10*n) (order n)) (products_work n x y)
  · simp only [List.map_map,Function.comp_def]
    have h := nat_sum_bound (axisKeys n) (fun k =>
      (collect n (prepare (10*n) (order n)) (products n x y) k).2+1)
      (((10*n+1)*18^n)*(25*n+3)+1) (by
        intro k _
        have h := collect_work n (prepare (10*n) (order n)) (products n x y) k
        simpa only [products,List.length_map,requests_length] using Nat.add_le_add_right h 1)
    simpa only [axisKeys_length] using h

theorem scalar_sum_magnitude (xs : List Scalar) (V : ℕ) (h : ∀ a ∈ xs,a.1.natAbs≤V) :
    (sum xs).1.natAbs≤xs.length*V := by
  induction xs with
  | nil => simp [sum,lit]
  | cons a xs ih =>
      have ha := h a (by simp)
      have ht := ih (fun b hb => h b (by simp [hb]))
      calc
        _ ≤ a.1.natAbs+(sum xs).1.natAbs := Int.natAbs_add_le _ _
        _ ≤ V+xs.length*V := Nat.add_le_add ha ht
        _ = _ := by simp only [List.length_cons];ring

def linearBound (n V : ℕ) : ℕ := 18^n*(CWCoefficientBounds.bound (10*n)^n*V)

theorem dot_magnitude (side : Fin 3) (n : ℕ) (a : Fin (10*n+1)) (s : TermIndex n)
    (x : Index n → ℤ) (V : ℕ) (hx : ∀ i,(x i).natAbs≤V) :
    (dot side n a.val s x).1.natAbs≤linearBound n V := by
  have h := scalar_sum_magnitude
    ((axisKeys n).map (fun i => mul (evaluate side a.val n s i) (lit (x i))))
    (CWCoefficientBounds.bound (10*n)^n*V) (by
      intro z hz
      obtain ⟨i,_,rfl⟩ := List.mem_map.mp hz
      simp only [mul,lit,Int.natAbs_mul,evaluate_value]
      exact Nat.mul_le_mul (CWCoefficientBounds.power_abs (10*n) a.val (by simp;omega) side n s i) (hx i))
  simpa only [dot,linearBound,List.length_map,axisKeys_length] using h

theorem products_magnitude (n V : ℕ) (x y : Index n → ℤ)
    (hx : ∀ i,(x i).natAbs≤V) (hy : ∀ i,(y i).natAbs≤V)
    (p : Request n × Scalar) (hp : p ∈ products n x y) : p.2.1.natAbs≤(linearBound n V)^2 := by
  obtain ⟨s,_,rfl⟩ := List.mem_map.mp hp
  simp only [mul,Int.natAbs_mul,pow_two]
  exact Nat.mul_le_mul (dot_magnitude 0 n s.1 s.2 x V hx) (dot_magnitude 1 n s.1 s.2 y V hy)

def numeratorBound (n V : ℕ) : ℕ := ((10*n+1)*18^n)*
  (coefficientBound (10*n)*(CWCoefficientBounds.bound (10*n)^n*(linearBound n V)^2))

theorem collect_magnitude (n V : ℕ) (x y : Index n → ℤ)
    (hx : ∀ i,(x i).natAbs≤V) (hy : ∀ i,(y i).natAbs≤V) (k : Index n) :
    (collect n (prepare (10*n) (order n)) (products n x y) k).1.natAbs≤numeratorBound n V := by
  have h := scalar_sum_magnitude
    ((products n x y).map (fun p => mul (lit ((prepare (10*n) (order n)).weights.get p.1.1))
      (mul (evaluate 2 p.1.1.val n p.1.2 k) (lit p.2.1))))
    (coefficientBound (10*n)*(CWCoefficientBounds.bound (10*n)^n*(linearBound n V)^2)) (by
      intro z hz
      obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hz
      simp only [mul,lit,Int.natAbs_mul,prepare_weight,evaluate_value]
      exact Nat.mul_le_mul (weight_magnitude (10*n) (order n) p.1.1)
        (Nat.mul_le_mul (CWCoefficientBounds.power_abs (10*n) p.1.1.val (by simp;omega) 2 n p.1.2 k)
          (products_magnitude n V x y hx hy p hp)))
  simpa only [collect,numeratorBound,List.length_map,products,requests_length] using h

#print axioms scalar_sum_work
#print axioms nat_sum_bound
#print axioms dot_work
#print axioms products_work
#print axioms collect_work
#print axioms execute_work
#print axioms scalar_sum_magnitude
#print axioms dot_magnitude
#print axioms products_magnitude
#print axioms collect_magnitude
end ThinMatrix.CWInterpolationCosts
