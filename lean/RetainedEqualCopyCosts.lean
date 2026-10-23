import RetainedEqualCopy

set_option autoImplicit false

namespace ThinMatrix.RetainedEqualCopyCosts
open scoped BigOperators
open RecursiveTable RecursiveBilinearStep RetainedEqualCopy
variable {I J K R : Type} [CommRing R] [Fintype I] [Fintype J] [Fintype K] {r t : ℕ}

def arithmetic (r t i j o : ℕ) : ℕ → ℕ
  | 0 => t
  | k+1 => ((r+t-1)/t)*arithmetic r t i j o k + 2*r*t*(i^(k+1)+j^(k+1)+o^(k+1))

def control (r t i j o : ℕ) : ℕ → ℕ
  | 0 => 40*t+8
  | k+1 => ((r+t-1)/t)*control r t i j o k +
      r*i^k*(20*t*i+36)+r*j^k*(20*t*j+36)+
      ((r+t-1)/t)*(40*t*(i^k+j^k)+56)+t*o^(k+1)*(20*r+36)+48

theorem padded_arithmetic {A : Type} [Fintype A] (a : Layout A) (g : ℕ)
    (x : Table (prod (fin r) a) R) : (padded (t:=t) a g x).arithmetic=0 := by
  rw [padded,tabulate_arithmetic]
  apply Finset.sum_eq_zero;intro i _
  split_ifs <;> rfl

theorem padded_control {A : Type} [Fintype A] (a : Layout A) (g : ℕ)
    (x : Table (prod (fin r) a) R) : (padded (t:=t) a g x).control=40*t*a.size+8 := by
  rw [padded,tabulate_control]
  have hv (i : Fin t×A) :
      (if h : g*t+i.1.val<r then (⟨read x (⟨g*t+i.1.val,h⟩,i.2),0,8⟩ : Run R)
        else ⟨0,0,8⟩).control=8 := by split_ifs <;> rfl
  simp only [hv,Finset.sum_const,Finset.card_univ,Fintype.card_prod,Fintype.card_fin,smul_eq_mul]
  rw [← size_eq_card a]
  simp only [prod,fin]
  ring

omit [Fintype I] in
theorem forms_arithmetic {A : Type} [Fintype A] (a : Layout I) (tail : Layout A)
    (coeff : Table (prod (fin r) (prod (fin t) a)) R) (x : Fin t×(I×A) → R) :
    (forms a tail coeff x).arithmetic=2*r*t*a.size*tail.size := by
  rw [forms,tabulate_arithmetic]
  simp only [dot_arithmetic,Finset.sum_const,Finset.card_univ,Fintype.card_prod,Fintype.card_fin,smul_eq_mul]
  rw [← size_eq_card tail]
  simp only [prod,fin]
  ring

omit [Fintype I] in
theorem forms_control {A : Type} [Fintype A] (a : Layout I) (tail : Layout A)
    (coeff : Table (prod (fin r) (prod (fin t) a)) R) (x : Fin t×(I×A) → R) :
    (forms a tail coeff x).control=r*tail.size*(20*t*a.size+36)+8 := by
  rw [forms,tabulate_control]
  simp only [dot_control,Finset.sum_const,Finset.card_univ,Fintype.card_prod,Fintype.card_fin,smul_eq_mul]
  rw [← size_eq_card tail]
  simp only [prod,fin]
  ring

theorem run_arithmetic (a : Layout I) (b : Layout J) (c : Layout K) (ht : 0<t)
    (d : Base r t a b c R) (k : ℕ)
    (x : Table (copies t a k) R) (y : Table (copies t b k) R) :
    (run a b c ht d k x y).arithmetic=arithmetic r t a.size b.size c.size k := by
  induction k with
  | zero => simp [run,tabulate_arithmetic,arithmetic,PolynomialDegeneration.PowerIndex]
  | succ k ih =>
    simp only [run,tabulate_arithmetic,forms_arithmetic,padded_arithmetic,zero_add,ih,dot_arithmetic,
      Finset.sum_const,Finset.card_univ,Fintype.card_fin,Fintype.card_prod,
      PolynomialDegeneration.powerIndex_card,smul_eq_mul,power_size,fin]
    rw [← size_eq_card c]
    simp only [arithmetic,pow_succ']
    ring

theorem run_control (a : Layout I) (b : Layout J) (c : Layout K) (ht : 0<t)
    (d : Base r t a b c R) (k : ℕ)
    (x : Table (copies t a k) R) (y : Table (copies t b k) R) :
    (run a b c ht d k x y).control=control r t a.size b.size c.size k := by
  induction k with
  | zero => simp [run,tabulate_control,control,copies,power,unit,prod,fin,
      PolynomialDegeneration.PowerIndex];ring
  | succ k ih =>
    simp only [run,tabulate_control,forms_control,padded_control,ih,dot_control,
      Finset.sum_const,Finset.card_univ,Fintype.card_fin,Fintype.card_prod,
      PolynomialDegeneration.powerIndex_card,smul_eq_mul,power_size,fin]
    rw [← size_eq_card c]
    simp only [copies,prod,fin,power_size,control]
    ring

/-- A general recurrence bound. It includes all additions, formation,
padding, copies and indexed-control terms already charged by the program. -/
theorem recurrence_bound (f : ℕ → ℕ) (g M C : ℕ) (hM : 1≤M) (hg : g≤M)
    (h0 : f 0≤C) (hs : ∀ k,f (k+1)≤g*f k+C*M^k) (k : ℕ) :
    f k≤C*(k+1)*M^k := by
  induction k with
  | zero => simpa using h0
  | succ k ih =>
    calc
      _ ≤ g*(C*(k+1)*M^k)+C*M^k := (hs k).trans (Nat.add_le_add_right (Nat.mul_le_mul_left g ih) _)
      _ ≤ M*(C*(k+1)*M^k)+C*M^k*M := by
        exact Nat.add_le_add (Nat.mul_le_mul_right _ hg) (Nat.le_mul_of_pos_right _ hM)
      _ = _ := by rw [pow_succ];ring

def levelConstant (r t i j o : ℕ) : ℕ :=
  2*r*t*(i+j+o) + r*(20*t*i+36)+r*(20*t*j+36)+
    ((r+t-1)/t)*(80*t+56)+t*o*(20*r+36)+48+41*t+8

theorem run_work_bound (a : Layout I) (b : Layout J) (c : Layout K) (ht : 0<t)
    (d : Base r t a b c R) (M : ℕ) (hM : 1≤M) (hg : (r+t-1)/t≤M)
    (hi : a.size≤M) (hj : b.size≤M) (ho : c.size≤M) (k : ℕ)
    (x : Table (copies t a k) R) (y : Table (copies t b k) R) :
    (run a b c ht d k x y).arithmetic+(run a b c ht d k x y).control≤
      levelConstant r t a.size b.size c.size*(k+1)*M^k := by
  rw [run_arithmetic,run_control]
  apply recurrence_bound (fun k => arithmetic r t a.size b.size c.size k+
    control r t a.size b.size c.size k) ((r+t-1)/t) M _ hM hg
  · simp only [arithmetic,control,levelConstant]
    omega
  · intro l
    have hpi : a.size^l≤M^l := Nat.pow_le_pow_left hi l
    have hpj : b.size^l≤M^l := Nat.pow_le_pow_left hj l
    have hpo : c.size^l≤M^l := Nat.pow_le_pow_left ho l
    have hp1 : 1≤M^l := one_le_pow₀ hM
    simp only [arithmetic,control,levelConstant,pow_succ']
    nlinarith [Nat.mul_le_mul_left (2*r*t*a.size+r*(20*t*a.size+36)+((r+t-1)/t)*40*t) hpi,
      Nat.mul_le_mul_left (2*r*t*b.size+r*(20*t*b.size+36)+((r+t-1)/t)*40*t) hpj,
      Nat.mul_le_mul_left (2*r*t*c.size+t*c.size*(20*r+36)) hpo,
      Nat.mul_le_mul_left (((r+t-1)/t)*56+48+41*t+8) hp1]

#print axioms padded_arithmetic
#print axioms padded_control
#print axioms forms_arithmetic
#print axioms forms_control
#print axioms run_arithmetic
#print axioms run_control
#print axioms recurrence_bound
#print axioms run_work_bound
end ThinMatrix.RetainedEqualCopyCosts
