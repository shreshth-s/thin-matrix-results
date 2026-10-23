import CountedCWCoefficients

set_option autoImplicit false

namespace ThinMatrix.CWCoefficientBounds
open scoped BigOperators
open FiniteTrilinear CWPolynomialCertificate PolynomialDegeneration CWPowerSpecialization CountedCWCoefficients

def bound (d : ℕ) : ℕ := 20+(1+16*d)*(1+d^3)+d*(1+d)+(1+16*d^2)

theorem basis_abs (a i : Axis 16) : (basis a i:ℤ).natAbs≤1 := by
  unfold basis
  split_ifs <;> simp

theorem sum_abs (f : Fin 16 → ℤ) (h : ∀ a,(f a).natAbs≤1) : (∑ a,f a).natAbs≤16 := by
  calc
    _ ≤ ∑ a,(f a).natAbs := Int.natAbs_sum_le _ _
    _ ≤ ∑ _ : Fin 16,1 := Finset.sum_le_sum (fun a _ => h a)
    _ = _ := by simp

theorem private_abs (d : ℕ) (t : ℤ) (ht : t.natAbs≤d) (a : Fin 16) (i : Axis 16) :
    (privateAt a t i).natAbs≤1+d := by
  calc
    _ ≤ (basis origin i:ℤ).natAbs+(t*basis (privateLabel a) i).natAbs := Int.natAbs_add_le _ _
    _ ≤ 1+d*1 := Nat.add_le_add (basis_abs _ _) (by
      rw [Int.natAbs_mul];exact Nat.mul_le_mul ht (basis_abs _ _))
    _ = _ := by omega

theorem sumAt_abs (d : ℕ) (t : ℤ) (ht : t.natAbs≤d) (i : Axis 16) :
    (sumAt t i).natAbs≤1+16*d^2 := by
  calc
    _ ≤ (basis origin i:ℤ).natAbs+(t^2*(∑ a : Fin 16,basis (privateLabel a) i)).natAbs := Int.natAbs_add_le _ _
    _ ≤ 1+d^2*16 := Nat.add_le_add (basis_abs _ _) (by
      rw [Int.natAbs_mul,Int.natAbs_pow]
      exact Nat.mul_le_mul (Nat.pow_le_pow_left ht _) (sum_abs _ (fun a => basis_abs _ _)))
    _ = _ := by ring

theorem terminal_abs (d : ℕ) (t : ℤ) (ht : t.natAbs≤d) (i : Axis 16) :
    (terminalAt t i).natAbs≤1+d^3 := by
  calc
    _ ≤ (basis origin i:ℤ).natAbs+(t^3*basis terminal i).natAbs := Int.natAbs_add_le _ _
    _ ≤ 1+d^3*1 := Nat.add_le_add (basis_abs _ _) (by
      rw [Int.natAbs_mul,Int.natAbs_pow]
      exact Nat.mul_le_mul (Nat.pow_le_pow_left ht _) (basis_abs _ _))
    _ = _ := by omega

theorem base_abs (d : ℕ) (t : ℤ) (ht : t.natAbs≤d) (s : Fin 18) (side : Fin 3) (i : Axis 16) :
    (component (termsAt 16 t s) side i).natAbs≤bound d := by
  have hp := private_abs d t ht
  have hs := sumAt_abs d t ht i
  have hz := terminal_abs d t ht i
  have hm : ((1:ℤ)-16*t).natAbs≤1+16*d := by
    calc
      _ ≤ (1:ℤ).natAbs+(16*t).natAbs := Int.natAbs_sub_le _ _
      _ ≤ 1+16*d := by simp only [Int.natAbs_one,Int.natAbs_mul];norm_num;omega
  have hpriv (a : Fin 16) : (t*privateAt a t i).natAbs≤d*(1+d) := by
    rw [Int.natAbs_mul];exact Nat.mul_le_mul ht (hp a i)
  have hterm : (((1:ℤ)-16*t)*terminalAt t i).natAbs≤(1+16*d)*(1+d^3) := by
    rw [Int.natAbs_mul];exact Nat.mul_le_mul hm hz
  have hall : ((termsAt 16 t s).left i).natAbs≤bound d ∧
      ((termsAt 16 t s).middle i).natAbs≤bound d ∧ ((termsAt 16 t s).right i).natAbs≤bound d := by
    refine Fin.addCases (m:=16) (n:=2) (motive:=fun s =>
      ((termsAt 16 t s).left i).natAbs≤bound d ∧ ((termsAt 16 t s).middle i).natAbs≤bound d ∧
        ((termsAt 16 t s).right i).natAbs≤bound d) (fun a => ?_) (fun a => ?_) s
    · simp only [termsAt,Fin.addCases_left,mainAt]
      exact ⟨(hpriv a).trans (by unfold bound;omega),
        (hp a i).trans (by unfold bound;nlinarith),(hp a i).trans (by unfold bound;nlinarith)⟩
    · simp only [termsAt,Fin.addCases_right]
      refine Fin.cases ?_ (fun b => ?_) a
      · simp only [Fin.cons_zero,negativeAt,Int.natAbs_neg]
        exact ⟨hs.trans (by unfold bound;omega),hs.trans (by unfold bound;omega),hs.trans (by unfold bound;omega)⟩
      · have hb : b=0 := Fin.eq_zero b
        subst b
        simp only [Fin.cons_succ,Fin.cons_zero,terminalTermAt,Nat.cast_ofNat]
        exact ⟨hterm.trans (by unfold bound;omega),hz.trans (by unfold bound;nlinarith),hz.trans (by unfold bound;nlinarith)⟩
  unfold component
  split_ifs
  · exact hall.1
  · exact hall.2.1
  · exact hall.2.2

theorem power_abs (d : ℕ) (t : ℤ) (ht : t.natAbs≤d) (side : Fin 3) (n : ℕ)
    (s : TermIndex n) (i : Index n) :
    (component (atInteger n t s) side i).natAbs≤bound d^n := by
  induction n with
  | zero => fin_cases side <;> simp [component,atInteger,powerTerms]
  | succ n ih =>
      have hh := base_abs d t ht s.1 side i.1
      have ht' := ih s.2 i.2
      have he : component (atInteger (n+1) t s) side i=
          component (termsAt 16 t s.1) side i.1*component (atInteger n t s.2) side i.2 := by
        fin_cases side <;> rfl
      rw [he,Int.natAbs_mul,pow_succ']
      exact Nat.mul_le_mul hh ht'

#print axioms basis_abs
#print axioms sum_abs
#print axioms private_abs
#print axioms sumAt_abs
#print axioms terminal_abs
#print axioms base_abs
#print axioms power_abs
end ThinMatrix.CWCoefficientBounds
