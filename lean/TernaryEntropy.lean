import EntropyBounds
import Mathlib

set_option autoImplicit false
namespace ThinMatrix.TernaryEntropy
open scoped BigOperators

/-- Natural-log entropy written as a binary chain. Defined also at zero counts. -/
noncomputable def entropy (a b c : ℝ) : ℝ :=
  Real.binEntropy (a/(a+b+c))+(b+c)/(a+b+c)*Real.binEntropy (b/(b+c))

def coefficient (a b c : ℕ) : ℕ := Nat.multinomial Finset.univ ![a,b,c]

theorem coefficient_eq (a b c : ℕ) :
    coefficient a b c=(a+b+c).choose a*(b+c).choose b := by
  have hu : (Finset.univ : Finset (Fin 3))={0,1,2} := by decide
  unfold coefficient
  rw [hu,Nat.multinomial_insert (by decide),Nat.multinomial_insert (by decide)]
  simp [add_assoc]

theorem weighted_chain (a b c : ℕ) :
    ((a+b+c:ℕ):ℝ)*entropy a b c=
      ((a+b+c:ℕ):ℝ)*Real.binEntropy ((a:ℝ)/(a+b+c:ℕ))+
      ((b+c:ℕ):ℝ)*Real.binEntropy ((b:ℝ)/(b+c:ℕ)) := by
  by_cases h : a+b+c=0
  · have ha : a=0 := by omega
    have hb : b=0 := by omega
    have hc : c=0 := by omega
    simp [ha,hb,hc]
  · have hr : (a:ℝ)+b+c≠0 := by exact_mod_cast h
    push_cast
    unfold entropy
    field_simp

/-- Both finite bounds include zero counts and total length zero. -/
theorem coefficient_bounds (a b c : ℕ) :
    Real.exp (((a+b+c:ℕ):ℝ)*entropy a b c)/((a+b+c:ℕ)+1)^2≤coefficient a b c ∧
    (coefficient a b c:ℝ)≤Real.exp (((a+b+c:ℕ):ℝ)*entropy a b c) := by
  have h1 := EntropyBounds.choose_entropy_lower_of_le (a+b+c) a (by omega)
  have h2 := EntropyBounds.choose_entropy_lower_of_le (b+c) b (by omega)
  have u1 := EntropyBounds.choose_entropy_upper_of_le (a+b+c) a (by omega)
  have u2 := EntropyBounds.choose_entropy_upper_of_le (b+c) b (by omega)
  rw [weighted_chain,Real.exp_add,coefficient_eq,Nat.cast_mul]
  constructor
  · calc
      _ ≤ Real.exp (((a+b+c:ℕ):ℝ)*Real.binEntropy ((a:ℝ)/(a+b+c:ℕ)))/((a+b+c:ℕ)+1)*
          (Real.exp (((b+c:ℕ):ℝ)*Real.binEntropy ((b:ℝ)/(b+c:ℕ)))/((b+c:ℕ)+1)) := by
        rw [div_mul_div_comm]
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        have h : ((b+c:ℕ):ℝ)+1≤(a+b+c:ℕ)+1 := by exact_mod_cast (show b+c+1≤a+b+c+1 by omega)
        nlinarith [show (0:ℝ)≤(a+b+c:ℕ)+1 by positivity]
      _ ≤ _ := mul_le_mul h1 h2 (by positivity) (by positivity)
  · exact mul_le_mul u1 u2 (by positivity) (by positivity)

theorem entropy_scale (a b c s : ℝ) (hs : s≠0) :
    entropy (s*a) (s*b) (s*c)=entropy a b c := by
  have h1 : s*a+s*b+s*c=s*(a+b+c) := by ring
  have h2 : s*b+s*c=s*(b+c) := by ring
  simp only [entropy,h1,h2,mul_div_mul_left _ _ hs]

/-- Identification with Shannon entropy, for the positive target coordinates. -/
theorem entropy_shannon (a b c : ℝ) (ha : 0<a) (hb : 0<b) (hc : 0<c) :
    entropy a b c= -(a/(a+b+c))*Real.log (a/(a+b+c))-
      (b/(a+b+c))*Real.log (b/(a+b+c))-(c/(a+b+c))*Real.log (c/(a+b+c)) := by
  have ht : a+b+c≠0 := by positivity
  have hu : b+c≠0 := by positivity
  have h1 : 1-a/(a+b+c)=(b+c)/(a+b+c) := by field_simp;ring
  have h2 : 1-b/(b+c)=c/(b+c) := by field_simp;ring
  simp only [entropy,EntropyBounds.binEntropy_eq,h1,h2]
  rw [Real.log_div ha.ne' ht,Real.log_div hu ht,Real.log_div hb.ne' hu,
    Real.log_div hc.ne' hu,Real.log_div hb.ne' ht,Real.log_div hc.ne' ht]
  field_simp
  ring

theorem entropy_pos (a b c : ℝ) (ha : 0<a) (hb : 0<b) (hc : 0<c) :
    0<entropy a b c := by
  have ht : 0<a+b+c := by positivity
  have hu : 0<b+c := by positivity
  apply add_pos_of_pos_of_nonneg
  · exact Real.binEntropy_pos (div_pos ha ht) ((div_lt_one ht).mpr (by linarith))
  · exact mul_nonneg (by positivity) (Real.binEntropy_nonneg (by positivity)
      ((div_le_one hu).mpr (by linarith)))

#print axioms entropy_pos
#print axioms coefficient_eq
#print axioms weighted_chain
#print axioms coefficient_bounds
#print axioms entropy_scale
#print axioms entropy_shannon
end ThinMatrix.TernaryEntropy
