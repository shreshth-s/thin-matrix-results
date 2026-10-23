import EqualCopyCoefficientGrowth

set_option autoImplicit false

namespace ThinMatrix.FiniteRationalCoefficients
open scoped BigOperators
open FiniteTrilinear EqualCopyCoefficientGrowth

variable {S I J K : Type*} [Fintype S] [Fintype I] [Fintype J] [Fintype K]

abbrev Index (S I J K : Type*) := (S×I) ⊕ ((S×J) ⊕ (S×K))
def value (a : S → Term I J K ℚ) : Index S I J K → ℚ
  | .inl (s,i) => (a s).left i
  | .inr (.inl (s,j)) => (a s).middle j
  | .inr (.inr (s,k)) => (a s).right k

def denominator (a : S → Term I J K ℚ) : ℕ := ∏ i,(value a i).den
def height (a : S → Term I J K ℚ) : ℚ := 1+∑ i,|value a i|

theorem denominator_pos (a : S → Term I J K ℚ) : 0<denominator a :=
  Finset.prod_pos (fun i _ => (value a i).den_pos)

theorem height_pos (a : S → Term I J K ℚ) : 0<height a := by
  unfold height
  positivity

theorem entry_bound (a : S → Term I J K ℚ) (i : Index S I J K) : |value a i|≤height a := by
  classical
  have h := Finset.single_le_sum (fun j (_ : j∈(Finset.univ : Finset (Index S I J K))) =>
    abs_nonneg (value a j)) (Finset.mem_univ i)
  unfold height
  linarith

theorem entry_cleared (a : S → Term I J K ℚ) (i : Index S I J K) :
    ∃ z : ℤ,(denominator a:ℚ)*value a i=z := by
  classical
  have hd : (value a i).den ∣ denominator a :=
    Finset.dvd_prod_of_mem (fun j => (value a j).den) (Finset.mem_univ i)
  obtain ⟨c,hc⟩ := hd
  have he : ((value a i).den:ℚ)*value a i=(value a i).num := by
    have hn := (value a i).num_div_den
    have hp : ((value a i).den:ℚ)≠0 := by exact_mod_cast (value a i).den_ne_zero
    field_simp at hn
    linarith
  refine ⟨(c:ℤ)*(value a i).num,?_⟩
  rw [hc,Nat.cast_mul,Int.cast_mul,Int.cast_natCast]
  calc
    _ = (c:ℚ)*(((value a i).den:ℚ)*value a i) := by ring
    _ = _ := by rw [he]

theorem bounded (a : S → Term I J K ℚ) : Bound a (height a) :=
  ⟨fun s i => entry_bound a (.inl (s,i)),
   fun s j => entry_bound a (.inr (.inl (s,j))),
   fun s k => entry_bound a (.inr (.inr (s,k)))⟩

theorem cleared (a : S → Term I J K ℚ) : Cleared (denominator a) a :=
  ⟨fun s i => entry_cleared a (.inl (s,i)),
   fun s j => entry_cleared a (.inr (.inl (s,j))),
   fun s k => entry_cleared a (.inr (.inr (s,k)))⟩

/-- Every finite rational base, without a supplied denominator or height
premise, has the same fixed constants at all recursion depths. -/
theorem recursive_invariants {r t : ℕ} (ht : 0<t)
    (a : Fin r → Term (Fin t×I) (Fin t×J) (Fin t×K) ℚ) (k : ℕ) :
    Bound (EqualCopyRecursion.terms ht a k) ((r*height a)^k) ∧
    Cleared ((denominator a)^k) (EqualCopyRecursion.terms ht a k) :=
  ⟨terms_bound ht a (height a) (height_pos a).le (bounded a) k,
   terms_cleared ht a (denominator a) (cleared a) k⟩

#print axioms denominator_pos
#print axioms height_pos
#print axioms entry_bound
#print axioms entry_cleared
#print axioms bounded
#print axioms cleared
#print axioms recursive_invariants
end ThinMatrix.FiniteRationalCoefficients
