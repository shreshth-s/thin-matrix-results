import EqualCopyRecursion

set_option autoImplicit false

/-! The recursive coefficient paths have exponential magnitude and a common
denominator d^k, hence linear-in-depth bit growth. These are coefficient
invariants, not a substitute for pricing a retained recursive evaluator. -/
namespace ThinMatrix.EqualCopyCoefficientGrowth
open scoped BigOperators
open FiniteTrilinear FiniteDirectSum FiniteBilinearSubstitution EqualCopyRecursion

variable {S H I J K A B C : Type*}

def Bound (a : S → Term I J K ℚ) (M : ℚ) : Prop :=
  (∀ s i, |(a s).left i|≤M) ∧ (∀ s j, |(a s).middle j|≤M) ∧ (∀ s k, |(a s).right k|≤M)

def Cleared (d : ℕ) (a : S → Term I J K ℚ) : Prop :=
  (∀ s i, ∃ z : ℤ,(d:ℚ)*(a s).left i=z) ∧
  (∀ s j, ∃ z : ℤ,(d:ℚ)*(a s).middle j=z) ∧
  (∀ s k, ∃ z : ℤ,(d:ℚ)*(a s).right k=z)

theorem sum_bound [Fintype S] (f g : S → ℚ) (M N : ℚ) (hM : 0≤M) (_hN : 0≤N)
    (hf : ∀ s, |f s|≤M) (hg : ∀ s, |g s|≤N) :
    |∑ s,f s*g s|≤Fintype.card S*M*N := by
  calc
    _ ≤ ∑ s,|f s*g s| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _s : S,M*N := Finset.sum_le_sum (fun s _ => by
      rw [abs_mul];exact mul_le_mul (hf s) (hg s) (abs_nonneg _) hM)
    _ = _ := by simp [mul_assoc]

theorem sum_cleared [Fintype S] (f g : S → ℚ) (d e : ℕ)
    (hf : ∀ s, ∃ z : ℤ,(d:ℚ)*f s=z) (hg : ∀ s, ∃ z : ℤ,(e:ℚ)*g s=z) :
    ∃ z : ℤ,((d*e:ℕ):ℚ)*(∑ s,f s*g s)=z := by
  classical
  choose u hu using hf
  choose v hv using hg
  refine ⟨∑ s,u s*v s,?_⟩
  simp only [Nat.cast_mul,Finset.mul_sum,Int.cast_sum,Int.cast_mul]
  apply Finset.sum_congr rfl
  intro s _
  rw [←hu s,←hv s]
  ring

theorem batch_bound {T G : Type*} [DecidableEq G]
    (e : S → G×T) (a : H → Term (T×I) (T×J) (T×K) ℚ) (M : ℚ)
    (hM : 0≤M) (ha : Bound a M) : Bound (batchTerm e a) M := by
  refine ⟨?_,?_,?_⟩ <;> intro gh x <;> dsimp [batchTerm]
  · split_ifs; exact ha.1 _ _; simpa using hM
  · split_ifs; exact ha.2.1 _ _; simpa using hM
  · split_ifs; exact ha.2.2 _ _; simpa using hM

theorem batch_cleared {T G : Type*} [DecidableEq G]
    (e : S → G×T) (a : H → Term (T×I) (T×J) (T×K) ℚ) (d : ℕ)
    (ha : Cleared d a) : Cleared d (batchTerm e a) := by
  refine ⟨?_,?_,?_⟩ <;> intro gh x <;> dsimp [batchTerm]
  · split_ifs; exact ha.1 _ _; exact ⟨0,by simp⟩
  · split_ifs; exact ha.2.1 _ _; exact ⟨0,by simp⟩
  · split_ifs; exact ha.2.2 _ _; exact ⟨0,by simp⟩

theorem substitute_bound [Fintype S] [DecidableEq S]
    (a : S → Term I J K ℚ) (b : H → Term (S×A) (S×B) (S×C) ℚ)
    (M N : ℚ) (hM : 0≤M) (hN : 0≤N) (ha : Bound a M) (hb : Bound b N) :
    Bound (substitute a b) (Fintype.card S*M*N) := by
  exact ⟨fun h x => sum_bound _ _ M N hM hN (fun s => ha.1 s _) (fun s => hb.1 h _),
    fun h y => sum_bound _ _ M N hM hN (fun s => ha.2.1 s _) (fun s => hb.2.1 h _),
    fun h z => sum_bound _ _ M N hM hN (fun s => ha.2.2 s _) (fun s => hb.2.2 h _)⟩

theorem substitute_cleared [Fintype S] [DecidableEq S]
    (a : S → Term I J K ℚ) (b : H → Term (S×A) (S×B) (S×C) ℚ)
    (d e : ℕ) (ha : Cleared d a) (hb : Cleared e b) :
    Cleared (d*e) (substitute a b) := by
  exact ⟨fun h x => sum_cleared _ _ d e (fun s => ha.1 s _) (fun s => hb.1 h _),
    fun h y => sum_cleared _ _ d e (fun s => ha.2.1 s _) (fun s => hb.2.1 h _),
    fun h z => sum_cleared _ _ d e (fun s => ha.2.2 s _) (fun s => hb.2.2 h _)⟩

theorem terms_bound {r t : ℕ} (ht : 0<t)
    (a : Fin r → Term (Fin t×I) (Fin t×J) (Fin t×K) ℚ)
    (M : ℚ) (hM : 0≤M) (ha : Bound a M) (k : ℕ) :
    Bound (terms ht a k) ((r*M)^k) := by
  induction k with
  | zero =>
    refine ⟨?_,?_,?_⟩ <;> intro h x <;> change Fin t at h <;>
      change |(if h=x.1 then (1:ℚ) else 0)|≤_ <;>
      split_ifs <;> norm_num
  | succ k ih =>
    have hb := batch_bound (slot r t ht) (terms ht a k) ((r*M)^k) (by positivity) ih
    have hh := substitute_bound a _ M ((r*M)^k) hM (by positivity) ha hb
    simp only [Fintype.card_fin,←pow_succ'] at hh
    exact ⟨fun j x => hh.1 j (unnest x),fun j y => hh.2.1 j (unnest y),
      fun j z => hh.2.2 j (unnest z)⟩

theorem terms_cleared {r t : ℕ} (ht : 0<t)
    (a : Fin r → Term (Fin t×I) (Fin t×J) (Fin t×K) ℚ)
    (d : ℕ) (ha : Cleared d a) (k : ℕ) : Cleared (d^k) (terms ht a k) := by
  induction k with
  | zero =>
    refine ⟨?_,?_,?_⟩ <;> intro h x <;> change Fin t at h <;>
      change ∃ z : ℤ,((d^0:ℕ):ℚ)*(if h=x.1 then 1 else 0)=z
    all_goals
      refine ⟨if h=x.1 then 1 else 0,?_⟩
      split_ifs <;> norm_num
  | succ k ih =>
    have hb := batch_cleared (slot r t ht) (terms ht a k) (d^k) ih
    have hh := substitute_cleared a _ d (d^k) ha hb
    rw [←pow_succ'] at hh
    exact ⟨fun j x => hh.1 j (unnest x),fun j y => hh.2.1 j (unnest y),
      fun j z => hh.2.2 j (unnest z)⟩

#print axioms sum_bound
#print axioms sum_cleared
#print axioms batch_bound
#print axioms batch_cleared
#print axioms substitute_bound
#print axioms substitute_cleared
#print axioms terms_bound
#print axioms terms_cleared
end ThinMatrix.EqualCopyCoefficientGrowth
