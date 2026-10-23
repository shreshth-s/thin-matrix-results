import CWQuantitativeCleanup

set_option autoImplicit false

namespace ThinMatrix.CWFiniteSurvival
open CWBlockWords CWHashFibers CWFilteredHashCounts CWQuantitativeCleanup

theorem cancel_sample_factor (M n T P B K : ℕ) (hM : 0<M) (hn : 0<n)
    (h : T*B*M^n≤M^(n+2)*K+P*B*M^(n-1)) : M*T*B≤M^3*K+P*B := by
  have ha : M^(n+2)=M^(n-1)*M^3 := by rw [show n+2=n-1+3 by omega,pow_add]
  have hb : M^n=M^(n-1)*M := by
    calc
      _ = M^((n-1)+1) := by congr 1;omega
      _ = _ := pow_succ _ _
  rw [ha,hb] at h
  have hh : M^(n-1)*(M*T*B)≤M^(n-1)*(M^3*K+P*B) := by
    convert h using 1 <;> ring
  exact Nat.le_of_mul_le_mul_left hh (pow_pos hM _)

theorem rational_bound (M T P B K : ℕ) (hM : 0<M) (h : M*T*B≤M^3*K+P*B) :
    (T:ℚ)*B/M^2-(P:ℚ)*B/M^3≤K := by
  have hm : (0:ℚ)<M := by exact_mod_cast hM
  have hq : (M:ℚ)*T*B≤(M:ℚ)^3*K+P*B := by exact_mod_cast h
  have he : (T:ℚ)*B/M^2-(P:ℚ)*B/M^3=((M:ℚ)*T*B-P*B)/M^3 := by
    field_simp
  rw [he]
  apply (div_le_iff₀ (pow_pos hm 3)).mpr
  nlinarith

variable (M : ℕ) [Fact (Nat.Prime M)]
/-- Finite quantitative extraction from the actual coordinate filters and cleanup.
The progression-free set is explicit; no size estimate for it is assumed here. -/
theorem exists_survivors_rational (hM : 2<M) (n : ℕ) (hn : 0<n) (reference : Word n)
    (B : Finset (ZMod M)) (hB : ThreeAPFree (B : Set (ZMod M))) :
    ∃ r : Sample (ZMod M) n,
      ((fullClass n reference).card:ℚ)*B.card/M^2-
        ((allCollisions n reference).card:ℚ)*B.card/M^3≤(survivors M n reference B r).card := by
  obtain ⟨r,hr⟩ := exists_survivors M hM n reference B hB
  exact ⟨r,rational_bound M _ _ _ _ (by omega)
    (cancel_sample_factor M n _ _ _ _ (by omega) hn hr)⟩

#print axioms cancel_sample_factor
#print axioms rational_bound
#print axioms exists_survivors_rational
end ThinMatrix.CWFiniteSurvival
