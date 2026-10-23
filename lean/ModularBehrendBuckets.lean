import ModularAPEmbedding

set_option autoImplicit false
namespace ThinMatrix.ModularBehrendBuckets
open ModularAPEmbedding FiniteAPSearch

/-- Deterministic exhaustive reference bucket construction. No efficient
search-cost assertion is made. -/
def buckets (M : ℕ) : Finset (ZMod M) := embed M (chosen (M/2))

theorem buckets_card (M : ℕ) : (buckets M).card=rothNumberNat (M/2) := by
  rw [buckets,embed_card M (M/2) (Nat.div_le_self M 2) _ (chosen_subset _),chosen_card]

theorem buckets_free (M : ℕ) : ThreeAPFree (buckets M : Set (ZMod M)) :=
  embed_free M (M/2) (by omega) _ (chosen_subset _) (chosen_free _)

theorem half_ge_third (M : ℕ) (hM : 2<M) : (M:ℝ)/3≤(M/2:ℕ) := by
  have h : M≤3*(M/2) := by omega
  have hr : (M:ℝ)≤3*(M/2:ℕ) := by exact_mod_cast h
  linarith

theorem buckets_bound (M : ℕ) (hM : 2<M) :
    (M:ℝ)/3*Real.exp (-4*Real.sqrt (Real.log M))≤(buckets M).card := by
  have hN : (0:ℝ)<(M/2:ℕ) := by exact_mod_cast (show 0<M/2 by omega)
  have hNM : ((M/2:ℕ):ℝ)≤M := by exact_mod_cast Nat.div_le_self M 2
  have hl := Real.log_le_log hN hNM
  have hs := Real.sqrt_le_sqrt hl
  have he : Real.exp (-4*Real.sqrt (Real.log M))≤Real.exp (-4*Real.sqrt (Real.log (M/2:ℕ))) :=
    Real.exp_le_exp.mpr (by nlinarith)
  calc
    _ ≤ (M/2:ℕ)*Real.exp (-4*Real.sqrt (Real.log (M/2:ℕ))) :=
      mul_le_mul (half_ge_third M hM) he (le_of_lt (Real.exp_pos _)) (Nat.cast_nonneg _)
    _ ≤ (chosen (M/2)).card := chosen_bound _
    _ = _ := by rw [buckets_card,chosen_card]

theorem buckets_density (M : ℕ) (hM : 2<M) :
    (1/3:ℝ)*Real.exp (-4*Real.sqrt (Real.log M))≤(buckets M).card/(M:ℝ) := by
  have hm : (0:ℝ)<M := by exact_mod_cast (show 0<M by omega)
  apply (le_div_iff₀ hm).mpr
  calc
    _ = (M:ℝ)/3*Real.exp (-4*Real.sqrt (Real.log M)) := by ring
    _ ≤ _ := buckets_bound M hM

theorem small_moduli : buckets 0=∅ ∧ buckets 1=∅ ∧ buckets 2={0} := by decide

#print axioms buckets_card
#print axioms buckets_free
#print axioms half_ge_third
#print axioms buckets_bound
#print axioms buckets_density
#print axioms small_moduli
end ThinMatrix.ModularBehrendBuckets
