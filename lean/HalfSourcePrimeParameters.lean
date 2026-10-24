import HalfSourceBatchGeometry
import CompleteAPSP

/-! Actual prime-parameter generation at the exact-half rational witness.
Every returned configuration satisfies the composite-incidence hypotheses;
the same decidable program succeeds uniformly for polynomially bounded
adaptive APSP magnitudes. This does not assert a fast backend runtime. -/
namespace ThinMatrix.HalfSourcePrimeParameters
open Filter
open HalfSourceBatchFit
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

def computedPool (n : ℕ) : Finset ℕ :=
  PrimePool.enumeratedCandidates (scale n) \ {3}

def reserve (n : ℕ) : ℕ := (computedPool n).card-R

theorem computedPool_eq (n : ℕ) :
    computedPool n = CertificationParameters.pool (scale n) := rfl

/-- The decidable finite conditions are checked by the same total
parameter program for every input; there is no chosen asymptotic cutoff. -/
def Good (n U : ℕ) : Prop :=
  2 ≤ scale n ∧ 0 < reserve n ∧ 2*U.size ≤ reserve n ∧
    4*block n*U.size^R ≤ (reserve n)^R

instance (n U : ℕ) : Decidable (Good n U) := by
  unfold Good
  infer_instance

def finiteComputedParameters (n U : ℕ) (h : Good n U) :
    CompleteAPSP.Parameters (block n) U where
  pool := computedPool n
  P := scale n
  lam := U.size
  k := R-1
  M := reserve n
  stages := (2*n).size
  prime _p hp := CertificationParameters.pool_prime (computedPool_eq n ▸ hp)
  lower _p hp := CertificationParameters.pool_lower (computedPool_eq n ▸ hp)
  P_pos := by have hh := h.1; omega
  power := CertificationParameters.magnitude_power _ _ h.1
  threshold := CertificationParameters.threshold_of_half _ _ h.2.1 h.2.2.1
  size := by
    have hM := h.2.1
    unfold reserve at hM ⊢
    have hR := CertificationParameters.reserve_size (scale n) R (by
      rw [← computedPool_eq]
      omega)
    simpa only [← computedPool_eq] using hR
  rate := by
    have hr := CertificationParameters.rate_of_sufficient (block n) U.size (reserve n)
      R (by norm_num [R]) h.2.2.1 h.2.2.2
    simpa only [Nat.sub_add_cancel (show 1 ≤ R by norm_num [R])] using hr

/-- Executable parameter selection. A caller handles none by the direct
algorithm; some contains its fully checked finite configuration. -/
def program (n U : ℕ) : Option (CompleteAPSP.Parameters (block n) U) :=
  if h : Good n U then some (finiteComputedParameters n U h) else none

theorem program_isSome_iff (n U : ℕ) : (program n U).isSome = true ↔ Good n U := by
  unfold program
  split_ifs <;> simp_all

theorem program_sound (n U : ℕ) (p : CompleteAPSP.Parameters (block n) U)
    (hp : program n U = some p) :
    p.pool = computedPool n ∧ p.P = scale n ∧ p.lam = U.size ∧
      p.k = R-1 ∧ p.M = reserve n ∧ p.stages = (2*n).size := by
  unfold program at hp
  split_ifs at hp with h
  · have heq : finiteComputedParameters n U h = p := Option.some.inj hp
    subst p
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem eventually_good (C κ : ℝ) (hC : 0 < C) :
    ∀ᶠ n : ℕ in atTop, ∀ U : ℕ, (U:ℝ) ≤ C*(n:ℝ)^κ → Good n U := by
  have hlo : ∀ᶠ n : ℕ in atTop,
      (1:ℝ)*(n:ℝ)^eta*(Real.log (n:ℝ))^4 ≤ (scale n:ℝ) := by
    filter_upwards [eventually_ge_atTop (3:ℕ)] with n hn
    simpa only [one_mul] using (scale_bounds n hn).1
  have hhi : ∀ᶠ n : ℕ in atTop,
      (scale n:ℝ) ≤ 512*(n:ℝ)^eta*(Real.log (n:ℝ))^4 := by
    filter_upwards [eventually_ge_atTop (3:ℕ)] with n hn
    exact (scale_bounds n hn).2
  have hh : ∀ᶠ n : ℕ in atTop, (block n:ℝ) ≤ 2*(n:ℝ)^b := by
    filter_upwards [eventually_ge_atTop (1:ℕ)] with n hn
    exact (block_bounds n hn).2
  have h := ComputableParameters.eventual_sufficient_scale scale block b eta
    C κ 1 512 R hh (by norm_num [R])
    (by norm_num [eta,b,bNumerator,bDenominator,R])
    (by norm_num [R,eta,b,bNumerator,bDenominator])
    hC (by norm_num) (by norm_num) hlo hhi
  filter_upwards [h] with n hn
  intro U hU
  simpa only [Good, reserve, computedPool_eq] using hn U hU

/-- The one executable program succeeds eventually on every
polynomially bounded magnitude. This is stronger than a pointwise
existence statement for configurations. -/
theorem eventually_program_isSome (C κ : ℝ) (hC : 0 < C) :
    ∀ᶠ n : ℕ in atTop, ∀ U : ℕ, (U:ℝ) ≤ C*(n:ℝ)^κ →
      (program n U).isSome = true := by
  filter_upwards [eventually_good C κ hC] with n hn
  intro U hU
  exact (program_isSome_iff n U).mpr (hn U hU)

theorem eventually_program_apspCap (degree : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ W : ℕ, W ≤ n^degree →
      (program n (192*n*W+40)).isSome = true := by
  have h := eventually_program_isSome 232 (degree+1:ℕ) (by norm_num)
  filter_upwards [h, eventually_ge_atTop (1:ℕ)] with n hn hn1
  intro W hW
  apply hn (192*n*W+40)
  have hc := ComputableParameters.apspCap_polynomial degree n W hn1 hW
  exact_mod_cast hc


#print axioms program_sound
#print axioms eventually_good
#print axioms eventually_program_isSome
#print axioms eventually_program_apspCap
end ThinMatrix.HalfSourcePrimeParameters
