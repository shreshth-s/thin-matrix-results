import CWEntropySurvival

set_option autoImplicit false
namespace ThinMatrix.CWEntropyFloors
open Filter
open scoped Topology
open CWCanonicalType CWTargetMarginals CWTypePrimeChoice CWQuantitativeCleanup CWEntropySurvival

def scale (N : ℕ) : ℕ := N/period

theorem floor_bounds (N : ℕ) : size (scale N) ≤ N ∧ N<size (scale N)+period := by
  have hp : 0<period := by norm_num [period]
  have h := Nat.mod_add_div N period
  rw [mul_comm period (N/period)] at h
  have hm := Nat.mod_lt N hp
  simp only [size_eq,scale]
  omega

theorem scale_positive (N : ℕ) (hN : period ≤ N) : 0<scale N :=
  Nat.div_pos hN (by norm_num [period])

theorem scale_tendsto : Tendsto scale atTop atTop := by
  apply Filter.tendsto_atTop.mpr
  intro b
  filter_upwards [eventually_ge_atTop (b*period)] with N hN
  exact (Nat.le_div_iff_mul_le (by norm_num [period])).mpr hN

/-- Floors only discard fewer than one fixed target period. Every strict
slack still gives the same rate measured against the original length N. -/
theorem exponential_survival (ε : ℝ) (he : 0<ε) :
    ∀ᶠ N : ℕ in atTop,
      ∃ r : CWHashFibers.Sample (ZMod (selected (size (scale N)) (reference (scale N)))) (size (scale N)),
        Real.exp ((N:ℝ)*(rate-ε)) ≤
          (survivors (selected (size (scale N)) (reference (scale N)))
            (size (scale N)) (reference (scale N))
            (ModularBehrendBuckets.buckets (selected (size (scale N)) (reference (scale N)))) r).card := by
  have hs := scale_tendsto.eventually (CWEntropySurvival.exponential_survival (ε/2) (by positivity))
  have hn := (tendsto_natCast_atTop_atTop (R:=ℝ)).eventually
    (eventually_ge_atTop (2*((period:ℝ)*rate)/ε))
  filter_upwards [hs,hn] with N hs hn
  obtain ⟨r,hr⟩ := hs
  refine ⟨r,le_trans ?_ hr⟩
  apply Real.exp_le_exp.mpr
  have hb := floor_bounds N
  have hl : (size (scale N):ℝ) ≤ N := by exact_mod_cast hb.1
  have hu : (N:ℝ)<size (scale N)+period := by exact_mod_cast hb.2
  have hdef := mul_le_mul_of_nonneg_right (show (N:ℝ)-size (scale N) ≤ period by linarith) rate_pos.le
  have hh : 2*((period:ℝ)*rate) ≤ (N:ℝ)*ε := (div_le_iff₀ he).mp hn
  nlinarith

#print axioms floor_bounds
#print axioms scale_positive
#print axioms scale_tendsto
#print axioms exponential_survival
end ThinMatrix.CWEntropyFloors
