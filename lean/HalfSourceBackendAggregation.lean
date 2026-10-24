import HalfSourceComputedCosts
import HalfSourceParameterMetadata
import BinaryTriangleCosts

/-! Intermediate composition of an explicitly supplied binary backend with
the new parameter program. The local production bound remains an explicit
premise here; this module is not the closed improved APSP theorem. -/
namespace ThinMatrix.HalfSourceBackendAggregation
open Filter Asymptotics BinaryTriangleExecution HalfSourceBatchFit HalfSourcePrimeParameters HalfSourceComputedCosts
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
attribute [local irreducible] HalfSourceBatchFit.R HalfSourceBatchFit.S HalfSourceBatchFit.block
noncomputable section

theorem pool_subset (n : ℕ) : computedPool n ⊆ PrimePool.candidates (scale n) := by
  intro p hp
  have hh := (Finset.mem_sdiff.mp hp).1
  rw [PrimePool.enumeratedCandidates_eq] at hh
  exact hh

def phaseOfPool (n : ℕ) (factors : List ℕ) (hlen : factors.length ≤ R)
    (hvalid : ∀ p∈factors,p∈computedPool n) : Call n where
  factors := factors
  length_le := hlen
  valid p hp := pool_subset n (hvalid p hp)

theorem rounds_log (n U : ℕ) (hn : 3 ≤ n)
    (parameters : CompleteAPSP.Parameters (block n) U) (hp : program n U=some parameters) :
    (parameters.stages*R:ℕ) ≤ (6*(R:ℝ))*Real.log (n:ℝ) := by
  have hs := (program_sound n U parameters hp).2.2.2.2.2
  have hsize := ParameterExecution.size_mul 2 n
  have hnsize := ComputableParameters.size_le_four_log n hn
  have hlog := PhaseGeometry.one_le_log_nat n hn
  have hh : ((2*n).size:ℝ) ≤ 2+(n.size:ℝ) := by
    exact_mod_cast (show (2*n).size ≤ 2+n.size by simpa only [show Nat.size 2=2 by decide] using hsize)
  rw [hs,Nat.cast_mul]
  nlinarith [Nat.cast_nonneg (α:=ℝ) R]

/-- Price every actual adaptive call in the chronological binary trace,
including all candidate counts and every prime-prefix length. -/
theorem solve_backend_le_ledger {n U : ℕ} {Payload : Type}
    (hn : 3 ≤ n) (backend : Backend n (block n) Payload)
    (parameters : CompleteAPSP.Parameters (block n) U) (hp : program n U=some parameters)
    (static : Static (n:=n) parameters) (X Y T : IntTable n)
    (C : ℝ) (k : ℕ) (hC : 0 ≤ C)
    (hfactory : ∀ phase : Call n, EndToEndAPSP.ValidFactors phase.factors →
      ∀ (selected : List ℕ) (candidate : ℕ),phase.factors=selected++[candidate] →
      ∀ active : ArrayCompositeAlgorithm.Flags (EndToEndAPSP.incidenceSize n (block n)),
      (((backend.oracle X Y T).table selected candidate active).work:ℝ) ≤
        C*(Real.log (n:ℝ))^k*phaseRawSum n phase) :
    ((solve backend parameters static X Y T).backendWork:ℝ) ≤
      (6*(R:ℝ)*C)*(Real.log (n:ℝ))^(k+1)*allPhaseLedger n := by
  let out := solve backend parameters static X Y T
  let calls := out.calls
  have hparams := program_sound n U parameters hp
  have hpool : parameters.pool=computedPool n := hparams.1
  have hkR : parameters.k+1=R := by
    rw[hparams.2.2.2.1]
    exact Nat.sub_add_cancel (by norm_num[HalfSourceBatchFit.R])
  have hthree : ∀ p∈parameters.pool,p≠3 := by
    intro p hp
    rw[hpool] at hp
    exact fun heq => (Finset.mem_sdiff.mp hp).2 (by simp only[heq,Finset.mem_singleton])
  have hlen (i : Fin calls.length) :
      ((calls.get i).factors.selected++[(calls.get i).factors.candidate]).length ≤ R := by
    have hh := solve_factors_length backend parameters static X Y T (calls.get i) (List.get_mem calls i)
    simpa only[List.length_append,List.length_singleton,hkR] using hh
  have hmem (i : Fin calls.length) :
      ∀ p∈(calls.get i).factors.selected++[(calls.get i).factors.candidate],p∈computedPool n := by
    intro p hp
    rw[←hpool]
    exact solve_factor_property backend parameters static X Y T (fun p=>p∈parameters.pool)
      (fun _ h=>h) (calls.get i) (List.get_mem calls i) p hp
  let phases : Fin calls.length → Call n := fun i => phaseOfPool n
    ((calls.get i).factors.selected++[(calls.get i).factors.candidate]) (hlen i) (hmem i)
  have hcount : calls.length ≤ (parameters.stages*R)*(PrimePool.candidates (scale n)).card := by
    have hh := solve_calls_bound backend parameters static X Y T
    rw[hkR,hpool] at hh
    exact hh.trans (Nat.mul_le_mul_left _ (Finset.card_le_card (pool_subset n)))
  have hlocal (i : Fin calls.length) : ((calls.get i).result.work:ℝ) ≤ C*(Real.log (n:ℝ))^k*phaseRawSum n (phases i) := by
    have hv := solve_valid_histories backend parameters static X Y T hthree (calls.get i) (List.get_mem calls i)
    have hr := solve_provenance backend parameters static X Y T (calls.get i) (List.get_mem calls i)
    have hh := hfactory (phases i) hv (calls.get i).factors.selected (calls.get i).factors.candidate rfl (calls.get i).factors.active
    rw[←hr] at hh
    exact hh
  have hsum := Finset.sum_le_sum (fun i (_ : i∈Finset.univ) => hlocal i)
  rw[←Finset.mul_sum] at hsum
  have hphase := callFamily_bound n calls.length (parameters.stages*R) hn phases hcount
  have hlog0 : 0 ≤ Real.log (n:ℝ) := by linarith [PhaseGeometry.one_le_log_nat n hn]
  have hcoef : 0 ≤ C*(Real.log (n:ℝ))^k := mul_nonneg hC (pow_nonneg hlog0 k)
  have hround := rounds_log n U hn parameters hp
  have heq := BinaryTriangleCosts.Aggregation.solve_backendWork_eq_fin_sum backend parameters static X Y T
  rw[heq,Nat.cast_sum]
  calc
    _ ≤ C*(Real.log (n:ℝ))^k*(∑ i : Fin calls.length,phaseRawSum n (phases i)) := hsum
    _ ≤ C*(Real.log (n:ℝ))^k*((parameters.stages*R:ℕ)*allPhaseLedger n) := mul_le_mul_of_nonneg_left hphase hcoef
    _ ≤ C*(Real.log (n:ℝ))^k*((6*(R:ℝ)*Real.log (n:ℝ))*allPhaseLedger n) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hround (allPhaseLedger_nonneg n hn)) hcoef
    _ = _ := by rw[pow_succ];ring

#print axioms pool_subset
#print axioms rounds_log
#print axioms solve_backend_le_ledger
end
end ThinMatrix.HalfSourceBackendAggregation
