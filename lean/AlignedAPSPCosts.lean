import AlignedAPSP
import ComputedReductionCosts
import BackendScalarBits
import UniformAPSPBound

/-!
# Costs of the concrete aligned producer

This module prices the counters returned by the same retained binary-cyclic
preparation and selected queries used by `AlignedAPSP`. Original coefficient
sources are zero or one; the multiplier and complete-numerator width bounds
are derived from those actual arrays. Scalar and controller binary-trace
refinement remains distinct from this finite returned-counter composition.
-/
namespace ThinMatrix.AlignedAPSPCosts
noncomputable section
open scoped BigOperators
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000

namespace Numerator
open BackendNumeratorBounds PhaseGeometry AsymptoticCosts
def cyclicLogConstant (R : ℕ) : ℝ :=
  (|Real.log ((8192:ℝ)^R)|+(4*R:ℕ)+(R:ℝ)*eta)/Real.log 2

theorem computed_cyclic_size_le_log (R S n : ℕ) (hn : 3 ≤ n)
    (call : ComputedPhaseGeometry.Call R n) :
    ((call.cyclic S).size:ℝ) ≤ (cyclicLogConstant R+1)*Real.log (n:ℝ) := by
  have hcyc := ComputedPhaseGeometry.actual_cyclic_bounds R S n hn call
  have hnpos : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hqpos : 0 < call.cyclic S := by
    exact_mod_cast (Real.rpow_pos_of_pos hnpos _).trans_le hcyc.1
  have hsR : ringExponent S call.factors.length ≤ (R:ℝ)*eta := by
    apply mul_le_mul_of_nonneg_right _ stageRelations.1
    exact_mod_cast (Nat.sub_le call.factors.length S).trans call.length_le
  have hpoly : (call.cyclic S:ℝ) ≤
      (8192:ℝ)^R*(Real.log (n:ℝ))^(4*R)*(n:ℝ)^((R:ℝ)*eta) := by
    calc
      _ ≤ ComputedPhaseGeometry.phaseOverhead R n*(n:ℝ)^(ringExponent S call.factors.length) := hcyc.2
      _ ≤ ComputedPhaseGeometry.phaseOverhead R n*(n:ℝ)^((R:ℝ)*eta) := by
        apply mul_le_mul_of_nonneg_left _ (by unfold ComputedPhaseGeometry.phaseOverhead; positivity)
        exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1≤n by omega)) hsR
      _ = _ := rfl
  have hlog := ComputedPhaseGeometry.generic_scale_log_upper n (call.cyclic S) (4*R)
    ((8192:ℝ)^R) ((R:ℝ)*eta) hn (by positivity) hqpos hpoly
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hdiv : Real.log (call.cyclic S:ℝ)/Real.log 2 ≤
      cyclicLogConstant R*Real.log (n:ℝ) := by
    simpa only [cyclicLogConstant, div_mul_eq_mul_div] using div_le_div_of_nonneg_right hlog htwo.le
  have hsize := CertificationParameters.size_le_log (call.cyclic S)
  have hl := one_le_log_nat n hn
  nlinarith

def numeratorBitsConstant (R : ℕ) : ℝ :=
  2*(RealCertificate.c+3)*ComputedPhaseGeometry.indexMajor R+cyclicLogConstant R+1

theorem numeratorBitsConstant_nonneg (R : ℕ) : 0 ≤ numeratorBitsConstant R := by
  have hc : 0 ≤ RealCertificate.c := by norm_num [RealCertificate.c]
  have hI := (ComputedPhaseGeometry.indexMajor_pos R).le
  have heta := stageRelations.1
  unfold numeratorBitsConstant cyclicLogConstant
  positivity

theorem computed_numeratorBits_log_bound (R S n : ℕ) (hn : 3 ≤ n)
    (call : ComputedPhaseGeometry.Call R n) :
    let m := ComputedPhaseGeometry.innerPower n call S
    let L := Nat.ceil (RealCertificate.c*(m:ℝ))
    (numeratorBitBudget L m (call.cyclic S) 1:ℝ) ≤ numeratorBitsConstant R*Real.log (n:ℝ) := by
  let m := ComputedPhaseGeometry.innerPower n call S
  let L := Nat.ceil (RealCertificate.c*(m:ℝ))
  have hL := ComputedPhaseGeometry.actual_roundedLength_le_log R S n hn call
  have hm := ComputedPhaseGeometry.actual_innerPower_add_one_le_log R S n hn call
  have hq := computed_cyclic_size_le_log R S n hn call
  have hnum : (numeratorBitBudget L m (call.cyclic S) 1:ℝ) =
      2*(L:ℝ)+2*(m:ℝ)+((call.cyclic S).size:ℝ)+3 := by
    norm_num [numeratorBitBudget]
    ring
  change (numeratorBitBudget L m (call.cyclic S) 1:ℝ) ≤ _
  rw [hnum]
  change (L:ℝ)+1 ≤ _ at hL
  change (m:ℝ)+1 ≤ _ at hm
  unfold numeratorBitsConstant
  nlinarith

end Numerator

namespace Geometry
open FoldedBackendExecution
theorem history_folded {R P : ℕ} (call : PhaseGeometry.PhaseCall R P) (S : ℕ)
    (hv : EndToEndAPSP.ValidFactors call.factors) :
    (EndToEndAPSP.historyFactorization S call.factors hv).folded = call.folded S := rfl

theorem history_cyclic {R P : ℕ} (call : PhaseGeometry.PhaseCall R P) (S : ℕ)
    (hv : EndToEndAPSP.ValidFactors call.factors) :
    (EndToEndAPSP.historyFactorization S call.factors hv).cyclic = call.cyclic S := rfl

theorem history_physicalFold {R P : ℕ} (call : PhaseGeometry.PhaseCall R P) (S : ℕ)
    (hv : EndToEndAPSP.ValidFactors call.factors) :
    physicalFold (EndToEndAPSP.historyFactorization S call.factors hv) =
      3 * call.folded S := rfl

theorem history_physicalFold_eq {R P : ℕ} (call : PhaseGeometry.PhaseCall R P) (S : ℕ)
    (hv : EndToEndAPSP.ValidFactors call.factors) :
    physicalFold (EndToEndAPSP.historyFactorization S call.factors hv) =
      PhaseGeometry.physicalFold call S := rfl

theorem history_outerSize (n : ℕ) {R P : ℕ} (call : PhaseGeometry.PhaseCall R P) (S : ℕ)
    (hv : EndToEndAPSP.ValidFactors call.factors) :
    outerSize n (physicalFold (EndToEndAPSP.historyFactorization S call.factors hv)) =
      PhaseGeometry.outerSize call S n := rfl

theorem history_middleExponent (n : ℕ) {R P : ℕ} (call : PhaseGeometry.PhaseCall R P) (S : ℕ)
    (hv : EndToEndAPSP.ValidFactors call.factors) :
    middleExponent (ComputableParameters.block n)
      (physicalFold (EndToEndAPSP.historyFactorization S call.factors hv)) =
      ComputedPhaseGeometry.innerPower n call S := rfl

theorem history_middleSize (n : ℕ) {R P : ℕ} (call : PhaseGeometry.PhaseCall R P) (S : ℕ)
    (hv : EndToEndAPSP.ValidFactors call.factors) :
    middleSize (ComputableParameters.block n)
      (physicalFold (EndToEndAPSP.historyFactorization S call.factors hv)) =
      ComputedPhaseGeometry.innerDimension n call S := rfl

theorem history_shape_length (n : ℕ) {R P : ℕ} (call : PhaseGeometry.PhaseCall R P) (S : ℕ)
    (hv : EndToEndAPSP.ValidFactors call.factors) :
    (AlignedAPSP.shape (ComputableParameters.block n)
      (physicalFold (EndToEndAPSP.historyFactorization S call.factors hv))).L =
      ComputableParameters.ordinaryLength (ComputedPhaseGeometry.innerPower n call S) := rfl

theorem history_shape_cutoff (n : ℕ) {R P : ℕ} (call : PhaseGeometry.PhaseCall R P) (S : ℕ)
    (hv : EndToEndAPSP.ValidFactors call.factors) :
    (AlignedAPSP.shape (ComputableParameters.block n)
      (physicalFold (EndToEndAPSP.historyFactorization S call.factors hv))).t =
      ComputableParameters.channelLength (ComputedPhaseGeometry.innerPower n call S) := rfl

theorem history_formationSites (n : ℕ) {R P : ℕ} (call : PhaseGeometry.PhaseCall R P) (S : ℕ)
    (hv : EndToEndAPSP.ValidFactors call.factors) :
    formationSites n (ComputableParameters.block n)
      (EndToEndAPSP.historyFactorization S call.factors hv) =
      2 * call.cyclic S * PhaseGeometry.outerSize call S n *
        ComputedPhaseGeometry.innerDimension n call S := rfl

theorem history_blockCount (n : ℕ) :
    CompactBlocks.blockCount n (ComputableParameters.block n) =
      ComputedPhaseGeometry.blockCount n := rfl

theorem history_incidenceSize (n : ℕ) :
    EndToEndAPSP.incidenceSize n (ComputableParameters.block n) =
      3 * ComputedPhaseGeometry.queryCount n := by
  unfold EndToEndAPSP.incidenceSize CompactBlocks.blockCount
    ComputedPhaseGeometry.queryCount ComputedPhaseGeometry.blockCount
  ring

/-- The physical producer's exact rounded grid obeys the computed uniform
full-grid bound, with its own middle exponent and original tile geometry. -/
theorem all_history_candidate_tiles_fit :
    ∀ᶠ n : ℕ in Filter.atTop,
      ∀ call : ComputedPhaseGeometry.Call AlignedCertificate.R n,
      ∀ hv : EndToEndAPSP.ValidFactors call.factors,
      let f := EndToEndAPSP.historyFactorization AlignedCertificate.S call.factors hv
      let h := ComputableParameters.block n
      (AlignedAPSP.shape h (physicalFold f)).L.choose
          (middleExponent h (physicalFold f)) *
        4 ^ ((AlignedAPSP.shape h (physicalFold f)).L -
          middleExponent h (physicalFold f)) ≤
      outerSize n (physicalFold f) := by
  filter_upwards [ComputedPhaseGeometry.all_computed_candidate_tiles_fit] with n hn
  intro call hv
  simpa only [history_shape_length, history_middleExponent, history_outerSize] using hn call

/-- Exactly the complete signed incidence row used by the producer, including
all three physical signed windows. -/
theorem history_queryFormationSites (n : ℕ) :
    queryFormationSites n (ComputableParameters.block n) =
      300 * ComputedPhaseGeometry.queryCount n := by
  unfold queryFormationSites
  rw [history_incidenceSize]
  ring

/-- The same bridge with the literal history supplied by a successful
parameter-program output. No modulus-only factorization is selected. -/
theorem all_program_physical_tiles_fit :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ U : ℕ,
      ∀ p : CompleteAPSP.Parameters (ComputableParameters.block n) U,
      ∀ _hp : ComputableParameters.program n U = some p, ∀ factors : List ℕ,
      ∀ _hlen : factors.length ≤ p.k + 1, ∀ _hvalid : ∀ q ∈ factors, q ∈ p.pool,
      ∀ hv : EndToEndAPSP.ValidFactors factors,
      let f := EndToEndAPSP.historyFactorization AlignedCertificate.S factors hv
      let h := ComputableParameters.block n
      (AlignedAPSP.shape h (physicalFold f)).L.choose
          (middleExponent h (physicalFold f)) *
        4 ^ ((AlignedAPSP.shape h (physicalFold f)).L -
          middleExponent h (physicalFold f)) ≤
      outerSize n (physicalFold f) := by
  filter_upwards [all_history_candidate_tiles_fit] with n hn
  intro U p hp factors hlen hvalid hv
  exact hn (ComputedPhaseGeometry.phaseCallOfProgram n U p hp factors hlen hvalid) hv

end Geometry

def binaryUnitCoefficient : ℕ :=
  2^70*(AdaptiveBitBounds.computedCyclicConstant+7*AdaptiveBitBounds.computedLengthConstant+
    AdaptiveBitBounds.computedIndexConstant+104)^11

def binaryAllowanceConstant : ℝ :=
  binaryUnitCoefficient*(2+1/Real.log 2)^11

def binaryAllowance (n : ℕ) : ℝ := binaryAllowanceConstant*(Real.log (n:ℝ))^11

theorem binaryAllowanceConstant_pos : 0 < binaryAllowanceConstant := by
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hK : 0 < binaryUnitCoefficient := by unfold binaryUnitCoefficient; positivity
  unfold binaryAllowanceConstant
  positivity

theorem binaryAllowance_ge_one (n : ℕ) (hn : 3 ≤ n) : 1 ≤ binaryAllowance n := by
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hK : 1 ≤ binaryUnitCoefficient := by
    have hpos : 0 < binaryUnitCoefficient := by unfold binaryUnitCoefficient; positivity
    omega
  have hKR : (1:ℝ) ≤ binaryUnitCoefficient := by exact_mod_cast hK
  have hsize : (1:ℝ) ≤ 2+1/Real.log 2 := by linarith [one_div_pos.mpr htwo]
  have hlog := PhaseGeometry.one_le_log_nat n hn
  unfold binaryAllowance binaryAllowanceConstant
  exact one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le hKR (one_le_pow₀ hsize)) (one_le_pow₀ hlog)

/-- The concrete binary multiplier allowance for the actual zero/one sources,
with no multiplier-width or backend-time assumption. -/
theorem computed_binary_work_le_allowance (n : ℕ) (hn : 3 ≤ n)
    (call : ComputedPhaseGeometry.Call AlignedCertificate.R n) :
    let m := ComputedPhaseGeometry.innerPower n call AlignedCertificate.S
    let L := Nat.ceil (RealCertificate.c*(m:ℝ))
    let q := call.cyclic AlignedCertificate.S
    (BinaryMultiplierAdapter.workBound q (AdaptiveBitBounds.highInputBudget L m 1):ℝ) ≤
      (q:ℝ)*binaryAllowance n := by
  let m := ComputedPhaseGeometry.innerPower n call AlignedCertificate.S
  let L := Nat.ceil (RealCertificate.c*(m:ℝ))
  let q := call.cyclic AlignedCertificate.S
  have h := AdaptiveBitBounds.computed_binary_workBound_polylog n 0 1 hn call (by simp)
  have hR : (BinaryMultiplierAdapter.workBound q (AdaptiveBitBounds.highInputBudget L m 1):ℝ) ≤
      (binaryUnitCoefficient:ℝ)*q*((n.size+1:ℕ):ℝ)^11 := by
    dsimp only at h
    simp only [Nat.add_zero] at h
    exact_mod_cast h
  have hs := BackendCostRefinement.size_add_one_le_log n hn
  calc
    _ ≤ (binaryUnitCoefficient:ℝ)*q*((n.size+1:ℕ):ℝ)^11 := hR
    _ ≤ (binaryUnitCoefficient:ℝ)*q*((2+1/Real.log 2)*Real.log (n:ℝ))^11 := by
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg (n.size+1)) hs 11)
        (mul_nonneg (Nat.cast_nonneg binaryUnitCoefficient) (Nat.cast_nonneg q))
    _ = _ := by unfold binaryAllowance binaryAllowanceConstant; rw [mul_pow]; ring

namespace Provenance
open StoredMinPlusAPSP
/-- Factor geometry of a retained call in the actual aligned counted solve. -/
noncomputable def solvePhaseCall {n U : ℕ}
    (parameters : CompleteAPSP.Parameters (ComputableParameters.block n) U)
    (hp : ComputableParameters.program n U = some parameters)
    (A B T : IntTable n)
    (call : CountedArrayComposite.Call
      (EndToEndAPSP.incidenceSize n (ComputableParameters.block n))
      (AlignedAPSP.Payload n (ComputableParameters.block n)))
    (hc : call ∈ (CountedEndToEndAPSP.solve
      (AlignedAPSP.backend n (ComputableParameters.block n) (EndToEndAPSP.block_pos n))
      parameters A B T).calls) : ComputedPhaseGeometry.Call AlignedCertificate.R n :=
  ComputedPhaseGeometry.phaseCallOfProgram n U parameters hp
    (call.factors.selected ++ [call.factors.candidate])
    (by
      have hl := CountedEndToEndAPSP.solve_factors_length
        (AlignedAPSP.backend n (ComputableParameters.block n) (EndToEndAPSP.block_pos n))
        parameters A B T call hc
      simpa only [List.length_append, List.length_singleton] using hl)
    (CountedEndToEndAPSP.solve_factor_membership
        (AlignedAPSP.backend n (ComputableParameters.block n) (EndToEndAPSP.block_pos n))
        parameters A B T call hc)

@[simp] theorem solvePhaseCall_factors {n U : ℕ}
    (parameters : CompleteAPSP.Parameters (ComputableParameters.block n) U)
    (hp : ComputableParameters.program n U = some parameters)
    (A B T : IntTable n)
    (call : CountedArrayComposite.Call
      (EndToEndAPSP.incidenceSize n (ComputableParameters.block n))
      (AlignedAPSP.Payload n (ComputableParameters.block n)))
    (hc : call ∈ (CountedEndToEndAPSP.solve
      (AlignedAPSP.backend n (ComputableParameters.block n) (EndToEndAPSP.block_pos n))
      parameters A B T).calls) :
    (solvePhaseCall parameters hp A B T call hc).factors =
      call.factors.selected ++ [call.factors.candidate] := rfl

theorem solve_call_valid_table {n U : ℕ}
    (parameters : CompleteAPSP.Parameters (ComputableParameters.block n) U)
    (hp : ComputableParameters.program n U = some parameters)
    (A B T : IntTable n)
    (call : CountedArrayComposite.Call
      (EndToEndAPSP.incidenceSize n (ComputableParameters.block n))
      (AlignedAPSP.Payload n (ComputableParameters.block n)))
    (hc : call ∈ (CountedEndToEndAPSP.solve
      (AlignedAPSP.backend n (ComputableParameters.block n) (EndToEndAPSP.block_pos n))
      parameters A B T).calls) :
    EndToEndAPSP.ValidFactors (call.factors.selected ++ [call.factors.candidate]) ∧
      call.result = AlignedAPSP.table A B T
        call.factors.selected call.factors.candidate call.factors.active := by
  have hthree : ∀ p ∈ parameters.pool, p ≠ 3 := by
    intro p hpmem
    rw [(ComputableParameters.program_sound n U parameters hp).1] at hpmem
    exact fun heq => (Finset.mem_sdiff.mp hpmem).2
      (by simp only [heq, Finset.mem_singleton])
  exact ⟨CountedEndToEndAPSP.solve_valid_histories _ parameters A B T hthree call hc,
    CountedEndToEndAPSP.solve_provenance _ parameters A B T call hc⟩

/-- The actual adaptive APSP callback supplies the geometry and exact producer
provenance for each retained backend call, through run_successful_call. -/
theorem run_successful_physical_calls {n : ℕ} (hn : 2 ≤ n)
    (w : OptionalTable n) (W : ℕ)
    (parameters : CompleteAPSP.Parameters (ComputableParameters.block n)
      (EndToEndAPSP.magnitudeCap n W))
    (hp : ComputableParameters.program n (EndToEndAPSP.magnitudeCap n W) = some parameters)
    (hw : APSPReduction.EdgeBound (decode w) W)
    (c : StoredMinPlusAPSP.Call n (CountedEndToEndAPSP.CallbackPayload n
      (ComputableParameters.block n) (AlignedAPSP.Payload n (ComputableParameters.block n))))
    (hc : c ∈ (AlignedAPSP.run w W).calls) :
    ∃ out : CountedEndToEndAPSP.Result n (ComputableParameters.block n)
        (AlignedAPSP.Payload n (ComputableParameters.block n)),
      c.output.payload = some out ∧
      c.output.work = out.resources.total ∧
      out.resources.backendWork = CountedArrayComposite.workSum out.calls ∧
      out.calls.length ≤ parameters.stages*(parameters.k+1)*parameters.pool.card ∧
      ∀ call ∈ out.calls,
        ∃ phase : ComputedPhaseGeometry.Call AlignedCertificate.R n,
          phase.factors = call.factors.selected ++ [call.factors.candidate] ∧
          EndToEndAPSP.ValidFactors phase.factors ∧
          call.result = AlignedAPSP.table c.left c.right c.target
            call.factors.selected call.factors.candidate call.factors.active := by
  obtain ⟨out, hpayload, hwork, hbackend, hcount, _, _, _, _, hcalls⟩ :=
    CountedEndToEndAPSP.run_successful_call hn
      (AlignedAPSP.backend n (ComputableParameters.block n) (EndToEndAPSP.block_pos n))
      w W parameters hp hw c hc
  refine ⟨out, hpayload, hwork, hbackend, hcount, ?_⟩
  intro call hcall
  obtain ⟨hresult, hvalid, hlen, hmem⟩ := hcalls call hcall
  let phase : ComputedPhaseGeometry.Call AlignedCertificate.R n :=
    ComputedPhaseGeometry.phaseCallOfPool _ _
      (call.factors.selected ++ [call.factors.candidate])
      (by simpa only [List.length_append, List.length_singleton,
        ComputableParameters.factorCount, AlignedCertificate.R] using hlen)
      (by
        intro p hp'
        rw [← (EndToEndAPSP.success_configuration n W parameters hp).1]
        exact hmem p hp')
  exact ⟨phase, rfl, hvalid, hresult⟩

/-- Proof geometry is mapped from the actual retained list; no producer is
re-evaluated and each member uses its literal factor history. -/
noncomputable def retainedPhaseCalls {n U I : ℕ} {Payload : Type}
    (parameters : CompleteAPSP.Parameters (ComputableParameters.block n) U)
    (hp : ComputableParameters.program n U = some parameters)
    (calls : List (CountedArrayComposite.Call I Payload))
    (hlen : ∀ call ∈ calls, call.factors.selected.length+1 ≤ parameters.k+1)
    (hmem : ∀ call ∈ calls, ∀ p ∈ call.factors.selected ++ [call.factors.candidate],
      p ∈ parameters.pool) : List (ComputedPhaseGeometry.Call AlignedCertificate.R n) :=
  calls.attach.map (fun call => ComputedPhaseGeometry.phaseCallOfProgram n U parameters hp
    (call.val.factors.selected ++ [call.val.factors.candidate])
    (by simpa only [List.length_append, List.length_singleton] using hlen call.val call.property)
    (hmem call.val call.property))

@[simp] theorem retainedPhaseCalls_length {n U I : ℕ} {Payload : Type}
    (parameters : CompleteAPSP.Parameters (ComputableParameters.block n) U)
    (hp : ComputableParameters.program n U = some parameters)
    (calls : List (CountedArrayComposite.Call I Payload))
    (hlen : ∀ call ∈ calls, call.factors.selected.length+1 ≤ parameters.k+1)
    (hmem : ∀ call ∈ calls, ∀ p ∈ call.factors.selected ++ [call.factors.candidate],
      p ∈ parameters.pool) :
    (retainedPhaseCalls parameters hp calls hlen hmem).length = calls.length := by
  simp only [retainedPhaseCalls, List.length_map, List.length_attach]

@[simp] theorem retainedPhaseCalls_factors {n U I : ℕ} {Payload : Type}
    (parameters : CompleteAPSP.Parameters (ComputableParameters.block n) U)
    (hp : ComputableParameters.program n U = some parameters)
    (calls : List (CountedArrayComposite.Call I Payload))
    (hlen : ∀ call ∈ calls, call.factors.selected.length+1 ≤ parameters.k+1)
    (hmem : ∀ call ∈ calls, ∀ p ∈ call.factors.selected ++ [call.factors.candidate],
      p ∈ parameters.pool) :
    (retainedPhaseCalls parameters hp calls hlen hmem).map PhaseGeometry.PhaseCall.factors =
      calls.map (fun call => call.factors.selected ++ [call.factors.candidate]) := by
  simp [retainedPhaseCalls, List.map_map]

theorem retainedPhaseCalls_count {n U I : ℕ} {Payload : Type}
    (parameters : CompleteAPSP.Parameters (ComputableParameters.block n) U)
    (hp : ComputableParameters.program n U = some parameters)
    (calls : List (CountedArrayComposite.Call I Payload))
    (hlen : ∀ call ∈ calls, call.factors.selected.length+1 ≤ parameters.k+1)
    (hmem : ∀ call ∈ calls, ∀ p ∈ call.factors.selected ++ [call.factors.candidate],
      p ∈ parameters.pool)
    (hcount : calls.length ≤ parameters.stages*(parameters.k+1)*parameters.pool.card) :
    (retainedPhaseCalls parameters hp calls hlen hmem).length ≤
      parameters.stages*AlignedCertificate.R*(ComputableParameters.computedPool n).card := by
  have hk := (ComputableParameters.program_sound n U parameters hp).2.2.2.1
  have hpool := (ComputableParameters.program_sound n U parameters hp).1
  rw [retainedPhaseCalls_length]
  have hkR : parameters.k+1 = AlignedCertificate.R := by
    rw [hk]
    norm_num [ComputableParameters.factorCount, AlignedCertificate.R]
  rwa [hkR, hpool] at hcount

/-- Retains the work equations and the exact attached-list map needed for
phase-cost aggregation over the actual adaptive callback. -/
theorem run_successful_physical_trace {n : ℕ} (hn : 2 ≤ n)
    (w : OptionalTable n) (W : ℕ)
    (parameters : CompleteAPSP.Parameters (ComputableParameters.block n)
      (EndToEndAPSP.magnitudeCap n W))
    (hp : ComputableParameters.program n (EndToEndAPSP.magnitudeCap n W) = some parameters)
    (hw : APSPReduction.EdgeBound (decode w) W)
    (c : StoredMinPlusAPSP.Call n (CountedEndToEndAPSP.CallbackPayload n
      (ComputableParameters.block n) (AlignedAPSP.Payload n (ComputableParameters.block n))))
    (hc : c ∈ (AlignedAPSP.run w W).calls) :
    ∃ (out : CountedEndToEndAPSP.Result n (ComputableParameters.block n)
        (AlignedAPSP.Payload n (ComputableParameters.block n)))
      (hlen : ∀ call ∈ out.calls, call.factors.selected.length+1 ≤ parameters.k+1)
      (hmem : ∀ call ∈ out.calls, ∀ p ∈ call.factors.selected ++ [call.factors.candidate],
        p ∈ parameters.pool),
      c.output.payload = some out ∧ c.output.work = out.resources.total ∧
      out.resources.backendWork = CountedArrayComposite.workSum out.calls ∧
      out.calls.length ≤ parameters.stages*(parameters.k+1)*parameters.pool.card ∧
      (retainedPhaseCalls parameters hp out.calls hlen hmem).length = out.calls.length ∧
      (retainedPhaseCalls parameters hp out.calls hlen hmem).length ≤
        parameters.stages*AlignedCertificate.R*(ComputableParameters.computedPool n).card ∧
      (retainedPhaseCalls parameters hp out.calls hlen hmem).map PhaseGeometry.PhaseCall.factors =
        out.calls.map (fun call => call.factors.selected ++ [call.factors.candidate]) ∧
      ∀ call ∈ out.calls,
        call.result = AlignedAPSP.table c.left c.right c.target
          call.factors.selected call.factors.candidate call.factors.active ∧
        EndToEndAPSP.ValidFactors (call.factors.selected ++ [call.factors.candidate]) := by
  obtain ⟨out, hpayload, hwork, hbackend, hcount, _, _, _, _, hcalls⟩ :=
    CountedEndToEndAPSP.run_successful_call hn
      (AlignedAPSP.backend n (ComputableParameters.block n) (EndToEndAPSP.block_pos n))
      w W parameters hp hw c hc
  have hlen : ∀ call ∈ out.calls, call.factors.selected.length+1 ≤ parameters.k+1 := by
    have hk := (EndToEndAPSP.success_configuration n W parameters hp).2.2.2.1
    intro call hcall
    simpa only [hk, ComputableParameters.factorCount] using (hcalls call hcall).2.2.1
  have hmem : ∀ call ∈ out.calls, ∀ p ∈ call.factors.selected ++ [call.factors.candidate],
      p ∈ parameters.pool := fun call hcall => (hcalls call hcall).2.2.2
  refine ⟨out, hlen, hmem, hpayload, hwork, hbackend, hcount,
    retainedPhaseCalls_length parameters hp out.calls hlen hmem,
    retainedPhaseCalls_count parameters hp out.calls hlen hmem hcount,
    retainedPhaseCalls_factors parameters hp out.calls hlen hmem, ?_⟩
  intro call hcall
  exact ⟨(hcalls call hcall).1, (hcalls call hcall).2.1⟩

end Provenance



theorem phaseRawSum_nonneg (n : ℕ) (call : ComputedPhaseGeometry.Call AlignedCertificate.R n) :
    0 ≤ ComputedReductionCosts.phaseRawSum n call := by
  unfold ComputedReductionCosts.phaseRawSum
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg (Nat.cast_nonneg _) (ReductionCosts.rawTerm_nonneg _ _ _ _ _ _
    (Nat.cast_nonneg n) (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _) i)

/-- The positive HIGH-query exponent pays the literal target/key/count
formation sites, once per signed incidence. -/
theorem phaseRawSum_dominates_queries (n : ℕ)
    (call : ComputedPhaseGeometry.Call AlignedCertificate.R n) :
    (ComputedPhaseGeometry.queryCount n:ℝ) ≤ ComputedReductionCosts.phaseRawSum n call := by
  have hD : (1:ℝ) ≤ ComputedPhaseGeometry.innerDimension n call AlignedCertificate.S := by
    rw [ComputedPhaseGeometry.innerDimension_eq_power, Nat.cast_pow, Nat.cast_ofNat]
    exact one_le_pow₀ (by norm_num)
  have he : 0 ≤ ThinProductCosts.highQueryExponent RealCertificate.theta := by
    rw [ReductionCosts.highQueryExponent_eq_q2]
    have hentropy : 0 ≤ RealCertificate.entropy RealCertificate.theta := by
      linarith [RealCertificate.entropyTheta.1]
    have ht : 0 ≤ RealCertificate.theta := by norm_num [RealCertificate.theta]
    have hlog : 0 ≤ Real.log 4 := (Real.log_pos (by norm_num)).le
    unfold RealCertificate.q2
    positivity
  have hpow := Real.one_le_rpow hD he
  have hsingle := Finset.single_le_sum
    (s:=Finset.univ) (a:=(2:Fin 6)) (f:=fun i =>
      (ComputedPhaseGeometry.blockCount n:ℝ)*ReductionCosts.rawTerm RealCertificate.c
        RealCertificate.theta n (PhaseGeometry.outerSize call AlignedCertificate.S n)
        (ComputedPhaseGeometry.innerDimension n call AlignedCertificate.S)
        (call.cyclic AlignedCertificate.S) i)
    (fun i _ => mul_nonneg (Nat.cast_nonneg _) (ReductionCosts.rawTerm_nonneg _ _ _ _ _ _
      (Nat.cast_nonneg n) (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _) i))
    (Finset.mem_univ (2:Fin 6))
  change _ ≤ ComputedReductionCosts.phaseRawSum n call at hsingle
  calc
    _ = (ComputedPhaseGeometry.blockCount n:ℝ)*(n:ℝ)^2 := by
      unfold ComputedPhaseGeometry.queryCount
      push_cast
      ring
    _ ≤ (ComputedPhaseGeometry.blockCount n:ℝ)*(n:ℝ)^2*
        (ComputedPhaseGeometry.innerDimension n call AlignedCertificate.S:ℝ)^
          (ThinProductCosts.highQueryExponent RealCertificate.theta) := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hpow
        (show 0 ≤ (ComputedPhaseGeometry.blockCount n:ℝ)*(n:ℝ)^2 by positivity)
    _ = (ComputedPhaseGeometry.blockCount n:ℝ)*ReductionCosts.rawTerm RealCertificate.c
        RealCertificate.theta n (PhaseGeometry.outerSize call AlignedCertificate.S n)
        (ComputedPhaseGeometry.innerDimension n call AlignedCertificate.S)
        (call.cyclic AlignedCertificate.S) 2 := by simp [ReductionCosts.rawTerm, mul_assoc]
    _ ≤ _ := hsingle

theorem phaseRawSum_dominates_formation (n : ℕ)
    (call : ComputedPhaseGeometry.Call AlignedCertificate.R n) :
    (ComputedPhaseGeometry.blockCount n:ℝ)*(2*(call.cyclic AlignedCertificate.S:ℝ)*
      PhaseGeometry.outerSize call AlignedCertificate.S n*
      ComputedPhaseGeometry.innerDimension n call AlignedCertificate.S) ≤
        2*ComputedReductionCosts.phaseRawSum n call := by
  have hsingle := Finset.single_le_sum
    (s:=Finset.univ) (a:=(5:Fin 6)) (f:=fun i =>
      (ComputedPhaseGeometry.blockCount n:ℝ)*ReductionCosts.rawTerm RealCertificate.c
        RealCertificate.theta n (PhaseGeometry.outerSize call AlignedCertificate.S n)
        (ComputedPhaseGeometry.innerDimension n call AlignedCertificate.S)
        (call.cyclic AlignedCertificate.S) i)
    (fun i _ => mul_nonneg (Nat.cast_nonneg _) (ReductionCosts.rawTerm_nonneg _ _ _ _ _ _
      (Nat.cast_nonneg n) (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _) i))
    (Finset.mem_univ (5:Fin 6))
  have hscaled := mul_le_mul_of_nonneg_left hsingle (show (0:ℝ)≤2 by norm_num)
  change 2*((ComputedPhaseGeometry.blockCount n:ℝ)*
      ((call.cyclic AlignedCertificate.S:ℝ)*PhaseGeometry.outerSize call AlignedCertificate.S n*
        ComputedPhaseGeometry.innerDimension n call AlignedCertificate.S)) ≤
      2*ComputedReductionCosts.phaseRawSum n call at hscaled
  convert hscaled using 1
  ring


namespace BlockCosts
open StoredMinPlusAPSP FoldedBackendExecution ThinMatrixBackend
open BackendCostRefinement BackendNumeratorBounds ThinProductCosts
/-- Counter of the same retained block used by the physical producer. The
only remaining arithmetic premise is the numerical allowance on its concrete
bounded binary multiplier; original input and numerator widths are derived. -/
theorem history_blockCounter_le_raw (n : ℕ)
    (call : ComputedPhaseGeometry.Call AlignedCertificate.R n)
    (hv : EndToEndAPSP.ValidFactors call.factors)
    (X Y T : IntTable n)
    (b : Fin (CompactBlocks.blockCount n (ComputableParameters.block n)))
    (hm0 : 0 < ComputedPhaseGeometry.innerPower n call AlignedCertificate.S)
    (hgeometry : gridSide
      (ComputableParameters.ordinaryLength (ComputedPhaseGeometry.innerPower n call AlignedCertificate.S))
      (ComputedPhaseGeometry.innerPower n call AlignedCertificate.S) ≤
        PhaseGeometry.outerSize call AlignedCertificate.S n)
    (hband : (bandSourceBudget
      (ComputableParameters.ordinaryLength (ComputedPhaseGeometry.innerPower n call AlignedCertificate.S))
      (ComputedPhaseGeometry.innerPower n call AlignedCertificate.S)
      (call.cyclic AlignedCertificate.S) : ℝ) ≤
        (call.cyclic AlignedCertificate.S : ℝ) *
          ((4:ℝ)^(ComputedPhaseGeometry.innerPower n call AlignedCertificate.S))^
            (2*RealCertificate.T-RealCertificate.G))
    (hshape : ((prepareShape
      (ComputableParameters.ordinaryLength (ComputedPhaseGeometry.innerPower n call AlignedCertificate.S))
      (ComputedPhaseGeometry.innerPower n call AlignedCertificate.S)).operations : ℝ) ≤
        (call.cyclic AlignedCertificate.S : ℝ) *
          ((4:ℝ)^(ComputedPhaseGeometry.innerPower n call AlignedCertificate.S))^
            (2*RealCertificate.T-RealCertificate.G))
    (allowance : ℝ) (hallowance : 1 ≤ allowance)
    (hfull : (BinaryMultiplierAdapter.workBound (call.cyclic AlignedCertificate.S)
      (AdaptiveBitBounds.highInputBudget
        (ComputableParameters.ordinaryLength (ComputedPhaseGeometry.innerPower n call AlignedCertificate.S))
        (ComputedPhaseGeometry.innerPower n call AlignedCertificate.S) 1) : ℝ) ≤
      (call.cyclic AlignedCertificate.S : ℝ)*allowance) :
    let f := EndToEndAPSP.historyFactorization AlignedCertificate.S call.factors hv
    let h := ComputableParameters.block n
    let d := physicalFold f
    let shape := AlignedAPSP.shape h d
    let m := ComputedPhaseGeometry.innerPower n call AlignedCertificate.S
    let L := ComputableParameters.ordinaryLength m
    ((prepareRetained f shape (AlignedAPSP.multiplier h d f.cyclic) X Y T).blockCounter b : ℝ) ≤
      3*allowance*backendLocalFactor (PhaseGeometry.outerSize call AlignedCertificate.S n) L m
        (numeratorBitBudget L m (call.cyclic AlignedCertificate.S) 1) *
      ∑ i : Fin 6, ReductionCosts.rawTerm RealCertificate.c RealCertificate.theta n
        (PhaseGeometry.outerSize call AlignedCertificate.S n) ((4:ℝ)^m)
        (call.cyclic AlignedCertificate.S) i := by
  let f := EndToEndAPSP.historyFactorization AlignedCertificate.S call.factors hv
  let h := ComputableParameters.block n
  let d := physicalFold f
  let shape := AlignedAPSP.shape h d
  let m := middleExponent h d
  let L := shape.L
  let q := f.cyclic
  let M := AlignedAPSP.multiplier h d q
  let left := formLeft f b X
  let right := formRight f b Y
  let μ := BinaryMultiplierAdapter.workBound q (AdaptiveBitBounds.highInputBudget L m 1)
  have hm : m = ComputedPhaseGeometry.innerPower n call AlignedCertificate.S := rfl
  have hL : shape.L = ComputableParameters.ordinaryLength m := rfl
  have hmActual : middleExponent h d = ComputedPhaseGeometry.innerPower n call AlignedCertificate.S := rfl
  have hLActual : L = ComputableParameters.ordinaryLength (ComputedPhaseGeometry.innerPower n call AlignedCertificate.S) := rfl
  have hq : q = call.cyclic AlignedCertificate.S := rfl
  have hN : outerSize n (physicalFold f) = PhaseGeometry.outerSize call AlignedCertificate.S n := rfl
  have hμ : (μ:ℝ) ≤ (q:ℝ)*allowance := by
    dsimp only [μ, L]
    rw [hL, hm, hq]
    exact hfull
  have hleft : ∀ i r, |(left.get i).get r| ≤ (1:ℤ) := by
    intro i r
    have hh : (((left.get i).get r).natAbs : ℤ) ≤ 1 := by
      exact_mod_cast formLeft_abs f b X i r
    simpa only [Int.natCast_natAbs] using hh
  have hright : ∀ i r, |(right.get i).get r| ≤ (1:ℤ) := by
    intro i r
    have hh : (((right.get i).get r).natAbs : ℤ) ≤ 1 := by
      exact_mod_cast formRight_abs f b Y i r
    simpa only [Int.natCast_natAbs] using hh
  have hD : middleSize h d ≤ 4^m := (middleSize_eq h d).le
  have hmul : GlobalMultiplierBudget M
      (prepareGlobal (L:=L) (m:=m) (t:=shape.t) M left right) μ := by
    exact AdaptiveBitBounds.actual_binary_globalMultiplierBudget (L:=L) (m:=m) (t:=shape.t)
      left right (by decide) hleft hright
  have hsize : ∀ i : Fin (windowQuerySize n),
      (globalNumerator (tileWidth_pos L m shape.hm)
        (prepareGlobal (L:=L) (m:=m) (t:=shape.t) M left right)
          ((requests f T).get i).row ((requests f T).get i).column
          ((requests f T).get i).coefficient).natAbs.size ≤
            numeratorBitBudget L m q 1 := by
    intro i
    exact globalNumerator_size_le M shape.hm shape.ht hD left right 1 hleft hright
      ((requests f T).get i).row ((requests f T).get i).column ((requests f T).get i).coefficient
  have hQ : windowQuerySize n ≤ 3*n^2 := by
    unfold windowQuerySize
    nlinarith
  have he := executeRequests_le_raw M left right (requests f T) shape.hm shape.ht
    n 3 (by decide) hQ hm0 (AlignedAPSP.shape_length h d) (AlignedAPSP.shape_cutoff h d)
    hgeometry μ (numeratorBitBudget L m q 1) 1 hmul hsize hband hshape allowance
    (by linarith) (by simpa only [Nat.cast_one] using hallowance)
    (by simpa only [Nat.mul_one] using hμ)
  have hcounter : (prepareRetained f shape M X Y T).blockCounter b =
      (executeRequests (t:=shape.t) (tileWidth_pos L m shape.hm) M left right (requests f T)).operations := by
    rw [prepareRetained_blockCounter]
    simp only [executeRequests, Vector.get_ofFn]
    rfl
  change ((prepareRetained f shape M X Y T).blockCounter b : ℝ) ≤ _
  rw [hcounter]
  simpa only [Nat.mul_one, Nat.cast_ofNat, hN, hL, hm, hmActual, hLActual, hq] using he

end BlockCosts


namespace ControllerCosts
open CountedEndToEndAPSP EndToEndAPSP StoredMinPlusAPSP AsymptoticCosts
def referenceControllerBudget (n h P depth stages : ℕ) : ℕ :=
  stages*(depth*CountedArrayComposite.batchVisits P (incidenceSize n h)+
    CountedArrayComposite.finalVisits P (incidenceSize n h))+
    P+6*incidenceSize n h+9*n^2

def controllerInflation (depth : ℕ) : ℕ := 256*(depth+1)*(depth+2)

def controllerBudget (n h P depth stages : ℕ) : ℕ :=
  controllerInflation depth*referenceControllerBudget n h P depth stages+1

theorem referenceControllerBudget_factor (n h P depth stages R : ℕ)
    (hinc : n^2 ≤ incidenceSize n h) (hdepth : depth ≤ R) :
    referenceControllerBudget n h P depth stages ≤
      (stages*(8*R+11)+16)*(P+1)*(incidenceSize n h+1) := by
  let I := incidenceSize n h
  let X := (P+1)*(I+1)
  have hb : CountedArrayComposite.batchVisits P I ≤ 8*X := by
    unfold CountedArrayComposite.batchVisits
    dsimp [X]
    nlinarith
  have hf : CountedArrayComposite.finalVisits P I ≤ 11*X := by
    unfold CountedArrayComposite.finalVisits
    dsimp [X]
    nlinarith
  have hc : depth*CountedArrayComposite.batchVisits P I+CountedArrayComposite.finalVisits P I ≤
      (8*R+11)*X := by
    calc
      _ ≤ depth*(8*X)+11*X := Nat.add_le_add (Nat.mul_le_mul_left _ hb) hf
      _ ≤ R*(8*X)+11*X := Nat.add_le_add_right (Nat.mul_le_mul_right _ hdepth) _
      _ = _ := by ring
  have he : P+6*I+9*n^2 ≤ 16*X := by dsimp [X]; nlinarith
  unfold referenceControllerBudget
  change stages*(depth*CountedArrayComposite.batchVisits P I+CountedArrayComposite.finalVisits P I)+P+6*I+9*n^2 ≤ _
  calc
    _ ≤ stages*((8*R+11)*X)+16*X := by
      have h := Nat.mul_le_mul_left stages hc
      nlinarith
    _ = _ := by dsimp [X,I]; ring

theorem stages_le_log (n : ℕ) (hn : 3 ≤ n) :
    ((2*n).size:ℝ) ≤ (2+1/Real.log 2)*Real.log (n:ℝ) := by
  have hne : Nat.bit false n ≠ 0 := by simp [Nat.bit]; omega
  have he : (2*n).size = n.size+1 := by
    simpa [Nat.bit, Nat.two_mul] using Nat.size_bit hne
  rw [he]
  exact BackendCostRefinement.size_add_one_le_log n hn

def referenceControllerConstant (R : ℕ) : ℝ :=
  7*8193*((2+1/Real.log 2)*(8*(R:ℝ)+11)+16)

theorem computed_referenceControllerBudget_le (R depth n : ℕ) (hn : 3 ≤ n) (hdepth : depth ≤ R) :
    (referenceControllerBudget n (ComputableParameters.block n) (ComputableParameters.computedPool n).card
      depth (2*n).size:ℝ) ≤
      referenceControllerConstant R*(Real.log (n:ℝ))^5*(n:ℝ)^(3-(b-eta)) := by
  let P := (ComputableParameters.computedPool n).card
  let I := incidenceSize n (ComputableParameters.block n)
  let logn := Real.log (n:ℝ)
  let Cs : ℝ := 2+1/Real.log 2
  have hl : 1 ≤ logn := PhaseGeometry.one_le_log_nat n hn
  have hl0 : 0 ≤ logn := by linarith
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast (show 1≤n by omega)
  have hnpos : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have heta := stageRelations.1
  have hb : b ≤ 1 := by norm_num [b,AlignedCertificate.b]
  have hspos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hCs : 0 ≤ Cs := by dsimp [Cs]; positivity
  have hbp := TilingCosts.bandCount_pos n (ComputableParameters.block n)
    (by omega) (ComputedPhaseGeometry.block_pos n)
  have hblocks : 1 ≤ ComputedPhaseGeometry.blockCount n := by
    simpa only [ComputedPhaseGeometry.blockCount,TilingCosts.bandCount] using Nat.succ_le_of_lt hbp
  have hIeq : I = 3*ComputedPhaseGeometry.queryCount n := by
    dsimp [I,incidenceSize,CompactBlocks.blockCount,ComputedPhaseGeometry.queryCount,ComputedPhaseGeometry.blockCount]
    ring
  have hinc : n^2 ≤ I := by
    rw [hIeq]
    unfold ComputedPhaseGeometry.queryCount
    nlinarith
  have hfinite := referenceControllerBudget_factor n (ComputableParameters.block n) P depth (2*n).size R hinc hdepth
  have hfiniteR : (referenceControllerBudget n (ComputableParameters.block n) P depth (2*n).size:ℝ) ≤
      (((2*n).size:ℝ)*(8*(R:ℝ)+11)+16)*((P:ℝ)+1)*((I:ℝ)+1) := by exact_mod_cast hfinite
  have hpool := ComputedPhaseGeometry.actual_pool_count n hn
  have hnpow : 1 ≤ (n:ℝ)^eta := Real.one_le_rpow hn1 heta
  have hbase : 1 ≤ logn^4*(n:ℝ)^eta := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hl) hnpow
  have hP : (P:ℝ)+1 ≤ 8193*logn^4*(n:ℝ)^eta := by
    change (P:ℝ) ≤ 8192*logn^4*(n:ℝ)^eta at hpool
    nlinarith
  have hquery := ComputedPhaseGeometry.queryCount_upper n (by omega)
  have hI : (I:ℝ)+1 ≤ 7*(n:ℝ)^(3-b) := by
    have hI' : (I:ℝ) ≤ 6*(n:ℝ)^(3-b) := by
      have hcast : (I:ℝ)=3*(ComputedPhaseGeometry.queryCount n:ℝ) := by exact_mod_cast hIeq
      nlinarith
    have hpow : 1 ≤ (n:ℝ)^(3-b) := Real.one_le_rpow hn1 (by linarith)
    linarith
  have hstages := stages_le_log n hn
  have hround : ((2*n).size:ℝ)*(8*(R:ℝ)+11)+16 ≤
      (Cs*(8*(R:ℝ)+11)+16)*logn := by
    have hm := mul_le_mul_of_nonneg_right hstages (show 0 ≤ 8*(R:ℝ)+11 by positivity)
    change ((2*n).size:ℝ) ≤ Cs*logn at hstages
    nlinarith
  calc
    _ ≤ (((2*n).size:ℝ)*(8*(R:ℝ)+11)+16)*((P:ℝ)+1)*((I:ℝ)+1) := hfiniteR
    _ ≤ ((Cs*(8*(R:ℝ)+11)+16)*logn)*(8193*logn^4*(n:ℝ)^eta)*(7*(n:ℝ)^(3-b)) := by gcongr
    _ = referenceControllerConstant R*logn^5*(n:ℝ)^(3-(b-eta)) := by
      rw [show 3-(b-eta)=eta+(3-b) by ring, Real.rpow_add hnpos]
      dsimp [referenceControllerConstant,Cs]
      ring



def controllerConstant (R : ℕ) : ℝ :=
  ((controllerInflation R:ℝ)+1)*referenceControllerConstant R


theorem computed_controllerBudget_le (R depth n : ℕ) (hn : 3 ≤ n) (hdepth : depth ≤ R) :
    (controllerBudget n (ComputableParameters.block n) (ComputableParameters.computedPool n).card
      depth (2*n).size:ℝ) ≤
      controllerConstant R*(Real.log (n:ℝ))^5*(n:ℝ)^(3-(b-eta)) := by
  have hInflation : controllerInflation depth ≤ controllerInflation R :=
    Nat.mul_le_mul (Nat.mul_le_mul_left 256 (Nat.add_le_add_right hdepth 1)) (Nat.add_le_add_right hdepth 2)
  have hfinite : controllerBudget n (ComputableParameters.block n) (ComputableParameters.computedPool n).card
      depth (2*n).size ≤
      controllerInflation R*referenceControllerBudget n (ComputableParameters.block n)
        (ComputableParameters.computedPool n).card depth (2*n).size+1 :=
    Nat.add_le_add_right (Nat.mul_le_mul_right _ hInflation) 1
  have hfiniteR : (controllerBudget n (ComputableParameters.block n) (ComputableParameters.computedPool n).card
      depth (2*n).size:ℝ) ≤
      (controllerInflation R:ℝ)*(referenceControllerBudget n (ComputableParameters.block n)
        (ComputableParameters.computedPool n).card depth (2*n).size:ℝ)+1 := by exact_mod_cast hfinite
  have href := computed_referenceControllerBudget_le R depth n hn hdepth
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hCs : 0 ≤ 2+1/Real.log 2 := add_nonneg (by norm_num) (one_div_pos.mpr htwo).le
  have hC : 1 ≤ referenceControllerConstant R := by
    unfold referenceControllerConstant
    have h : 0 ≤ (2+1/Real.log 2)*(8*(R:ℝ)+11) := mul_nonneg hCs (by positivity)
    nlinarith
  have hl : 1 ≤ (Real.log (n:ℝ))^5 := one_le_pow₀ (PhaseGeometry.one_le_log_nat n hn)
  have heta := stageRelations.1
  have hb : b ≤ 1 := by norm_num [b,AlignedCertificate.b]
  have hp : 1 ≤ (n:ℝ)^(3-(b-eta)) :=
    Real.one_le_rpow (by exact_mod_cast (show 1≤n by omega)) (by linarith)
  have hbound : 1 ≤ referenceControllerConstant R*(Real.log (n:ℝ))^5*(n:ℝ)^(3-(b-eta)) :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hC hl) hp
  calc
    _ ≤ (controllerInflation R:ℝ)*(referenceControllerBudget n (ComputableParameters.block n)
        (ComputableParameters.computedPool n).card depth (2*n).size:ℝ)+1 := hfiniteR
    _ ≤ (controllerInflation R:ℝ)*(referenceControllerConstant R*(Real.log (n:ℝ))^5*(n:ℝ)^(3-(b-eta)))+1 :=
      add_le_add (mul_le_mul_of_nonneg_left href (Nat.cast_nonneg _)) (le_refl 1)
    _ ≤ ((controllerInflation R:ℝ)+1)*(referenceControllerConstant R*(Real.log (n:ℝ))^5*(n:ℝ)^(3-(b-eta))) := by nlinarith only [hbound]
    _ = _ := by unfold controllerConstant; ring

theorem charged_solve_resources_of_controller_bound {n h U : ℕ} {Payload : Type}
    (hh : 0 < h) (hhn : h ≤ n) (backend : Backend n h Payload)
    (parameters : CompleteAPSP.Parameters h U) (hs : (2*n).size ≤ parameters.stages)
    (A B T : IntTable n)
    (hmag : ∀ i k, k ∈ (flatInstance (h := h) A B T).block i →
      ((flatInstance (h := h) A B T).value i k).natAbs ≤ U)
    (hcontroller : (solve backend parameters A B T).resources.controllerVisits ≤
      controllerInflation parameters.k*(parameters.stages*
        (parameters.k*CountedArrayComposite.batchVisits parameters.pool.card (incidenceSize n h)+
          CountedArrayComposite.finalVisits parameters.pool.card (incidenceSize n h)))+1) :
    let out := chargeCapScan (solve backend parameters A B T)
    out.resources.total+(n*n+out.resources.denseAnswerWrites+out.resources.finalScatterWrites) ≤
      out.resources.backendWork+controllerBudget n h parameters.pool.card parameters.k parameters.stages := by
  let M := controllerInflation parameters.k
  let C := parameters.stages*(parameters.k*CountedArrayComposite.batchVisits parameters.pool.card (incidenceSize n h)+
    CountedArrayComposite.finalVisits parameters.pool.card (incidenceSize n h))
  let E := parameters.pool.card+6*incidenceSize n h+9*n^2
  have hM : 1 ≤ M := by
    have hpos : 0 < 256*(parameters.k+1)*(parameters.k+2) := by positivity
    exact Nat.succ_le_of_lt hpos
  have hE : E ≤ M*E := Nat.le_mul_of_pos_left _ hM
  have hscan := solve_scan_budget hh hhn backend parameters hs A B T hmag
  have hfinal := solve_final_visits backend parameters A B T
  have hdense := solve_denseAnswerWrites backend parameters A B T
  have hscatter := solve_scatter_budget hh hhn backend parameters hs A B T hmag
  have hsetup : (solve backend parameters A B T).resources.setupVisits =
      parameters.pool.card+3*incidenceSize n h+n*n := by
    rw [solve_setupVisits_value]
    rfl
  dsimp only [chargeCapScan, ResourceParts.total]
  have hbudget : controllerBudget n h parameters.pool.card parameters.k parameters.stages = M*(C+E)+1 := by
    dsimp [controllerBudget,referenceControllerBudget,M,C,E]
    ring
  rw [hbudget]
  change (solve backend parameters A B T).resources.controllerVisits ≤ M*C+1 at hcontroller
  have hrest : (solve backend parameters A B T).resources.originalSumTests+
      (solve backend parameters A B T).resources.finalVisits+
      ((solve backend parameters A B T).resources.setupVisits+3*n*n)+
      (n*n+(solve backend parameters A B T).resources.denseAnswerWrites+
        (solve backend parameters A B T).resources.finalScatterWrites) ≤ E := by
    dsimp [E]
    nlinarith only [hscan,hfinal,hdense,hscatter,hsetup]
  nlinarith only [hcontroller,hrest,hE]



theorem charged_solve_resources_le {n h U : ℕ} {Payload : Type}
    (hh : 0 < h) (hhn : h ≤ n) (backend : Backend n h Payload)
    (parameters : CompleteAPSP.Parameters h U) (hs : (2*n).size ≤ parameters.stages)
    (A B T : IntTable n)
    (hmag : ∀ i k, k ∈ (flatInstance (h := h) A B T).block i →
      ((flatInstance (h := h) A B T).value i k).natAbs ≤ U) :
    let out := chargeCapScan (solve backend parameters A B T)
    out.resources.total+(n*n+out.resources.denseAnswerWrites+out.resources.finalScatterWrites) ≤
      out.resources.backendWork+controllerBudget n h parameters.pool.card parameters.k parameters.stages := by
  exact charged_solve_resources_of_controller_bound hh hhn backend parameters hs A B T hmag
    (solve_controllerVisits backend parameters A B T)

theorem callback_resources_le {n h U : ℕ} {Payload : Type}
    (hh : 0 < h) (hhn : h ≤ n) (backend : Backend n h Payload)
    (parameters : CompleteAPSP.Parameters h U) (hs : (2*n).size ≤ parameters.stages)
    (A B T : IntTable n) (hcap : entryQueryBound A B T ≤ U) :
    let out := chargeCapScan (solve backend (parameters.weaken hcap) A B T)
    (callback backend parameters A B T).work+(callback backend parameters A B T).answerWrites ≤
      out.resources.backendWork+controllerBudget n h parameters.pool.card parameters.k parameters.stages := by
  have h := charged_solve_resources_le hh hhn backend (parameters.weaken hcap) hs A B T
    (fun i k _ => entryQueryBound_flat A B T i k)
  simpa only [callback,dif_pos hcap,CompleteAPSP.Parameters.weaken] using h

theorem computed_callback_resources_le {n U : ℕ} {Payload : Type}
    (hn : 3 ≤ n) (backend : Backend n (ComputableParameters.block n) Payload)
    (parameters : CompleteAPSP.Parameters (ComputableParameters.block n) U)
    (hp : ComputableParameters.program n U = some parameters)
    (A B T : IntTable n) (hcap : entryQueryBound A B T ≤ U) :
    let out := chargeCapScan (solve backend (parameters.weaken hcap) A B T)
    (((callback backend parameters A B T).work+(callback backend parameters A B T).answerWrites:ℕ):ℝ) ≤
      (out.resources.backendWork:ℝ)+controllerConstant AlignedCertificate.R*
        (Real.log (n:ℝ))^5*(n:ℝ)^(3-(b-eta)) := by
  rcases ComputableParameters.program_sound n U parameters hp with ⟨hpool,hP,hlam,hk,hM,hstages⟩
  have hdepth : parameters.k ≤ AlignedCertificate.R := by
    rw [hk]
    norm_num [ComputableParameters.factorCount,AlignedCertificate.R]
  have hs : (2*n).size ≤ parameters.stages := hstages.ge
  have hf := callback_resources_le (ComputedPhaseGeometry.block_pos n)
    (ComputableParameters.block_le_n n (by omega)) backend parameters hs A B T hcap
  have hfR : (((callback backend parameters A B T).work+(callback backend parameters A B T).answerWrites:ℕ):ℝ) ≤
      ((chargeCapScan (solve backend (parameters.weaken hcap) A B T)).resources.backendWork:ℝ)+
        (controllerBudget n (ComputableParameters.block n) parameters.pool.card parameters.k parameters.stages:ℝ) := by
    exact_mod_cast hf
  have hc := computed_controllerBudget_le AlignedCertificate.R parameters.k n hn hdepth
  rw [← hpool,← hstages] at hc
  exact hfR.trans (add_le_add (le_refl _) hc)

end ControllerCosts


namespace GuardCosts
open PhaseGeometry ReductionCosts ComputedReductionCosts
def guardConstant (R : ℕ) : ℕ := 32*(R+1)^3+8*R+1

theorem guard_work_product (R S : ℕ) (factors : List ℕ)
    (hv : EndToEndAPSP.ValidFactors factors) (hlen : factors.length ≤ R) :
    (FactorValidation.validate factors).2+(FactorValidation.splitProducts S factors).2 ≤
      guardConstant R*factors.prod := by
  have hp : 1 ≤ factors.prod := Nat.succ_le_of_lt
    (FactorValidation.positive_product factors (FactorValidation.valid_factor_positive factors hv))
  have hval : (FactorValidation.validate factors).2 ≤ 32*(R+1)^3*factors.prod :=
    (FactorValidation.validate_work_product factors hv).trans
      (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega : factors.length+1≤R+1) 3)))
  have hsplit : (FactorValidation.splitProducts S factors).2 ≤ (8*R+1)*factors.prod := by
    rw [FactorValidation.splitProducts_work]
    exact (show 8*factors.length+1≤8*R+1 by omega).trans (Nat.le_mul_of_pos_right _ hp)
  unfold guardConstant
  have h := Nat.add_le_add hval hsplit
  nlinarith only [h]

theorem computed_folded_le_inner (R S n : ℕ) (call : ComputedPhaseGeometry.Call R n) :
    call.folded S ≤ ComputedPhaseGeometry.innerDimension n call S := by
  have hb : 1 ≤ ComputableParameters.block n := Nat.succ_le_of_lt (ComputedPhaseGeometry.block_pos n)
  have h : call.folded S ≤ ComputableParameters.block n*(3*call.folded S) := by nlinarith
  have hpad := PhaseGeometry.pad4_lower (ComputableParameters.block n*(3*call.folded S))
  exact h.trans hpad

theorem guard_price_le_phaseRawSum (n : ℕ) (hn : 3 ≤ n)
    (call : ComputedPhaseGeometry.Call AlignedCertificate.R n)
    (hv : EndToEndAPSP.ValidFactors call.factors) :
    (((FactorValidation.validate call.factors).2+
      (FactorValidation.splitProducts AlignedCertificate.S call.factors).2:ℕ):ℝ) ≤
      (guardConstant AlignedCertificate.R:ℝ)*phaseRawSum n call := by
  let S := AlignedCertificate.S
  let N := outerSize call S n
  let D := ComputedPhaseGeometry.innerDimension n call S
  let q := call.cyclic S
  let B := ComputedPhaseGeometry.blockCount n
  have hprod : call.factors.prod = call.folded S*call.cyclic S := by
    exact (List.prod_take_mul_prod_drop call.factors S).symm
  have hfold := computed_folded_le_inner AlignedCertificate.R S n call
  have hqD : call.factors.prod ≤ q*D := by
    rw [hprod]
    simpa only [q,D,Nat.mul_comm] using Nat.mul_le_mul_right (call.cyclic S) hfold
  have hN : 1 ≤ N := Nat.succ_le_of_lt (ComputedPhaseGeometry.actual_outer_pos AlignedCertificate.R S n hn call)
  have hB : 1 ≤ B := by
    have h := TilingCosts.bandCount_pos n (ComputableParameters.block n)
      (by omega) (ComputedPhaseGeometry.block_pos n)
    simpa only [B,ComputedPhaseGeometry.blockCount,TilingCosts.bandCount] using Nat.succ_le_of_lt h
  have hbig : q*D ≤ B*q*N*D := by
    calc
      _ ≤ (q*D)*N := Nat.le_mul_of_pos_right _ hN
      _ ≤ ((q*D)*N)*B := Nat.le_mul_of_pos_right _ hB
      _ = _ := by ring
  have hguard := (guard_work_product AlignedCertificate.R S call.factors hv call.length_le).trans
    (Nat.mul_le_mul_left _ (hqD.trans hbig))
  have hnonneg (i : Fin 6) : 0 ≤ (B:ℝ)*rawTerm RealCertificate.c RealCertificate.theta n N D q i :=
    mul_nonneg (Nat.cast_nonneg B) (rawTerm_nonneg _ _ _ _ _ _
      (Nat.cast_nonneg n) (Nat.cast_nonneg N) (Nat.cast_nonneg D) (Nat.cast_nonneg q) i)
  have hterm : (B:ℝ)*rawTerm RealCertificate.c RealCertificate.theta n N D q 5 ≤ phaseRawSum n call :=
    Finset.single_le_sum (fun i _ => hnonneg i) (Finset.mem_univ (5:Fin 6))
  calc
    _ ≤ (guardConstant AlignedCertificate.R:ℝ)*(B:ℝ)*q*N*D := by
      have hg : (FactorValidation.validate call.factors).2+
          (FactorValidation.splitProducts AlignedCertificate.S call.factors).2 ≤
          guardConstant AlignedCertificate.R*B*q*N*D := by
        simpa only [S,Nat.mul_assoc] using hguard
      exact_mod_cast hg
    _ = (guardConstant AlignedCertificate.R:ℝ)*((B:ℝ)*rawTerm RealCertificate.c RealCertificate.theta n N D q 5) := by
      change (guardConstant AlignedCertificate.R:ℝ)*(B:ℝ)*q*N*D =
        (guardConstant AlignedCertificate.R:ℝ)*((B:ℝ)*((q:ℝ)*N*D))
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hterm (Nat.cast_nonneg _)

end GuardCosts



/-- Fixed guard and mask-formation factors for one actual valid table call. -/
def tableCoefficient (producerCoefficient : ℝ) : ℝ :=
  producerCoefficient+3+(GuardCosts.guardConstant AlignedCertificate.R:ℝ)

theorem tableCoefficient_nonneg (producerCoefficient : ℝ) (h : 0 ≤ producerCoefficient) :
    0 ≤ tableCoefficient producerCoefficient := by unfold tableCoefficient; positivity

/-- Pointwise composition of the literal valid-history branch. This finite
lemma is later instantiated with the proved uniform physical-producer bound. -/
theorem valid_table_work_le {n : ℕ} (hn : 3 ≤ n)
    (call : ComputedPhaseGeometry.Call AlignedCertificate.R n)
    (hv : EndToEndAPSP.ValidFactors call.factors)
    (X Y T : StoredMinPlusAPSP.IntTable n) (selected : List ℕ) (candidate : ℕ)
    (hfac : call.factors=selected++[candidate])
    (active : ArrayCompositeAlgorithm.Flags
      (EndToEndAPSP.incidenceSize n (ComputableParameters.block n)))
    (Cprod : ℝ)
    (hprod : ((AlignedAPSP.physicalProducer (h:=ComputableParameters.block n)
      (EndToEndAPSP.historyFactorization AlignedCertificate.S call.factors hv) X Y T).work:ℝ) ≤
      binaryAllowance n*Cprod*(Real.log (n:ℝ))^13*ComputedReductionCosts.phaseRawSum n call) :
    ((AlignedAPSP.table (h:=ComputableParameters.block n) X Y T selected candidate active).work:ℝ) ≤
      binaryAllowance n*tableCoefficient Cprod*(Real.log (n:ℝ))^13*
        ComputedReductionCosts.phaseRawSum n call := by
  rcases call with ⟨factors,hlen,hvalid⟩
  change factors=selected++[candidate] at hfac
  subst factors
  let call : ComputedPhaseGeometry.Call AlignedCertificate.R n := ⟨selected++[candidate],hlen,hvalid⟩
  have he := AlignedAPSP.valid_table_retains_producer_work X Y T selected candidate active hv
  have hp : (FoldedBackendExecution.Payload.work
      (AlignedAPSP.physicalProducer (h:=ComputableParameters.block n)
        (EndToEndAPSP.historyFactorization AlignedCertificate.S call.factors hv) X Y T).payload:ℝ) ≤
      binaryAllowance n*Cprod*(Real.log (n:ℝ))^13*ComputedReductionCosts.phaseRawSum n call := by
    simpa only [AlignedAPSP.physicalProducer,FoldedBackendExecution.produce_work] using hprod
  have hi : (EndToEndAPSP.incidenceSize n (ComputableParameters.block n):ℝ) ≤
      3*ComputedReductionCosts.phaseRawSum n call := by
    rw [Geometry.history_incidenceSize, Nat.cast_mul, Nat.cast_ofNat]
    exact mul_le_mul_of_nonneg_left (phaseRawSum_dominates_queries n call) (by norm_num)
  have hg := GuardCosts.guard_price_le_phaseRawSum n hn call hv
  push_cast at hg
  have hF : (1:ℝ) ≤ binaryAllowance n*(Real.log (n:ℝ))^13 :=
    one_le_mul_of_one_le_of_one_le (binaryAllowance_ge_one n hn)
      (one_le_pow₀ (PhaseGeometry.one_le_log_nat n hn))
  have hs := phaseRawSum_nonneg n call
  have hextra : (3+(GuardCosts.guardConstant AlignedCertificate.R:ℝ))*
      ComputedReductionCosts.phaseRawSum n call ≤
      (binaryAllowance n*(Real.log (n:ℝ))^13)*
        ((3+(GuardCosts.guardConstant AlignedCertificate.R:ℝ))*
          ComputedReductionCosts.phaseRawSum n call) := by
    exact le_mul_of_one_le_left (by positivity) hF
  rw [he]
  push_cast
  calc
    _ ≤ binaryAllowance n*Cprod*(Real.log (n:ℝ))^13*ComputedReductionCosts.phaseRawSum n call+
        3*ComputedReductionCosts.phaseRawSum n call+
        (GuardCosts.guardConstant AlignedCertificate.R:ℝ)*ComputedReductionCosts.phaseRawSum n call :=
      add_le_add (add_le_add hp hi) hg
    _ ≤ binaryAllowance n*Cprod*(Real.log (n:ℝ))^13*ComputedReductionCosts.phaseRawSum n call+
        (binaryAllowance n*(Real.log (n:ℝ))^13)*
          ((3+(GuardCosts.guardConstant AlignedCertificate.R:ℝ))*ComputedReductionCosts.phaseRawSum n call) := by
      nlinarith only [hextra]
    _ = _ := by unfold tableCoefficient; ring


namespace ProducerCosts
open StoredMinPlusAPSP FoldedBackendExecution ThinMatrixBackend
open BackendCostRefinement BackendNumeratorBounds ThinProductCosts
def producerCoefficient : ℝ :=
  3*backendCoefficientConstant AlignedCertificate.R
    (AlignedAPSPCosts.Numerator.numeratorBitsConstant AlignedCertificate.R)+302

/-- The full counter returned by the same physical producer, including all
sources and all three signed windows, obeys one uniform eventual bound. -/
theorem eventual_physicalProducer_work_le :
    ∀ᶠ n : ℕ in Filter.atTop,
      ∀ call : ComputedPhaseGeometry.Call AlignedCertificate.R n,
      ∀ hv : EndToEndAPSP.ValidFactors call.factors, ∀ X Y T : IntTable n,
      let f := EndToEndAPSP.historyFactorization AlignedCertificate.S call.factors hv
      ((AlignedAPSP.physicalProducer (h:=ComputableParameters.block n) f X Y T).work : ℝ) ≤
        AlignedAPSPCosts.binaryAllowance n *
          producerCoefficient *
          (Real.log (n:ℝ))^13 * ComputedReductionCosts.phaseRawSum n call := by
  filter_upwards [computed_source_budgets_fit AlignedCertificate.R AlignedCertificate.S,
    ComputedPhaseGeometry.actual_innerPower_uniformly_large AlignedCertificate.R 1,
    ComputedPhaseGeometry.all_computed_candidate_tiles_fit,
    Filter.eventually_ge_atTop (3:ℕ)] with n hsource hlarge hgrid hn
  intro call hv X Y T
  let f := EndToEndAPSP.historyFactorization AlignedCertificate.S call.factors hv
  let h := ComputableParameters.block n
  let m := ComputedPhaseGeometry.innerPower n call AlignedCertificate.S
  let L := ComputableParameters.ordinaryLength m
  let q := call.cyclic AlignedCertificate.S
  let N := PhaseGeometry.outerSize call AlignedCertificate.S n
  let bits := numeratorBitBudget L m q 1
  let CB := backendCoefficientConstant AlignedCertificate.R
    (AlignedAPSPCosts.Numerator.numeratorBitsConstant AlignedCertificate.R)
  let ell := Real.log (n:ℝ)
  let A := AlignedAPSPCosts.binaryAllowance n
  let shape := AlignedAPSP.shape h (physicalFold f)
  let M := AlignedAPSP.multiplier h (physicalFold f) f.cyclic
  let payload := prepareRetained f shape M X Y T
  let B := CompactBlocks.blockCount n h
  let rawSum := ∑ i : Fin 6, ReductionCosts.rawTerm RealCertificate.c RealCertificate.theta
    n N ((4:ℝ)^m) q i
  have hL : L = Nat.ceil (RealCertificate.c*(m:ℝ)) := ComputableParameters.ordinaryLength_eq m
  have hq : 1 ≤ q := by
    change 1 ≤ f.cyclic
    exact f.cyclic_pos
  have hm0 : 0 < m := by
    have hm := hlarge call AlignedCertificate.S
    omega
  have hgeometry : gridSide L m ≤ N := by
    simpa only [gridSide, ←hL] using hgrid call
  have hbudgets := hsource call q hq
  change (bandSourceBudget (Nat.ceil (RealCertificate.c*(m:ℝ))) m q:ℝ) ≤
      (q:ℝ)*((4:ℝ)^m)^(2*RealCertificate.T-RealCertificate.G) ∧
    ((prepareShape (Nat.ceil (RealCertificate.c*(m:ℝ))) m).operations:ℝ) ≤
      (q:ℝ)*((4:ℝ)^m)^(2*RealCertificate.T-RealCertificate.G) at hbudgets
  rw [←hL] at hbudgets
  have hA : 1 ≤ A := AlignedAPSPCosts.binaryAllowance_ge_one n hn
  have hA0 : 0 ≤ A := le_trans (by norm_num) hA
  have hfull : (BinaryMultiplierAdapter.workBound q
      (AdaptiveBitBounds.highInputBudget L m 1):ℝ) ≤ (q:ℝ)*A := by
    rw [hL]
    exact AlignedAPSPCosts.computed_binary_work_le_allowance n hn call
  have hbits : (bits:ℝ) ≤ AlignedAPSPCosts.Numerator.numeratorBitsConstant AlignedCertificate.R*ell := by
    dsimp only [bits]
    rw [hL]
    exact AlignedAPSPCosts.Numerator.computed_numeratorBits_log_bound
        AlignedCertificate.R AlignedCertificate.S n hn call
  have hfactor : backendLocalFactor N L m bits ≤ CB*ell^13 := by
    rw [hL]
    exact computed_backendLocalFactor_le_polylog
      AlignedCertificate.R AlignedCertificate.S n bits hn call
      (AlignedAPSPCosts.Numerator.numeratorBitsConstant AlignedCertificate.R)
      (AlignedAPSPCosts.Numerator.numeratorBitsConstant_nonneg AlignedCertificate.R) hbits
  have hraw : 0 ≤ rawSum := by
    apply Finset.sum_nonneg
    intro i _
    exact ReductionCosts.rawTerm_nonneg _ _ _ _ _ _ (Nat.cast_nonneg n)
      (Nat.cast_nonneg N) (by positivity) (Nat.cast_nonneg q) i
  have hblock (b : Fin B) : (payload.blockCounter b:ℝ) ≤ 3*A*CB*ell^13*rawSum := by
    have hb := AlignedAPSPCosts.BlockCosts.history_blockCounter_le_raw n call hv X Y T b hm0 hgeometry
      hbudgets.1 hbudgets.2 A hA hfull
    calc
      _ ≤ 3*A*backendLocalFactor N L m bits*rawSum := hb
      _ ≤ 3*A*(CB*ell^13)*rawSum :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hfactor (by positivity)) hraw
      _ = _ := by ring
  have hphase : (B:ℝ)*rawSum = ComputedReductionCosts.phaseRawSum n call := by
    unfold ComputedReductionCosts.phaseRawSum
    rw [←Finset.mul_sum]
    simp only [ComputedPhaseGeometry.innerDimension, ComputedPhaseGeometry.innerPower,
      Nat.cast_pow, Nat.cast_ofNat]
    rfl
  have hsum : ((∑ b : Fin B, payload.blockCounter b):ℝ) ≤
      3*A*CB*ell^13*ComputedReductionCosts.phaseRawSum n call := by
    calc
      _ = ∑ b : Fin B, (payload.blockCounter b:ℝ) := by rfl
      _ ≤ ∑ _b : Fin B, 3*A*CB*ell^13*rawSum := Finset.sum_le_sum (fun b _ => hblock b)
      _ = 3*A*CB*ell^13*((B:ℝ)*rawSum) := by simp; ring
      _ = _ := by rw [hphase]
  have hquery : (queryFormationSites n h:ℝ) ≤ 300*ComputedReductionCosts.phaseRawSum n call := by
    have he : queryFormationSites n h = 300*ComputedPhaseGeometry.queryCount n := by
      unfold queryFormationSites EndToEndAPSP.incidenceSize ComputedPhaseGeometry.queryCount
      change 100*(n*n*(B*3)) = 300*(n^2*B)
      ring
    rw [he]
    push_cast
    exact mul_le_mul_of_nonneg_left (phaseRawSum_dominates_queries n call) (by norm_num)
  have hformation : (B:ℝ)*(formationSites n h f:ℝ) ≤
      2*ComputedReductionCosts.phaseRawSum n call := by
    have he : formationSites n h f = 2*q*N*ComputedPhaseGeometry.innerDimension n call AlignedCertificate.S := rfl
    rw [he]
    push_cast
    exact phaseRawSum_dominates_formation n call
  have hwork : ((AlignedAPSP.physicalProducer (h:=h) f X Y T).work:ℝ) =
      (queryFormationSites n h:ℝ)+(B:ℝ)*(formationSites n h f:ℝ)+
        ((∑ b : Fin B, payload.blockCounter b):ℝ) := by
    change (payload.work:ℝ) = _
    rw [Retained.work_reindex]
    push_cast
    rfl
  have hell : 1 ≤ ell := PhaseGeometry.one_le_log_nat n hn
  have hprice : 1 ≤ A*ell^13 := one_le_mul_of_one_le_of_one_le hA (one_le_pow₀ hell)
  have hpaid : 302*ComputedReductionCosts.phaseRawSum n call ≤
      A*302*ell^13*ComputedReductionCosts.phaseRawSum n call := by
    have hp := mul_le_mul_of_nonneg_right hprice
      (show 0 ≤ 302*ComputedReductionCosts.phaseRawSum n call by
        exact mul_nonneg (by norm_num) (phaseRawSum_nonneg n call))
    nlinarith only [hp]
  change ((AlignedAPSP.physicalProducer (h:=h) f X Y T).work:ℝ) ≤
    A*(3*CB+302)*ell^13*ComputedReductionCosts.phaseRawSum n call
  rw [hwork]
  calc
    _ ≤ 302*ComputedReductionCosts.phaseRawSum n call+
        3*A*CB*ell^13*ComputedReductionCosts.phaseRawSum n call := by linarith
    _ ≤ A*302*ell^13*ComputedReductionCosts.phaseRawSum n call+
        3*A*CB*ell^13*ComputedReductionCosts.phaseRawSum n call := add_le_add hpaid le_rfl
    _ = _ := by ring

theorem producerCoefficient_nonneg : 0 ≤ producerCoefficient := by
  have h := backendCoefficientConstant_nonneg AlignedCertificate.R
    (Numerator.numeratorBitsConstant AlignedCertificate.R)
  unfold producerCoefficient
  positivity
end ProducerCosts


namespace AggregationCosts
open ComputedReductionCosts CountedEndToEndAPSP EndToEndAPSP StoredMinPlusAPSP
theorem workSum_eq_fin_sum {I : ℕ} {Payload : Type*}
    (calls : List (CountedArrayComposite.Call I Payload)) :
    CountedArrayComposite.workSum calls = ∑ i : Fin calls.length, (calls.get i).result.work := by
  unfold CountedArrayComposite.workSum
  conv_lhs => rw [← List.ofFn_get calls]
  simp only [List.map_ofFn,List.sum_ofFn,Function.comp_apply]

def roundConstant : ℝ := (AlignedCertificate.R:ℝ)*(2+1/Real.log 2)

def backendBatchConstant (CB : ℝ) : ℝ :=
  roundConstant*binaryAllowanceConstant*CB*ledgerConstant

def backendBatchLog : ℕ := 1+11+13+ledgerLogDegree

theorem solve_backend_le_chargedCost {n U : ℕ} (hn : 3 ≤ n)
    (parameters : CompleteAPSP.Parameters (ComputableParameters.block n) U)
    (hp : ComputableParameters.program n U = some parameters)
    (A B T : IntTable n) (hcap : entryQueryBound A B T ≤ U)
    (CB : ℝ) (hCB : 0 ≤ CB)
    (hpointwise : ∀ phase : ComputedPhaseGeometry.Call AlignedCertificate.R n,
      EndToEndAPSP.ValidFactors phase.factors → ∀ (selected : List ℕ) (candidate : ℕ),
      phase.factors = selected++[candidate] →
      ∀ active : ArrayCompositeAlgorithm.Flags (incidenceSize n (ComputableParameters.block n)),
      ((AlignedAPSP.table A B T selected candidate active).work:ℝ) ≤
        binaryAllowance n*CB*(Real.log (n:ℝ))^13*phaseRawSum n phase) :
    let out := CountedEndToEndAPSP.solve
      (AlignedAPSP.backend n (ComputableParameters.block n) (EndToEndAPSP.block_pos n))
      (parameters.weaken hcap) A B T
    (out.resources.backendWork:ℝ) ≤ backendBatchConstant CB*ArithmeticSlack.chargedCost backendBatchLog n := by
  let backend := AlignedAPSP.backend n (ComputableParameters.block n) (EndToEndAPSP.block_pos n)
  let p := parameters.weaken hcap
  let out := CountedEndToEndAPSP.solve backend p A B T
  let calls := out.calls
  have hparams := ComputableParameters.program_sound n U parameters hp
  have hpool : p.pool = ComputableParameters.computedPool n := hparams.1
  have hkR : p.k+1 = AlignedCertificate.R := by
    change parameters.k+1 = _
    rw [hparams.2.2.2.1]
    norm_num [ComputableParameters.factorCount,AlignedCertificate.R]
  have hstages : p.stages = (2*n).size := hparams.2.2.2.2.2
  have hthree : ∀ q ∈ p.pool, q ≠ 3 := by
    intro q hq
    rw [hpool] at hq
    exact fun heq => (Finset.mem_sdiff.mp hq).2 (by simp only [heq,Finset.mem_singleton])
  have hlen (i : Fin calls.length) :
      ((calls.get i).factors.selected++[(calls.get i).factors.candidate]).length ≤ AlignedCertificate.R := by
    have h := CountedEndToEndAPSP.solve_factors_length backend p A B T (calls.get i) (List.get_mem calls i)
    simpa only [List.length_append,List.length_singleton,hkR] using h
  have hmem (i : Fin calls.length) :
      ∀ q ∈ (calls.get i).factors.selected++[(calls.get i).factors.candidate], q ∈ ComputableParameters.computedPool n := by
    intro q hq
    rw [← hpool]
    exact CountedEndToEndAPSP.solve_factor_membership backend p A B T (calls.get i) (List.get_mem calls i) q hq
  let phases : Fin calls.length → ComputedPhaseGeometry.Call AlignedCertificate.R n := fun i =>
    ComputedPhaseGeometry.phaseCallOfPool AlignedCertificate.R n
      ((calls.get i).factors.selected++[(calls.get i).factors.candidate]) (hlen i) (hmem i)
  let cost : Fin calls.length → ℕ := fun i => (calls.get i).result.work
  let rounds := p.stages*AlignedCertificate.R
  have hcount : calls.length ≤ rounds*(ComputableParameters.computedPool n).card := by
    have h := CountedEndToEndAPSP.solve_calls_bound backend p A B T
    simpa only [hkR,hpool] using h
  have hcost (i : Fin calls.length) : (cost i:ℝ) ≤
      binaryAllowance n*CB*(Real.log (n:ℝ))^13*phaseRawSum n (phases i) := by
    have hvalid := CountedEndToEndAPSP.solve_valid_histories backend p A B T hthree (calls.get i) (List.get_mem calls i)
    have hresult := CountedEndToEndAPSP.solve_provenance backend p A B T (calls.get i) (List.get_mem calls i)
    change (calls.get i).result = AlignedAPSP.table A B T
      (calls.get i).factors.selected (calls.get i).factors.candidate (calls.get i).factors.active at hresult
    have h := hpointwise (phases i) hvalid (calls.get i).factors.selected (calls.get i).factors.candidate rfl (calls.get i).factors.active
    rw [← hresult] at h
    exact h
  have hA : 0 ≤ binaryAllowance n := le_trans (by norm_num) (binaryAllowance_ge_one n hn)
  have hCbit := binaryAllowanceConstant_pos.le
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hCround : 0 ≤ roundConstant :=
    mul_nonneg (Nat.cast_nonneg AlignedCertificate.R)
      (add_nonneg (by norm_num) (one_div_pos.mpr htwo).le)
  have hextra : (0:ℝ) ≤ (ArithmeticSlack.extra:ℝ) := by
    norm_num [ArithmeticSlack.extra,ArithmeticSlack.epsilon,AlignedCertificate.v,AlignedCertificate.eta,
      AlignedCertificate.b,AlignedCertificate.R,AlignedCertificate.S]
  have hnpow : 1 ≤ (n:ℝ)^(ArithmeticSlack.extra:ℝ) :=
    Real.one_le_rpow (by exact_mod_cast (show 1≤n by omega)) hextra
  have harithmetic : binaryAllowance n ≤
      binaryAllowanceConstant*(Real.log (n:ℝ))^11*(n:ℝ)^(ArithmeticSlack.extra:ℝ) := by
    exact le_mul_of_one_le_right hA hnpow
  have hrounds : (rounds:ℝ) ≤ roundConstant*(Real.log (n:ℝ))^1 := by
    have hs := ControllerCosts.stages_le_log n hn
    have h := mul_le_mul_of_nonneg_right hs (Nat.cast_nonneg AlignedCertificate.R)
    simpa only [rounds,Nat.cast_mul,hstages,roundConstant,pow_one,mul_assoc,mul_left_comm,mul_comm] using h
  have hbatch := callCost_batch_le_chargedCost_pool phases cost hn rounds hcount
    (binaryAllowance n) CB binaryAllowanceConstant roundConstant 13 11 1
    hA hCB hCbit hCround hcost harithmetic hrounds
  have heq : out.resources.backendWork = ∑ i : Fin calls.length, cost i := by
    rw [CountedEndToEndAPSP.solve_backendWork]
    exact workSum_eq_fin_sum calls
  change (out.resources.backendWork:ℝ) ≤ _
  rw [heq]
  exact hbatch

end AggregationCosts



def actualTableCoefficient : ℝ := tableCoefficient ProducerCosts.producerCoefficient

theorem actualTableCoefficient_nonneg : 0 ≤ actualTableCoefficient :=
  tableCoefficient_nonneg _ ProducerCosts.producerCoefficient_nonneg

/-- Uniform counter bound for the exact validated, split, masked producer
used by the aligned oracle. Every arithmetic and width budget is discharged. -/
theorem eventual_valid_table_work_le :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ call : ComputedPhaseGeometry.Call AlignedCertificate.R n,
      ∀ _hv : EndToEndAPSP.ValidFactors call.factors,
      ∀ X Y T : StoredMinPlusAPSP.IntTable n, ∀ (selected : List ℕ) (candidate : ℕ),
      call.factors=selected++[candidate] →
      ∀ active : ArrayCompositeAlgorithm.Flags
        (EndToEndAPSP.incidenceSize n (ComputableParameters.block n)),
      ((AlignedAPSP.table X Y T selected candidate active).work:ℝ) ≤
        binaryAllowance n*actualTableCoefficient*(Real.log (n:ℝ))^13*
          ComputedReductionCosts.phaseRawSum n call := by
  filter_upwards [ProducerCosts.eventual_physicalProducer_work_le,
    Filter.eventually_ge_atTop (3:ℕ)] with n hprod hn
  intro call hv X Y T selected candidate hfac active
  exact valid_table_work_le hn call hv X Y T selected candidate hfac active
    ProducerCosts.producerCoefficient (hprod call hv X Y T)

theorem backendBatchConstant_nonneg :
    0 ≤ AggregationCosts.backendBatchConstant actualTableCoefficient := by
  have hC := actualTableCoefficient_nonneg
  have hB := binaryAllowanceConstant_pos.le
  have hL := ComputedReductionCosts.ledgerConstant_nonneg
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hround : 0 ≤ AggregationCosts.roundConstant := by
    unfold AggregationCosts.roundConstant
    exact mul_nonneg (Nat.cast_nonneg _)
      (add_nonneg (by norm_num) (one_div_nonneg.mpr htwo.le))
  exact mul_nonneg (mul_nonneg (mul_nonneg hround hB) hC) hL

/-- The actual retained backend-work field, summed in its original call
order, satisfies the certified phase ledger without any oracle-time premise. -/
theorem eventual_solve_backendWork_le :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ (U : ℕ)
      (parameters : CompleteAPSP.Parameters (ComputableParameters.block n) U),
      ComputableParameters.program n U=some parameters →
      ∀ X Y T : StoredMinPlusAPSP.IntTable n,
      ∀ hcap : CountedEndToEndAPSP.entryQueryBound X Y T ≤ U,
      let out := CountedEndToEndAPSP.solve
        (AlignedAPSP.backend n (ComputableParameters.block n) (EndToEndAPSP.block_pos n))
        (parameters.weaken hcap) X Y T
      (out.resources.backendWork:ℝ) ≤
        AggregationCosts.backendBatchConstant actualTableCoefficient*
          ArithmeticSlack.chargedCost AggregationCosts.backendBatchLog n := by
  filter_upwards [eventual_valid_table_work_le,Filter.eventually_ge_atTop (3:ℕ)] with n htable hn
  intro U parameters hp X Y T hcap
  exact AggregationCosts.solve_backend_le_chargedCost hn parameters hp X Y T hcap
    actualTableCoefficient actualTableCoefficient_nonneg
    (fun phase hv selected candidate hfac active => htable phase hv X Y T selected candidate hfac active)



def callbackLogDegree : ℕ := AggregationCosts.backendBatchLog+5

def callbackCoefficient : ℝ := AggregationCosts.backendBatchConstant actualTableCoefficient+
  ControllerCosts.controllerConstant AlignedCertificate.R

theorem controllerCoefficient_nonneg :
    0 ≤ ControllerCosts.controllerConstant AlignedCertificate.R := by
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold ControllerCosts.controllerConstant ControllerCosts.referenceControllerConstant
  positivity

theorem callbackCoefficient_nonneg : 0 ≤ callbackCoefficient :=
  add_nonneg backendBatchConstant_nonneg controllerCoefficient_nonneg

/-- Complete actual callback resource bound. The executed dense controller,
its retained literal binary-cyclic producer returns, original-sum checks,
cap scan and output writes are all charged. No oracle-time hypothesis remains. -/
theorem eventual_callback_resources_le :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ (U : ℕ)
      (parameters : CompleteAPSP.Parameters (ComputableParameters.block n) U),
      ComputableParameters.program n U=some parameters →
      ∀ X Y T : StoredMinPlusAPSP.IntTable n,
      CountedEndToEndAPSP.entryQueryBound X Y T ≤ U →
      let backend := AlignedAPSP.backend n (ComputableParameters.block n) (EndToEndAPSP.block_pos n)
      ((CountedEndToEndAPSP.callback backend parameters X Y T).work:ℝ)+
        (CountedEndToEndAPSP.callback backend parameters X Y T).answerWrites ≤
          callbackCoefficient*ArithmeticSlack.chargedCost callbackLogDegree n := by
  filter_upwards [eventual_solve_backendWork_le,Filter.eventually_ge_atTop (3:ℕ)] with n hbackend hn
  intro U parameters hp X Y T hcap
  let backend := AlignedAPSP.backend n (ComputableParameters.block n) (EndToEndAPSP.block_pos n)
  have hb := hbackend U parameters hp X Y T hcap
  have hc := ControllerCosts.computed_callback_resources_le hn backend parameters hp X Y T hcap
  have hb' : ((CountedEndToEndAPSP.chargeCapScan
      (CountedEndToEndAPSP.solve backend (parameters.weaken hcap) X Y T)).resources.backendWork:ℝ) ≤
      AggregationCosts.backendBatchConstant actualTableCoefficient*
        ArithmeticSlack.chargedCost AggregationCosts.backendBatchLog n := hb
  have hbook : (Real.log (n:ℝ))^5*(n:ℝ)^(3-(AsymptoticCosts.b-AsymptoticCosts.eta)) ≤
      ArithmeticSlack.chargedCost 5 n := by
    calc
      _ ≤ (Real.log (n:ℝ))^5*((n:ℝ)^2+(n:ℝ)^(3-(AsymptoticCosts.b-AsymptoticCosts.eta))) :=
        mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (sq_nonneg _))
          (pow_nonneg (by linarith [PhaseGeometry.one_le_log_nat n hn]) _)
      _ ≤ _ := ReductionCosts.bookScan_le_chargedCost n 5 hn
  have hbm := mul_le_mul_of_nonneg_left
    (ReductionCosts.chargedCost_mono n AggregationCosts.backendBatchLog callbackLogDegree hn
      (by unfold callbackLogDegree; omega)) backendBatchConstant_nonneg
  have hcm := mul_le_mul_of_nonneg_left
    (hbook.trans (ReductionCosts.chargedCost_mono n 5 callbackLogDegree hn
      (by unfold callbackLogDegree; omega))) controllerCoefficient_nonneg
  have hc' : ((CountedEndToEndAPSP.callback backend parameters X Y T).work:ℝ)+
      (CountedEndToEndAPSP.callback backend parameters X Y T).answerWrites ≤
      ((CountedEndToEndAPSP.chargeCapScan
        (CountedEndToEndAPSP.solve backend (parameters.weaken hcap) X Y T)).resources.backendWork:ℝ)+
      ControllerCosts.controllerConstant AlignedCertificate.R*(Real.log (n:ℝ))^5*
        (n:ℝ)^(3-(AsymptoticCosts.b-AsymptoticCosts.eta)) := by
    exact_mod_cast hc
  change _ ≤ callbackCoefficient*ArithmeticSlack.chargedCost callbackLogDegree n
  unfold callbackCoefficient
  nlinarith only [hc',hb',hbm,hcm]


end
end ThinMatrix.AlignedAPSPCosts

#print axioms ThinMatrix.AlignedAPSPCosts.Numerator.computed_numeratorBits_log_bound
#print axioms ThinMatrix.AlignedAPSPCosts.Geometry.all_history_candidate_tiles_fit
#print axioms ThinMatrix.AlignedAPSPCosts.computed_binary_work_le_allowance

#print axioms ThinMatrix.AlignedAPSPCosts.Provenance.run_successful_physical_trace

#print axioms ThinMatrix.AlignedAPSPCosts.phaseRawSum_dominates_queries

#print axioms ThinMatrix.AlignedAPSPCosts.BlockCosts.history_blockCounter_le_raw

#print axioms ThinMatrix.AlignedAPSPCosts.ControllerCosts.computed_callback_resources_le

#print axioms ThinMatrix.AlignedAPSPCosts.GuardCosts.guard_price_le_phaseRawSum

#print axioms ThinMatrix.AlignedAPSPCosts.valid_table_work_le

#print axioms ThinMatrix.AlignedAPSPCosts.ProducerCosts.eventual_physicalProducer_work_le

#print axioms ThinMatrix.AlignedAPSPCosts.AggregationCosts.solve_backend_le_chargedCost

#print axioms ThinMatrix.AlignedAPSPCosts.eventual_valid_table_work_le
#print axioms ThinMatrix.AlignedAPSPCosts.eventual_solve_backendWork_le

#print axioms ThinMatrix.AlignedAPSPCosts.eventual_callback_resources_le
