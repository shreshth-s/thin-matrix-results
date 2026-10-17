import CompactBlocks
import StoredMinPlusAPSP

/-!
# Compact composite counting as a stored APSP callback

Each callback decodes the stored integer inputs, invokes the compact all-pairs
program once, and retains that same returned composite payload. The Boolean
vector is reshaped once into the stored reduction's table format. Reads do not
restart the composite solver or scan a finite answer set.

`work` here records only the already returned controller bookkeeping and
original-sum tests. Backend preparations, complete source formation, cyclic
arithmetic and their bit costs require the separate backend cost composition;
this module neither assumes nor claims a numerical fast running-time bound.
-/

namespace ThinMatrix.CompactStoredAPSP

abbrev Payload (n h : ℕ) := CompositeAlgorithm.Result
  (CompleteAPSP.Incidence (Fin n) (Fin n) (Fin (CompactBlocks.blockCount n h)))
  (Fin n × Fin n)

def callback {n h : ℕ}
    (backend : CompleteAPSP.ProductBackend (Fin n) (Fin h) (Fin n))
    (plan : CompactBlocks.PhysicalPlan) (policy : CompleteAPSP.ParameterPolicy h) :
    StoredMinPlusAPSP.DenseOracle n (Payload n h) :=
  fun A B T =>
    let out := CompactBlocks.denseOracle backend plan policy
      (StoredMinPlusAPSP.decode A) (StoredMinPlusAPSP.decode B) (StoredMinPlusAPSP.decode T)
    { answers := StoredMinPlusAPSP.store (fun i j => DenseAnswers.read out.1 (i,j))
      payload := out.2
      work := out.2.bookkeeping+out.2.originalSumTests
      answerWrites := out.1.2+n*n }

theorem callback_correct {n h : ℕ} (hh : 0 < h)
    (backend : CompleteAPSP.ProductBackend (Fin n) (Fin h) (Fin n))
    (plan : CompactBlocks.PhysicalPlan) (policy : CompleteAPSP.ParameterPolicy h) :
    StoredMinPlusAPSP.DenseOracleCorrect (callback backend plan policy) := by
  intro A B T i j
  simpa only [callback, StoredMinPlusAPSP.decode_store] using
    CompactBlocks.denseOracle_correct hh backend plan policy
      (StoredMinPlusAPSP.decode A) (StoredMinPlusAPSP.decode B) (StoredMinPlusAPSP.decode T) i j

theorem callback_payload {n h : ℕ}
    (backend : CompleteAPSP.ProductBackend (Fin n) (Fin h) (Fin n))
    (plan : CompactBlocks.PhysicalPlan) (policy : CompleteAPSP.ParameterPolicy h)
    (A B T : StoredMinPlusAPSP.IntTable n) :
    (callback backend plan policy A B T).payload =
      (CompactBlocks.denseOracle backend plan policy
        (StoredMinPlusAPSP.decode A) (StoredMinPlusAPSP.decode B) (StoredMinPlusAPSP.decode T)).2 := rfl

theorem callback_controller_work {n h : ℕ}
    (backend : CompleteAPSP.ProductBackend (Fin n) (Fin h) (Fin n))
    (plan : CompactBlocks.PhysicalPlan) (policy : CompleteAPSP.ParameterPolicy h)
    (A B T : StoredMinPlusAPSP.IntTable n) :
    (callback backend plan policy A B T).work =
      (callback backend plan policy A B T).payload.bookkeeping+
      (callback backend plan policy A B T).payload.originalSumTests := rfl

/-- The extra n² writes are the actual flat-to-nested table conversion. -/
theorem callback_answer_writes {n h : ℕ}
    (backend : CompleteAPSP.ProductBackend (Fin n) (Fin h) (Fin n))
    (plan : CompactBlocks.PhysicalPlan) (policy : CompleteAPSP.ParameterPolicy h)
    (A B T : StoredMinPlusAPSP.IntTable n) :
    (callback backend plan policy A B T).answerWrites ≤ 3*n*n := by
  have hw := CompactBlocks.denseOracle_writes backend plan policy
    (StoredMinPlusAPSP.decode A) (StoredMinPlusAPSP.decode B) (StoredMinPlusAPSP.decode T)
  change (CompactBlocks.denseOracle backend plan policy
    (StoredMinPlusAPSP.decode A) (StoredMinPlusAPSP.decode B) (StoredMinPlusAPSP.decode T)).1.2+n*n ≤ _
  nlinarith

def apsp {n h : ℕ}
    (backend : CompleteAPSP.ProductBackend (Fin n) (Fin h) (Fin n))
    (plan : CompactBlocks.PhysicalPlan) (policy : CompleteAPSP.ParameterPolicy h)
    (w : StoredMinPlusAPSP.OptionalTable n) (W : ℕ) :
    StoredMinPlusAPSP.Execution n (Option ℤ) (Payload n h) :=
  StoredMinPlusAPSP.apsp (callback backend plan policy) w W

theorem apsp_correct {n h : ℕ} (hh : 0 < h)
    (backend : CompleteAPSP.ProductBackend (Fin n) (Fin h) (Fin n))
    (plan : CompactBlocks.PhysicalPlan) (policy : CompleteAPSP.ParameterPolicy h)
    (w : StoredMinPlusAPSP.OptionalTable n) (W : ℕ)
    (hw : APSPReduction.EdgeBound (StoredMinPlusAPSP.decode w) W)
    (hno : APSPReduction.NoNegativeCycles (StoredMinPlusAPSP.decode w)) :
    APSPReduction.IsAPSP (StoredMinPlusAPSP.decode w)
      (StoredMinPlusAPSP.decode (apsp backend plan policy w W).value) :=
  StoredMinPlusAPSP.apsp_correct (callback backend plan policy)
    (callback_correct hh backend plan policy) w W hw hno

def boundedAPSP {n h : ℕ}
    (backend : CompleteAPSP.ProductBackend (Fin n) (Fin h) (Fin n))
    (plan : CompactBlocks.PhysicalPlan) (w : StoredMinPlusAPSP.OptionalTable n) (W : ℕ)
    (parameters : CompleteAPSP.Parameters h (192*n*W+40)) :
    StoredMinPlusAPSP.Execution n (Option ℤ) (Payload n h) :=
  apsp backend plan (CompleteAPSP.boundedPolicy parameters) w W

theorem boundedAPSP_correct {n h : ℕ} (hh : 0 < h)
    (backend : CompleteAPSP.ProductBackend (Fin n) (Fin h) (Fin n))
    (plan : CompactBlocks.PhysicalPlan) (w : StoredMinPlusAPSP.OptionalTable n) (W : ℕ)
    (parameters : CompleteAPSP.Parameters h (192*n*W+40))
    (hw : APSPReduction.EdgeBound (StoredMinPlusAPSP.decode w) W)
    (hno : APSPReduction.NoNegativeCycles (StoredMinPlusAPSP.decode w)) :
    APSPReduction.IsAPSP (StoredMinPlusAPSP.decode w)
      (StoredMinPlusAPSP.decode (boundedAPSP backend plan w W parameters).value) :=
  apsp_correct hh backend plan (CompleteAPSP.boundedPolicy parameters) w W hw hno

def inputMagnitude {n : ℕ} (h : ℕ) (A B T : StoredMinPlusAPSP.IntTable n) : ℕ :=
  CompleteAPSP.magnitude (CompleteAPSP.incidenceInstance (CompactBlocks.block n h)
    (StoredMinPlusAPSP.decode A) (StoredMinPlusAPSP.decode B) (StoredMinPlusAPSP.decode T))

/-- Logarithmically many restart stages suffice for an n² final scan. The
proof uses actual rounded block sizes, including the incomplete last block. -/
theorem scan_budget {n h stages : ℕ} (hhn : h ≤ n)
    (hs : (2*n).size ≤ stages) :
    h*n^2*CompactBlocks.blockCount n h ≤ 2^stages*n^2 := by
  have hb : h*CompactBlocks.blockCount n h ≤ n+h := by
    have hd := Nat.div_mul_le_self (n+h-1) h
    rw [CompactBlocks.blockCount, Nat.ceilDiv_eq_add_pred_div]
    have hd' : h*((n+h-1)/h) ≤ n+h-1 := by simpa only [Nat.mul_comm] using hd
    exact hd'.trans (Nat.sub_le _ _)
  have hp : 2*n ≤ 2^stages :=
    (Nat.lt_size_self (2*n)).le.trans (Nat.pow_le_pow_right (by decide) hs)
  calc
    h*n^2*CompactBlocks.blockCount n h = (h*CompactBlocks.blockCount n h)*n^2 := by ring
    _ ≤ (2*n)*n^2 := Nat.mul_le_mul_right _ (by omega)
    _ ≤ _ := Nat.mul_le_mul_right _ hp

/-- These are resources of the returned callback payload, not a separate
existence theorem about a good sequence. The supplied finite configuration
is retained below its magnitude cap; the correctness fallback is unused. -/
theorem callback_resources_below {n h U : ℕ} (hh : 0 < h) (hhn : h ≤ n)
    (backend : CompleteAPSP.ProductBackend (Fin n) (Fin h) (Fin n))
    (plan : CompactBlocks.PhysicalPlan) (parameters : CompleteAPSP.Parameters h U)
    (hs : (2*n).size ≤ parameters.stages)
    (A B T : StoredMinPlusAPSP.IntTable n) (hcap : inputMagnitude h A B T ≤ U) :
    let out := callback backend plan (CompleteAPSP.boundedPolicy parameters) A B T
    out.payload.calls.length ≤ parameters.stages*(parameters.k+1)*parameters.pool.card ∧
    CompositeAlgorithm.tableCells out.payload.calls ≤
      parameters.stages*(parameters.k+1)*parameters.pool.card*(n^2*CompactBlocks.blockCount n h) ∧
    CompleteAPSP.preparationCalls (CompactBlocks.blockCount n h) out.payload.calls ≤
      parameters.stages*(parameters.k+1)*parameters.pool.card*CompactBlocks.blockCount n h ∧
    out.payload.bookkeeping ≤
      16*parameters.stages*(parameters.k+1)*(parameters.pool.card+1)*(n^2*CompactBlocks.blockCount n h+1) ∧
    out.payload.originalSumTests ≤ n^2 ∧
    out.work ≤ 16*parameters.stages*(parameters.k+1)*(parameters.pool.card+1)*
      (n^2*CompactBlocks.blockCount n h+1)+n^2 ∧ out.answerWrites ≤ 3*n*n := by
  let params := CompleteAPSP.boundedPolicy parameters (inputMagnitude h A B T)
  rcases CompleteAPSP.boundedPolicy_below parameters hcap with ⟨hpool, hk, hlam, hM, hstages⟩
  change params.pool = parameters.pool at hpool
  change params.k = parameters.k at hk
  change params.stages = parameters.stages at hstages
  have hbudget : h*(CompleteAPSP.zeroIncidences
      (I := Fin n) (J := Fin n) (H := Fin (CompactBlocks.blockCount n h))).card ≤
      2^params.stages*n^2 := by
    rw [CompactBlocks.zero_incidence_card]
    rw [hstages]
    convert scan_budget hhn hs using 1; ring
  have hc := CompactBlocks.solve_correct_and_resources hh backend plan
    (StoredMinPlusAPSP.decode A) (StoredMinPlusAPSP.decode B) (StoredMinPlusAPSP.decode T) params
    (fun x v _ => CompleteAPSP.magnitude_bound
      (CompleteAPSP.incidenceInstance (CompactBlocks.block n h)
        (StoredMinPlusAPSP.decode A) (StoredMinPlusAPSP.decode B) (StoredMinPlusAPSP.decode T)) x v)
    Prod.fst CompleteAPSP.zeroIncidences (n^2) hbudget
  have hp := CompactBlocks.solve_preparations backend plan
    (StoredMinPlusAPSP.decode A) (StoredMinPlusAPSP.decode B) (StoredMinPlusAPSP.decode T) params
    Prod.fst CompleteAPSP.zeroIncidences
  have hcalls : (callback backend plan (CompleteAPSP.boundedPolicy parameters) A B T).payload.calls.length ≤
      parameters.stages*(parameters.k+1)*parameters.pool.card := by
    have hv := hc.2.1
    rw [hstages, hk, hpool] at hv
    simpa only [callback, CompactBlocks.denseOracle, params, inputMagnitude] using hv
  have hcells : CompositeAlgorithm.tableCells
      (callback backend plan (CompleteAPSP.boundedPolicy parameters) A B T).payload.calls ≤
      parameters.stages*(parameters.k+1)*parameters.pool.card*(n^2*CompactBlocks.blockCount n h) := by
    have hv := hc.2.2.1
    rw [hstages, hk, hpool] at hv
    simpa only [callback, CompactBlocks.denseOracle, params, inputMagnitude, CompactBlocks.zero_incidence_card] using hv
  have hpreps : CompleteAPSP.preparationCalls (CompactBlocks.blockCount n h)
      (callback backend plan (CompleteAPSP.boundedPolicy parameters) A B T).payload.calls ≤
      parameters.stages*(parameters.k+1)*parameters.pool.card*CompactBlocks.blockCount n h := by
    rw [hstages, hk, hpool] at hp
    simpa only [callback, CompactBlocks.denseOracle, params, inputMagnitude] using hp
  have hbook : (callback backend plan (CompleteAPSP.boundedPolicy parameters) A B T).payload.bookkeeping ≤
      16*parameters.stages*(parameters.k+1)*(parameters.pool.card+1)*(n^2*CompactBlocks.blockCount n h+1) := by
    have hv := hc.2.2.2.1
    rw [hstages, hk, hpool] at hv
    simpa only [callback, CompactBlocks.denseOracle, params, inputMagnitude, CompactBlocks.zero_incidence_card] using hv
  have hscan : (callback backend plan (CompleteAPSP.boundedPolicy parameters) A B T).payload.originalSumTests ≤ n^2 := by
    exact hc.2.2.2.2
  refine ⟨hcalls, hcells, hpreps, hbook, hscan, ?_, callback_answer_writes _ _ _ _ _ _⟩
  rw [callback_controller_work]
  exact Nat.add_le_add hbook hscan

/-- The cap applies to the inputs of actual recorded callback invocations.
The joint execution list is read here; no callback or trace is executed again. -/
theorem actual_call_magnitude {n h : ℕ} (hh : 0 < h)
    (backend : CompleteAPSP.ProductBackend (Fin n) (Fin h) (Fin n))
    (plan : CompactBlocks.PhysicalPlan) (policy : CompleteAPSP.ParameterPolicy h)
    (w : StoredMinPlusAPSP.OptionalTable n) (W : ℕ)
    (hw : APSPReduction.EdgeBound (StoredMinPlusAPSP.decode w) W)
    (c : StoredMinPlusAPSP.Call n (Payload n h))
    (hc : c ∈ (apsp backend plan policy w W).calls) :
    inputMagnitude h c.left c.right c.target ≤ 192*n*W+40 := by
  unfold inputMagnitude CompleteAPSP.magnitude
  apply Finset.sup_le
  intro xv hx
  change (StoredMinPlusAPSP.decode c.left xv.1.1.1 xv.2+
    StoredMinPlusAPSP.decode c.right xv.2 xv.1.1.2+
    StoredMinPlusAPSP.decode c.target xv.1.1.1 xv.1.1.2-
    CompleteAPSP.windowValue xv.1.2.2).natAbs ≤ _
  have hr : -1 ≤ CompleteAPSP.windowValue xv.1.2.2 ∧ CompleteAPSP.windowValue xv.1.2.2 ≤ 1 := by
    have hv := xv.1.2.2.isLt
    unfold CompleteAPSP.windowValue
    omega
  exact StoredMinPlusAPSP.apsp_original_sum_bound (callback backend plan policy)
    (callback_correct hh backend plan policy) w W hw c hc xv.1.1.1 xv.1.1.2 xv.2
    (CompleteAPSP.windowValue xv.1.2.2) hr

theorem actual_calls_keep_parameters {n h : ℕ} (hh : 0 < h)
    (backend : CompleteAPSP.ProductBackend (Fin n) (Fin h) (Fin n))
    (plan : CompactBlocks.PhysicalPlan) (w : StoredMinPlusAPSP.OptionalTable n) (W : ℕ)
    (parameters : CompleteAPSP.Parameters h (192*n*W+40))
    (hw : APSPReduction.EdgeBound (StoredMinPlusAPSP.decode w) W)
    (c : StoredMinPlusAPSP.Call n (Payload n h))
    (hc : c ∈ (boundedAPSP backend plan w W parameters).calls) :
    let p := CompleteAPSP.boundedPolicy parameters (inputMagnitude h c.left c.right c.target)
    p.pool = parameters.pool ∧ p.k = parameters.k ∧ p.lam = parameters.lam ∧
      p.M = parameters.M ∧ p.stages = parameters.stages :=
  CompleteAPSP.boundedPolicy_below parameters
    (actual_call_magnitude hh backend plan (CompleteAPSP.boundedPolicy parameters) w W hw c hc)

def controllerBound {n h U : ℕ} (parameters : CompleteAPSP.Parameters h U) : ℕ :=
  16*parameters.stages*(parameters.k+1)*(parameters.pool.card+1)*
    (n^2*CompactBlocks.blockCount n h+1)+n^2

/-- A derived resource contract, rather than an assumed running-time bound.
Its work component is explicitly the controller component named above. -/
theorem controller_contract {n h : ℕ} (hh : 0 < h) (hhn : h ≤ n)
    (backend : CompleteAPSP.ProductBackend (Fin n) (Fin h) (Fin n))
    (plan : CompactBlocks.PhysicalPlan) (W : ℕ)
    (parameters : CompleteAPSP.Parameters h (192*n*W+40))
    (hs : (2*n).size ≤ parameters.stages) :
    StoredMinPlusAPSP.CostContract (callback backend plan (CompleteAPSP.boundedPolicy parameters))
      (64*n*W+13) (controllerBound (n := n) parameters) (3*n*n) := by
  constructor
  · intro A B T hb
    have hm := CompleteAPSP.triangle_magnitude_bound (CompactBlocks.block n h)
      (StoredMinPlusAPSP.decode A) (StoredMinPlusAPSP.decode B) (StoredMinPlusAPSP.decode T)
      (64*n*W+13)
      (fun i k => CompleteAPSP.natAbs_of_symmetric (hb.1 i k))
      (fun k j => CompleteAPSP.natAbs_of_symmetric (hb.2.1 k j))
      (fun i j => CompleteAPSP.natAbs_of_symmetric (hb.2.2 i j))
    change inputMagnitude h A B T ≤ 3*(64*n*W+13)+1 at hm
    have hcap : inputMagnitude h A B T ≤ 192*n*W+40 := by nlinarith
    exact (callback_resources_below hh hhn backend plan parameters hs A B T hcap).2.2.2.2.2.1
  · intro A B T _hb
    exact callback_answer_writes backend plan _ A B T

/-- Full stored-program correctness and its proved controller/array resource
bounds. This intentionally does not turn those components into a numerical
running-time claim for the matrix backend. -/
theorem boundedAPSP_correct_and_resources {n h : ℕ} (hh : 0 < h) (hhn : h ≤ n)
    (backend : CompleteAPSP.ProductBackend (Fin n) (Fin h) (Fin n))
    (plan : CompactBlocks.PhysicalPlan) (w : StoredMinPlusAPSP.OptionalTable n) (W degree : ℕ)
    (parameters : CompleteAPSP.Parameters h (192*n*W+40))
    (hs : (2*n).size ≤ parameters.stages)
    (hw : APSPReduction.EdgeBound (StoredMinPlusAPSP.decode w) W)
    (hno : APSPReduction.NoNegativeCycles (StoredMinPlusAPSP.decode w))
    (hn : 2 ≤ n) (hW : W ≤ n^degree) :
    let out := boundedAPSP backend plan w W parameters
    APSPReduction.IsAPSP (StoredMinPlusAPSP.decode w) (StoredMinPlusAPSP.decode out.value) ∧
    out.calls.length ≤ (n.log2+1)*(2*((degree+5)*(n.log2+1)+2)) ∧
    out.formationWrites ≤ (1+(n.log2+1)*(5*((degree+5)*(n.log2+1)+2)+7))*n^2 ∧
    out.oracleWork ≤ out.calls.length*controllerBound (n := n) parameters ∧
    out.answerWrites ≤ out.calls.length*(3*n*n) :=
  StoredMinPlusAPSP.apsp_correct_and_resources
    (callback backend plan (CompleteAPSP.boundedPolicy parameters))
    (callback_correct hh backend plan _) w W (controllerBound (n := n) parameters) (3*n*n) degree
    hw hno hn hW (controller_contract hh hhn backend plan W parameters hs)

#print axioms callback_correct
#print axioms callback_controller_work
#print axioms callback_answer_writes
#print axioms apsp_correct
#print axioms boundedAPSP_correct
#print axioms scan_budget
#print axioms callback_resources_below
#print axioms actual_call_magnitude
#print axioms actual_calls_keep_parameters
#print axioms controller_contract
#print axioms boundedAPSP_correct_and_resources

end ThinMatrix.CompactStoredAPSP
