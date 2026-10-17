import CompactStoredAPSP
import ComputableParameters
import ArrayCompositeAlgorithm

/-!
# Executable parameter selection and stored APSP

The finite parameter search is evaluated once before the stored APSP program.
Its successful branch keeps that same checked configuration throughout all
adaptive callbacks. Its unsuccessful branch performs direct integer triangle
scans; it does not select an unproved asymptotic cutoff or a large-prime oracle.

The generic successful branch below uses the concrete compact folded-count
program and the supplied, correct-by-construction product backend. The closed
`referenceRun` instantiates finite integer products and is a correctness
implementation. The controller resources proved here are not a running-time
claim for a fast thin-product implementation. The factor-aware array controller
and complete bit execution must be connected before such a claim is available.
-/

namespace ThinMatrix.EndToEndAPSP

open StoredMinPlusAPSP

def magnitudeCap (n W : ℕ) : ℕ := 192*n*W+40

abbrev Payload (n : ℕ) := Option (CompactStoredAPSP.Payload n (ComputableParameters.block n))

/-- Every middle label is visited, including those after the first witness.
The counter is returned by the same recursion as the Boolean answer. -/
def directScan {n : ℕ} (A B T : IntTable n) (i j : Fin n) :
    List (Fin n) → Bool × ℕ
  | [] => (false, 0)
  | k :: ks =>
    let rest := directScan A B T i j ks
    (decide (decode A i k+decode B k j+decode T i j=0) || rest.1, rest.2+1)

theorem directScan_correct {n : ℕ} (A B T : IntTable n) (i j : Fin n)
    (ks : List (Fin n)) :
    (directScan A B T i j ks).1 = true ↔
      ∃ k ∈ ks, decode A i k+decode B k j+decode T i j=0 := by
  induction ks with
  | nil => simp [directScan]
  | cons k ks ih => simp [directScan, ih]

theorem directScan_tests {n : ℕ} (A B T : IntTable n) (i j : Fin n)
    (ks : List (Fin n)) : (directScan A B T i j ks).2 = ks.length := by
  induction ks with
  | nil => rfl
  | cons k ks ih => simp [directScan, ih]

/-- The complete scan table is built once; both answers and counters read it.
`work` counts original-sum tests, rather than claiming a bit-time bound. -/
def directCallback (n : ℕ) : DenseOracle n (Payload n) :=
  fun A B T =>
    let scanned := store (fun i j => directScan A B T i j (List.finRange n))
    { answers := store (fun i j => (decode scanned i j).1)
      payload := none
      work := ∑ i : Fin n, ∑ j : Fin n, (decode scanned i j).2
      answerWrites := n*n }

theorem directCallback_correct (n : ℕ) : DenseOracleCorrect (directCallback n) := by
  intro A B T i j
  simpa only [directCallback, decode_store, List.mem_finRange, true_and] using
    directScan_correct A B T i j (List.finRange n)

theorem directCallback_tests (n : ℕ) (A B T : IntTable n) :
    (directCallback n A B T).work = n^3 := by
  simp [directCallback, directScan_tests, pow_succ, Nat.mul_assoc]

theorem directCallback_writes (n : ℕ) (A B T : IntTable n) :
    (directCallback n A B T).answerWrites = n*n := rfl

/-- Configuration is selected outside the input-matrix lambda. The successful
branch evaluates the compact callback once and retains that exact payload. -/
def oracleFromConfiguration {n : ℕ}
    (backend : CompleteAPSP.ProductBackend (Fin n) (Fin (ComputableParameters.block n)) (Fin n))
    (plan : CompactBlocks.PhysicalPlan) (W : ℕ)
    (configuration : Option (CompleteAPSP.Parameters (ComputableParameters.block n) (magnitudeCap n W))) :
    DenseOracle n (Payload n) :=
  match configuration with
  | none => directCallback n
  | some parameters =>
    let oracle := CompactStoredAPSP.callback backend plan (CompleteAPSP.boundedPolicy parameters)
    fun A B T =>
      let out := oracle A B T
      { answers := out.answers
        payload := some out.payload
        work := out.work
        answerWrites := out.answerWrites }

theorem block_pos (n : ℕ) : 0 < ComputableParameters.block n := by
  unfold ComputableParameters.block ComputableParameters.roundedPower
  omega

theorem oracleFromConfiguration_correct {n : ℕ}
    (backend : CompleteAPSP.ProductBackend (Fin n) (Fin (ComputableParameters.block n)) (Fin n))
    (plan : CompactBlocks.PhysicalPlan) (W : ℕ)
    (configuration : Option (CompleteAPSP.Parameters (ComputableParameters.block n) (magnitudeCap n W))) :
    DenseOracleCorrect (oracleFromConfiguration backend plan W configuration) := by
  cases configuration with
  | none => exact directCallback_correct n
  | some parameters =>
    exact CompactStoredAPSP.callback_correct (block_pos n) backend plan
      (CompleteAPSP.boundedPolicy parameters)

/-- One uniform executable program, including its finite-size fallback. -/
def run {n : ℕ}
    (backend : CompleteAPSP.ProductBackend (Fin n) (Fin (ComputableParameters.block n)) (Fin n))
    (plan : CompactBlocks.PhysicalPlan) (w : OptionalTable n) (W : ℕ) :
    Execution n (Option ℤ) (Payload n) :=
  let configuration := ComputableParameters.program n (magnitudeCap n W)
  let oracle := oracleFromConfiguration backend plan W configuration
  StoredMinPlusAPSP.apsp oracle w W

theorem run_correct {n : ℕ}
    (backend : CompleteAPSP.ProductBackend (Fin n) (Fin (ComputableParameters.block n)) (Fin n))
    (plan : CompactBlocks.PhysicalPlan) (w : OptionalTable n) (W : ℕ)
    (hw : APSPReduction.EdgeBound (decode w) W)
    (hno : APSPReduction.NoNegativeCycles (decode w)) :
    APSPReduction.IsAPSP (decode w) (decode (run backend plan w W).value) :=
  StoredMinPlusAPSP.apsp_correct _ (oracleFromConfiguration_correct backend plan W _) w W hw hno

/-- This closed correctness implementation uses actual finite integer sums.
It is explicitly a reference branch, without a fast running-time claim. -/
def referenceRun {n : ℕ} (w : OptionalTable n) (W : ℕ) :
    Execution n (Option ℤ) (Payload n) :=
  run CompleteAPSP.naiveBackend CompactBlocks.scalarPhysicalPlan w W

theorem referenceRun_correct {n : ℕ} (w : OptionalTable n) (W : ℕ)
    (hw : APSPReduction.EdgeBound (decode w) W)
    (hno : APSPReduction.NoNegativeCycles (decode w)) :
    APSPReduction.IsAPSP (decode w) (decode (referenceRun w W).value) :=
  run_correct _ _ w W hw hno

theorem success_configuration (n W : ℕ)
    (parameters : CompleteAPSP.Parameters (ComputableParameters.block n) (magnitudeCap n W))
    (hp : ComputableParameters.program n (magnitudeCap n W) = some parameters) :
    parameters.pool = ComputableParameters.computedPool n ∧
    parameters.P = ComputableParameters.scale n ∧
    parameters.lam = (magnitudeCap n W).size ∧
    parameters.k = ComputableParameters.factorCount-1 ∧
    parameters.M = ComputableParameters.reserve n ∧
    parameters.stages = (2*n).size :=
  ComputableParameters.program_sound n (magnitudeCap n W) parameters hp

/-- The oracle retained in an actual recorded call is the callback selected
before execution; this theorem inspects the returned list rather than replaying
the bit-scaling reduction or any modular product. -/
theorem calls_faithful {n : ℕ}
    (backend : CompleteAPSP.ProductBackend (Fin n) (Fin (ComputableParameters.block n)) (Fin n))
    (plan : CompactBlocks.PhysicalPlan) (w : OptionalTable n) (W : ℕ)
    (c : Call n (Payload n)) (hc : c ∈ (run backend plan w W).calls) :
    c.output = oracleFromConfiguration backend plan W
      (ComputableParameters.program n (magnitudeCap n W)) c.left c.right c.target :=
  StoredMinPlusAPSP.apsp_calls_faithful _ w W c hc

/-- Actual adaptive calls stay below the single precomputed cap, in either
branch of the parameter program. -/
theorem actual_call_magnitude {n : ℕ}
    (backend : CompleteAPSP.ProductBackend (Fin n) (Fin (ComputableParameters.block n)) (Fin n))
    (plan : CompactBlocks.PhysicalPlan) (w : OptionalTable n) (W : ℕ)
    (hw : APSPReduction.EdgeBound (decode w) W)
    (c : Call n (Payload n)) (hc : c ∈ (run backend plan w W).calls) :
    CompactStoredAPSP.inputMagnitude (ComputableParameters.block n) c.left c.right c.target ≤
      magnitudeCap n W := by
  have hb := StoredMinPlusAPSP.apsp_query_bound
    (oracleFromConfiguration backend plan W (ComputableParameters.program n (magnitudeCap n W)))
    (oracleFromConfiguration_correct backend plan W _) w W hw c hc
  have hm := CompleteAPSP.triangle_magnitude_bound
    (CompactBlocks.block n (ComputableParameters.block n))
    (decode c.left) (decode c.right) (decode c.target) (64*n*W+13)
    (fun i k => CompleteAPSP.natAbs_of_symmetric (hb.1 i k))
    (fun k j => CompleteAPSP.natAbs_of_symmetric (hb.2.1 k j))
    (fun i j => CompleteAPSP.natAbs_of_symmetric (hb.2.2 i j))
  change CompactStoredAPSP.inputMagnitude (ComputableParameters.block n)
    c.left c.right c.target ≤ 3*(64*n*W+13)+1 at hm
  unfold magnitudeCap
  nlinarith

/-- No large-prime fallback inside boundedPolicy is used by any actual call
after the outer parameter program succeeds. -/
theorem successful_calls_keep_parameters {n : ℕ}
    (backend : CompleteAPSP.ProductBackend (Fin n) (Fin (ComputableParameters.block n)) (Fin n))
    (plan : CompactBlocks.PhysicalPlan) (w : OptionalTable n) (W : ℕ)
    (parameters : CompleteAPSP.Parameters (ComputableParameters.block n) (magnitudeCap n W))
    (_hp : ComputableParameters.program n (magnitudeCap n W) = some parameters)
    (hw : APSPReduction.EdgeBound (decode w) W)
    (c : Call n (Payload n)) (hc : c ∈ (run backend plan w W).calls) :
    let p := CompleteAPSP.boundedPolicy parameters
      (CompactStoredAPSP.inputMagnitude (ComputableParameters.block n) c.left c.right c.target)
    p.pool = parameters.pool ∧ p.k = parameters.k ∧ p.lam = parameters.lam ∧
      p.M = parameters.M ∧ p.stages = parameters.stages :=
  CompleteAPSP.boundedPolicy_below parameters (actual_call_magnitude backend plan w W hw c hc)

/-- This proves eventual success of the same executable program used in run,
uniformly over all polynomially bounded edge magnitudes. -/
theorem eventually_successful (degree : ℕ) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ W : ℕ, W ≤ n^degree →
      (ComputableParameters.program n (magnitudeCap n W)).isSome = true := by
  simpa only [magnitudeCap] using ComputableParameters.eventually_program_apspCap degree

/-- Successful finite configurations give a derived controller resource
contract. Matrix-backend work is deliberately not identified with this field. -/
theorem successful_controller_contract {n : ℕ}
    (backend : CompleteAPSP.ProductBackend (Fin n) (Fin (ComputableParameters.block n)) (Fin n))
    (plan : CompactBlocks.PhysicalPlan) (W : ℕ) (hn : 2 ≤ n)
    (parameters : CompleteAPSP.Parameters (ComputableParameters.block n) (magnitudeCap n W))
    (hp : ComputableParameters.program n (magnitudeCap n W) = some parameters) :
    CostContract
      (oracleFromConfiguration backend plan W (ComputableParameters.program n (magnitudeCap n W)))
      (64*n*W+13) (CompactStoredAPSP.controllerBound (n := n) parameters) (3*n*n) := by
  have hs : (2*n).size ≤ parameters.stages := (success_configuration n W parameters hp).2.2.2.2.2.ge
  have hcontract := CompactStoredAPSP.controller_contract (block_pos n)
    (ComputableParameters.block_le_n n hn) backend plan W parameters hs
  rw [hp]
  constructor
  · intro A B T hbound
    exact hcontract.work A B T hbound
  · intro A B T hbound
    exact hcontract.answerWrites A B T hbound

theorem successful_correct_and_resources {n : ℕ}
    (backend : CompleteAPSP.ProductBackend (Fin n) (Fin (ComputableParameters.block n)) (Fin n))
    (plan : CompactBlocks.PhysicalPlan) (w : OptionalTable n) (W degree : ℕ)
    (parameters : CompleteAPSP.Parameters (ComputableParameters.block n) (magnitudeCap n W))
    (hp : ComputableParameters.program n (magnitudeCap n W) = some parameters)
    (hw : APSPReduction.EdgeBound (decode w) W)
    (hno : APSPReduction.NoNegativeCycles (decode w)) (hn : 2 ≤ n) (hW : W ≤ n^degree) :
    let out := run backend plan w W
    APSPReduction.IsAPSP (decode w) (decode out.value) ∧
    out.calls.length ≤ (n.log2+1)*(2*((degree+5)*(n.log2+1)+2)) ∧
    out.formationWrites ≤ (1+(n.log2+1)*(5*((degree+5)*(n.log2+1)+2)+7))*n^2 ∧
    out.oracleWork ≤ out.calls.length*CompactStoredAPSP.controllerBound (n := n) parameters ∧
    out.answerWrites ≤ out.calls.length*(3*n*n) :=
  StoredMinPlusAPSP.apsp_correct_and_resources _ (oracleFromConfiguration_correct backend plan W _)
    w W (CompactStoredAPSP.controllerBound (n := n) parameters) (3*n*n) degree hw hno hn hW
    (successful_controller_contract backend plan W hn parameters hp)

/-! ## Factor-aware compact count tables

These tables provide the actual callback expected by the array controller.
Their split is computed from the supplied factor history, rather than from a
modulus-only plan. Invalid histories have a correctness fallback; every valid
history uses the literal take/drop split and the fixed physical factor three.
-/

def ValidFactors (factors : List ℕ) : Prop :=
  factors.Nodup ∧ ∀ p ∈ factors, Nat.Prime p ∧ p ≠ 3

instance (factors : List ℕ) : Decidable (ValidFactors factors) := by
  unfold ValidFactors
  infer_instance

def historyFactorization (S : ℕ) (factors : List ℕ) (hv : ValidFactors factors) :
    CompactBlocks.PhysicalFactorization factors.prod where
  folded := (factors.take S).prod
  cyclic := (factors.drop S).prod
  folded_pos := List.prod_pos (fun p hp => (hv.2 p (List.mem_of_mem_take hp)).1.pos)
  cyclic_pos := List.prod_pos (fun p hp => (hv.2 p (List.mem_of_mem_drop hp)).1.pos)
  coprime := PhaseGeometry.split_prime_products_coprime factors S hv.1
    (fun p hp => (hv.2 p hp).1) (fun p hp => (hv.2 p hp).2)
  product := by rw [← List.prod_append, List.take_append_drop]

abbrev Incidence (n h : ℕ) :=
  CompleteAPSP.Incidence (Fin n) (Fin n) (Fin (CompactBlocks.blockCount n h))

def incidenceSize (n h : ℕ) : ℕ := (n*n)*(CompactBlocks.blockCount n h*3)

/-- Explicit mixed-radix indexing, without a chosen Fintype enumeration. -/
def incidenceEquiv (n h : ℕ) : Incidence n h ≃ Fin (incidenceSize n h) :=
  (Equiv.prodCongr finProdFinEquiv finProdFinEquiv).trans finProdFinEquiv

def flatInstance {n h : ℕ} (A B T : IntTable n) :
    CompositeCertification.Instance (Fin (incidenceSize n h)) (Fin n) where
  block i := (CompleteAPSP.incidenceInstance (CompactBlocks.block n h)
    (decode A) (decode B) (decode T)).block ((incidenceEquiv n h).symm i)
  value i k := (CompleteAPSP.incidenceInstance (CompactBlocks.block n h)
    (decode A) (decode B) (decode T)).value ((incidenceEquiv n h).symm i) k

def slotCount {n h : ℕ} (b : Fin (CompactBlocks.blockCount n h)) : ℕ :=
  min h (n-b.val*h)

/-- The incomplete block's size is a constant number of natural arithmetic
operations; constructing its size table need not scan all original labels. -/
theorem active_card_slotCount {n h : ℕ} (b : Fin (CompactBlocks.blockCount n h)) :
    (CompactBlocks.activeSlots n h b).card = slotCount b := by
  let f (s : Fin h) (hs : s ∈ CompactBlocks.activeSlots n h b) : Fin (slotCount b) :=
    ⟨s.val, by
      have hv := (Finset.mem_filter.mp hs).2
      have hh := s.isLt
      unfold CompactBlocks.index at hv
      unfold slotCount
      omega⟩
  have hc : (CompactBlocks.activeSlots n h b).card =
      (Finset.univ : Finset (Fin (slotCount b))).card := by
    apply Finset.card_bij f
    · intro s hs
      exact Finset.mem_univ _
    · intro s hs t ht heq
      apply Fin.ext
      exact congrArg (fun x : Fin (slotCount b) => x.val) heq
    · intro u _hu
      have hu := u.isLt
      have hh : u.val < h := hu.trans_le (Nat.min_le_left _ _)
      let s : Fin h := ⟨u.val, hh⟩
      have hs : s ∈ CompactBlocks.activeSlots n h b := by
        simp only [CompactBlocks.activeSlots, Finset.mem_filter, Finset.mem_univ, true_and]
        unfold CompactBlocks.index
        dsimp only [s]
        unfold slotCount at hu
        omega
      exact ⟨s, hs, Fin.ext rfl⟩
  simpa only [Finset.card_univ, Fintype.card_fin] using hc

theorem block_card_slotCount {n h : ℕ} (hh : 0 < h)
    (b : Fin (CompactBlocks.blockCount n h)) :
    (CompactBlocks.block n h b).card = slotCount b := by
  rw [← CompactBlocks.active_card_eq_block hh, active_card_slotCount]

def blockSizeTable (n h : ℕ) : ArrayCompositeAlgorithm.Counts (incidenceSize n h) :=
  Vector.ofFn (fun i => slotCount ((incidenceEquiv n h).symm i).2.1)

theorem blockSizeTable_correct {n h : ℕ} (hh : 0 < h) (A B T : IntTable n)
    (i : Fin (incidenceSize n h)) :
    (blockSizeTable n h).get i = ((flatInstance (h := h) A B T).block i).card := by
  simp only [blockSizeTable, Vector.get_ofFn, flatInstance, CompleteAPSP.incidenceInstance]
  exact (block_card_slotCount hh _).symm

def ownerTable (n h : ℕ) : ArrayCompositeAlgorithm.Owners (incidenceSize n h) (n*n) :=
  Vector.ofFn (fun i => finProdFinEquiv (((incidenceEquiv n h).symm i).1))

def initialFlags (n h : ℕ) : ArrayCompositeAlgorithm.Flags (incidenceSize n h) :=
  Vector.ofFn (fun i => decide (((incidenceEquiv n h).symm i).2.2 = CompleteAPSP.zeroWindow))

theorem incidenceSize_eq (n h : ℕ) :
    incidenceSize n h = 3*n^2*CompactBlocks.blockCount n h := by
  unfold incidenceSize
  ring

/-- One product array, of length ceil(n/h), is captured by each call's table.
All three signed-window targets read that same per-block array. -/
def historyTable {n h : ℕ}
    (backend : CompleteAPSP.ProductBackend (Fin n) (Fin h) (Fin n))
    (S : ℕ) (selected : List ℕ) (candidate : ℕ) (A B T : IntTable n) :
    Incidence n h → ℕ :=
  let factors := selected ++ [candidate]
  if hv : ValidFactors factors then
    CompactBlocks.physicalTable backend (historyFactorization S factors hv)
      (decode A) (decode B) (decode T)
  else if hz : factors.prod = 0 then
    fun x => ((CompactBlocks.block n h x.2.1).filter (fun k =>
      decode A x.1.1 k+decode B k x.1.2+decode T x.1.1 x.1.2-
        CompleteAPSP.windowValue x.2.2=0)).card
  else
    CompactBlocks.physicalTable backend (CompactBlocks.scalarPhysicalPlan factors.prod hz)
      (decode A) (decode B) (decode T)

theorem historyTable_correct {n h : ℕ} (hh : 0 < h)
    (backend : CompleteAPSP.ProductBackend (Fin n) (Fin h) (Fin n))
    (S : ℕ) (selected : List ℕ) (candidate : ℕ) (A B T : IntTable n)
    (x : Incidence n h) :
    historyTable backend S selected candidate A B T x =
      (CompleteAPSP.incidenceInstance (CompactBlocks.block n h)
        (decode A) (decode B) (decode T)).modCount (selected.prod*candidate) x := by
  have hprod : (selected ++ [candidate]).prod = selected.prod*candidate := by simp
  unfold historyTable
  split_ifs with hv hz
  · rw [CompactBlocks.physicalTable_correct hh]
    simp only [CompositeCertification.Instance.modCount, CompleteAPSP.incidenceInstance,
      ← hprod, Finset.card_filter]
  · rw [hprod] at hz
    simp only [CompositeCertification.Instance.modCount, CompleteAPSP.incidenceInstance,
      hz, Nat.cast_zero, zero_dvd_iff, Finset.card_filter]
  · rw [CompactBlocks.physicalTable_correct hh]
    simp only [CompositeCertification.Instance.modCount, CompleteAPSP.incidenceInstance,
      ← hprod, Finset.card_filter]

def factorOracle {n h : ℕ}
    (backend : CompleteAPSP.ProductBackend (Fin n) (Fin h) (Fin n))
    (S : ℕ) (A B T : IntTable n) : ArrayCompositeAlgorithm.Oracle (incidenceSize n h) where
  table selected candidate active :=
    let table := historyTable backend S selected candidate A B T
    Vector.ofFn (fun i => if active.get i then table ((incidenceEquiv n h).symm i) else 0)

theorem factorOracle_correct {n h : ℕ} (hh : 0 < h)
    (backend : CompleteAPSP.ProductBackend (Fin n) (Fin h) (Fin n))
    (S : ℕ) (A B T : IntTable n) :
    ArrayCompositeAlgorithm.Oracle.Correct (factorOracle backend S A B T) (flatInstance (h := h) A B T) := by
  intro selected candidate active i hi
  simp only [factorOracle, Vector.get_ofFn, hi, if_true]
  change historyTable backend S selected candidate A B T ((incidenceEquiv n h).symm i) =
    (CompleteAPSP.incidenceInstance (CompactBlocks.block n h)
      (decode A) (decode B) (decode T)).modCount (selected.prod*candidate) ((incidenceEquiv n h).symm i)
  exact historyTable_correct hh backend S selected candidate A B T ((incidenceEquiv n h).symm i)

theorem valid_history_uses_split {n h : ℕ}
    (backend : CompleteAPSP.ProductBackend (Fin n) (Fin h) (Fin n))
    (S : ℕ) (selected : List ℕ) (candidate : ℕ) (A B T : IntTable n)
    (hv : ValidFactors (selected ++ [candidate])) :
    historyTable backend S selected candidate A B T =
      CompactBlocks.physicalTable backend (historyFactorization S (selected ++ [candidate]) hv)
        (decode A) (decode B) (decode T) := by
  simp only [historyTable, dif_pos hv]

def primeVector (pool : Finset ℕ) : Vector ℕ pool.card :=
  ⟨(pool.sort (· ≤ ·)).toArray, by simp⟩

theorem primeVector_mem (pool : Finset ℕ) (i : Fin pool.card) :
    (primeVector pool).get i ∈ pool := by
  have hi : i.val < (pool.sort (· ≤ ·)).length := by simp
  have hm : (pool.sort (· ≤ ·))[i.val] ∈ pool.sort (· ≤ ·) := List.getElem_mem hi
  have hp := (Finset.mem_sort (· ≤ ·)).mp hm
  simpa only [primeVector, Vector.get, List.getElem_toArray, Fin.val_cast] using hp

theorem primeVector_injective (pool : Finset ℕ) :
    Function.Injective (primeVector pool).get := by
  intro i j hij
  have hi : i.val < (pool.sort (· ≤ ·)).length := by simp
  have hj : j.val < (pool.sort (· ≤ ·)).length := by simp
  have hv : (pool.sort (· ≤ ·))[i.val] = (pool.sort (· ≤ ·))[j.val] := by
    simpa [primeVector, Vector.get] using hij
  exact Fin.ext ((pool.sort_nodup (· ≤ ·)).getElem_inj_iff.mp hv)

theorem primeVector_pool (pool : Finset ℕ) :
    ArrayCompositeAlgorithm.pool (primeVector pool) (Vector.replicate pool.card true) = pool := by
  have hc := ArrayCompositeAlgorithm.pool_card (primeVector pool)
    (Vector.replicate pool.card true) (primeVector_injective pool)
  have hd : ArrayCompositeAlgorithm.decode (Vector.replicate pool.card true) = Finset.univ := by
    ext i
    simp [ArrayCompositeAlgorithm.mem_decode]
  rw [hd, Finset.card_univ, Fintype.card_fin] at hc
  apply Finset.eq_of_subset_of_card_le
  · intro p hp
    obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hp
    exact primeVector_mem pool i
  · exact hc.ge

theorem initialFlags_card (n h : ℕ) :
    (ArrayCompositeAlgorithm.decode (initialFlags n h)).card = n^2*CompactBlocks.blockCount n h := by
  have he : ArrayCompositeAlgorithm.decode (initialFlags n h) =
      (CompleteAPSP.zeroIncidences (I := Fin n) (J := Fin n)
        (H := Fin (CompactBlocks.blockCount n h))).map (incidenceEquiv n h).toEmbedding := by
    ext i
    simp [ArrayCompositeAlgorithm.mem_decode, initialFlags, CompleteAPSP.zeroIncidences]
  rw [he, Finset.card_map, CompactBlocks.zero_incidence_card]

def arrayRestarts {n h U : ℕ}
    (backend : CompleteAPSP.ProductBackend (Fin n) (Fin h) (Fin n))
    (S : ℕ) (parameters : CompleteAPSP.Parameters h U) (A B T : IntTable n) :
    ArrayCompositeAlgorithm.StageResult parameters.pool.card (incidenceSize n h) (n*n) :=
  let primes := primeVector parameters.pool
  ArrayCompositeAlgorithm.restarts (factorOracle backend S A B T) (ownerTable n h) primes
    (blockSizeTable n h) (Vector.replicate parameters.pool.card true)
    parameters.k parameters.lam parameters.stages (initialFlags n h) (Vector.replicate (n*n) false)

theorem arrayRestarts_correct {n h U : ℕ} (hh : 0 < h)
    (backend : CompleteAPSP.ProductBackend (Fin n) (Fin h) (Fin n))
    (S : ℕ) (parameters : CompleteAPSP.Parameters h U) (A B T : IntTable n)
    (hmag : ∀ i k, k ∈ (flatInstance (h := h) A B T).block i →
      ((flatInstance (h := h) A B T).value i k).natAbs ≤ U) :
    let out := arrayRestarts backend S parameters A B T
    (flatInstance (h := h) A B T).StateInvariant (ownerTable n h).get
      (ArrayCompositeAlgorithm.decode (initialFlags n h))
      (ArrayCompositeAlgorithm.decode out.active) (ArrayCompositeAlgorithm.decode out.marked) ∧
    2^parameters.stages*(ArrayCompositeAlgorithm.decode out.active).card ≤
      n^2*CompactBlocks.blockCount n h := by
  have hfalse : ArrayCompositeAlgorithm.decode (Vector.replicate (n*n) false) = ∅ := by
    ext i
    simp [ArrayCompositeAlgorithm.mem_decode]
  have hinv := (flatInstance (h := h) A B T).initial_invariant
    (ownerTable n h).get (ArrayCompositeAlgorithm.decode (initialFlags n h))
  have hc := ArrayCompositeAlgorithm.restarts_correct (factorOracle backend S A B T)
    (flatInstance (h := h) A B T) (factorOracle_correct hh backend S A B T)
    (ownerTable n h) (primeVector parameters.pool) (primeVector_injective parameters.pool)
    (ArrayCompositeAlgorithm.decode (initialFlags n h)) (initialFlags n h)
    (Vector.replicate (n*n) false) (blockSizeTable n h) (Vector.replicate parameters.pool.card true)
    parameters.k parameters.M parameters.lam h parameters.stages
    (by simpa only [hfalse] using hinv)
    (fun i _hi => blockSizeTable_correct hh A B T i) parameters.threshold
    (by simpa only [primeVector_pool] using parameters.size)
    (by simpa only [primeVector_pool] using
      CertificationParameters.parameters_divisorBound parameters (flatInstance (h := h) A B T) hmag)
    (fun i _hi => CompactBlocks.block_card_le hh ((incidenceEquiv n h).symm i).2.1) parameters.rate
  simpa only [arrayRestarts, initialFlags_card] using hc

theorem arrayRestarts_calls_bound {n h U : ℕ}
    (backend : CompleteAPSP.ProductBackend (Fin n) (Fin h) (Fin n))
    (S : ℕ) (parameters : CompleteAPSP.Parameters h U) (A B T : IntTable n) :
    (arrayRestarts backend S parameters A B T).calls.length ≤
      parameters.stages*(parameters.k+1)*parameters.pool.card :=
  ArrayCompositeAlgorithm.restarts_calls_bound _ _ _ _ _ _ _ _ _ _

theorem arrayRestarts_valid_histories {n h U : ℕ}
    (backend : CompleteAPSP.ProductBackend (Fin n) (Fin h) (Fin n))
    (S : ℕ) (parameters : CompleteAPSP.Parameters h U) (A B T : IntTable n)
    (hthree : ∀ p ∈ parameters.pool, p ≠ 3) :
    ∀ call ∈ (arrayRestarts backend S parameters A B T).calls,
      ValidFactors (call.selected ++ [call.candidate]) := by
  have hd := ArrayCompositeAlgorithm.restarts_factors_distinct
    (factorOracle backend S A B T) (ownerTable n h) (primeVector parameters.pool)
    (primeVector_injective parameters.pool) (blockSizeTable n h)
    (Vector.replicate parameters.pool.card true) parameters.k parameters.lam parameters.stages
    (initialFlags n h) (Vector.replicate (n*n) false)
  have hp := ArrayCompositeAlgorithm.restarts_factors_property
    (factorOracle backend S A B T) (ownerTable n h) (primeVector parameters.pool)
    (fun p => Nat.Prime p ∧ p ≠ 3)
    (fun i => ⟨parameters.prime _ (primeVector_mem _ i), hthree _ (primeVector_mem _ i)⟩)
    (blockSizeTable n h) (Vector.replicate parameters.pool.card true)
    parameters.k parameters.lam parameters.stages (initialFlags n h) (Vector.replicate (n*n) false)
  intro call hc
  exact ⟨hd call hc, hp call hc⟩

def scanBool {α : Type} (test : α → Bool) : List α → Bool × ℕ
  | [] => (false, 0)
  | x :: xs =>
    let tail := scanBool test xs
    (test x || tail.1, tail.2+1)

theorem scanBool_correct {α : Type} (test : α → Bool) (xs : List α) :
    (scanBool test xs).1 = true ↔ ∃ x ∈ xs, test x = true := by
  induction xs with
  | nil => simp [scanBool]
  | cons x xs ih => simp [scanBool, ih]

theorem scanBool_tests {α : Type} (test : α → Bool) (xs : List α) :
    (scanBool test xs).2 = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [scanBool, ih]

def slotTest {n h : ℕ} (A B T : IntTable n) (x : Incidence n h) (s : Fin h) : Bool :=
  if CompactBlocks.index x.2.1 s < n then
    decide (CompactBlocks.localLeft x.2.1 (decode A) x.1.1 s+
      CompactBlocks.localRight x.2.1 (decode B) s x.1.2+decode T x.1.1 x.1.2 =
        CompleteAPSP.windowValue x.2.2)
  else false

def compactScan {n h : ℕ} (A B T : IntTable n) (x : Incidence n h) : Bool × ℕ :=
  scanBool (slotTest A B T x) (List.finRange h)

theorem compactScan_correct {n h : ℕ} (hh : 0 < h) (A B T : IntTable n)
    (x : Incidence n h) :
    (compactScan A B T x).1 = true ↔
      ∃ k ∈ CompactBlocks.block n h x.2.1,
        decode A x.1.1 k+decode B k x.1.2+decode T x.1.1 x.1.2-
          CompleteAPSP.windowValue x.2.2=0 := by
  rw [compactScan, scanBool_correct]
  have hs : (∃ s ∈ List.finRange h, slotTest A B T x s = true) ↔
      ∃ s ∈ CompactBlocks.activeSlots n h x.2.1,
        CompactBlocks.localLeft x.2.1 (decode A) x.1.1 s+
          CompactBlocks.localRight x.2.1 (decode B) s x.1.2+decode T x.1.1 x.1.2 =
            CompleteAPSP.windowValue x.2.2 := by
    simp [slotTest, CompactBlocks.activeSlots]
  rw [hs, CompactBlocks.compact_witness_iff hh]
  simp only [sub_eq_zero]

theorem compactScan_tests {n h : ℕ} (A B T : IntTable n) (x : Incidence n h) :
    (compactScan A B T x).2 = h := by
  simp [compactScan, scanBool_tests]

/-- Each active incidence computes its original-sum scan once. -/
def finalScans {n h : ℕ} (A B T : IntTable n)
    (active : ArrayCompositeAlgorithm.Flags (incidenceSize n h)) :
    Vector (Bool × ℕ) (incidenceSize n h) :=
  Vector.ofFn (fun i => if active.get i then
    compactScan A B T ((incidenceEquiv n h).symm i) else (false,0))

def scanAnswers {n h : ℕ} (scans : Vector (Bool × ℕ) (incidenceSize n h)) :
    ArrayCompositeAlgorithm.Flags (incidenceSize n h) :=
  Vector.ofFn (fun i => (scans.get i).1)

def scanTests {n h : ℕ} (scans : Vector (Bool × ℕ) (incidenceSize n h)) : ℕ :=
  ∑ i : Fin (incidenceSize n h), (scans.get i).2

theorem scanTests_eq {n h : ℕ} (A B T : IntTable n)
    (active : ArrayCompositeAlgorithm.Flags (incidenceSize n h)) :
    scanTests (finalScans A B T active) = h*(ArrayCompositeAlgorithm.decode active).card := by
  unfold scanTests finalScans
  simp only [Vector.get_ofFn]
  have he : (∑ i : Fin (incidenceSize n h),
      (if active.get i then compactScan A B T ((incidenceEquiv n h).symm i) else (false,0)).2) =
      ∑ i ∈ ArrayCompositeAlgorithm.decode active, h := by
    unfold ArrayCompositeAlgorithm.decode
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _hi
    by_cases ha : active.get i = true
    · simp [ha, compactScan_tests]
    · have ha' : active.get i = false := Bool.eq_false_iff.mpr ha
      simp [ha']
  rw [he]
  simp [Nat.mul_comm]

theorem finalScans_mark_correct {n h : ℕ} (hh : 0 < h) (A B T : IntTable n)
    (active : ArrayCompositeAlgorithm.Flags (incidenceSize n h))
    (marked : ArrayCompositeAlgorithm.Flags (n*n)) :
    ArrayCompositeAlgorithm.decode (ArrayCompositeAlgorithm.mark (ownerTable n h)
      (scanAnswers (finalScans A B T active)) marked) =
    ArrayCompositeAlgorithm.decode marked ∪
      (flatInstance (h := h) A B T).exactPairs (ownerTable n h).get
        (ArrayCompositeAlgorithm.decode active) := by
  ext q
  simp only [ArrayCompositeAlgorithm.mem_decode, ArrayCompositeAlgorithm.mark_get,
    Finset.mem_union, CompositeCertification.Instance.mem_exactPairs_iff]
  apply or_congr Iff.rfl
  constructor
  · rintro ⟨i, hi, howner⟩
    simp only [scanAnswers, finalScans, Vector.get_ofFn] at hi
    have ha : active.get i = true := by
      by_contra hn
      have hf := Bool.eq_false_iff.mpr hn
      simp [hf] at hi
    have hv : (compactScan A B T ((incidenceEquiv n h).symm i)).1 = true := by simpa only [ha, if_true] using hi
    exact ⟨i, ha, howner, (compactScan_correct hh A B T _).mp hv⟩
  · rintro ⟨i, hi, howner, hwitness⟩
    refine ⟨i, ?_, howner⟩
    simp only [scanAnswers, finalScans, Vector.get_ofFn, hi, if_true]
    exact (compactScan_correct hh A B T _).mpr hwitness

theorem initial_exactPairs_zero {n h : ℕ} (hh : 0 < h) (A B T : IntTable n) (i j : Fin n) :
    let q := finProdFinEquiv (i,j)
    q ∈ (flatInstance (h := h) A B T).exactPairs (ownerTable n h).get
      (ArrayCompositeAlgorithm.decode (initialFlags n h)) ↔
      ∃ k, decode A i k+decode B k j+decode T i j=0 := by
  dsimp only
  rw [CompositeCertification.Instance.mem_exactPairs_iff]
  constructor
  · rintro ⟨x, hx, howner, k, _hk, hz⟩
    have hw : ((incidenceEquiv n h).symm x).2.2 = CompleteAPSP.zeroWindow := by
      simpa only [ArrayCompositeAlgorithm.mem_decode, initialFlags, Vector.get_ofFn,
        decide_eq_true_eq] using hx
    have hp : ((incidenceEquiv n h).symm x).1 = (i,j) :=
      finProdFinEquiv.injective (by simpa only [ownerTable, Vector.get_ofFn] using howner)
    have hi := congrArg Prod.fst hp
    have hj := congrArg Prod.snd hp
    refine ⟨k, ?_⟩
    simpa only [flatInstance, CompleteAPSP.incidenceInstance, hi, hj, hw,
      CompleteAPSP.windowValue_zero, sub_zero] using hz
  · rintro ⟨k, hk⟩
    obtain ⟨b, hb⟩ := CompactBlocks.blocks_cover hh k
    let u : Incidence n h := ((i,j),b,CompleteAPSP.zeroWindow)
    refine ⟨incidenceEquiv n h u, ?_, ?_, k, ?_, ?_⟩
    · simp [ArrayCompositeAlgorithm.mem_decode, initialFlags, u]
    · simp [ownerTable, u]
    · simpa only [flatInstance, CompleteAPSP.incidenceInstance, Equiv.symm_apply_apply, u] using hb
    · simpa only [flatInstance, CompleteAPSP.incidenceInstance, Equiv.symm_apply_apply, u,
        CompleteAPSP.windowValue_zero, sub_zero] using hk

structure ArrayPayload (n h : ℕ) where
  active : ArrayCompositeAlgorithm.Flags (incidenceSize n h)
  marked : ArrayCompositeAlgorithm.Flags (n*n)
  calls : List (ArrayCompositeAlgorithm.FactorCall (incidenceSize n h))
  originalSumTests : ℕ

structure ArraySolution (n h : ℕ) where
  answers : BoolTable n
  payload : ArrayPayload n h

/-- One joint execution produces the dense answer matrix, retained factor
history, and actual original-sum-test counter. No oracle is replayed to form
the trace or to price those tests. -/
def arraySolve {n h U : ℕ}
    (backend : CompleteAPSP.ProductBackend (Fin n) (Fin h) (Fin n))
    (S : ℕ) (parameters : CompleteAPSP.Parameters h U) (A B T : IntTable n) :
    ArraySolution n h :=
  let restarts := arrayRestarts backend S parameters A B T
  let scans := finalScans A B T restarts.active
  let yes := scanAnswers scans
  let marked := ArrayCompositeAlgorithm.mark (ownerTable n h) yes restarts.marked
  { answers := store (fun i j => marked.get (finProdFinEquiv (i,j)))
    payload := ⟨restarts.active, marked, restarts.calls, scanTests scans⟩ }

theorem arraySolve_correct {n h U : ℕ} (hh : 0 < h)
    (backend : CompleteAPSP.ProductBackend (Fin n) (Fin h) (Fin n))
    (S : ℕ) (parameters : CompleteAPSP.Parameters h U) (A B T : IntTable n)
    (hmag : ∀ i k, k ∈ (flatInstance (h := h) A B T).block i →
      ((flatInstance (h := h) A B T).value i k).natAbs ≤ U) (i j : Fin n) :
    decode (arraySolve backend S parameters A B T).answers i j = true ↔
      ∃ k, decode A i k+decode B k j+decode T i j=0 := by
  have hc := arrayRestarts_correct hh backend S parameters A B T hmag
  have hm := finalScans_mark_correct hh A B T
    (arrayRestarts backend S parameters A B T).active
    (arrayRestarts backend S parameters A B T).marked
  have hf := ArrayCompositeAlgorithm.final_scan_of_invariant (flatInstance (h := h) A B T)
    (ownerTable n h) (ArrayCompositeAlgorithm.decode (initialFlags n h))
    (arrayRestarts backend S parameters A B T).active
    (arrayRestarts backend S parameters A B T).marked hc.1
  have he := hm.trans hf
  have hmem := Finset.ext_iff.mp he (finProdFinEquiv (i,j))
  simpa only [arraySolve, decode_store, ArrayCompositeAlgorithm.mem_decode] using
    hmem.trans (initial_exactPairs_zero hh A B T i j)

theorem arraySolve_scan_budget {n h U : ℕ} (hh : 0 < h) (hhn : h ≤ n)
    (backend : CompleteAPSP.ProductBackend (Fin n) (Fin h) (Fin n))
    (S : ℕ) (parameters : CompleteAPSP.Parameters h U)
    (hs : (2*n).size ≤ parameters.stages) (A B T : IntTable n)
    (hmag : ∀ i k, k ∈ (flatInstance (h := h) A B T).block i →
      ((flatInstance (h := h) A B T).value i k).natAbs ≤ U) :
    (arraySolve backend S parameters A B T).payload.originalSumTests ≤ n^2 := by
  have hc := (arrayRestarts_correct hh backend S parameters A B T hmag).2
  have hb := CompactStoredAPSP.scan_budget hhn hs
  change scanTests (finalScans A B T (arrayRestarts backend S parameters A B T).active) ≤ _
  rw [scanTests_eq]
  apply Nat.le_of_mul_le_mul_left (c := 2^parameters.stages) ?_ (by positivity)
  calc
    _ = h*(2^parameters.stages*(ArrayCompositeAlgorithm.decode
        (arrayRestarts backend S parameters A B T).active).card) := by ring
    _ ≤ h*(n^2*CompactBlocks.blockCount n h) := Nat.mul_le_mul_left h hc
    _ = h*n^2*CompactBlocks.blockCount n h := by ring
    _ ≤ _ := hb

/-- Only the original-sum-test component is placed in work here. Complete
controller/backend/bit work still requires its execution-cost refinement. -/
def arrayCallback {n h : ℕ}
    (backend : CompleteAPSP.ProductBackend (Fin n) (Fin h) (Fin n))
    (S : ℕ) (policy : CompleteAPSP.ParameterPolicy h) : DenseOracle n (ArrayPayload n h) :=
  fun A B T =>
    let parameters := policy (CompactStoredAPSP.inputMagnitude h A B T)
    let out := arraySolve backend S parameters A B T
    { answers := out.answers
      payload := out.payload
      work := out.payload.originalSumTests
      answerWrites := n*n }

theorem arrayCallback_correct {n h : ℕ} (hh : 0 < h)
    (backend : CompleteAPSP.ProductBackend (Fin n) (Fin h) (Fin n))
    (S : ℕ) (policy : CompleteAPSP.ParameterPolicy h) :
    DenseOracleCorrect (arrayCallback backend S policy) := by
  intro A B T i j
  exact arraySolve_correct hh backend S _ A B T
    (fun x k _hk => CompleteAPSP.magnitude_bound
      (CompleteAPSP.incidenceInstance (CompactBlocks.block n h) (decode A) (decode B) (decode T))
      ((incidenceEquiv n h).symm x) k) i j

abbrev ActualPayload (n : ℕ) := Option (ArrayPayload n (ComputableParameters.block n))

def arrayOracleFromConfiguration {n : ℕ}
    (backend : CompleteAPSP.ProductBackend (Fin n) (Fin (ComputableParameters.block n)) (Fin n))
    (W : ℕ)
    (configuration : Option (CompleteAPSP.Parameters (ComputableParameters.block n) (magnitudeCap n W))) :
    DenseOracle n (ActualPayload n) :=
  match configuration with
  | none => fun A B T =>
      let out := directCallback n A B T
      { answers := out.answers, payload := none, work := out.work, answerWrites := out.answerWrites }
  | some parameters =>
      let oracle := arrayCallback backend AlignedCertificate.S (CompleteAPSP.boundedPolicy parameters)
      fun A B T =>
        let out := oracle A B T
        { answers := out.answers, payload := some out.payload, work := out.work, answerWrites := out.answerWrites }

theorem arrayOracleFromConfiguration_correct {n : ℕ}
    (backend : CompleteAPSP.ProductBackend (Fin n) (Fin (ComputableParameters.block n)) (Fin n))
    (W : ℕ)
    (configuration : Option (CompleteAPSP.Parameters (ComputableParameters.block n) (magnitudeCap n W))) :
    DenseOracleCorrect (arrayOracleFromConfiguration backend W configuration) := by
  cases configuration with
  | none => exact directCallback_correct n
  | some parameters => exact arrayCallback_correct (block_pos n) backend _ _

/-- The factor-aware array algorithm is the successful branch of this actual
stored APSP execution. The one checked configuration is bound before any
adaptive matrix inputs exist. -/
def arrayRun {n : ℕ}
    (backend : CompleteAPSP.ProductBackend (Fin n) (Fin (ComputableParameters.block n)) (Fin n))
    (w : OptionalTable n) (W : ℕ) : Execution n (Option ℤ) (ActualPayload n) :=
  let configuration := ComputableParameters.program n (magnitudeCap n W)
  let oracle := arrayOracleFromConfiguration backend W configuration
  StoredMinPlusAPSP.apsp oracle w W

theorem arrayRun_correct {n : ℕ}
    (backend : CompleteAPSP.ProductBackend (Fin n) (Fin (ComputableParameters.block n)) (Fin n))
    (w : OptionalTable n) (W : ℕ) (hw : APSPReduction.EdgeBound (decode w) W)
    (hno : APSPReduction.NoNegativeCycles (decode w)) :
    APSPReduction.IsAPSP (decode w) (decode (arrayRun backend w W).value) :=
  StoredMinPlusAPSP.apsp_correct _ (arrayOracleFromConfiguration_correct backend W _) w W hw hno

/-- Fully instantiated exact-arithmetic correctness, independently of the
unfinished fast thin-product cost/bit execution bridge. -/
def referenceArrayRun {n : ℕ} (w : OptionalTable n) (W : ℕ) :
    Execution n (Option ℤ) (ActualPayload n) :=
  arrayRun CompleteAPSP.naiveBackend w W

theorem referenceArrayRun_correct {n : ℕ} (w : OptionalTable n) (W : ℕ)
    (hw : APSPReduction.EdgeBound (decode w) W)
    (hno : APSPReduction.NoNegativeCycles (decode w)) :
    APSPReduction.IsAPSP (decode w) (decode (referenceArrayRun w W).value) :=
  arrayRun_correct _ w W hw hno

theorem arrayRun_calls_faithful {n : ℕ}
    (backend : CompleteAPSP.ProductBackend (Fin n) (Fin (ComputableParameters.block n)) (Fin n))
    (w : OptionalTable n) (W : ℕ) (c : Call n (ActualPayload n))
    (hc : c ∈ (arrayRun backend w W).calls) :
    c.output = arrayOracleFromConfiguration backend W
      (ComputableParameters.program n (magnitudeCap n W)) c.left c.right c.target :=
  StoredMinPlusAPSP.apsp_calls_faithful _ w W c hc

theorem arrayRun_actual_call_magnitude {n : ℕ}
    (backend : CompleteAPSP.ProductBackend (Fin n) (Fin (ComputableParameters.block n)) (Fin n))
    (w : OptionalTable n) (W : ℕ) (hw : APSPReduction.EdgeBound (decode w) W)
    (c : Call n (ActualPayload n)) (hc : c ∈ (arrayRun backend w W).calls) :
    CompactStoredAPSP.inputMagnitude (ComputableParameters.block n) c.left c.right c.target ≤
      magnitudeCap n W := by
  have hb := StoredMinPlusAPSP.apsp_query_bound
    (arrayOracleFromConfiguration backend W (ComputableParameters.program n (magnitudeCap n W)))
    (arrayOracleFromConfiguration_correct backend W _) w W hw c hc
  have hm := CompleteAPSP.triangle_magnitude_bound
    (CompactBlocks.block n (ComputableParameters.block n))
    (decode c.left) (decode c.right) (decode c.target) (64*n*W+13)
    (fun i k => CompleteAPSP.natAbs_of_symmetric (hb.1 i k))
    (fun k j => CompleteAPSP.natAbs_of_symmetric (hb.2.1 k j))
    (fun i j => CompleteAPSP.natAbs_of_symmetric (hb.2.2 i j))
  change CompactStoredAPSP.inputMagnitude (ComputableParameters.block n)
    c.left c.right c.target ≤ 3*(64*n*W+13)+1 at hm
  unfold magnitudeCap
  nlinarith

/-- Every actual call in the successful program retains a payload from that
same callback invocation. All backend histories are distinct prime lists
excluding three, so both correctness fallbacks are unused. -/
theorem arrayRun_successful_call_resources {n : ℕ} (hn : 2 ≤ n)
    (backend : CompleteAPSP.ProductBackend (Fin n) (Fin (ComputableParameters.block n)) (Fin n))
    (w : OptionalTable n) (W : ℕ)
    (parameters : CompleteAPSP.Parameters (ComputableParameters.block n) (magnitudeCap n W))
    (hp : ComputableParameters.program n (magnitudeCap n W) = some parameters)
    (hw : APSPReduction.EdgeBound (decode w) W)
    (c : Call n (ActualPayload n)) (hc : c ∈ (arrayRun backend w W).calls) :
    ∃ out : ArrayPayload n (ComputableParameters.block n), c.output.payload = some out ∧
      out.calls.length ≤ parameters.stages*(parameters.k+1)*parameters.pool.card ∧
      out.originalSumTests ≤ n^2 ∧
      ∀ call ∈ out.calls, ValidFactors (call.selected ++ [call.candidate]) := by
  let p := CompleteAPSP.boundedPolicy parameters
    (CompactStoredAPSP.inputMagnitude (ComputableParameters.block n) c.left c.right c.target)
  have hcap := arrayRun_actual_call_magnitude backend w W hw c hc
  obtain ⟨hpool, hk, _hlam, _hM, hstages⟩ := CompleteAPSP.boundedPolicy_below parameters hcap
  change p.pool = parameters.pool at hpool
  change p.k = parameters.k at hk
  change p.stages = parameters.stages at hstages
  let out := (arraySolve backend AlignedCertificate.S p c.left c.right c.target).payload
  have hfaith := arrayRun_calls_faithful backend w W c hc
  rw [hp] at hfaith
  have hout : c.output.payload = some out := by rw [hfaith]; rfl
  have hmag : ∀ i k, k ∈ (flatInstance (h := ComputableParameters.block n) c.left c.right c.target).block i →
      ((flatInstance (h := ComputableParameters.block n) c.left c.right c.target).value i k).natAbs ≤
        CompactStoredAPSP.inputMagnitude (ComputableParameters.block n) c.left c.right c.target :=
    fun i k _ => CompleteAPSP.magnitude_bound
      (CompleteAPSP.incidenceInstance (CompactBlocks.block n (ComputableParameters.block n))
        (decode c.left) (decode c.right) (decode c.target)) ((incidenceEquiv n _).symm i) k
  have hs : (2*n).size ≤ p.stages := by
    rw [hstages, (success_configuration n W parameters hp).2.2.2.2.2]
  have hthree : ∀ q ∈ p.pool, q ≠ 3 := by
    intro q hq
    rw [hpool, (success_configuration n W parameters hp).1] at hq
    exact fun heq => (Finset.mem_sdiff.mp hq).2 (by simp only [heq, Finset.mem_singleton])
  refine ⟨out, hout, ?_, ?_, ?_⟩
  · have hb := arrayRestarts_calls_bound backend AlignedCertificate.S p c.left c.right c.target
    calc
      out.calls.length ≤ p.stages*(p.k+1)*p.pool.card := hb
      _ = parameters.stages*(parameters.k+1)*parameters.pool.card := by rw [hstages, hk, hpool]
  · exact arraySolve_scan_budget (block_pos n) (ComputableParameters.block_le_n n hn)
      backend AlignedCertificate.S p hs c.left c.right c.target hmag
  · exact arrayRestarts_valid_histories backend AlignedCertificate.S p c.left c.right c.target hthree

#print axioms directScan_correct
#print axioms directScan_tests
#print axioms directCallback_correct
#print axioms directCallback_tests
#print axioms oracleFromConfiguration_correct
#print axioms run_correct
#print axioms referenceRun_correct
#print axioms success_configuration
#print axioms calls_faithful
#print axioms actual_call_magnitude
#print axioms successful_calls_keep_parameters
#print axioms eventually_successful
#print axioms successful_controller_contract
#print axioms successful_correct_and_resources
#print axioms historyTable_correct
#print axioms factorOracle_correct
#print axioms valid_history_uses_split
#print axioms active_card_slotCount
#print axioms block_card_slotCount
#print axioms blockSizeTable_correct
#print axioms incidenceSize_eq
#print axioms primeVector_mem
#print axioms primeVector_injective
#print axioms primeVector_pool
#print axioms initialFlags_card
#print axioms arrayRestarts_correct
#print axioms arrayRestarts_calls_bound
#print axioms arrayRestarts_valid_histories
#print axioms compactScan_correct
#print axioms compactScan_tests
#print axioms scanTests_eq
#print axioms finalScans_mark_correct
#print axioms initial_exactPairs_zero
#print axioms arraySolve_correct
#print axioms arraySolve_scan_budget
#print axioms arrayCallback_correct
#print axioms arrayOracleFromConfiguration_correct
#print axioms arrayRun_correct
#print axioms referenceArrayRun_correct
#print axioms arrayRun_calls_faithful
#print axioms arrayRun_actual_call_magnitude
#print axioms arrayRun_successful_call_resources

end ThinMatrix.EndToEndAPSP
