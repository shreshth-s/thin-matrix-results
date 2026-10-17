import EndToEndAPSP
import CountedArrayComposite
import ThinMatrixBackend
import DenseControllerExecution

/-!
# Stored APSP with retained counted modular producers

The counted controller invokes a factor-aware producer once per candidate,
retains its materialized count row, payload and counter, and uses those same
values for selection and subsequent resource aggregation. Final original-sum
scans and pair scatter are also evaluated jointly with their counters.
`solve` calls the instrumented controller once and stores its returned sites;
the uninstrumented controller occurs only in reference definitions and proofs.

The resource components here have explicit meanings. Backend work is the sum
of producer-returned counters; controller visits and dense writes are indexed
loop/site counts. Adding these components is not an assertion that they are
all constant-time bit operations, nor a word-RAM running-time theorem.
-/

namespace ThinMatrix.CountedEndToEndAPSP

open StoredMinPlusAPSP
open EndToEndAPSP

structure Backend (n h : ℕ) (Payload : Type) where
  oracle : IntTable n → IntTable n → IntTable n →
    CountedArrayComposite.Oracle (incidenceSize n h) Payload
  correct : ∀ A B T, (oracle A B T).Correct (flatInstance (h := h) A B T)

def restarts {n h U : ℕ} {Payload : Type} (backend : Backend n h Payload)
    (parameters : CompleteAPSP.Parameters h U) (A B T : IntTable n) :
    CountedArrayComposite.StageResult parameters.pool.card (incidenceSize n h) (n*n) Payload :=
  CountedArrayComposite.restarts (backend.oracle A B T) (ownerTable n h)
    (primeVector parameters.pool) (blockSizeTable n h) (Vector.replicate parameters.pool.card true)
    parameters.k parameters.lam parameters.stages (initialFlags n h) (Vector.replicate (n*n) false)

/-- The executed controller returns its value and measured sites jointly.
The earlier `restarts` is retained only as a proof specification. -/
def restartsExec {n h U : ℕ} {Payload : Type} (backend : Backend n h Payload)
    (parameters : CompleteAPSP.Parameters h U) (A B T : IntTable n) :
    DenseControllerExecution.Result
      (CountedArrayComposite.StageResult parameters.pool.card (incidenceSize n h) (n*n) Payload) :=
  DenseControllerExecution.restartsExec (backend.oracle A B T) (ownerTable n h)
    (primeVector parameters.pool) (blockSizeTable n h) (Vector.replicate parameters.pool.card true)
    parameters.k parameters.lam parameters.stages (initialFlags n h) (Vector.replicate (n*n) false)

theorem restartsExec_value {n h U : ℕ} {Payload : Type} (backend : Backend n h Payload)
    (parameters : CompleteAPSP.Parameters h U) (A B T : IntTable n) :
    (restartsExec backend parameters A B T).value = restarts backend parameters A B T :=
  DenseControllerExecution.restartsExec_value _ _ _ _ _ _ _ _ _ _

theorem restarts_correct {n h U : ℕ} {Payload : Type} (hh : 0 < h)
    (backend : Backend n h Payload) (parameters : CompleteAPSP.Parameters h U) (A B T : IntTable n)
    (hmag : ∀ i k, k ∈ (flatInstance (h := h) A B T).block i →
      ((flatInstance (h := h) A B T).value i k).natAbs ≤ U) :
    let out := restarts backend parameters A B T
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
  have hc := ArrayCompositeAlgorithm.restarts_correct (backend.oracle A B T).erase
    (flatInstance (h := h) A B T) (backend.correct A B T) (ownerTable n h)
    (primeVector parameters.pool) (primeVector_injective parameters.pool)
    (ArrayCompositeAlgorithm.decode (initialFlags n h)) (initialFlags n h)
    (Vector.replicate (n*n) false) (blockSizeTable n h) (Vector.replicate parameters.pool.card true)
    parameters.k parameters.M parameters.lam h parameters.stages
    (by simpa only [hfalse] using hinv)
    (fun i _hi => blockSizeTable_correct hh A B T i) parameters.threshold
    (by simpa only [primeVector_pool] using parameters.size)
    (by simpa only [primeVector_pool] using
      CertificationParameters.parameters_divisorBound parameters (flatInstance (h := h) A B T) hmag)
    (fun i _hi => CompactBlocks.block_card_le hh ((incidenceEquiv n h).symm i).2.1) parameters.rate
  have he := CountedArrayComposite.restarts_erases (backend.oracle A B T) (ownerTable n h)
    (primeVector parameters.pool) (blockSizeTable n h) (Vector.replicate parameters.pool.card true)
    parameters.k parameters.lam parameters.stages (initialFlags n h) (Vector.replicate (n*n) false)
  rw [← he] at hc
  simpa only [CountedArrayComposite.StageResult.erase, restarts, initialFlags_card] using hc

structure Scatter (Q : ℕ) where
  flags : ArrayCompositeAlgorithm.Flags Q
  visits : ℕ
  writes : ℕ

def scatter {I Q : ℕ} (owner : ArrayCompositeAlgorithm.Owners I Q)
    (yes : ArrayCompositeAlgorithm.Flags I) :
    ArrayCompositeAlgorithm.Flags Q → List (Fin I) → Scatter Q
  | marked, [] => ⟨marked,0,0⟩
  | marked, i :: is =>
    let flag := yes.get i
    let marked' := if flag then ArrayCompositeAlgorithm.put marked (owner.get i) true else marked
    let tail := scatter owner yes marked' is
    ⟨tail.flags, tail.visits+1, tail.writes+(if flag then 1 else 0)⟩

theorem scatter_value {I Q : ℕ} (owner : ArrayCompositeAlgorithm.Owners I Q)
    (yes : ArrayCompositeAlgorithm.Flags I) (marked : ArrayCompositeAlgorithm.Flags Q)
    (is : List (Fin I)) :
    (scatter owner yes marked is).flags = ArrayCompositeAlgorithm.markScan owner yes marked is := by
  induction is generalizing marked with
  | nil => rfl
  | cons i is ih => simp only [scatter, ArrayCompositeAlgorithm.markScan, ih]

theorem scatter_visits {I Q : ℕ} (owner : ArrayCompositeAlgorithm.Owners I Q)
    (yes : ArrayCompositeAlgorithm.Flags I) (marked : ArrayCompositeAlgorithm.Flags Q)
    (is : List (Fin I)) : (scatter owner yes marked is).visits = is.length := by
  induction is generalizing marked with
  | nil => rfl
  | cons i is ih => simp only [scatter, ih, List.length_cons]

theorem scatter_writes_le {I Q : ℕ} (owner : ArrayCompositeAlgorithm.Owners I Q)
    (yes : ArrayCompositeAlgorithm.Flags I) (marked : ArrayCompositeAlgorithm.Flags Q)
    (is : List (Fin I)) : (scatter owner yes marked is).writes ≤ is.length := by
  induction is generalizing marked with
  | nil => exact le_rfl
  | cons i is ih =>
    have ht := ih (if yes.get i then ArrayCompositeAlgorithm.put marked (owner.get i) true else marked)
    change (scatter owner yes (if yes.get i then
      ArrayCompositeAlgorithm.put marked (owner.get i) true else marked) is).writes+
      (if yes.get i then 1 else 0) ≤ is.length+1
    cases ha : yes.get i <;> simp only [ha, Bool.false_eq_true, if_false, if_true] at ht ⊢ <;> omega

theorem scatter_writes_countP {I Q : ℕ} (owner : ArrayCompositeAlgorithm.Owners I Q)
    (yes : ArrayCompositeAlgorithm.Flags I) (marked : ArrayCompositeAlgorithm.Flags Q)
    (is : List (Fin I)) :
    (scatter owner yes marked is).writes = is.countP (fun i => yes.get i) := by
  induction is generalizing marked with
  | nil => rfl
  | cons i is ih => simp only [scatter, ih, List.countP_cons]

theorem scatter_writes_card {I Q : ℕ} (owner : ArrayCompositeAlgorithm.Owners I Q)
    (yes : ArrayCompositeAlgorithm.Flags I) (marked : ArrayCompositeAlgorithm.Flags Q) :
    (scatter owner yes marked (List.finRange I)).writes = (ArrayCompositeAlgorithm.decode yes).card := by
  have he : ((List.finRange I).filter (fun i => yes.get i)).toFinset =
      ArrayCompositeAlgorithm.decode yes := by
    ext i
    simp [ArrayCompositeAlgorithm.mem_decode]
  have hd := (List.nodup_finRange I).filter (fun i => yes.get i)
  rw [scatter_writes_countP, List.countP_eq_length_filter, ← he]
  exact (List.toFinset_card_of_nodup hd).symm

structure ResourceParts where
  backendWork : ℕ
  controllerVisits : ℕ
  originalSumTests : ℕ
  finalVisits : ℕ
  setupVisits : ℕ
  denseAnswerWrites : ℕ
  finalScatterWrites : ℕ

def ResourceParts.total (p : ResourceParts) : ℕ :=
  p.backendWork+p.controllerVisits+p.originalSumTests+p.finalVisits+p.setupVisits

structure Result (n h : ℕ) (Payload : Type) where
  answers : BoolTable n
  active : ArrayCompositeAlgorithm.Flags (incidenceSize n h)
  marked : ArrayCompositeAlgorithm.Flags (n*n)
  calls : List (CountedArrayComposite.Call (incidenceSize n h) Payload)
  resources : ResourceParts

def finalize {n h P : ℕ} {Payload : Type}
    (controller : CountedArrayComposite.StageResult P (incidenceSize n h) (n*n) Payload)
    (A B T : IntTable n) : Result n h Payload :=
  let scans := finalScans A B T controller.active
  let yes := scanAnswers scans
  let marked := scatter (ownerTable n h) yes controller.marked (List.finRange (incidenceSize n h))
  { answers := store (fun i j => marked.flags.get (finProdFinEquiv (i,j)))
    active := controller.active
    marked := marked.flags
    calls := controller.calls
    resources :=
      { backendWork := controller.backendWork
        controllerVisits := controller.controllerVisits
        originalSumTests := scanTests scans
        finalVisits := 2*incidenceSize n h+marked.visits+n*n
        setupVisits := P+3*incidenceSize n h+n*n
        denseAnswerWrites := n*n
        finalScatterWrites := marked.writes } }

def solveReference {n h U : ℕ} {Payload : Type} (backend : Backend n h Payload)
    (parameters : CompleteAPSP.Parameters h U) (A B T : IntTable n) : Result n h Payload :=
  finalize (restarts backend parameters A B T) A B T

def solve {n h U : ℕ} {Payload : Type} (backend : Backend n h Payload)
    (parameters : CompleteAPSP.Parameters h U) (A B T : IntTable n) : Result n h Payload :=
  let controller := restartsExec backend parameters A B T
  let out := finalize controller.value A B T
  { out with resources := {out.resources with controllerVisits := controller.sites} }

theorem solve_refines {n h U : ℕ} {Payload : Type} (backend : Backend n h Payload)
    (parameters : CompleteAPSP.Parameters h U) (A B T : IntTable n) :
    solve backend parameters A B T =
      { solveReference backend parameters A B T with
        resources := {(solveReference backend parameters A B T).resources with
          controllerVisits := (restartsExec backend parameters A B T).sites} } := by
  simp only [solve, restartsExec_value, solveReference]

theorem solve_answers_value {n h U : ℕ} {Payload : Type} (backend : Backend n h Payload)
    (parameters : CompleteAPSP.Parameters h U) (A B T : IntTable n) :
    (solve backend parameters A B T).answers = (solveReference backend parameters A B T).answers := by
  rw [solve_refines]

theorem solve_calls_value {n h U : ℕ} {Payload : Type} (backend : Backend n h Payload)
    (parameters : CompleteAPSP.Parameters h U) (A B T : IntTable n) :
    (solve backend parameters A B T).calls = (solveReference backend parameters A B T).calls := by
  rw [solve_refines]

theorem solve_backendWork_value {n h U : ℕ} {Payload : Type} (backend : Backend n h Payload)
    (parameters : CompleteAPSP.Parameters h U) (A B T : IntTable n) :
    (solve backend parameters A B T).resources.backendWork =
      (solveReference backend parameters A B T).resources.backendWork := by rw [solve_refines]

theorem solve_originalSumTests_value {n h U : ℕ} {Payload : Type} (backend : Backend n h Payload)
    (parameters : CompleteAPSP.Parameters h U) (A B T : IntTable n) :
    (solve backend parameters A B T).resources.originalSumTests =
      (solveReference backend parameters A B T).resources.originalSumTests := by rw [solve_refines]

theorem solve_finalVisits_value {n h U : ℕ} {Payload : Type} (backend : Backend n h Payload)
    (parameters : CompleteAPSP.Parameters h U) (A B T : IntTable n) :
    (solve backend parameters A B T).resources.finalVisits =
      (solveReference backend parameters A B T).resources.finalVisits := by rw [solve_refines]

theorem solve_setupVisits_value {n h U : ℕ} {Payload : Type} (backend : Backend n h Payload)
    (parameters : CompleteAPSP.Parameters h U) (A B T : IntTable n) :
    (solve backend parameters A B T).resources.setupVisits =
      (solveReference backend parameters A B T).resources.setupVisits := by rw [solve_refines]

theorem solve_denseAnswerWrites_value {n h U : ℕ} {Payload : Type} (backend : Backend n h Payload)
    (parameters : CompleteAPSP.Parameters h U) (A B T : IntTable n) :
    (solve backend parameters A B T).resources.denseAnswerWrites =
      (solveReference backend parameters A B T).resources.denseAnswerWrites := by rw [solve_refines]

theorem solve_finalScatterWrites_value {n h U : ℕ} {Payload : Type} (backend : Backend n h Payload)
    (parameters : CompleteAPSP.Parameters h U) (A B T : IntTable n) :
    (solve backend parameters A B T).resources.finalScatterWrites =
      (solveReference backend parameters A B T).resources.finalScatterWrites := by rw [solve_refines]

theorem solve_controllerVisits_value {n h U : ℕ} {Payload : Type} (backend : Backend n h Payload)
    (parameters : CompleteAPSP.Parameters h U) (A B T : IntTable n) :
    (solve backend parameters A B T).resources.controllerVisits =
      (restartsExec backend parameters A B T).sites := rfl

theorem solve_correct {n h U : ℕ} {Payload : Type} (hh : 0 < h)
    (backend : Backend n h Payload) (parameters : CompleteAPSP.Parameters h U) (A B T : IntTable n)
    (hmag : ∀ i k, k ∈ (flatInstance (h := h) A B T).block i →
      ((flatInstance (h := h) A B T).value i k).natAbs ≤ U) (i j : Fin n) :
    decode (solve backend parameters A B T).answers i j = true ↔
      ∃ k, decode A i k+decode B k j+decode T i j=0 := by
  rw [solve_answers_value]
  have hc := restarts_correct hh backend parameters A B T hmag
  have hm := finalScans_mark_correct hh A B T
    (restarts backend parameters A B T).active (restarts backend parameters A B T).marked
  have hf := ArrayCompositeAlgorithm.final_scan_of_invariant (flatInstance (h := h) A B T)
    (ownerTable n h) (ArrayCompositeAlgorithm.decode (initialFlags n h))
    (restarts backend parameters A B T).active (restarts backend parameters A B T).marked hc.1
  have hmem := Finset.ext_iff.mp (hm.trans hf) (finProdFinEquiv (i,j))
  simpa only [solveReference, finalize, decode_store, scatter_value, ArrayCompositeAlgorithm.mark,
    ArrayCompositeAlgorithm.mem_decode] using hmem.trans (initial_exactPairs_zero hh A B T i j)

theorem solve_backendWork {n h U : ℕ} {Payload : Type} (backend : Backend n h Payload)
    (parameters : CompleteAPSP.Parameters h U) (A B T : IntTable n) :
    (solve backend parameters A B T).resources.backendWork =
      CountedArrayComposite.workSum (solve backend parameters A B T).calls := by
  rw [solve_backendWork_value, solve_calls_value]
  exact CountedArrayComposite.restarts_backendWork _ _ _ _ _ _ _ _ _ _

theorem solve_provenance {n h U : ℕ} {Payload : Type} (backend : Backend n h Payload)
    (parameters : CompleteAPSP.Parameters h U) (A B T : IntTable n) :
    ∀ call ∈ (solve backend parameters A B T).calls,
      call.result = (backend.oracle A B T).table
        call.factors.selected call.factors.candidate call.factors.active := by
  rw [solve_calls_value]
  exact CountedArrayComposite.restarts_retained_results _ _ _ _ _ _ _ _ _ _

theorem solve_work_measure {n h U : ℕ} {Payload : Type} (backend : Backend n h Payload)
    (measure : Payload → ℕ) (parameters : CompleteAPSP.Parameters h U) (A B T : IntTable n)
    (hmeasure : (backend.oracle A B T).WorkMatches measure) :
    (solve backend parameters A B T).resources.backendWork =
      ((solve backend parameters A B T).calls.map (fun call => measure call.result.payload)).sum := by
  rw [solve_backendWork_value, solve_calls_value]
  exact CountedArrayComposite.restarts_work_measure _ measure hmeasure _ _ _ _ _ _ _ _ _

theorem solve_calls_bound {n h U : ℕ} {Payload : Type} (backend : Backend n h Payload)
    (parameters : CompleteAPSP.Parameters h U) (A B T : IntTable n) :
    (solve backend parameters A B T).calls.length ≤ parameters.stages*(parameters.k+1)*parameters.pool.card := by
  rw [solve_calls_value]
  exact CountedArrayComposite.restarts_calls_bound _ _ _ _ _ _ _ _ _ _

theorem solve_scan_budget {n h U : ℕ} {Payload : Type} (hh : 0 < h) (hhn : h ≤ n)
    (backend : Backend n h Payload) (parameters : CompleteAPSP.Parameters h U)
    (hs : (2*n).size ≤ parameters.stages) (A B T : IntTable n)
    (hmag : ∀ i k, k ∈ (flatInstance (h := h) A B T).block i →
      ((flatInstance (h := h) A B T).value i k).natAbs ≤ U) :
    (solve backend parameters A B T).resources.originalSumTests ≤ n^2 := by
  rw [solve_originalSumTests_value]
  have hc := (restarts_correct hh backend parameters A B T hmag).2
  have hb := CompactStoredAPSP.scan_budget hhn hs
  change scanTests (finalScans A B T (restarts backend parameters A B T).active) ≤ _
  rw [scanTests_eq]
  apply Nat.le_of_mul_le_mul_left (c := 2^parameters.stages) ?_ (by positivity)
  calc
    _ = h*(2^parameters.stages*(ArrayCompositeAlgorithm.decode
        (restarts backend parameters A B T).active).card) := by ring
    _ ≤ h*(n^2*CompactBlocks.blockCount n h) := Nat.mul_le_mul_left h hc
    _ = h*n^2*CompactBlocks.blockCount n h := by ring
    _ ≤ _ := hb

theorem solve_final_visits {n h U : ℕ} {Payload : Type} (backend : Backend n h Payload)
    (parameters : CompleteAPSP.Parameters h U) (A B T : IntTable n) :
    (solve backend parameters A B T).resources.finalVisits = 3*incidenceSize n h+n*n := by
  rw [solve_finalVisits_value]
  simp only [solveReference, finalize, scatter_visits, List.length_finRange]
  ring

theorem solve_denseAnswerWrites {n h U : ℕ} {Payload : Type} (backend : Backend n h Payload)
    (parameters : CompleteAPSP.Parameters h U) (A B T : IntTable n) :
    (solve backend parameters A B T).resources.denseAnswerWrites = n*n := by
  rw [solve_denseAnswerWrites_value]
  rfl

theorem solve_setup_visits {n h U : ℕ} {Payload : Type} (backend : Backend n h Payload)
    (parameters : CompleteAPSP.Parameters h U) (A B T : IntTable n) :
    (solve backend parameters A B T).resources.setupVisits =
      parameters.pool.card+3*incidenceSize n h+n*n := by
  rw [solve_setupVisits_value]
  rfl

theorem solve_finalScatterWrites {n h U : ℕ} {Payload : Type} (backend : Backend n h Payload)
    (parameters : CompleteAPSP.Parameters h U) (A B T : IntTable n) :
    (solve backend parameters A B T).resources.finalScatterWrites ≤ incidenceSize n h := by
  rw [solve_finalScatterWrites_value]
  simpa only [solveReference, finalize, List.length_finRange] using scatter_writes_le (ownerTable n h)
    (scanAnswers (finalScans A B T (restarts backend parameters A B T).active))
    (restarts backend parameters A B T).marked (List.finRange (incidenceSize n h))

theorem solve_scatter_budget {n h U : ℕ} {Payload : Type} (hh : 0 < h) (hhn : h ≤ n)
    (backend : Backend n h Payload) (parameters : CompleteAPSP.Parameters h U)
    (hs : (2*n).size ≤ parameters.stages) (A B T : IntTable n)
    (hmag : ∀ i k, k ∈ (flatInstance (h := h) A B T).block i →
      ((flatInstance (h := h) A B T).value i k).natAbs ≤ U) :
    (solve backend parameters A B T).resources.finalScatterWrites ≤ n^2 := by
  rw [solve_finalScatterWrites_value]
  have hsub : ArrayCompositeAlgorithm.decode
      (scanAnswers (finalScans A B T (restarts backend parameters A B T).active)) ⊆
      ArrayCompositeAlgorithm.decode (restarts backend parameters A B T).active := by
    intro i hi
    simp only [ArrayCompositeAlgorithm.mem_decode, scanAnswers, finalScans, Vector.get_ofFn] at hi ⊢
    by_contra hn
    have hf := Bool.eq_false_iff.mpr hn
    simp only [hf, Bool.false_eq_true, if_false] at hi
  have hc := Finset.card_le_card hsub
  have ht := solve_scan_budget hh hhn backend parameters hs A B T hmag
  have he : (solve backend parameters A B T).resources.originalSumTests =
      h*(ArrayCompositeAlgorithm.decode (restarts backend parameters A B T).active).card := by
    rw [solve_originalSumTests_value]
    exact scanTests_eq A B T _
  change (scatter (ownerTable n h)
    (scanAnswers (finalScans A B T (restarts backend parameters A B T).active))
    (restarts backend parameters A B T).marked (List.finRange (incidenceSize n h))).writes ≤ _
  rw [scatter_writes_card]
  rw [he] at ht
  nlinarith

theorem solve_controllerVisits_reference {n h U : ℕ} {Payload : Type} (backend : Backend n h Payload)
    (parameters : CompleteAPSP.Parameters h U) (A B T : IntTable n) :
    (solve backend parameters A B T).resources.controllerVisits ≤
      256*(parameters.k+1)*(parameters.k+2)*
        (solveReference backend parameters A B T).resources.controllerVisits+1 := by
  have hp : 0 < parameters.pool.card := by
    have ht := parameters.threshold
    have hs := parameters.size
    omega
  have hx := DenseControllerExecution.restartsExec_sites_by_visits (backend.oracle A B T)
    (ownerTable n h) (primeVector parameters.pool) (blockSizeTable n h)
    (Vector.replicate parameters.pool.card true) parameters.k parameters.lam parameters.stages
    (initialFlags n h) (Vector.replicate (n*n) false) hp
  change (restartsExec backend parameters A B T).sites ≤ _
  change (restartsExec backend parameters A B T).sites ≤
    256*(parameters.k+1)*(parameters.k+2)*(restartsExec backend parameters A B T).value.controllerVisits+1 at hx
  rw [restartsExec_value] at hx
  exact hx

theorem solve_controllerVisits {n h U : ℕ} {Payload : Type} (backend : Backend n h Payload)
    (parameters : CompleteAPSP.Parameters h U) (A B T : IntTable n) :
    (solve backend parameters A B T).resources.controllerVisits ≤
      256*(parameters.k+1)*(parameters.k+2)*(parameters.stages*
        (parameters.k*CountedArrayComposite.batchVisits parameters.pool.card (incidenceSize n h)+
          CountedArrayComposite.finalVisits parameters.pool.card (incidenceSize n h)))+1 := by
  have hv := CountedArrayComposite.restarts_visits_bound (backend.oracle A B T)
    (ownerTable n h) (primeVector parameters.pool) (blockSizeTable n h)
    (Vector.replicate parameters.pool.card true) parameters.k parameters.lam parameters.stages
    (initialFlags n h) (Vector.replicate (n*n) false)
  exact (solve_controllerVisits_reference backend parameters A B T).trans
    (Nat.add_le_add_right (Nat.mul_le_mul_left _ hv) _)

theorem solve_factors_length {n h U : ℕ} {Payload : Type} (backend : Backend n h Payload)
    (parameters : CompleteAPSP.Parameters h U) (A B T : IntTable n) :
    ∀ call ∈ (solve backend parameters A B T).calls,
      call.factors.selected.length+1 ≤ parameters.k+1 := by
  rw [solve_calls_value]
  exact CountedArrayComposite.restarts_factors_length_le _ _ _ _ _ _ _ _ _ _

theorem solve_valid_histories {n h U : ℕ} {Payload : Type} (backend : Backend n h Payload)
    (parameters : CompleteAPSP.Parameters h U) (A B T : IntTable n)
    (hthree : ∀ p ∈ parameters.pool, p ≠ 3) :
    ∀ call ∈ (solve backend parameters A B T).calls,
      ValidFactors (call.factors.selected ++ [call.factors.candidate]) := by
  have hd := CountedArrayComposite.restarts_factors_distinct (backend.oracle A B T)
    (ownerTable n h) (primeVector parameters.pool) (primeVector_injective parameters.pool)
    (blockSizeTable n h) (Vector.replicate parameters.pool.card true)
    parameters.k parameters.lam parameters.stages (initialFlags n h) (Vector.replicate (n*n) false)
  have hp := CountedArrayComposite.restarts_factors_property (backend.oracle A B T)
    (ownerTable n h) (primeVector parameters.pool) (fun p => Nat.Prime p ∧ p ≠ 3)
    (fun i => ⟨parameters.prime _ (primeVector_mem _ i), hthree _ (primeVector_mem _ i)⟩)
    (blockSizeTable n h) (Vector.replicate parameters.pool.card true)
    parameters.k parameters.lam parameters.stages (initialFlags n h) (Vector.replicate (n*n) false)
  intro call hc
  rw [solve_calls_value] at hc
  exact ⟨hd call hc, hp call hc⟩

theorem solve_factor_membership {n h U : ℕ} {Payload : Type} (backend : Backend n h Payload)
    (parameters : CompleteAPSP.Parameters h U) (A B T : IntTable n) :
    ∀ call ∈ (solve backend parameters A B T).calls,
      ∀ p ∈ call.factors.selected ++ [call.factors.candidate], p ∈ parameters.pool := by
  rw [solve_calls_value]
  exact CountedArrayComposite.restarts_factors_property (backend.oracle A B T) (ownerTable n h)
    (primeVector parameters.pool) (fun p => p ∈ parameters.pool) (primeVector_mem parameters.pool)
    (blockSizeTable n h) (Vector.replicate parameters.pool.card true)
    parameters.k parameters.lam parameters.stages (initialFlags n h) (Vector.replicate (n*n) false)

abbrev CallbackPayload (n h : ℕ) (Payload : Type) := Option (Result n h Payload)

/-- Three scans of stored n-by-n inputs. The exhaustive incidence/label
magnitude used in specifications is deliberately not executed here. -/
def entryMagnitude {n : ℕ} (A B T : IntTable n) : ℕ :=
  max (Finset.univ.sup (fun p : Fin n × Fin n => (decode A p.1 p.2).natAbs))
    (max (Finset.univ.sup (fun p : Fin n × Fin n => (decode B p.1 p.2).natAbs))
      (Finset.univ.sup (fun p : Fin n × Fin n => (decode T p.1 p.2).natAbs)))

def entryQueryBound {n : ℕ} (A B T : IntTable n) : ℕ := 3*entryMagnitude A B T+1

theorem entryMagnitude_bounds {n : ℕ} (A B T : IntTable n) (i j : Fin n) :
    (decode A i j).natAbs ≤ entryMagnitude A B T ∧
    (decode B i j).natAbs ≤ entryMagnitude A B T ∧
    (decode T i j).natAbs ≤ entryMagnitude A B T := by
  have ha := Finset.le_sup (f := fun p : Fin n × Fin n => (decode A p.1 p.2).natAbs)
    (b := (i,j)) (Finset.mem_univ _)
  have hb := Finset.le_sup (f := fun p : Fin n × Fin n => (decode B p.1 p.2).natAbs)
    (b := (i,j)) (Finset.mem_univ _)
  have ht := Finset.le_sup (f := fun p : Fin n × Fin n => (decode T p.1 p.2).natAbs)
    (b := (i,j)) (Finset.mem_univ _)
  exact ⟨ha.trans (Nat.le_max_left _ _),
    hb.trans ((Nat.le_max_left _ _).trans (Nat.le_max_right _ _)),
    ht.trans ((Nat.le_max_right _ _).trans (Nat.le_max_right _ _))⟩

theorem entryMagnitude_le {n W : ℕ} (A B T : IntTable n)
    (hb : APSPAlgorithm.SymmetricQueryBound (decode A,decode B,decode T) W) :
    entryMagnitude A B T ≤ W := by
  apply max_le
  · exact Finset.sup_le (fun p _ => CompleteAPSP.natAbs_of_symmetric (hb.1 p.1 p.2))
  · apply max_le
    · exact Finset.sup_le (fun p _ => CompleteAPSP.natAbs_of_symmetric (hb.2.1 p.1 p.2))
    · exact Finset.sup_le (fun p _ => CompleteAPSP.natAbs_of_symmetric (hb.2.2 p.1 p.2))

theorem entryQueryBound_flat {n h : ℕ} (A B T : IntTable n)
    (i : Fin (incidenceSize n h)) (k : Fin n) :
    ((flatInstance (h := h) A B T).value i k).natAbs ≤ entryQueryBound A B T := by
  have hm := CompleteAPSP.triangle_magnitude_bound (CompactBlocks.block n h)
    (decode A) (decode B) (decode T) (entryMagnitude A B T)
    (fun i k => (entryMagnitude_bounds A B T i k).1)
    (fun k j => (entryMagnitude_bounds A B T k j).2.1)
    (fun i j => (entryMagnitude_bounds A B T i j).2.2)
  exact (CompleteAPSP.magnitude_bound
    (CompleteAPSP.incidenceInstance (CompactBlocks.block n h) (decode A) (decode B) (decode T))
    ((incidenceEquiv n h).symm i) k).trans hm

def chargeCapScan {n h : ℕ} {Payload : Type} (out : Result n h Payload) : Result n h Payload :=
  { out with resources := {out.resources with setupVisits := out.resources.setupVisits+3*n*n} }

/-- Both finite-size failure and an out-of-cap callback use the real direct
scan. There is no factorial-size reference-prime fallback in this module. -/
def direct {n h : ℕ} {Payload : Type} : DenseOracle n (CallbackPayload n h Payload) :=
  fun A B T =>
    let out := EndToEndAPSP.directCallback n A B T
    { answers := out.answers, payload := none, work := out.work, answerWrites := out.answerWrites }

theorem direct_correct {n h : ℕ} {Payload : Type} :
    DenseOracleCorrect (direct (n := n) (h := h) (Payload := Payload)) :=
  EndToEndAPSP.directCallback_correct n

def callback {n h U : ℕ} {Payload : Type} (backend : Backend n h Payload)
    (parameters : CompleteAPSP.Parameters h U) : DenseOracle n (CallbackPayload n h Payload) :=
  fun A B T =>
    if hcap : entryQueryBound A B T ≤ U then
      let out := chargeCapScan (solve backend (parameters.weaken hcap) A B T)
      { answers := out.answers
        payload := some out
        work := out.resources.total
        answerWrites := n*n+out.resources.denseAnswerWrites+out.resources.finalScatterWrites }
    else
      let out := direct A B T
      { out with work := out.work+3*n*n }

theorem callback_correct {n h U : ℕ} {Payload : Type} (hh : 0 < h)
    (backend : Backend n h Payload) (parameters : CompleteAPSP.Parameters h U) :
    DenseOracleCorrect (callback backend parameters) := by
  intro A B T i j
  unfold callback
  split_ifs with hcap
  · exact solve_correct hh backend (parameters.weaken hcap) A B T
      (fun x k _hk => entryQueryBound_flat A B T x k) i j
  · exact direct_correct (h := h) (Payload := Payload) A B T i j

def fromConfiguration {n : ℕ} {Payload : Type}
    (backend : Backend n (ComputableParameters.block n) Payload) (W : ℕ)
    (configuration : Option (CompleteAPSP.Parameters (ComputableParameters.block n) (magnitudeCap n W))) :
    DenseOracle n (CallbackPayload n (ComputableParameters.block n) Payload) :=
  match configuration with
  | none => direct
  | some parameters => callback backend parameters

theorem fromConfiguration_correct {n : ℕ} {Payload : Type}
    (backend : Backend n (ComputableParameters.block n) Payload) (W : ℕ)
    (configuration : Option (CompleteAPSP.Parameters (ComputableParameters.block n) (magnitudeCap n W))) :
    DenseOracleCorrect (fromConfiguration backend W configuration) := by
  cases configuration with
  | none => exact direct_correct
  | some parameters => exact callback_correct (block_pos n) backend parameters

def run {n : ℕ} {Payload : Type} (backend : Backend n (ComputableParameters.block n) Payload)
    (w : OptionalTable n) (W : ℕ) :
    Execution n (Option ℤ) (CallbackPayload n (ComputableParameters.block n) Payload) :=
  let configuration := ComputableParameters.program n (magnitudeCap n W)
  let oracle := fromConfiguration backend W configuration
  StoredMinPlusAPSP.apsp oracle w W

theorem run_correct {n : ℕ} {Payload : Type} (backend : Backend n (ComputableParameters.block n) Payload)
    (w : OptionalTable n) (W : ℕ) (hw : APSPReduction.EdgeBound (decode w) W)
    (hno : APSPReduction.NoNegativeCycles (decode w)) :
    APSPReduction.IsAPSP (decode w) (decode (run backend w W).value) :=
  StoredMinPlusAPSP.apsp_correct _ (fromConfiguration_correct backend W _) w W hw hno

theorem run_calls_faithful {n : ℕ} {Payload : Type}
    (backend : Backend n (ComputableParameters.block n) Payload) (w : OptionalTable n) (W : ℕ)
    (c : Call n (CallbackPayload n (ComputableParameters.block n) Payload))
    (hc : c ∈ (run backend w W).calls) :
    c.output = fromConfiguration backend W (ComputableParameters.program n (magnitudeCap n W))
      c.left c.right c.target :=
  StoredMinPlusAPSP.apsp_calls_faithful _ w W c hc

theorem run_actual_call_magnitude {n : ℕ} {Payload : Type}
    (backend : Backend n (ComputableParameters.block n) Payload) (w : OptionalTable n) (W : ℕ)
    (hw : APSPReduction.EdgeBound (decode w) W)
    (c : Call n (CallbackPayload n (ComputableParameters.block n) Payload))
    (hc : c ∈ (run backend w W).calls) :
    CompactStoredAPSP.inputMagnitude (ComputableParameters.block n) c.left c.right c.target ≤
      magnitudeCap n W := by
  have hb := StoredMinPlusAPSP.apsp_query_bound
    (fromConfiguration backend W (ComputableParameters.program n (magnitudeCap n W)))
    (fromConfiguration_correct backend W _) w W hw c hc
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

theorem run_actual_entryQueryBound {n : ℕ} {Payload : Type}
    (backend : Backend n (ComputableParameters.block n) Payload) (w : OptionalTable n) (W : ℕ)
    (hw : APSPReduction.EdgeBound (decode w) W)
    (c : Call n (CallbackPayload n (ComputableParameters.block n) Payload))
    (hc : c ∈ (run backend w W).calls) : entryQueryBound c.left c.right c.target ≤ magnitudeCap n W := by
  have hb := StoredMinPlusAPSP.apsp_query_bound
    (fromConfiguration backend W (ComputableParameters.program n (magnitudeCap n W)))
    (fromConfiguration_correct backend W _) w W hw c hc
  have he := entryMagnitude_le c.left c.right c.target hb
  unfold entryQueryBound magnitudeCap
  nlinarith

/-- A callback output and all its retained producer returns belong to the
same joint execution. Neither the callback nor a backend table is replayed
by an executable counter definition. -/
theorem run_successful_call {n : ℕ} {Payload : Type} (hn : 2 ≤ n)
    (backend : Backend n (ComputableParameters.block n) Payload) (w : OptionalTable n) (W : ℕ)
    (parameters : CompleteAPSP.Parameters (ComputableParameters.block n) (magnitudeCap n W))
    (hp : ComputableParameters.program n (magnitudeCap n W) = some parameters)
    (hw : APSPReduction.EdgeBound (decode w) W)
    (c : Call n (CallbackPayload n (ComputableParameters.block n) Payload))
    (hc : c ∈ (run backend w W).calls) :
    ∃ out : Result n (ComputableParameters.block n) Payload,
      c.output.payload = some out ∧ c.output.work = out.resources.total ∧
      out.resources.backendWork = CountedArrayComposite.workSum out.calls ∧
      out.calls.length ≤ parameters.stages*(parameters.k+1)*parameters.pool.card ∧
      out.resources.originalSumTests ≤ n^2 ∧
      out.resources.denseAnswerWrites = n*n ∧
      out.resources.finalScatterWrites ≤ n^2 ∧ c.output.answerWrites ≤ 3*n*n ∧
      ∀ call ∈ out.calls,
        call.result = (backend.oracle c.left c.right c.target).table
          call.factors.selected call.factors.candidate call.factors.active ∧
        ValidFactors (call.factors.selected ++ [call.factors.candidate]) ∧
        call.factors.selected.length+1 ≤ ComputableParameters.factorCount ∧
        ∀ q ∈ call.factors.selected ++ [call.factors.candidate], q ∈ parameters.pool := by
  have hcap := run_actual_entryQueryBound backend w W hw c hc
  let p := parameters.weaken hcap
  let out := chargeCapScan (solve backend p c.left c.right c.target)
  have hf := run_calls_faithful backend w W c hc
  rw [hp] at hf
  have hpayload : c.output.payload = some out := by
    rw [hf]
    simp only [fromConfiguration, callback, dif_pos hcap]
    rfl
  have hwork : c.output.work = out.resources.total := by
    rw [hf]
    simp only [fromConfiguration, callback, dif_pos hcap]
    rfl
  have hwrites : c.output.answerWrites = n*n+out.resources.denseAnswerWrites+out.resources.finalScatterWrites := by
    rw [hf]
    simp only [fromConfiguration, callback, dif_pos hcap]
    rfl
  have hmag : ∀ i k, k ∈ (flatInstance (h := ComputableParameters.block n) c.left c.right c.target).block i →
      ((flatInstance (h := ComputableParameters.block n) c.left c.right c.target).value i k).natAbs ≤
        entryQueryBound c.left c.right c.target := fun i k _ => entryQueryBound_flat _ _ _ i k
  have hs : (2*n).size ≤ p.stages := (success_configuration n W parameters hp).2.2.2.2.2.ge
  have hthree : ∀ q ∈ p.pool, q ≠ 3 := by
    intro q hq
    change q ∈ parameters.pool at hq
    rw [(success_configuration n W parameters hp).1] at hq
    exact fun heq => (Finset.mem_sdiff.mp hq).2 (by simp only [heq, Finset.mem_singleton])
  have hscatter := solve_scatter_budget (block_pos n) (ComputableParameters.block_le_n n hn)
    backend p hs c.left c.right c.target hmag
  refine ⟨out, hpayload, hwork, solve_backendWork backend p _ _ _,
    solve_calls_bound backend p _ _ _, ?_, rfl, hscatter, ?_, ?_⟩
  · exact solve_scan_budget (block_pos n) (ComputableParameters.block_le_n n hn)
      backend p hs c.left c.right c.target hmag
  · rw [hwrites]
    change n*n+n*n+out.resources.finalScatterWrites ≤ _
    change out.resources.finalScatterWrites ≤ n^2 at hscatter
    nlinarith
  · intro call hcall
    refine ⟨solve_provenance backend p _ _ _ call hcall,
      solve_valid_histories backend p _ _ _ hthree call hcall, ?_,
      solve_factor_membership backend p _ _ _ call hcall⟩
    have hl := solve_factors_length backend p _ _ _ call hcall
    have hk := (success_configuration n W parameters hp).2.2.2.1
    have he : p.k+1 = ComputableParameters.factorCount := by
      change parameters.k+1 = _
      rw [hk]
      norm_num [ComputableParameters.factorCount]
    exact hl.trans_eq he

#print axioms restarts_correct
#print axioms restartsExec_value
#print axioms solve_refines
#print axioms solve_controllerVisits_value
#print axioms scatter_value
#print axioms scatter_visits
#print axioms scatter_writes_le
#print axioms scatter_writes_countP
#print axioms scatter_writes_card
#print axioms solve_correct
#print axioms solve_backendWork
#print axioms solve_provenance
#print axioms solve_work_measure
#print axioms solve_calls_bound
#print axioms solve_scan_budget
#print axioms solve_final_visits
#print axioms solve_denseAnswerWrites
#print axioms solve_setup_visits
#print axioms solve_finalScatterWrites
#print axioms solve_scatter_budget
#print axioms solve_controllerVisits
#print axioms solve_controllerVisits_reference
#print axioms solve_factors_length
#print axioms solve_valid_histories
#print axioms solve_factor_membership
#print axioms entryMagnitude_bounds
#print axioms entryMagnitude_le
#print axioms entryQueryBound_flat
#print axioms direct_correct
#print axioms callback_correct
#print axioms fromConfiguration_correct
#print axioms run_correct
#print axioms run_calls_faithful
#print axioms run_actual_call_magnitude
#print axioms run_actual_entryQueryBound
#print axioms run_successful_call

end ThinMatrix.CountedEndToEndAPSP
