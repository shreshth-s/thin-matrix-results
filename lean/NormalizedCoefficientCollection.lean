import FoldedRequestBounds

set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 2400000

/-! Copy each original request's selected cyclic coefficient from the actual
retained normalized outputs. Equal requests remain distinct array entries. -/
namespace ThinMatrix.NormalizedCoefficientCollection
open BinaryCell BinaryGroupedCoordinates BinaryGroupedPreparation
open FoldedBandTransport FoldedRequestBounds
open scoped BigOperators

def extract {L m q M : ℕ} (requests : Vector (GraphCompletionRequests.Physical L m q) M)
    (values : Vector (Vector BinaryLowHighNormalize.CellOutput q) M) : Run (Vector Cell M) :=
  tabulate requests fun i =>
    let out := copy (BinaryLowHighNormalize.output values i (requests.get i).coefficient)
    ⟨out.value,out.bitSteps,8⟩

theorem extract_value {L m q M : ℕ} (requests : Vector (GraphCompletionRequests.Physical L m q) M)
    (values : Vector (Vector BinaryLowHighNormalize.CellOutput q) M) (i : Fin M) :
    view ((extract requests values).value.get i)=view (BinaryLowHighNormalize.output values i (requests.get i).coefficient) := by
  simp only [extract,tabulate_get,copy_view]

theorem extract_bits {L m q M : ℕ} (requests : Vector (GraphCompletionRequests.Physical L m q) M)
    (values : Vector (Vector BinaryLowHighNormalize.CellOutput q) M) (A : ℕ)
    (ha : ∀ i, (view (BinaryLowHighNormalize.output values i (requests.get i).coefficient)).natAbs≤A) :
    (extract requests values).bitSteps≤M*BackendScalarBits.backendScalarUnit A.size := by
  apply tabulate_bits
  intro i
  exact copy_price A.size _ (Nat.size_le_size (ha i))

theorem extract_control {L m q M : ℕ} (requests : Vector (GraphCompletionRequests.Physical L m q) M)
    (values : Vector (Vector BinaryLowHighNormalize.CellOutput q) M) :
    (extract requests values).control≤40*M+8 := by
  have he := tabulate_control requests (fun i =>
    let out := copy (BinaryLowHighNormalize.output values i (requests.get i).coefficient)
    (⟨out.value,out.bitSteps,8⟩ : Run Cell)) (W:=8) (fun _ => le_refl _)
  simpa only [extract,Nat.reduceAdd,Nat.mul_comm] using he

variable {n h r : ℕ}

def execute (f : CompactBlocks.PhysicalFactorization r) (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f)
    (block : Fin (CompactBlocks.blockCount n h)) (input : BinaryFoldedFormation.Inputs n) (bandL bandR ell : ℕ) :=
  let graph := GraphPrefixProgram.fromInputs f p block input bandL bandR ell
  let completed := GraphNormalizedBand.execute graph input.target bandL bandR
  let extracted := extract completed.2.1.1.physical.value completed.2.2.2.2.2.value
  (graph,completed,extracted)

theorem execute_value (f : CompactBlocks.PhysicalFactorization r) (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f)
    (block : Fin (CompactBlocks.blockCount n h)) (input : BinaryFoldedFormation.Inputs n) (bandL bandR ell : ℕ)
    (index : Fin (FoldedBackendExecution.windowQuerySize n)) :
    view ((execute f p block input bandL bandR ell).2.2.value.get index)=
      if (physical f p input.target index).bandL=bandL ∧ (physical f p input.target index).bandR=bandR then
        count f block input index else 0 := by
  simp only [execute,extract_value]
  change view (GraphNormalizedBand.output (GraphPrefixProgram.fromInputs f p block input bandL bandR ell) input.target bandL bandR
    index (LowRequestLocator.physical (GraphPrefixProgram.fromInputs f p block input bandL bandR ell) input.target index).coefficient)=_
  rw [physical_fromInputs]
  exact normalized_value f p block input bandL bandR ell index

theorem execute_bound (f : CompactBlocks.PhysicalFactorization r) (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f)
    (block : Fin (CompactBlocks.blockCount n h)) (input : BinaryFoldedFormation.Inputs n) (bandL bandR ell : ℕ)
    (index : Fin (FoldedBackendExecution.windowQuerySize n)) :
    (view ((execute f p block input bandL bandR ell).2.2.value.get index)).natAbs≤h := by
  rw [execute_value]
  split_ifs
  · exact count_bound f block input index
  · simp

theorem execute_extraction_bits (f : CompactBlocks.PhysicalFactorization r) (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f)
    (block : Fin (CompactBlocks.blockCount n h)) (input : BinaryFoldedFormation.Inputs n) (bandL bandR ell : ℕ) :
    (execute f p block input bandL bandR ell).2.2.bitSteps≤
      FoldedBackendExecution.windowQuerySize n*BackendScalarBits.backendScalarUnit h.size := by
  apply extract_bits
  intro i
  change (view (GraphNormalizedBand.output (GraphPrefixProgram.fromInputs f p block input bandL bandR ell) input.target bandL bandR
    i (LowRequestLocator.physical (GraphPrefixProgram.fromInputs f p block input bandL bandR ell) input.target i).coefficient)).natAbs≤h
  rw [physical_fromInputs]
  exact normalized_bound f p block input bandL bandR ell i

theorem execute_extraction_control (f : CompactBlocks.PhysicalFactorization r) (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f)
    (block : Fin (CompactBlocks.blockCount n h)) (input : BinaryFoldedFormation.Inputs n) (bandL bandR ell : ℕ) :
    (execute f p block input bandL bandR ell).2.2.control≤40*FoldedBackendExecution.windowQuerySize n+8 :=
  extract_control _ _

#print axioms extract_value
#print axioms extract_bits
#print axioms extract_control
#print axioms execute_value
#print axioms execute_bound
#print axioms execute_extraction_bits
#print axioms execute_extraction_control
end ThinMatrix.NormalizedCoefficientCollection
