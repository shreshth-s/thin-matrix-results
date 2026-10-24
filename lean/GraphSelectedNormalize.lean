import GraphOwnRootSpec
import FoldedRequestBounds

set_option autoImplicit false
set_option maxRecDepth 6000
set_option maxHeartbeats 1600000

/-! Normalize only the selected coefficient after the complete LOW/HIGH
numerator has been assembled. The M by B table has one entry per original
occurrence and middle block; no per-channel division is performed. -/
namespace ThinMatrix.GraphSelectedNormalize
open BinaryCell BinaryGroupedCoordinates
variable {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
  (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f)
abbrev M := FoldedBackendExecution.windowQuerySize n
abbrev B := CompactBlocks.blockCount n h
abbrev Rows := Vector (Vector Cell (B (n:=n) (h:=h))) (M (n:=n))

def execute (low high : Rows (n:=n) (h:=h)) := BinaryLowHighNormalize.table p.L low high

def output (low high : Rows (n:=n) (h:=h)) (j : Fin (M (n:=n))) (block : Fin (B (n:=n) (h:=h))) :=
  BinaryLowHighNormalize.output (execute f p low high).2.value j block

noncomputable def lowValue (input : BinaryFoldedFormation.Inputs n)
    (j : Fin (M (n:=n))) (block : Fin (B (n:=n) (h:=h))) : ℤ :=
  let q := GraphOwnRootSpec.physical f p input.target j
  view ((RootProductCollection.output (GraphLowMaskAssembly.execute
    (GraphOwnRootSpec.graph f p input block j) input.target q.bandL q.bandR).value j).get q.coefficient)

noncomputable def highValue (input : BinaryFoldedFormation.Inputs n)
    (j : Fin (M (n:=n))) (block : Fin (B (n:=n) (h:=h))) : ℤ :=
  let q := GraphOwnRootSpec.physical f p input.target j
  view ((CountedCyclicCollection.output (GraphHighFamily.execute
    (GraphOwnRootSpec.graph f p input block j) input.target q.bandL q.bandR).2.value j).get q.coefficient)

attribute [local irreducible] GraphPrefixProgram.fromInputs

theorem correct (input : BinaryFoldedFormation.Inputs n) (low high : Rows (n:=n) (h:=h))
    (hl : ∀ j block,view ((low.get j).get block)=lowValue f p input j block)
    (hh : ∀ j block,view ((high.get j).get block)=highValue f p input j block)
    (j : Fin (M (n:=n))) (block : Fin (B (n:=n) (h:=h))) :
    view (output f p low high j block)=FoldedRequestBounds.count f block input j := by
  have he := FoldedRequestBounds.normalized_value f p block input
    (GraphOwnRootSpec.physical f p input.target j).bandL
    (GraphOwnRootSpec.physical f p input.target j).bandR 0 j
  have hp : FoldedBandTransport.physical f p input.target j=GraphOwnRootSpec.physical f p input.target j := by
    unfold GraphOwnRootSpec.physical GraphSharedTargets.prepare
    rw [GraphCompletionRequests.prepare_get]
    rfl
  rw [hp] at he
  simp only [and_self,ite_true] at he
  change view (BinaryLowHighNormalize.output (BinaryLowHighNormalize.table p.L low high).2.value j block)=_
  rw [BinaryLowHighNormalize.table_value,hl,hh]
  simpa only [GraphNormalizedBand.output,GraphNormalizedBand.execute,
    BinaryLowHighNormalize.table_value,Vector.get_ofFn,lowValue,highValue,
    GraphOwnRootSpec.graph] using he

theorem bound (input : BinaryFoldedFormation.Inputs n) (low high : Rows (n:=n) (h:=h))
    (hl : ∀ j block,view ((low.get j).get block)=lowValue f p input j block)
    (hh : ∀ j block,view ((high.get j).get block)=highValue f p input j block)
    (j : Fin (M (n:=n))) (block : Fin (B (n:=n) (h:=h))) :
    (view (output f p low high j block)).natAbs≤h := by
  rw [correct f p input low high hl hh]
  exact FoldedRequestBounds.count_bound f block input j

theorem bits (low high : Rows (n:=n) (h:=h)) (A H : ℕ)
    (hl : ∀ j b,(view ((low.get j).get b)).natAbs≤A)
    (hh : ∀ j b,(view ((high.get j).get b)).natAbs≤H) :
    (execute f p low high).1.bitSteps+(execute f p low high).2.bitSteps≤
      p.L*BackendScalarBits.backendScalarUnit (2*p.L+3)+M (n:=n)*(B (n:=n) (h:=h)*BinaryLowHighNormalize.cellBudget p.L A H) :=
  BinaryLowHighNormalize.table_bits _ _ _ _ _ hl hh

theorem control (low high : Rows (n:=n) (h:=h)) :
    (execute f p low high).1.control+(execute f p low high).2.control≤
      8*p.L+1+M (n:=n)*(44*B (n:=n) (h:=h)+40)+8 :=
  BinaryLowHighNormalize.table_control _ _ _

#print axioms correct
#print axioms bound
#print axioms bits
#print axioms control
end ThinMatrix.GraphSelectedNormalize
