import GraphLowHighScale
import BinaryLowHighNormalize

set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 2400000

/-! Execute both retained families and normalize every cyclic coefficient.
This is a finite one-block/band-pair program. LOW arithmetic, indexed control,
and HIGH's existing mixed charge are explicit; shared graph preparation and
outer scheduling are not silently included in those charges. -/
namespace ThinMatrix.GraphNormalizedBand
open BinaryCell ExactHalfSourcePlan GoodMapEmbedding
open scoped BigOperators
variable {n h r b ell : ℕ} {f : CompactBlocks.PhysicalFactorization r}
  {p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f}

/-- The two row-reference arrays are materialized once. All child executions,
numerators, quotients and the shared binary divisor are retained. -/
def execute (graph : GraphPrefixProgram.Prepared f p b ell)
    (target : BinaryFoldedFormation.BinaryTable n) (bandL bandR : ℕ) :=
  let low := GraphLowMaskAssembly.execute graph target bandL bandR
  let high := GraphHighFamily.execute graph target bandL bandR
  let lowRows := Vector.ofFn (RootProductCollection.output low.value)
  let highRows := Vector.ofFn (CountedCyclicCollection.output high.2.value)
  let normalized := BinaryLowHighNormalize.table p.L lowRows highRows
  (low,high,lowRows,highRows,normalized)

def output (graph : GraphPrefixProgram.Prepared f p b ell)
    (target : BinaryFoldedFormation.BinaryTable n) (bandL bandR : ℕ)
    (request : Fin (FoldedBackendExecution.windowQuerySize n)) (residue : Fin f.cyclic) : Cell :=
  BinaryLowHighNormalize.output (execute graph target bandL bandR).2.2.2.2.2.value request residue

def bitSteps (graph : GraphPrefixProgram.Prepared f p b ell)
    (target : BinaryFoldedFormation.BinaryTable n) (bandL bandR : ℕ) : ℕ :=
  let out := execute graph target bandL bandR
  out.1.bitSteps+out.2.2.2.2.1.bitSteps+out.2.2.2.2.2.bitSteps

def control (graph : GraphPrefixProgram.Prepared f p b ell)
    (target : BinaryFoldedFormation.BinaryTable n) (bandL bandR : ℕ) : ℕ :=
  let out := execute graph target bandL bandR
  out.1.control+out.2.2.2.2.1.control+out.2.2.2.2.2.control+64*FoldedBackendExecution.windowQuerySize n+16

def highWork (graph : GraphPrefixProgram.Prepared f p b ell)
    (target : BinaryFoldedFormation.BinaryTable n) (bandL bandR : ℕ) : ℕ :=
  let high := (execute graph target bandL bandR).2.1
  high.1.folded.geometry.bitSteps+high.1.folded.requests.bitSteps+high.1.physical.bitSteps+
    high.1.physical.control+high.2.operations+16

noncomputable def lowMagnitude (L m t q : ℕ) : ℕ :=
  (goodSlots L m).card*((goodSlots L m).card*GraphLowMaskAssembly.pairMagnitude L m t q)
noncomputable def highMagnitude (L m t q : ℕ) : ℕ := J m*(J m*((2*m+1)*GraphHighRun.magnitude L m t q))

noncomputable def bitBudget (graph : GraphPrefixProgram.Prepared f p b ell)
    (target : BinaryFoldedFormation.BinaryTable n) : ℕ :=
  GraphLowMaskAssembly.bitBudget graph target+p.L*BackendScalarBits.backendScalarUnit (2*p.L+3)+
    FoldedBackendExecution.windowQuerySize n*(f.cyclic*BinaryLowHighNormalize.cellBudget p.L
      (lowMagnitude p.L p.m p.t f.cyclic) (highMagnitude p.L p.m p.t f.cyclic))

def controlBudget (graph : GraphPrefixProgram.Prepared f p b ell) : ℕ :=
  GraphLowMaskAssembly.controlBudget graph+8*p.L+1+
    FoldedBackendExecution.windowQuerySize n*(44*f.cyclic+40)+8+64*FoldedBackendExecution.windowQuerySize n+16

theorem fromInputs_value (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (bandL bandR ell : ℕ)
    (request : Fin (FoldedBackendExecution.windowQuerySize n)) (residue : Fin f.cyclic) :
    let graph := GraphPrefixProgram.fromInputs f p block input bandL bandR ell
    let q := LowRequestLocator.physical graph input.target request
    view (output graph input.target bandL bandR request residue)=
      if q.bandL=bandL ∧ q.bandR=bandR then GraphLowHighScale.entry graph input.target request residue else 0 := by
  letI : NeZero f.cyclic := ⟨Nat.ne_of_gt f.cyclic_pos⟩
  dsimp only
  simp only [output,execute,BinaryLowHighNormalize.table_value,Vector.get_ofFn]
  rw [GraphLowHighScale.fromInputs_scale]
  exact Int.mul_ediv_cancel_left _ (pow_ne_zero p.L (by decide : (4:ℤ)≠0))

theorem fromInputs_divisible (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (bandL bandR ell : ℕ)
    (request : Fin (FoldedBackendExecution.windowQuerySize n)) (residue : Fin f.cyclic) :
    let graph := GraphPrefixProgram.fromInputs f p block input bandL bandR ell
    (4:ℤ)^p.L ∣ view ((RootProductCollection.output (GraphLowMaskAssembly.execute graph input.target bandL bandR).value request).get residue)+
      view ((CountedCyclicCollection.output (GraphHighFamily.execute graph input.target bandL bandR).2.value request).get residue) := by
  dsimp only
  rw [GraphLowHighScale.fromInputs_scale]
  exact dvd_mul_right _ _

theorem fromInputs_bits (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (bandL bandR ell : ℕ) :
    let graph := GraphPrefixProgram.fromInputs f p block input bandL bandR ell
    bitSteps graph input.target bandL bandR≤bitBudget graph input.target := by
  let graph := GraphPrefixProgram.fromInputs f p block input bandL bandR ell
  have hl := GraphLowMaskAssembly.execute_bits f p block input bandL bandR ell
  have hn := BinaryLowHighNormalize.table_bits p.L (lowMagnitude p.L p.m p.t f.cyclic)
    (highMagnitude p.L p.m p.t f.cyclic)
    (Vector.ofFn (RootProductCollection.output (GraphLowMaskAssembly.execute graph input.target bandL bandR).value))
    (Vector.ofFn (CountedCyclicCollection.output (GraphHighFamily.execute graph input.target bandL bandR).2.value))
    (fun i r => by simpa only [Vector.get_ofFn,lowMagnitude,graph] using GraphLowMaskAssembly.execute_bound f p block input bandL bandR ell i r)
    (fun i r => by simpa only [Vector.get_ofFn,highMagnitude,graph] using GraphHighFamily.fromInputs_bound f p block input bandL bandR ell i r)
  dsimp only at hl ⊢
  change _≤bitBudget graph input.target
  unfold bitSteps execute bitBudget
  dsimp only
  dsimp only [graph] at hn ⊢
  omega

theorem execute_control (graph : GraphPrefixProgram.Prepared f p b ell)
    (target : BinaryFoldedFormation.BinaryTable n) (bandL bandR : ℕ) :
    control graph target bandL bandR≤controlBudget graph := by
  have hl := GraphLowMaskAssembly.execute_control graph target bandL bandR
  have hn := BinaryLowHighNormalize.table_control p.L
    (Vector.ofFn (RootProductCollection.output (GraphLowMaskAssembly.execute graph target bandL bandR).value))
    (Vector.ofFn (CountedCyclicCollection.output (GraphHighFamily.execute graph target bandL bandR).2.value))
  unfold control execute controlBudget
  dsimp only
  omega

theorem fromInputs_highWork (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (bandL bandR ell : ℕ) :
    let graph := GraphPrefixProgram.fromInputs f p block input bandL bandR ell
    highWork graph input.target bandL bandR≤GraphHighFamily.budget f p input.target :=
  GraphHighFamily.fromInputs_work f p block input bandL bandR ell

#print axioms fromInputs_value
#print axioms fromInputs_divisible
#print axioms fromInputs_bits
#print axioms execute_control
#print axioms fromInputs_highWork
end ThinMatrix.GraphNormalizedBand
