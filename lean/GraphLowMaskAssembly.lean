import LowRequestLocator

set_option autoImplicit false
set_option maxRecDepth 6000
set_option maxHeartbeats 1600000

/-! Exhaustively execute and retain every good-mask pair, then accumulate all
cyclic coefficients per original request. Unmatched executions are charged;
no routing or fast completion bound is assumed. Graph preparation is shared. -/
namespace ThinMatrix.GraphLowMaskAssembly
open GoodMapEmbedding ExactHalfSourcePlan ResidualFamilyKeys BinaryCell
open scoped BigOperators

variable {n h r b ell : ℕ} {f : CompactBlocks.PhysicalFactorization r}
  {p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f}

def pairMagnitude (L m t q : ℕ) : ℕ :=
  J m*(J m*((2*m+1)*(channelCount m t*GraphWeightedRootProducts.magnitude L m q t)))

def row (graph : GraphPrefixProgram.Prepared f p b ell) (left : Fin (goodSlots p.L p.m).card)
    (target : BinaryFoldedFormation.BinaryTable n) (bandL bandR : ℕ) :=
  RootProductCollection.execute graph.permuted.transformed.source.roots.keys.value.masks
    (fun right => GraphRootFamilyProducts.execute graph left right target bandL bandR) RootProductCollection.output

noncomputable def rowBitBudget (graph : GraphPrefixProgram.Prepared f p b ell) (left : Fin (goodSlots p.L p.m).card)
    (target : BinaryFoldedFormation.BinaryTable n) : ℕ :=
  RootProductCollection.bitBudget (fun right => GraphRootFamilyProducts.executeBitBudget graph left right target)
    (FoldedBackendExecution.windowQuerySize n) f.cyclic (pairMagnitude p.L p.m p.t f.cyclic)

def rowControlBudget (graph : GraphPrefixProgram.Prepared f p b ell) (left : Fin (goodSlots p.L p.m).card) : ℕ :=
  RootProductCollection.controlBudget (fun right => GraphRootFamilyProducts.executeControlBudget graph left right)
    (FoldedBackendExecution.windowQuerySize n) f.cyclic

theorem row_bound (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (bandL bandR ell : ℕ) (left : Fin (goodSlots p.L p.m).card)
    (request : Fin (FoldedBackendExecution.windowQuerySize n)) (residue : Fin f.cyclic) :
    (view ((RootProductCollection.output (row (GraphPrefixProgram.fromInputs f p block input bandL bandR ell) left input.target bandL bandR).value request).get residue)).natAbs≤
      (goodSlots p.L p.m).card*pairMagnitude p.L p.m p.t f.cyclic := by
  apply RootProductCollection.execute_bound
  intro right
  exact GraphRootFamilyProducts.execute_bound f p block input bandL bandR ell left right

theorem row_bits (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (bandL bandR ell : ℕ) (left : Fin (goodSlots p.L p.m).card) :
    (row (GraphPrefixProgram.fromInputs f p block input bandL bandR ell) left input.target bandL bandR).bitSteps≤
      rowBitBudget (GraphPrefixProgram.fromInputs f p block input bandL bandR ell) left input.target := by
  apply RootProductCollection.execute_bits
  · intro right
    exact GraphRootFamilyProducts.execute_bound f p block input bandL bandR ell left right
  · intro right
    exact GraphRootFamilyProducts.execute_bits f p block input bandL bandR ell left right

theorem row_control (graph : GraphPrefixProgram.Prepared f p b ell) (left : Fin (goodSlots p.L p.m).card)
    (target : BinaryFoldedFormation.BinaryTable n) (bandL bandR : ℕ) :
    (row graph left target bandL bandR).control≤rowControlBudget graph left := by
  apply RootProductCollection.execute_control
  intro right
  exact GraphRootFamilyProducts.execute_control graph left right target bandL bandR

def execute (graph : GraphPrefixProgram.Prepared f p b ell) (target : BinaryFoldedFormation.BinaryTable n)
    (bandL bandR : ℕ) :=
  RootProductCollection.execute graph.permuted.transformed.source.roots.keys.value.masks
    (fun left => row graph left target bandL bandR) RootProductCollection.output

noncomputable def bitBudget (graph : GraphPrefixProgram.Prepared f p b ell) (target : BinaryFoldedFormation.BinaryTable n) : ℕ :=
  RootProductCollection.bitBudget (fun left => rowBitBudget graph left target)
    (FoldedBackendExecution.windowQuerySize n) f.cyclic ((goodSlots p.L p.m).card*pairMagnitude p.L p.m p.t f.cyclic)

def controlBudget (graph : GraphPrefixProgram.Prepared f p b ell) : ℕ :=
  RootProductCollection.controlBudget (fun left => rowControlBudget graph left) (FoldedBackendExecution.windowQuerySize n) f.cyclic

theorem execute_bound (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (bandL bandR ell : ℕ)
    (request : Fin (FoldedBackendExecution.windowQuerySize n)) (residue : Fin f.cyclic) :
    (view ((RootProductCollection.output (execute (GraphPrefixProgram.fromInputs f p block input bandL bandR ell) input.target bandL bandR).value request).get residue)).natAbs≤
      (goodSlots p.L p.m).card*((goodSlots p.L p.m).card*pairMagnitude p.L p.m p.t f.cyclic) := by
  apply RootProductCollection.execute_bound
  intro left
  exact row_bound f p block input bandL bandR ell left

theorem execute_bits (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (bandL bandR ell : ℕ) :
    (execute (GraphPrefixProgram.fromInputs f p block input bandL bandR ell) input.target bandL bandR).bitSteps≤
      bitBudget (GraphPrefixProgram.fromInputs f p block input bandL bandR ell) input.target := by
  apply RootProductCollection.execute_bits
  · intro left
    exact row_bound f p block input bandL bandR ell left
  · intro left
    exact row_bits f p block input bandL bandR ell left

theorem execute_control (graph : GraphPrefixProgram.Prepared f p b ell) (target : BinaryFoldedFormation.BinaryTable n)
    (bandL bandR : ℕ) : (execute graph target bandL bandR).control≤controlBudget graph := by
  apply RootProductCollection.execute_control
  intro left
  exact row_control graph left target bandL bandR

theorem fromInputs_value (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (bandL bandR ell : ℕ)
    (request : Fin (FoldedBackendExecution.windowQuerySize n)) (residue : Fin f.cyclic) :
    let graph := GraphPrefixProgram.fromInputs f p block input bandL bandR ell
    view ((RootProductCollection.output (execute graph input.target bandL bandR).value request).get residue)=
      LowRequestLocator.value graph input.target bandL bandR request residue := by
  dsimp only
  rw [← LowRequestLocator.family_sum]
  simp only [execute,row,RootProductCollection.execute_value]
  apply Finset.sum_congr rfl; intro left _
  apply Finset.sum_congr rfl; intro right _
  exact GraphShiftedLow.fromInputs_value f p block input bandL bandR ell left right request residue

#print axioms row_bound
#print axioms row_bits
#print axioms row_control
#print axioms execute_bound
#print axioms execute_bits
#print axioms execute_control
#print axioms fromInputs_value
end ThinMatrix.GraphLowMaskAssembly
