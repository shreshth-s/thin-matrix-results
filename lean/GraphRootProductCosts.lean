import GraphRootProducts

set_option autoImplicit false
set_option maxRecDepth 5000
set_option maxHeartbeats 1000000

/-! Bounds for the actual paired graph execution, including both target
formations, all unmatched completions, selection copies and full products.
Earlier graph preparation is retained once and has its own ledger. Native
indexing/control is explicitly not a binary address-cost theorem. -/
namespace ThinMatrix.GraphRootProducts
open ExactHalfSourcePlan ResidualFamilyKeys BinaryGroupedCoordinates BinaryGroupedPreparation BinaryResidualPolynomial

def Prepared.newBitSteps {n h r b ell : ℕ} {f : CompactBlocks.PhysicalFactorization r}
    {p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f} (out : Prepared f p b ell) : ℕ :=
  out.transposed.bitSteps+out.left.newBitSteps+out.right.newBitSteps+
    out.leftSelected.bitSteps+out.rightSelected.bitSteps+out.paired.bitSteps

def Prepared.newControl {n h r b ell : ℕ} {f : CompactBlocks.PhysicalFactorization r}
    {p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f} (out : Prepared f p b ell) : ℕ :=
  out.transposed.control+out.left.newControl+out.right.newControl+
    out.leftSelected.control+out.rightSelected.control+out.paired.control+24

noncomputable def rootBitBudget {n h r b ell : ℕ} {f : CompactBlocks.PhysicalFactorization r}
    {p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f} (graph : GraphPrefixProgram.Prepared f p b ell)
    (i : GraphRootCompletion.Index p.L p.m p.t) (target : BinaryFoldedFormation.BinaryTable n) : ℕ :=
  let B := GraphCompletionRequests.metadataWidth n h (FoldedBackendExecution.physicalFold f) f.cyclic
  10000*(B+1)^2+2000000*FoldedBackendExecution.windowQuerySize n*(GraphTargetWidth.width target+B+10)^2+
    RetainedWindowCompletion.bitBudget (GraphRootCompletion.sources graph i)
      (GraphRootCompletion.magnitude p.L p.m ell) (FoldedBackendExecution.windowQuerySize n)

def rootControlBudget {n h r b ell : ℕ} {f : CompactBlocks.PhysicalFactorization r}
    {p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f} (graph : GraphPrefixProgram.Prepared f p b ell)
    (i : GraphRootCompletion.Index p.L p.m p.t) : ℕ :=
  let M := FoldedBackendExecution.windowQuerySize n
  M*(1000*(p.L+p.m+1)^5+32)+8+(48*p.L+24+(M*(32*(p.L-p.m)+48)+8))+
    (RetainedRootWindows.slots (p.L-p.m)*40+8)+RetainedWindowCompletion.controlBudget (GraphRootCompletion.sources graph i) M+40

noncomputable def bitBudget {n h r b ell : ℕ} {f : CompactBlocks.PhysicalFactorization r}
    {p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f} (graph : GraphPrefixProgram.Prepared f p b ell)
    (i : Index p.L p.m p.t) (target : BinaryFoldedFormation.BinaryTable n) : ℕ :=
  rootBitBudget graph i.leftIndex target+rootBitBudget graph (transpose graph i).value target+
    2*(FoldedBackendExecution.windowQuerySize n*(((p.m+1)*f.cyclic)*BackendScalarBits.backendScalarUnit (magnitude p.L p.m).size))+
    PairedRootRows.bitBudget (p.m+1) f.cyclic (FoldedBackendExecution.windowQuerySize n) (magnitude p.L p.m)

def controlBudget {n h r b ell : ℕ} {f : CompactBlocks.PhysicalFactorization r}
    {p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f} (graph : GraphPrefixProgram.Prepared f p b ell)
    (i : Index p.L p.m p.t) : ℕ :=
  ResidualChannelTranspose.budget p.m (channelCount p.m p.t)+16+
    rootControlBudget graph i.leftIndex+rootControlBudget graph (transpose graph i).value+
    2*(FoldedBackendExecution.windowQuerySize n*(40*((p.m+1)*f.cyclic)+112)+8)+
    PairedRootRows.controlBudget (p.m+1) f.cyclic (FoldedBackendExecution.windowQuerySize n)+24

theorem fromInputs_bound {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (bandL bandR ell : ℕ) (i : Index p.L p.m p.t)
    (request : Fin (FoldedBackendExecution.windowQuerySize n)) :
    Bound (CompletedRootProducts.magnitude (p.m+1) f.cyclic (magnitude p.L p.m))
      ((fromInputs f p block input bandL bandR ell i).paired.value.products.value.get request) := by
  letI : NeZero f.cyclic := ⟨Nat.ne_of_gt f.cyclic_pos⟩
  exact PairedRootRows.execute_bound _ _ _
    (selected_bound f p block input bandL bandR ell i.leftIndex)
    (selected_bound f p block input bandL bandR ell (transpose (GraphPrefixProgram.fromInputs f p block input bandL bandR ell) i).value) request

theorem selection_bits {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (bandL bandR ell : ℕ) (i : GraphRootCompletion.Index p.L p.m p.t) :
    (select (GraphRootCompletion.fromInputs f p block input bandL bandR ell i) i bandL bandR).bitSteps≤
      FoldedBackendExecution.windowQuerySize n*(((p.m+1)*f.cyclic)*BackendScalarBits.backendScalarUnit (magnitude p.L p.m).size) := by
  have h := RootRequestSelection.fromInputs_bits f p block input bandL bandR ell i
  rw [GraphRootCompletion.aggregate_magnitude] at h
  exact h

theorem fromInputs_bits {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (bandL bandR ell : ℕ) (i : Index p.L p.m p.t) :
    (fromInputs f p block input bandL bandR ell i).newBitSteps≤
      bitBudget (GraphPrefixProgram.fromInputs f p block input bandL bandR ell) i input.target := by
  letI : NeZero f.cyclic := ⟨Nat.ne_of_gt f.cyclic_pos⟩
  let graph := GraphPrefixProgram.fromInputs f p block input bandL bandR ell
  have hl := GraphRootCompletion.fromInputs_newBits f p block input bandL bandR ell i.leftIndex
  have hr := GraphRootCompletion.fromInputs_newBits f p block input bandL bandR ell (transpose graph i).value
  have ha := selection_bits f p block input bandL bandR ell i.leftIndex
  have hb := selection_bits f p block input bandL bandR ell (transpose graph i).value
  have hp := PairedRootRows.execute_bits _ _ _
    (selected_bound f p block input bandL bandR ell i.leftIndex)
    (selected_bound f p block input bandL bandR ell (transpose graph i).value)
  have hs := Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hl hr) ha) hb) hp
  dsimp only [fromInputs,Prepared.newBitSteps,execute]
  simp only [transpose_bits,Nat.zero_add]
  simpa only [graph,GraphRootCompletion.fromInputs,bitBudget,rootBitBudget,two_mul,Nat.add_assoc] using hs

theorem execute_control {n h r b ell : ℕ} {f : CompactBlocks.PhysicalFactorization r}
    {p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f} (graph : GraphPrefixProgram.Prepared f p b ell)
    (i : Index p.L p.m p.t) (target : BinaryFoldedFormation.BinaryTable n) (bandL bandR : ℕ) :
    (execute graph i target bandL bandR).newControl≤controlBudget graph i := by
  letI : NeZero f.cyclic := ⟨Nat.ne_of_gt f.cyclic_pos⟩
  have ht := (transpose_control graph i).le
  have hl := GraphRootCompletion.execute_control graph i.leftIndex target
  have hr := GraphRootCompletion.execute_control graph (transpose graph i).value target
  have ha : (select (GraphRootCompletion.execute graph i.leftIndex target) i.leftIndex bandL bandR).control≤
      FoldedBackendExecution.windowQuerySize n*(40*((p.m+1)*f.cyclic)+112)+8 := RootRequestSelection.select_control _ _ _ _ _ _ _
  have hb : (select (GraphRootCompletion.execute graph (transpose graph i).value target) (transpose graph i).value bandL bandR).control≤
      FoldedBackendExecution.windowQuerySize n*(40*((p.m+1)*f.cyclic)+112)+8 := RootRequestSelection.select_control _ _ _ _ _ _ _
  have hp := PairedRootRows.execute_control
    (select (GraphRootCompletion.execute graph i.leftIndex target) i.leftIndex bandL bandR).value
    (select (GraphRootCompletion.execute graph (transpose graph i).value target) (transpose graph i).value bandL bandR).value
  have hs := Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add ht hl) hr) ha) hb) hp) 24
  dsimp only [Prepared.newControl,execute]
  simpa only [controlBudget,rootControlBudget,two_mul,Nat.add_assoc] using hs

#print axioms fromInputs_bound
#print axioms selection_bits
#print axioms fromInputs_bits
#print axioms execute_control
end ThinMatrix.GraphRootProducts
