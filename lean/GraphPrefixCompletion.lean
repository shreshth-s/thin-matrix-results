import GraphCompletionRequests
import WindowCompletionProgram

set_option autoImplicit false
set_option maxRecDepth 4000

/-! One selected oriented root/window of the actual retained graph program,
completed for every folded request. The original preparation is retained once.
No full-root contraction, band filtering, batching or fast cost is asserted. -/
namespace ThinMatrix.GraphPrefixCompletion
open GoodMapEmbedding ExactHalfSourcePlan ResidualFamilyKeys BinaryGroupedCoordinates

structure Index (L m t : ℕ) where
  u : Fin (J m)
  v : Fin (J m)
  run : Fin (2*m+1)
  normal : Fin (goodSlots L m).card
  opposite : Fin (goodSlots L m).card
  channel : Fin (channelCount m t)
  slot : Fin (RetainedRootWindows.slots (L-m))
  right : Bool

def side {A : Type} (right : Bool) (pair : A×A) : A := if right then pair.2 else pair.1

def encodedSlot {n h r b ell : ℕ} {f : CompactBlocks.PhysicalFactorization r}
    {p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f} (graph : GraphPrefixProgram.Prepared f p b ell) (index : Index p.L p.m p.t) :=
  ((((side index.right (((graph.encoded.value.get index.u).get index.v).get index.run)).get index.normal).get index.opposite).get index.channel).get index.slot

def permuted {n h r b ell : ℕ} {f : CompactBlocks.PhysicalFactorization r}
    {p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f} (graph : GraphPrefixProgram.Prepared f p b ell) (index : Index p.L p.m p.t) :=
  ((((side index.right (((graph.permuted.permuted.value.get index.u).get index.v).get index.run)).get index.normal).get index.opposite).get index.channel).get index.slot

def window {n h r b ell : ℕ} {f : CompactBlocks.PhysicalFactorization r}
    {p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f} (graph : GraphPrefixProgram.Prepared f p b ell) (index : Index p.L p.m p.t) :=
  (((side index.right (((graph.permuted.transformed.source.windows.value.get index.u).get index.v).get index.run)).get index.normal).get index.opposite).get index.channel

structure Prepared {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (b ell : ℕ) where
  graph : GraphPrefixProgram.Prepared f p b ell
  targets : GraphCompletionRequests.Prepared f p
  residuals : Run (GraphCompletionRequests.Residuals p.L p.m)
  completed : WindowCompletionProgram.Prepared (p.L-p.m) ell ((p.m+1)*f.cyclic)

def execute {n h r b ell : ℕ} {f : CompactBlocks.PhysicalFactorization r}
    {p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f} (graph : GraphPrefixProgram.Prepared f p b ell)
    (index : Index p.L p.m p.t) (target : BinaryFoldedFormation.BinaryTable n) : Prepared f p b ell :=
  let roots := graph.permuted.transformed.source.roots
  let targets := GraphCompletionRequests.prepare f p roots.source.shape target
  let residuals := GraphCompletionRequests.project index.right (roots.keys.value.masks.get index.normal)
    (roots.keys.value.masks.get index.opposite) targets.physical.value
  let completed := WindowCompletionProgram.execute (encodedSlot graph index) (permuted graph index).layout residuals.value.labels
  ⟨graph,targets,residuals,completed⟩

def fromInputs {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (bandL bandR ell : ℕ) (index : Index p.L p.m p.t) : Prepared f p block ell :=
  execute (GraphPrefixProgram.fromInputs f p block input bandL bandR ell) index input.target

@[simp] theorem execute_size {n h r b ell : ℕ} {f : CompactBlocks.PhysicalFactorization r}
    {p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f} (graph : GraphPrefixProgram.Prepared f p b ell)
    (index : Index p.L p.m p.t) (target : BinaryFoldedFormation.BinaryTable n) :
    (execute graph index target).completed.completed.value.requests.size=FoldedBackendExecution.windowQuerySize n := by
  simp [execute]

@[simp] theorem residuals_size {n h r b ell : ℕ} {f : CompactBlocks.PhysicalFactorization r}
    {p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f} (graph : GraphPrefixProgram.Prepared f p b ell)
    (index : Index p.L p.m p.t) (target : BinaryFoldedFormation.BinaryTable n) :
    (execute graph index target).residuals.value.labels.size=FoldedBackendExecution.windowQuerySize n := by
  simp [execute]

theorem fromInputs_query {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (bandL bandR ell : ℕ) (index : Index p.L p.m p.t)
    (pair : Fin (2^(WindowPrefixProgram.length (p.L-p.m) ell)))
    (q : Fin (WindowPrefixProgram.prefixLength (p.L-p.m) ell) → Fin 4)
    (active : Finset (Fin (WindowPrefixProgram.length (p.L-p.m) ell))) (col : Fin ((p.m+1)*f.cyclic)) :
    let graph := GraphPrefixProgram.fromInputs f p block input bandL bandR ell
    CappedPrefixProgram.query (encodedSlot graph index).encoded pair q active col=
      EncoderCorrectness.tensorSum (fun _ : Fin (2*(p.L-p.m)) => 3)
        (GraphPrefixTensor.originalForms ell (decide ((window graph index).counts.2≤(window graph index).counts.1)) index.slot
          (Fin.append (fun a => BinaryPrefixContraction.form (q a))
          (fun a => CroppedGroupedSuffix.localForm (((GroupedPreparation.pairKeys (WindowPrefixProgram.length (p.L-p.m) ell)).get pair).get a) (decide (a∈active)))))
        (fun w => BinaryWindowPartition.sourceValue ((window graph index).windows.components.get index.slot) w col) := by
  rcases index with ⟨u,v,run,i,j,c,slot,right⟩
  cases right
  · exact GraphPrefixTensor.fromInputs_left_original_query f p block input bandL bandR ell u v run i j c slot pair q active col
  · exact GraphPrefixTensor.fromInputs_right_original_query f p block input bandL bandR ell u v run i j c slot pair q active col

theorem fromInputs_prefix {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (bandL bandR ell : ℕ) (index : Index p.L p.m p.t)
 :
    let graph := GraphPrefixProgram.fromInputs f p block input bandL bandR ell
    encodedSlot graph index=(WindowPrefixProgram.execute ell (p.m/2) (window graph index).counts.1
      (window graph index).counts.2 (permuted graph index).coefficients).value := by
  rcases index with ⟨u,v,run,i,j,c,slot,right⟩
  cases right
  · exact GraphPrefixProgram.fromInputs_left_entry f p block input bandL bandR ell u v run i j c slot
  · exact GraphPrefixProgram.fromInputs_right_entry f p block input bandL bandR ell u v run i j c slot

theorem fromInputs_pairs {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (bandL bandR ell : ℕ) (index : Index p.L p.m p.t)
 :
    (encodedSlot (GraphPrefixProgram.fromInputs f p block input bandL bandR ell) index).encoded.grouped.pairs=
      GroupedPreparation.pairKeys (WindowPrefixProgram.length (p.L-p.m) ell) := by
  rw [fromInputs_prefix]
  simp only [WindowPrefixProgram.execute,CappedPrefixProgram.execute,RetainedCappedGroups.prepare,GroupedPreparation.storePairs_value]

theorem fromInputs_layout {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (bandL bandR ell : ℕ) (index : Index p.L p.m p.t)
 :
    let graph := GraphPrefixProgram.fromInputs f p block input bandL bandR ell
    (permuted graph index).layout=(RetainedWindowPermutation.build (p.L-p.m) (min ell (p.L-p.m))
      (decide ((window graph index).counts.2≤(window graph index).counts.1)) index.slot).value := by
  rcases index with ⟨u,v,run,i,j,c,slot,right⟩
  cases right
  · have h := GraphWindowPermutations.fromInputs_left_entry f p block input bandL bandR ell u v run i j c slot
    exact congrArg RetainedWindowPermutation.Prepared.layout h
  · have h := GraphWindowPermutations.fromInputs_right_entry f p block input bandL bandR ell u v run i j c slot
    exact congrArg RetainedWindowPermutation.Prepared.layout h

theorem fromInputs_bound {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (bandL bandR ell : ℕ) (index : Index p.L p.m p.t)
 :
    let graph := GraphPrefixProgram.fromInputs f p block input bandL bandR ell
    ∀ pair, PrefixCompletionMatrices.LeafBound ((encodedSlot graph index).encoded.traces.get pair)
      (2^(WindowPrefixProgram.prefixLength (p.L-p.m) ell)*
        (2^(p.L-p.m)*(2^p.m*(4^p.m*2^(p.L+p.m))))) := by
  dsimp only
  rw [fromInputs_prefix]
  intro pair supportIdx q col
  apply CappedPrefixProgram.output_bound
  apply WindowPrefixProgram.castSource_bound
  have h := GraphPrefixProgram.permuted_bound f p block input bandL bandR ell index.u index.v index.run
  rcases index with ⟨u,v,run,i,j,c,slot,right⟩
  cases right
  · exact h.1 i j c slot
  · exact h.2 i j c slot

theorem fromInputs_tensor {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (bandL bandR ell : ℕ) (index : Index p.L p.m p.t)

    (request : Fin (FoldedBackendExecution.windowQuerySize n)) (col : Fin ((p.m+1)*f.cyclic)) :
    let graph := GraphPrefixProgram.fromInputs f p block input bandL bandR ell
    let out := fromInputs f p block input bandL bandR ell index
    BinaryCell.view ((out.completed.completed.value.requests[request.val]'(by simp [out,fromInputs])).output.get col)=
      EncoderCorrectness.tensorSum (fun _ : Fin (2*(p.L-p.m)) => 3)
        (OppositeTensorBridge.pushForms (RetainedOppositeTransform.axes (p.L-p.m))
          (fun i => BinaryPrefixContraction.form ((WindowCompletionRequests.orient
            (out.residuals.value.labels[request.val]'(by simp [out,fromInputs]))).value.get i)))
        (fun w => BinaryWindowPartition.sourceValue ((window graph index).windows.components.get index.slot) w col) := by
  dsimp only
  let graph := GraphPrefixProgram.fromInputs f p block input bandL bandR ell
  let labels := (execute graph index input.target).residuals.value.labels
  have hi : request.val<labels.size := by simp [labels]
  have h := WindowCompletionProgram.execute_value (encodedSlot graph index) (permuted graph index).layout
    labels request.val hi col
  dsimp only at h
  rw [fromInputs_query,PrefixRequestKey.make_forms _ (fromInputs_pairs f p block input bandL bandR ell index)] at h
  conv at h => rhs; rw [fromInputs_layout,WindowCompletionRequests.forms]
  exact h

theorem fromInputs_bits {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (bandL bandR ell : ℕ) (index : Index p.L p.m p.t)
 :
    let out := fromInputs f p block input bandL bandR ell index
    out.completed.completed.bitSteps≤PrefixCompletionProgram.bitBudget
      (WindowPrefixProgram.prefixLength (p.L-p.m) ell) (WindowPrefixProgram.length (p.L-p.m) ell)
      out.completed.source.rareCap ((p.m+1)*f.cyclic)
      (2^(WindowPrefixProgram.prefixLength (p.L-p.m) ell)*(2^(p.L-p.m)*(2^p.m*(4^p.m*2^(p.L+p.m)))))
      (FoldedBackendExecution.windowQuerySize n) := by
  have h := WindowCompletionProgram.execute_bits
    (encodedSlot (GraphPrefixProgram.fromInputs f p block input bandL bandR ell) index)
    (permuted (GraphPrefixProgram.fromInputs f p block input bandL bandR ell) index).layout
    (fromInputs f p block input bandL bandR ell index).residuals.value.labels _
    (fromInputs_bound f p block input bandL bandR ell index)
  rw [show (fromInputs f p block input bandL bandR ell index).residuals.value.labels.size=FoldedBackendExecution.windowQuerySize n from residuals_size _ _ _] at h
  exact h

def Prepared.newBitSteps {n h r b ell : ℕ} {f : CompactBlocks.PhysicalFactorization r}
    {p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f} (out : Prepared f p b ell) : ℕ :=
  out.targets.folded.geometry.bitSteps+out.targets.folded.requests.bitSteps+out.targets.physical.bitSteps+
    out.residuals.bitSteps+out.completed.completed.bitSteps

def Prepared.newControl {n h r b ell : ℕ} {f : CompactBlocks.PhysicalFactorization r}
    {p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f} (out : Prepared f p b ell) : ℕ :=
  out.targets.physical.control+out.residuals.control+out.completed.requests.work+out.completed.completed.control+32

theorem execute_control {n h r b ell : ℕ} {f : CompactBlocks.PhysicalFactorization r}
    {p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f} (graph : GraphPrefixProgram.Prepared f p b ell)
    (index : Index p.L p.m p.t) (target : BinaryFoldedFormation.BinaryTable n) :
    let M := FoldedBackendExecution.windowQuerySize n
    (execute graph index target).newControl≤M*(1000*(p.L+p.m+1)^5+32)+8+
      (48*p.L+24+(M*(32*(p.L-p.m)+48)+8))+(M*(48*(p.L-p.m)+56)+8)+
      PrefixCompletionProgram.controlBudget (WindowPrefixProgram.prefixLength (p.L-p.m) ell)
        (WindowPrefixProgram.length (p.L-p.m) ell) (encodedSlot graph index).rareCap ((p.m+1)*f.cyclic) M+32 := by
  let roots := graph.permuted.transformed.source.roots
  let targets := GraphCompletionRequests.prepare f p roots.source.shape target
  have hp := GraphCompletionRequests.prepare_control f p roots.source.shape target
  have hr := GraphCompletionRequests.project_control index.right (roots.keys.value.masks.get index.normal)
    (roots.keys.value.masks.get index.opposite) targets.physical.value
  have hc := WindowCompletionProgram.execute_control (encodedSlot graph index) (permuted graph index).layout
    (execute graph index target).residuals.value.labels
  rw [residuals_size] at hc
  have hs := Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add hp hr) hc) 32
  simpa only [execute,Prepared.newControl,Nat.add_assoc] using hs

theorem fromInputs_newBits {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (bandL bandR ell : ℕ) (index : Index p.L p.m p.t)
 :
    let out := fromInputs f p block input bandL bandR ell index
    let B := GraphCompletionRequests.metadataWidth n h (FoldedBackendExecution.physicalFold f) f.cyclic
    out.newBitSteps≤10000*(B+1)^2+
      2000000*FoldedBackendExecution.windowQuerySize n*(GraphCompletionRequests.targetWidth input.target+B+10)^2+
      PrefixCompletionProgram.bitBudget (WindowPrefixProgram.prefixLength (p.L-p.m) ell)
        (WindowPrefixProgram.length (p.L-p.m) ell) out.completed.source.rareCap ((p.m+1)*f.cyclic)
        (2^(WindowPrefixProgram.prefixLength (p.L-p.m) ell)*(2^(p.L-p.m)*(2^p.m*(4^p.m*2^(p.L+p.m)))))
        (FoldedBackendExecution.windowQuerySize n) := by
  have hp := GraphCompletionRequests.prepare_formation_bits f p
    (GraphPrefixProgram.fromInputs f p block input bandL bandR ell).permuted.transformed.source.roots.source.shape input.target
  have hc := fromInputs_bits f p block input bandL bandR ell index
  dsimp only at hp hc ⊢
  have hz : (fromInputs f p block input bandL bandR ell index).targets.physical.bitSteps=0 := GraphCompletionRequests.prepare_bits _ _ _ _
  have hr : (fromInputs f p block input bandL bandR ell index).residuals.bitSteps=0 := GraphCompletionRequests.project_bits _ _ _ _
  unfold Prepared.newBitSteps
  simp only [hz,hr,Nat.add_zero]
  exact Nat.add_le_add hp hc


#print axioms execute_size
#print axioms residuals_size
#print axioms fromInputs_query
#print axioms fromInputs_prefix
#print axioms fromInputs_pairs
#print axioms fromInputs_layout
#print axioms fromInputs_bound
#print axioms fromInputs_tensor
#print axioms fromInputs_bits
#print axioms execute_control
#print axioms fromInputs_newBits
end ThinMatrix.GraphPrefixCompletion
