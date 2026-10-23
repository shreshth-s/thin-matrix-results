import GraphPrefixCompletion
import RetainedWindowCompletion
import GraphTargetWidth

set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 800000

/-! One oriented root/channel of the actual graph source, completed for every
folded request and every formal-degree/cyclic column. Targets and residual
labels are constructed once. Every window is executed; their actual outputs
are retained and added in binary. Outer root/band selection is a later stage. -/
namespace ThinMatrix.GraphRootCompletion
open GoodMapEmbedding ExactHalfSourcePlan ResidualFamilyKeys BinaryGroupedCoordinates
open BinaryGroupedPreparation GraphPrefixCompletion
open scoped BigOperators

structure Index (L m t : ℕ) where
  u : Fin (J m)
  v : Fin (J m)
  run : Fin (2*m+1)
  normal : Fin (goodSlots L m).card
  opposite : Fin (goodSlots L m).card
  channel : Fin (channelCount m t)
  right : Bool

def Index.atSlot {L m t : ℕ} (i : Index L m t) (s : Fin (RetainedRootWindows.slots (L-m))) : GraphPrefixCompletion.Index L m t :=
  ⟨i.u,i.v,i.run,i.normal,i.opposite,i.channel,s,i.right⟩

def sources {n h r b ell : ℕ} {f : CompactBlocks.PhysicalFactorization r}
    {p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f} (graph : GraphPrefixProgram.Prepared f p b ell) (i : Index p.L p.m p.t) :=
  (((side i.right (((graph.encoded.value.get i.u).get i.v).get i.run)).get i.normal).get i.opposite).get i.channel

def layouts {n h r b ell : ℕ} {f : CompactBlocks.PhysicalFactorization r}
    {p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f} (graph : GraphPrefixProgram.Prepared f p b ell) (i : Index p.L p.m p.t) :=
  let entries := (((side i.right (((graph.permuted.permuted.value.get i.u).get i.v).get i.run)).get i.normal).get i.opposite).get i.channel
  tabulate entries (fun s => ⟨(entries.get s).layout,0,8⟩)

def root {n h r b ell : ℕ} {f : CompactBlocks.PhysicalFactorization r}
    {p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f} (graph : GraphPrefixProgram.Prepared f p b ell) (i : Index p.L p.m p.t) :=
  (((side i.right (((graph.permuted.transformed.source.roots.roots.value.get i.u).get i.v).get i.run)).get i.normal).get i.opposite).get i.channel

@[simp] theorem layouts_get {n h r b ell : ℕ} {f : CompactBlocks.PhysicalFactorization r}
    {p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f} (graph : GraphPrefixProgram.Prepared f p b ell) (i : Index p.L p.m p.t)
    (s : Fin (RetainedRootWindows.slots (p.L-p.m))) :
    (layouts graph i).value.get s=(permuted graph (i.atSlot s)).layout := by simp only [layouts,tabulate_get]; rfl

@[simp] theorem layouts_bits {n h r b ell : ℕ} {f : CompactBlocks.PhysicalFactorization r}
    {p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f} (graph : GraphPrefixProgram.Prepared f p b ell) (i : Index p.L p.m p.t) :
    (layouts graph i).bitSteps=0 := by simp only [layouts,tabulate_bits_eq,Finset.sum_const_zero]

theorem layouts_control {n h r b ell : ℕ} {f : CompactBlocks.PhysicalFactorization r}
    {p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f} (graph : GraphPrefixProgram.Prepared f p b ell) (i : Index p.L p.m p.t) :
    (layouts graph i).control≤RetainedRootWindows.slots (p.L-p.m)*40+8 := tabulate_control _ _ (fun _ => le_refl 8)

structure Prepared {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (b ell : ℕ) where
  graph : GraphPrefixProgram.Prepared f p b ell
  targets : GraphCompletionRequests.Prepared f p
  residuals : Run (GraphCompletionRequests.Residuals p.L p.m)
  layouts : Run (Vector (RetainedWindowPermutation.Layout (2*(p.L-p.m))) (RetainedRootWindows.slots (p.L-p.m)))
  completed : Run (RetainedWindowCompletion.Prepared (p.L-p.m) ell ((p.m+1)*f.cyclic)
    (FoldedBackendExecution.windowQuerySize n) (RetainedRootWindows.slots (p.L-p.m)))

def execute {n h r b ell : ℕ} {f : CompactBlocks.PhysicalFactorization r}
    {p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f} (graph : GraphPrefixProgram.Prepared f p b ell)
    (i : Index p.L p.m p.t) (target : BinaryFoldedFormation.BinaryTable n) : Prepared f p b ell :=
  let roots := graph.permuted.transformed.source.roots
  let targets := GraphCompletionRequests.prepare f p roots.source.shape target
  let residuals := GraphCompletionRequests.project i.right (roots.keys.value.masks.get i.normal)
    (roots.keys.value.masks.get i.opposite) targets.physical.value
  let labels : Vector _ (FoldedBackendExecution.windowQuerySize n) := ⟨residuals.value.labels,by simp [residuals]⟩
  let maps := layouts graph i
  let completed := RetainedWindowCompletion.execute (sources graph i) maps.value labels
  ⟨graph,targets,residuals,maps,completed⟩

def fromInputs {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (bandL bandR ell : ℕ) (i : Index p.L p.m p.t) : Prepared f p block ell :=
  execute (GraphPrefixProgram.fromInputs f p block input bandL bandR ell) i input.target

@[simp] theorem residuals_size {n h r b ell : ℕ} {f : CompactBlocks.PhysicalFactorization r}
    {p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f} (graph : GraphPrefixProgram.Prepared f p b ell)
    (i : Index p.L p.m p.t) (target : BinaryFoldedFormation.BinaryTable n) :
    (execute graph i target).residuals.value.labels.size=FoldedBackendExecution.windowQuerySize n := by simp [execute]

theorem execute_view {n h r b ell : ℕ} {f : CompactBlocks.PhysicalFactorization r}
    {p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f} (graph : GraphPrefixProgram.Prepared f p b ell)
    (i : Index p.L p.m p.t) (target : BinaryFoldedFormation.BinaryTable n)
    (request : Fin (FoldedBackendExecution.windowQuerySize n)) (col : Fin ((p.m+1)*f.cyclic)) :
    BinaryCell.view (((execute graph i target).completed.value.sums.value.get request).output.get col)=
      ∑ s, BinaryCell.view (((GraphPrefixCompletion.execute graph (i.atSlot s) target).completed.completed.value.requests[request.val]'(by simp)).output.get col) := by
  unfold execute
  rw [RetainedWindowCompletion.execute_view]
  apply Finset.sum_congr rfl
  intro s _
  rw [layouts_get]
  rfl

theorem fromInputs_reconstruct {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (bandL bandR ell : ℕ) (i : Index p.L p.m p.t)
    (w : CroppedGroupedSuffix.Word (2*(p.L-p.m))) (d : Fin (p.m+1)) (residue : Fin f.cyclic) :
    let graph := GraphPrefixProgram.fromInputs f p block input bandL bandR ell
    (∑ s, BinaryWindowPartition.sourceValue ((window graph (i.atSlot s)).windows.components.get s) w (finProdFinEquiv (d,residue)))=
      BinaryResidualPolynomial.cellView ((ResidualWindowSource.rows (root graph i)).get (StoredGroupedCompletion.rawIndex _ w)) d residue := by
  rcases i with ⟨u,v,run,a,b,c,right⟩
  cases right
  · exact GraphRootWindows.fromInputs_left_reconstruct f p block input bandL bandR (min ell (p.L-p.m)) u v run a b c w d residue
  · exact GraphRootWindows.fromInputs_right_reconstruct f p block input bandL bandR (min ell (p.L-p.m)) u v run a b c w d residue

/-- The fully executed sum of all windows is the actual retained root's
contraction, independently at every formal degree and every cyclic residue. -/
theorem fromInputs_contraction {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (bandL bandR ell : ℕ) (i : Index p.L p.m p.t)
    (request : Fin (FoldedBackendExecution.windowQuerySize n)) (d : Fin (p.m+1)) (residue : Fin f.cyclic) :
    let graph := GraphPrefixProgram.fromInputs f p block input bandL bandR ell
    let out := fromInputs f p block input bandL bandR ell i
    BinaryCell.view ((out.completed.value.sums.value.get request).output.get (finProdFinEquiv (d,residue)))=
      EncoderCorrectness.tensorSum (fun _ : Fin (2*(p.L-p.m)) => 3)
        (OppositeTensorBridge.pushForms (RetainedOppositeTransform.axes (p.L-p.m))
          (fun j => BinaryPrefixContraction.form ((WindowCompletionRequests.orient
            (out.residuals.value.labels[request.val]'(by simp [out,fromInputs]))).value.get j)))
        (fun w => BinaryResidualPolynomial.cellView ((ResidualWindowSource.rows (root graph i)).get
          (StoredGroupedCompletion.rawIndex _ w)) d residue) := by
  dsimp only
  let graph := GraphPrefixProgram.fromInputs f p block input bandL bandR ell
  let out := fromInputs f p block input bandL bandR ell i
  let forms := OppositeTensorBridge.pushForms (RetainedOppositeTransform.axes (p.L-p.m))
    (fun j => BinaryPrefixContraction.form ((WindowCompletionRequests.orient
      (out.residuals.value.labels[request.val]'(by simp [out,fromInputs]))).value.get j))
  calc
    _ = ∑ s, BinaryCell.view (((GraphPrefixCompletion.execute graph (i.atSlot s) input.target).completed.completed.value.requests[request.val]'(by simp)).output.get (finProdFinEquiv (d,residue))) :=
      execute_view graph i input.target request _
    _ = ∑ s, EncoderCorrectness.tensorSum (fun _ : Fin (2*(p.L-p.m)) => 3) forms
        (fun w => BinaryWindowPartition.sourceValue ((window graph (i.atSlot s)).windows.components.get s) w (finProdFinEquiv (d,residue))) := by
      apply Finset.sum_congr rfl
      intro s _
      exact GraphPrefixCompletion.fromInputs_tensor f p block input bandL bandR ell (i.atSlot s) request _
    _ = _ := by
      unfold EncoderCorrectness.tensorSum
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro w _
      rw [← Finset.sum_mul]
      rw [fromInputs_reconstruct]

def magnitude (L m ell : ℕ) : ℕ :=
  2^(WindowPrefixProgram.prefixLength (L-m) ell)*(2^(L-m)*(2^m*(4^m*2^(L+m))))

theorem fromInputs_bound {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (bandL bandR ell : ℕ) (i : Index p.L p.m p.t) :
    let graph := GraphPrefixProgram.fromInputs f p block input bandL bandR ell
    ∀ s pair, PrefixCompletionMatrices.LeafBound (((sources graph i).get s).encoded.traces.get pair) (magnitude p.L p.m ell) := by
  dsimp only
  intro s
  exact GraphPrefixCompletion.fromInputs_bound f p block input bandL bandR ell (i.atSlot s)

theorem fromInputs_abs {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (bandL bandR ell : ℕ) (i : Index p.L p.m p.t)
    (request : Fin (FoldedBackendExecution.windowQuerySize n)) (col : Fin ((p.m+1)*f.cyclic)) :
    (BinaryCell.view (((fromInputs f p block input bandL bandR ell i).completed.value.sums.value.get request).output.get col)).natAbs≤
      RetainedRootWindows.slots (p.L-p.m)*RetainedWindowCompletion.leafMagnitude (p.L-p.m) ell (magnitude p.L p.m ell) :=
  RetainedWindowCompletion.execute_abs _ _ _ _ (fromInputs_bound f p block input bandL bandR ell i) request col

theorem fromInputs_bits {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (bandL bandR ell : ℕ) (i : Index p.L p.m p.t) :
    (fromInputs f p block input bandL bandR ell i).completed.bitSteps≤
      RetainedWindowCompletion.bitBudget (sources (GraphPrefixProgram.fromInputs f p block input bandL bandR ell) i)
        (magnitude p.L p.m ell) (FoldedBackendExecution.windowQuerySize n) :=
  RetainedWindowCompletion.execute_bits _ _ _ _ (fromInputs_bound f p block input bandL bandR ell i)

def Prepared.newBitSteps {n h r b ell : ℕ} {f : CompactBlocks.PhysicalFactorization r}
    {p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f} (out : Prepared f p b ell) : ℕ :=
  out.targets.folded.geometry.bitSteps+out.targets.folded.requests.bitSteps+out.targets.physical.bitSteps+
    out.residuals.bitSteps+out.layouts.bitSteps+out.completed.bitSteps

def Prepared.newControl {n h r b ell : ℕ} {f : CompactBlocks.PhysicalFactorization r}
    {p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f} (out : Prepared f p b ell) : ℕ :=
  out.targets.physical.control+out.residuals.control+out.layouts.control+out.completed.control+40

theorem execute_control {n h r b ell : ℕ} {f : CompactBlocks.PhysicalFactorization r}
    {p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f} (graph : GraphPrefixProgram.Prepared f p b ell)
    (i : Index p.L p.m p.t) (target : BinaryFoldedFormation.BinaryTable n) :
    let M := FoldedBackendExecution.windowQuerySize n
    (execute graph i target).newControl≤M*(1000*(p.L+p.m+1)^5+32)+8+
      (48*p.L+24+(M*(32*(p.L-p.m)+48)+8))+(RetainedRootWindows.slots (p.L-p.m)*40+8)+
      RetainedWindowCompletion.controlBudget (sources graph i) M+40 := by
  let roots := graph.permuted.transformed.source.roots
  let targets := GraphCompletionRequests.prepare f p roots.source.shape target
  have hp := GraphCompletionRequests.prepare_control f p roots.source.shape target
  have hr := GraphCompletionRequests.project_control i.right (roots.keys.value.masks.get i.normal)
    (roots.keys.value.masks.get i.opposite) targets.physical.value
  have hl := layouts_control graph i
  have hc : (execute graph i target).completed.control≤RetainedWindowCompletion.controlBudget (sources graph i) (FoldedBackendExecution.windowQuerySize n) :=
    RetainedWindowCompletion.execute_control _ _ _
  exact Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hp hr) hl) hc) 40

theorem fromInputs_newBits {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (bandL bandR ell : ℕ) (i : Index p.L p.m p.t) :
    let graph := GraphPrefixProgram.fromInputs f p block input bandL bandR ell
    let out := fromInputs f p block input bandL bandR ell i
    let B := GraphCompletionRequests.metadataWidth n h (FoldedBackendExecution.physicalFold f) f.cyclic
    out.newBitSteps≤10000*(B+1)^2+
      2000000*FoldedBackendExecution.windowQuerySize n*(GraphTargetWidth.width input.target+B+10)^2+
      RetainedWindowCompletion.bitBudget (sources graph i) (magnitude p.L p.m ell) (FoldedBackendExecution.windowQuerySize n) := by
  have hp := GraphTargetWidth.prepare_formation_bits f p
    (GraphPrefixProgram.fromInputs f p block input bandL bandR ell).permuted.transformed.source.roots.source.shape input.target
  have hc := fromInputs_bits f p block input bandL bandR ell i
  dsimp only at hp hc ⊢
  have hz : (fromInputs f p block input bandL bandR ell i).targets.physical.bitSteps=0 := GraphCompletionRequests.prepare_bits _ _ _ _
  have hr : (fromInputs f p block input bandL bandR ell i).residuals.bitSteps=0 := GraphCompletionRequests.project_bits _ _ _ _
  have hl : (fromInputs f p block input bandL bandR ell i).layouts.bitSteps=0 := layouts_bits _ _
  unfold Prepared.newBitSteps
  simp only [hz,hr,hl,Nat.add_zero]
  exact Nat.add_le_add hp hc

/-- The leaf-count and prefix factors combine to a linear exponent in the
physical dimension. The additional window factor is kept in the sum width. -/
theorem aggregate_magnitude (L m ell : ℕ) :
    RetainedWindowCompletion.leafMagnitude (L-m) ell (magnitude L m ell)=2^(3*(L-m)+L+4*m) := by
  unfold RetainedWindowCompletion.leafMagnitude magnitude
  rw [show (4:ℕ)=2^2 by decide,← pow_mul]
  simp only [← pow_add]
  congr 1
  have hd := WindowPrefixProgram.dimension (L-m) ell
  omega

theorem fromInputs_width {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (bandL bandR ell : ℕ) (i : Index p.L p.m p.t)
    (request : Fin (FoldedBackendExecution.windowQuerySize n)) (col : Fin ((p.m+1)*f.cyclic)) :
    (BinaryCell.view (((fromInputs f p block input bandL bandR ell i).completed.value.sums.value.get request).output.get col)).natAbs.size≤
      3*(p.L-p.m)+p.L+4*p.m+(RetainedRootWindows.slots (p.L-p.m)).size := by
  apply BinaryWalshBounds.natAbs_size_of_le_power_mul
  have h := fromInputs_abs f p block input bandL bandR ell i request col
  rw [aggregate_magnitude] at h
  simpa only [Nat.mul_comm] using h

#print axioms aggregate_magnitude
#print axioms fromInputs_width

#print axioms layouts_get
#print axioms layouts_bits
#print axioms layouts_control
#print axioms residuals_size
#print axioms execute_view
#print axioms fromInputs_reconstruct
#print axioms fromInputs_contraction
#print axioms fromInputs_bound
#print axioms fromInputs_abs
#print axioms fromInputs_bits
#print axioms execute_control
#print axioms fromInputs_newBits
end ThinMatrix.GraphRootCompletion
