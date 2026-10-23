import PairedRootRows
import ResidualChannelTranspose

set_option autoImplicit false
set_option maxRecDepth 5000
set_option maxHeartbeats 1000000

/-! Pair actual oriented graph-root completions. The graph preparation is
shared, but target formation/projection is presently executed for each side
and both executions are charged. Post-selection retains every request. -/
namespace ThinMatrix.GraphRootProducts
open GoodMapEmbedding ExactHalfSourcePlan ResidualFamilyKeys BinaryGroupedCoordinates BinaryGroupedPreparation
open BinaryCell BinaryResidualPolynomial

structure Index (L m t : ℕ) where
  u : Fin (J m)
  v : Fin (J m)
  run : Fin (2*m+1)
  left : Fin (goodSlots L m).card
  right : Fin (goodSlots L m).card
  channel : Fin (channelCount m t)

def Index.leftIndex {L m t : ℕ} (i : Index L m t) : GraphRootCompletion.Index L m t :=
  ⟨i.u,i.v,i.run,i.left,i.right,i.channel,false⟩

def transpose {n h r b ell : ℕ} {f : CompactBlocks.PhysicalFactorization r}
    {p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f} (graph : GraphPrefixProgram.Prepared f p b ell)
    (i : Index p.L p.m p.t) : Run (GraphRootCompletion.Index p.L p.m p.t) :=
  let j := ResidualChannelTranspose.locate graph.permuted.transformed.source.roots.keys.value.channels i.channel
  ⟨⟨i.u,i.v,i.run,i.right,i.left,j.value,true⟩,j.bitSteps,j.control+16⟩

theorem transpose_bits {n h r b ell : ℕ} {f : CompactBlocks.PhysicalFactorization r}
    {p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f} (graph : GraphPrefixProgram.Prepared f p b ell)
    (i : Index p.L p.m p.t) : (transpose graph i).bitSteps=0 := rfl

theorem transpose_control {n h r b ell : ℕ} {f : CompactBlocks.PhysicalFactorization r}
    {p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f} (graph : GraphPrefixProgram.Prepared f p b ell)
    (i : Index p.L p.m p.t) : (transpose graph i).control=ResidualChannelTranspose.budget p.m (channelCount p.m p.t)+16 := by
  simp only [transpose,ResidualChannelTranspose.locate_control]

theorem fromInputs_halves {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (bandL bandR ell : ℕ) (i : Index p.L p.m p.t) :
    let graph := GraphPrefixProgram.fromInputs f p block input bandL bandR ell
    let keys := graph.permuted.transformed.source.roots.keys.value.channels
    normal (keys.get (transpose graph i).value.channel)=opposite (keys.get i.channel) ∧
    opposite (keys.get (transpose graph i).value.channel)=normal (keys.get i.channel) := by
  dsimp only
  apply ResidualChannelTranspose.locate_halves
  exact ResidualFamilyKeys.prepare_channels _ _

def select {n h r b ell : ℕ} {f : CompactBlocks.PhysicalFactorization r}
    {p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f} (out : GraphRootCompletion.Prepared f p b ell)
    (i : GraphRootCompletion.Index p.L p.m p.t) (bandL bandR : ℕ) :=
  RootRequestSelection.select bandL bandR i.right i.normal i.opposite out.targets.physical.value out.completed.value.sums.value

structure Prepared {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (b ell : ℕ) where
  transposed : Run (GraphRootCompletion.Index p.L p.m p.t)
  left : GraphRootCompletion.Prepared f p b ell
  right : GraphRootCompletion.Prepared f p b ell
  leftSelected : Run (Vector (RootRequestSelection.Selected ((p.m+1)*f.cyclic)) (FoldedBackendExecution.windowQuerySize n))
  rightSelected : Run (Vector (RootRequestSelection.Selected ((p.m+1)*f.cyclic)) (FoldedBackendExecution.windowQuerySize n))
  paired : Run (PairedRootRows.Prepared (p.m+1) f.cyclic (FoldedBackendExecution.windowQuerySize n))

def execute {n h r b ell : ℕ} {f : CompactBlocks.PhysicalFactorization r}
    {p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f} (graph : GraphPrefixProgram.Prepared f p b ell)
    (i : Index p.L p.m p.t) (target : BinaryFoldedFormation.BinaryTable n) (bandL bandR : ℕ) : Prepared f p b ell :=
  let transposed := transpose graph i
  let left := GraphRootCompletion.execute graph i.leftIndex target
  let right := GraphRootCompletion.execute graph transposed.value target
  let a := select left i.leftIndex bandL bandR
  let b := select right transposed.value bandL bandR
  letI : NeZero f.cyclic := ⟨Nat.ne_of_gt f.cyclic_pos⟩
  let paired := PairedRootRows.execute a.value b.value
  ⟨transposed,left,right,a,b,paired⟩

def fromInputs {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (bandL bandR ell : ℕ) (i : Index p.L p.m p.t) : Prepared f p block ell :=
  execute (GraphPrefixProgram.fromInputs f p block input bandL bandR ell) i input.target bandL bandR

/-- The source-only polynomial: its coefficients are tensor contractions of
the actual retained root and actual projected labels, never returned answers. -/
noncomputable def rootPolynomial {n h r b ell : ℕ} {f : CompactBlocks.PhysicalFactorization r}
    {p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f} (graph : GraphPrefixProgram.Prepared f p b ell)
    (i : GraphRootCompletion.Index p.L p.m p.t) (target : BinaryFoldedFormation.BinaryTable n)
    (request : Fin (FoldedBackendExecution.windowQuerySize n)) : Polynomial (CyclicRing.Cyclic f.cyclic) :=
  let out := GraphRootCompletion.execute graph i target
  letI : NeZero f.cyclic := ⟨Nat.ne_of_gt f.cyclic_pos⟩
  CompletedRootProducts.polynomialOf (fun (d : Fin (p.m+1)) residue =>
    EncoderCorrectness.tensorSum (fun _ : Fin (2*(p.L-p.m)) => 3)
      (OppositeTensorBridge.pushForms (RetainedOppositeTransform.axes (p.L-p.m))
        (fun j => BinaryPrefixContraction.form ((WindowCompletionRequests.orient
          (out.residuals.value.labels[request.val]'(by simp [out]))).value.get j)))
      (fun w => cellView ((ResidualWindowSource.rows (GraphRootCompletion.root graph i)).get (StoredGroupedCompletion.rawIndex _ w)) d residue))

def accepted {n h r b ell : ℕ} {f : CompactBlocks.PhysicalFactorization r}
    {p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f} (graph : GraphPrefixProgram.Prepared f p b ell)
    (i : GraphRootCompletion.Index p.L p.m p.t) (target : BinaryFoldedFormation.BinaryTable n)
    (bandL bandR : ℕ) (request : Fin (FoldedBackendExecution.windowQuerySize n)) : Bool :=
  RootRequestSelection.accepts bandL bandR i.right i.normal i.opposite
    ((GraphRootCompletion.execute graph i target).targets.physical.value.get request)

theorem selected_polynomial {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (bandL bandR ell : ℕ) (i : GraphRootCompletion.Index p.L p.m p.t)
    (request : Fin (FoldedBackendExecution.windowQuerySize n)) :
    let graph := GraphPrefixProgram.fromInputs f p block input bandL bandR ell
    letI : NeZero f.cyclic := ⟨Nat.ne_of_gt f.cyclic_pos⟩
    ResidualPolynomialDegree.decode (CompletedRootProducts.inflate (p.m+1) f.cyclic
      (((select (GraphRootCompletion.execute graph i input.target) i bandL bandR).value.get request).output)).value=
      if accepted graph i input.target bandL bandR request then rootPolynomial graph i input.target request else 0 := by
  dsimp only
  letI : NeZero f.cyclic := ⟨Nat.ne_of_gt f.cyclic_pos⟩
  apply Polynomial.ext
  intro d
  funext residue
  rw [ResidualPolynomialDegree.decode_coeff]
  split
  · rename_i hd
    rw [CompletedRootProducts.inflate_value]
    have h := RootRequestSelection.fromInputs_value f p block input bandL bandR ell i request ⟨d,hd⟩ residue
    dsimp only at h
    calc
      _ = _ := h
      _ = _ := by
        change (if accepted _ i input.target bandL bandR request then _ else _) = _
        split <;> simp_all only [rootPolynomial,CompletedRootProducts.polynomialOf_coeff,Polynomial.coeff_zero,CyclicRing.zero_coeff,↓reduceDIte]
        rfl
  · rename_i hd
    split <;> simp only [rootPolynomial,CompletedRootProducts.polynomialOf_coeff,hd,↓reduceDIte,Polynomial.coeff_zero,CyclicRing.zero_coeff]

theorem accepts_pair {n h r b ell : ℕ} {f : CompactBlocks.PhysicalFactorization r}
    {p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f} (graph : GraphPrefixProgram.Prepared f p b ell)
    (i : Index p.L p.m p.t) (target : BinaryFoldedFormation.BinaryTable n) (bandL bandR : ℕ)
    (request : Fin (FoldedBackendExecution.windowQuerySize n)) :
    accepted graph (transpose graph i).value target bandL bandR request=accepted graph i.leftIndex target bandL bandR request := by
  simp only [accepted,transpose,Index.leftIndex,GraphRootCompletion.execute,RootRequestSelection.accepts,RootRequestSelection.ranks]
  simp only [Bool.false_eq_true,↓reduceIte]
  congr 1
  simp only [and_comm]

theorem fromInputs_product {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (bandL bandR ell : ℕ) (i : Index p.L p.m p.t)
    (request : Fin (FoldedBackendExecution.windowQuerySize n)) :
    let graph := GraphPrefixProgram.fromInputs f p block input bandL bandR ell
    letI : NeZero f.cyclic := ⟨Nat.ne_of_gt f.cyclic_pos⟩
    ResidualPolynomialDegree.decode ((fromInputs f p block input bandL bandR ell i).paired.value.products.value.get request)=
      if accepted graph i.leftIndex input.target bandL bandR request then
        rootPolynomial graph i.leftIndex input.target request*rootPolynomial graph (transpose graph i).value input.target request else 0 := by
  dsimp only
  letI : NeZero f.cyclic := ⟨Nat.ne_of_gt f.cyclic_pos⟩
  change ResidualPolynomialDegree.decode ((PairedRootRows.execute _ _).value.products.value.get request)=_
  rw [PairedRootRows.execute_polynomial,selected_polynomial,selected_polynomial,accepts_pair]
  split <;> simp_all

def magnitude (L m : ℕ) : ℕ := RetainedRootWindows.slots (L-m)*2^(3*(L-m)+L+4*m)

theorem selected_bound {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (bandL bandR ell : ℕ) (i : GraphRootCompletion.Index p.L p.m p.t) :
    PairedRootRows.BoundRows (magnitude p.L p.m)
      (select (GraphRootCompletion.fromInputs f p block input bandL bandR ell i) i bandL bandR).value := by
  intro request c
  simp only [select,RootRequestSelection.select_value]
  split
  · have h := GraphRootCompletion.fromInputs_abs f p block input bandL bandR ell i request c
    rwa [GraphRootCompletion.aggregate_magnitude] at h
  · simp

#print axioms transpose_bits
#print axioms transpose_control
#print axioms fromInputs_halves
#print axioms selected_polynomial
#print axioms accepts_pair
#print axioms fromInputs_product
#print axioms selected_bound
end ThinMatrix.GraphRootProducts
