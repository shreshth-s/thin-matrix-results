import GraphRootCompletion

set_option autoImplicit false
set_option maxRecDepth 4000

/-! Match the actual physical request's band and good-mask ranks to one root.
The executed all-window result is copied for accepts and zeroed otherwise;
every request and every degree/cyclic column keeps its original position.
Native quotient/comparison work is indexed control, not binary addressing. -/
namespace ThinMatrix.RootRequestSelection
open BinaryCell BinaryGroupedCoordinates BinaryGroupedPreparation GoodMapEmbedding

def rowRank {L m : ℕ} (row : Fin (ThinMatrixBackend.tileWidth L m)) : Fin (goodSlots L m).card :=
  (finProdFinEquiv.symm row).1

theorem rowRank_value {L m : ℕ} (row : Fin (ThinMatrixBackend.tileWidth L m)) :
    (rowRank row).val=row.val/4^(L-m) := rfl

theorem rowRank_decoded {L m : ℕ} (store : RowIndexing.GoodIndexStore L m)
    (row : Fin (ThinMatrixBackend.tileWidth L m)) :
    rowRank row=RowIndexing.goodRankEquiv L m (RowIndexing.rowUnrank store row).1 := by
  apply Fin.ext
  exact (RowIndexing.rowUnrank_good_rank store row).symm

def ranks {L m C : ℕ} (right : Bool) (q : GraphCompletionRequests.Physical L m C) :=
  if right then (rowRank q.column,rowRank q.row) else (rowRank q.row,rowRank q.column)

def accepts {L m C : ℕ} (bandL bandR : ℕ) (right : Bool)
    (normal opposite : Fin (goodSlots L m).card) (q : GraphCompletionRequests.Physical L m C) : Bool :=
  decide (q.bandL=bandL ∧ q.bandR=bandR ∧ (ranks right q).1=normal ∧ (ranks right q).2=opposite)

theorem matches_iff {L m C : ℕ} (bandL bandR : ℕ) (right : Bool)
    (normal opposite : Fin (goodSlots L m).card) (q : GraphCompletionRequests.Physical L m C) :
    accepts bandL bandR right normal opposite q=true ↔
      q.bandL=bandL ∧ q.bandR=bandR ∧ (ranks right q).1=normal ∧ (ranks right q).2=opposite := by
  simp only [accepts,decide_eq_true_eq]

theorem unique_ranks {L m C : ℕ} (right : Bool) (q : GraphCompletionRequests.Physical L m C) :
    ∃! pair : Fin (goodSlots L m).card × Fin (goodSlots L m).card,
      accepts q.bandL q.bandR right pair.1 pair.2 q=true := by
  refine ⟨ranks right q,by simp [accepts],?_⟩
  intro pair hp
  rw [matches_iff] at hp
  exact Prod.ext hp.2.2.1.symm hp.2.2.2.symm

theorem matched_mask {L m : ℕ} (store : RowIndexing.GoodIndexStore L m)
    (row : Fin (ThinMatrixBackend.tileWidth L m)) :
    SourceFormation.cubeSupport (ResidualFamilyKeys.maskAt store (rowRank row)).bits.get=
      (RowIndexing.rowUnrank store row).1.val := by
  rw [ResidualFamilyKeys.maskAt_support,rowRank_decoded,Equiv.symm_apply_apply]

theorem selected_masks {L m C : ℕ} (store : RowIndexing.GoodIndexStore L m) (t bandL bandR : ℕ)
    (right : Bool) (normal opposite : Fin (goodSlots L m).card) (q : GraphCompletionRequests.Physical L m C)
    (h : accepts bandL bandR right normal opposite q=true) :
    SourceFormation.cubeSupport ((ResidualFamilyKeys.prepare store t).value.masks.get normal).bits.get=
      (RowIndexing.rowUnrank store (if right then q.column else q.row)).1.val ∧
    SourceFormation.cubeSupport ((ResidualFamilyKeys.prepare store t).value.masks.get opposite).bits.get=
      (RowIndexing.rowUnrank store (if right then q.row else q.column)).1.val := by
  rw [matches_iff] at h
  simp only [ResidualFamilyKeys.prepare_masks]
  cases right <;> simp only [ranks,Bool.false_eq_true,↓reduceIte] at h ⊢ <;>
    rw [← h.2.2.1,← h.2.2.2] <;> exact ⟨matched_mask _ _,matched_mask _ _⟩

structure Selected (C : ℕ) where
  matched : Bool
  output : Vector Cell C

def selectRow {C : ℕ} (matched : Bool) (row : Vector Cell C) : Run (Selected C) :=
  if matched then
    let copied := WindowCompletionRows.copyRow row
    ⟨⟨true,copied.value⟩,copied.bitSteps,copied.control+8⟩
  else ⟨⟨false,Vector.cast (by simp) (Vector.replicate row.toArray.size zero)⟩,0,3*row.toArray.size+8⟩

theorem selectRow_value {C : ℕ} (matched : Bool) (row : Vector Cell C) (c : Fin C) :
    view ((selectRow matched row).value.output.get c)=if matched then view (row.get c) else 0 := by
  cases matched <;> simp [selectRow]

theorem selectRow_bits {C : ℕ} (matched : Bool) (row : Vector Cell C) (A : ℕ)
    (ha : ∀ c, (view (row.get c)).natAbs≤A) :
    (selectRow matched row).bitSteps≤C*BackendScalarBits.backendScalarUnit A.size := by
  cases matched
  · exact Nat.zero_le _
  · exact WindowCompletionRows.copyRow_bits _ A ha

theorem selectRow_control {C : ℕ} (matched : Bool) (row : Vector Cell C) :
    (selectRow matched row).control≤40*C+16 := by
  have h := WindowCompletionRows.copyRow_control row
  cases matched <;> simp only [selectRow,Bool.false_eq_true,↓reduceIte,Vector.size_toArray] <;> omega

def select {L m C D M S : ℕ} (bandL bandR : ℕ) (right : Bool)
    (normal opposite : Fin (goodSlots L m).card) (requests : Vector (GraphCompletionRequests.Physical L m D) M)
    (rows : Vector (RetainedWindowCompletion.SumRow S C) M) : Run (Vector (Selected C) M) :=
  tabulate requests (fun j =>
    let out := selectRow (accepts bandL bandR right normal opposite (requests.get j)) (rows.get j).output
    ⟨out.value,out.bitSteps,out.control+64⟩)

theorem select_value {L m C D M S : ℕ} (bandL bandR : ℕ) (right : Bool)
    (normal opposite : Fin (goodSlots L m).card) (requests : Vector (GraphCompletionRequests.Physical L m D) M)
    (rows : Vector (RetainedWindowCompletion.SumRow S C) M) (j : Fin M) (c : Fin C) :
    view (((select bandL bandR right normal opposite requests rows).value.get j).output.get c)=
      if accepts bandL bandR right normal opposite (requests.get j) then view ((rows.get j).output.get c) else 0 := by
  simp only [select,tabulate_get,selectRow_value]

theorem select_matched {L m C D M S : ℕ} (bandL bandR : ℕ) (right : Bool)
    (normal opposite : Fin (goodSlots L m).card) (requests : Vector (GraphCompletionRequests.Physical L m D) M)
    (rows : Vector (RetainedWindowCompletion.SumRow S C) M) (j : Fin M) :
    ((select bandL bandR right normal opposite requests rows).value.get j).matched=
      accepts bandL bandR right normal opposite (requests.get j) := by
  simp only [select,tabulate_get]
  generalize accepts bandL bandR right normal opposite (requests.get j)=b
  cases b <;> rfl

theorem select_bits {L m C D M S : ℕ} (bandL bandR : ℕ) (right : Bool)
    (normal opposite : Fin (goodSlots L m).card) (requests : Vector (GraphCompletionRequests.Physical L m D) M)
    (rows : Vector (RetainedWindowCompletion.SumRow S C) M) (A : ℕ)
    (ha : ∀ j c, (view ((rows.get j).output.get c)).natAbs≤A) :
    (select bandL bandR right normal opposite requests rows).bitSteps≤M*(C*BackendScalarBits.backendScalarUnit A.size) :=
  tabulate_bits _ _ (fun j => selectRow_bits _ _ A (ha j))

theorem select_control {L m C D M S : ℕ} (bandL bandR : ℕ) (right : Bool)
    (normal opposite : Fin (goodSlots L m).card) (requests : Vector (GraphCompletionRequests.Physical L m D) M)
    (rows : Vector (RetainedWindowCompletion.SumRow S C) M) :
    (select bandL bandR right normal opposite requests rows).control≤M*(40*C+112)+8 := by
  exact tabulate_control _ _ (fun _ => Nat.add_le_add_right (selectRow_control _ _) 64)

structure Prepared {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (b ell : ℕ) where
  source : GraphRootCompletion.Prepared f p b ell
  selected : Run (Vector (Selected ((p.m+1)*f.cyclic)) (FoldedBackendExecution.windowQuerySize n))

def fromInputs {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (bandL bandR ell : ℕ) (i : GraphRootCompletion.Index p.L p.m p.t) : Prepared f p block ell :=
  let source := GraphRootCompletion.fromInputs f p block input bandL bandR ell i
  let selected := select bandL bandR i.right i.normal i.opposite source.targets.physical.value source.completed.value.sums.value
  ⟨source,selected⟩

theorem fromInputs_value {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (bandL bandR ell : ℕ) (i : GraphRootCompletion.Index p.L p.m p.t)
    (request : Fin (FoldedBackendExecution.windowQuerySize n)) (d : Fin (p.m+1)) (residue : Fin f.cyclic) :
    let out := fromInputs f p block input bandL bandR ell i
    BinaryCell.view ((out.selected.value.get request).output.get (finProdFinEquiv (d,residue)))=
      if accepts bandL bandR i.right i.normal i.opposite (out.source.targets.physical.value.get request) then
        EncoderCorrectness.tensorSum (fun _ : Fin (2*(p.L-p.m)) => 3)
          (OppositeTensorBridge.pushForms (RetainedOppositeTransform.axes (p.L-p.m))
            (fun j => BinaryPrefixContraction.form ((WindowCompletionRequests.orient
              (out.source.residuals.value.labels[request.val]'(by simp [out,fromInputs,GraphRootCompletion.fromInputs]))).value.get j)))
          (fun w => BinaryResidualPolynomial.cellView ((ResidualWindowSource.rows
            (GraphRootCompletion.root out.source.graph i)).get (StoredGroupedCompletion.rawIndex _ w)) d residue)
      else 0 := by
  dsimp only
  have hv := select_value bandL bandR i.right i.normal i.opposite
    (GraphRootCompletion.fromInputs f p block input bandL bandR ell i).targets.physical.value
    (GraphRootCompletion.fromInputs f p block input bandL bandR ell i).completed.value.sums.value request (finProdFinEquiv (d,residue))
  rw [GraphRootCompletion.fromInputs_contraction] at hv
  exact hv

theorem fromInputs_bits {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (bandL bandR ell : ℕ) (i : GraphRootCompletion.Index p.L p.m p.t) :
    (fromInputs f p block input bandL bandR ell i).selected.bitSteps≤
      FoldedBackendExecution.windowQuerySize n*(((p.m+1)*f.cyclic)*BackendScalarBits.backendScalarUnit
        (RetainedRootWindows.slots (p.L-p.m)*RetainedWindowCompletion.leafMagnitude (p.L-p.m) ell (GraphRootCompletion.magnitude p.L p.m ell)).size) :=
  select_bits _ _ _ _ _ _ _ _ (GraphRootCompletion.fromInputs_abs f p block input bandL bandR ell i)

theorem fromInputs_control {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (bandL bandR ell : ℕ) (i : GraphRootCompletion.Index p.L p.m p.t) :
    (fromInputs f p block input bandL bandR ell i).selected.control≤
      FoldedBackendExecution.windowQuerySize n*(40*((p.m+1)*f.cyclic)+112)+8 := select_control _ _ _ _ _ _ _

theorem fromInputs_selected_masks {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (bandL bandR ell : ℕ) (i : GraphRootCompletion.Index p.L p.m p.t)
    (request : Fin (FoldedBackendExecution.windowQuerySize n)) :
    let out := fromInputs f p block input bandL bandR ell i
    let roots := out.source.graph.permuted.transformed.source.roots
    let q := out.source.targets.physical.value.get request
    (out.selected.value.get request).matched=true →
      SourceFormation.cubeSupport (roots.keys.value.masks.get i.normal).bits.get=
        (RowIndexing.rowUnrank roots.source.shape.layout (if i.right then q.column else q.row)).1.val ∧
      SourceFormation.cubeSupport (roots.keys.value.masks.get i.opposite).bits.get=
        (RowIndexing.rowUnrank roots.source.shape.layout (if i.right then q.row else q.column)).1.val := by
  dsimp only
  intro hm
  have he := select_matched bandL bandR i.right i.normal i.opposite
    (GraphRootCompletion.fromInputs f p block input bandL bandR ell i).targets.physical.value
    (GraphRootCompletion.fromInputs f p block input bandL bandR ell i).completed.value.sums.value request
  have accepted := he.symm.trans hm
  exact selected_masks _ p.t bandL bandR i.right i.normal i.opposite _ accepted

#print axioms selected_masks
#print axioms fromInputs_selected_masks

#print axioms rowRank_value
#print axioms rowRank_decoded
#print axioms matches_iff
#print axioms unique_ranks
#print axioms matched_mask
#print axioms selectRow_value
#print axioms selectRow_bits
#print axioms selectRow_control
#print axioms select_value
#print axioms select_matched
#print axioms select_bits
#print axioms select_control
#print axioms fromInputs_value
#print axioms fromInputs_bits
#print axioms fromInputs_control
end ThinMatrix.RootRequestSelection
