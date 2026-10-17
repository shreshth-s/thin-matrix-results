import BinaryBackendExecution
import BinaryFoldedFormationCorrect
import BinaryFoldedTargets
import BinaryControllerExecution

/-!
# Shared binary folded count producer

Original inputs are stored binary cells. Public cached dimensions are supplied
by the parameter program and justified by erased equalities. One global
backend preparation is retained per middle block. Signed-window requests are
formed once and reused by every block. Native matrix/count views occur only
in correctness statements.
-/
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace ThinMatrix.BinaryFoldedFactory
open scoped BigOperators
open BinaryFoldedFormation
open Fin.CommRing

/-- Actual public dimensions and the LOW arithmetic width.
The native expressions in the equalities are proof-only specifications. -/
structure Plan {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r) where
  L : ℕ
  m : ℕ
  t : ℕ
  foldWidth : ℕ
  N : ℕ
  D : ℕ
  raw : ℕ
  lowWidth : ℕ
  foldWidth_eq : foldWidth=FoldedCounts.foldWidth (FoldedBackendExecution.physicalFold f)
  N_eq : N=FoldedBackendExecution.outerSize n (FoldedBackendExecution.physicalFold f)
  D_eq : D=FoldedBackendExecution.middleSize h (FoldedBackendExecution.physicalFold f)
  raw_eq : raw=FoldedBackendExecution.rawMiddle h (FoldedBackendExecution.physicalFold f)
  m_le_L : m≤L
  t_le : t≤2*m
  middle_fit : D≤4^m

abbrev SourceResult {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r) (block : ℕ) :=
  BinaryCell.Result (Sources n h (FoldedBackendExecution.physicalFold f) f.cyclic block)

def Plan.castLeft {n h r : ℕ} {f : CompactBlocks.PhysicalFactorization r} (p : Plan (n:=n) (h:=h) f)
    (data : Left (FoldedBackendExecution.outerSize n (FoldedBackendExecution.physicalFold f))
      (FoldedBackendExecution.middleSize h (FoldedBackendExecution.physicalFold f)) f.cyclic) :
    BinaryBackendExecution.OriginalLeft p.N p.D f.cyclic :=
  Vector.cast (by rw [p.N_eq,p.D_eq]) data

def Plan.castRight {n h r : ℕ} {f : CompactBlocks.PhysicalFactorization r} (p : Plan (n:=n) (h:=h) f)
    (data : Right (FoldedBackendExecution.outerSize n (FoldedBackendExecution.physicalFold f))
      (FoldedBackendExecution.middleSize h (FoldedBackendExecution.physicalFold f)) f.cyclic) :
    BinaryBackendExecution.OriginalRight p.N p.D f.cyclic :=
  Vector.cast (by rw [p.N_eq,p.D_eq]) data

/-- The source result keeps its formation counter and complete cyclic arrays.
Its block label is stored public data, so one ordinary vector stores all blocks. -/
structure PreparedBlock {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r) (p : Plan (n:=n) (h:=h) f) where
  block : ℕ
  sources : SourceResult (n:=n) (h:=h) f block
  prepared : BinaryBackendExecution.PreparedGlobal p.N p.D p.L p.m p.t f.cyclic

def prepareBlock {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r) (p : Plan (n:=n) (h:=h) f)
    (b : Fin (CompactBlocks.blockCount n h)) (input : Inputs n) : PreparedBlock f p :=
  let sources:=formSourcesCached f b input p.foldWidth p.N p.D p.raw
    p.foldWidth_eq p.N_eq p.D_eq p.raw_eq
  let prepared:=BinaryBackendExecution.prepareGlobal (L:=p.L) (m:=p.m) (t:=p.t) p.lowWidth 1
    (p.castLeft sources.value.left) (p.castRight sources.value.right)
  ⟨b.val,sources,prepared⟩

def PreparedBlock.bitSteps {n h r : ℕ} {f : CompactBlocks.PhysicalFactorization r} {p : Plan (n:=n) (h:=h) f}
    (block : PreparedBlock f p) : ℕ := block.sources.bitSteps+block.prepared.bitSteps

structure PreparedRequests {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r) where
  geometry : BinaryCell.Result (Geometry n h (FoldedBackendExecution.physicalFold f) f.cyclic 0)
  requests : BinaryCell.Result (Vector
    (TilingCosts.Request (FoldedBackendExecution.outerSize n (FoldedBackendExecution.physicalFold f)) f.cyclic)
    (FoldedBackendExecution.windowQuerySize n))

def prepareRequests {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r) (p : Plan (n:=n) (h:=h) f)
    (T : BinaryTable n) : PreparedRequests (n:=n) (h:=h) f :=
  let geometry:=makeGeometryCached n h (FoldedBackendExecution.physicalFold f) f.cyclic 0
    p.foldWidth p.N p.D p.raw p.foldWidth_eq p.N_eq p.D_eq p.raw_eq
  let requests:=BinaryFoldedTargets.requests f geometry.value T
  ⟨geometry,requests⟩

theorem prepareRequests_values {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : Plan (n:=n) (h:=h) f) (T : BinaryTable n) :
    (prepareRequests f p T).requests.value=FoldedBackendExecution.requests f (viewTable T) :=
  BinaryFoldedTargets.requests_values f _ T

/-- Binary source values are literal zero/one cells, regardless of the
original integer magnitudes. The backend's original coefficient cap is one. -/
theorem sources_left_abs {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : Plan (n:=n) (h:=h) f) (b : Fin (CompactBlocks.blockCount n h)) (input : Inputs n)
    (address : Fin (p.N*p.D)) (coeff : Fin f.cyclic) :
    (((BinaryBackendExecution.viewLeft (p.castLeft (prepareBlock f p b input).sources.value.left)).get address).get coeff).natAbs≤1 := by
  cases p with
  | mk L m t w N D raw lowWidth hw hN hD hraw hm ht hfit =>
    subst N D
    simp only [prepareBlock,Plan.castLeft,Vector.cast_rfl,formSourcesCached_refines]
    change (((BinaryFoldedFormation.viewLeft (formSources f b input).value.left).get address).get coeff).natAbs≤1
    rw [BinaryFoldedFormationCorrect.formSources_left_view]
    exact FoldedBackendExecution.formLeft_abs f b (viewTable input.left) address coeff


theorem sources_right_abs {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : Plan (n:=n) (h:=h) f) (b : Fin (CompactBlocks.blockCount n h)) (input : Inputs n)
    (address : Fin (p.D*p.N)) (coeff : Fin f.cyclic) :
    (((BinaryBackendExecution.viewRight (p.castRight (prepareBlock f p b input).sources.value.right)).get address).get coeff).natAbs≤1 := by
  cases p with
  | mk L m t w N D raw lowWidth hw hN hD hraw hm ht hfit =>
    subst N D
    simp only [prepareBlock,Plan.castRight,Vector.cast_rfl,formSourcesCached_refines]
    change (((BinaryFoldedFormation.viewRight (formSources f b input).value.right).get address).get coeff).natAbs≤1
    rw [BinaryFoldedFormationCorrect.formSources_right_view]
    exact FoldedBackendExecution.formRight_abs f b (viewTable input.right) address coeff

structure Retained {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r) (p : Plan (n:=n) (h:=h) f) where
  targets : PreparedRequests (n:=n) (h:=h) f
  blocks : BinaryControllerExecution.Result (Vector (PreparedBlock f p) (CompactBlocks.blockCount n h))
  queries : BinaryControllerExecution.Result
    (Vector (BinaryBackendExecution.GlobalQuery p.L p.m p.t f.cyclic) (EndToEndAPSP.incidenceSize n h))

/-- The request vector is formed once. Eager tabulation retains every block
preparation and every query result; projections below read these payloads. -/
def prepareRetained {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : Plan (n:=n) (h:=h) f) (input : Inputs n) : Retained f p :=
  let targets:=prepareRequests f p input.target
  let blocks:=BinaryControllerExecution.tabulate (fun b : Fin (CompactBlocks.blockCount n h)=>
    let block:=prepareBlock f p b input
    (⟨block,block.bitSteps,6,0⟩ : BinaryControllerExecution.Result (PreparedBlock f p)))
  let queries:=BinaryControllerExecution.tabulate (fun index : Fin (EndToEndAPSP.incidenceSize n h)=>
    let x:=(EndToEndAPSP.incidenceEquiv n h).symm index
    let request:=targets.requests.value.get (FoldedBackendExecution.windowQueryEquiv n (x.1,x.2.2))
    let block:=blocks.value.get x.2.1
    let answer:=BinaryBackendExecution.queryGlobalExecution (ThinMatrixBackend.tileWidth_pos p.L p.m p.m_le_L)
      block.prepared (Fin.cast p.N_eq.symm request.row) (Fin.cast p.N_eq.symm request.column) request.coefficient
    (⟨answer,answer.result.operations,20,0⟩ : BinaryControllerExecution.Result _))
  ⟨targets,blocks,queries⟩

def Retained.cells {n h r : ℕ} {f : CompactBlocks.PhysicalFactorization r} {p : Plan (n:=n) (h:=h) f}
    (payload : Retained f p) : Vector BinaryCell.Cell (EndToEndAPSP.incidenceSize n h) :=
  payload.queries.value.map (fun query=>query.result.value)

def Retained.bitSteps {n h r : ℕ} {f : CompactBlocks.PhysicalFactorization r} {p : Plan (n:=n) (h:=h) f}
    (payload : Retained f p) : ℕ :=
  payload.targets.geometry.bitSteps+payload.targets.requests.bitSteps+payload.blocks.bitSteps+payload.queries.bitSteps

def Retained.controlSites {n h r : ℕ} {f : CompactBlocks.PhysicalFactorization r} {p : Plan (n:=n) (h:=h) f}
    (payload : Retained f p) : ℕ := payload.blocks.controlSites+payload.queries.controlSites+10

abbrev Payload (n h : ℕ) := Σ r : ℕ, Σ f : CompactBlocks.PhysicalFactorization r,
  Σ p : Plan (n:=n) (h:=h) f, Retained f p

/-- The nonnegative wrapper preserves the stored result bits. Its returned
counter is combined with the same retained producer, without rerunning it. -/
def wrapRetained {n h r : ℕ} {f : CompactBlocks.PhysicalFactorization r} {p : Plan (n:=n) (h:=h) f}
    (payload : Retained f p) (hnonnegative : ∀i,0≤BinaryCell.view (payload.cells.get i)) :
    BinaryControllerExecution.Result (BinaryControllerExecution.Table (EndToEndAPSP.incidenceSize n h) (Payload n h)) :=
  let wrapped:=BinaryControllerExecution.Table.fromCells payload.cells hnonnegative ⟨r,f,p,payload⟩ 0
  let bits:=payload.bitSteps+wrapped.bitSteps
  let control:=payload.controlSites+wrapped.controlSites
  ⟨{wrapped.value with work:=bits+control},bits,control,wrapped.arithSites⟩

theorem wrapRetained_work {n h r : ℕ} {f : CompactBlocks.PhysicalFactorization r} {p : Plan (n:=n) (h:=h) f}
    (payload : Retained f p) (hnonnegative : ∀i,0≤BinaryCell.view (payload.cells.get i)) :
    (wrapRetained payload hnonnegative).value.work=
      (wrapRetained payload hnonnegative).bitSteps+(wrapRetained payload hnonnegative).controlSites := rfl

theorem wrapRetained_get {n h r : ℕ} {f : CompactBlocks.PhysicalFactorization r} {p : Plan (n:=n) (h:=h) f}
    (payload : Retained f p) (hnonnegative : ∀i,0≤BinaryCell.view (payload.cells.get i))
    (index : Fin (EndToEndAPSP.incidenceSize n h)) :
    ((wrapRetained payload hnonnegative).value.counts.get index).cell=payload.cells.get index := by
  exact BinaryControllerExecution.Table.fromCells_get _ _ _ _ _

theorem prepareBlock_query {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : Plan (n:=n) (h:=h) f) (b : Fin (CompactBlocks.blockCount n h)) (input : Inputs n)
    (i j : Fin n) (w : Fin 3) :
    (BinaryBackendExecution.queryGlobal (ThinMatrixBackend.tileWidth_pos p.L p.m p.m_le_L)
      (prepareBlock f p b input).prepared
      (Fin.cast p.N_eq.symm (CompactBlocks.outerEquiv n (FoldedBackendExecution.physicalFold f)
        (i,FoldedCounts.residueLow (FoldedBackendExecution.target (viewTable input.target) i j w : ZMod (FoldedBackendExecution.physicalFold f)))))
      (Fin.cast p.N_eq.symm (CompactBlocks.outerEquiv n (FoldedBackendExecution.physicalFold f)
        (j,FoldedCounts.residueHigh (FoldedBackendExecution.target (viewTable input.target) i j w : ZMod (FoldedBackendExecution.physicalFold f)))))
      ((-FoldedBackendExecution.target (viewTable input.target) i j w : ℤ) : Fin f.cyclic)).value.view =
      FoldedBackendExecution.semanticCoefficient f b (viewTable input.left) (viewTable input.right)
        (viewTable input.target) i j w := by
  have hl := sources_left_abs f p b input
  have hr := sources_right_abs f p b input
  cases p with
  | mk L m t width N D raw lowWidth hw hN hD hraw hm ht hfit =>
    subst N D
    simp only [prepareBlock,Plan.castLeft,Plan.castRight,Vector.cast_rfl,Fin.cast_eq_self,
      formSourcesCached_refines] at hl hr ⊢
    simp only [BinaryBackendExecution.viewLeft_get] at hl
    simp only [BinaryBackendExecution.viewRight_get] at hr
    rw [BinaryBackendExecution.prepared_queryGlobal_correct lowWidth (by decide) hm ht hfit _ _ hl hr]
    change (ThinMatrixBackend.originalLeftMatrix
      (BinaryFoldedFormation.viewLeft (formSources f b input).value.left) *
      ThinMatrixBackend.originalRightMatrix
        (BinaryFoldedFormation.viewRight (formSources f b input).value.right)) _ _ _ = _
    rw [BinaryFoldedFormationCorrect.formSources_left_view,
      BinaryFoldedFormationCorrect.formSources_right_view,FoldedBackendExecution.form_product]
    simp only [Matrix.reindex_apply,Matrix.submatrix_apply,Equiv.symm_apply_apply]
    rfl

theorem prepareRetained_cells_view {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : Plan (n:=n) (h:=h) f) (input : Inputs n) (index : Fin (EndToEndAPSP.incidenceSize n h)) :
    BinaryCell.view ((prepareRetained f p input).cells.get index) =
      let x:=(EndToEndAPSP.incidenceEquiv n h).symm index
      FoldedBackendExecution.semanticCoefficient f x.2.1 (viewTable input.left) (viewTable input.right)
        (viewTable input.target) x.1.1 x.1.2 x.2.2 := by
  simp only [Retained.cells,Vector.get_map,prepareRetained,BinaryControllerExecution.tabulate_value,
    Vector.get_ofFn,prepareRequests_values,FoldedBackendExecution.requests,Vector.get_ofFn,
    Equiv.symm_apply_apply]
  exact prepareBlock_query f p _ input _ _ _

theorem prepareRetained_nonnegative {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : Plan (n:=n) (h:=h) f) (input : Inputs n) (index : Fin (EndToEndAPSP.incidenceSize n h)) :
    0 ≤ BinaryCell.view ((prepareRetained f p input).cells.get index) := by
  rw [prepareRetained_cells_view]
  dsimp only
  rw [FoldedBackendExecution.semanticCoefficient_count]
  exact Nat.cast_nonneg _

theorem prepareRetained_modCount {n h r : ℕ} (hh : 0<h) (f : CompactBlocks.PhysicalFactorization r)
    (p : Plan (n:=n) (h:=h) f) (input : Inputs n) (index : Fin (EndToEndAPSP.incidenceSize n h)) :
    (BinaryCell.view ((prepareRetained f p input).cells.get index)).toNat =
      (EndToEndAPSP.flatInstance (h:=h) (viewTable input.left) (viewTable input.right)
        (viewTable input.target)).modCount r index := by
  rw [prepareRetained_cells_view]
  dsimp only
  rw [← FoldedBackendExecution.physicalTable_semantic CompleteAPSP.naiveBackend,
    CompactBlocks.physicalTable_correct hh]
  simp only [EndToEndAPSP.flatInstance,CompositeCertification.Instance.modCount,
    CompleteAPSP.incidenceInstance,Finset.card_filter]
  rfl

theorem prepareRetained_count_le {n h r : ℕ} (hh : 0<h) (f : CompactBlocks.PhysicalFactorization r)
    (p : Plan (n:=n) (h:=h) f) (input : Inputs n) (index : Fin (EndToEndAPSP.incidenceSize n h)) :
    (BinaryCell.view ((prepareRetained f p input).cells.get index)).toNat ≤ h := by
  rw [prepareRetained_cells_view]
  dsimp only
  rw [← FoldedBackendExecution.physicalTable_semantic CompleteAPSP.naiveBackend]
  exact CompactBlocks.physicalTable_le_block hh _ _ _ _ _ _

/-- Closed positive-factor count producer. The proof of nonnegativity is erased;
the same retained cells are wrapped without decoding or recomputing them. -/
def produce {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : Plan (n:=n) (h:=h) f) (input : Inputs n) :
    BinaryControllerExecution.Result (BinaryControllerExecution.Table (EndToEndAPSP.incidenceSize n h) (Payload n h)) :=
  let retained:=prepareRetained f p input
  wrapRetained retained (prepareRetained_nonnegative f p input)

theorem produce_modCount {n h r : ℕ} (hh : 0<h) (f : CompactBlocks.PhysicalFactorization r)
    (p : Plan (n:=n) (h:=h) f) (input : Inputs n) (index : Fin (EndToEndAPSP.incidenceSize n h)) :
    BinaryControllerExecution.nview ((produce f p input).value.counts.get index) =
      (EndToEndAPSP.flatInstance (h:=h) (viewTable input.left) (viewTable input.right)
        (viewTable input.target)).modCount r index := by
  unfold BinaryControllerExecution.nview produce
  rw [wrapRetained_get]
  exact prepareRetained_modCount hh f p input index

theorem produce_count_le {n h r : ℕ} (hh : 0<h) (f : CompactBlocks.PhysicalFactorization r)
    (p : Plan (n:=n) (h:=h) f) (input : Inputs n) (index : Fin (EndToEndAPSP.incidenceSize n h)) :
    BinaryControllerExecution.nview ((produce f p input).value.counts.get index) ≤ h := by
  unfold BinaryControllerExecution.nview produce
  rw [wrapRetained_get]
  exact prepareRetained_count_le hh f p input index

theorem produce_work {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : Plan (n:=n) (h:=h) f) (input : Inputs n) :
    (produce f p input).value.work=(produce f p input).bitSteps+(produce f p input).controlSites := rfl

/-- This sum is a proof-side description of the true bounded `scanTotals`
loop. The runtime loop reads counters already stored by eager tabulation. -/
theorem scanTotals_bitSteps {s : ℕ} {α : Type*}
    (stored : Vector (BinaryControllerExecution.Result α) s) (indices : List (Fin s)) :
    (BinaryControllerExecution.scanTotals stored indices).bitSteps =
      (indices.map (fun i => (stored.get i).bitSteps)).sum := by
  induction indices with
  | nil => rfl
  | cons i indices ih => simp [BinaryControllerExecution.scanTotals,ih]

theorem tabulate_bitSteps {s : ℕ} {α : Type*}
    (callback : Fin s → BinaryControllerExecution.Result α) :
    (BinaryControllerExecution.tabulate callback).bitSteps = ∑ i : Fin s, (callback i).bitSteps := by
  change (BinaryControllerExecution.scanTotals (Vector.ofFn callback) (List.finRange s)).bitSteps = _
  rw [scanTotals_bitSteps]
  simp only [Vector.get_ofFn]
  rw [← List.sum_toFinset _ (List.nodup_finRange _),List.toFinset_finRange]

theorem prepareRetained_block_get {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : Plan (n:=n) (h:=h) f) (input : Inputs n) (b : Fin (CompactBlocks.blockCount n h)) :
    (prepareRetained f p input).blocks.value.get b = prepareBlock f p b input := by
  simp only [prepareRetained,BinaryControllerExecution.tabulate_value,Vector.get_ofFn]

theorem prepareRetained_blockSteps {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : Plan (n:=n) (h:=h) f) (input : Inputs n) :
    (prepareRetained f p input).blocks.bitSteps =
      ∑ b : Fin (CompactBlocks.blockCount n h),
        ((prepareRetained f p input).blocks.value.get b).bitSteps := by
  simp only [prepareRetained,tabulate_bitSteps,BinaryControllerExecution.tabulate_value,Vector.get_ofFn]

theorem prepareRetained_querySteps {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : Plan (n:=n) (h:=h) f) (input : Inputs n) :
    (prepareRetained f p input).queries.bitSteps =
      ∑ i : Fin (EndToEndAPSP.incidenceSize n h),
        ((prepareRetained f p input).queries.value.get i).result.operations := by
  simp only [prepareRetained,tabulate_bitSteps,BinaryControllerExecution.tabulate_value,Vector.get_ofFn]

/-- Proof-side regrouping reads the already retained query vector. -/
def Retained.blockQueries {n h r : ℕ} {f : CompactBlocks.PhysicalFactorization r}
    {p : Plan (n:=n) (h:=h) f} (payload : Retained f p) (b : Fin (CompactBlocks.blockCount n h)) :
    Vector (BinaryBackendExecution.GlobalQuery p.L p.m p.t f.cyclic) (FoldedBackendExecution.windowQuerySize n) :=
  Vector.ofFn (fun i => payload.queries.value.get (FoldedBackendExecution.groupedIncidenceEquiv n h (b,i)))

theorem Retained.queryCounter_reindex {n h r : ℕ} {f : CompactBlocks.PhysicalFactorization r}
    {p : Plan (n:=n) (h:=h) f} (payload : Retained f p) :
    (∑ i : Fin (EndToEndAPSP.incidenceSize n h), (payload.queries.value.get i).result.operations) =
      ∑ b : Fin (CompactBlocks.blockCount n h),
        ∑ i : Fin (FoldedBackendExecution.windowQuerySize n), ((payload.blockQueries b).get i).result.operations := by
  rw [← (FoldedBackendExecution.groupedIncidenceEquiv n h).sum_comp
    (fun i => (payload.queries.value.get i).result.operations),Fintype.sum_prod_type]
  simp only [Retained.blockQueries,Vector.get_ofFn]

theorem prepareRetained_blockQueries {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : Plan (n:=n) (h:=h) f) (input : Inputs n) (b : Fin (CompactBlocks.blockCount n h))
    (i : Fin (FoldedBackendExecution.windowQuerySize n)) :
    ((prepareRetained f p input).blockQueries b).get i =
      let request:=(prepareRetained f p input).targets.requests.value.get i
      BinaryBackendExecution.queryGlobalExecution (ThinMatrixBackend.tileWidth_pos p.L p.m p.m_le_L)
        ((prepareRetained f p input).blocks.value.get b).prepared
        (Fin.cast p.N_eq.symm request.row) (Fin.cast p.N_eq.symm request.column) request.coefficient := by
  simp only [Retained.blockQueries,Vector.get_ofFn,prepareRetained,BinaryControllerExecution.tabulate_value,
    Vector.get_ofFn,FoldedBackendExecution.groupedIncidenceEquiv_decode]
  rw [Equiv.apply_symm_apply]

theorem prepareRetained_control {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : Plan (n:=n) (h:=h) f) (input : Inputs n) :
    (prepareRetained f p input).controlSites ≤
      19*CompactBlocks.blockCount n h+33*EndToEndAPSP.incidenceSize n h+14 := by
  have hb := BinaryControllerExecution.tabulate_control_le (C:=6)
    (fun b : Fin (CompactBlocks.blockCount n h) =>
      let block:=prepareBlock f p b input
      (⟨block,block.bitSteps,6,0⟩ : BinaryControllerExecution.Result _)) (by intro b; rfl)
  have hq := BinaryControllerExecution.tabulate_control_le (C:=20)
    (fun index : Fin (EndToEndAPSP.incidenceSize n h) =>
      let x:=(EndToEndAPSP.incidenceEquiv n h).symm index
      let request:=(prepareRequests f p input.target).requests.value.get
        (FoldedBackendExecution.windowQueryEquiv n (x.1,x.2.2))
      let block:=(prepareRetained f p input).blocks.value.get x.2.1
      let answer:=BinaryBackendExecution.queryGlobalExecution (ThinMatrixBackend.tileWidth_pos p.L p.m p.m_le_L)
        block.prepared (Fin.cast p.N_eq.symm request.row) (Fin.cast p.N_eq.symm request.column) request.coefficient
      (⟨answer,answer.result.operations,20,0⟩ : BinaryControllerExecution.Result _)) (by intro i; rfl)
  change (prepareRetained f p input).blocks.controlSites ≤ _ at hb
  change (prepareRetained f p input).queries.controlSites ≤ _ at hq
  unfold Retained.controlSites
  omega

theorem wrapRetained_bitSteps {n h r : ℕ} {f : CompactBlocks.PhysicalFactorization r}
    {p : Plan (n:=n) (h:=h) f} (payload : Retained f p)
    (hnonnegative : ∀i,0≤BinaryCell.view (payload.cells.get i)) :
    (wrapRetained payload hnonnegative).bitSteps=payload.bitSteps := by
  have hz := BinaryControllerExecution.tabulate_zero_bits
    (fun i => (⟨⟨payload.cells.get i,hnonnegative i⟩,0,1,0⟩ :
      BinaryControllerExecution.Result BinaryControllerExecution.NatCell)) (by intro i; rfl)
  change payload.bitSteps+(BinaryControllerExecution.tabulate
    (fun i => (⟨⟨payload.cells.get i,hnonnegative i⟩,0,1,0⟩ :
      BinaryControllerExecution.Result BinaryControllerExecution.NatCell))).bitSteps = _
  rw [hz]
  omega

theorem produce_bitSteps {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : Plan (n:=n) (h:=h) f) (input : Inputs n) :
    (produce f p input).bitSteps=(prepareRetained f p input).bitSteps :=
  wrapRetained_bitSteps _ _

theorem produce_control {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : Plan (n:=n) (h:=h) f) (input : Inputs n) :
    (produce f p input).controlSites ≤
      19*CompactBlocks.blockCount n h+47*EndToEndAPSP.incidenceSize n h+19 := by
  have hret:=prepareRetained_control f p input
  have hwrap:=BinaryControllerExecution.Table.fromCells_control
    (prepareRetained f p input).cells (prepareRetained_nonnegative f p input)
    (⟨r,f,p,prepareRetained f p input⟩ : Payload n h) 0
  change (prepareRetained f p input).controlSites+_ ≤ _
  omega

theorem produce_ledger {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : Plan (n:=n) (h:=h) f) (input : Inputs n) :
    (produce f p input).value.work ≤
      (prepareRetained f p input).targets.geometry.bitSteps+
      (prepareRetained f p input).targets.requests.bitSteps+
      (∑ b : Fin (CompactBlocks.blockCount n h),
        ((prepareRetained f p input).blocks.value.get b).bitSteps)+
      (∑ i : Fin (EndToEndAPSP.incidenceSize n h),
        ((prepareRetained f p input).queries.value.get i).result.operations)+
      19*CompactBlocks.blockCount n h+47*EndToEndAPSP.incidenceSize n h+19 := by
  rw [produce_work,produce_bitSteps,Retained.bitSteps,prepareRetained_blockSteps,prepareRetained_querySteps]
  have hc:=produce_control f p input
  omega

#print axioms prepareRequests_values
#print axioms sources_left_abs
#print axioms prepareBlock_query
#print axioms prepareRetained_cells_view
#print axioms prepareRetained_nonnegative
#print axioms prepareRetained_modCount
#print axioms produce_modCount
#print axioms produce_count_le
#print axioms produce_work
#print axioms prepareRetained_blockSteps
#print axioms prepareRetained_querySteps
#print axioms Retained.queryCounter_reindex
#print axioms prepareRetained_blockQueries
#print axioms produce_ledger

end ThinMatrix.BinaryFoldedFactory
