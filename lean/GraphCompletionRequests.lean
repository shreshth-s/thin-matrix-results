import WindowCompletionRequests
import BinaryFoldedFormationCost

set_option autoImplicit false

/-! Actual folded requests and physical ordinary labels. All request
occurrences are retained. Band/rank tags are retained for the pending root
aggregation; this phase does not silently discard unmatched requests.
Native decoding and labels have indexed-register costs, separately from the
existing binary target-formation circuits. -/
namespace ThinMatrix.GraphCompletionRequests
open BinaryCell BinaryGroupedCoordinates BinaryGroupedPreparation GoodMapEmbedding
open scoped BigOperators

structure Physical (L m C : ℕ) where
  bandL : ℕ
  bandR : ℕ
  row : Fin (ThinMatrixBackend.tileWidth L m)
  column : Fin (ThinMatrixBackend.tileWidth L m)
  coefficient : Fin C
  outside : Vector (Fin 4) (2*L)

/-- This allowance includes row decoding, complement scans, Delta dot loops,
materialization of all physical labels and the stored tags. It is indexed
control; arithmetic on their unbounded addresses is not claimed binary. -/
def locate {N L m C : ℕ} (shape : ThinMatrixBackend.ShapePlan L m) (hm : m≤L)
    (request : TilingCosts.Request N C) : Run (Physical L m C) :=
  let a := ThinMatrixBackend.storedLocate shape (ThinMatrixBackend.tileWidth_pos L m hm) request.row
  let b := ThinMatrixBackend.storedLocate shape (ThinMatrixBackend.tileWidth_pos L m hm) request.column
  let row := RowIndexing.rowUnrank shape.layout a.2
  let col := RowIndexing.rowUnrank shape.layout b.2
  let geometry := BinaryBackendExecution.queryGeometry shape.environment row col
  ⟨⟨a.1.val,b.1.val,a.2,b.2,request.coefficient,Vector.ofFn geometry.outside⟩,0,1000*(L+m+1)^5⟩

theorem locate_outside {N L m C : ℕ} (shape : ThinMatrixBackend.ShapePlan L m) (hm : m≤L)
    (request : TilingCosts.Request N C) :
    (locate shape hm request).value.outside.get=
      (ThinMatrixBackend.storedQueryGeometry shape.environment
        (RowIndexing.rowUnrank shape.layout (ThinMatrixBackend.storedLocate shape (ThinMatrixBackend.tileWidth_pos L m hm) request.row).2)
        (RowIndexing.rowUnrank shape.layout (ThinMatrixBackend.storedLocate shape (ThinMatrixBackend.tileWidth_pos L m hm) request.column).2)).outside := by
  funext i; simp [locate]

theorem locate_tags {N L m C : ℕ} (shape : ThinMatrixBackend.ShapePlan L m) (hm : m≤L)
    (request : TilingCosts.Request N C) :
    (locate shape hm request).value.bandL=request.row.val/shape.width ∧
    (locate shape hm request).value.bandR=request.column.val/shape.width ∧
    (locate shape hm request).value.coefficient=request.coefficient := by
  simp [locate,ThinMatrixBackend.storedLocate,TilingCosts.locate,TilingCosts.splitIndex,TilingCosts.originalIndex]

def castRequest {N M C : ℕ} (h : N=M) (q : TilingCosts.Request N C) : TilingCosts.Request M C :=
  ⟨Fin.cast h q.row,Fin.cast h q.column,q.coefficient⟩

structure Prepared {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) where
  folded : BinaryFoldedFactory.PreparedRequests (n:=n) (h:=h) f
  physical : Run (Vector (Physical p.L p.m f.cyclic) (FoldedBackendExecution.windowQuerySize n))

def prepare {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (shape : ThinMatrixBackend.ShapePlan p.L p.m)
    (target : BinaryFoldedFormation.BinaryTable n) : Prepared f p :=
  let requests := BinaryFoldedFactory.prepareRequests f p target
  let physical := tabulate requests.requests.value (fun i => locate shape p.m_le_L (castRequest p.N_eq.symm (requests.requests.value.get i)))
  ⟨requests,physical⟩

theorem prepare_get {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (shape : ThinMatrixBackend.ShapePlan p.L p.m)
    (target : BinaryFoldedFormation.BinaryTable n) (i : Fin (FoldedBackendExecution.windowQuerySize n)) :
    (prepare f p shape target).physical.value.get i=
      (locate shape p.m_le_L (castRequest p.N_eq.symm ((FoldedBackendExecution.requests f (BinaryFoldedFormation.viewTable target)).get i))).value := by
  simp only [prepare,tabulate_get,BinaryFoldedFactory.prepareRequests_values]

theorem prepare_bits {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (shape : ThinMatrixBackend.ShapePlan p.L p.m)
    (target : BinaryFoldedFormation.BinaryTable n) : (prepare f p shape target).physical.bitSteps=0 := by
  simp [prepare,tabulate_bits_eq,locate]

theorem prepare_control {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (shape : ThinMatrixBackend.ShapePlan p.L p.m)
    (target : BinaryFoldedFormation.BinaryTable n) :
    (prepare f p shape target).physical.control≤FoldedBackendExecution.windowQuerySize n*(1000*(p.L+p.m+1)^5+32)+8 :=
  tabulate_control _ _ (by intro i; rfl)

def metadataWidth (n h d q : ℕ) : ℕ := n.size+h.size+d.size+q.size+
  (FoldedCounts.foldWidth d).size+(FoldedBackendExecution.outerSize n d).size+
  (FoldedBackendExecution.middleSize h d).size+(FoldedBackendExecution.rawMiddle h d).size

noncomputable def targetWidth {n : ℕ} (target : BinaryFoldedFormation.BinaryTable n) : ℕ :=
  ∑ i, ∑ j, (view ((target.get i).get j)).natAbs.size

theorem target_width {n : ℕ} (target : BinaryFoldedFormation.BinaryTable n) (i j : Fin n) :
    (view ((target.get i).get j)).natAbs.size≤targetWidth target := by
  have ha : (view ((target.get i).get j)).natAbs.size≤∑ j, (view ((target.get i).get j)).natAbs.size :=
    Finset.single_le_sum (f:=fun j => (view ((target.get i).get j)).natAbs.size) (fun j _ => Nat.zero_le _) (Finset.mem_univ j)
  have hb : (∑ j, (view ((target.get i).get j)).natAbs.size)≤targetWidth target :=
    Finset.single_le_sum (f:=fun i => ∑ j, (view ((target.get i).get j)).natAbs.size) (fun i _ => Nat.zero_le _) (Finset.mem_univ i)
  exact ha.trans hb

theorem prepare_formation_bits {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (shape : ThinMatrixBackend.ShapePlan p.L p.m)
    (target : BinaryFoldedFormation.BinaryTable n) :
    let B := metadataWidth n h (FoldedBackendExecution.physicalFold f) f.cyclic
    (prepare f p shape target).folded.geometry.bitSteps+(prepare f p shape target).folded.requests.bitSteps≤
      10000*(B+1)^2+2000000*FoldedBackendExecution.windowQuerySize n*(targetWidth target+B+10)^2 := by
  dsimp only
  have hb : BinaryFoldedFormationCost.MetadataBound n h (FoldedBackendExecution.physicalFold f) f.cyclic 0
      (metadataWidth n h (FoldedBackendExecution.physicalFold f) f.cyclic) := by
    constructor <;> simp only [metadataWidth,Nat.size_zero] <;> omega
  have ht : BinaryFoldedTargets.MetadataBound n (FoldedBackendExecution.physicalFold f) f.cyclic
      (metadataWidth n h (FoldedBackendExecution.physicalFold f) f.cyclic) :=
    ⟨hb.n_size,hb.d_size,hb.q_size,hb.width_size⟩
  have hg := BinaryFoldedFormationCost.makeGeometry_cost hb
  have hr := BinaryFoldedTargets.requests_cost f (BinaryFoldedFactory.prepareRequests f p target).geometry.value target ht (target_width target)
  apply Nat.add_le_add _ hr
  simpa only [prepare,BinaryFoldedFactory.prepareRequests,BinaryFoldedFormation.makeGeometryCached_refines] using hg

/-- Actual retained residual positions, in the same filtered order used by
ResidualLayout and the root program. No assumed position table is supplied. -/
def positions {L m : ℕ} (mask : ResidualFamilyKeys.Mask L m) : Run (Vector (Fin L) (L-m)) :=
  ⟨⟨(ResidualLayout.remaining mask.bits).toArray,by simpa using ResidualFamilyKeys.remaining_size mask⟩,0,24*mask.bits.toArray.size+8⟩

theorem positions_get {L m : ℕ} (mask : ResidualFamilyKeys.Mask L m) (i : Fin (L-m)) :
    (positions mask).value.get i=(ResidualLayout.remaining mask.bits)[i.val]'(by rw [ResidualFamilyKeys.remaining_size]; exact i.isLt) := rfl

def residual {L m C : ℕ} (right : Bool) (normal opposite : Vector (Fin L) (L-m))
    (request : Physical L m C) : Run (Vector (Fin 4) (2*(L-m))) :=
  let a := GroupedPreparation.ofStoredFn normal (fun i => request.outside.get
    (if right then CompleteThinProduct.physicalRight (normal.get i) else CompleteThinProduct.physicalLeft (normal.get i)))
  let b := GroupedPreparation.ofStoredFn opposite (fun i => request.outside.get
    (if right then CompleteThinProduct.physicalLeft (opposite.get i) else CompleteThinProduct.physicalRight (opposite.get i)))
  ⟨Vector.cast (by omega) (a++b),0,16*(normal.toArray.size+opposite.toArray.size)+16⟩

theorem residual_get {L m C : ℕ} (right : Bool) (normal opposite : Vector (Fin L) (L-m))
    (request : Physical L m C) (i : Fin (2*(L-m))) :
    (residual right normal opposite request).value.get i=
      Fin.append
        (fun j => request.outside.get (if right then CompleteThinProduct.physicalRight (normal.get j) else CompleteThinProduct.physicalLeft (normal.get j)))
        (fun j => request.outside.get (if right then CompleteThinProduct.physicalLeft (opposite.get j) else CompleteThinProduct.physicalRight (opposite.get j)))
        (Fin.cast (by omega : 2*(L-m)=(L-m)+(L-m)) i) := by
  simp only [residual,GroupedPreparation.ofStoredFn_eq,Vector.get_cast]
  generalize Fin.cast (by omega : 2*(L-m)=(L-m)+(L-m)) i=z
  refine Fin.addCases (fun j => ?_) (fun j => ?_) z <;>
    simp [Vector.get_eq_getElem]
  simp only [Fin.append,Fin.addCases]
  simp

structure Residuals (L m : ℕ) where
  normalPositions : Vector (Fin L) (L-m)
  oppositePositions : Vector (Fin L) (L-m)
  labels : Array (Vector (Fin 4) (2*(L-m)))

def project {L m C M : ℕ} (right : Bool) (normal opposite : ResidualFamilyKeys.Mask L m)
    (requests : Vector (Physical L m C) M) : Run (Residuals L m) :=
  let a := positions normal
  let b := positions opposite
  let out := mapArray (residual right a.value b.value) requests.toArray
  ⟨⟨a.value,b.value,out.value⟩,out.bitSteps,a.control+b.control+out.control+8⟩

@[simp] theorem project_size {L m C M : ℕ} (right : Bool) (normal opposite : ResidualFamilyKeys.Mask L m)
    (requests : Vector (Physical L m C) M) : (project right normal opposite requests).value.labels.size=M := by simp [project]

theorem project_get {L m C M : ℕ} (right : Bool) (normal opposite : ResidualFamilyKeys.Mask L m)
    (requests : Vector (Physical L m C) M) (i : Fin M) :
    (project right normal opposite requests).value.labels[i.val]'(by simp)=
      (residual right (positions normal).value (positions opposite).value (requests.get i)).value := by
  have hh := mapArray_get (residual right (positions normal).value (positions opposite).value) requests.toArray i.val (by simp)
  exact hh

theorem project_bits {L m C M : ℕ} (right : Bool) (normal opposite : ResidualFamilyKeys.Mask L m)
    (requests : Vector (Physical L m C) M) : (project right normal opposite requests).bitSteps=0 := by
  apply Nat.eq_zero_of_le_zero
  exact (mapArray_bits _ _ (W:=0) (by intro q _; rfl)).trans (by simp)

theorem project_control {L m C M : ℕ} (right : Bool) (normal opposite : ResidualFamilyKeys.Mask L m)
    (requests : Vector (Physical L m C) M) :
    (project right normal opposite requests).control≤48*L+24+(M*(32*(L-m)+48)+8) := by
  have h := mapArray_control (residual right (positions normal).value (positions opposite).value) requests.toArray
    (W:=32*(L-m)+16) (by intro q _; simp [residual]; omega)
  simp only [project,positions,Vector.size_toArray] at h ⊢
  nlinarith

#print axioms locate_outside
#print axioms locate_tags
#print axioms prepare_get
#print axioms prepare_bits
#print axioms prepare_control
#print axioms target_width
#print axioms prepare_formation_bits
#print axioms positions_get
#print axioms residual_get
#print axioms project_size
#print axioms project_get
#print axioms project_bits
#print axioms project_control
end ThinMatrix.GraphCompletionRequests
