import RetainedOppositeTransform

set_option autoImplicit false

/-! Every actual graph-derived window through the forward opposite transform.
Original roots/windows remain retained; every new intermediate layer and every
coefficient column is charged, without deduplicating family occurrences. -/
namespace ThinMatrix.GraphWindowTransforms
open GoodMapEmbedding BinaryGroupedCoordinates BinaryGroupedPreparation
open ExactHalfSourcePlan ResidualFamilyKeys
open scoped BigOperators

abbrev Entry (L m C : ℕ) := Vector (RetainedOppositeTransform.Trace (2*(L-m)) ((m+1)*C))
  (RetainedRootWindows.slots (L-m))
abbrev Family (L m C t : ℕ) := Vector (Vector (Vector (Entry L m C)
  (channelCount m t)) (goodSlots L m).card) (goodSlots L m).card
abbrev Both (L m C t : ℕ) := Family L m C t × Family L m C t
abbrev Transforms (L m C t : ℕ) := Vector (Vector (Vector (Both L m C t) (2*m+1)) (J m)) (J m)

def entry {L m C : ℕ} (e : RetainedRootWindows.Prepared L m C) : Run (Entry L m C) :=
  tabulate e.windows.components (fun s => RetainedOppositeTransform.execute (e.windows.components.get s))

def family {L m C t : ℕ} (xs : GraphRootWindows.Family L m C t) : Run (Family L m C t) :=
  tabulate xs (fun i => tabulate (xs.get i) (fun j => tabulate ((xs.get i).get j)
    (fun c => entry (((xs.get i).get j).get c))))

@[simp] theorem family_get {L m C t : ℕ} (xs : GraphRootWindows.Family L m C t)
    (i j : Fin (goodSlots L m).card) (c : Fin (channelCount m t)) :
    (((family xs).value.get i).get j).get c=(entry (((xs.get i).get j).get c)).value := by
  simp only [family,tabulate_get]

def execute {L m C t : ℕ} (xs : GraphRootWindows.Windows L m C t) : Run (Transforms L m C t) :=
  tabulate xs (fun u => tabulate (xs.get u) (fun v => tabulate ((xs.get u).get v) (fun run =>
    let a := family ((((xs.get u).get v).get run).1)
    let b := family ((((xs.get u).get v).get run).2)
    ⟨(a.value,b.value),a.bitSteps+b.bitSteps,a.control+b.control+8⟩)))

@[simp] theorem execute_get {L m C t : ℕ} (xs : GraphRootWindows.Windows L m C t)
    (u v : Fin (J m)) (run : Fin (2*m+1)) :
    (((execute xs).value.get u).get v).get run=
      ((family ((((xs.get u).get v).get run).1)).value,
       (family ((((xs.get u).get v).get run).2)).value) := by simp only [execute,tabulate_get]

def EntryBound {L m C : ℕ} (e : RetainedRootWindows.Prepared L m C) (A : ℕ) : Prop :=
  ∀ s, BinaryWindowPartition.InputBound (e.windows.components.get s) A

def FamilyBound {L m C t : ℕ} (xs : GraphRootWindows.Family L m C t) (A : ℕ) : Prop :=
  ∀ i j c, EntryBound (((xs.get i).get j).get c) A

def WindowBound {L m C t : ℕ} (xs : GraphRootWindows.Windows L m C t) (A : ℕ) : Prop :=
  ∀ u v run, FamilyBound ((((xs.get u).get v).get run).1) A ∧
    FamilyBound ((((xs.get u).get v).get run).2) A

def entryBitBudget (L m C A : ℕ) : ℕ := RetainedRootWindows.slots (L-m)*
  RetainedOppositeTransform.bitBudget (2*(L-m)) ((m+1)*C) (L-m) A

def entryControlBudget (L m C : ℕ) : ℕ := RetainedRootWindows.slots (L-m)*
  (RetainedOppositeTransform.controlBudget (2*(L-m)) ((m+1)*C) (L-m)+8*(L-m)+40)+8

theorem entry_bits {L m C : ℕ} (e : RetainedRootWindows.Prepared L m C) (A : ℕ) (ha : EntryBound e A) :
    (entry e).bitSteps≤entryBitBudget L m C A := tabulate_bits _ _ (fun s => RetainedOppositeTransform.execute_bits _ A (ha s))

theorem entry_control {L m C : ℕ} (e : RetainedRootWindows.Prepared L m C) :
    (entry e).control≤entryControlBudget L m C := by
  have h := tabulate_control e.windows.components (fun s => RetainedOppositeTransform.execute (e.windows.components.get s))
    (fun s => RetainedOppositeTransform.execute_control (e.windows.components.get s))
  simpa only [entry,entryControlBudget,Nat.add_assoc,show 8+32=40 by decide] using h

def familyBitBudget (L m C t G A : ℕ) : ℕ := G*(G*(channelCount m t*entryBitBudget L m C A))
def familyControlBudget (L m C t G : ℕ) : ℕ := G*(G*(channelCount m t*(entryControlBudget L m C+32)+40)+40)+8

theorem family_bits {L m C t : ℕ} (xs : GraphRootWindows.Family L m C t)
    (A : ℕ) (ha : FamilyBound xs A) :
    (family xs).bitSteps≤familyBitBudget L m C t (goodSlots L m).card A := by
  apply tabulate_bits; intro i
  apply tabulate_bits; intro j
  apply tabulate_bits; intro c
  exact entry_bits _ A (ha i j c)

theorem family_control {L m C t : ℕ} (xs : GraphRootWindows.Family L m C t) :
    (family xs).control≤familyControlBudget L m C t (goodSlots L m).card := by
  apply tabulate_control; intro i
  apply tabulate_control; intro j
  apply tabulate_control; intro c
  exact entry_control _

def bitBudget (L m C t G A : ℕ) : ℕ := J m*(J m*((2*m+1)*(2*familyBitBudget L m C t G A)))
def controlBudget (L m C t G : ℕ) : ℕ :=
  J m*(J m*((2*m+1)*(2*familyControlBudget L m C t G+40)+40)+40)+8

theorem execute_bits {L m C t : ℕ} (xs : GraphRootWindows.Windows L m C t)
    (A : ℕ) (ha : WindowBound xs A) :
    (execute xs).bitSteps≤bitBudget L m C t (goodSlots L m).card A := by
  apply tabulate_bits; intro u
  apply tabulate_bits; intro v
  apply tabulate_bits; intro run
  have hl := family_bits ((((xs.get u).get v).get run).1) A (ha u v run).1
  have hr := family_bits ((((xs.get u).get v).get run).2) A (ha u v run).2
  dsimp only
  omega

theorem execute_control {L m C t : ℕ} (xs : GraphRootWindows.Windows L m C t) :
    (execute xs).control≤controlBudget L m C t (goodSlots L m).card := by
  apply tabulate_control; intro u
  apply tabulate_control; intro v
  apply tabulate_control; intro run
  have hl := family_control ((((xs.get u).get v).get run).1)
  have hr := family_control ((((xs.get u).get v).get run).2)
  dsimp only
  omega

structure Prepared {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : ℕ) where
  source : GraphRootWindows.Prepared f p block
  transformed : Run (Transforms p.L p.m f.cyclic p.t)

def fromInputs {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (bandL bandR ell : ℕ) : Prepared f p block :=
  let source := GraphRootWindows.fromInputs f p block input bandL bandR ell
  let transformed := execute source.windows.value
  ⟨source,transformed⟩

theorem window_bound {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (bandL bandR ell : ℕ) :
    WindowBound (GraphRootWindows.fromInputs f p block input bandL bandR ell).windows.value
      (2^p.m*(4^p.m*2^(p.L+p.m))) := by
  intro u v run
  constructor <;> intro i j c s
  · rw [GraphRootWindows.fromInputs_left_entry]
    exact RetainedRootWindows.execute_magnitude ell _ _
      ((GraphRootWindows.root_bound f p block input bandL bandR u v run).1 i j c) s
  · rw [GraphRootWindows.fromInputs_right_entry]
    exact RetainedRootWindows.execute_magnitude ell _ _
      ((GraphRootWindows.root_bound f p block input bandL bandR u v run).2 i j c) s

theorem fromInputs_bits {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (bandL bandR ell : ℕ) :
    (fromInputs f p block input bandL bandR ell).transformed.bitSteps≤
      bitBudget p.L p.m f.cyclic p.t (goodSlots p.L p.m).card (2^p.m*(4^p.m*2^(p.L+p.m))) :=
  execute_bits _ _ (window_bound f p block input bandL bandR ell)

theorem fromInputs_control {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (bandL bandR ell : ℕ) :
    (fromInputs f p block input bandL bandR ell).transformed.control≤
      controlBudget p.L p.m f.cyclic p.t (goodSlots p.L p.m).card := execute_control _

theorem fromInputs_left_entry {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (bandL bandR ell : ℕ)
    (u v : Fin (J p.m)) (run : Fin (2*p.m+1))
    (i j : Fin (goodSlots p.L p.m).card) (c : Fin (channelCount p.m p.t))
    (slot : Fin (RetainedRootWindows.slots (p.L-p.m))) :
    ((((((((fromInputs f p block input bandL bandR ell).transformed.value.get u).get v).get run).1).get i).get j).get c).get slot=
      (RetainedOppositeTransform.execute (((((((((GraphRootWindows.fromInputs f p block input bandL bandR ell).windows.value.get u).get v).get run).1).get i).get j).get c).windows.components.get slot)).value := by
  simp only [fromInputs,execute_get,family_get,entry,tabulate_get]

theorem fromInputs_left_reconstruct {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (bandL bandR ell : ℕ)
    (u v : Fin (J p.m)) (run : Fin (2*p.m+1))
    (i j : Fin (goodSlots p.L p.m).card) (c : Fin (channelCount p.m p.t))
    (w : CroppedGroupedSuffix.Word (2*(p.L-p.m))) (d : Fin (p.m+1)) (residue : Fin f.cyclic) :
    (∑ slot, OppositeWindowLayer.value (((((((((fromInputs f p block input bandL bandR ell).transformed.value.get u).get v).get run).1).get i).get j).get c).get slot).result w (finProdFinEquiv (d,residue)))=
      RetainedOppositeTransform.evaluate (RetainedOppositeTransform.axes (p.L-p.m))
        (fun word => BinaryResidualPolynomial.cellView ((ResidualWindowSource.rows ((((((((GraphResidualFamilies.fromInputs f p block input bandL bandR).roots.value.get u).get v).get run).1).get i).get j).get c)).get
          (StoredGroupedCompletion.rawIndex _ word)) d residue) w := by
  letI : NeZero f.cyclic := ⟨Nat.ne_of_gt f.cyclic_pos⟩
  simp_rw [fromInputs_left_entry,GraphRootWindows.fromInputs_left_entry]
  change (∑ slot, OppositeWindowLayer.value
    (RetainedOppositeTransform.execute (((RetainedRootWindows.execute ell ((((((((GraphResidualFamilies.fromInputs f p block input bandL bandR).roots.value.get u).get v).get run).1).get i).get j).get c)).value.windows.components.get slot))).value.result
      w (finProdFinEquiv (d,residue)))=_
  rw [GraphResidualFamilies.fromInputs_left_entry]
  exact RetainedOppositeTransform.sum_windows ell _ _ _ _ w d residue

theorem fromInputs_right_entry {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (bandL bandR ell : ℕ)
    (u v : Fin (J p.m)) (run : Fin (2*p.m+1))
    (i j : Fin (goodSlots p.L p.m).card) (c : Fin (channelCount p.m p.t))
    (slot : Fin (RetainedRootWindows.slots (p.L-p.m))) :
    ((((((((fromInputs f p block input bandL bandR ell).transformed.value.get u).get v).get run).2).get i).get j).get c).get slot=
      (RetainedOppositeTransform.execute (((((((((GraphRootWindows.fromInputs f p block input bandL bandR ell).windows.value.get u).get v).get run).2).get i).get j).get c).windows.components.get slot)).value := by
  simp only [fromInputs,execute_get,family_get,entry,tabulate_get]

theorem fromInputs_right_reconstruct {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (bandL bandR ell : ℕ)
    (u v : Fin (J p.m)) (run : Fin (2*p.m+1))
    (i j : Fin (goodSlots p.L p.m).card) (c : Fin (channelCount p.m p.t))
    (w : CroppedGroupedSuffix.Word (2*(p.L-p.m))) (d : Fin (p.m+1)) (residue : Fin f.cyclic) :
    (∑ slot, OppositeWindowLayer.value (((((((((fromInputs f p block input bandL bandR ell).transformed.value.get u).get v).get run).2).get i).get j).get c).get slot).result w (finProdFinEquiv (d,residue)))=
      RetainedOppositeTransform.evaluate (RetainedOppositeTransform.axes (p.L-p.m))
        (fun word => BinaryResidualPolynomial.cellView ((ResidualWindowSource.rows ((((((((GraphResidualFamilies.fromInputs f p block input bandL bandR).roots.value.get u).get v).get run).2).get i).get j).get c)).get
          (StoredGroupedCompletion.rawIndex _ word)) d residue) w := by
  letI : NeZero f.cyclic := ⟨Nat.ne_of_gt f.cyclic_pos⟩
  simp_rw [fromInputs_right_entry,GraphRootWindows.fromInputs_right_entry]
  change (∑ slot, OppositeWindowLayer.value
    (RetainedOppositeTransform.execute (((RetainedRootWindows.execute ell ((((((((GraphResidualFamilies.fromInputs f p block input bandL bandR).roots.value.get u).get v).get run).2).get i).get j).get c)).value.windows.components.get slot))).value.result
      w (finProdFinEquiv (d,residue)))=_
  rw [GraphResidualFamilies.fromInputs_right_entry]
  exact RetainedOppositeTransform.sum_windows ell _ _ _ _ w d residue

#print axioms family_get
#print axioms execute_get
#print axioms entry_bits
#print axioms entry_control
#print axioms family_bits
#print axioms family_control
#print axioms execute_bits
#print axioms execute_control
#print axioms window_bound
#print axioms fromInputs_bits
#print axioms fromInputs_control
#print axioms fromInputs_left_entry
#print axioms fromInputs_right_entry
#print axioms fromInputs_left_reconstruct
#print axioms fromInputs_right_reconstruct
end ThinMatrix.GraphWindowTransforms
