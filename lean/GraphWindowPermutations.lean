import RetainedWindowPermutation

set_option autoImplicit false

/-! Reindex every retained graph/window transform with the selected side and
window occurrence inherited from the actual root construction. Length is
clamped once before partitioning. All coefficients and position tables persist. -/
namespace ThinMatrix.GraphWindowPermutations
open GoodMapEmbedding BinaryGroupedCoordinates BinaryGroupedPreparation
open ExactHalfSourcePlan ResidualFamilyKeys
open scoped BigOperators

abbrev Entry (L m C : ℕ) := Vector (RetainedWindowPermutation.Prepared (L-m) ((m+1)*C))
  (RetainedRootWindows.slots (L-m))
abbrev Family (L m C t : ℕ) := Vector (Vector (Vector (Entry L m C)
  (channelCount m t)) (goodSlots L m).card) (goodSlots L m).card
abbrev Both (L m C t : ℕ) := Family L m C t × Family L m C t
abbrev Results (L m C t : ℕ) := Vector (Vector (Vector (Both L m C t) (2*m+1)) (J m)) (J m)

def entry {L m C : ℕ} (ell : ℕ) (e : RetainedRootWindows.Prepared L m C)
    (ts : GraphWindowTransforms.Entry L m C) : Run (Entry L m C) :=
  let normal := decide (e.counts.2≤e.counts.1)
  let out := tabulate ts (fun slot => RetainedWindowPermutation.prepare ell normal slot (ts.get slot).result)
  ⟨out.value,out.bitSteps,out.control+8⟩

def family {L m C t : ℕ} (ell : ℕ) (xs : GraphRootWindows.Family L m C t)
    (ts : GraphWindowTransforms.Family L m C t) : Run (Family L m C t) :=
  tabulate ts (fun i => tabulate (ts.get i) (fun j => tabulate ((ts.get i).get j)
    (fun c => entry ell (((xs.get i).get j).get c) (((ts.get i).get j).get c))))

@[simp] theorem family_get {L m C t : ℕ} (ell : ℕ) (xs : GraphRootWindows.Family L m C t)
    (ts : GraphWindowTransforms.Family L m C t) (i j : Fin (goodSlots L m).card) (c : Fin (channelCount m t)) :
    (((family ell xs ts).value.get i).get j).get c=
      (entry ell (((xs.get i).get j).get c) (((ts.get i).get j).get c)).value := by
  simp only [family,tabulate_get]

def execute {L m C t : ℕ} (ell : ℕ) (xs : GraphRootWindows.Windows L m C t)
    (ts : GraphWindowTransforms.Transforms L m C t) : Run (Results L m C t) :=
  tabulate ts (fun u => tabulate (ts.get u) (fun v => tabulate ((ts.get u).get v) (fun run =>
    let a := family ell ((((xs.get u).get v).get run).1) ((((ts.get u).get v).get run).1)
    let b := family ell ((((xs.get u).get v).get run).2) ((((ts.get u).get v).get run).2)
    ⟨(a.value,b.value),a.bitSteps+b.bitSteps,a.control+b.control+8⟩)))

@[simp] theorem execute_get {L m C t : ℕ} (ell : ℕ) (xs : GraphRootWindows.Windows L m C t)
    (ts : GraphWindowTransforms.Transforms L m C t) (u v : Fin (J m)) (run : Fin (2*m+1)) :
    (((execute ell xs ts).value.get u).get v).get run=
      ((family ell ((((xs.get u).get v).get run).1) ((((ts.get u).get v).get run).1)).value,
       (family ell ((((xs.get u).get v).get run).2) ((((ts.get u).get v).get run).2)).value) := by
  simp only [execute,tabulate_get]

def EntryBound {L m C : ℕ} (ts : GraphWindowTransforms.Entry L m C) (A : ℕ) : Prop :=
  ∀ slot, OppositeWindowLayer.Bound (ts.get slot).result A

def FamilyBound {L m C t : ℕ} (ts : GraphWindowTransforms.Family L m C t) (A : ℕ) : Prop :=
  ∀ i j c, EntryBound (((ts.get i).get j).get c) A

def TransformBound {L m C t : ℕ} (ts : GraphWindowTransforms.Transforms L m C t) (A : ℕ) : Prop :=
  ∀ u v run, FamilyBound ((((ts.get u).get v).get run).1) A ∧
    FamilyBound ((((ts.get u).get v).get run).2) A

def entryBitBudget (L m C A : ℕ) : ℕ := RetainedRootWindows.slots (L-m)*
  RetainedWindowPermutation.bitBudget (2*(L-m)) ((m+1)*C) A

def entryControlBudget (L m C : ℕ) : ℕ := RetainedRootWindows.slots (L-m)*
  (128*(2*(L-m))+40+RetainedWindowPermutation.controlBudget (2*(L-m)) ((m+1)*C)+32)+8+8

theorem entry_bits {L m C : ℕ} (ell : ℕ) (e : RetainedRootWindows.Prepared L m C)
    (ts : GraphWindowTransforms.Entry L m C) (A : ℕ) (ha : EntryBound ts A) :
    (entry ell e ts).bitSteps≤entryBitBudget L m C A :=
  tabulate_bits _ _ (fun slot => RetainedWindowPermutation.prepare_bits _ _ _ _ A (ha slot))

theorem entry_control {L m C : ℕ} (ell : ℕ) (e : RetainedRootWindows.Prepared L m C)
    (ts : GraphWindowTransforms.Entry L m C) : (entry ell e ts).control≤entryControlBudget L m C :=
  Nat.add_le_add_right (tabulate_control _ _ (fun _ => RetainedWindowPermutation.prepare_control _ _ _ _)) 8

def familyBitBudget (L m C t G A : ℕ) : ℕ := G*(G*(channelCount m t*entryBitBudget L m C A))
def familyControlBudget (L m C t G : ℕ) : ℕ := G*(G*(channelCount m t*(entryControlBudget L m C+32)+40)+40)+8

theorem family_bits {L m C t : ℕ} (ell : ℕ) (xs : GraphRootWindows.Family L m C t)
    (ts : GraphWindowTransforms.Family L m C t) (A : ℕ) (ha : FamilyBound ts A) :
    (family ell xs ts).bitSteps≤familyBitBudget L m C t (goodSlots L m).card A := by
  apply tabulate_bits; intro i
  apply tabulate_bits; intro j
  apply tabulate_bits; intro c
  exact entry_bits _ _ _ A (ha i j c)

theorem family_control {L m C t : ℕ} (ell : ℕ) (xs : GraphRootWindows.Family L m C t)
    (ts : GraphWindowTransforms.Family L m C t) :
    (family ell xs ts).control≤familyControlBudget L m C t (goodSlots L m).card := by
  apply tabulate_control; intro i
  apply tabulate_control; intro j
  apply tabulate_control; intro c
  exact entry_control _ _ _

def bitBudget (L m C t G A : ℕ) : ℕ := J m*(J m*((2*m+1)*(2*familyBitBudget L m C t G A)))
def controlBudget (L m C t G : ℕ) : ℕ := J m*(J m*((2*m+1)*(2*familyControlBudget L m C t G+40)+40)+40)+8

theorem execute_bits {L m C t : ℕ} (ell : ℕ) (xs : GraphRootWindows.Windows L m C t)
    (ts : GraphWindowTransforms.Transforms L m C t) (A : ℕ) (ha : TransformBound ts A) :
    (execute ell xs ts).bitSteps≤bitBudget L m C t (goodSlots L m).card A := by
  apply tabulate_bits; intro u
  apply tabulate_bits; intro v
  apply tabulate_bits; intro run
  have hl := family_bits ell ((((xs.get u).get v).get run).1) ((((ts.get u).get v).get run).1) A (ha u v run).1
  have hr := family_bits ell ((((xs.get u).get v).get run).2) ((((ts.get u).get v).get run).2) A (ha u v run).2
  dsimp only
  omega

theorem execute_control {L m C t : ℕ} (ell : ℕ) (xs : GraphRootWindows.Windows L m C t)
    (ts : GraphWindowTransforms.Transforms L m C t) :
    (execute ell xs ts).control≤controlBudget L m C t (goodSlots L m).card := by
  apply tabulate_control; intro u
  apply tabulate_control; intro v
  apply tabulate_control; intro run
  have hl := family_control ell ((((xs.get u).get v).get run).1) ((((ts.get u).get v).get run).1)
  have hr := family_control ell ((((xs.get u).get v).get run).2) ((((ts.get u).get v).get run).2)
  dsimp only
  omega

structure Prepared {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : ℕ) where
  transformed : GraphWindowTransforms.Prepared f p block
  permuted : Run (Results p.L p.m f.cyclic p.t)

def fromInputs {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (bandL bandR ell : ℕ) : Prepared f p block :=
  let length := min ell (p.L-p.m)
  let transformed := GraphWindowTransforms.fromInputs f p block input bandL bandR length
  let out := execute length transformed.source.windows.value transformed.transformed.value
  ⟨transformed,⟨out.value,out.bitSteps,out.control+8⟩⟩

theorem transformed_bound {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (bandL bandR ell : ℕ) :
    TransformBound (GraphWindowTransforms.fromInputs f p block input bandL bandR ell).transformed.value
      (2^(p.L-p.m)*(2^p.m*(4^p.m*2^(p.L+p.m)))) := by
  intro u v run
  have hs := GraphWindowTransforms.window_bound f p block input bandL bandR ell u v run
  constructor <;> intro i j c slot
  · rw [GraphWindowTransforms.fromInputs_left_entry]
    exact RetainedOppositeTransform.execute_bound _ _ (hs.1 i j c slot)
  · rw [GraphWindowTransforms.fromInputs_right_entry]
    exact RetainedOppositeTransform.execute_bound _ _ (hs.2 i j c slot)

theorem fromInputs_bits {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (bandL bandR ell : ℕ) :
    (fromInputs f p block input bandL bandR ell).permuted.bitSteps≤
      bitBudget p.L p.m f.cyclic p.t (goodSlots p.L p.m).card (2^(p.L-p.m)*(2^p.m*(4^p.m*2^(p.L+p.m)))) :=
  execute_bits _ _ _ _ (transformed_bound f p block input bandL bandR (min ell (p.L-p.m)))

theorem fromInputs_control {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (bandL bandR ell : ℕ) :
    (fromInputs f p block input bandL bandR ell).permuted.control≤
      controlBudget p.L p.m f.cyclic p.t (goodSlots p.L p.m).card+8 :=
  Nat.add_le_add_right (execute_control _ _ _) 8

theorem fromInputs_left_entry {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (bandL bandR ell : ℕ)
    (u v : Fin (J p.m)) (run : Fin (2*p.m+1))
    (i j : Fin (goodSlots p.L p.m).card) (c : Fin (channelCount p.m p.t))
    (slot : Fin (RetainedRootWindows.slots (p.L-p.m))) :
    let length := min ell (p.L-p.m)
    let prior := GraphWindowTransforms.fromInputs f p block input bandL bandR length
    let window := (((((((prior.source.windows.value.get u).get v).get run).1).get i).get j).get c)
    let trace := ((((((((prior.transformed.value.get u).get v).get run).1).get i).get j).get c).get slot)
    (((((((((fromInputs f p block input bandL bandR ell).permuted.value.get u).get v).get run).1).get i).get j).get c).get slot)=
      (RetainedWindowPermutation.prepare length (decide (window.counts.2≤window.counts.1)) slot trace.result).value := by
  simp only [fromInputs,execute_get,family_get,entry,tabulate_get]

theorem fromInputs_right_entry {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (bandL bandR ell : ℕ)
    (u v : Fin (J p.m)) (run : Fin (2*p.m+1))
    (i j : Fin (goodSlots p.L p.m).card) (c : Fin (channelCount p.m p.t))
    (slot : Fin (RetainedRootWindows.slots (p.L-p.m))) :
    let length := min ell (p.L-p.m)
    let prior := GraphWindowTransforms.fromInputs f p block input bandL bandR length
    let window := (((((((prior.source.windows.value.get u).get v).get run).2).get i).get j).get c)
    let trace := ((((((((prior.transformed.value.get u).get v).get run).2).get i).get j).get c).get slot)
    (((((((((fromInputs f p block input bandL bandR ell).permuted.value.get u).get v).get run).2).get i).get j).get c).get slot)=
      (RetainedWindowPermutation.prepare length (decide (window.counts.2≤window.counts.1)) slot trace.result).value := by
  simp only [fromInputs,execute_get,family_get,entry,tabulate_get]

theorem fromInputs_left_reconstruct {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (bandL bandR ell : ℕ)
    (u v : Fin (J p.m)) (run : Fin (2*p.m+1))
    (i j : Fin (goodSlots p.L p.m).card) (c : Fin (channelCount p.m p.t))
    (w : CroppedGroupedSuffix.Word (2*(p.L-p.m))) (d : Fin (p.m+1)) (residue : Fin f.cyclic) :
    (∑ slot, let output := (((((((((fromInputs f p block input bandL bandR ell).permuted.value.get u).get v).get run).1).get i).get j).get c).get slot)
      OppositeWindowLayer.value output.coefficients (fun a => w (output.layout.forward.get a)) (finProdFinEquiv (d,residue)))=
      RetainedOppositeTransform.evaluate (RetainedOppositeTransform.axes (p.L-p.m))
        (fun word => BinaryResidualPolynomial.cellView ((ResidualWindowSource.rows ((((((((GraphResidualFamilies.fromInputs f p block input bandL bandR).roots.value.get u).get v).get run).1).get i).get j).get c)).get
          (StoredGroupedCompletion.rawIndex _ word)) d residue) w := by
  simp_rw [fromInputs_left_entry]
  simp only [RetainedWindowPermutation.prepare_recover]
  exact GraphWindowTransforms.fromInputs_left_reconstruct f p block input bandL bandR (min ell (p.L-p.m)) u v run i j c w d residue

theorem fromInputs_right_reconstruct {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (bandL bandR ell : ℕ)
    (u v : Fin (J p.m)) (run : Fin (2*p.m+1))
    (i j : Fin (goodSlots p.L p.m).card) (c : Fin (channelCount p.m p.t))
    (w : CroppedGroupedSuffix.Word (2*(p.L-p.m))) (d : Fin (p.m+1)) (residue : Fin f.cyclic) :
    (∑ slot, let output := (((((((((fromInputs f p block input bandL bandR ell).permuted.value.get u).get v).get run).2).get i).get j).get c).get slot)
      OppositeWindowLayer.value output.coefficients (fun a => w (output.layout.forward.get a)) (finProdFinEquiv (d,residue)))=
      RetainedOppositeTransform.evaluate (RetainedOppositeTransform.axes (p.L-p.m))
        (fun word => BinaryResidualPolynomial.cellView ((ResidualWindowSource.rows ((((((((GraphResidualFamilies.fromInputs f p block input bandL bandR).roots.value.get u).get v).get run).2).get i).get j).get c)).get
          (StoredGroupedCompletion.rawIndex _ word)) d residue) w := by
  simp_rw [fromInputs_right_entry]
  simp only [RetainedWindowPermutation.prepare_recover]
  exact GraphWindowTransforms.fromInputs_right_reconstruct f p block input bandL bandR (min ell (p.L-p.m)) u v run i j c w d residue

theorem fromInputs_left_support {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (bandL bandR ell : ℕ)
    (u v : Fin (J p.m)) (run : Fin (2*p.m+1))
    (i j : Fin (goodSlots p.L p.m).card) (c : Fin (channelCount p.m p.t))
    (slot : Fin (RetainedRootWindows.slots (p.L-p.m)))
    (w : CroppedGroupedSuffix.Word (2*(p.L-p.m))) (col : Fin ((p.m+1)*f.cyclic)) :
    let length := min ell (p.L-p.m)
    let window := ((((((((GraphRootWindows.fromInputs f p block input bandL bandR length).windows.value.get u).get v).get run).1).get i).get j).get c)
    (p.m/2-max window.counts.1 window.counts.2)*length/(p.L-p.m)<RetainedWindowPermutation.suffixRare (p.L-p.m) length w →
      OppositeWindowLayer.value (((((((((fromInputs f p block input bandL bandR ell).permuted.value.get u).get v).get run).1).get i).get j).get c).get slot).coefficients w col=0 := by
  dsimp only
  intro hw
  rw [fromInputs_left_entry]
  change OppositeWindowLayer.value (RetainedWindowPermutation.prepare (min ell (p.L-p.m))
    (decide (((((((((GraphRootWindows.fromInputs f p block input bandL bandR (min ell (p.L-p.m))).windows.value.get u).get v).get run).1).get i).get j).get c).counts.2≤
      ((((((((GraphRootWindows.fromInputs f p block input bandL bandR (min ell (p.L-p.m))).windows.value.get u).get v).get run).1).get i).get j).get c).counts.1)) slot
    (((((((((GraphWindowTransforms.fromInputs f p block input bandL bandR (min ell (p.L-p.m))).transformed.value.get u).get v).get run).1).get i).get j).get c).get slot).result).value.coefficients w col=0
  rw [GraphWindowTransforms.fromInputs_left_entry,GraphRootWindows.fromInputs_left_entry]
  rw [GraphRootWindows.fromInputs_left_entry] at hw
  simp only [RetainedRootWindows.execute] at hw ⊢
  have hh := RetainedWindowPermutation.partition_support (min ell (p.L-p.m)) (p.m/2)
    (RetainedRootWindows.weights ((((((((GraphResidualFamilies.fromInputs f p block input bandL bandR).roots.value.get u).get v).get run).1).get i).get j).get c).channel).value.1
    (RetainedRootWindows.weights ((((((((GraphResidualFamilies.fromInputs f p block input bandL bandR).roots.value.get u).get v).get run).1).get i).get j).get c).channel).value.2
    (ResidualWindowSource.execute ((((((((GraphResidualFamilies.fromInputs f p block input bandL bandR).roots.value.get u).get v).get run).1).get i).get j).get c)).value slot w col
  simp only [min_assoc,min_self] at hh
  exact hh hw

theorem fromInputs_right_support {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (bandL bandR ell : ℕ)
    (u v : Fin (J p.m)) (run : Fin (2*p.m+1))
    (i j : Fin (goodSlots p.L p.m).card) (c : Fin (channelCount p.m p.t))
    (slot : Fin (RetainedRootWindows.slots (p.L-p.m)))
    (w : CroppedGroupedSuffix.Word (2*(p.L-p.m))) (col : Fin ((p.m+1)*f.cyclic)) :
    let length := min ell (p.L-p.m)
    let window := ((((((((GraphRootWindows.fromInputs f p block input bandL bandR length).windows.value.get u).get v).get run).2).get i).get j).get c)
    (p.m/2-max window.counts.1 window.counts.2)*length/(p.L-p.m)<RetainedWindowPermutation.suffixRare (p.L-p.m) length w →
      OppositeWindowLayer.value (((((((((fromInputs f p block input bandL bandR ell).permuted.value.get u).get v).get run).2).get i).get j).get c).get slot).coefficients w col=0 := by
  dsimp only
  intro hw
  rw [fromInputs_right_entry]
  change OppositeWindowLayer.value (RetainedWindowPermutation.prepare (min ell (p.L-p.m))
    (decide (((((((((GraphRootWindows.fromInputs f p block input bandL bandR (min ell (p.L-p.m))).windows.value.get u).get v).get run).2).get i).get j).get c).counts.2≤
      ((((((((GraphRootWindows.fromInputs f p block input bandL bandR (min ell (p.L-p.m))).windows.value.get u).get v).get run).2).get i).get j).get c).counts.1)) slot
    (((((((((GraphWindowTransforms.fromInputs f p block input bandL bandR (min ell (p.L-p.m))).transformed.value.get u).get v).get run).2).get i).get j).get c).get slot).result).value.coefficients w col=0
  rw [GraphWindowTransforms.fromInputs_right_entry,GraphRootWindows.fromInputs_right_entry]
  rw [GraphRootWindows.fromInputs_right_entry] at hw
  simp only [RetainedRootWindows.execute] at hw ⊢
  have hh := RetainedWindowPermutation.partition_support (min ell (p.L-p.m)) (p.m/2)
    (RetainedRootWindows.weights ((((((((GraphResidualFamilies.fromInputs f p block input bandL bandR).roots.value.get u).get v).get run).2).get i).get j).get c).channel).value.1
    (RetainedRootWindows.weights ((((((((GraphResidualFamilies.fromInputs f p block input bandL bandR).roots.value.get u).get v).get run).2).get i).get j).get c).channel).value.2
    (ResidualWindowSource.execute ((((((((GraphResidualFamilies.fromInputs f p block input bandL bandR).roots.value.get u).get v).get run).2).get i).get j).get c)).value slot w col
  simp only [min_assoc,min_self] at hh
  exact hh hw

def entryCells {L m C : ℕ} (xs : Entry L m C) : ℕ :=
  (xs.toList.map (fun e => (e.coefficients.toList.map (fun row => row.toArray.size)).sum)).sum

theorem entryCells_eq {L m C : ℕ} (xs : Entry L m C) :
    entryCells xs=RetainedRootWindows.slots (L-m)*3^(2*(L-m))*((m+1)*C) := by
  simp only [entryCells,Vector.size_toArray,List.map_const',Vector.length_toList,List.sum_replicate,smul_eq_mul]
  ring

def familyCells {L m C t : ℕ} (xs : Family L m C t) : ℕ :=
  (xs.toList.map (fun row => (row.toList.map (fun group => (group.toList.map (fun e => entryCells e)).sum)).sum)).sum

theorem familyCells_eq {L m C t : ℕ} (xs : Family L m C t) :
    familyCells xs=(goodSlots L m).card^2*channelCount m t*(RetainedRootWindows.slots (L-m)*3^(2*(L-m))*((m+1)*C)) := by
  simp only [familyCells,entryCells_eq,List.map_const',Vector.length_toList,List.sum_replicate,smul_eq_mul]
  ring

def coefficientCells {L m C t : ℕ} (xs : Results L m C t) : ℕ :=
  (xs.toList.map (fun row => (row.toList.map (fun runs =>
    (runs.toList.map (fun both => familyCells both.1+familyCells both.2)).sum)).sum)).sum

theorem coefficientCells_eq {L m C t : ℕ} (xs : Results L m C t) :
    coefficientCells xs=2*(J m)^2*(2*m+1)*(goodSlots L m).card^2*channelCount m t*
      (RetainedRootWindows.slots (L-m)*3^(2*(L-m))*((m+1)*C)) := by
  simp only [coefficientCells,familyCells_eq,List.map_const',Vector.length_toList,List.sum_replicate,smul_eq_mul]
  ring

#print axioms fromInputs_left_support
#print axioms fromInputs_right_support
#print axioms entryCells_eq
#print axioms familyCells_eq
#print axioms coefficientCells_eq
#print axioms fromInputs_left_reconstruct
#print axioms fromInputs_right_reconstruct
#print axioms family_get
#print axioms execute_get
#print axioms entry_bits
#print axioms entry_control
#print axioms family_bits
#print axioms family_control
#print axioms execute_bits
#print axioms execute_control
#print axioms transformed_bound
#print axioms fromInputs_bits
#print axioms fromInputs_control
#print axioms fromInputs_left_entry
#print axioms fromInputs_right_entry
end ThinMatrix.GraphWindowPermutations
