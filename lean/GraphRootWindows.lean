import RetainedRootWindows

set_option autoImplicit false

/-! The actual graph-to-root program followed by retained window execution.
Every translation occurrence, run, good-set pair, strict channel key and both
inputs are traversed. Source/setup, root and window counters remain separate.
The scope is one physical block and band pair, not a complete APSP backend. -/
namespace ThinMatrix.GraphRootWindows
open GoodMapEmbedding BinaryGroupedCoordinates BinaryGroupedPreparation
open ExactHalfSourcePlan ResidualFamilyKeys
open scoped BigOperators

abbrev Family (L m C t : ℕ) := Vector (Vector (Vector (RetainedRootWindows.Prepared L m C)
  (channelCount m t)) (goodSlots L m).card) (goodSlots L m).card
abbrev Both (L m C t : ℕ) := Family L m C t × Family L m C t
abbrev Windows (L m C t : ℕ) := Vector (Vector (Vector (Both L m C t) (2*m+1)) (J m)) (J m)

def family {L m C t : ℕ} (ell : ℕ) (xs : RetainedResidualFamily.Family L m C t) : Run (Family L m C t) :=
  tabulate xs (fun i => tabulate (xs.get i) (fun j => tabulate ((xs.get i).get j)
    (fun c => RetainedRootWindows.execute ell (((xs.get i).get j).get c))))

@[simp] theorem family_get {L m C t : ℕ} (ell : ℕ) (xs : RetainedResidualFamily.Family L m C t)
    (i j : Fin (goodSlots L m).card) (c : Fin (channelCount m t)) :
    (((family ell xs).value.get i).get j).get c=
      (RetainedRootWindows.execute ell (((xs.get i).get j).get c)).value := by
  simp only [family,tabulate_get]

def execute {L m C t : ℕ} (ell : ℕ) (xs : GraphResidualFamilies.Roots L m C t) : Run (Windows L m C t) :=
  tabulate xs (fun u => tabulate (xs.get u) (fun v => tabulate ((xs.get u).get v) (fun run =>
    let a := family ell ((((xs.get u).get v).get run).1)
    let b := family ell ((((xs.get u).get v).get run).2)
    ⟨(a.value,b.value),a.bitSteps+b.bitSteps,a.control+b.control+8⟩)))

@[simp] theorem execute_get {L m C t : ℕ} (ell : ℕ) (xs : GraphResidualFamilies.Roots L m C t)
    (u v : Fin (J m)) (run : Fin (2*m+1)) :
    (((execute ell xs).value.get u).get v).get run=
      ((family ell ((((xs.get u).get v).get run).1)).value,
       (family ell ((((xs.get u).get v).get run).2)).value) := by simp only [execute,tabulate_get]

def FamilyBound {L m C t : ℕ} (xs : RetainedResidualFamily.Family L m C t) (A : ℕ) : Prop :=
  ∀ i j c, ResidualWindowSource.BoundRows (((xs.get i).get j).get c) A

def RootBound {L m C t : ℕ} (xs : GraphResidualFamilies.Roots L m C t) (A : ℕ) : Prop :=
  ∀ u v run, FamilyBound ((((xs.get u).get v).get run).1) A ∧
    FamilyBound ((((xs.get u).get v).get run).2) A

def familyBitBudget (L m C t G A : ℕ) : ℕ := G*(G*(channelCount m t*RetainedRootWindows.bitBudget L m C A))
def familyControlBudget (L m C t G ell : ℕ) : ℕ :=
  G*(G*(channelCount m t*(RetainedRootWindows.controlBudget L m C ell+32)+40)+40)+8

theorem family_bits {L m C t : ℕ} (ell : ℕ) (xs : RetainedResidualFamily.Family L m C t)
    (A : ℕ) (ha : FamilyBound xs A) :
    (family ell xs).bitSteps≤familyBitBudget L m C t (goodSlots L m).card A := by
  apply tabulate_bits; intro i
  apply tabulate_bits; intro j
  apply tabulate_bits; intro c
  exact RetainedRootWindows.execute_bits ell _ A (ha i j c)

theorem family_control {L m C t : ℕ} (ell : ℕ) (xs : RetainedResidualFamily.Family L m C t) :
    (family ell xs).control≤familyControlBudget L m C t (goodSlots L m).card ell := by
  apply tabulate_control; intro i
  apply tabulate_control; intro j
  apply tabulate_control; intro c
  exact RetainedRootWindows.execute_control ell _

def bitBudget (L m C t G A : ℕ) : ℕ := J m*(J m*((2*m+1)*(2*familyBitBudget L m C t G A)))
def controlBudget (L m C t G ell : ℕ) : ℕ :=
  J m*(J m*((2*m+1)*(2*familyControlBudget L m C t G ell+40)+40)+40)+8

theorem execute_bits {L m C t : ℕ} (ell : ℕ) (xs : GraphResidualFamilies.Roots L m C t)
    (A : ℕ) (ha : RootBound xs A) :
    (execute ell xs).bitSteps≤bitBudget L m C t (goodSlots L m).card A := by
  apply tabulate_bits; intro u
  apply tabulate_bits; intro v
  apply tabulate_bits; intro run
  have hl := family_bits ell ((((xs.get u).get v).get run).1) A (ha u v run).1
  have hr := family_bits ell ((((xs.get u).get v).get run).2) A (ha u v run).2
  dsimp only
  omega

theorem execute_control {L m C t : ℕ} (ell : ℕ) (xs : GraphResidualFamilies.Roots L m C t) :
    (execute ell xs).control≤controlBudget L m C t (goodSlots L m).card ell := by
  apply tabulate_control; intro u
  apply tabulate_control; intro v
  apply tabulate_control; intro run
  have hl := family_control ell ((((xs.get u).get v).get run).1)
  have hr := family_control ell ((((xs.get u).get v).get run).2)
  dsimp only
  omega

structure Prepared {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : ℕ) where
  roots : GraphResidualFamilies.Prepared f p block
  windows : Run (Windows p.L p.m f.cyclic p.t)

def fromInputs {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (bandL bandR ell : ℕ) : Prepared f p block :=
  let roots := GraphResidualFamilies.fromInputs f p block input bandL bandR
  let windows := execute ell roots.roots.value
  ⟨roots,windows⟩

theorem root_bound {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (bandL bandR : ℕ) :
    RootBound (GraphResidualFamilies.fromInputs f p block input bandL bandR).roots.value
      (2^p.m*(4^p.m*2^(p.L+p.m))) := by
  intro u v run
  constructor <;> intro i j c
  · rw [GraphResidualFamilies.fromInputs_left_entry]
    exact ResidualWindowSupport.produce_bound _ _ _ _ _
      (ExactHalfSourceBounds.graph_left f p block input bandL bandR u v run)
  · rw [GraphResidualFamilies.fromInputs_right_entry]
    exact ResidualWindowSupport.produce_bound _ _ _ _ _
      (ExactHalfSourceBounds.graph_right f p block input bandL bandR u v run)

theorem fromInputs_bits {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (bandL bandR ell : ℕ) :
    (fromInputs f p block input bandL bandR ell).windows.bitSteps≤
      bitBudget p.L p.m f.cyclic p.t (goodSlots p.L p.m).card (2^p.m*(4^p.m*2^(p.L+p.m))) :=
  execute_bits ell _ _ (root_bound f p block input bandL bandR)

theorem fromInputs_control {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (bandL bandR ell : ℕ) :
    (fromInputs f p block input bandL bandR ell).windows.control≤
      controlBudget p.L p.m f.cyclic p.t (goodSlots p.L p.m).card ell := execute_control ell _

theorem fromInputs_left_entry {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (bandL bandR ell : ℕ)
    (u v : Fin (J p.m)) (run : Fin (2*p.m+1))
    (i j : Fin (goodSlots p.L p.m).card) (c : Fin (channelCount p.m p.t)) :
    ((((((((fromInputs f p block input bandL bandR ell).windows.value.get u).get v).get run).1).get i).get j).get c) =
      (RetainedRootWindows.execute ell ((((((((fromInputs f p block input bandL bandR ell).roots.roots.value.get u).get v).get run).1).get i).get j).get c)).value := by
  simp only [fromInputs,execute_get,family_get]

theorem fromInputs_left_reconstruct {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (bandL bandR ell : ℕ)
    (u v : Fin (J p.m)) (run : Fin (2*p.m+1))
    (i j : Fin (goodSlots p.L p.m).card) (c : Fin (channelCount p.m p.t))
    (w : CroppedGroupedSuffix.Word (2*(p.L-p.m))) (d : Fin (p.m+1)) (residue : Fin f.cyclic) :
    (∑ s, BinaryWindowPartition.sourceValue (((((((((fromInputs f p block input bandL bandR ell).windows.value.get u).get v).get run).1).get i).get j).get c).windows.components.get s)
      w (finProdFinEquiv (d,residue)))=
      BinaryResidualPolynomial.cellView ((ResidualWindowSource.rows ((((((((fromInputs f p block input bandL bandR ell).roots.roots.value.get u).get v).get run).1).get i).get j).get c)).get
        (StoredGroupedCompletion.rawIndex _ w)) d residue := by
  letI : NeZero f.cyclic := ⟨Nat.ne_of_gt f.cyclic_pos⟩
  rw [fromInputs_left_entry]
  change (∑ s, BinaryWindowPartition.sourceValue
    ((RetainedRootWindows.execute ell ((((((((GraphResidualFamilies.fromInputs f p block input bandL bandR).roots.value.get u).get v).get run).1).get i).get j).get c)).value.windows.components.get s)
      w (finProdFinEquiv (d,residue)))=
      BinaryResidualPolynomial.cellView ((ResidualWindowSource.rows ((((((((GraphResidualFamilies.fromInputs f p block input bandL bandR).roots.value.get u).get v).get run).1).get i).get j).get c)).get
        (StoredGroupedCompletion.rawIndex _ w)) d residue
  rw [GraphResidualFamilies.fromInputs_left_entry]
  exact RetainedRootWindows.produce_reconstruct ell _ _ _ _ w d residue

theorem fromInputs_right_entry {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (bandL bandR ell : ℕ)
    (u v : Fin (J p.m)) (run : Fin (2*p.m+1))
    (i j : Fin (goodSlots p.L p.m).card) (c : Fin (channelCount p.m p.t)) :
    ((((((((fromInputs f p block input bandL bandR ell).windows.value.get u).get v).get run).2).get i).get j).get c) =
      (RetainedRootWindows.execute ell ((((((((fromInputs f p block input bandL bandR ell).roots.roots.value.get u).get v).get run).2).get i).get j).get c)).value := by
  simp only [fromInputs,execute_get,family_get]

theorem fromInputs_right_reconstruct {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (bandL bandR ell : ℕ)
    (u v : Fin (J p.m)) (run : Fin (2*p.m+1))
    (i j : Fin (goodSlots p.L p.m).card) (c : Fin (channelCount p.m p.t))
    (w : CroppedGroupedSuffix.Word (2*(p.L-p.m))) (d : Fin (p.m+1)) (residue : Fin f.cyclic) :
    (∑ s, BinaryWindowPartition.sourceValue (((((((((fromInputs f p block input bandL bandR ell).windows.value.get u).get v).get run).2).get i).get j).get c).windows.components.get s)
      w (finProdFinEquiv (d,residue)))=
      BinaryResidualPolynomial.cellView ((ResidualWindowSource.rows ((((((((fromInputs f p block input bandL bandR ell).roots.roots.value.get u).get v).get run).2).get i).get j).get c)).get
        (StoredGroupedCompletion.rawIndex _ w)) d residue := by
  letI : NeZero f.cyclic := ⟨Nat.ne_of_gt f.cyclic_pos⟩
  rw [fromInputs_right_entry]
  change (∑ s, BinaryWindowPartition.sourceValue
    ((RetainedRootWindows.execute ell ((((((((GraphResidualFamilies.fromInputs f p block input bandL bandR).roots.value.get u).get v).get run).2).get i).get j).get c)).value.windows.components.get s)
      w (finProdFinEquiv (d,residue)))=
      BinaryResidualPolynomial.cellView ((ResidualWindowSource.rows ((((((((GraphResidualFamilies.fromInputs f p block input bandL bandR).roots.value.get u).get v).get run).2).get i).get j).get c)).get
        (StoredGroupedCompletion.rawIndex _ w)) d residue
  rw [GraphResidualFamilies.fromInputs_right_entry]
  exact RetainedRootWindows.produce_reconstruct ell _ _ _ _ w d residue

def familyCells {L m C t : ℕ} (xs : Family L m C t) : ℕ :=
  (xs.toList.map (fun row => (row.toList.map (fun group =>
    (group.toList.map (fun e => RetainedRootWindows.coefficientCells e)).sum)).sum)).sum

theorem familyCells_eq {L m C t : ℕ} (xs : Family L m C t) :
    familyCells xs=(goodSlots L m).card^2*channelCount m t*
      ((1+RetainedRootWindows.slots (L-m))*3^(2*(L-m))*((m+1)*C)) := by
  simp only [familyCells,RetainedRootWindows.coefficientCells_eq,List.map_const',Vector.length_toList,List.sum_replicate,smul_eq_mul]
  ring

def coefficientCells {L m C t : ℕ} (xs : Windows L m C t) : ℕ :=
  (xs.toList.map (fun row => (row.toList.map (fun runs =>
    (runs.toList.map (fun both => familyCells both.1+familyCells both.2)).sum)).sum)).sum

theorem coefficientCells_eq {L m C t : ℕ} (xs : Windows L m C t) :
    coefficientCells xs=2*(J m)^2*(2*m+1)*(goodSlots L m).card^2*channelCount m t*
      ((1+RetainedRootWindows.slots (L-m))*3^(2*(L-m))*((m+1)*C)) := by
  simp only [coefficientCells,familyCells_eq,List.map_const',Vector.length_toList,List.sum_replicate,smul_eq_mul]
  ring

#print axioms fromInputs_left_entry
#print axioms fromInputs_right_entry
#print axioms fromInputs_left_reconstruct
#print axioms fromInputs_right_reconstruct
#print axioms familyCells_eq
#print axioms coefficientCells_eq
#print axioms family_get
#print axioms execute_get
#print axioms family_bits
#print axioms family_control
#print axioms execute_bits
#print axioms execute_control
#print axioms root_bound
#print axioms fromInputs_bits
#print axioms fromInputs_control
end ThinMatrix.GraphRootWindows
