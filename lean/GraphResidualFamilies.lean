import ExactHalfSourceBounds

set_option autoImplicit false

/-! Original callback inputs through retained graph sources into all LOW root
families for one physical block and band pair. Keys are prepared once. Each
translation-list incidence, run, good-set pair and strict channel key retains
both complete input roots. Source/setup costs remain separate from root
binary work and indexed control; outer scheduling and LOW completion remain. -/
namespace ThinMatrix.GraphResidualFamilies
open WalshEmbedding GoodMapEmbedding BinaryGroupedCoordinates BinaryGroupedPreparation
open ExactHalfSourcePlan ExactHalfBandSources

abbrev Both (L m C t : ℕ) := RetainedResidualFamily.Family L m C t × RetainedResidualFamily.Family L m C t
abbrev Roots (L m C t : ℕ) := Vector (Vector (Vector (Both L m C t) (2*m+1)) (J m)) (J m)

def pair {L m C t : ℕ} (keys : ResidualFamilyKeys.Prepared L m t) (sources : PairArrays L m C) :
    Run (Vector (Both L m C t) (2*m+1)) :=
  tabulate sources.1 (fun run =>
    let a := RetainedResidualFamily.execute keys (sources.1.get run)
    let b := RetainedResidualFamily.execute keys (sources.2.get run)
    ⟨(a.value,b.value),a.bitSteps+b.bitSteps,a.control+b.control+8⟩)

def execute {L m C t : ℕ} (keys : ResidualFamilyKeys.Prepared L m t) (sources : Families L m C) : Run (Roots L m C t) :=
  tabulate sources (fun u => tabulate (sources.get u) (fun v => pair keys ((sources.get u).get v)))

@[simp] theorem execute_get {L m C t : ℕ} (keys : ResidualFamilyKeys.Prepared L m t) (sources : Families L m C)
    (u v : Fin (J m)) (run : Fin (2*m+1)) :
    (((execute keys sources).value.get u).get v).get run=
      ((RetainedResidualFamily.execute keys ((((sources.get u).get v).1).get run)).value,
       (RetainedResidualFamily.execute keys ((((sources.get u).get v).2).get run)).value) := by
  simp only [execute,pair,tabulate_get]

def bitBudget (L m C t G A : ℕ) : ℕ := J m*(J m*((2*m+1)*(2*RetainedResidualFamily.bitBudget L m C t G A)))
def pairControl (L m C t G : ℕ) : ℕ := (2*m+1)*(2*RetainedResidualFamily.controlBudget L m C t G+40)+8
def controlBudget (L m C t G : ℕ) : ℕ := J m*(J m*(pairControl L m C t G+32)+40)+8

def SourceBound {L m C : ℕ} (sources : Families L m C) (A : ℕ) : Prop :=
  ∀ u v run, BinaryResidualLeaf.RawBound ((((sources.get u).get v).1).get run) A ∧
    BinaryResidualLeaf.RawBound ((((sources.get u).get v).2).get run) A

theorem execute_bits {L m C t : ℕ} (keys : ResidualFamilyKeys.Prepared L m t) (sources : Families L m C)
    (A : ℕ) (ha : SourceBound sources A) :
    (execute keys sources).bitSteps≤bitBudget L m C t (goodSlots L m).card A := by
  apply tabulate_bits; intro u
  apply tabulate_bits; intro v
  apply tabulate_bits; intro run
  have hl := RetainedResidualFamily.execute_bits keys ((((sources.get u).get v).1).get run) A (ha u v run).1
  have hr := RetainedResidualFamily.execute_bits keys ((((sources.get u).get v).2).get run) A (ha u v run).2
  dsimp only
  omega

theorem execute_control {L m C t : ℕ} (keys : ResidualFamilyKeys.Prepared L m t) (sources : Families L m C) :
    (execute keys sources).control≤controlBudget L m C t (goodSlots L m).card := by
  apply tabulate_control; intro u
  apply tabulate_control; intro v
  apply tabulate_control; intro run
  have hl := RetainedResidualFamily.execute_control keys ((((sources.get u).get v).1).get run)
  have hr := RetainedResidualFamily.execute_control keys ((((sources.get u).get v).2).get run)
  dsimp only
  omega

structure Prepared {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : ℕ) where
  source : ExactHalfGraphSources.Prepared f p block
  keys : Run (ResidualFamilyKeys.Prepared p.L p.m p.t)
  roots : Run (Roots p.L p.m f.cyclic p.t)

def fromInputs {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (bandL bandR : ℕ) : Prepared f p block :=
  let source := ExactHalfGraphSources.execute f p block input bandL bandR
  let keys := ResidualFamilyKeys.prepare source.shape.layout p.t
  let roots := execute keys.value source.sources.value
  ⟨source,keys,roots⟩

theorem source_bound {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (bandL bandR : ℕ) :
    SourceBound (fromInputs f p block input bandL bandR).source.sources.value (2^(p.L+p.m)) := by
  intro u v run
  exact ⟨ExactHalfSourceBounds.graph_left f p block input bandL bandR u v run,
    ExactHalfSourceBounds.graph_right f p block input bandL bandR u v run⟩

theorem fromInputs_bits {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (bandL bandR : ℕ) :
    (fromInputs f p block input bandL bandR).keys.bitSteps+
      (fromInputs f p block input bandL bandR).roots.bitSteps≤
      bitBudget p.L p.m f.cyclic p.t (goodSlots p.L p.m).card (2^(p.L+p.m)) := by
  have hs := source_bound f p block input bandL bandR
  simpa only [fromInputs,ResidualFamilyKeys.prepare_bits,Nat.zero_add] using execute_bits _ _ _ hs

theorem fromInputs_control {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (bandL bandR : ℕ) :
    (fromInputs f p block input bandL bandR).keys.control+
      (fromInputs f p block input bandL bandR).roots.control≤
      ResidualFamilyKeys.prepareBudget p.L p.m p.t (goodSlots p.L p.m).card+
      controlBudget p.L p.m f.cyclic p.t (goodSlots p.L p.m).card := by
  exact Nat.add_le_add (ResidualFamilyKeys.prepare_control _ _) (execute_control _ _)

theorem fromInputs_left_entry {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (bandL bandR : ℕ)
    (u v : Fin (J p.m)) (run : Fin (2*p.m+1))
    (i j : Fin (goodSlots p.L p.m).card) (c : Fin (ResidualFamilyKeys.channelCount p.m p.t)) :
    (((((((fromInputs f p block input bandL bandR).roots.value.get u).get v).get run).1).get i).get j).get c=
      (RetainedResidualFamily.produce
        (((((fromInputs f p block input bandL bandR).source.sources.value.get u).get v).1).get run)
        ((fromInputs f p block input bandL bandR).keys.value.masks.get i)
        ((fromInputs f p block input bandL bandR).keys.value.masks.get j)
        ((fromInputs f p block input bandL bandR).keys.value.channels.get c)).value := by
  simp only [fromInputs,execute_get,RetainedResidualFamily.execute_get]

theorem fromInputs_right_entry {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (bandL bandR : ℕ)
    (u v : Fin (J p.m)) (run : Fin (2*p.m+1))
    (i j : Fin (goodSlots p.L p.m).card) (c : Fin (ResidualFamilyKeys.channelCount p.m p.t)) :
    (((((((fromInputs f p block input bandL bandR).roots.value.get u).get v).get run).2).get i).get j).get c=
      (RetainedResidualFamily.produce
        (((((fromInputs f p block input bandL bandR).source.sources.value.get u).get v).2).get run)
        ((fromInputs f p block input bandL bandR).keys.value.masks.get i)
        ((fromInputs f p block input bandL bandR).keys.value.masks.get j)
        ((fromInputs f p block input bandL bandR).keys.value.channels.get c)).value := by
  simp only [fromInputs,execute_get,RetainedResidualFamily.execute_get]

def familyEntries {L m C t : ℕ} (xs : RetainedResidualFamily.Family L m C t) : ℕ :=
  (xs.toList.map (fun row => (row.toList.map (fun groups => groups.toArray.size)).sum)).sum

theorem familyEntries_eq {L m C t : ℕ} (xs : RetainedResidualFamily.Family L m C t) :
    familyEntries xs=(goodSlots L m).card^2*ResidualFamilyKeys.channelCount m t := by
  simp only [familyEntries,Vector.size_toArray,List.map_const',Vector.length_toList,List.sum_replicate,smul_eq_mul]
  ring

def rootEntries {L m C t : ℕ} (xs : Roots L m C t) : ℕ :=
  (xs.toList.map (fun row => (row.toList.map (fun runs =>
    (runs.toList.map (fun both => familyEntries both.1+familyEntries both.2)).sum)).sum)).sum

theorem rootEntries_eq {L m C t : ℕ} (xs : Roots L m C t) :
    rootEntries xs=2*(J m)^2*(2*m+1)*(goodSlots L m).card^2*ResidualFamilyKeys.channelCount m t := by
  simp only [rootEntries,familyEntries_eq,List.map_const',Vector.length_toList,List.sum_replicate,smul_eq_mul]
  ring

theorem fromInputs_entries {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (bandL bandR : ℕ) :
    rootEntries (fromInputs f p block input bandL bandR).roots.value=
      2*(if p.m=0 then 1 else 4096*p.m^6)*(2*p.m+1)*
        (goodSlots p.L p.m).card^2*ResidualFamilyKeys.channelCount p.m p.t := by
  rw [rootEntries_eq]
  have hp := ExactHalfCroppedEmbedding.pair_count p.m
  have he : (J p.m)^2=(if p.m=0 then 1 else 4096*p.m^6) := by
    simpa only [Fintype.card_prod,Fintype.card_fin,pow_two,J] using hp
  rw [he]

def familyCells {L m C t : ℕ} (xs : RetainedResidualFamily.Family L m C t) : ℕ :=
  (xs.toList.map (fun row => (row.toList.map (fun groups => (groups.toList.map (fun e =>
    (e.rows.toList.map (fun block => (block.toList.map (fun coeff => coeff.toArray.size)).sum)).sum)).sum)).sum)).sum

theorem familyCells_eq {L m C t : ℕ} (xs : RetainedResidualFamily.Family L m C t) :
    familyCells xs=(goodSlots L m).card^2*ResidualFamilyKeys.channelCount m t*(3^(2*(L-m))*(m+1)*C) := by
  simp only [familyCells,RetainedResidualFamily.entry_cells,List.map_const',Vector.length_toList,List.sum_replicate,smul_eq_mul]
  ring

def rootCells {L m C t : ℕ} (xs : Roots L m C t) : ℕ :=
  (xs.toList.map (fun row => (row.toList.map (fun runs =>
    (runs.toList.map (fun both => familyCells both.1+familyCells both.2)).sum)).sum)).sum

theorem rootCells_eq {L m C t : ℕ} (xs : Roots L m C t) :
    rootCells xs=2*(J m)^2*(2*m+1)*(goodSlots L m).card^2*ResidualFamilyKeys.channelCount m t*
      (3^(2*(L-m))*(m+1)*C) := by
  simp only [rootCells,familyCells_eq,List.map_const',Vector.length_toList,List.sum_replicate,smul_eq_mul]
  ring

#print axioms familyCells_eq
#print axioms rootCells_eq
#print axioms familyEntries_eq
#print axioms rootEntries_eq
#print axioms fromInputs_entries
#print axioms execute_get
#print axioms execute_bits
#print axioms execute_control
#print axioms source_bound
#print axioms fromInputs_bits
#print axioms fromInputs_control
#print axioms fromInputs_left_entry
#print axioms fromInputs_right_entry
end ThinMatrix.GraphResidualFamilies
