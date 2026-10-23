import ResidualFamilyKeys

set_option autoImplicit false

/-! Complete LOW root families from retained raw sources and generated keys.
Each good-set pair and admissible joint channel key has one retained entry,
including zero roots. All formal degrees and cyclic coefficients are written.
Binary arithmetic and indexed-control costs remain separate. -/
namespace ThinMatrix.RetainedResidualFamily
open WalshEmbedding GoodMapEmbedding BinaryGroupedCoordinates BinaryGroupedPreparation
open ResidualFamilyKeys BinaryResidualPolynomial
open scoped BigOperators

structure Entry (L m C : ℕ) where
  normalMask : Mask L m
  oppositeMask : Mask L m
  channel : Channel m
  rows : CompleteResidualArray.Rows normalMask.bits oppositeMask.bits C

def normalKey {L m : ℕ} (a : Mask L m) (c : Channel m) : Vector Bool (ResidualLayout.selected a.bits).length :=
  (normal c).cast (selected_size a).symm

def oppositeKey {L m : ℕ} (a : Mask L m) (c : Channel m) : Vector Bool (ResidualLayout.selected a.bits).length :=
  (opposite c).cast (selected_size a).symm

def produce {L m C : ℕ} (raw : BinarySourceFormation.RawStore L C)
    (a b : Mask L m) (c : Channel m) : Run (Entry L m C) :=
  let out := CompleteResidualArray.execute (m/2) raw a.bits b.bits (normalKey a c) (oppositeKey b c)
  ⟨⟨a,b,c,out.value⟩,out.bitSteps,out.control+16*m+16⟩

def entryBitBudget (L m C A : ℕ) : ℕ := CompleteResidualArray.bitBudget L m m (L-m) (L-m) C (m/2) A

def entryControlBudget (L m C : ℕ) : ℕ := CompleteResidualArray.controlBudget L m m (L-m) (L-m) C+16*m+16

theorem produce_bits {L m C : ℕ} (raw : BinarySourceFormation.RawStore L C)
    (a b : Mask L m) (c : Channel m) (A : ℕ) (ha : BinaryResidualLeaf.RawBound raw A) :
    (produce raw a b c).bitSteps≤entryBitBudget L m C A := by
  simpa only [produce,entryBitBudget,selected_size,remaining_size] using
    CompleteResidualArray.execute_bits (m/2) raw a.bits b.bits (normalKey a c) (oppositeKey b c) A ha

theorem produce_control {L m C : ℕ} (raw : BinarySourceFormation.RawStore L C)
    (a b : Mask L m) (c : Channel m) : (produce raw a b c).control≤entryControlBudget L m C := by
  have h := CompleteResidualArray.execute_control (m/2) raw a.bits b.bits (normalKey a c) (oppositeKey b c)
  simpa only [produce,entryControlBudget,selected_size,remaining_size,Nat.add_assoc] using Nat.add_le_add_right h (16*m+16)

theorem produce_polynomial {L m C : ℕ} [NeZero C] (raw : BinarySourceFormation.RawStore L C)
    (a b : Mask L m) (c : Channel m)
    (w : CroppedGroupedSuffix.Word ((ResidualLayout.remaining a.bits).length+(ResidualLayout.remaining b.bits).length)) :
    ResidualPolynomialDegree.decode ((produce raw a b c).value.rows.get (StoredGroupedCompletion.rawIndex _ w)) =
      ResidualPolynomialDegree.polynomial (m/2) raw a.bits b.bits (normalKey a c) (oppositeKey b c)
        (Vector.ofFn (fun i => w (Fin.castAdd _ i))) (Vector.ofFn (fun i => w (Fin.natAdd _ i))) :=
  CompleteResidualArray.execute_polynomial _ _ _ _ _ _ _

theorem produce_root {L m C : ℕ} [NeZero C] (raw : BinarySourceFormation.RawStore L C)
    (a b : Mask L m) (c : Channel m)
    (w : CroppedGroupedSuffix.Word ((ResidualLayout.remaining a.bits).length+(ResidualLayout.remaining b.bits).length)) :
    ResidualPolynomialDegree.decode ((produce raw a b c).value.rows.get (StoredGroupedCompletion.rawIndex _ w)) =
      DistinguishedResidualSupport.root (ResidualLayout.equivalence a.bits)
        (ResidualRootBridge.transport (ResidualLayout.equivalence b.bits)
          ((selected_size b).trans (selected_size a).symm)
          (ResidualRootBridge.remaining_eq a.bits b.bits ((selected_size b).trans (selected_size a).symm)))
        (normalKey a c).get
        (fun i => (oppositeKey b c).get ((finCongr ((selected_size b).trans (selected_size a).symm)).symm i))
        Polynomial.X (m/2) (ResidualRootBridge.rawPolynomial raw)
        (fun i => w (Fin.castAdd _ i))
        (fun i => w (Fin.natAdd _ ((finCongr (ResidualRootBridge.remaining_eq a.bits b.bits
          ((selected_size b).trans (selected_size a).symm))).symm i))) :=
  CompleteResidualArray.execute_root _ _ _ _ _ _ _ _

theorem produce_bound {L m C : ℕ} (raw : BinarySourceFormation.RawStore L C)
    (a b : Mask L m) (c : Channel m) (A : ℕ) (ha : BinaryResidualLeaf.RawBound raw A)
    (i : Fin (3^((ResidualLayout.remaining a.bits).length+(ResidualLayout.remaining b.bits).length))) :
    Bound (2^m*(4^m*A)) ((produce raw a b c).value.rows.get i) := by
  let w := (StoredGroupedCompletion.rawIndex ((ResidualLayout.remaining a.bits).length+(ResidualLayout.remaining b.bits).length)).symm i
  have hi : StoredGroupedCompletion.rawIndex _ w=i := Equiv.apply_symm_apply _ _
  change Bound _ ((CompleteResidualArray.execute _ _ _ _ _ _).value.get i)
  rw [CompleteResidualArray.execute_value,← hi,BinaryResidualArray.execute_get]
  simpa only [selected_size] using BinaryResidualRootProgram.execute_bound (m/2) raw a.bits b.bits
    (normalKey a c) (oppositeKey b c) _ _ A ha

theorem entry_cells {L m C : ℕ} (e : Entry L m C) :
    ((e.rows.toList.map (fun block => (block.toList.map (fun row => row.toArray.size)).sum)).sum)=
      3^(2*(L-m))*(m+1)*C := by
  simp only [Vector.size_toArray,List.map_const',Vector.length_toList,List.sum_replicate,smul_eq_mul,
    selected_size,remaining_size]
  rw [← two_mul (L-m)]
  ring

abbrev Family (L m C t : ℕ) := Vector (Vector (Vector (Entry L m C) (channelCount m t)) (goodSlots L m).card) (goodSlots L m).card

def execute {L m C t : ℕ} (keys : Prepared L m t) (raw : BinarySourceFormation.RawStore L C) : Run (Family L m C t) :=
  tabulate keys.masks (fun i => tabulate keys.masks (fun j => tabulate keys.channels
    (fun h => produce raw (keys.masks.get i) (keys.masks.get j) (keys.channels.get h))))

@[simp] theorem execute_get {L m C t : ℕ} (keys : Prepared L m t) (raw : BinarySourceFormation.RawStore L C)
    (i j : Fin (goodSlots L m).card) (h : Fin (channelCount m t)) :
    (((execute keys raw).value.get i).get j).get h=
      (produce raw (keys.masks.get i) (keys.masks.get j) (keys.channels.get h)).value := by
  simp only [execute,tabulate_get]

def bitBudget (L m C t G A : ℕ) : ℕ := G*(G*(channelCount m t*entryBitBudget L m C A))
def controlBudget (L m C t G : ℕ) : ℕ := G*(G*(channelCount m t*(entryControlBudget L m C+32)+40)+40)+8

theorem execute_bits {L m C t : ℕ} (keys : Prepared L m t) (raw : BinarySourceFormation.RawStore L C)
    (A : ℕ) (ha : BinaryResidualLeaf.RawBound raw A) :
    (execute keys raw).bitSteps≤bitBudget L m C t (goodSlots L m).card A := by
  apply tabulate_bits; intro i
  apply tabulate_bits; intro j
  apply tabulate_bits; intro h
  exact produce_bits raw _ _ _ A ha

theorem execute_control {L m C t : ℕ} (keys : Prepared L m t) (raw : BinarySourceFormation.RawStore L C) :
    (execute keys raw).control≤controlBudget L m C t (goodSlots L m).card := by
  apply tabulate_control; intro i
  apply tabulate_control; intro j
  apply tabulate_control; intro h
  exact produce_control raw _ _ _

theorem entry_count {L m C t : ℕ} (keys : Prepared L m t) (raw : BinarySourceFormation.RawStore L C) :
    (((execute keys raw).value.toList.map (fun row => (row.toList.map (fun groups => groups.toArray.size)).sum)).sum)=
      (goodSlots L m).card^2*channelCount m t := by
  simp only [Vector.size_toArray,List.map_const',Vector.length_toList,List.sum_replicate,smul_eq_mul]
  ring

theorem coefficient_cells {L m C t : ℕ} (keys : Prepared L m t) (raw : BinarySourceFormation.RawStore L C) :
    (((execute keys raw).value.toList.map (fun row => (row.toList.map (fun groups =>
      (groups.toList.map (fun e => (e.rows.toList.map (fun b => (b.toList.map (fun r => r.toArray.size)).sum)).sum)).sum)).sum)).sum)=
      (goodSlots L m).card^2*channelCount m t*(3^(2*(L-m))*(m+1)*C) := by
  simp only [entry_cells,List.map_const',Vector.length_toList,List.sum_replicate,smul_eq_mul]
  ring

#print axioms produce_bits
#print axioms produce_control
#print axioms produce_polynomial
#print axioms produce_root
#print axioms produce_bound
#print axioms entry_cells
#print axioms execute_get
#print axioms execute_bits
#print axioms execute_control
#print axioms entry_count
#print axioms coefficient_cells
end ThinMatrix.RetainedResidualFamily
