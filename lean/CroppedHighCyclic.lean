import PhysicalLowHighGeometry

set_option autoImplicit false
set_option maxRecDepth 6000
set_option maxHeartbeats 2000000

/-! Lift actual stored HIGH coefficients to a cyclic-ring contraction before
joining LOW. Coefficient extraction commutes with the full stored box sums. -/
namespace ThinMatrix.CroppedHighCyclic
open BinaryCell CompleteThinProduct PhysicalShiftedForms
open scoped BigOperators

noncomputable def source {L q : ℕ} [NeZero q] (cap : ℕ)
    (raw : BinarySourceFormation.RawStore L q) (w : SourceWord L) : CyclicRing.Cyclic q :=
  CroppedSourceContraction.crop cap (fun n o r => view (BinarySourceFormation.readRaw raw n o r)) w.1 w.2

theorem transform_coefficient {L q : ℕ} [NeZero q] (side : Bool) (cap : ℕ)
    (raw : BinarySourceFormation.RawStore L q) (word : HighBoxDP.LeafWord (2*L)) (r : Fin q) :
    (∑ w, source cap raw w*∏ i, lift (R:=CyclicRing.Cyclic q) side i (word i) w) r=
      ShiftedPhysicalHigh.coefficient side cap raw word r := by
  rw [CyclicRing.sum_coeff]
  unfold ShiftedPhysicalHigh.coefficient
  apply Finset.sum_congr rfl
  intro w _
  simp only [lift]
  rw [←Int.cast_prod,mul_comm,SourceCoordinates.intCast_mul_coeff,mul_comm]
  unfold source CroppedSourceContraction.crop
  split <;> rfl

theorem global_coefficient {L q : ℕ} [NeZero q] (cap : ℕ)
    (X Y : BinarySourceFormation.RawStore L q) (word : HighBoxDP.LeafWord (2*L)) (r : Fin q) :
    globalLeaf (source cap X) (source cap Y) (lift true) (lift false) word r=
      ShiftedPhysicalHigh.leaf cap X Y r word := by
  unfold globalLeaf ShiftedPhysicalHigh.leaf
  rw [CyclicRing.mul_eq_convolution]
  unfold CyclicRing.convolution
  simp_rw [transform_coefficient]

theorem stored_coefficient {L m t k q : ℕ} [NeZero q] (hk : k=2*m)
    (e : Fin k ↪o Fin (2*L)) (outside : Fin (2*L) → Fin 4)
    (hleft : ((HighBoxDP.embeddedSupport e).filter (fun i => i.val<L)).card ≤ m)
    (hright : ((HighBoxDP.embeddedSupport e).filter (fun i => L ≤ i.val)).card ≤ m)
    (leaf : HighBoxDP.LeafWord (2*L) → CyclicRing.Cyclic q) (r : Fin q) :
    storedHigh (t:=t) hk e outside hleft hright leaf r=
      storedHigh (t:=t) hk e outside hleft hright (fun w => leaf w r) := by
  simp only [storedHigh,ThinMatrixBackend.cyclic_list_sum_coeff,List.map_map,Function.comp_def]
  apply congrArg List.sum
  apply List.map_congr_left
  intro ms _
  unfold storedBox
  split <;> simp only [CyclicRing.sum_coeff,ThinMatrixBackend.tableAfter_coefficient]

theorem query_coefficient {L m q : ℕ} [NeZero q] (t cap bandL bandR : ℕ)
    (shape : ThinMatrixBackend.ShapePlan L m) (request : GraphCompletionRequests.Physical L m q)
    (X Y : BinarySourceFormation.RawStore L q) (r : Fin q) :
    ShiftedPhysicalHigh.query t cap bandL bandR shape request X Y r=
      if CroppedHighQueries.accepts bandL bandR request then
        storedHigh (t:=t) rfl (CroppedHighQueries.geometry shape request).embedding request.outside.get
          (CroppedHighQueries.geometry shape request).left_cap (CroppedHighQueries.geometry shape request).right_cap
          (globalLeaf (source cap X) (source cap Y) (lift true) (lift false)) r
      else 0 := by
  unfold ShiftedPhysicalHigh.query
  split
  · rw [stored_coefficient]
    dsimp only
    simp_rw [global_coefficient]
  · rfl

#print axioms transform_coefficient
#print axioms global_coefficient
#print axioms stored_coefficient
#print axioms query_coefficient
end ThinMatrix.CroppedHighCyclic
