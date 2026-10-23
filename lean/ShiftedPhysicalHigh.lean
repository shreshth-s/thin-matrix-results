import GraphHighFamily

set_option autoImplicit false
set_option maxRecDepth 6000
set_option maxHeartbeats 2000000

/-! Reindex the actual shifted HIGH encoder's heterogeneous grid to physical
source words. This bridge uses the literal binary ROM, the actual raw cells,
and the opposite crop, without an assumed encoded source or query value. -/
namespace ThinMatrix.ShiftedPhysicalHigh
open BinaryCell WalshEmbedding CompleteThinProduct SourceCoordinates SharedEncoder
open scoped BigOperators

noncomputable def form {L : ℕ} (side : Bool) (i : Fin (2*L)) (label : Fin 5)
    (w : SourceWord L) : ℤ :=
  if side then halfLift (fun j l (w : SourceWord L) => ShiftedHighForms.normalForm (w.1 j) l)
    (fun j l (w : SourceWord L) => oppositeForm (w.2 j) l) i label w
  else halfLift (fun j l (w : SourceWord L) => oppositeForm (w.2 j) l)
    (fun j l (w : SourceWord L) => ShiftedHighForms.normalForm (w.1 j) l) i label w


theorem oppositeCell_view (row : Fin 5) (col : Fin 3) :
    view (BinaryHighExecution.highCoefficient false row.castSucc col.castSucc)=
      oppositeForm (R:=ℤ) (oppositeEquiv col) row := by
  fin_cases row <;> fin_cases col <;> rfl

theorem forms_at_true_left {L : ℕ} (a : Coordinates (HighBaseEncoder.rootDims L true)) (j : Fin L) (l : Fin 5) :
    ShiftedHighForms.integerForms L true (physicalLeft j).val l.castSucc (a (physicalLeft j)).val =
      form true (physicalLeft j) l (toSourceTrue a) := by
  have hd : HighBaseEncoder.rootDims L true (physicalLeft j)=4 := by
    simp [HighBaseEncoder.rootDims,CacheBounds.rawDim,physicalLeft,j.isLt]
  have ha : (a (physicalLeft j)).val < 4 := hd ▸ (a (physicalLeft j)).isLt
  simp only [physicalLeft] at ha
  simp only [ShiftedHighForms.integerForms,ShiftedHighForms.forms,physicalLeft,ha,↓reduceDIte,Fin.val_castSucc,l.isLt,↓reduceIte,j.isLt,ShiftedHighForms.coefficient,↓reduceIte]
  rw [ShiftedHighForms.normalCell_view]
  simp [form,halfLift,physicalLeft,j.isLt,toSourceTrue]
  congr 2

theorem forms_at_true_right {L : ℕ} (a : Coordinates (HighBaseEncoder.rootDims L true)) (j : Fin L) (l : Fin 5) :
    ShiftedHighForms.integerForms L true (physicalRight j).val l.castSucc (a (physicalRight j)).val =
      form true (physicalRight j) l (toSourceTrue a) := by
  have hd : HighBaseEncoder.rootDims L true (physicalRight j)=3 := by
    simp [HighBaseEncoder.rootDims,CacheBounds.rawDim,physicalRight,Nat.not_lt.mpr (Nat.le_add_right L j.val)]
  have ha : (a (physicalRight j)).val < 3 := hd ▸ (a (physicalRight j)).isLt
  have hb : (a (physicalRight j)).val < 4 := by omega
  simp only [physicalRight] at ha hb
  simp only [ShiftedHighForms.integerForms,ShiftedHighForms.forms,physicalRight,hb,↓reduceDIte,Fin.val_castSucc,l.isLt,↓reduceIte,Nat.not_lt.mpr (Nat.le_add_right L j.val),Bool.not_true,ShiftedHighForms.coefficient,Bool.false_eq_true,↓reduceIte]
  have he := oppositeCell_view l ⟨_,ha⟩
  change view (BinaryHighExecution.highCoefficient false l.castSucc (⟨_,ha⟩ : Fin 3).castSucc)=_
  rw [he]
  simp [form,halfLift,physicalRight,Nat.not_lt.mpr (Nat.le_add_right L j.val),toSourceTrue]
  congr 2

theorem forms_at_false_left {L : ℕ} (a : Coordinates (HighBaseEncoder.rootDims L false)) (j : Fin L) (l : Fin 5) :
    ShiftedHighForms.integerForms L false (physicalLeft j).val l.castSucc (a (physicalLeft j)).val =
      form false (physicalLeft j) l (toSourceFalse a) := by
  have hd : HighBaseEncoder.rootDims L false (physicalLeft j)=3 := by
    simp [HighBaseEncoder.rootDims,CacheBounds.rawDim,physicalLeft,j.isLt]
  have ha : (a (physicalLeft j)).val < 3 := hd ▸ (a (physicalLeft j)).isLt
  have hb : (a (physicalLeft j)).val < 4 := by omega
  simp only [physicalLeft] at ha hb
  simp only [ShiftedHighForms.integerForms,ShiftedHighForms.forms,physicalLeft,hb,↓reduceDIte,Fin.val_castSucc,l.isLt,↓reduceIte,j.isLt,ShiftedHighForms.coefficient,Bool.false_eq_true,↓reduceIte]
  have he := oppositeCell_view l ⟨_,ha⟩
  change view (BinaryHighExecution.highCoefficient false l.castSucc (⟨_,ha⟩ : Fin 3).castSucc)=_
  rw [he]
  simp [form,halfLift,physicalLeft,j.isLt,toSourceFalse]
  congr 2

theorem forms_at_false_right {L : ℕ} (a : Coordinates (HighBaseEncoder.rootDims L false)) (j : Fin L) (l : Fin 5) :
    ShiftedHighForms.integerForms L false (physicalRight j).val l.castSucc (a (physicalRight j)).val =
      form false (physicalRight j) l (toSourceFalse a) := by
  have hd : HighBaseEncoder.rootDims L false (physicalRight j)=4 := by
    simp [HighBaseEncoder.rootDims,CacheBounds.rawDim,physicalRight,Nat.not_lt.mpr (Nat.le_add_right L j.val)]
  have ha : (a (physicalRight j)).val < 4 := hd ▸ (a (physicalRight j)).isLt
  simp only [physicalRight] at ha
  simp only [ShiftedHighForms.integerForms,ShiftedHighForms.forms,physicalRight,ha,↓reduceDIte,Fin.val_castSucc,l.isLt,↓reduceIte,Nat.not_lt.mpr (Nat.le_add_right L j.val),Bool.not_false,ShiftedHighForms.coefficient,↓reduceIte]
  rw [ShiftedHighForms.normalCell_view]
  simp [form,halfLift,physicalRight,Nat.not_lt.mpr (Nat.le_add_right L j.val),toSourceFalse]
  congr 2



theorem forms_at {L : ℕ} (side : Bool) (a : Coordinates (HighBaseEncoder.rootDims L side))
    (i : Fin (2*L)) (l : Fin 5) :
    ShiftedHighForms.integerForms L side i.val l.castSucc (a i).val =
      form side i l (BinaryHighExecution.decodeSource side a) := by
  by_cases hi : i.val < L
  · have he : physicalLeft (⟨i.val,hi⟩ : Fin L)=i := by apply Fin.ext; rfl
    rw [←he]
    cases side
    · exact forms_at_false_left a _ l
    · exact forms_at_true_left a _ l
  · have he : physicalRight (⟨i.val-L,by omega⟩ : Fin L)=i := by
      apply Fin.ext
      simp only [physicalRight]
      omega
    rw [←he]
    cases side
    · exact forms_at_false_right a _ l
    · exact forms_at_true_right a _ l

noncomputable def coefficient {L q : ℕ} (side : Bool) (cap : ℕ)
    (raw : BinarySourceFormation.RawStore L q) (word : HighBoxDP.LeafWord (2*L)) (r : Fin q) : ℤ :=
  ∑ w : SourceWord L,
    CroppedSourceContraction.crop cap (fun n o => view (BinarySourceFormation.readRaw raw n o r)) w.1 w.2 *
      ∏ i, form side i (word i) w

theorem coefficient_eq {L q : ℕ} (side : Bool) (cap : ℕ)
    (raw : BinarySourceFormation.RawStore L q) (word : HighBoxDP.LeafWord (2*L)) (r : Fin q) :
    BinaryCroppedHighEncoder.coefficientValue side cap raw (liftLeaf word) r=coefficient side cap raw word r := by
  unfold BinaryCroppedHighEncoder.coefficientValue coefficient
  simp_rw [liftLeaf,forms_at]
  cases side
  · exact (coordinateEquivFalse L).sum_comp (fun w => CroppedSourceContraction.crop cap (fun n o => view (BinarySourceFormation.readRaw raw n o r)) w.1 w.2 * ∏ i, form false i (word i) w)
  · exact (coordinateEquivTrue L).sum_comp (fun w => CroppedSourceContraction.crop cap (fun n o => view (BinarySourceFormation.readRaw raw n o r)) w.1 w.2 * ∏ i, form true i (word i) w)

noncomputable def leaf {L q : ℕ} [NeZero q] (cap : ℕ)
    (X Y : BinarySourceFormation.RawStore L q) (residue : Fin q) (word : HighBoxDP.LeafWord (2*L)) : ℤ :=
  CyclicRing.convolution (coefficient true cap X word) (coefficient false cap Y word) residue

theorem leaf_eq {L q : ℕ} [NeZero q] (cap : ℕ) (X Y : BinarySourceFormation.RawStore L q)
    (residue : Fin q) : CroppedHighQueries.leaf cap X Y residue=leaf cap X Y residue := by
  funext word
  unfold CroppedHighQueries.leaf BinaryCroppedHighEncoder.leafValues leaf
  apply congrArg₂ (fun a b => CyclicRing.convolution a b residue)
  · funext r; rw [Vector.get_ofFn]; exact coefficient_eq true cap X word r
  · funext r; rw [Vector.get_ofFn]; exact coefficient_eq false cap Y word r

noncomputable def query {L m q : ℕ} [NeZero q] (t cap bandL bandR : ℕ)
    (shape : ThinMatrixBackend.ShapePlan L m) (request : GraphCompletionRequests.Physical L m q)
    (X Y : BinarySourceFormation.RawStore L q) (residue : Fin q) : ℤ :=
  let d := CroppedHighQueries.geometry shape request
  if CroppedHighQueries.accepts bandL bandR request then
    storedHigh (t:=t) rfl d.embedding request.outside.get d.left_cap d.right_cap (leaf cap X Y residue)
  else 0

/-- All actually executed HIGH children equal the physical-word contraction.
Every retained list occurrence, degree run and cyclic residue is retained. -/
theorem fromInputs_value {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (bandL bandR ell : ℕ)
    (request : Fin (FoldedBackendExecution.windowQuerySize n)) (residue : Fin f.cyclic) :
    letI : NeZero f.cyclic := ⟨Nat.ne_of_gt f.cyclic_pos⟩
    let graph := GraphPrefixProgram.fromInputs f p block input bandL bandR ell
    view ((CountedCyclicCollection.output (GraphHighFamily.execute graph input.target bandL bandR).2.value request).get residue)=
      ∑ u, ∑ v, ∑ run, query p.t (p.m/2) bandL bandR graph.permuted.transformed.source.roots.source.shape
        (LowRequestLocator.physical graph input.target request)
        (GraphShiftedRootFactors.raw graph u v run false) (GraphShiftedRootFactors.raw graph u v run true) residue := by
  dsimp only
  rw [GraphHighFamily.fromInputs_value]
  simp only [GraphHighRun.value,CroppedHighQueries.value,leaf_eq,query]

#print axioms fromInputs_value
#print axioms oppositeCell_view
#print axioms forms_at_true_left
#print axioms forms_at_true_right
#print axioms forms_at_false_left
#print axioms forms_at_false_right
#print axioms forms_at
#print axioms coefficient_eq
#print axioms leaf_eq
end ThinMatrix.ShiftedPhysicalHigh
