import SharedEncoder
import CompleteThinProduct

/-!
# Actual raw-word coordinates for stored source encoders

The two heterogeneous root grids are equivalent to the actual normal/opposite
source-word types. The local forms use the five physical source forms: label
four is the unshifted private H(0) form. Label five is zero and is not used by
the HIGH base-leaf interface. No auxiliary-variable LOW form is introduced.

Both scalar and explicitly materialized integer-vector roots have tensor sums
equal to the actual source transforms, including the swapped right-source
orientation. Vector coefficient identities do not require cyclic inverses.
Execution and formation costs are separate obligations.
-/

namespace ThinMatrix.SourceCoordinates
open scoped BigOperators
open WalshEmbedding CompleteThinProduct SharedEncoder CacheBounds

private def normalCode : NormalLetter → Fin 4
  | .x1 => 0 | .x2 => 1 | .p1 => 2 | .p2 => 3
private def normalLetter (i : Fin 4) : NormalLetter := ![.x1,.x2,.p1,.p2] i
private def oppositeCode : OppositeLetter → Fin 3
  | .s => 0 | .v => 1 | .w => 2
private def oppositeLetter (i : Fin 3) : OppositeLetter := ![.s,.v,.w] i

def normalEquiv : Fin 4 ≃ NormalLetter where
  toFun := normalLetter
  invFun := normalCode
  left_inv i := by fin_cases i <;> rfl
  right_inv n := by cases n <;> rfl

def oppositeEquiv : Fin 3 ≃ OppositeLetter where
  toFun := oppositeLetter
  invFun := oppositeCode
  left_inv i := by fin_cases i <;> rfl
  right_inv n := by cases n <;> rfl

@[simp] lemma rootDims_left (L : ℕ) (b : Bool) (j : Fin L) :
    rootDims L b (physicalLeft j) = if b then 4 else 3 := by
  cases b <;> simp [rootDims, rawDim, physicalLeft, j.isLt]
@[simp] lemma rootDims_right (L : ℕ) (b : Bool) (j : Fin L) :
    rootDims L b (physicalRight j) = if b then 3 else 4 := by
  cases b <;> simp [rootDims, rawDim, physicalRight, Nat.not_lt.mpr (Nat.le_add_right L j.val)]

noncomputable def fromSourceTrue {L : ℕ} (a : SourceWord L) : Coordinates (rootDims L true) := fun i =>
  if hi : i.val < L then
    Fin.cast (by simp [rootDims,rawDim,hi]) (normalEquiv.symm (a.1 ⟨i.val,hi⟩))
  else Fin.cast (by simp [rootDims,rawDim,hi])
    (oppositeEquiv.symm (a.2 ⟨i.val-L,by omega⟩))

noncomputable def toSourceTrue {L : ℕ} (a : Coordinates (rootDims L true)) : SourceWord L :=
  (fun j => normalEquiv (Fin.cast (by simp) (a (physicalLeft j))),
   fun j => oppositeEquiv (Fin.cast (by simp) (a (physicalRight j))))

@[simp] lemma fromSourceTrue_left {L : ℕ} (a : SourceWord L) (j : Fin L) :
    fromSourceTrue a (physicalLeft j) = Fin.cast (by simp) (normalEquiv.symm (a.1 j)) := by
  simp [fromSourceTrue,physicalLeft,j.isLt]
@[simp] lemma fromSourceTrue_right {L : ℕ} (a : SourceWord L) (j : Fin L) :
    fromSourceTrue a (physicalRight j) = Fin.cast (by simp) (oppositeEquiv.symm (a.2 j)) := by
  simp [fromSourceTrue,physicalRight,Nat.not_lt.mpr (Nat.le_add_right L j.val)]

noncomputable def coordinateEquivTrue (L : ℕ) : Coordinates (rootDims L true) ≃ SourceWord L where
  toFun := toSourceTrue
  invFun := fromSourceTrue
  left_inv a := by
    funext i
    by_cases hi : i.val < L
    · have he : physicalLeft (⟨i.val,hi⟩ : Fin L) = i := by apply Fin.ext; rfl
      rw [← he,fromSourceTrue_left]
      simp [toSourceTrue]
    · have he : physicalRight (⟨i.val-L,by omega⟩ : Fin L) = i := by
        apply Fin.ext
        simp [physicalRight]
        omega
      rw [← he,fromSourceTrue_right]
      simp [toSourceTrue]
  right_inv a := by
    apply Prod.ext <;> funext j <;> simp [toSourceTrue]

noncomputable def fromSourceFalse {L : ℕ} (a : SourceWord L) : Coordinates (rootDims L false) := fun i =>
  if hi : i.val < L then
    Fin.cast (by simp [rootDims,rawDim,hi]) (oppositeEquiv.symm (a.2 ⟨i.val,hi⟩))
  else Fin.cast (by simp [rootDims,rawDim,hi])
    (normalEquiv.symm (a.1 ⟨i.val-L,by omega⟩))

noncomputable def toSourceFalse {L : ℕ} (a : Coordinates (rootDims L false)) : SourceWord L :=
  (fun j => normalEquiv (Fin.cast (by simp) (a (physicalRight j))),
   fun j => oppositeEquiv (Fin.cast (by simp) (a (physicalLeft j))))

@[simp] lemma fromSourceFalse_left {L : ℕ} (a : SourceWord L) (j : Fin L) :
    fromSourceFalse a (physicalLeft j) = Fin.cast (by simp) (oppositeEquiv.symm (a.2 j)) := by
  simp [fromSourceFalse,physicalLeft,j.isLt]
@[simp] lemma fromSourceFalse_right {L : ℕ} (a : SourceWord L) (j : Fin L) :
    fromSourceFalse a (physicalRight j) = Fin.cast (by simp) (normalEquiv.symm (a.1 j)) := by
  simp [fromSourceFalse,physicalRight,Nat.not_lt.mpr (Nat.le_add_right L j.val)]

noncomputable def coordinateEquivFalse (L : ℕ) : Coordinates (rootDims L false) ≃ SourceWord L where
  toFun := toSourceFalse
  invFun := fromSourceFalse
  left_inv a := by
    funext i
    by_cases hi : i.val < L
    · have he : physicalLeft (⟨i.val,hi⟩ : Fin L) = i := by apply Fin.ext; rfl
      rw [← he,fromSourceFalse_left]
      simp [toSourceFalse]
    · have he : physicalRight (⟨i.val-L,by omega⟩ : Fin L) = i := by
        apply Fin.ext
        simp [physicalRight]
        omega
      rw [← he,fromSourceFalse_right]
      simp [toSourceFalse]
  right_inv a := by
    apply Prod.ext <;> funext j <;> simp [toSourceFalse]

variable {R : Type*} [CommRing R]

def leftForms (L : ℕ) : LocalForms R := fun d label raw =>
  if d < L then
    if ha : raw < 4 then
      if hl : label.val < 5 then normalForm (normalEquiv ⟨raw,ha⟩) ⟨label.val,hl⟩ else 0
    else 0
  else
    if ha : raw < 3 then
      if hl : label.val < 5 then oppositeForm (oppositeEquiv ⟨raw,ha⟩) ⟨label.val,hl⟩ else 0
    else 0

def rightForms (L : ℕ) : LocalForms R := fun d label raw =>
  if d < L then
    if ha : raw < 3 then
      if hl : label.val < 5 then oppositeForm (oppositeEquiv ⟨raw,ha⟩) ⟨label.val,hl⟩ else 0
    else 0
  else
    if ha : raw < 4 then
      if hl : label.val < 5 then normalForm (normalEquiv ⟨raw,ha⟩) ⟨label.val,hl⟩ else 0
    else 0

def liftLeaf {L : ℕ} (v : HighBoxDP.LeafWord (2*L)) : Word (2*L) := fun i => (v i).castSucc

lemma leftForms_at_left {L : ℕ} (a : Coordinates (rootDims L true)) (j : Fin L) (l : Fin 5) :
    leftForms (R := R) L (physicalLeft j).val l.castSucc (a (physicalLeft j)).val =
      sourceF (physicalLeft j) l (toSourceTrue a) := by
  have ha : (a (physicalLeft j)).val < 4 := by simpa using (a (physicalLeft j)).isLt
  simp only [physicalLeft] at ha
  simp [leftForms, physicalLeft, j.isLt, ha, l.isLt, sourceF, halfLift, toSourceTrue]
  congr 2

lemma leftForms_at_right {L : ℕ} (a : Coordinates (rootDims L true)) (j : Fin L) (l : Fin 5) :
    leftForms (R := R) L (physicalRight j).val l.castSucc (a (physicalRight j)).val =
      sourceF (physicalRight j) l (toSourceTrue a) := by
  have ha : (a (physicalRight j)).val < 3 := by simpa using (a (physicalRight j)).isLt
  simp only [physicalRight] at ha
  simp [leftForms, physicalRight, Nat.not_lt.mpr (Nat.le_add_right L j.val),
    ha, l.isLt, sourceF, halfLift, toSourceTrue]
  congr 2

lemma rightForms_at_left {L : ℕ} (a : Coordinates (rootDims L false)) (j : Fin L) (l : Fin 5) :
    rightForms (R := R) L (physicalLeft j).val l.castSucc (a (physicalLeft j)).val =
      sourceG (physicalLeft j) l (toSourceFalse a) := by
  have ha : (a (physicalLeft j)).val < 3 := by simpa using (a (physicalLeft j)).isLt
  simp only [physicalLeft] at ha
  simp [rightForms, physicalLeft, j.isLt, ha, l.isLt, sourceG, halfLift, toSourceFalse]
  congr 2

lemma rightForms_at_right {L : ℕ} (a : Coordinates (rootDims L false)) (j : Fin L) (l : Fin 5) :
    rightForms (R := R) L (physicalRight j).val l.castSucc (a (physicalRight j)).val =
      sourceG (physicalRight j) l (toSourceFalse a) := by
  have ha : (a (physicalRight j)).val < 4 := by simpa using (a (physicalRight j)).isLt
  simp only [physicalRight] at ha
  simp [rightForms, physicalRight, Nat.not_lt.mpr (Nat.le_add_right L j.val),
    ha, l.isLt, sourceG, halfLift, toSourceFalse]
  congr 2

lemma leftForms_at {L : ℕ} (a : Coordinates (rootDims L true))
    (v : HighBoxDP.LeafWord (2*L)) (i : Fin (2*L)) :
    leftForms (R := R) L i.val (liftLeaf v i) (a i).val = sourceF i (v i) (toSourceTrue a) := by
  by_cases hi : i.val < L
  · have he : physicalLeft (⟨i.val,hi⟩ : Fin L) = i := by apply Fin.ext; rfl
    rw [← he]
    exact leftForms_at_left a _ _
  · have he : physicalRight (⟨i.val-L,by omega⟩ : Fin L) = i := by
      apply Fin.ext
      simp [physicalRight]
      omega
    rw [← he]
    exact leftForms_at_right a _ _

lemma rightForms_at {L : ℕ} (a : Coordinates (rootDims L false))
    (v : HighBoxDP.LeafWord (2*L)) (i : Fin (2*L)) :
    rightForms (R := R) L i.val (liftLeaf v i) (a i).val = sourceG i (v i) (toSourceFalse a) := by
  by_cases hi : i.val < L
  · have he : physicalLeft (⟨i.val,hi⟩ : Fin L) = i := by apply Fin.ext; rfl
    rw [← he]
    exact rightForms_at_left a _ _
  · have he : physicalRight (⟨i.val-L,by omega⟩ : Fin L) = i := by
      apply Fin.ext
      simp [physicalRight]
      omega
    rw [← he]
    exact rightForms_at_right a _ _

noncomputable def leftInput {L : ℕ} (X : SourceWord L → R) : Dense (R := R) (2*L) (rootDims L true) :=
  materialize (2*L) (rootDims L true) (fun a => X (toSourceTrue a))
noncomputable def rightInput {L : ℕ} (Y : SourceWord L → R) : Dense (R := R) (2*L) (rootDims L false) :=
  materialize (2*L) (rootDims L false) (fun a => Y (toSourceFalse a))

lemma left_tensorValue {L : ℕ} (X : SourceWord L → R) (v : HighBoxDP.LeafWord (2*L)) :
    tensorValue L true (leftForms L) (leftInput X) (liftLeaf v) =
      ∑ a : SourceWord L, X a * ∏ i, sourceF i (v i) a := by
  unfold tensorValue EncoderCorrectness.tensorSum leftInput
  simp_rw [read_materialize, leftForms_at]
  exact (coordinateEquivTrue L).sum_comp (fun a => X a * ∏ i, sourceF i (v i) a)

lemma right_tensorValue {L : ℕ} (Y : SourceWord L → R) (v : HighBoxDP.LeafWord (2*L)) :
    tensorValue L false (rightForms L) (rightInput Y) (liftLeaf v) =
      ∑ a : SourceWord L, Y a * ∏ i, sourceG i (v i) a := by
  unfold tensorValue EncoderCorrectness.tensorSum rightInput
  simp_rw [read_materialize, rightForms_at]
  exact (coordinateEquivFalse L).sum_comp (fun a => Y a * ∏ i, sourceG i (v i) a)

lemma normalForm_intCast {S : Type*} [CommRing S] (n : NormalLetter) (l : Fin 5) :
    normalForm (R := S) n l = ((normalForm (R := ℤ) n l : ℤ) : S) := by
  cases n <;> fin_cases l <;> norm_num [normalForm,TensorContraction.alignedLeft,letterIndicator]

lemma oppositeForm_intCast {S : Type*} [CommRing S] (o : OppositeLetter) (l : Fin 5) :
    oppositeForm (R := S) o l = ((oppositeForm (R := ℤ) o l : ℤ) : S) := by
  cases o <;> fin_cases l <;> norm_num [oppositeForm,TensorContraction.alignedRight,letterIndicator]

lemma sourceF_intCast {S : Type*} [CommRing S] {L : ℕ}
    (i : Fin (2*L)) (l : Fin 5) (a : SourceWord L) :
    sourceF (R := S) i l a = ((sourceF (R := ℤ) i l a : ℤ) : S) := by
  unfold sourceF halfLift
  split <;> simp only [normalForm_intCast (S := S),oppositeForm_intCast (S := S)]

lemma sourceG_intCast {S : Type*} [CommRing S] {L : ℕ}
    (i : Fin (2*L)) (l : Fin 5) (a : SourceWord L) :
    sourceG (R := S) i l a = ((sourceG (R := ℤ) i l a : ℤ) : S) := by
  unfold sourceG halfLift
  split <;> simp only [normalForm_intCast (S := S),oppositeForm_intCast (S := S)]

lemma intCast_mul_coeff {q : ℕ} [NeZero q] (c : ℤ) (x : CyclicRing.Cyclic q) (r : Fin q) :
    ((c : CyclicRing.Cyclic q) * x) r = c * x r := by
  rw [← CyclicRing.scale_eq_intCast_mul]
  rfl

lemma left_coefficient_transform {q L : ℕ} [NeZero q]
    (X : SourceWord L → CyclicRing.Cyclic q) (v : HighBoxDP.LeafWord (2*L)) (r : Fin q) :
    (∑ a : SourceWord L, X a * ∏ i, sourceF i (v i) a) r =
      ∑ a : SourceWord L, X a r * ∏ i, sourceF (R := ℤ) i (v i) a := by
  rw [CyclicRing.sum_coeff]
  apply Finset.sum_congr rfl
  intro a _
  simp_rw [sourceF_intCast (S := CyclicRing.Cyclic q)]
  rw [← Int.cast_prod, mul_comm, intCast_mul_coeff, mul_comm]

lemma right_coefficient_transform {q L : ℕ} [NeZero q]
    (Y : SourceWord L → CyclicRing.Cyclic q) (v : HighBoxDP.LeafWord (2*L)) (r : Fin q) :
    (∑ a : SourceWord L, Y a * ∏ i, sourceG i (v i) a) r =
      ∑ a : SourceWord L, Y a r * ∏ i, sourceG (R := ℤ) i (v i) a := by
  rw [CyclicRing.sum_coeff]
  apply Finset.sum_congr rfl
  intro a _
  simp_rw [sourceG_intCast (S := CyclicRing.Cyclic q)]
  rw [← Int.cast_prod, mul_comm, intCast_mul_coeff, mul_comm]

lemma left_tensorValue_coefficient {q L : ℕ} [NeZero q]
    (X : SourceWord L → CyclicRing.Cyclic q) (v : HighBoxDP.LeafWord (2*L)) (r : Fin q) :
    tensorValue L true (leftForms (R := ℤ) L) (leftInput (fun a => X a r)) (liftLeaf v) =
      (∑ a : SourceWord L, X a * ∏ i, sourceF i (v i) a) r := by
  rw [left_tensorValue, left_coefficient_transform]

lemma right_tensorValue_coefficient {q L : ℕ} [NeZero q]
    (Y : SourceWord L → CyclicRing.Cyclic q) (v : HighBoxDP.LeafWord (2*L)) (r : Fin q) :
    tensorValue L false (rightForms (R := ℤ) L) (rightInput (fun a => Y a r)) (liftLeaf v) =
      (∑ a : SourceWord L, Y a * ∏ i, sourceG i (v i) a) r := by
  rw [right_tensorValue, right_coefficient_transform]

/-- Explicit vectors are materialized at every root raw-word address. -/
noncomputable def leftVectorInput {q L : ℕ} (X : SourceWord L → CyclicRing.Cyclic q) :
    Dense (R := Vector ℤ q) (2*L) (rootDims L true) :=
  materialize (2*L) (rootDims L true) (fun a => Vector.ofFn (fun r => X (toSourceTrue a) r))

noncomputable def rightVectorInput {q L : ℕ} (Y : SourceWord L → CyclicRing.Cyclic q) :
    Dense (R := Vector ℤ q) (2*L) (rootDims L false) :=
  materialize (2*L) (rootDims L false) (fun a => Vector.ofFn (fun r => Y (toSourceFalse a) r))

@[simp] lemma leftVectorInput_read {q L : ℕ} (X : SourceWord L → CyclicRing.Cyclic q)
    (a : Coordinates (rootDims L true)) (r : Fin q) :
    (read (2*L) (rootDims L true) (leftVectorInput X) a).get r = X (toSourceTrue a) r := by
  simp [leftVectorInput,read_materialize]

@[simp] lemma rightVectorInput_read {q L : ℕ} (Y : SourceWord L → CyclicRing.Cyclic q)
    (a : Coordinates (rootDims L false)) (r : Fin q) :
    (read (2*L) (rootDims L false) (rightVectorInput Y) a).get r = Y (toSourceFalse a) r := by
  simp [rightVectorInput,read_materialize]

/-- Scalar coefficient denotation of a stored vector root. This uses only
integer local forms, with no multiplication in the cyclic coefficient ring. -/
noncomputable def vectorTensorValue {q : ℕ} (L : ℕ) (b : Bool)
    (forms : LocalForms ℤ) (input : Dense (R := Vector ℤ q) (2*L) (rootDims L b))
    (word : Word (2*L)) (r : Fin q) : ℤ :=
  EncoderCorrectness.tensorSum (rootDims L b)
    (fun i a => forms i.val (word i) a.val)
    (fun a => (read (2*L) (rootDims L b) input a).get r)

lemma left_vectorTensorValue {q L : ℕ} [NeZero q]
    (X : SourceWord L → CyclicRing.Cyclic q) (v : HighBoxDP.LeafWord (2*L)) (r : Fin q) :
    vectorTensorValue L true (leftForms L) (leftVectorInput X) (liftLeaf v) r =
      (∑ a : SourceWord L, X a * ∏ i, sourceF i (v i) a) r := by
  unfold vectorTensorValue EncoderCorrectness.tensorSum
  simp_rw [leftVectorInput_read,leftForms_at]
  rw [left_coefficient_transform]
  exact (coordinateEquivTrue L).sum_comp
    (fun a => X a r * ∏ i, sourceF (R := ℤ) i (v i) a)

lemma right_vectorTensorValue {q L : ℕ} [NeZero q]
    (Y : SourceWord L → CyclicRing.Cyclic q) (v : HighBoxDP.LeafWord (2*L)) (r : Fin q) :
    vectorTensorValue L false (rightForms L) (rightVectorInput Y) (liftLeaf v) r =
      (∑ a : SourceWord L, Y a * ∏ i, sourceG i (v i) a) r := by
  unfold vectorTensorValue EncoderCorrectness.tensorSum
  simp_rw [rightVectorInput_read,rightForms_at]
  rw [right_coefficient_transform]
  exact (coordinateEquivFalse L).sum_comp
    (fun a => Y a r * ∏ i, sourceG (R := ℤ) i (v i) a)

#print axioms coordinateEquivTrue
#print axioms coordinateEquivFalse
#print axioms left_tensorValue
#print axioms right_tensorValue
#print axioms left_tensorValue_coefficient
#print axioms right_tensorValue_coefficient
#print axioms left_vectorTensorValue
#print axioms right_vectorTensorValue
end ThinMatrix.SourceCoordinates
