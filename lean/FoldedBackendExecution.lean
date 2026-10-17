import EndToEndAPSP
import CountedArrayComposite
import ThinMatrixBackend

/-!
# Concrete folded coefficient producer

The sources below are flat vectors of complete cyclic coefficient vectors.
Their formation tests compact-slot bounds arithmetically; no finite-set
membership search occurs in the producer. The physical folded factor three
is included in both the raw middle dimension and the residue locator.

The retained producer prepares one global data structure per middle block,
then stores one integer/counter result per signed incidence. Its work field
adds source coefficient sites, returned preparation work, and the counters
of those same stored query results. It is not a word-RAM running-time theorem.
-/

namespace ThinMatrix.FoldedBackendExecution

open scoped BigOperators
open Fin.CommRing
open StoredMinPlusAPSP
open ThinMatrixBackend

def physicalFold {r : ℕ} (f : CompactBlocks.PhysicalFactorization r) : ℕ := 3 * f.folded

instance {r : ℕ} (f : CompactBlocks.PhysicalFactorization r) : NeZero (physicalFold f) :=
  ⟨Nat.ne_of_gt (Nat.mul_pos (by decide) f.folded_pos)⟩

instance {r : ℕ} (f : CompactBlocks.PhysicalFactorization r) : NeZero f.cyclic :=
  ⟨Nat.ne_of_gt f.cyclic_pos⟩

def outerSize (n d : ℕ) : ℕ := n * FoldedCounts.foldWidth d
def rawMiddle (h d : ℕ) : ℕ := h * d
def middleExponent (h d : ℕ) : ℕ := Nat.clog 4 (rawMiddle h d)
def middleSize (h d : ℕ) : ℕ := PhaseGeometry.pad4 (rawMiddle h d)

theorem rawMiddle_le (h d : ℕ) : rawMiddle h d ≤ middleSize h d :=
  PhaseGeometry.pad4_lower _

theorem middleSize_eq (h d : ℕ) : middleSize h d = 4 ^ middleExponent h d := rfl

structure Shape (h d : ℕ) where
  L : ℕ
  t : ℕ
  hm : middleExponent h d ≤ L
  ht : t ≤ 2 * middleExponent h d

def basicShape (h d : ℕ) : Shape h d := ⟨middleExponent h d, 0, le_rfl, Nat.zero_le _⟩

/-- Direct arithmetic exclusion of the last block's absent original labels. -/
def rawLeft {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (b : Fin (CompactBlocks.blockCount n h)) (A : IntTable n) :
    Matrix (Fin (outerSize n (physicalFold f))) (Fin (rawMiddle h (physicalFold f)))
      (CyclicRing.Cyclic f.cyclic) :=
  fun row middle coeff =>
    let i := (CompactBlocks.outerEquiv n (physicalFold f)).symm row
    let k := (CompactBlocks.middleEquiv h (physicalFold f)).symm middle
    let value := CompactBlocks.localLeft b (fun i k => 3 * decode A i k) i.1 k.1
    if CompactBlocks.index b k.1 < n ∧
      k.2 = (value : ZMod (physicalFold f)) + (i.2.val : ZMod (physicalFold f)) ∧
      coeff = (value : Fin f.cyclic) then 1 else 0

def rawRight {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (b : Fin (CompactBlocks.blockCount n h)) (B : IntTable n) :
    Matrix (Fin (rawMiddle h (physicalFold f))) (Fin (outerSize n (physicalFold f)))
      (CyclicRing.Cyclic f.cyclic) :=
  fun middle column coeff =>
    let k := (CompactBlocks.middleEquiv h (physicalFold f)).symm middle
    let j := (CompactBlocks.outerEquiv n (physicalFold f)).symm column
    let value := CompactBlocks.localRight b (fun k j => 3 * decode B k j) k.1 j.1
    if k.2 = -(value : ZMod (physicalFold f)) -
      (FoldedCounts.foldWidth (physicalFold f) : ZMod (physicalFold f)) *
        (j.2.val : ZMod (physicalFold f)) ∧ coeff = (value : Fin f.cyclic) then 1 else 0

theorem rawLeft_eq {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (b : Fin (CompactBlocks.blockCount n h)) (A : IntTable n) :
    rawLeft f b A = Matrix.reindex (CompactBlocks.outerEquiv n (physicalFold f))
      (CompactBlocks.middleEquiv h (physicalFold f))
      (CompleteAPSP.leftEncoded (physicalFold f) f.cyclic (CompactBlocks.activeSlots n h b)
        (CompactBlocks.localLeft b (fun i k => 3 * decode A i k))) := by
  funext row middle coeff
  simp [rawLeft, Matrix.reindex_apply, CompleteAPSP.leftEncoded, CompactBlocks.activeSlots]

theorem rawRight_eq {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (b : Fin (CompactBlocks.blockCount n h)) (B : IntTable n) :
    rawRight f b B = Matrix.reindex (CompactBlocks.middleEquiv h (physicalFold f))
      (CompactBlocks.outerEquiv n (physicalFold f))
      (CompleteAPSP.rightEncoded (physicalFold f) f.cyclic
        (CompactBlocks.localRight b (fun k j => 3 * decode B k j))) := by
  rfl

def paddedLeft {N R D : ℕ} {S : Type*} [Zero S] (A : Matrix (Fin N) (Fin R) S) :
    Matrix (Fin N) (Fin D) S :=
  fun i k => if hk : k.val < R then A i ⟨k.val, hk⟩ else 0

def paddedRight {N R D : ℕ} {S : Type*} [Zero S] (B : Matrix (Fin R) (Fin N) S) :
    Matrix (Fin D) (Fin N) S :=
  fun k j => if hk : k.val < R then B ⟨k.val, hk⟩ j else 0

theorem padded_product {N R D : ℕ} {S : Type*} [Semiring S] (hRD : R ≤ D)
    (A : Matrix (Fin N) (Fin R) S) (B : Matrix (Fin R) (Fin N) S) :
    paddedLeft (D := D) A * paddedRight (D := D) B = A * B := by
  funext i j
  simp only [Matrix.mul_apply]
  unfold paddedLeft paddedRight
  simp_rw [apply_dite₂ (fun x y : S => x * y)]
  simp only [zero_mul]
  obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le hRD
  exact ThinMatrixBackend.sum_fin_prefix R s (fun k => A i k * B k j)

def serializeLeft {N R D q : ℕ} (A : Matrix (Fin N) (Fin R) (CyclicRing.Cyclic q)) :
    OriginalLeft N D q :=
  Vector.ofFn (fun address => Vector.ofFn (fun coeff =>
    let pair := (finProdFinEquiv : Fin N × Fin D ≃ _).symm address
    if hk : pair.2.val < R then A pair.1 ⟨pair.2.val, hk⟩ coeff else 0))

def serializeRight {N R D q : ℕ} (B : Matrix (Fin R) (Fin N) (CyclicRing.Cyclic q)) :
    OriginalRight N D q :=
  Vector.ofFn (fun address => Vector.ofFn (fun coeff =>
    let pair := (finProdFinEquiv : Fin D × Fin N ≃ _).symm address
    if hk : pair.1.val < R then B ⟨pair.1.val, hk⟩ pair.2 coeff else 0))

theorem serializeLeft_value {N R D q : ℕ} [NeZero q]
    (A : Matrix (Fin N) (Fin R) (CyclicRing.Cyclic q)) :
    originalLeftMatrix (serializeLeft (D := D) A) = paddedLeft A := by
  funext i k coeff
  simp only [originalLeftMatrix, serializeLeft, Vector.get_ofFn, Equiv.symm_apply_apply, paddedLeft]
  split <;> rfl

theorem serializeRight_value {N R D q : ℕ} [NeZero q]
    (B : Matrix (Fin R) (Fin N) (CyclicRing.Cyclic q)) :
    originalRightMatrix (serializeRight (D := D) B) = paddedRight B := by
  funext k j coeff
  simp only [originalRightMatrix, serializeRight, Vector.get_ofFn, Equiv.symm_apply_apply, paddedRight]
  split <;> rfl

def formLeft {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (b : Fin (CompactBlocks.blockCount n h)) (A : IntTable n) :
    OriginalLeft (outerSize n (physicalFold f)) (middleSize h (physicalFold f)) f.cyclic :=
  serializeLeft (rawLeft f b A)

def formRight {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (b : Fin (CompactBlocks.blockCount n h)) (B : IntTable n) :
    OriginalRight (outerSize n (physicalFold f)) (middleSize h (physicalFold f)) f.cyclic :=
  serializeRight (rawRight f b B)

theorem formLeft_zero_one {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (b : Fin (CompactBlocks.blockCount n h)) (A : IntTable n)
    (address : Fin (outerSize n (physicalFold f) * middleSize h (physicalFold f)))
    (coeff : Fin f.cyclic) :
    ((formLeft f b A).get address).get coeff = 0 ∨
      ((formLeft f b A).get address).get coeff = 1 := by
  simp only [formLeft, serializeLeft, Vector.get_ofFn]
  split
  · unfold rawLeft
    dsimp only
    split <;> simp
  · exact Or.inl rfl

theorem formRight_zero_one {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (b : Fin (CompactBlocks.blockCount n h)) (B : IntTable n)
    (address : Fin (middleSize h (physicalFold f) * outerSize n (physicalFold f)))
    (coeff : Fin f.cyclic) :
    ((formRight f b B).get address).get coeff = 0 ∨
      ((formRight f b B).get address).get coeff = 1 := by
  simp only [formRight, serializeRight, Vector.get_ofFn]
  split
  · unfold rawRight
    dsimp only
    split <;> simp
  · exact Or.inl rfl

theorem form_product {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (b : Fin (CompactBlocks.blockCount n h)) (A B : IntTable n) :
    originalLeftMatrix (formLeft f b A) * originalRightMatrix (formRight f b B) =
      Matrix.reindex (CompactBlocks.outerEquiv n (physicalFold f))
        (CompactBlocks.outerEquiv n (physicalFold f))
        (CompleteAPSP.leftEncoded (physicalFold f) f.cyclic (CompactBlocks.activeSlots n h b)
            (CompactBlocks.localLeft b (fun i k => 3 * decode A i k)) *
          CompleteAPSP.rightEncoded (physicalFold f) f.cyclic
            (CompactBlocks.localRight b (fun k j => 3 * decode B k j))) := by
  rw [formLeft, formRight, serializeLeft_value, serializeRight_value,
    padded_product (rawMiddle_le h (physicalFold f)), rawLeft_eq, rawRight_eq]
  exact (CompactBlocks.flattened_product _ _ _ _ _).symm

/-- Complete padded coefficient sites, including zeros and all q entries. -/
def formationSites (n h : ℕ) {r : ℕ} (f : CompactBlocks.PhysicalFactorization r) : ℕ :=
  2 * f.cyclic * outerSize n (physicalFold f) * middleSize h (physicalFold f)

structure PreparedBlock (n h : ℕ) {r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (shape : Shape h (physicalFold f)) where
  left : OriginalLeft (outerSize n (physicalFold f)) (middleSize h (physicalFold f)) f.cyclic
  right : OriginalRight (outerSize n (physicalFold f)) (middleSize h (physicalFold f)) f.cyclic
  prepared : PreparedGlobal (outerSize n (physicalFold f)) (middleSize h (physicalFold f))
    shape.L (middleExponent h (physicalFold f)) shape.t f.cyclic

noncomputable def prepareBlock {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (shape : Shape h (physicalFold f)) (M : FullMultiplier f.cyclic)
    (b : Fin (CompactBlocks.blockCount n h)) (A B : IntTable n) : PreparedBlock n h f shape :=
  let left := formLeft f b A
  let right := formRight f b B
  let prepared := prepareGlobal (L := shape.L) (m := middleExponent h (physicalFold f))
    (t := shape.t) M left right
  ⟨left, right, prepared⟩

def target {n : ℕ} (T : IntTable n) (i j : Fin n) (w : Fin 3) : ℤ :=
  3 * (decode T i j - CompleteAPSP.windowValue w)

noncomputable def queryBlock {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (shape : Shape h (physicalFold f)) (prepared : PreparedBlock n h f shape)
    (T : IntTable n) (i j : Fin n) (w : Fin 3) : ℤ × ℕ :=
  let value := target T i j w
  queryGlobal (tileWidth_pos shape.L (middleExponent h (physicalFold f)) shape.hm)
    prepared.prepared
    (CompactBlocks.outerEquiv n (physicalFold f) (i, FoldedCounts.residueLow (value : ZMod (physicalFold f))))
    (CompactBlocks.outerEquiv n (physicalFold f) (j, FoldedCounts.residueHigh (value : ZMod (physicalFold f))))
    ((-value : ℤ) : Fin f.cyclic)

noncomputable def semanticCoefficient {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (b : Fin (CompactBlocks.blockCount n h)) (A B T : IntTable n) (i j : Fin n) (w : Fin 3) : ℤ :=
  (CompleteAPSP.leftEncoded (physicalFold f) f.cyclic (CompactBlocks.activeSlots n h b)
      (CompactBlocks.localLeft b (fun i k => 3 * decode A i k)) *
    CompleteAPSP.rightEncoded (physicalFold f) f.cyclic
      (CompactBlocks.localRight b (fun k j => 3 * decode B k j)))
    (i, FoldedCounts.residueLow (target T i j w : ZMod (physicalFold f)))
    (j, FoldedCounts.residueHigh (target T i j w : ZMod (physicalFold f)))
    ((-target T i j w : ℤ) : Fin f.cyclic)

theorem queryBlock_value {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (shape : Shape h (physicalFold f)) (M : FullMultiplier f.cyclic)
    (b : Fin (CompactBlocks.blockCount n h)) (A B T : IntTable n) (i j : Fin n) (w : Fin 3) :
    (queryBlock f shape (prepareBlock f shape M b A B) T i j w).1 =
      semanticCoefficient f b A B T i j w := by
  unfold queryBlock prepareBlock
  rw [queryGlobal_correct M shape.hm shape.ht (by rw [middleSize_eq])]
  rw [form_product]
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply]
  rfl

theorem semanticCoefficient_count {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (b : Fin (CompactBlocks.blockCount n h)) (A B T : IntTable n) (i j : Fin n) (w : Fin 3) :
    semanticCoefficient f b A B T i j w =
      (((CompactBlocks.activeSlots n h b).filter (fun s =>
        ((physicalFold f * f.cyclic : ℕ) : ℤ) ∣
          CompactBlocks.localLeft b (fun i k => 3 * decode A i k) i s +
          CompactBlocks.localRight b (fun k j => 3 * decode B k j) s j + target T i j w)).card : ℤ) := by
  unfold semanticCoefficient
  rw [CompleteAPSP.leftEncoded_eq, CompleteAPSP.rightEncoded_eq]
  exact FoldedCounts.canonical_folded_count (d := physicalFold f) (q := f.cyclic)
    f.coprime _ _ _ (fun i j => target T i j w) i j

theorem queryBlock_nonneg {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (shape : Shape h (physicalFold f)) (M : FullMultiplier f.cyclic)
    (b : Fin (CompactBlocks.blockCount n h)) (A B T : IntTable n) (i j : Fin n) (w : Fin 3) :
    0 ≤ (queryBlock f shape (prepareBlock f shape M b A B) T i j w).1 := by
  rw [queryBlock_value, semanticCoefficient_count]
  exact Nat.cast_nonneg _

theorem physicalTable_semantic {n h r : ℕ}
    (backend : CompleteAPSP.ProductBackend (Fin n) (Fin h) (Fin n))
    (f : CompactBlocks.PhysicalFactorization r) (A B T : IntTable n)
    (x : EndToEndAPSP.Incidence n h) :
    CompactBlocks.physicalTable backend f (decode A) (decode B) (decode T) x =
      (semanticCoefficient f x.2.1 A B T x.1.1 x.1.2 x.2.2).toNat := by
  simp only [CompactBlocks.physicalTable, CompactBlocks.preparedProducts, Array.getElem_ofFn]
  rw [backend.correct]
  rfl

theorem queryBlock_count {n h r : ℕ}
    (backend : CompleteAPSP.ProductBackend (Fin n) (Fin h) (Fin n))
    (f : CompactBlocks.PhysicalFactorization r) (shape : Shape h (physicalFold f))
    (M : FullMultiplier f.cyclic) (b : Fin (CompactBlocks.blockCount n h))
    (A B T : IntTable n) (i j : Fin n) (w : Fin 3) :
    (queryBlock f shape (prepareBlock f shape M b A B) T i j w).1.natAbs =
      CompactBlocks.physicalTable backend f (decode A) (decode B) (decode T) ((i,j),b,w) := by
  rw [queryBlock_value, physicalTable_semantic, semanticCoefficient_count]
  simp

structure Retained (n h : ℕ) {r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (shape : Shape h (physicalFold f)) where
  blocks : Vector (PreparedBlock n h f shape) (CompactBlocks.blockCount n h)
  queries : Vector (ℤ × ℕ) (EndToEndAPSP.incidenceSize n h)

def queryFormationSites (n h : ℕ) : ℕ := 100 * EndToEndAPSP.incidenceSize n h

def Retained.work {n h r : ℕ} {f : CompactBlocks.PhysicalFactorization r}
    {shape : Shape h (physicalFold f)} (payload : Retained n h f shape) : ℕ :=
  (payload.blocks.toList.map (fun block => formationSites n h f + block.prepared.operations)).sum +
    (payload.queries.toList.map Prod.snd).sum + queryFormationSites n h

abbrev Payload (n h : ℕ) :=
  Σ r : ℕ, Σ f : CompactBlocks.PhysicalFactorization r,
    Σ shape : Shape h (physicalFold f), Retained n h f shape

def Payload.work {n h : ℕ} (payload : Payload n h) : ℕ := payload.2.2.2.work

noncomputable def prepareRetained {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (shape : Shape h (physicalFold f)) (M : FullMultiplier f.cyclic) (A B T : IntTable n) :
    Retained n h f shape :=
  let blocks := Vector.ofFn (fun b => prepareBlock f shape M b A B)
  let queries := Vector.ofFn (fun index =>
    let x := (EndToEndAPSP.incidenceEquiv n h).symm index
    queryBlock f shape (blocks.get x.2.1) T x.1.1 x.1.2 x.2.2)
  ⟨blocks, queries⟩

noncomputable def produce {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (shape : Shape h (physicalFold f)) (M : FullMultiplier f.cyclic) (A B T : IntTable n) :
    CountedArrayComposite.Table (EndToEndAPSP.incidenceSize n h) (Payload n h) :=
  let payload := prepareRetained f shape M A B T
  ⟨payload.queries.map (fun result => result.1.natAbs), ⟨r,f,shape,payload⟩, payload.work⟩

theorem produce_work {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (shape : Shape h (physicalFold f)) (M : FullMultiplier f.cyclic) (A B T : IntTable n) :
    (produce f shape M A B T).work = Payload.work (produce f shape M A B T).payload := rfl

theorem produce_counts {n h r : ℕ}
    (backend : CompleteAPSP.ProductBackend (Fin n) (Fin h) (Fin n))
    (f : CompactBlocks.PhysicalFactorization r) (shape : Shape h (physicalFold f))
    (M : FullMultiplier f.cyclic) (A B T : IntTable n)
    (index : Fin (EndToEndAPSP.incidenceSize n h)) :
    (produce f shape M A B T).counts.get index =
      CompactBlocks.physicalTable backend f (decode A) (decode B) (decode T)
        ((EndToEndAPSP.incidenceEquiv n h).symm index) := by
  simp only [produce, prepareRetained, Vector.get_map, Vector.get_ofFn]
  exact queryBlock_count backend f shape M _ A B T _ _ _

theorem produce_modCount {n h r : ℕ} (hh : 0 < h)
    (f : CompactBlocks.PhysicalFactorization r) (shape : Shape h (physicalFold f))
    (M : FullMultiplier f.cyclic) (A B T : IntTable n)
    (index : Fin (EndToEndAPSP.incidenceSize n h)) :
    (produce f shape M A B T).counts.get index =
      (EndToEndAPSP.flatInstance (h := h) A B T).modCount r index := by
  rw [produce_counts CompleteAPSP.naiveBackend, CompactBlocks.physicalTable_correct hh]
  simp only [EndToEndAPSP.flatInstance, CompositeCertification.Instance.modCount,
    CompleteAPSP.incidenceInstance, Finset.card_filter]
  rfl

theorem produce_count_bound {n h r : ℕ} (hh : 0 < h)
    (f : CompactBlocks.PhysicalFactorization r) (shape : Shape h (physicalFold f))
    (M : FullMultiplier f.cyclic) (A B T : IntTable n)
    (index : Fin (EndToEndAPSP.incidenceSize n h)) :
    (produce f shape M A B T).counts.get index ≤ h := by
  rw [produce_counts CompleteAPSP.naiveBackend]
  exact CompactBlocks.physicalTable_le_block hh _ _ _ _ _ _

theorem formLeft_abs {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (b : Fin (CompactBlocks.blockCount n h)) (A : IntTable n)
    (address : Fin (outerSize n (physicalFold f) * middleSize h (physicalFold f)))
    (coeff : Fin f.cyclic) : (((formLeft f b A).get address).get coeff).natAbs ≤ 1 := by
  rcases formLeft_zero_one f b A address coeff with hz | ho
  · rw [hz]; norm_num
  · rw [ho]; norm_num

theorem formRight_abs {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (b : Fin (CompactBlocks.blockCount n h)) (B : IntTable n)
    (address : Fin (middleSize h (physicalFold f) * outerSize n (physicalFold f)))
    (coeff : Fin f.cyclic) : (((formRight f b B).get address).get coeff).natAbs ≤ 1 := by
  rcases formRight_zero_one f b B address coeff with hz | ho
  · rw [hz]; norm_num
  · rw [ho]; norm_num

theorem prepareRetained_block {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (shape : Shape h (physicalFold f)) (M : FullMultiplier f.cyclic) (A B T : IntTable n)
    (b : Fin (CompactBlocks.blockCount n h)) :
    (prepareRetained f shape M A B T).blocks.get b = prepareBlock f shape M b A B := by
  simp [prepareRetained]

theorem prepareRetained_query {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (shape : Shape h (physicalFold f)) (M : FullMultiplier f.cyclic) (A B T : IntTable n)
    (index : Fin (EndToEndAPSP.incidenceSize n h)) :
    (prepareRetained f shape M A B T).queries.get index =
      let x := (EndToEndAPSP.incidenceEquiv n h).symm index
      queryBlock f shape ((prepareRetained f shape M A B T).blocks.get x.2.1)
        T x.1.1 x.1.2 x.2.2 := by
  simp [prepareRetained]

theorem prepareRetained_query_nonneg {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (shape : Shape h (physicalFold f)) (M : FullMultiplier f.cyclic) (A B T : IntTable n)
    (index : Fin (EndToEndAPSP.incidenceSize n h)) :
    0 ≤ ((prepareRetained f shape M A B T).queries.get index).1 := by
  rw [prepareRetained_query]
  dsimp only
  rw [prepareRetained_block]
  exact queryBlock_nonneg f shape M _ A B T _ _ _

theorem vector_sum {α : Type*} {n : ℕ} (v : Vector α n) (f : α → ℕ) :
    (v.toList.map f).sum = ∑ i : Fin n, f (v.get i) := by
  have hv : Vector.ofFn v.get = v := by
    apply Vector.ext
    intro i hi
    simp only [Vector.getElem_ofFn]
    rfl
  conv_lhs => rw [← hv]
  simp only [Vector.toList_ofFn, List.map_ofFn, List.sum_ofFn]
  rfl

theorem Retained.work_eq {n h r : ℕ} {f : CompactBlocks.PhysicalFactorization r}
    {shape : Shape h (physicalFold f)} (payload : Retained n h f shape) :
    payload.work =
      Finset.sum Finset.univ (fun b : Fin (CompactBlocks.blockCount n h) =>
        formationSites n h f + (payload.blocks.get b).prepared.operations) +
      Finset.sum Finset.univ (fun i : Fin (EndToEndAPSP.incidenceSize n h) =>
        (payload.queries.get i).2) + queryFormationSites n h := by
  rw [Retained.work, vector_sum, vector_sum]

theorem prepareRetained_query_count {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (shape : Shape h (physicalFold f)) (M : FullMultiplier f.cyclic) (A B T : IntTable n) :
    (prepareRetained f shape M A B T).queries.toArray.size =
      3 * n ^ 2 * CompactBlocks.blockCount n h := by
  rw [Vector.size_toArray]
  unfold EndToEndAPSP.incidenceSize
  ring

theorem prepareRetained_block_count {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (shape : Shape h (physicalFold f)) (M : FullMultiplier f.cyclic) (A B T : IntTable n) :
    (prepareRetained f shape M A B T).blocks.toArray.size = CompactBlocks.blockCount n h :=
  Vector.size_toArray _

theorem physical_middle_dimension {h r : ℕ} (f : CompactBlocks.PhysicalFactorization r) :
    middleSize h (physicalFold f) = PhaseGeometry.pad4 (3 * h * f.folded) := by
  unfold middleSize rawMiddle physicalFold
  congr 1
  ring

noncomputable def produceFFT {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (shape : Shape h (physicalFold f)) (A B T : IntTable n) :
    CountedArrayComposite.Table (EndToEndAPSP.incidenceSize n h) (Payload n h) :=
  produce f shape (fftFullMultiplier f.cyclic) A B T

theorem produceFFT_modCount {n h r : ℕ} (hh : 0 < h)
    (f : CompactBlocks.PhysicalFactorization r) (shape : Shape h (physicalFold f)) (A B T : IntTable n)
    (index : Fin (EndToEndAPSP.incidenceSize n h)) :
    (produceFFT f shape A B T).counts.get index =
      (EndToEndAPSP.flatInstance (h := h) A B T).modCount r index :=
  produce_modCount hh f shape (fftFullMultiplier f.cyclic) A B T index

abbrev WindowQuery (n : ℕ) := (Fin n × Fin n) × Fin 3
def windowQuerySize (n : ℕ) : ℕ := n * n * 3

def windowQueryEquiv (n : ℕ) : WindowQuery n ≃ Fin (windowQuerySize n) :=
  (Equiv.prodCongr finProdFinEquiv (Equiv.refl (Fin 3))).trans finProdFinEquiv

def regroup (n h : ℕ) :
    (Fin (CompactBlocks.blockCount n h) × WindowQuery n) ≃ EndToEndAPSP.Incidence n h :=
  ⟨fun x => (x.2.1, x.1, x.2.2), fun x => (x.2.1, (x.1, x.2.2)),
    by rintro ⟨b,ij,w⟩; rfl, by rintro ⟨ij,b,w⟩; rfl⟩

def groupedIncidenceEquiv (n h : ℕ) :
    (Fin (CompactBlocks.blockCount n h) × Fin (windowQuerySize n)) ≃
      Fin (EndToEndAPSP.incidenceSize n h) :=
  ((Equiv.prodCongr (Equiv.refl _) (windowQueryEquiv n).symm).trans (regroup n h)).trans
    (EndToEndAPSP.incidenceEquiv n h)

theorem groupedIncidenceEquiv_apply (n h : ℕ) (b : Fin (CompactBlocks.blockCount n h))
    (index : Fin (windowQuerySize n)) :
    groupedIncidenceEquiv n h (b,index) =
      EndToEndAPSP.incidenceEquiv n h
        (((windowQueryEquiv n).symm index).1, b, ((windowQueryEquiv n).symm index).2) := rfl

theorem groupedIncidenceEquiv_decode (n h : ℕ) (b : Fin (CompactBlocks.blockCount n h))
    (index : Fin (windowQuerySize n)) :
    (EndToEndAPSP.incidenceEquiv n h).symm (groupedIncidenceEquiv n h (b,index)) =
      (((windowQueryEquiv n).symm index).1, b, ((windowQueryEquiv n).symm index).2) := by
  rw [groupedIncidenceEquiv_apply, Equiv.symm_apply_apply]

/-- The block request vector has exactly three requests per original pair. -/
def requests {n r : ℕ} (f : CompactBlocks.PhysicalFactorization r) (T : IntTable n) :
    Vector (TilingCosts.Request (outerSize n (physicalFold f)) f.cyclic) (windowQuerySize n) :=
  Vector.ofFn (fun index =>
    let x := (windowQueryEquiv n).symm index
    let value := target T x.1.1 x.1.2 x.2
    ⟨CompactBlocks.outerEquiv n (physicalFold f)
        (x.1.1, FoldedCounts.residueLow (value : ZMod (physicalFold f))),
      CompactBlocks.outerEquiv n (physicalFold f)
        (x.1.2, FoldedCounts.residueHigh (value : ZMod (physicalFold f))),
      ((-value : ℤ) : Fin f.cyclic)⟩)

/-- A view of the stored results; this function invokes no backend query. -/
def Retained.blockQueries {n h r : ℕ} {f : CompactBlocks.PhysicalFactorization r}
    {shape : Shape h (physicalFold f)} (payload : Retained n h f shape)
    (b : Fin (CompactBlocks.blockCount n h)) : Vector (ℤ × ℕ) (windowQuerySize n) :=
  Vector.ofFn (fun index => payload.queries.get (groupedIncidenceEquiv n h (b,index)))

theorem prepareRetained_blockQueries {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (shape : Shape h (physicalFold f)) (M : FullMultiplier f.cyclic) (A B T : IntTable n)
    (b : Fin (CompactBlocks.blockCount n h)) (index : Fin (windowQuerySize n)) :
    ((prepareRetained f shape M A B T).blockQueries b).get index =
      queryGlobal (tileWidth_pos shape.L (middleExponent h (physicalFold f)) shape.hm)
        ((prepareRetained f shape M A B T).blocks.get b).prepared
        ((requests f T).get index).row ((requests f T).get index).column
        ((requests f T).get index).coefficient := by
  rw [Retained.blockQueries, Vector.get_ofFn, prepareRetained_query]
  dsimp only
  rw [groupedIncidenceEquiv_decode]
  simp only [requests, Vector.get_ofFn, queryBlock]

theorem Retained.queryCounter_reindex {n h r : ℕ} {f : CompactBlocks.PhysicalFactorization r}
    {shape : Shape h (physicalFold f)} (payload : Retained n h f shape) :
    (∑ index : Fin (EndToEndAPSP.incidenceSize n h), (payload.queries.get index).2) =
      ∑ b : Fin (CompactBlocks.blockCount n h),
        ∑ index : Fin (windowQuerySize n), ((payload.blockQueries b).get index).2 := by
  rw [← (groupedIncidenceEquiv n h).sum_comp (fun index => (payload.queries.get index).2)]
  rw [Fintype.sum_prod_type]
  simp only [Retained.blockQueries, Vector.get_ofFn]

def Retained.blockCounter {n h r : ℕ} {f : CompactBlocks.PhysicalFactorization r}
    {shape : Shape h (physicalFold f)} (payload : Retained n h f shape)
    (b : Fin (CompactBlocks.blockCount n h)) : ℕ :=
  (payload.blocks.get b).prepared.operations +
    ((payload.blockQueries b).toList.map Prod.snd).sum

theorem Retained.work_reindex {n h r : ℕ} {f : CompactBlocks.PhysicalFactorization r}
    {shape : Shape h (physicalFold f)} (payload : Retained n h f shape) :
    payload.work = queryFormationSites n h + CompactBlocks.blockCount n h * formationSites n h f +
      ∑ b : Fin (CompactBlocks.blockCount n h), payload.blockCounter b := by
  rw [Retained.work_eq, Retained.queryCounter_reindex]
  simp only [Retained.blockCounter, vector_sum, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  ring

/-- Literal shared-prepare/selected-query counter, matching the generic
`executeRequests` driver after unfolding its result constructor. -/
theorem prepareRetained_blockCounter {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (shape : Shape h (physicalFold f)) (M : FullMultiplier f.cyclic) (A B T : IntTable n)
    (b : Fin (CompactBlocks.blockCount n h)) :
    (prepareRetained f shape M A B T).blockCounter b =
      (prepareGlobal (L := shape.L) (m := middleExponent h (physicalFold f)) (t := shape.t)
        M (formLeft f b A) (formRight f b B)).operations +
      ∑ index : Fin (windowQuerySize n),
        (queryGlobal (tileWidth_pos shape.L (middleExponent h (physicalFold f)) shape.hm)
          (prepareGlobal (L := shape.L) (m := middleExponent h (physicalFold f)) (t := shape.t)
            M (formLeft f b A) (formRight f b B))
          ((requests f T).get index).row ((requests f T).get index).column
          ((requests f T).get index).coefficient).2 := by
  rw [Retained.blockCounter, vector_sum]
  simp only [prepareRetained_blockQueries, prepareRetained_block, prepareBlock]

theorem requests_size {n r : ℕ} (f : CompactBlocks.PhysicalFactorization r) (T : IntTable n) :
    (requests f T).toArray.size = 3 * n ^ 2 := by
  rw [Vector.size_toArray]
  unfold windowQuerySize
  ring

end ThinMatrix.FoldedBackendExecution

#print axioms ThinMatrix.FoldedBackendExecution.rawLeft_eq
#print axioms ThinMatrix.FoldedBackendExecution.serializeLeft_value
#print axioms ThinMatrix.FoldedBackendExecution.formLeft_zero_one
#print axioms ThinMatrix.FoldedBackendExecution.form_product
#print axioms ThinMatrix.FoldedBackendExecution.queryBlock_value
#print axioms ThinMatrix.FoldedBackendExecution.queryBlock_nonneg
#print axioms ThinMatrix.FoldedBackendExecution.queryBlock_count
#print axioms ThinMatrix.FoldedBackendExecution.produce_work
#print axioms ThinMatrix.FoldedBackendExecution.produce_counts
#print axioms ThinMatrix.FoldedBackendExecution.produce_modCount
#print axioms ThinMatrix.FoldedBackendExecution.produce_count_bound
#print axioms ThinMatrix.FoldedBackendExecution.formLeft_abs
#print axioms ThinMatrix.FoldedBackendExecution.formRight_abs
#print axioms ThinMatrix.FoldedBackendExecution.prepareRetained_block
#print axioms ThinMatrix.FoldedBackendExecution.prepareRetained_query
#print axioms ThinMatrix.FoldedBackendExecution.prepareRetained_query_nonneg
#print axioms ThinMatrix.FoldedBackendExecution.Retained.work_eq
#print axioms ThinMatrix.FoldedBackendExecution.prepareRetained_query_count
#print axioms ThinMatrix.FoldedBackendExecution.prepareRetained_block_count
#print axioms ThinMatrix.FoldedBackendExecution.physical_middle_dimension
#print axioms ThinMatrix.FoldedBackendExecution.produceFFT_modCount
#print axioms ThinMatrix.FoldedBackendExecution.prepareRetained_blockQueries
#print axioms ThinMatrix.FoldedBackendExecution.Retained.queryCounter_reindex
#print axioms ThinMatrix.FoldedBackendExecution.Retained.work_reindex
#print axioms ThinMatrix.FoldedBackendExecution.prepareRetained_blockCounter
#print axioms ThinMatrix.FoldedBackendExecution.requests_size
