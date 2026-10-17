import CompleteThinProduct
import TilingCosts
import SourceCoordinates
import ApproximateConvolution
import ArrayFFT
import SourceFormation
import RowIndexing
import HighBaseEncoder
import CachedLowQuery
import CacheDenseLowering
import IntegerArithmetic
import ArrayKeys
import HighQueryKeys
import GoodMapRuntime

/-!
# Compact matrix tiles and their stored aligned backend

Rows and columns are the actual compact good-set/outside/outer indices;
the middle type has exactly `4^m` labels. The raw A3--A4 adapters read
these original matrix entries, rather than postulating a source output.
The finite stored encoders and high tables are assembled below.
Asymptotic execution and bit costs are separate theorems.
-/

namespace ThinMatrix.ThinMatrixBackend
open scoped BigOperators
open WalshEmbedding GoodMapEmbedding CompleteThinProduct

abbrev GoodSlots (L m : ℕ) := {Q : Finset (Fin L) // Q ∈ goodSlots L m}
abbrev OuterIndex (L m : ℕ) := GoodSlots L m × (Cube (L-m) × Cube (L-m))
abbrev InnerIndex (m : ℕ) := Cube m × Cube m

lemma outsideCard {L m : ℕ} (Q : Finset (Fin L)) (hQ : Q.card = m) :
    Qᶜ.card = L-m := by
  rw [Finset.card_compl]
  simp [hQ]

noncomputable def outsideEmbedding {L m : ℕ} (Q : Finset (Fin L)) (hQ : Q.card = m) :
    Fin (L-m) ↪o Fin L := Qᶜ.orderEmbOfFin (outsideCard Q hQ)

noncomputable def compressOutside {L m : ℕ} (Q : Finset (Fin L)) (hQ : Q.card = m)
    (bits : Cube L) : Cube (L-m) := fun j => bits (outsideEmbedding Q hQ j)

noncomputable def expandOutside {L m : ℕ} (Q : Finset (Fin L)) (hQ : Q.card = m)
    (bits : Cube (L-m)) : Cube L := fun i =>
  if hi : i ∈ Qᶜ then bits ((Qᶜ.orderIsoOfFin (outsideCard Q hQ)).symm ⟨i, hi⟩) else false

@[simp] theorem expandOutside_at {L m : ℕ} (Q : Finset (Fin L)) (hQ : Q.card = m)
    (bits : Cube (L-m)) (j : Fin (L-m)) :
    expandOutside Q hQ bits (outsideEmbedding Q hQ j) = bits j := by
  have hi := Finset.orderEmbOfFin_mem Qᶜ (outsideCard Q hQ) j
  unfold expandOutside outsideEmbedding
  rw [dif_pos hi]
  change bits ((Qᶜ.orderIsoOfFin (outsideCard Q hQ)).symm
    ((Qᶜ.orderIsoOfFin (outsideCard Q hQ)) j)) = bits j
  simp

@[simp] theorem expandOutside_on {L m : ℕ} (Q : Finset (Fin L)) (hQ : Q.card = m)
    (bits : Cube (L-m)) (i : Fin L) (hi : i ∈ Q) : expandOutside Q hQ bits i = false := by
  simp [expandOutside, hi]

@[simp] theorem compress_expand {L m : ℕ} (Q : Finset (Fin L)) (hQ : Q.card = m)
    (bits : Cube (L-m)) : compressOutside Q hQ (expandOutside Q hQ bits) = bits := by
  funext j
  exact expandOutside_at Q hQ bits j

@[simp] theorem compress_outsideBits {L m : ℕ} (Q : Finset (Fin L)) (hQ : Q.card = m)
    (bits : Cube L) : compressOutside Q hQ (outsideBits Q bits) = compressOutside Q hQ bits := by
  funext j
  have hi := Finset.orderEmbOfFin_mem Qᶜ (outsideCard Q hQ) j
  simp only [Finset.mem_compl] at hi
  simp [compressOutside, outsideEmbedding, outsideBits, hi]

@[simp] theorem compress_outside_expand {L m : ℕ} (Q : Finset (Fin L)) (hQ : Q.card = m)
    (bits : Cube (L-m)) :
    compressOutside Q hQ (outsideBits Q (expandOutside Q hQ bits)) = bits := by
  rw [compress_outsideBits, compress_expand]

lemma outerIndex_card (L m : ℕ) : Fintype.card (OuterIndex L m) =
    (goodSlots L m).card * 4^(L-m) := by
  simp only [OuterIndex, GoodSlots, Fintype.card_prod, Fintype.card_coe, Cube,
    Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  rw [← mul_pow]
  norm_num

variable {R : Type*} [CommRing R]

noncomputable def rawLeft {L m : ℕ} (A : Matrix (OuterIndex L m) (InnerIndex m) R) :
    RawLeftInput L m (L-m) R := fun Q bits outer h1 h2 =>
  if hQ : Q ∈ goodSlots L m then
    A (⟨Q,hQ⟩, (compressOutside Q (goodSlots_size L m Q hQ) bits, outer)) (h1,h2)
  else 0

noncomputable def rawRight {L m : ℕ} (B : Matrix (InnerIndex m) (OuterIndex L m) R) :
    RawRightInput L m (L-m) R := fun Q bits h1 h2 outer =>
  if hQ : Q ∈ goodSlots L m then
    B (h1,h2) (⟨Q,hQ⟩, (compressOutside Q (goodSlots_size L m Q hQ) bits, outer))
  else 0

@[simp] theorem rawLeft_at {L m : ℕ} (A : Matrix (OuterIndex L m) (InnerIndex m) R)
    (Q : GoodSlots L m) (bits outer : Cube (L-m)) (h1 h2 : Cube m) :
    rawLeft A Q.val (outsideBits Q.val (expandOutside Q.val
      (goodSlots_size L m Q.val Q.property) bits)) outer h1 h2 =
      A (Q,(bits,outer)) (h1,h2) := by
  simp [rawLeft]

@[simp] theorem rawRight_at {L m : ℕ} (B : Matrix (InnerIndex m) (OuterIndex L m) R)
    (Q : GoodSlots L m) (bits outer : Cube (L-m)) (h1 h2 : Cube m) :
    rawRight B Q.val (outsideBits Q.val (expandOutside Q.val
      (goodSlots_size L m Q.val Q.property) bits)) h1 h2 outer =
      B (h1,h2) (Q,(bits,outer)) := by
  simp [rawRight]

noncomputable def compactQuery {L m : ℕ}
    (A : Matrix (OuterIndex L m) (InnerIndex m) R)
    (B : Matrix (InnerIndex m) (OuterIndex L m) R)
    (row col : OuterIndex L m) : SourceQueryData L m (L-m) R :=
  constructedSourceQuery L m (rawLeft A) (rawRight B) row.1.val col.1.val
    row.1.property col.1.property
    (expandOutside row.1.val (goodSlots_size L m row.1.val row.1.property) row.2.1)
    (expandOutside col.1.val (goodSlots_size L m col.1.val col.1.property) col.2.1)
    row.2.2 col.2.2

lemma compactQuery_matrixProductEntry {L m : ℕ}
    (A : Matrix (OuterIndex L m) (InnerIndex m) R)
    (B : Matrix (InnerIndex m) (OuterIndex L m) R)
    (row col : OuterIndex L m) :
    (compactQuery A B row col).matrixProductEntry row.2.2 col.2.2 = (A * B) row col := by
  unfold compactQuery SourceQueryData.matrixProductEntry constructedSourceQuery
  simp only [rawLeft_at, rawRight_at, Matrix.mul_apply, InnerIndex, Fintype.sum_prod_type]

lemma compactQuery_numerator {L m : ℕ} (t : ℕ) (hm : m ≤ L) (ht : t ≤ 2*m)
    (A : Matrix (OuterIndex L m) (InnerIndex m) R)
    (B : Matrix (InnerIndex m) (OuterIndex L m) R)
    (row col : OuterIndex L m) :
    (compactQuery A B row col).numerator t = (4 : R)^L * (A * B) row col := by
  simpa only [compactQuery, rawLeft_at, rawRight_at, Matrix.mul_apply,
    InnerIndex, Fintype.sum_prod_type] using
    constructed_complete_numerator L m t hm ht (rawLeft A) (rawRight B)
      row.1.val col.1.val row.1.property col.1.property
      (expandOutside row.1.val (goodSlots_size L m row.1.val row.1.property) row.2.1)
      (expandOutside col.1.val (goodSlots_size L m col.1.val col.1.property) col.2.1)
      row.2.2 col.2.2

lemma compactQuery_decode {q : ℕ} [NeZero q] {L m : ℕ}
    (t : ℕ) (hm : m ≤ L) (ht : t ≤ 2*m)
    (A : Matrix (OuterIndex L m) (InnerIndex m) (CyclicRing.Cyclic q))
    (B : Matrix (InnerIndex m) (OuterIndex L m) (CyclicRing.Cyclic q))
    (row col : OuterIndex L m) :
    CyclicRing.decode L ((compactQuery A B row col).residual t +
      (compactQuery A B row col).high t) = (A * B) row col := by
  simpa only [compactQuery, rawLeft_at, rawRight_at, Matrix.mul_apply,
    InnerIndex, Fintype.sum_prod_type] using
    constructed_cyclic_decode L m t hm ht (rawLeft A) (rawRight B)
      row.1.val col.1.val row.1.property col.1.property
      (expandOutside row.1.val (goodSlots_size L m row.1.val row.1.property) row.2.1)
      (expandOutside col.1.val (goodSlots_size L m col.1.val col.1.property) col.2.1)
      row.2.2 col.2.2

#print axioms compress_outside_expand
#print axioms outerIndex_card
#print axioms compactQuery_matrixProductEntry
#print axioms compactQuery_numerator
#print axioms compactQuery_decode

/-- Full-grid tile width, determined by source geometry rather than by
how many encoder entries happen to be retained. -/
def tileWidth (L m : ℕ) : ℕ := (goodSlots L m).card * 4^(L-m)

def rowEquiv (L m : ℕ) : OuterIndex L m ≃ Fin (tileWidth L m) :=
  ThinMatrix.RowIndexing.rowEquiv L m

lemma innerIndex_card (m : ℕ) : Fintype.card (InnerIndex m) = 4^m := by
  simp only [InnerIndex, Fintype.card_prod, Cube, Fintype.card_fun,
    Fintype.card_fin, Fintype.card_bool]
  rw [← mul_pow]
  norm_num

lemma tileWidth_pos (L m : ℕ) (hm : m ≤ L) : 0 < tileWidth L m := by
  have hd := goodSlots_density L m
  have hp := Nat.choose_pos hm
  have hg : 0 < (goodSlots L m).card := by nlinarith
  exact Nat.mul_pos hg (by positivity)

/-- Ordinary zero padding into physical row bands. Each compact row slot
is identified once by the full-grid row equivalence. -/
noncomputable def rowBand {N L m : ℕ}
    (A : Matrix (Fin N) (InnerIndex m) R)
    (b : Fin (ThinMatrix.TilingCosts.bandCount N (tileWidth L m))) :
    Matrix (OuterIndex L m) (InnerIndex m) R := fun row h =>
  let v := b.val * tileWidth L m + (rowEquiv L m row).val
  if hv : v < N then A ⟨v,hv⟩ h else 0

noncomputable def columnBand {N L m : ℕ}
    (B : Matrix (InnerIndex m) (Fin N) R)
    (b : Fin (ThinMatrix.TilingCosts.bandCount N (tileWidth L m))) :
    Matrix (InnerIndex m) (OuterIndex L m) R := fun h col =>
  let v := b.val * tileWidth L m + (rowEquiv L m col).val
  if hv : v < N then B h ⟨v,hv⟩ else 0

noncomputable def localRow {N L m : ℕ} (hB : 0 < tileWidth L m) (i : Fin N) : OuterIndex L m :=
  (rowEquiv L m).symm (ThinMatrix.TilingCosts.locate hB i).2

lemma rowBand_original {N L m : ℕ} (hB : 0 < tileWidth L m)
    (A : Matrix (Fin N) (InnerIndex m) R) (i : Fin N) (h : InnerIndex m) :
    rowBand A (ThinMatrix.TilingCosts.locate hB i).1 (localRow hB i) h = A i h := by
  have he := congrArg Fin.val (ThinMatrix.TilingCosts.locate_reconstruct hB i)
  have he' : (ThinMatrix.TilingCosts.locate hB i).1.val * tileWidth L m +
      (ThinMatrix.TilingCosts.locate hB i).2.val = i.val := by
    simpa only [ThinMatrix.TilingCosts.flatten, ThinMatrix.TilingCosts.originalIndex] using he
  simp only [rowBand, localRow, Equiv.apply_symm_apply, he', i.isLt, dite_true]

lemma columnBand_original {N L m : ℕ} (hB : 0 < tileWidth L m)
    (B : Matrix (InnerIndex m) (Fin N) R) (i : Fin N) (h : InnerIndex m) :
    columnBand B (ThinMatrix.TilingCosts.locate hB i).1 h (localRow hB i) = B h i := by
  have he := congrArg Fin.val (ThinMatrix.TilingCosts.locate_reconstruct hB i)
  have he' : (ThinMatrix.TilingCosts.locate hB i).1.val * tileWidth L m +
      (ThinMatrix.TilingCosts.locate hB i).2.val = i.val := by
    simpa only [ThinMatrix.TilingCosts.flatten, ThinMatrix.TilingCosts.originalIndex] using he
  simp only [columnBand, localRow, Equiv.apply_symm_apply, he', i.isLt, dite_true]

lemma genuine_tile_product {N L m : ℕ} (hB : 0 < tileWidth L m)
    (A : Matrix (Fin N) (InnerIndex m) R) (B : Matrix (InnerIndex m) (Fin N) R)
    (i j : Fin N) :
    (rowBand A (ThinMatrix.TilingCosts.locate hB i).1 *
      columnBand B (ThinMatrix.TilingCosts.locate hB j).1)
      (localRow hB i) (localRow hB j) = (A*B) i j := by
  simp only [Matrix.mul_apply, rowBand_original, columnBand_original]

lemma fullGrid_padding (N L m : ℕ) (hm : m ≤ L) (hgeometry : tileWidth L m ≤ N) :
    N ≤ ThinMatrix.TilingCosts.paddedSize N (tileWidth L m) ∧
      ThinMatrix.TilingCosts.paddedSize N (tileWidth L m) ≤ 2*N :=
  ⟨ThinMatrix.TilingCosts.padding_lower _ _ (tileWidth_pos L m hm),
    ThinMatrix.TilingCosts.padding_upper _ _ (tileWidth_pos L m hm) hgeometry⟩



#print axioms ThinMatrix.ThinMatrixBackend.genuine_tile_product
#print axioms ThinMatrix.ThinMatrixBackend.fullGrid_padding

/-- A magnitude bound computed from the two stored coefficient vectors. -/
def productMagnitude {q : ℕ} (a b : Vector ℤ q) : ℕ :=
  1 + (∑ r : Fin q, (a.get r).natAbs) + ∑ r : Fin q, (b.get r).natAbs

lemma productMagnitude_left {q : ℕ} (a b : Vector ℤ q) (r : Fin q) :
    (a.get r).natAbs ≤ productMagnitude a b := by
  have hs := Finset.single_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin q))) =>
    Nat.zero_le (a.get i).natAbs) (Finset.mem_univ r)
  unfold productMagnitude
  omega

lemma productMagnitude_right {q : ℕ} (a b : Vector ℤ q) (r : Fin q) :
    (b.get r).natAbs ≤ productMagnitude a b := by
  have hs := Finset.single_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin q))) =>
    Nat.zero_le (b.get i).natAbs) (Finset.mem_univ r)
  unfold productMagnitude
  omega

lemma integerProduct_length {q : ℕ} (A : ℕ) (a b : CyclicRing.Cyclic q) :
    (ThinMatrix.ApproximateConvolution.multiplication A a b).value.length = q := by
  simp [ThinMatrix.ApproximateConvolution.multiplication,
    ThinMatrix.ApproximateConvolution.cyclic, ThinMatrix.FastConvolution.Counted.sequence_value]

/-- Exact all-coefficient integer multiplication uses the proved array
fixed-point FFT program. The computed magnitude controls precision and
both arithmetic and array actions are charged. -/
def cyclicVectorProduct {q : ℕ} (a b : Vector ℤ q) : Vector ℤ q × ℕ :=
  let product := ThinMatrix.ArrayFFT.multiplication q (productMagnitude a b) a.toArray b.toArray
  (⟨product.value, ThinMatrix.ArrayFFT.multiplication_size _ _ _ _⟩,
    product.arithmeticAllowance + product.arrayActions + 10*q)

lemma vector_getD {q : ℕ} (a : Vector ℤ q) (r : Fin q) :
    a.toArray.getD r.val 0 = a.get r := by
  simp [Array.getD, r.isLt, Vector.get]

lemma cyclicVectorProduct_correct {q : ℕ} [NeZero q] (a b : Vector ℤ q) (r : Fin q) :
    (cyclicVectorProduct a b).1.get r = CyclicRing.convolution a.get b.get r := by
  have ha (i : Fin q) : (a.toArray.getD i.val 0).natAbs ≤ productMagnitude a b := by
    rw [vector_getD]
    exact productMagnitude_left a b i
  have hb (i : Fin q) : (b.toArray.getD i.val 0).natAbs ≤ productMagnitude a b := by
    rw [vector_getD]
    exact productMagnitude_right a b i
  have h := ThinMatrix.ArrayFFT.multiplication_correct_natAbs q (productMagnitude a b)
    (by unfold productMagnitude; omega) a.toArray b.toArray ha hb r
  have hca : ThinMatrix.ArrayFFT.asCyclic q a.toArray = a.get := by funext i; exact vector_getD a i
  have hcb : ThinMatrix.ArrayFFT.asCyclic q b.toArray = b.get := by funext i; exact vector_getD b i
  rw [hca, hcb] at h
  have hr : r.val < (ThinMatrix.ArrayFFT.multiplication q (productMagnitude a b)
      a.toArray b.toArray).value.size := by
    rw [ThinMatrix.ArrayFFT.multiplication_size]
    exact r.isLt
  simpa only [cyclicVectorProduct, Vector.get, Fin.val_cast, Array.getD, dif_pos hr, Array.getInternal_eq_getElem] using h

section SourceStorage
open SourceFormation

/-- A conservative allowance includes forming the compact input address,
scanning at most all binary set masks, and the original coefficient read. -/
def inputEntryAllowance (L m : ℕ) : ℕ := 100*(L+m+1)^3*2^L

/-- The input adapter is materialized before Walsh formation. Its radix
keys are the full set mask, full outside-bit vector, outer coordinate,
and the two actual middle labels. Extra set/bit addresses are filled by
reads of the original compact matrix or by literal zero. -/
abbrev InputStore (L m q : ℕ) :=
  Table (Table (Table (Table (Table (Vector ℤ q) 2 m) 2 m) 2 (L-m)) 2 L) 2 L

noncomputable def buildLeftInput {L m q : ℕ} [NeZero q]
    (A : Matrix (OuterIndex L m) (InnerIndex m) (CyclicRing.Cyclic q)) : Program (InputStore L m q) :=
  tableBuild 2 L fun Q => tableBuild 2 L fun bits =>
    tableBuild 2 (L-m) fun outer => tableBuild 2 m fun h1 => tableBuild 2 m fun h2 =>
      vectorBuild q fun r =>
        { value := rawLeft A (cubeSupport (keyCube Q)) (keyCube bits) (keyCube outer)
            (keyCube h1) (keyCube h2) r
          operations := inputEntryAllowance L m }

noncomputable def buildRightInput {L m q : ℕ} [NeZero q]
    (B : Matrix (InnerIndex m) (OuterIndex L m) (CyclicRing.Cyclic q)) : Program (InputStore L m q) :=
  tableBuild 2 L fun Q => tableBuild 2 L fun bits =>
    tableBuild 2 (L-m) fun outer => tableBuild 2 m fun h1 => tableBuild 2 m fun h2 =>
      vectorBuild q fun r =>
        { value := rawRight B (cubeSupport (keyCube Q)) (keyCube bits)
            (keyCube h1) (keyCube h2) (keyCube outer) r
          operations := inputEntryAllowance L m }

def readInput {L m q : ℕ} (store : InputStore L m q)
    (Q : Finset (Fin L)) (bits : Cube L) (outer : Cube (L-m)) (h1 h2 : Cube m) (r : Fin q) : ℤ :=
  (tableRead 2 m (tableRead 2 m (tableRead 2 (L-m)
    (tableRead 2 L (tableRead 2 L store (cubeKey (setBits Q))) (cubeKey bits))
    (cubeKey outer)) (cubeKey h1)) (cubeKey h2)).get r

lemma cubeSupport_setBits {L : ℕ} (Q : Finset (Fin L)) : cubeSupport (setBits Q) = Q := by
  ext i
  simp [cubeSupport, setBits]

lemma readInput_buildLeft {L m q : ℕ} [NeZero q]
    (A : Matrix (OuterIndex L m) (InnerIndex m) (CyclicRing.Cyclic q))
    (Q : Finset (Fin L)) (bits : Cube L) (outer : Cube (L-m)) (h1 h2 : Cube m) (r : Fin q) :
    readInput (buildLeftInput A).value Q bits outer h1 h2 r = rawLeft A Q bits outer h1 h2 r := by
  unfold readInput buildLeftInput
  simp only [tableRead_build, keyCube_cubeKey, cubeSupport_setBits, vectorBuild_get]

lemma readInput_buildRight {L m q : ℕ} [NeZero q]
    (B : Matrix (InnerIndex m) (OuterIndex L m) (CyclicRing.Cyclic q))
    (Q : Finset (Fin L)) (bits : Cube L) (outer : Cube (L-m)) (h1 h2 : Cube m) (r : Fin q) :
    readInput (buildRightInput B).value Q bits outer h1 h2 r = rawRight B Q bits h1 h2 outer r := by
  unfold readInput buildRightInput
  simp only [tableRead_build, keyCube_cubeKey, cubeSupport_setBits, vectorBuild_get]

/-- Every input-adapter cell and radix-tree allocation is included. -/
def binaryTableBudget (n B : ℕ) : ℕ := (B+16*n)*2^n

def inputBudget (L m q : ℕ) : ℕ :=
  binaryTableBudget L (binaryTableBudget L (binaryTableBudget (L-m)
    (binaryTableBudget m (binaryTableBudget m ((inputEntryAllowance L m+8)*q)))))

lemma buildLeftInput_cost {L m q : ℕ} [NeZero q]
    (A : Matrix (OuterIndex L m) (InnerIndex m) (CyclicRing.Cyclic q)) :
    (buildLeftInput A).operations ≤ inputBudget L m q := by
  unfold buildLeftInput inputBudget binaryTableBudget
  apply tableBuild_cost
  intro Q
  apply tableBuild_cost
  intro bits
  apply tableBuild_cost
  intro outer
  apply tableBuild_cost
  intro h1
  apply tableBuild_cost
  intro h2
  apply vectorBuild_cost
  intro r
  exact le_rfl

lemma buildRightInput_cost {L m q : ℕ} [NeZero q]
    (B : Matrix (InnerIndex m) (OuterIndex L m) (CyclicRing.Cyclic q)) :
    (buildRightInput B).operations ≤ inputBudget L m q := by
  unfold buildRightInput inputBudget binaryTableBudget
  apply tableBuild_cost
  intro Q
  apply tableBuild_cost
  intro bits
  apply tableBuild_cost
  intro outer
  apply tableBuild_cost
  intro h1
  apply tableBuild_cost
  intro h2
  apply vectorBuild_cost
  intro r
  exact le_rfl

/-- Formation reads an already stored radix table, with a path-length
counter; it does not invoke a deferred raw-input function. -/
def leftInputReader {L m q : ℕ} (store : InputStore L m q) : LeftRead L m (L-m) q :=
  fun Q bits outer h1 h2 r =>
    { value := readInput store Q bits outer h1 h2 r
      operations := 8*(3*L+m+1) }

def rightInputReader {L m q : ℕ} (store : InputStore L m q) : RightRead L m (L-m) q :=
  fun Q bits h1 h2 outer r =>
    { value := readInput store Q bits outer h1 h2 r
      operations := 8*(3*L+m+1) }

def goodMasks (L m : ℕ) : List (Cube L) :=
  (RowIndexing.goodCodes L m).map (RowIndexing.cubeEquiv L).symm

lemma maskSlots_goodMasks (L m : ℕ) : maskSlots (goodMasks L m) = goodSlots L m := by
  ext Q
  simp only [maskSlots, goodMasks, List.map_map, Function.comp_def, List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨code,hcode,rfl⟩
    exact (RowIndexing.mem_goodCodes L m code).mp hcode
  · intro hQ
    refine ⟨RowIndexing.cubeEquiv L (setBits Q), ?_, ?_⟩
    · rw [RowIndexing.mem_goodCodes]
      simpa only [Equiv.symm_apply_apply, cubeSupport_setBits] using hQ
    · simp only [Equiv.symm_apply_apply, cubeSupport_setBits]

noncomputable def sourceEnvironment (L m : ℕ) : Environment L m (L-m) where
  good := (prepareGood (goodMasks L m)).value
  gammaColumns := Vector.ofFn (fun i => Vector.ofFn
    (boolColumns (GoodSetConstruction.constructGoodMaps L m).1 i))
  deltaColumns := Vector.ofFn (fun i => Vector.ofFn
    (boolColumns (GoodSetConstruction.constructGoodMaps L m).2 i))

lemma sourceEnvironment_good (L m : ℕ) (n : Fin L → NormalLetter) :
    readGood (sourceEnvironment L m).good n = decide (normalSupport n ∈ goodSlots L m) := by
  rw [sourceEnvironment, readGood_prepare, maskSlots_goodMasks]

lemma sourceEnvironment_gamma (L m : ℕ) :
    (sourceEnvironment L m).gamma = cubeMap (GoodSetConstruction.constructGoodMaps L m).1 := by
  unfold Environment.gamma sourceEnvironment columnFunction cubeMap
  simp only [Vector.get_ofFn]

lemma sourceEnvironment_delta (L m : ℕ) :
    (sourceEnvironment L m).delta = cubeMap (GoodSetConstruction.constructGoodMaps L m).2 := by
  unfold Environment.delta sourceEnvironment columnFunction cubeMap
  simp only [Vector.get_ofFn]

noncomputable def prepareLeftSource {L m q : ℕ} [NeZero q]
    (A : Matrix (OuterIndex L m) (InnerIndex m) (CyclicRing.Cyclic q))
    (run : ℤ) : Program (RawStore L q) :=
  let input := buildLeftInput A
  let source := formLeftSource (sourceEnvironment L m) (leftInputReader input.value) run
  ⟨source.value, input.operations + source.operations⟩

noncomputable def prepareRightSource {L m q : ℕ} [NeZero q]
    (B : Matrix (InnerIndex m) (OuterIndex L m) (CyclicRing.Cyclic q))
    (run : ℤ) : Program (RawStore L q) :=
  let input := buildRightInput B
  let source := formRightSource (sourceEnvironment L m) (rightInputReader input.value) run
  ⟨source.value, input.operations + source.operations⟩

lemma prepareLeftSource_correct {L m q : ℕ} [NeZero q]
    (A : Matrix (OuterIndex L m) (InnerIndex m) (CyclicRing.Cyclic q)) (run : ℤ)
    (n : Fin L → NormalLetter) (o : Fin L → OppositeLetter) (r : Fin q) :
    readRaw (prepareLeftSource A run).value n o r =
      rawLeftSource (rawLeft A) (goodSlots L m)
        (cubeMap (GoodSetConstruction.constructGoodMaps L m).1)
        (cubeMap (GoodSetConstruction.constructGoodMaps L m).2) run n o r := by
  have h := formLeftSource_correct (sourceEnvironment L m)
    (leftInputReader (buildLeftInput A).value) (rawLeft A) (goodSlots L m)
    (sourceEnvironment_good L m) (readInput_buildLeft A) run n o r
  simpa only [prepareLeftSource, sourceEnvironment_gamma, sourceEnvironment_delta] using h

lemma prepareRightSource_correct {L m q : ℕ} [NeZero q]
    (B : Matrix (InnerIndex m) (OuterIndex L m) (CyclicRing.Cyclic q)) (run : ℤ)
    (n : Fin L → NormalLetter) (o : Fin L → OppositeLetter) (r : Fin q) :
    readRaw (prepareRightSource B run).value n o r =
      rawRightSource (rawRight B) (goodSlots L m)
        (cubeMap (GoodSetConstruction.constructGoodMaps L m).1)
        (cubeMap (GoodSetConstruction.constructGoodMaps L m).2) run n o r := by
  have h := formRightSource_correct (sourceEnvironment L m)
    (rightInputReader (buildRightInput B).value) (rawRight B) (goodSlots L m)
    (sourceEnvironment_good L m) (fun Q bits h1 h2 outer r => readInput_buildRight B Q bits outer h1 h2 r)
    run n o r
  simpa only [prepareRightSource, sourceEnvironment_gamma, sourceEnvironment_delta] using h

end SourceStorage



#print axioms ThinMatrix.ThinMatrixBackend.prepareLeftSource_correct
#print axioms ThinMatrix.ThinMatrixBackend.prepareRightSource_correct

abbrev SourceRuns (m : ℕ) := ↥(Finset.Icc (-(m : ℤ)) (m : ℤ))

lemma sourceRuns_card (m : ℕ) : Fintype.card (SourceRuns m) = 2*m+1 := by
  simp [SourceRuns]
  omega

noncomputable def sourceRunEquiv (m : ℕ) : SourceRuns m ≃ Fin (2*m+1) :=
  Fintype.equivFinOfCardEq (sourceRuns_card m)

/-- Both input adapters and the source environment are built once. Every
same-degree run is then materialized once in backing vectors. -/
structure SourcePreparation (L m q : ℕ) where
  environment : SourceFormation.Environment L m (L-m)
  leftInput : InputStore L m q
  rightInput : InputStore L m q
  runs : Vector (SourceFormation.RawStore L q × SourceFormation.RawStore L q) (2*m+1)
  operations : ℕ

noncomputable def prepareSources {L m q : ℕ} [NeZero q]
    (A : Matrix (OuterIndex L m) (InnerIndex m) (CyclicRing.Cyclic q))
    (B : Matrix (InnerIndex m) (OuterIndex L m) (CyclicRing.Cyclic q)) : SourcePreparation L m q :=
  let env := sourceEnvironment L m
  let inputA := buildLeftInput A
  let inputB := buildRightInput B
  let runs := Vector.ofFn fun i : Fin (2*m+1) =>
    let run := ((sourceRunEquiv m).symm i).val
    let left := SourceFormation.formLeftSource env (leftInputReader inputA.value) run
    let right := SourceFormation.formRightSource env (rightInputReader inputB.value) run
    ((left.value, right.value), left.operations + right.operations)
  { environment := env
    leftInput := inputA.value
    rightInput := inputB.value
    runs := runs.map Prod.fst
    operations := inputA.operations + inputB.operations +
      (SourceFormation.prepareGood (goodMasks L m)).operations + 10*(L+1)^2 +
      ∑ i : Fin (2*m+1), (runs.get i).2 }

noncomputable def sourceStores {L m q : ℕ} (prepared : SourcePreparation L m q) (run : SourceRuns m) :
    SourceFormation.RawStore L q × SourceFormation.RawStore L q :=
  prepared.runs.get (sourceRunEquiv m run)

lemma prepareSources_left {L m q : ℕ} [NeZero q]
    (A : Matrix (OuterIndex L m) (InnerIndex m) (CyclicRing.Cyclic q))
    (B : Matrix (InnerIndex m) (OuterIndex L m) (CyclicRing.Cyclic q))
    (run : SourceRuns m) (n : Fin L → NormalLetter) (o : Fin L → OppositeLetter) (r : Fin q) :
    SourceFormation.readRaw (sourceStores (prepareSources A B) run).1 n o r =
      rawLeftSource (rawLeft A) (goodSlots L m)
        (cubeMap (GoodSetConstruction.constructGoodMaps L m).1)
        (cubeMap (GoodSetConstruction.constructGoodMaps L m).2) run.val n o r := by
  have h := SourceFormation.formLeftSource_correct (sourceEnvironment L m)
    (leftInputReader (buildLeftInput A).value) (rawLeft A) (goodSlots L m)
    (sourceEnvironment_good L m) (readInput_buildLeft A) run.val n o r
  simpa only [sourceStores, prepareSources, Vector.get_map, Vector.get_ofFn,
    Equiv.symm_apply_apply, sourceEnvironment_gamma, sourceEnvironment_delta] using h

lemma prepareSources_right {L m q : ℕ} [NeZero q]
    (A : Matrix (OuterIndex L m) (InnerIndex m) (CyclicRing.Cyclic q))
    (B : Matrix (InnerIndex m) (OuterIndex L m) (CyclicRing.Cyclic q))
    (run : SourceRuns m) (n : Fin L → NormalLetter) (o : Fin L → OppositeLetter) (r : Fin q) :
    SourceFormation.readRaw (sourceStores (prepareSources A B) run).2 n o r =
      rawRightSource (rawRight B) (goodSlots L m)
        (cubeMap (GoodSetConstruction.constructGoodMaps L m).1)
        (cubeMap (GoodSetConstruction.constructGoodMaps L m).2) run.val n o r := by
  have h := SourceFormation.formRightSource_correct (sourceEnvironment L m)
    (rightInputReader (buildRightInput B).value) (rawRight B) (goodSlots L m)
    (sourceEnvironment_good L m) (fun Q bits h1 h2 outer r => readInput_buildRight B Q bits outer h1 h2 r)
    run.val n o r
  simpa only [sourceStores, prepareSources, Vector.get_map, Vector.get_ofFn,
    Equiv.symm_apply_apply, sourceEnvironment_gamma, sourceEnvironment_delta] using h



#print axioms ThinMatrix.ThinMatrixBackend.cyclicVectorProduct_correct
#print axioms ThinMatrix.ThinMatrixBackend.prepareSources_left
#print axioms ThinMatrix.ThinMatrixBackend.prepareSources_right

/-- The full-vector arithmetic primitive has a concrete run and value
specification. The backend below instantiates it with the proved array FFT;
other proved integer programs can use the identical preparation pipeline. -/
structure FullMultiplier (q : ℕ) [NeZero q] where
  run : Vector ℤ q → Vector ℤ q → Vector ℤ q × ℕ
  correct : ∀ a b r, (run a b).1.get r = CyclicRing.convolution a.get b.get r

def fftFullMultiplier (q : ℕ) [NeZero q] : FullMultiplier q :=
  ⟨cyclicVectorProduct, cyclicVectorProduct_correct⟩

lemma fftFullMultiplier_work {q : ℕ} [NeZero q] (a b : Vector ℤ q) :
    ((fftFullMultiplier q).run a b).2 ≤
      46000 * (ThinMatrix.FastConvolution.paddedExponent q + 1) * q *
        (ThinMatrix.FastConvolution.paddedExponent q + (productMagnitude a b).log2 + 100)^2 + 10*q := by
  exact Nat.add_le_add_right
    (ThinMatrix.ArrayFFT.multiplication_totalAllowance q (productMagnitude a b) a.toArray b.toArray) _

def booleanCubeEquiv (n : ℕ) : Cube n ≃ Fin (2^n) :=
  (Equiv.piCongrRight (fun _ : Fin n => finTwoEquiv.symm)).trans finFunctionFinEquiv

def middleEquiv (m : ℕ) : InnerIndex m ≃ Fin (4^m) :=
  ((booleanCubeEquiv m).prodCongr (booleanCubeEquiv m)).trans
    (finProdFinEquiv.trans (finCongr (by rw [← mul_pow]; norm_num)))

/-- Original coefficient cells are backing arrays, before the source
adapter or any transform is evaluated. -/
abbrev StoredLeftMatrix (L m q : ℕ) :=
  Vector (Vector ℤ q) (tileWidth L m * 4^m)

abbrev StoredRightMatrix (L m q : ℕ) :=
  Vector (Vector ℤ q) (4^m * tileWidth L m)

noncomputable def readLeftMatrix {L m q : ℕ} (data : StoredLeftMatrix L m q) :
    Matrix (OuterIndex L m) (InnerIndex m) (CyclicRing.Cyclic q) :=
  fun row h r => (data.get (finProdFinEquiv (rowEquiv L m row, middleEquiv m h))).get r

noncomputable def readRightMatrix {L m q : ℕ} (data : StoredRightMatrix L m q) :
    Matrix (InnerIndex m) (OuterIndex L m) (CyclicRing.Cyclic q) :=
  fun h col r => (data.get (finProdFinEquiv (middleEquiv m h, rowEquiv L m col))).get r

noncomputable def materializeLeftMatrix {L m q : ℕ}
    (A : Matrix (OuterIndex L m) (InnerIndex m) (CyclicRing.Cyclic q)) : StoredLeftMatrix L m q :=
  Vector.ofFn (fun address => Vector.ofFn (fun r =>
    A ((rowEquiv L m).symm (finProdFinEquiv.symm address).1)
      ((middleEquiv m).symm (finProdFinEquiv.symm address).2) r))

noncomputable def materializeRightMatrix {L m q : ℕ}
    (B : Matrix (InnerIndex m) (OuterIndex L m) (CyclicRing.Cyclic q)) : StoredRightMatrix L m q :=
  Vector.ofFn (fun address => Vector.ofFn (fun r =>
    B ((middleEquiv m).symm (finProdFinEquiv.symm address).1)
      ((rowEquiv L m).symm (finProdFinEquiv.symm address).2) r))

lemma read_materializeLeftMatrix {L m q : ℕ}
    (A : Matrix (OuterIndex L m) (InnerIndex m) (CyclicRing.Cyclic q)) :
    readLeftMatrix (materializeLeftMatrix A) = A := by
  funext row h r
  simp only [readLeftMatrix, materializeLeftMatrix, Vector.get_ofFn, Equiv.symm_apply_apply]

lemma read_materializeRightMatrix {L m q : ℕ}
    (B : Matrix (InnerIndex m) (OuterIndex L m) (CyclicRing.Cyclic q)) :
    readRightMatrix (materializeRightMatrix B) = B := by
  funext h col r
  simp only [readRightMatrix, materializeRightMatrix, Vector.get_ofFn, Equiv.symm_apply_apply]



#print axioms ThinMatrix.ThinMatrixBackend.fftFullMultiplier_work
#print axioms ThinMatrix.ThinMatrixBackend.read_materializeLeftMatrix
#print axioms ThinMatrix.ThinMatrixBackend.read_materializeRightMatrix

section HighPreparation
open HighBoxDP

structure PreparedHigh (L m t q : ℕ) where
  left : HighBaseEncoder.StoredResult (Vector ℤ q) (2*L)
  right : HighBaseEncoder.StoredResult (Vector ℤ q) (2*L)
  table : StoredHighDP.Trie (Vector ℤ q)
  operations : ℕ

def cachedBaseProduct {L m t q : ℕ} [NeZero q] (M : FullMultiplier q)
    (left right : HighBaseEncoder.StoredResult (Vector ℤ q) (2*L))
    (w : BaseStates L m t) : StoredHighDP.BaseResult ℤ q :=
  let a := HighBaseEncoder.readBase left w
  let b := HighBaseEncoder.readBase right w
  let product := M.run a b
  (product.1, product.2 + 2*(4*L+1))

noncomputable def prepareHigh {L m t q : ℕ} [NeZero q] (M : FullMultiplier q)
    (X Y : SourceWord L → CyclicRing.Cyclic q) : PreparedHigh L m t q :=
  let left := HighBaseEncoder.encodeLeftSource (m := m) (t := t) X
  let right := HighBaseEncoder.encodeRightSource (m := m) (t := t) Y
  let high := ArrayKeys.highExecuteCounted (m := m) (t := t)
    (StoredHighDP.guardedBase (cachedBaseProduct (m := m) (t := t) M left right)) (2*L+1)
  { left := left
    right := right
    table := high.1
    operations := left.encoding.coefficientWork + left.encoding.capWork + left.trieWork +
      right.encoding.coefficientWork + right.encoding.capWork + right.trieWork + high.2 }

noncomputable def intendedGlobal {L q : ℕ} [NeZero q]
    (X Y : SourceWord L → CyclicRing.Cyclic q) (v : LeafWord (2*L)) : Vector ℤ q :=
  Vector.ofFn (fun r => globalLeaf X Y sourceF sourceG v r)

lemma cachedBaseProduct_correct {L m t q : ℕ} [NeZero q] (M : FullMultiplier q)
    (X Y : SourceWord L → CyclicRing.Cyclic q) (w : BaseStates L m t) :
    (cachedBaseProduct M (HighBaseEncoder.encodeLeftSource (m := m) (t := t) X)
      (HighBaseEncoder.encodeRightSource (m := m) (t := t) Y) w).1 =
      intendedGlobal X Y (baseLeaf w.val w.property.2) := by
  apply Vector.ext
  intro i hi
  let r : Fin q := ⟨i,hi⟩
  change (M.run _ _).1.get r = _
  rw [M.correct]
  have ha : (HighBaseEncoder.readBase (HighBaseEncoder.encodeLeftSource (m := m) (t := t) X) w).get =
      ∑ a : SourceWord L, X a * ∏ i, sourceF i (baseLeaf w.val w.property.2 i) a := by
    funext s
    exact HighBaseEncoder.encodeLeftSource_read X w s
  have hb : (HighBaseEncoder.readBase (HighBaseEncoder.encodeRightSource (m := m) (t := t) Y) w).get =
      ∑ b : SourceWord L, Y b * ∏ i, sourceG i (baseLeaf w.val w.property.2 i) b := by
    funext s
    exact HighBaseEncoder.encodeRightSource_read Y w s
  rw [ha, hb, ← CyclicRing.mul_eq_convolution]
  simp only [intendedGlobal, Vector.getElem_ofFn, globalLeaf]
  rfl

lemma prepareHigh_coefficient {L m t q : ℕ} [NeZero q] (M : FullMultiplier q)
    (X Y : SourceWord L → CyclicRing.Cyclic q) (w : States L m t) (r : Fin q) :
    (StoredHighDP.lookup (prepareHigh (m := m) (t := t) M X Y).table w.val).get r =
      tableAfter (fun v => globalLeaf X Y sourceF sourceG v r) (2*L+1) w := by
  change (StoredHighDP.lookup
    (ArrayKeys.highExecuteCounted (m := m) (t := t)
      (StoredHighDP.guardedBase (cachedBaseProduct (m := m) (t := t) M
        (HighBaseEncoder.encodeLeftSource (m := m) (t := t) X)
        (HighBaseEncoder.encodeRightSource (m := m) (t := t) Y))) (2*L+1)).1 w.val).get r = _
  rw [ArrayKeys.highExecuteCounted_value, ArrayKeys.highExecute_refine]
  have h := StoredHighDP.guarded_execute_complete
    (cachedBaseProduct M (HighBaseEncoder.encodeLeftSource (m := m) (t := t) X)
      (HighBaseEncoder.encodeRightSource (m := m) (t := t) Y))
    (intendedGlobal X Y) (cachedBaseProduct_correct M X Y) w r
  rw [StoredHighDP.executeCounted_value] at h
  rw [tableAfter_complete]
  have hg : StoredHighDP.logicalLeaf (intendedGlobal X Y) r =
      (fun v => globalLeaf X Y sourceF sourceG v r) := by
    funext v
    exact Vector.get_ofFn _ _
  rw [hg] at h
  exact h

end HighPreparation



#print axioms ThinMatrix.ThinMatrixBackend.cachedBaseProduct_correct
#print axioms ThinMatrix.ThinMatrixBackend.prepareHigh_coefficient

section HighQueries
open HighBoxDP

/-- A physical state query materializes its key, reads the stored vector,
and selects precisely the requested coefficient. -/
def queryHighState {L m t q : ℕ} (prepared : PreparedHigh L m t q)
    (w : States L m t) (r : Fin q) : ℤ × ℕ :=
  let result := ArrayKeys.readSelected prepared.table (ArrayKeys.materialize w.val) r
  (result.1.getD 0, 2*L + result.2)

lemma queryHighState_value {L m t q : ℕ} (prepared : PreparedHigh L m t q)
    (w : States L m t) (r : Fin q) :
    (queryHighState prepared w r).1 = (StoredHighDP.lookup prepared.table w.val).get r := by
  simp only [queryHighState, ArrayKeys.readSelected_value, ArrayKeys.toWord_materialize,
    StoredHighDP.readCoefficient, StoredHighDP.lookup]
  cases h : prepared.table.read (StoredHighDP.key w.val) <;>
    simp [StoredHighDP.zeroVector]

lemma queryHighState_work {L m t q : ℕ} (prepared : PreparedHigh L m t q)
    (w : States L m t) (r : Fin q) :
    (queryHighState prepared w r).2 = 6*L+2 := by
  simp [queryHighState]
  omega

lemma queryHighState_correct {L m t q : ℕ} [NeZero q] (M : FullMultiplier q)
    (X Y : SourceWord L → CyclicRing.Cyclic q) (w : States L m t) (r : Fin q) :
    (queryHighState (prepareHigh (m := m) (t := t) M X Y) w r).1 =
      tableAfter (fun v => globalLeaf X Y sourceF sourceG v r) (2*L+1) w := by
  rw [queryHighState_value]
  exact prepareHigh_coefficient M X Y w r

/-- Each generated mask lists only its true ordinary-key assignments.
The key type has exactly `4^t` members, independently of the physical L. -/
noncomputable def queryHighBox {L m t k q : ℕ} [NeZero q]
    (hk : k = 2*m) (e : Fin k ↪o Fin (2*L)) (outside : Fin (2*L) → Fin 4)
    (hleft : ((embeddedSupport e).filter (fun i => i.val < L)).card ≤ m)
    (hright : ((embeddedSupport e).filter (fun i => L ≤ i.val)).card ≤ m)
    (prepared : PreparedHigh L m t q) (ms : List (Option Bool)) (r : Fin q) : ℤ × ℕ :=
  if hms : ms ∈ ThinMatrix.OrderedBoxes.orderedBoxMasks t k then
    let hlen := (ThinMatrix.OrderedBoxes.orderedBoxMasks_shape hms).1
    let e' := reindexEmbedding ms hlen e
    let keys : List (SelectedAssignments (embeddedMask e' (reverseMask ms)) (embeddedSupport e')) :=
      Finset.univ.toList
    let rows := keys.map fun a => queryHighState prepared
      (physicalState ms hms (hlen.trans hk) e' outside
        (by simpa only [e', reindexEmbedding_support] using hleft)
        (by simpa only [e', reindexEmbedding_support] using hright) a) r
    ((rows.map Prod.fst).sum, (rows.map Prod.snd).sum)
  else (0,0)

/-- A stored physical key is queried without reconstructing a semantic state. -/
def queryHighKey {L m t q : ℕ} (prepared : PreparedHigh L m t q)
    (key : ArrayKeys.Key (2*L)) (r : Fin q) : ℤ × ℕ :=
  let result := ArrayKeys.readSelected prepared.table key r
  (result.1.getD 0,result.2)

@[simp] lemma queryHighKey_materialize {L m t q : ℕ} (prepared : PreparedHigh L m t q)
    (w : States L m t) (r : Fin q) :
    (queryHighKey prepared (ArrayKeys.materialize w.val) r).1 = (queryHighState prepared w r).1 := rfl

@[simp] lemma queryHighKey_work {L m t q : ℕ} (prepared : PreparedHigh L m t q)
    (key : ArrayKeys.Key (2*L)) (r : Fin q) :
    (queryHighKey prepared key r).2 = 4*L+2 := by
  simp [queryHighKey]
  omega

/-- The production mask loop carries its membership proof and directly
materializes the four-way digit keys. No finite-universe enumeration or
whole-mask-list membership test is performed here. -/
noncomputable def queryHighBoxGenerated {L m t k q : ℕ} [NeZero q]
    (_hk : k = 2*m) (e : Fin k ↪o Fin (2*L)) (outside : Fin (2*L) → Fin 4)
    (_hleft : ((embeddedSupport e).filter (fun i => i.val < L)).card ≤ m)
    (_hright : ((embeddedSupport e).filter (fun i => L ≤ i.val)).card ≤ m)
    (prepared : PreparedHigh L m t q) (ms : List (Option Bool))
    (hms : ms ∈ ThinMatrix.OrderedBoxes.orderedBoxMasks t k) (r : Fin q) : ℤ × ℕ :=
  let hlen := (ThinMatrix.OrderedBoxes.orderedBoxMasks_shape hms).1
  let e' := reindexEmbedding ms hlen e
  let keys := HighQueryKeys.physicalKeysCounted ms e' (Vector.ofFn outside)
  let rows := keys.1.map (fun key => queryHighKey prepared key r)
  ((rows.map Prod.fst).sum,keys.2+(rows.map Prod.snd).sum+2*rows.length)

lemma queryHighBoxGenerated_refines {L m t k q : ℕ} [NeZero q]
    (hk : k = 2*m) (e : Fin k ↪o Fin (2*L)) (outside : Fin (2*L) → Fin 4)
    (hleft : ((embeddedSupport e).filter (fun i => i.val < L)).card ≤ m)
    (hright : ((embeddedSupport e).filter (fun i => L ≤ i.val)).card ≤ m)
    (prepared : PreparedHigh L m t q) (ms : List (Option Bool))
    (hms : ms ∈ ThinMatrix.OrderedBoxes.orderedBoxMasks t k) (r : Fin q) :
    (queryHighBoxGenerated hk e outside hleft hright prepared ms hms r).1 =
      (queryHighBox hk e outside hleft hright prepared ms r).1 := by
  simp only [queryHighBoxGenerated,HighQueryKeys.physicalKeysCounted_value,
    queryHighBox,dif_pos hms,List.map_map,Function.comp_def]
  rw [HighQueryKeys.physicalState_sum ms hms
    ((ThinMatrix.OrderedBoxes.orderedBoxMasks_shape hms).1.trans hk)
    (reindexEmbedding ms (ThinMatrix.OrderedBoxes.orderedBoxMasks_shape hms).1 e)
    (Vector.ofFn outside)
    (by simpa only [reindexEmbedding_support] using hleft)
    (by simpa only [reindexEmbedding_support] using hright)]
  simp only [queryHighKey_materialize]
  have ho : (Vector.ofFn outside).get = outside := by funext i; exact Vector.get_ofFn _ _
  rw [ho]
  rw [← List.sum_toFinset _ (Finset.nodup_toList _),Finset.toList_toFinset]

/-- The physical location table is built once per HIGH run. All generated
mask/key loops then read the stored coordinates instead of sorting again. -/
def materializeEmbedding {k n : ℕ} (e : Fin k ↪o Fin n) : Fin k ↪o Fin n :=
  let locations := Vector.ofFn e
  OrderEmbedding.ofStrictMono locations.get (by
    intro i j hij
    simpa only [locations,Vector.get_ofFn] using e.strictMono hij)

lemma materializeEmbedding_eq {k n : ℕ} (e : Fin k ↪o Fin n) : materializeEmbedding e = e := by
  ext1 i
  exact Vector.get_ofFn _ _

noncomputable def queryHigh {L m t k q : ℕ} [NeZero q]
    (hk : k = 2*m) (e : Fin k ↪o Fin (2*L)) (outside : Fin (2*L) → Fin 4)
    (hleft : ((embeddedSupport e).filter (fun i => i.val < L)).card ≤ m)
    (hright : ((embeddedSupport e).filter (fun i => L ≤ i.val)).card ≤ m)
    (prepared : PreparedHigh L m t q) (r : Fin q) : ℤ × ℕ :=
  let stored := materializeEmbedding e
  let hsleft : ((embeddedSupport stored).filter (fun i => i.val < L)).card ≤ m := by
    simpa only [stored,materializeEmbedding_eq] using hleft
  let hsright : ((embeddedSupport stored).filter (fun i => L ≤ i.val)).card ≤ m := by
    simpa only [stored,materializeEmbedding_eq] using hright
  let masks := HighQueryKeys.generateMasks t k
  let typed := HighQueryKeys.attachMasks t k masks.1 (HighQueryKeys.generateMasks_value t k)
  let rows := typed.map
    (fun ms => queryHighBoxGenerated hk stored outside hsleft hsright prepared ms.val ms.property r)
  ((rows.map Prod.fst).sum,k+masks.2+(rows.map Prod.snd).sum+2*rows.length)

lemma queryHigh_refines {L m t k q : ℕ} [NeZero q]
    (hk : k = 2*m) (e : Fin k ↪o Fin (2*L)) (outside : Fin (2*L) → Fin 4)
    (hleft : ((embeddedSupport e).filter (fun i => i.val < L)).card ≤ m)
    (hright : ((embeddedSupport e).filter (fun i => L ≤ i.val)).card ≤ m)
    (prepared : PreparedHigh L m t q) (r : Fin q) :
    (queryHigh hk e outside hleft hright prepared r).1 =
      (((ThinMatrix.OrderedBoxes.orderedBoxMasks t k).map
        (fun ms => queryHighBox hk e outside hleft hright prepared ms r)).map Prod.fst).sum := by
  simp only [queryHigh,materializeEmbedding_eq]
  change (((HighQueryKeys.generatedMasks t k).map
    (fun ms => queryHighBoxGenerated hk e outside hleft hright prepared ms.val ms.property r)).map Prod.fst).sum = _
  simp only [List.map_map,Function.comp_def,queryHighBoxGenerated_refines]
  have he := HighQueryKeys.generatedMasks_values t k
  have hf := congrArg (fun xs => (xs.map
    (fun ms => (queryHighBox hk e outside hleft hright prepared ms r).1)).sum) he
  simpa only [List.map_map,Function.comp_def] using hf


lemma tableAfter_coefficient {L m t q : ℕ} [NeZero q]
    (leaf : LeafWord (2*L) → CyclicRing.Cyclic q) (w : States L m t) (r : Fin q) :
    (tableAfter leaf (2*L+1) w) r =
      tableAfter (fun v => leaf v r) (2*L+1) w := by
  rw [tableAfter_complete, tableAfter_complete]
  unfold boxValue
  rw [CyclicRing.sum_coeff]
  apply Finset.sum_congr rfl
  intro v _
  by_cases hv : Compatible w.val v <;> simp [hv, CyclicRing.zero_coeff]

lemma queryHighBox_correct {L m t k q : ℕ} [NeZero q] (M : FullMultiplier q)
    (hk : k = 2*m) (e : Fin k ↪o Fin (2*L)) (outside : Fin (2*L) → Fin 4)
    (hleft : ((embeddedSupport e).filter (fun i => i.val < L)).card ≤ m)
    (hright : ((embeddedSupport e).filter (fun i => L ≤ i.val)).card ≤ m)
    (X Y : SourceWord L → CyclicRing.Cyclic q) (ms : List (Option Bool)) (r : Fin q) :
    (queryHighBox hk e outside hleft hright (prepareHigh (m := m) (t := t) M X Y) ms r).1 =
      (storedBox (t := t) hk e outside hleft hright (globalLeaf X Y sourceF sourceG) ms) r := by
  by_cases hms : ms ∈ ThinMatrix.OrderedBoxes.orderedBoxMasks t k
  · simp only [queryHighBox, storedBox, dif_pos hms, List.map_map, Function.comp_def]
    simp_rw [queryHighState_correct]
    rw [← List.sum_toFinset _ (Finset.nodup_toList _), Finset.toList_toFinset,
      CyclicRing.sum_coeff]
    apply Finset.sum_congr rfl
    intro a _
    exact (tableAfter_coefficient _ _ r).symm
  · simp [queryHighBox, storedBox, hms, CyclicRing.zero_coeff]

lemma cyclic_list_sum_coeff {q : ℕ} [NeZero q]
    (xs : List (CyclicRing.Cyclic q)) (r : Fin q) :
    xs.sum r = (xs.map (fun a => a r)).sum := by
  induction xs with
  | nil => simp [CyclicRing.zero_coeff]
  | cons a xs ih => simp [CyclicRing.add_coeff, ih]

lemma queryHigh_correct {L m t k q : ℕ} [NeZero q] (M : FullMultiplier q)
    (hk : k = 2*m) (e : Fin k ↪o Fin (2*L)) (outside : Fin (2*L) → Fin 4)
    (hleft : ((embeddedSupport e).filter (fun i => i.val < L)).card ≤ m)
    (hright : ((embeddedSupport e).filter (fun i => L ≤ i.val)).card ≤ m)
    (X Y : SourceWord L → CyclicRing.Cyclic q) (r : Fin q) :
    (queryHigh hk e outside hleft hright (prepareHigh (m := m) (t := t) M X Y) r).1 =
      storedHigh (t := t) hk e outside hleft hright (globalLeaf X Y sourceF sourceG) r := by
  rw [queryHigh_refines]
  unfold storedHigh
  rw [cyclic_list_sum_coeff]
  simp only [List.map_map, Function.comp_def]
  congr 1
  apply List.map_congr_left
  intro ms _
  exact queryHighBox_correct M hk e outside hleft hright X Y ms r

lemma queryHighBox_work {L m t k q : ℕ} [NeZero q]
    (hk : k = 2*m) (e : Fin k ↪o Fin (2*L)) (outside : Fin (2*L) → Fin 4)
    (hleft : ((embeddedSupport e).filter (fun i => i.val < L)).card ≤ m)
    (hright : ((embeddedSupport e).filter (fun i => L ≤ i.val)).card ≤ m)
    (prepared : PreparedHigh L m t q) (ms : List (Option Bool))
    (hms : ms ∈ ThinMatrix.OrderedBoxes.orderedBoxMasks t k) (r : Fin q) :
    (queryHighBox hk e outside hleft hright prepared ms r).2 = 4^t*(6*L+2) := by
  simp only [queryHighBox, dif_pos hms, List.map_map, Function.comp_def]
  simp_rw [queryHighState_work]
  rw [List.map_const', List.sum_const_nat, Finset.length_toList, Finset.card_univ]
  rw [physicalState_key_count ms hms]

def highBoxKeyWork (L k : ℕ) : ℕ :=
  HighQueryKeys.physicalFormationWork (2*L) k+HighQueryKeys.keyFactor (2*L)+4*L+4

lemma queryHighBoxGenerated_work {L m t k q : ℕ} [NeZero q]
    (hk : k = 2*m) (e : Fin k ↪o Fin (2*L)) (outside : Fin (2*L) → Fin 4)
    (hleft : ((embeddedSupport e).filter (fun i => i.val < L)).card ≤ m)
    (hright : ((embeddedSupport e).filter (fun i => L ≤ i.val)).card ≤ m)
    (prepared : PreparedHigh L m t q) (ms : List (Option Bool))
    (hms : ms ∈ ThinMatrix.OrderedBoxes.orderedBoxMasks t k) (r : Fin q) :
    (queryHighBoxGenerated hk e outside hleft hright prepared ms hms r).2 ≤
      highBoxKeyWork L k*4^t := by
  have hp := HighQueryKeys.physicalKeysCounted_work_le ms hms
    (reindexEmbedding ms (ThinMatrix.OrderedBoxes.orderedBoxMasks_shape hms).1 e)
    (Vector.ofFn outside)
  simp only [queryHighBoxGenerated,List.map_map,Function.comp_def,queryHighKey_work,
    List.map_const',List.sum_const_nat,List.length_map,
    HighQueryKeys.physicalKeysCounted_value]
  rw [HighQueryKeys.physicalKeys_length ms hms]
  unfold highBoxKeyWork
  nlinarith

def highKeyWork (L k : ℕ) : ℕ := 32*(k+1)^2+highBoxKeyWork L k+k+4

lemma highKeyWork_bound (L k : ℕ) : highKeyWork L k ≤ 10000*(L+k+1)^5 := by
  have hL : L ≤ L+k+1 := by omega
  have hk : k ≤ L+k+1 := by omega
  have hp : 1 ≤ L+k+1 := by omega
  have h2 : (L+k+1)^2 ≤ (L+k+1)^5 := Nat.pow_le_pow_right hp (by omega)
  unfold highKeyWork highBoxKeyWork HighQueryKeys.physicalFormationWork HighQueryKeys.keyFactor
  nlinarith

lemma queryHigh_work {L m t k q : ℕ} [NeZero q]
    (hk : k = 2*m) (e : Fin k ↪o Fin (2*L)) (outside : Fin (2*L) → Fin 4)
    (hleft : ((embeddedSupport e).filter (fun i => i.val < L)).card ≤ m)
    (hright : ((embeddedSupport e).filter (fun i => L ≤ i.val)).card ≤ m)
    (prepared : PreparedHigh L m t q) (r : Fin q) (ht : t ≤ k) :
    (queryHigh hk e outside hleft hright prepared r).2 ≤
      k.choose t*4^t*highKeyWork L k := by
  simp only [queryHigh,materializeEmbedding_eq]
  let rows := (HighQueryKeys.generatedMasks t k).map
    (fun ms => queryHighBoxGenerated hk e outside hleft hright prepared ms.val ms.property r)
  have hh := List.sum_le_card_nsmul (rows.map Prod.snd) (highBoxKeyWork L k*4^t) (by
    intro x hx
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hx
    obtain ⟨ms,_,rfl⟩ := List.mem_map.mp ha
    exact queryHighBoxGenerated_work hk e outside hleft hright prepared ms.val ms.property r)
  have hlen : rows.length = k.choose t := by simp only [rows,List.length_map,HighQueryKeys.generatedMasks_length]
  simp only [List.length_map,smul_eq_mul,hlen] at hh
  have hm := HighQueryKeys.generateMasks_work_small t k
  have hC : 1 ≤ k.choose t := Nat.choose_pos ht
  have hP : 1 ≤ 4^t := Nat.one_le_pow t 4 (by omega)
  have hscale : 32*(k+1)^2*(k.choose t) ≤ 32*(k+1)^2*(k.choose t)*4^t :=
    Nat.le_mul_of_pos_right _ hP
  have hloop : 2*(k.choose t) ≤ 2*(k.choose t)*4^t := Nat.le_mul_of_pos_right _ hP
  have htwo : 2 ≤ 2*(k.choose t)*4^t := by nlinarith
  have hkwork : k ≤ k*(k.choose t)*4^t := by nlinarith
  change k+(HighQueryKeys.generateMasks t k).2+(rows.map Prod.snd).sum+2*rows.length ≤ _
  rw [hlen]
  unfold highKeyWork
  nlinarith

end HighQueries



/-- Original compact entries are read by the literal stored-good-rank and
binary middle-address programs; this is not an arbitrary Fintype locator. -/
def originalLeftReader {L m q : ℕ} (layout : RowIndexing.GoodIndexStore L m)
    (data : StoredLeftMatrix L m q) (row : OuterIndex L m) (h : InnerIndex m) (r : Fin q) :
    SourceFormation.Program ℤ := RowIndexing.readOriginalLeftProgram layout data 0 row h r

def originalRightReader {L m q : ℕ} (layout : RowIndexing.GoodIndexStore L m)
    (data : StoredRightMatrix L m q) (h : InnerIndex m) (col : OuterIndex L m) (r : Fin q) :
    SourceFormation.Program ℤ := RowIndexing.readOriginalRightProgram layout data 0 h col r

lemma originalLeftReader_value {L m q : ℕ} (layout : RowIndexing.GoodIndexStore L m)
    (data : StoredLeftMatrix L m q) (row : OuterIndex L m) (h : InnerIndex m) (r : Fin q) :
    (originalLeftReader layout data row h r).value = readLeftMatrix data row h r := by
  rw [originalLeftReader, RowIndexing.readOriginalLeftProgram_value]
  simp only [Nat.zero_mul, Nat.zero_add, tileWidth,
    (RowIndexing.rowEquiv L m row).isLt, dite_true]
  rfl

lemma originalRightReader_value {L m q : ℕ} (layout : RowIndexing.GoodIndexStore L m)
    (data : StoredRightMatrix L m q) (h : InnerIndex m) (col : OuterIndex L m) (r : Fin q) :
    (originalRightReader layout data h col r).value = readRightMatrix data h col r := by
  rw [originalRightReader, RowIndexing.readOriginalRightProgram_value]
  simp only [Nat.zero_mul, Nat.zero_add, tileWidth,
    (RowIndexing.rowEquiv L m col).isLt, dite_true]
  rfl



#print axioms ThinMatrix.ThinMatrixBackend.originalLeftReader_value
#print axioms ThinMatrix.ThinMatrixBackend.originalRightReader_value

section OriginalInputAdapter
open SourceFormation

def readGoodSet {L : ℕ} (good : GoodStore L) (Q : Finset (Fin L)) : Bool :=
  tableRead 2 L good (cubeKey (setBits Q))

lemma sourceEnvironment_goodSet (L m : ℕ) (Q : Finset (Fin L)) :
    readGoodSet (sourceEnvironment L m).good Q = decide (Q ∈ goodSlots L m) := by
  unfold readGoodSet sourceEnvironment prepareGood
  rw [tableRead_build, keyCube_cubeKey, goodMaskProgram_correct, maskSlots_goodMasks,
    cubeSupport_setBits]

def complementList {L : ℕ} (Q : Finset (Fin L)) : List (Fin L) :=
  (List.finRange L).filter (fun i => decide (i ∉ Q))

lemma complementList_sort {L : ℕ} (Q : Finset (Fin L)) :
    Qᶜ.sort = complementList Q := by
  apply (Finset.sortedLT_sort Qᶜ).eq_of_mem_iff
    (List.Pairwise.sortedLT (List.Pairwise.filter _
      (List.sortedLT_iff_pairwise.mp (List.sortedLT_finRange L))))
  intro i
  simp

lemma complementList_length {L m : ℕ} (Q : Finset (Fin L)) (hQ : Q.card = m) :
    (complementList Q).length = L-m := by
  rw [← complementList_sort, Finset.length_sort, outsideCard Q hQ]

def outsidePositionArray {L m : ℕ} (Q : Finset (Fin L)) (hQ : Q.card = m) : Vector (Fin L) (L-m) :=
  ⟨(complementList Q).toArray, by rw [List.size_toArray, complementList_length Q hQ]⟩

lemma outsidePositionArray_get {L m : ℕ} (Q : Finset (Fin L)) (hQ : Q.card = m) (j : Fin (L-m)) :
    (outsidePositionArray Q hQ).get j = outsideEmbedding Q hQ j := by
  rw [outsideEmbedding, Finset.orderEmbOfFin_apply]
  unfold outsidePositionArray
  simp only [Vector.get, Fin.val_cast, List.getElem_toArray]
  simp only [complementList_sort, Fin.getElem_fin]

def compressOutsideProgram {L m : ℕ} (Q : Finset (Fin L)) (hQ : Q.card = m) (bits : Cube L) :
    Program (Vector Bool (L-m)) :=
  let positions := outsidePositionArray Q hQ
  ⟨Vector.ofFn (fun j => bits (positions.get j)), 16*(L+1)^2⟩

lemma compressOutsideProgram_value {L m : ℕ} (Q : Finset (Fin L)) (hQ : Q.card = m) (bits : Cube L) :
    asCube (compressOutsideProgram Q hQ bits).value = compressOutside Q hQ bits := by
  funext j
  simp only [asCube, compressOutsideProgram, Vector.get_ofFn, outsidePositionArray_get, compressOutside]

/-- Literal inverse coordinate program. Complement positions are materialized
once; each physical coordinate scans that stored list for its binary position
and reads the corresponding stored bit, with false as the missing default.
No order isomorphism is executed. -/
def expandOutsideVector {L m : ℕ} (Q : Finset (Fin L)) (hQ : Q.card=m)
    (bits : Cube (L-m)) : Vector Bool L :=
  let positions := outsidePositionArray Q hQ
  let bitsVector := Vector.ofFn bits
  Vector.ofFn (fun i => bitsVector.toArray.getD (positions.toList.idxOf i) false)

lemma outsidePositionArray_toList {L m : ℕ} (Q : Finset (Fin L)) (hQ : Q.card=m) :
    (outsidePositionArray Q hQ).toList = complementList Q := by
  simp [outsidePositionArray]

lemma outsidePositionArray_nodup {L m : ℕ} (Q : Finset (Fin L)) (hQ : Q.card=m) :
    (outsidePositionArray Q hQ).toList.Nodup := by
  rw [outsidePositionArray_toList]
  exact (List.nodup_finRange L).filter _

lemma outsidePositionArray_idxOf {L m : ℕ} (Q : Finset (Fin L)) (hQ : Q.card=m)
    (j : Fin (L-m)) :
    (outsidePositionArray Q hQ).toList.idxOf (outsideEmbedding Q hQ j) = j.val := by
  have hj : j.val < (outsidePositionArray Q hQ).toList.length := by simp
  have hg : (outsidePositionArray Q hQ).toList[j.val] = outsideEmbedding Q hQ j := by
    rw [Vector.getElem_toList]
    exact outsidePositionArray_get Q hQ j
  rw [← hg]
  exact (outsidePositionArray_nodup Q hQ).idxOf_getElem j.val hj

@[simp] theorem expandOutsideVector_at {L m : ℕ} (Q : Finset (Fin L)) (hQ : Q.card=m)
    (bits : Cube (L-m)) (j : Fin (L-m)) :
    (expandOutsideVector Q hQ bits).get (outsideEmbedding Q hQ j) = bits j := by
  simp only [expandOutsideVector,Vector.get_ofFn]
  rw [outsidePositionArray_idxOf Q hQ j]
  simp [Array.getD,j.isLt]

@[simp] theorem expandOutsideVector_on {L m : ℕ} (Q : Finset (Fin L)) (hQ : Q.card=m)
    (bits : Cube (L-m)) (i : Fin L) (hi : i ∈ Q) :
    (expandOutsideVector Q hQ bits).get i = false := by
  have hn : i ∉ (outsidePositionArray Q hQ).toList := by
    rw [outsidePositionArray_toList]
    simp [complementList,hi]
  simp only [expandOutsideVector,Vector.get_ofFn]
  rw [List.idxOf_eq_length hn]
  simp [Array.getD]

/-- Correctness against the semantic order-isomorphism specification. The
isomorphism occurs only in this proof's surjectivity argument. -/
theorem expandOutsideVector_get {L m : ℕ} (Q : Finset (Fin L)) (hQ : Q.card=m)
    (bits : Cube (L-m)) (i : Fin L) :
    (expandOutsideVector Q hQ bits).get i = expandOutside Q hQ bits i := by
  by_cases hi : i ∈ Q
  · rw [expandOutsideVector_on Q hQ bits i hi,expandOutside_on Q hQ bits i hi]
  · have hc : i ∈ Qᶜ := by simpa using hi
    let j : Fin (L-m) := (Qᶜ.orderIsoOfFin (outsideCard Q hQ)).symm ⟨i,hc⟩
    have hj : outsideEmbedding Q hQ j = i := by
      change ((Qᶜ.orderIsoOfFin (outsideCard Q hQ)) j).val = i
      simp [j]
    rw [← hj,expandOutsideVector_at,expandOutside_at]

theorem expandOutsideVector_value {L m : ℕ} (Q : Finset (Fin L)) (hQ : Q.card=m)
    (bits : Cube (L-m)) : asCube (expandOutsideVector Q hQ bits) = expandOutside Q hQ bits := by
  funext i
  exact expandOutsideVector_get Q hQ bits i


/-- Only the prepared good-mask byte is tested. A successful entry reads
the original backing array by the proved compact row/middle program. -/
noncomputable def storedRawLeftReader {L m q : ℕ}
    (good : GoodStore L) (hg : ∀ Q, readGoodSet good Q = decide (Q ∈ goodSlots L m))
    (layout : RowIndexing.GoodIndexStore L m) (data : StoredLeftMatrix L m q) : LeftRead L m (L-m) q :=
  fun Q bits outer h1 h2 r =>
    if hb : readGoodSet good Q = true then
      let hQ : Q ∈ goodSlots L m := by rw [hg Q] at hb; exact of_decide_eq_true hb
      let compressed := compressOutsideProgram Q (goodSlots_size L m Q hQ) bits
      let read := originalLeftReader layout data
        (⟨Q,hQ⟩,(asCube compressed.value,outer)) (h1,h2) r
      ⟨read.value, read.operations+compressed.operations+100*(L+m+1)^3⟩
    else ⟨0,100*(L+m+1)^3⟩

noncomputable def storedRawRightReader {L m q : ℕ}
    (good : GoodStore L) (hg : ∀ Q, readGoodSet good Q = decide (Q ∈ goodSlots L m))
    (layout : RowIndexing.GoodIndexStore L m) (data : StoredRightMatrix L m q) : RightRead L m (L-m) q :=
  fun Q bits h1 h2 outer r =>
    if hb : readGoodSet good Q = true then
      let hQ : Q ∈ goodSlots L m := by rw [hg Q] at hb; exact of_decide_eq_true hb
      let compressed := compressOutsideProgram Q (goodSlots_size L m Q hQ) bits
      let read := originalRightReader layout data (h1,h2)
        (⟨Q,hQ⟩,(asCube compressed.value,outer)) r
      ⟨read.value, read.operations+compressed.operations+100*(L+m+1)^3⟩
    else ⟨0,100*(L+m+1)^3⟩

lemma storedRawLeftReader_value {L m q : ℕ} [NeZero q]
    (good : GoodStore L) (hg : ∀ Q, readGoodSet good Q = decide (Q ∈ goodSlots L m))
    (layout : RowIndexing.GoodIndexStore L m) (data : StoredLeftMatrix L m q)
    (Q : Finset (Fin L)) (bits : Cube L) (outer : Cube (L-m)) (h1 h2 : Cube m) (r : Fin q) :
    (storedRawLeftReader good hg layout data Q bits outer h1 h2 r).value =
      rawLeft (readLeftMatrix data) Q bits outer h1 h2 r := by
  unfold storedRawLeftReader rawLeft
  by_cases hQ : Q ∈ goodSlots L m
  · have hb : readGoodSet good Q = true := by rw [hg Q]; simp [hQ]
    rw [dif_pos hb, dif_pos hQ]
    dsimp only
    rw [originalLeftReader_value, compressOutsideProgram_value]
  · have hb : readGoodSet good Q ≠ true := by rw [hg Q]; simp [hQ]
    rw [dif_neg hb, dif_neg hQ]
    rfl

lemma storedRawRightReader_value {L m q : ℕ} [NeZero q]
    (good : GoodStore L) (hg : ∀ Q, readGoodSet good Q = decide (Q ∈ goodSlots L m))
    (layout : RowIndexing.GoodIndexStore L m) (data : StoredRightMatrix L m q)
    (Q : Finset (Fin L)) (bits : Cube L) (h1 h2 : Cube m) (outer : Cube (L-m)) (r : Fin q) :
    (storedRawRightReader good hg layout data Q bits h1 h2 outer r).value =
      rawRight (readRightMatrix data) Q bits h1 h2 outer r := by
  unfold storedRawRightReader rawRight
  by_cases hQ : Q ∈ goodSlots L m
  · have hb : readGoodSet good Q = true := by rw [hg Q]; simp [hQ]
    rw [dif_pos hb, dif_pos hQ]
    dsimp only
    rw [originalRightReader_value, compressOutsideProgram_value]
  · have hb : readGoodSet good Q ≠ true := by rw [hg Q]; simp [hQ]
    rw [dif_neg hb, dif_neg hQ]
    rfl

noncomputable def buildLeftAdapter {L m q : ℕ} (read : LeftRead L m (L-m) q) : Program (InputStore L m q) :=
  tableBuild 2 L fun Q => tableBuild 2 L fun bits =>
    tableBuild 2 (L-m) fun outer => tableBuild 2 m fun h1 => tableBuild 2 m fun h2 =>
      vectorBuild q (fun r => read (cubeSupport (keyCube Q)) (keyCube bits)
        (keyCube outer) (keyCube h1) (keyCube h2) r)

noncomputable def buildRightAdapter {L m q : ℕ} (read : RightRead L m (L-m) q) : Program (InputStore L m q) :=
  tableBuild 2 L fun Q => tableBuild 2 L fun bits =>
    tableBuild 2 (L-m) fun outer => tableBuild 2 m fun h1 => tableBuild 2 m fun h2 =>
      vectorBuild q (fun r => read (cubeSupport (keyCube Q)) (keyCube bits)
        (keyCube h1) (keyCube h2) (keyCube outer) r)

lemma read_buildLeftAdapter {L m q : ℕ} (read : LeftRead L m (L-m) q)
    (Q : Finset (Fin L)) (bits : Cube L) (outer : Cube (L-m)) (h1 h2 : Cube m) (r : Fin q) :
    readInput (buildLeftAdapter read).value Q bits outer h1 h2 r =
      (read Q bits outer h1 h2 r).value := by
  unfold readInput buildLeftAdapter
  simp only [tableRead_build, keyCube_cubeKey, cubeSupport_setBits, vectorBuild_get]

lemma read_buildRightAdapter {L m q : ℕ} (read : RightRead L m (L-m) q)
    (Q : Finset (Fin L)) (bits : Cube L) (h1 h2 : Cube m) (outer : Cube (L-m)) (r : Fin q) :
    readInput (buildRightAdapter read).value Q bits outer h1 h2 r =
      (read Q bits h1 h2 outer r).value := by
  unfold readInput buildRightAdapter
  simp only [tableRead_build, keyCube_cubeKey, cubeSupport_setBits, vectorBuild_get]

end OriginalInputAdapter



#print axioms ThinMatrix.ThinMatrixBackend.storedRawLeftReader_value
#print axioms ThinMatrix.ThinMatrixBackend.storedRawRightReader_value

open SourceFormation

/-- Stored finite-field columns are converted once, coordinatewise. -/
def booleanColumns {L r : ℕ} (columns : GoodMapRuntime.Kernel.Columns L r) :
    Vector (Vector Bool r) L := columns.map (fun column => column.map boolF2Equiv.symm)

lemma booleanColumns_function {L r : ℕ} (columns : GoodMapRuntime.Kernel.Columns L r) :
    SourceFormation.columnFunction (booleanColumns columns) =
      boolColumns (GoodMapRuntime.Indexing.decodeColumns columns) := by
  funext i j
  simp only [SourceFormation.columnFunction,booleanColumns,Vector.get_map]
  rfl

def runtimeGoodMasks (L m : ℕ) : List (Cube L) :=
  (GoodMapRuntime.construct L m).good.map (fun Q => setBits Q.val)

lemma runtimeGoodMasks_slots (L m : ℕ) : maskSlots (runtimeGoodMasks L m) = goodSlots L m := by
  unfold maskSlots runtimeGoodMasks
  simp only [List.map_map,Function.comp_def,RowIndexing.cubeSupport_setBits]
  exact GoodMapRuntime.constructed_goodSlots L m

lemma runtimeGoodMasks_nodup (L m : ℕ) : (runtimeGoodMasks L m).Nodup := by
  apply (GoodMapRuntime.constructed_good_nodup L m).map
  intro Q P h
  apply Subtype.ext
  simpa only [RowIndexing.cubeSupport_setBits] using congrArg cubeSupport h

/-- The ascending compact index is prepared by scanning stored good bytes,
without rerunning any restriction or map-construction test. -/
def storedGoodCodes {L : ℕ} (good : GoodStore L) : List (Fin (2^L)) :=
  (List.finRange (2^L)).filter (fun code =>
    readGoodSet good (cubeSupport ((RowIndexing.cubeEquiv L).symm code)))

lemma storedGoodCodes_eq {L m : ℕ} (good : GoodStore L)
    (hg : ∀ Q, readGoodSet good Q = decide (Q ∈ goodSlots L m)) :
    storedGoodCodes good = RowIndexing.goodCodes L m := by
  unfold storedGoodCodes RowIndexing.goodCodes
  congr 1
  funext code
  exact hg _

def prepareStoredGoodIndex {L m : ℕ} (good : GoodStore L)
    (hg : ∀ Q, readGoodSet good Q = decide (Q ∈ goodSlots L m)) : RowIndexing.GoodIndexStore L m where
  codes := ⟨(storedGoodCodes good).toArray, by
    rw [List.size_toArray,storedGoodCodes_eq good hg,RowIndexing.goodCodes_length]⟩
  correct := by simpa using storedGoodCodes_eq good hg

/-- Shape data is prepared once and then shared by all row/column bands. -/
structure ShapePlan (L m : ℕ) where
  environment : SourceFormation.Environment L m (L-m)
  layout : RowIndexing.GoodIndexStore L m
  good : ∀ Q, readGoodSet environment.good Q = decide (Q ∈ goodSlots L m)
  gamma : environment.gamma = cubeMap (GoodSetConstruction.constructGoodMaps L m).1
  delta : environment.delta = cubeMap (GoodSetConstruction.constructGoodMaps L m).2
  deltaColumns_eq : SourceFormation.columnFunction environment.deltaColumns =
    boolColumns (GoodSetConstruction.constructGoodMaps L m).2
  width : ℕ
  width_eq : width = tileWidth L m
  operations : ℕ

noncomputable def prepareShape (L m : ℕ) : ShapePlan L m :=
  let setup := GoodMapRuntime.construct L m
  let masks := setup.good.map (fun Q => setBits Q.val)
  let good := SourceFormation.prepareGood masks
  let hg : ∀ Q, readGoodSet good.value Q = decide (Q ∈ goodSlots L m) := by
    intro Q
    change readGoodSet (SourceFormation.prepareGood masks).value Q = _
    simp only [readGoodSet,SourceFormation.prepareGood,SourceFormation.tableRead_build,
      SourceFormation.keyCube_cubeKey,SourceFormation.goodMaskProgram_correct,
      RowIndexing.cubeSupport_setBits]
    rw [show maskSlots masks = goodSlots L m from runtimeGoodMasks_slots L m]
  let hgamma : SourceFormation.columnFunction (booleanColumns setup.gamma) =
      boolColumns (GoodSetConstruction.constructGoodMaps L m).1 := by
    rw [booleanColumns_function]
    exact congrArg boolColumns (congrArg Prod.fst (GoodMapRuntime.constructedMaps_eq L m))
  let hdelta : SourceFormation.columnFunction (booleanColumns setup.delta) =
      boolColumns (GoodSetConstruction.constructGoodMaps L m).2 := by
    rw [booleanColumns_function]
    exact congrArg boolColumns (congrArg Prod.snd (GoodMapRuntime.constructedMaps_eq L m))
  let layout := prepareStoredGoodIndex good.value hg
  { environment := ⟨good.value,booleanColumns setup.gamma,booleanColumns setup.delta⟩
    layout := layout
    good := hg
    gamma := by change columnMap _ = _; rw [hgamma]; rfl
    delta := by change columnMap _ = _; rw [hdelta]; rfl
    deltaColumns_eq := hdelta
    width := layout.codes.toArray.size*4^(L-m)
    width_eq := by simp only [Vector.size_toArray]; rfl
    operations := setup.sites+good.operations+1000*(L+m+1)^5*4^L }

abbrev BandCache (L m q : ℕ) := CachedLowQuery.Prepared (2*L) q (2*m+1)

structure PreparedBandRun (L m q : ℕ) where
  source : SourceFormation.RawStore L q
  cache : BandCache L m q
  operations : ℕ

structure PreparedBand (L m q : ℕ) where
  environment : SourceFormation.Environment L m (L-m)
  input : InputStore L m q
  runs : Vector (PreparedBandRun L m q) (2*m+1)
  operations : ℕ

def sourceValue {L q : ℕ} (source : SourceFormation.RawStore L q) :
    SourceWord L → CyclicRing.Cyclic q := fun a r => SourceFormation.readRaw source a.1 a.2 r

noncomputable def prepareBandRun {L m t q : ℕ} [NeZero q] (side : Bool)
    (source : SourceFormation.Program (SourceFormation.RawStore L q)) : PreparedBandRun L m q :=
  let value := sourceValue source.value
  let cache := CacheDenseLowering.prepareSource (m := m) (t := t) (width := 2*m+1) side value
  { source := source.value
    cache := cache.1
    operations := source.operations + cache.2 }

noncomputable def prepareLeftBand {L m t q : ℕ} [NeZero q] (shape : ShapePlan L m)
    (data : StoredLeftMatrix L m q) : PreparedBand L m q :=
  let originalRead := storedRawLeftReader shape.environment.good shape.good shape.layout data
  let input := buildLeftAdapter originalRead
  let runs := Vector.ofFn (fun i : Fin (2*m+1) =>
    prepareBandRun (t := t) true (SourceFormation.formLeftSource shape.environment
      (leftInputReader input.value) (CachedLowQuery.sourceRun i)))
  { environment := shape.environment
    input := input.value
    runs := runs
    operations := input.operations + ∑ i, (runs.get i).operations }

noncomputable def prepareRightBand {L m t q : ℕ} [NeZero q] (shape : ShapePlan L m)
    (data : StoredRightMatrix L m q) : PreparedBand L m q :=
  let originalRead := storedRawRightReader shape.environment.good shape.good shape.layout data
  let input := buildRightAdapter originalRead
  let runs := Vector.ofFn (fun i : Fin (2*m+1) =>
    prepareBandRun (t := t) false (SourceFormation.formRightSource shape.environment
      (rightInputReader input.value) (CachedLowQuery.sourceRun i)))
  { environment := shape.environment
    input := input.value
    runs := runs
    operations := input.operations + ∑ i, (runs.get i).operations }

@[simp] lemma prepareLeftBand_environment {L m t q : ℕ} [NeZero q] (shape : ShapePlan L m)
    (data : StoredLeftMatrix L m q) : (prepareLeftBand (t := t) shape data).environment = shape.environment := rfl

@[simp] lemma prepareRightBand_environment {L m t q : ℕ} [NeZero q] (shape : ShapePlan L m)
    (data : StoredRightMatrix L m q) : (prepareRightBand (t := t) shape data).environment = shape.environment := rfl

lemma prepareLeftBand_source {L m t q : ℕ} [NeZero q] (shape : ShapePlan L m)
    (data : StoredLeftMatrix L m q) (i : Fin (2*m+1)) :
    sourceValue ((prepareLeftBand (t := t) shape data).runs.get i).source =
      fun a => rawLeftSource (rawLeft (readLeftMatrix data)) (goodSlots L m)
        (cubeMap (GoodSetConstruction.constructGoodMaps L m).1)
        (cubeMap (GoodSetConstruction.constructGoodMaps L m).2) (CachedLowQuery.sourceRun i) a.1 a.2 := by
  funext a r
  have hg (n : Fin L → NormalLetter) :
      SourceFormation.readGood shape.environment.good n = decide (normalSupport n ∈ goodSlots L m) := by
    have hb : setBits (normalSupport n) = (fun i => decide (normalIsP (n i))) := by
      funext i
      simp [setBits, normalSupport]
    simpa only [readGoodSet, SourceFormation.readGood, hb] using shape.good (normalSupport n)
  have h := SourceFormation.formLeftSource_correct shape.environment
    (leftInputReader (buildLeftAdapter (storedRawLeftReader shape.environment.good shape.good shape.layout data)).value)
    (rawLeft (readLeftMatrix data)) (goodSlots L m) hg
    (fun Q bits outer h1 h2 r => (read_buildLeftAdapter _ Q bits outer h1 h2 r).trans
      (storedRawLeftReader_value _ _ _ data Q bits outer h1 h2 r))
    (CachedLowQuery.sourceRun i) a.1 a.2 r
  simpa only [sourceValue, prepareLeftBand, Vector.get_ofFn, prepareBandRun, shape.gamma, shape.delta] using h

lemma prepareRightBand_source {L m t q : ℕ} [NeZero q] (shape : ShapePlan L m)
    (data : StoredRightMatrix L m q) (i : Fin (2*m+1)) :
    sourceValue ((prepareRightBand (t := t) shape data).runs.get i).source =
      fun a => rawRightSource (rawRight (readRightMatrix data)) (goodSlots L m)
        (cubeMap (GoodSetConstruction.constructGoodMaps L m).1)
        (cubeMap (GoodSetConstruction.constructGoodMaps L m).2) (CachedLowQuery.sourceRun i) a.1 a.2 := by
  funext a r
  have hg (n : Fin L → NormalLetter) :
      SourceFormation.readGood shape.environment.good n = decide (normalSupport n ∈ goodSlots L m) := by
    have hb : setBits (normalSupport n) = (fun i => decide (normalIsP (n i))) := by
      funext i
      simp [setBits, normalSupport]
    simpa only [readGoodSet, SourceFormation.readGood, hb] using shape.good (normalSupport n)
  have h := SourceFormation.formRightSource_correct shape.environment
    (rightInputReader (buildRightAdapter (storedRawRightReader shape.environment.good shape.good shape.layout data)).value)
    (rawRight (readRightMatrix data)) (goodSlots L m) hg
    (fun Q bits h1 h2 outer r => (read_buildRightAdapter _ Q bits h1 h2 outer r).trans
      (storedRawRightReader_value _ _ _ data Q bits h1 h2 outer r))
    (CachedLowQuery.sourceRun i) a.1 a.2 r
  simpa only [sourceValue, prepareRightBand, Vector.get_ofFn, prepareBandRun, shape.gamma, shape.delta] using h



#print axioms ThinMatrix.ThinMatrixBackend.prepareLeftBand_source
#print axioms ThinMatrix.ThinMatrixBackend.prepareRightBand_source

lemma prepareLeftBand_cache {L m t q : ℕ} [NeZero q] (shape : ShapePlan L m)
    (data : StoredLeftMatrix L m q) (i : Fin (2*m+1)) :
    ((prepareLeftBand (t := t) shape data).runs.get i).cache =
      (CacheDenseLowering.prepareSource (m := m) (t := t) (width := 2*m+1) true
        (sourceValue ((prepareLeftBand (t := t) shape data).runs.get i).source)).1 := by
  simp only [prepareLeftBand, Vector.get_ofFn, prepareBandRun]

lemma prepareRightBand_cache {L m t q : ℕ} [NeZero q] (shape : ShapePlan L m)
    (data : StoredRightMatrix L m q) (i : Fin (2*m+1)) :
    ((prepareRightBand (t := t) shape data).runs.get i).cache =
      (CacheDenseLowering.prepareSource (m := m) (t := t) (width := 2*m+1) false
        (sourceValue ((prepareRightBand (t := t) shape data).runs.get i).source)).1 := by
  simp only [prepareRightBand, Vector.get_ofFn, prepareBandRun]

/-- A tile stores HIGH once for each matching run. Its LOW tables belong
to the separate row/column bands and are not rebuilt here. -/
structure PreparedTile (L m t q : ℕ) where
  environment : SourceFormation.Environment L m (L-m)
  high : Vector (PreparedHigh L m t q) (2*m+1)
  operations : ℕ

noncomputable def prepareTile {L m t q : ℕ} [NeZero q] (M : FullMultiplier q)
    (left right : PreparedBand L m q) : PreparedTile L m t q :=
  let high := Vector.ofFn (fun i : Fin (2*m+1) => prepareHigh (m := m) (t := t) M
    (sourceValue (left.runs.get i).source) (sourceValue (right.runs.get i).source))
  { environment := left.environment
    high := high
    operations := ∑ i, (high.get i).operations }

@[simp] lemma prepareTile_environment {L m t q : ℕ} [NeZero q] (M : FullMultiplier q)
    (left right : PreparedBand L m q) : (prepareTile (t := t) M left right).environment = left.environment := rfl

@[simp] lemma prepareTile_high {L m t q : ℕ} [NeZero q] (M : FullMultiplier q)
    (left right : PreparedBand L m q) (i : Fin (2*m+1)) :
    (prepareTile (t := t) M left right).high.get i = prepareHigh (m := m) (t := t) M
      (sourceValue (left.runs.get i).source) (sourceValue (right.runs.get i).source) := by
  exact Vector.get_ofFn _ _

noncomputable def bandRunCaches {L m q : ℕ} (left right : PreparedBand L m q) :
    CachedLowQuery.RunCaches L m q (2*m+1) :=
  Vector.ofFn (fun i => ((left.runs.get i).cache, (right.runs.get i).cache))

lemma preparedBandRunCaches_valid {L m t q : ℕ} [NeZero q] (shape : ShapePlan L m)
    (left : StoredLeftMatrix L m q) (right : StoredRightMatrix L m q)
    (i : Fin (2*m+1)) :
    CachedLowQuery.SourceCacheValid (m := m) (t := t)
      (sourceValue ((prepareLeftBand (t := t) shape left).runs.get i).source)
      (sourceValue ((prepareRightBand (t := t) shape right).runs.get i).source)
      ((bandRunCaches (prepareLeftBand (t := t) shape left) (prepareRightBand (t := t) shape right)).get i) := by
  simp only [bandRunCaches, Vector.get_ofFn, prepareLeftBand_cache, prepareRightBand_cache]
  exact CacheDenseLowering.sourceCacheValid _ _

/-- The mathematical metadata reference is used only in refinement proofs. -/
noncomputable def queryGeometry (L m q : ℕ) [NeZero q] (row col : OuterIndex L m) :
    SourceQueryData L m (L-m) (CyclicRing.Cyclic q) := compactQuery 0 0 row col

open HighBoxDP

structure QueryMetadata (L m : ℕ) where
  embedding : Fin (2*m) ↪o Fin (2*L)
  outside : Fin (2*L) → Fin 4
  left_cap : ((embeddedSupport embedding).filter (fun i => i.val < L)).card ≤ m
  right_cap : ((embeddedSupport embedding).filter (fun i => L ≤ i.val)).card ≤ m

/-- Query locators read the captured Delta column arrays. Complement-bit
expansion is a literal stored-list scan, and both transpose products are
materialized by L Boolean dot loops before the source-cache/table reads. -/
noncomputable def storedQueryGeometry {L m : ℕ}
    (environment : SourceFormation.Environment L m (L-m)) (row col : OuterIndex L m) : QueryMetadata L m :=
  let hL := goodSlots_size L m row.1.val row.1.property
  let hR := goodSlots_size L m col.1.val col.1.property
  let iL := expandOutsideVector row.1.val hL row.2.1
  let iR := expandOutsideVector col.1.val hR col.2.1
  let jL := Vector.ofFn (fun i => dotBits (fun j => (environment.deltaColumns.get i).get j) col.2.2)
  let jR := Vector.ofFn (fun i => dotBits (fun j => (environment.deltaColumns.get i).get j) row.2.2)
  let outside := Vector.ofFn (sourceOutside iL.get iR.get jL.get jR.get)
  { embedding := physicalEmbedding row.1.val col.1.val hL hR
    outside := outside.get
    left_cap := by rw [physicalEmbedding_support,physicalSupport_left_card row.1.val col.1.val hL]
    right_cap := by rw [physicalEmbedding_support,physicalSupport_right_card row.1.val col.1.val hR] }

lemma storedQueryGeometry_embedding {L m q : ℕ} [NeZero q]
    (environment : SourceFormation.Environment L m (L-m)) (row col : OuterIndex L m) :
    (storedQueryGeometry environment row col).embedding = (queryGeometry L m q row col).embedding := rfl

lemma storedQueryGeometry_outside {L m q : ℕ} [NeZero q]
    (shape : ShapePlan L m) (row col : OuterIndex L m) :
    (storedQueryGeometry shape.environment row col).outside = (queryGeometry L m q row col).outside := by
  have hcolumns := shape.deltaColumns_eq
  change (fun i j => (shape.environment.deltaColumns.get i).get j) = _ at hcolumns
  unfold storedQueryGeometry
  dsimp only
  have hL : (expandOutsideVector row.1.val (goodSlots_size L m row.1.val row.1.property) row.2.1).get =
      expandOutside row.1.val (goodSlots_size L m row.1.val row.1.property) row.2.1 := by
    funext i; exact expandOutsideVector_get _ _ _ i
  have hR : (expandOutsideVector col.1.val (goodSlots_size L m col.1.val col.1.property) col.2.1).get =
      expandOutside col.1.val (goodSlots_size L m col.1.val col.1.property) col.2.1 := by
    funext i; exact expandOutsideVector_get _ _ _ i
  have hJL : (Vector.ofFn (fun i => dotBits (fun j => (shape.environment.deltaColumns.get i).get j) col.2.2)).get =
      transposeMap (boolColumns (GoodSetConstruction.constructGoodMaps L m).2) col.2.2 := by
    funext i
    simp only [Vector.get_ofFn,transposeMap]
    rw [congrFun hcolumns i]
  have hJR : (Vector.ofFn (fun i => dotBits (fun j => (shape.environment.deltaColumns.get i).get j) row.2.2)).get =
      transposeMap (boolColumns (GoodSetConstruction.constructGoodMaps L m).2) row.2.2 := by
    funext i
    simp only [Vector.get_ofFn,transposeMap]
    rw [congrFun hcolumns i]
  rw [hL,hR,hJL,hJR]
  funext i
  exact Vector.get_ofFn _ _

noncomputable def queryLowFromBands {L m t q : ℕ} [NeZero q]
    (left right : PreparedBand L m q) (row col : OuterIndex L m) (r : Fin q) : ℤ × ℕ :=
  let d := storedQueryGeometry left.environment row col
  CachedLowQuery.queryLowRuns t (Vector.ofFn d.embedding) (Vector.ofFn d.outside)
    (bandRunCaches left right) r

noncomputable def queryHighFromTile {L m t q : ℕ} [NeZero q]
    (tile : PreparedTile L m t q) (row col : OuterIndex L m) (r : Fin q) : ℤ × ℕ :=
  let d := storedQueryGeometry tile.environment row col
  let rows := (List.finRange (2*m+1)).map (fun i =>
    queryHigh rfl d.embedding d.outside d.left_cap d.right_cap (tile.high.get i) r)
  ((rows.map Prod.fst).sum, (rows.map Prod.snd).sum)

lemma queryLowFromBands_correct {L m t q : ℕ} [NeZero q]
    (shape : ShapePlan L m) (hm : m ≤ L) (ht : t ≤ 2*m)
    (left : StoredLeftMatrix L m q) (right : StoredRightMatrix L m q)
    (row col : OuterIndex L m) (r : Fin q) :
    (queryLowFromBands (t := t) (prepareLeftBand (t := t) shape left)
      (prepareRightBand (t := t) shape right) row col r).1 =
      (compactQuery (readLeftMatrix left) (readRightMatrix right) row col).residual t r := by
  let d := compactQuery (readLeftMatrix left) (readRightMatrix right) row col
  have hv (i : Fin (2*m+1)) : CachedLowQuery.SourceCacheValid (m := m) (t := t)
      (d.leftRun (CachedLowQuery.sourceRun i)) (d.rightRun (CachedLowQuery.sourceRun i))
      ((bandRunCaches (prepareLeftBand (t := t) shape left)
        (prepareRightBand (t := t) shape right)).get i) := by
    have h := preparedBandRunCaches_valid (t := t) shape left right i
    rw [prepareLeftBand_source, prepareRightBand_source] at h
    exact h
  have h := CachedLowQuery.queryLowRuns_contract_of_valid d (Vector.ofFn d.embedding) (Vector.ofFn d.outside)
    (fun _ => Vector.get_ofFn _ _) (fun _ => Vector.get_ofFn _ _)
    (bandRunCaches (prepareLeftBand (t := t) shape left) (prepareRightBand (t := t) shape right))
    hv (by omega) ht hm (by omega) r
  unfold queryLowFromBands
  rw [prepareLeftBand_environment]
  dsimp only
  rw [storedQueryGeometry_outside (q := q)]
  exact h.1

lemma queryHighFromTile_correct {L m t q : ℕ} [NeZero q] (M : FullMultiplier q)
    (shape : ShapePlan L m) (left : StoredLeftMatrix L m q) (right : StoredRightMatrix L m q)
    (row col : OuterIndex L m) (r : Fin q) :
    (queryHighFromTile (prepareTile (t := t) M (prepareLeftBand (t := t) shape left)
      (prepareRightBand (t := t) shape right)) row col r).1 =
      (compactQuery (readLeftMatrix left) (readRightMatrix right) row col).high t r := by
  let d := compactQuery (readLeftMatrix left) (readRightMatrix right) row col
  unfold queryHighFromTile
  simp only [prepareTile_environment,prepareLeftBand_environment]
  rw [storedQueryGeometry_outside (q := q)]
  simp only [List.map_map,Function.comp_def,prepareTile_high]
  simp_rw [queryHigh_correct, prepareLeftBand_source, prepareRightBand_source]
  change ((List.finRange (2*m+1)).map (fun i => d.highRun t (CachedLowQuery.sourceRun i) r)).sum = _
  rw [← List.ofFn_eq_map, List.sum_ofFn]
  exact (CachedLowQuery.sum_sourceRun (m := m) (fun run => d.highRun t run r)).trans
    (CyclicRing.sum_coeff _ _ r).symm

noncomputable def queryTile {L m t q : ℕ} [NeZero q]
    (left right : PreparedBand L m q) (tile : PreparedTile L m t q)
    (row col : OuterIndex L m) (r : Fin q) : ℤ × ℕ :=
  let low := queryLowFromBands (t := t) left right row col r
  let high := queryHighFromTile tile row col r
  let decode := IntegerArithmetic.binaryExactDivCounted (4^L) (low.1+high.1)
  (decode.1, low.2+high.2+decode.2+1000*(L+m+1)^5)

lemma queryTile_correct {L m t q : ℕ} [NeZero q] (M : FullMultiplier q)
    (shape : ShapePlan L m) (hm : m ≤ L) (ht : t ≤ 2*m)
    (left : StoredLeftMatrix L m q) (right : StoredRightMatrix L m q)
    (row col : OuterIndex L m) (r : Fin q) :
    (queryTile (prepareLeftBand (t := t) shape left) (prepareRightBand (t := t) shape right)
      (prepareTile (t := t) M (prepareLeftBand (t := t) shape left)
        (prepareRightBand (t := t) shape right)) row col r).1 =
      (readLeftMatrix left * readRightMatrix right) row col r := by
  unfold queryTile
  simp only [queryLowFromBands_correct shape hm ht, queryHighFromTile_correct]
  apply IntegerArithmetic.binaryExactDivCounted_exact _ _ _ (by positivity)
  have h := congrFun (compactQuery_numerator t hm ht (readLeftMatrix left) (readRightMatrix right) row col) r
  have hc : ((4 : CyclicRing.Cyclic q)^L *
      (readLeftMatrix left * readRightMatrix right) row col) r =
      ((4^L : ℕ) : ℤ) * (readLeftMatrix left * readRightMatrix right) row col r := by
    simpa only [Int.cast_pow, Int.cast_ofNat, Nat.cast_pow, Nat.cast_ofNat] using
      CyclicRing.intCast_mul_coeff ((4:ℤ)^L) ((readLeftMatrix left * readRightMatrix right) row col) r
  simpa only [SourceQueryData.numerator, CyclicRing.add_coeff, hc] using h



#print axioms ThinMatrix.ThinMatrixBackend.preparedBandRunCaches_valid
#print axioms ThinMatrix.ThinMatrixBackend.queryTile_correct

section GlobalMatrices

abbrev OriginalLeft (N D q : ℕ) := Vector (Vector ℤ q) (N*D)
abbrev OriginalRight (N D q : ℕ) := Vector (Vector ℤ q) (D*N)

def originalLeftMatrix {N D q : ℕ} (A : OriginalLeft N D q) : Matrix (Fin N) (Fin D) (CyclicRing.Cyclic q) :=
  fun i h r => (A.get (finProdFinEquiv (i,h))).get r

def originalRightMatrix {N D q : ℕ} (B : OriginalRight N D q) : Matrix (Fin D) (Fin N) (CyclicRing.Cyclic q) :=
  fun h j r => (B.get (finProdFinEquiv (h,j))).get r

noncomputable def padMiddleLeft {N D m : ℕ}
    (A : Matrix (Fin N) (Fin D) R) : Matrix (Fin N) (InnerIndex m) R :=
  fun i h => if hh : (middleEquiv m h).val < D then A i ⟨(middleEquiv m h).val,hh⟩ else 0

noncomputable def padMiddleRight {N D m : ℕ}
    (B : Matrix (Fin D) (Fin N) R) : Matrix (InnerIndex m) (Fin N) R :=
  fun h j => if hh : (middleEquiv m h).val < D then B ⟨(middleEquiv m h).val,hh⟩ j else 0

lemma sum_fin_prefix {S : Type*} [AddCommMonoid S] (D r : ℕ) (f : Fin D → S) :
    (∑ i : Fin (D+r), if hi : i.val < D then f ⟨i.val,hi⟩ else 0) = ∑ i, f i := by
  induction r with
  | zero => simp
  | succ r ih =>
    change (∑ i : Fin (D+r+1), if hi : i.val < D then f ⟨i.val,hi⟩ else 0) = _
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [dif_neg (by omega : ¬ D+r < D), add_zero]
    exact ih

lemma padMiddle_product {N D m : ℕ} (hD : D ≤ 4^m)
    (A : Matrix (Fin N) (Fin D) R) (B : Matrix (Fin D) (Fin N) R) :
    padMiddleLeft (m := m) A * padMiddleRight (m := m) B = A*B := by
  funext i j
  simp only [Matrix.mul_apply]
  unfold padMiddleLeft padMiddleRight
  simp_rw [apply_dite₂ (fun x y : R => x*y)]
  simp only [zero_mul]
  rw [← (middleEquiv m).symm.sum_comp]
  simp only [Equiv.apply_symm_apply]
  have hprefix : ∀ M : ℕ, D ≤ M →
      (∑ h : Fin M, if hh : h.val < D then A i ⟨h.val,hh⟩ * B ⟨h.val,hh⟩ j else 0) =
        ∑ h : Fin D, A i h * B h j := by
    intro M hDM
    obtain ⟨r,rfl⟩ := Nat.exists_eq_add_of_le hDM
    exact sum_fin_prefix D r (fun h => A i h * B h j)
  exact hprefix (4^m) hD

/-- Contiguous copying into a padded band does no source-row rank search.
It uses the original flat array address and keeps complete coefficient vectors. -/
def makeLeftBand {N D L m q : ℕ} (A : OriginalLeft N D q)
    (b : Fin (TilingCosts.bandCount N (tileWidth L m))) : StoredLeftMatrix L m q :=
  Vector.ofFn fun address =>
    let pair := (finProdFinEquiv : Fin (tileWidth L m) × Fin (4^m) ≃ _).symm address
    let v := b.val*tileWidth L m + pair.1.val
    if hv : v < N then
      if hh : pair.2.val < D then A.get (finProdFinEquiv (⟨v,hv⟩,⟨pair.2.val,hh⟩))
      else Vector.replicate q 0
    else Vector.replicate q 0

def makeRightBand {N D L m q : ℕ} (B : OriginalRight N D q)
    (b : Fin (TilingCosts.bandCount N (tileWidth L m))) : StoredRightMatrix L m q :=
  Vector.ofFn fun address =>
    let pair := (finProdFinEquiv : Fin (4^m) × Fin (tileWidth L m) ≃ _).symm address
    let v := b.val*tileWidth L m + pair.2.val
    if hv : v < N then
      if hh : pair.1.val < D then B.get (finProdFinEquiv (⟨pair.1.val,hh⟩,⟨v,hv⟩))
      else Vector.replicate q 0
    else Vector.replicate q 0

lemma makeLeftBand_value {N D L m q : ℕ} [NeZero q] (A : OriginalLeft N D q)
    (b : Fin (TilingCosts.bandCount N (tileWidth L m))) :
    readLeftMatrix (makeLeftBand (L := L) (m := m) A b) =
      rowBand (padMiddleLeft (m := m) (originalLeftMatrix A)) b := by
  funext row h r
  simp only [readLeftMatrix, makeLeftBand, Vector.get_ofFn, Equiv.symm_apply_apply,
    rowBand, padMiddleLeft]
  by_cases hv : b.val*tileWidth L m + (rowEquiv L m row).val < N
  · by_cases hh : (middleEquiv m h).val < D
    · simp only [dif_pos hv, dif_pos hh]
      rfl
    · simp only [dif_pos hv, dif_neg hh, CyclicRing.zero_coeff, Vector.get_replicate]
  · simp only [dif_neg hv, CyclicRing.zero_coeff, Vector.get_replicate]

lemma makeRightBand_value {N D L m q : ℕ} [NeZero q] (B : OriginalRight N D q)
    (b : Fin (TilingCosts.bandCount N (tileWidth L m))) :
    readRightMatrix (makeRightBand (L := L) (m := m) B b) =
      columnBand (padMiddleRight (m := m) (originalRightMatrix B)) b := by
  funext h col r
  simp only [readRightMatrix, makeRightBand, Vector.get_ofFn, Equiv.symm_apply_apply,
    columnBand, padMiddleRight]
  by_cases hv : b.val*tileWidth L m + (rowEquiv L m col).val < N
  · by_cases hh : (middleEquiv m h).val < D
    · simp only [dif_pos hv, dif_pos hh]
      rfl
    · simp only [dif_pos hv, dif_neg hh, CyclicRing.zero_coeff, Vector.get_replicate]
  · simp only [dif_neg hv, CyclicRing.zero_coeff, Vector.get_replicate]

structure PreparedGlobal (N D L m t q : ℕ) where
  shape : ShapePlan L m
  left : Vector (PreparedBand L m q) (TilingCosts.bandCount N (tileWidth L m))
  right : Vector (PreparedBand L m q) (TilingCosts.bandCount N (tileWidth L m))
  tiles : Vector (Vector (PreparedTile L m t q) (TilingCosts.bandCount N (tileWidth L m)))
    (TilingCosts.bandCount N (tileWidth L m))
  operations : ℕ

/-- Padded copies allocate by the stored width, not a reference cardinality. -/
def makeLeftBandRuntime {N D m q : ℕ} (width : ℕ) (A : OriginalLeft N D q) (band : ℕ) :
    Vector (Vector ℤ q) (width*4^m) :=
  Vector.ofFn fun address =>
    let pair := (finProdFinEquiv : Fin width × Fin (4^m) ≃ _).symm address
    let v := band*width+pair.1.val
    if hv : v < N then
      if hh : pair.2.val < D then A.get (finProdFinEquiv (⟨v,hv⟩,⟨pair.2.val,hh⟩))
      else Vector.replicate q 0
    else Vector.replicate q 0

def makeRightBandRuntime {N D m q : ℕ} (width : ℕ) (B : OriginalRight N D q) (band : ℕ) :
    Vector (Vector ℤ q) (4^m*width) :=
  Vector.ofFn fun address =>
    let pair := (finProdFinEquiv : Fin (4^m) × Fin width ≃ _).symm address
    let v := band*width+pair.2.val
    if hv : v < N then
      if hh : pair.1.val < D then B.get (finProdFinEquiv (⟨pair.1.val,hh⟩,⟨v,hv⟩))
      else Vector.replicate q 0
    else Vector.replicate q 0

def makeLeftBandStored {N D L m q : ℕ} (shape : ShapePlan L m) (A : OriginalLeft N D q) (band : ℕ) :
    StoredLeftMatrix L m q := Vector.cast (congrArg (fun w => w*4^m) shape.width_eq)
      (makeLeftBandRuntime shape.width A band)

def makeRightBandStored {N D L m q : ℕ} (shape : ShapePlan L m) (B : OriginalRight N D q) (band : ℕ) :
    StoredRightMatrix L m q := Vector.cast (congrArg (fun w => 4^m*w) shape.width_eq)
      (makeRightBandRuntime shape.width B band)

lemma makeLeftBandStored_refines {N D L m q : ℕ} (shape : ShapePlan L m) (A : OriginalLeft N D q)
    (band : Fin (TilingCosts.bandCount N (tileWidth L m))) :
    makeLeftBandStored shape A band.val = makeLeftBand A band := by
  have hh (width : ℕ) (hwidth : width = tileWidth L m) :
      Vector.cast (congrArg (fun w => w*4^m) hwidth) (makeLeftBandRuntime width A band.val) =
        makeLeftBand A band := by
    subst width
    rfl
  exact hh shape.width shape.width_eq

lemma makeRightBandStored_refines {N D L m q : ℕ} (shape : ShapePlan L m) (B : OriginalRight N D q)
    (band : Fin (TilingCosts.bandCount N (tileWidth L m))) :
    makeRightBandStored shape B band.val = makeRightBand B band := by
  have hh (width : ℕ) (hwidth : width = tileWidth L m) :
      Vector.cast (congrArg (fun w => 4^m*w) hwidth) (makeRightBandRuntime width B band.val) =
        makeRightBand B band := by
    subst width
    rfl
  exact hh shape.width shape.width_eq

/-- All source and LOW encoders are formed before the tile loop. Each
input band is encoded once, and each tile stores only its HIGH preparation. -/
noncomputable def prepareGlobalShapeReference {N D L m t q : ℕ} [NeZero q]
    (shape : ShapePlan L m) (M : FullMultiplier q)
    (A : OriginalLeft N D q) (B : OriginalRight N D q) : PreparedGlobal N D L m t q :=
  let leftData := Vector.ofFn (fun b => makeLeftBand (L := L) (m := m) A b)
  let rightData := Vector.ofFn (fun b => makeRightBand (L := L) (m := m) B b)
  let left := leftData.map (prepareLeftBand (t := t) shape)
  let right := rightData.map (prepareRightBand (t := t) shape)
  let tiles := Vector.ofFn (fun b => Vector.ofFn (fun c => prepareTile (t := t) M (left.get b) (right.get c)))
  { shape := shape
    left := left
    right := right
    tiles := tiles
    operations := shape.operations + 20*q*TilingCosts.bandCount N (tileWidth L m)*tileWidth L m*4^m +
      (∑ b, (left.get b).operations) + (∑ c, (right.get c).operations) +
      ∑ b, ∑ c, ((tiles.get b).get c).operations }

/-- Every allocation and grid stride reads the cached physical width.
Casts transport index proofs and do not reconstruct the good family. -/
noncomputable def prepareGlobalShape {N D L m t q : ℕ} [NeZero q]
    (shape : ShapePlan L m) (M : FullMultiplier q)
    (A : OriginalLeft N D q) (B : OriginalRight N D q) : PreparedGlobal N D L m t q :=
  let bands := TilingCosts.bandCount N shape.width
  let hbands : bands = TilingCosts.bandCount N (tileWidth L m) := congrArg (TilingCosts.bandCount N) shape.width_eq
  let leftData := Vector.ofFn (n := bands) (fun b => makeLeftBandStored shape A b.val)
  let rightData := Vector.ofFn (n := bands) (fun b => makeRightBandStored shape B b.val)
  let left := leftData.map (prepareLeftBand (t := t) shape)
  let right := rightData.map (prepareRightBand (t := t) shape)
  let tiles := Vector.ofFn (n := bands) (fun b => Vector.ofFn (n := bands)
    (fun c => prepareTile (t := t) M (left.get b) (right.get c)))
  { shape := shape
    left := Vector.cast hbands left
    right := Vector.cast hbands right
    tiles := Vector.cast hbands (tiles.map (Vector.cast hbands))
    operations := shape.operations+20*q*bands*shape.width*4^m+
      (∑ b, (left.get b).operations)+(∑ c, (right.get c).operations)+
      ∑ b, ∑ c, ((tiles.get b).get c).operations }

lemma prepareGlobalShape_refines {N D L m t q : ℕ} [NeZero q]
    (shape : ShapePlan L m) (M : FullMultiplier q)
    (A : OriginalLeft N D q) (B : OriginalRight N D q) :
    prepareGlobalShape (t := t) shape M A B = prepareGlobalShapeReference shape M A B := by
  rcases shape with ⟨env,layout,hgood,hgamma,hdelta,hcols,width,hwidth,operations⟩
  subst width
  unfold prepareGlobalShape prepareGlobalShapeReference
  simp only [makeLeftBandStored_refines,makeRightBandStored_refines,Vector.cast_rfl]
  have hcast : (Vector.cast (rfl : TilingCosts.bandCount N (tileWidth L m) =
      TilingCosts.bandCount N (tileWidth L m)) :
      Vector (PreparedTile L m t q) (TilingCosts.bandCount N (tileWidth L m)) →
      Vector (PreparedTile L m t q) (TilingCosts.bandCount N (tileWidth L m))) = id := by
    funext v; rfl
  simp only [hcast,Vector.map_id_fun,id_eq]

noncomputable def prepareGlobalReference {N D L m t q : ℕ} [NeZero q] (M : FullMultiplier q)
    (A : OriginalLeft N D q) (B : OriginalRight N D q) : PreparedGlobal N D L m t q :=
  prepareGlobalShapeReference (prepareShape L m) M A B

noncomputable def prepareGlobal {N D L m t q : ℕ} [NeZero q] (M : FullMultiplier q)
    (A : OriginalLeft N D q) (B : OriginalRight N D q) : PreparedGlobal N D L m t q :=
  prepareGlobalShape (prepareShape L m) M A B

lemma prepareGlobal_refines {N D L m t q : ℕ} [NeZero q] (M : FullMultiplier q)
    (A : OriginalLeft N D q) (B : OriginalRight N D q) :
    prepareGlobal (L := L) (m := m) (t := t) M A B = prepareGlobalReference M A B :=
  prepareGlobalShape_refines _ _ _ _

/-- Division and remainder use the captured width; the casts change
only semantic Fin bounds. No reference good-family cardinality is evaluated. -/
def storedLocate {N L m : ℕ} (shape : ShapePlan L m) (hB : 0 < tileWidth L m) (i : Fin N) :
    Fin (TilingCosts.bandCount N (tileWidth L m)) × Fin (tileWidth L m) :=
  let hwidth : 0 < shape.width := by rw [shape.width_eq]; exact hB
  let located := TilingCosts.locate hwidth i
  (Fin.cast (congrArg (TilingCosts.bandCount N) shape.width_eq) located.1,
    Fin.cast shape.width_eq located.2)

lemma storedLocate_refines {N L m : ℕ} (shape : ShapePlan L m) (hB : 0 < tileWidth L m) (i : Fin N) :
    storedLocate shape hB i = TilingCosts.locate hB i := by
  rcases shape with ⟨env,layout,hgood,hgamma,hdelta,hcols,width,hwidth,operations⟩
  subst width
  rfl

noncomputable def queryGlobalReference {N D L m t q : ℕ} [NeZero q] (hB : 0 < tileWidth L m)
    (prepared : PreparedGlobal N D L m t q) (i j : Fin N) (r : Fin q) : ℤ × ℕ :=
  let bi := TilingCosts.locate hB i
  let bj := TilingCosts.locate hB j
  let row := RowIndexing.rowUnrank prepared.shape.layout bi.2
  let col := RowIndexing.rowUnrank prepared.shape.layout bj.2
  let result := queryTile (prepared.left.get bi.1) (prepared.right.get bj.1)
    ((prepared.tiles.get bi.1).get bj.1) row col r
  (result.1,result.2+1000*(L+m+N.log2+1)^5)

noncomputable def queryGlobal {N D L m t q : ℕ} [NeZero q] (hB : 0 < tileWidth L m)
    (prepared : PreparedGlobal N D L m t q) (i j : Fin N) (r : Fin q) : ℤ × ℕ :=
  let bi := storedLocate prepared.shape hB i
  let bj := storedLocate prepared.shape hB j
  let row := RowIndexing.rowUnrank prepared.shape.layout bi.2
  let col := RowIndexing.rowUnrank prepared.shape.layout bj.2
  let result := queryTile (prepared.left.get bi.1) (prepared.right.get bj.1)
    ((prepared.tiles.get bi.1).get bj.1) row col r
  (result.1,result.2+1000*(L+m+N.log2+1)^5)

lemma queryGlobal_refines {N D L m t q : ℕ} [NeZero q] (hB : 0 < tileWidth L m)
    (prepared : PreparedGlobal N D L m t q) (i j : Fin N) (r : Fin q) :
    queryGlobal hB prepared i j r = queryGlobalReference hB prepared i j r := by
  simp only [queryGlobal,storedLocate_refines]
  rfl

lemma queryGlobal_correct {N D L m t q : ℕ} [NeZero q] (M : FullMultiplier q)
    (hm : m ≤ L) (ht : t ≤ 2*m) (hD : D ≤ 4^m)
    (A : OriginalLeft N D q) (B : OriginalRight N D q) (i j : Fin N) (r : Fin q) :
    (queryGlobal (tileWidth_pos L m hm) (prepareGlobal (L := L) (m := m) (t := t) M A B) i j r).1 =
      (originalLeftMatrix A * originalRightMatrix B) i j r := by
  rw [queryGlobal_refines]
  unfold queryGlobalReference
  rw [prepareGlobal_refines]
  simp only [prepareGlobalReference,prepareGlobalShapeReference, Vector.get_map, Vector.get_ofFn, RowIndexing.rowUnrank_value]
  rw [queryTile_correct M _ hm ht, makeLeftBand_value, makeRightBand_value]
  change ((rowBand (padMiddleLeft (m := m) (originalLeftMatrix A))
    (TilingCosts.locate (tileWidth_pos L m hm) i).1 *
    columnBand (padMiddleRight (m := m) (originalRightMatrix B))
      (TilingCosts.locate (tileWidth_pos L m hm) j).1)
    (localRow (tileWidth_pos L m hm) i) (localRow (tileWidth_pos L m hm) j)) r = _
  rw [genuine_tile_product, padMiddle_product hD]

/-- The concrete array-FFT backend answers arbitrary selected cyclic
coefficients of the original, unpadded matrix product exactly. -/
lemma fft_queryGlobal_correct {N D L m t q : ℕ} [NeZero q]
    (hm : m ≤ L) (ht : t ≤ 2*m) (hD : D ≤ 4^m)
    (A : OriginalLeft N D q) (B : OriginalRight N D q) (i j : Fin N) (r : Fin q) :
    (queryGlobal (tileWidth_pos L m hm)
      (prepareGlobal (L := L) (m := m) (t := t) (fftFullMultiplier q) A B) i j r).1 =
      (originalLeftMatrix A * originalRightMatrix B) i j r :=
  queryGlobal_correct (fftFullMultiplier q) hm ht hD A B i j r

end GlobalMatrices

end ThinMatrix.ThinMatrixBackend

#print axioms ThinMatrix.ThinMatrixBackend.padMiddle_product
#print axioms ThinMatrix.ThinMatrixBackend.queryGlobal_correct
#print axioms ThinMatrix.ThinMatrixBackend.fft_queryGlobal_correct

#print axioms ThinMatrix.ThinMatrixBackend.queryHighBoxGenerated_refines
#print axioms ThinMatrix.ThinMatrixBackend.queryHigh_work
#print axioms ThinMatrix.ThinMatrixBackend.highKeyWork_bound
#print axioms ThinMatrix.ThinMatrixBackend.expandOutsideVector_value
#print axioms ThinMatrix.ThinMatrixBackend.runtimeGoodMasks_slots
#print axioms ThinMatrix.ThinMatrixBackend.storedGoodCodes_eq
#print axioms ThinMatrix.ThinMatrixBackend.storedQueryGeometry_outside
#print axioms ThinMatrix.ThinMatrixBackend.prepareGlobal_refines
#print axioms ThinMatrix.ThinMatrixBackend.queryGlobal_refines
