import CachedLowQuery

/-!
# Sparse coefficient-array realization of the retained LOW encoder

The executable payload is a nested vector of integer coefficients. Every
accepted child allocates its dense suffix array once and uses the thirteen
instruction sparse row program at each coefficient cell. No polynomial
multiplication, cyclic convolution, or polynomial representation is evaluated
by this program. Polynomial arrays occur only in the refinement proofs.

The counters count scalar reads/arithmetic/writes and cap scans. Integer bit
costs and machine addressing remain separate from these finite counters.
-/

namespace ThinMatrix.CacheDenseLowering

open CacheBounds CappedEnumeration SharedEncoder SparseLocalForms
open scoped BigOperators

abbrev Block (q width : ℕ) := DenseVector q width
abbrev Data (q width n : ℕ) (dims : Fin n → ℕ) :=
  SharedEncoder.Dense (R := Block q width) n dims
abbrev DataNode (q width N n : ℕ) (dims : Fin n → ℕ) :=
  SharedEncoder.Node (R := Block q width) N n dims
abbrev PolyData (q : ℕ) [NeZero q] (n : ℕ) (dims : Fin n → ℕ) :=
  SharedEncoder.Dense (R := Polynomial (CyclicRing.Cyclic q)) n dims

/-- Dense-array extensionality is a proof principle, not an executable scan. -/
theorem dense_ext {A : Type*} (n : ℕ) (dims : Fin n → ℕ)
    (a b : SharedEncoder.Dense (R := A) n dims)
    (h : ∀ x, SharedEncoder.read n dims a x = SharedEncoder.read n dims b x) : a = b := by
  induction n with
  | zero => exact h (fun i => Fin.elim0 i)
  | succ n ih =>
      apply Vector.ext
      intro i hi
      apply ih
      intro rest
      have hh := h (Fin.cons ⟨i,hi⟩ rest)
      simpa [SharedEncoder.read, Vector.get] using hh

theorem block_ext {q width : ℕ} (a b : Block q width)
    (h : ∀ d r, denseRead a d r = denseRead b d r) : a = b := by
  apply Vector.ext
  intro d hd
  apply Vector.ext
  intro r hr
  simpa [denseRead,Vector.get] using h ⟨d,hd⟩ ⟨r,hr⟩

/-- Proof-only projection of the first `width` polynomial coefficients. -/
noncomputable def lowerData {q width : ℕ} [NeZero q] (n : ℕ) (dims : Fin n → ℕ)
    (input : PolyData q n dims) : Data q width n dims :=
  SharedEncoder.materialize n dims (fun a => CachedLowQuery.extractedBlock
    (width := width) (SharedEncoder.read n dims input a))

@[simp] theorem read_lowerData {q width : ℕ} [NeZero q] (n : ℕ) (dims : Fin n → ℕ)
    (input : PolyData q n dims) (a : Coordinates dims) :
    SharedEncoder.read n dims (lowerData (width := width) n dims input) a =
      CachedLowQuery.extractedBlock (SharedEncoder.read n dims input a) := by
  exact SharedEncoder.read_materialize _ _ _ _

/-- Source orientation of a physical row. -/
def normalHere (L : ℕ) (side : Bool) (d : ℕ) : Bool :=
  decide ((d < L) = (side = true))

/-- Four stored reads, with the absent fourth opposite coordinate padded
by a shared literal zero block. -/
def gather {q width n : ℕ} (dims : Fin (n+1) → ℕ)
    (input : Data q width (n+1) dims) (zero : Block q width)
    (rest : Coordinates (fun i : Fin n => dims i.succ)) : Fin 4 → Block q width :=
  fun col => if hc : col.val < dims 0 then
    SharedEncoder.read (n+1) dims input (Fin.cons ⟨col.val,hc⟩ rest) else zero

/-- Each output suffix cell is materialized exactly once. The padding
block is formed once per accepted child, outside that materialization. -/
def contract {q width n : ℕ} (L : ℕ) (side : Bool) (d : ℕ) (row : Label)
    (dims : Fin (n+1) → ℕ) (input : Data q width (n+1) dims) :
    Data q width n (fun i => dims i.succ) :=
  let zero := CachedLowQuery.zeroBlock q width
  SharedEncoder.materialize n (fun i => dims i.succ) (fun rest =>
    denseLocalRow (normalHere L side d) row (gather dims input zero rest))

private theorem source_row {q : ℕ} [NeZero q] (L : ℕ) (side : Bool) (d N : ℕ)
    (hN : N = rawDim L side d) (row : Label)
    (children : Fin N → Polynomial (CyclicRing.Cyclic q)) :
    (∑ col, CachedLowIdentity.sourceCacheForms L side d row col.val * children col) =
      localPolynomial (normalHere L side d) row
        (fun col : Fin 4 => if hc : col.val < N then children ⟨col.val,hc⟩ else 0) := by
  by_cases hn : (d < L) = (side = true)
  · have hfour : N = 4 := by simpa [rawDim,hn] using hN
    clear hN
    subst N
    simp only [CachedLowIdentity.sourceCacheForms, hn, ↓reduceIte, Fin.isLt,
      normalHere, decide_true]
    simpa only [dite_true,Fin.eta] using CachedLowQuery.normal_cache_localPolynomial row children
  · have hthree : N = 3 := by simpa [rawDim,hn] using hN
    clear hN
    subst N
    simp only [CachedLowIdentity.sourceCacheForms, hn, ↓reduceIte, Fin.isLt,
      normalHere, decide_false]
    exact CachedLowQuery.opposite_cache_localPolynomial row children

/-- The actual sparse child preserves all retained polynomial coefficients.
The degree-one H row reads only the previous stored auxiliary degree. -/
theorem contract_refines {q width n : ℕ} [NeZero q]
    (L : ℕ) (side : Bool) (d : ℕ) (row : Label) (dims : Fin (n+1) → ℕ)
    (hdim : dims 0 = rawDim L side d) (input : PolyData q (n+1) dims) :
    contract L side d row dims (lowerData (width := width) (n+1) dims input) =
      lowerData n (fun i => dims i.succ)
        (SharedEncoder.contract dims (fun col => CachedLowIdentity.sourceCacheForms L side d row col.val) input) := by
  apply dense_ext
  intro rest
  rw [contract, SharedEncoder.read_materialize, read_lowerData, SharedEncoder.read_contract]
  apply block_ext
  intro degree residue
  rw [denseLocalRow_correct]
  have hg : (fun col => denseRead
      (gather dims (lowerData (width := width) (n+1) dims input)
        (CachedLowQuery.zeroBlock q width) rest col)) =
      (fun col => extract (width := width)
        (if hc : col.val < dims 0 then
          SharedEncoder.read (n+1) dims input (Fin.cons ⟨col.val,hc⟩ rest) else 0)) := by
    funext col deg res
    unfold gather
    split
    · rw [read_lowerData]
      simp only [CachedLowQuery.extractedBlock,denseRead_toDense]
    · simp [CachedLowQuery.zeroBlock,denseRead,extract,CyclicRing.zero_coeff]
  rw [hg, localRow_extract]
  simp only [CachedLowQuery.extractedBlock,denseRead_toDense]
  change extract (localPolynomial _ _ _) degree residue =
    extract (EncoderCorrectness.contractFirst dims _ _ rest) degree residue
  congr 2
  exact (source_row L side d (dims 0) hdim row
    (fun col => SharedEncoder.read (n+1) dims input (Fin.cons col rest))).symm

/-- Six candidate labels; only accepted children allocate coefficient arrays. -/
def nodeChildren (L m t d n q width : ℕ) (side : Bool) (hd : d < 2*L)
    (dims : Fin (n+1) → ℕ) (parent : DataNode q width (2*L) (n+1) dims) :
    List (DataNode q width (2*L) n (fun i => dims i.succ)) :=
  (List.finRange 6).filterMap (fun row =>
    let word := put d hd parent.word row
    if capTest L m t word then
      some ⟨word,contract L side d row dims parent.data⟩ else none)

def nextLayer (L m t d n q width : ℕ) (side : Bool) (hd : d < 2*L)
    (dims : Fin (n+1) → ℕ) (parents : List (DataNode q width (2*L) (n+1) dims)) :
    List (DataNode q width (2*L) n (fun i => dims i.succ)) :=
  parents.flatMap (nodeChildren L m t d n q width side hd dims)

/-- Forward array loop; stored parents are reused by every accepted child.
The 84 charge is justified below by the actual sparse instruction program. -/
def run (L m t q width : ℕ) (side : Bool) :
    (n : ℕ) → (dims : Fin n → ℕ) → ℕ → List (DataNode q width (2*L) n dims) →
      SharedEncoder.Result (Block q width) (2*L)
  | 0,dims,d,parents =>
      { leaves := parents.map (fun node => (node.word,node.data))
        formed := parents.map (fun node => ⟨d,0,dims,node⟩)
        coefficientWork := 84*q*width*parents.length*volume 0 dims
        capWork := 0
        coefficientCells := q*width*parents.length*volume 0 dims }
  | n+1,dims,d,parents =>
      if hd : d < 2*L then
        let children := nextLayer L m t d n q width side hd dims parents
        let tail := run L m t q width side n (fun i => dims i.succ) (d+1) children
        { tail with
          formed := parents.map (fun node => ⟨d,n+1,dims,node⟩) ++ tail.formed
          coefficientWork := 84*q*width*parents.length*volume (n+1) dims +tail.coefficientWork
          capWork := 6*parents.length*(1+3*(2*L))+tail.capWork
          coefficientCells := q*width*parents.length*volume (n+1) dims+tail.coefficientCells }
      else
        { leaves := []
          formed := parents.map (fun node => ⟨d,n+1,dims,node⟩)
          coefficientWork := 84*q*width*parents.length*volume (n+1) dims
          capWork := 0
          coefficientCells := q*width*parents.length*volume (n+1) dims }

noncomputable def lowerNode {q width N n : ℕ} [NeZero q] (dims : Fin n → ℕ)
    (node : SharedEncoder.Node (R := Polynomial (CyclicRing.Cyclic q)) N n dims) :
    DataNode q width N n dims := ⟨node.word, lowerData n dims node.data⟩

noncomputable def lowerStored {q width N : ℕ} [NeZero q]
    (s : SharedEncoder.Stored (Polynomial (CyclicRing.Cyclic q)) N) :
    SharedEncoder.Stored (Block q width) N :=
  ⟨s.depth,s.remaining,s.dims,lowerNode s.dims s.node⟩

noncomputable def lowerResult {q width N : ℕ} [NeZero q]
    (r : SharedEncoder.Result (Polynomial (CyclicRing.Cyclic q)) N) :
    SharedEncoder.Result (Block q width) N :=
  { leaves := r.leaves.map (fun leaf => (leaf.1,CachedLowQuery.extractedBlock leaf.2))
    formed := r.formed.map lowerStored
    coefficientWork := r.coefficientWork
    capWork := r.capWork
    coefficientCells := r.coefficientCells }


@[simp] theorem lowerNode_word {q width N n : ℕ} [NeZero q] (dims : Fin n → ℕ)
    (node : SharedEncoder.Node (R := Polynomial (CyclicRing.Cyclic q)) N n dims) :
    (lowerNode (width := width) dims node).word = node.word := rfl

theorem nodeChildren_refines {q width : ℕ} [NeZero q]
    (L m t d n : ℕ) (side : Bool) (hd : d < 2*L) (dims : Fin (n+1) → ℕ)
    (hdim : dims 0 = rawDim L side d)
    (parent : SharedEncoder.Node (R := Polynomial (CyclicRing.Cyclic q)) (2*L) (n+1) dims) :
    nodeChildren L m t d n q width side hd dims (lowerNode dims parent) =
      (SharedEncoder.nodeChildren L m t d n hd dims
        (CachedLowIdentity.sourceCacheForms L side) parent).map (lowerNode (width := width) _) := by
  simp only [nodeChildren,SharedEncoder.nodeChildren,List.map_filterMap]
  apply List.filterMap_congr
  intro row _
  simp only [lowerNode]
  split
  · simp only [Option.map_some,Option.some.injEq]
    congr 1
    exact contract_refines L side d row dims hdim parent.data
  · rfl

theorem nextLayer_refines {q width : ℕ} [NeZero q]
    (L m t d n : ℕ) (side : Bool) (hd : d < 2*L) (dims : Fin (n+1) → ℕ)
    (hdim : dims 0 = rawDim L side d)
    (parents : List (SharedEncoder.Node (R := Polynomial (CyclicRing.Cyclic q)) (2*L) (n+1) dims)) :
    nextLayer L m t d n q width side hd dims (parents.map (lowerNode dims)) =
      (SharedEncoder.nextLayer L m t d n hd dims
        (CachedLowIdentity.sourceCacheForms L side) parents).map (lowerNode (width := width) _) := by
  simp only [nextLayer,SharedEncoder.nextLayer,List.flatMap_map,List.map_flatMap]
  apply List.flatMap_congr
  intro parent _
  exact nodeChildren_refines L m t d n side hd dims hdim parent

/-- Full loop refinement, including every retained intermediate array and
all finite counters. The right side is used only as a mathematical model. -/
theorem run_refines {q width : ℕ} [NeZero q]
    (L m t : ℕ) (side : Bool) (n : ℕ) (dims : Fin n → ℕ) (d : ℕ)
    (parents : List (SharedEncoder.Node (R := Polynomial (CyclicRing.Cyclic q)) (2*L) n dims))
    (hs : Shape L side d n dims) :
    run L m t q width side n dims d (parents.map (lowerNode dims)) =
      lowerResult (width := width) (SharedEncoder.run L m t q width
        (CachedLowIdentity.sourceCacheForms L side) n dims d parents) := by
  induction n generalizing d with
  | zero =>
      simp [run,SharedEncoder.run,lowerResult,lowerStored,lowerNode,lowerData,
        SharedEncoder.materialize,SharedEncoder.read,List.map_map,Function.comp_def]
  | succ n ih =>
      have hd : d < 2*L := by have := hs.1; omega
      have hdim : dims 0 = rawDim L side d := by simpa using hs.2 0
      simp only [run,SharedEncoder.run,dif_pos hd]
      rw [nextLayer_refines L m t d n side hd dims hdim]
      rw [ih _ _ _ (shape_tail L side d n dims hs)]
      simp [lowerResult,lowerStored,lowerNode,List.map_map,Function.comp_def]

def encode (L m t q width : ℕ) (side : Bool)
    (input : Data q width (2*L) (rootDims L side)) : SharedEncoder.Result (Block q width) (2*L) :=
  run L m t q width side (2*L) (rootDims L side) 0 [⟨zeroWord (2*L),input⟩]

theorem encode_refines {q width : ℕ} [NeZero q] (L m t : ℕ) (side : Bool)
    (input : PolyData q (2*L) (rootDims L side)) :
    encode L m t q width side (lowerData (2*L) (rootDims L side) input) =
      lowerResult (width := width) (SharedEncoder.encode L m t q width side
        (CachedLowIdentity.sourceCacheForms L side) input) := by
  exact run_refines L m t side (2*L) (rootDims L side) 0
    [⟨zeroWord (2*L),input⟩] (root_shape L side)


/-- Actual auxiliary-degree-zero input formation. -/
def constantBlock {q : ℕ} (width : ℕ) (x : CyclicRing.Cyclic q) : Block q width :=
  Vector.ofFn fun degree => Vector.ofFn fun residue =>
    if degree.val = 0 then x residue else 0

theorem constantBlock_refines {q width : ℕ} [NeZero q] (x : CyclicRing.Cyclic q) :
    constantBlock width x = CachedLowQuery.extractedBlock (width := width) (Polynomial.C x) := by
  apply block_ext
  intro degree residue
  simp only [CachedLowQuery.extractedBlock,denseRead_toDense]
  simp only [constantBlock,denseRead,Vector.get_ofFn,extract,Polynomial.coeff_C]
  by_cases h : degree.val = 0 <;> simp [h]

/-- Integer-vector input array converted to dense auxiliary coefficient
blocks by one formation visit per degree/residue/suffix cell. -/
def constantInput {q width : ℕ} (n : ℕ) (dims : Fin n → ℕ)
    (input : SharedEncoder.Dense (R := Vector ℤ q) n dims) : Data q width n dims :=
  SharedEncoder.materialize n dims (fun a => constantBlock width
    (fun r => (SharedEncoder.read n dims input a).get r))

noncomputable def inputPolynomial {q : ℕ} [NeZero q] (n : ℕ) (dims : Fin n → ℕ)
    (input : SharedEncoder.Dense (R := Vector ℤ q) n dims) : PolyData q n dims :=
  SharedEncoder.materialize n dims (fun a => Polynomial.C
    (fun r => (SharedEncoder.read n dims input a).get r : CyclicRing.Cyclic q))

theorem constantInput_refines {q width : ℕ} [NeZero q] (n : ℕ) (dims : Fin n → ℕ)
    (input : SharedEncoder.Dense (R := Vector ℤ q) n dims) :
    constantInput (width := width) n dims input = lowerData n dims (inputPolynomial n dims input) := by
  unfold constantInput lowerData inputPolynomial
  apply congrArg (SharedEncoder.materialize n dims)
  funext a
  rw [SharedEncoder.read_materialize]
  exact constantBlock_refines _

/-- Computable public entry point from a stored raw integer-vector array. -/
def encodeVectors (L m t q width : ℕ) (side : Bool)
    (input : SharedEncoder.Dense (R := Vector ℤ q) (2*L) (rootDims L side)) :=
  encode L m t q width side (constantInput (2*L) (rootDims L side) input)

theorem encodeVectors_refines {q width : ℕ} [NeZero q] (L m t : ℕ) (side : Bool)
    (input : SharedEncoder.Dense (R := Vector ℤ q) (2*L) (rootDims L side)) :
    encodeVectors L m t q width side input =
      lowerResult (width := width) (SharedEncoder.encode L m t q width side
        (CachedLowIdentity.sourceCacheForms L side)
        (inputPolynomial (2*L) (rootDims L side) input)) := by
  rw [encodeVectors,constantInput_refines,encode_refines]

/-- Literal insertion of the already formed integer-array leaves. -/
def prepare {L m t q width : ℕ} (side : Bool)
    (input : Data q width (2*L) (rootDims L side)) :
    CachedLowQuery.Prepared (2*L) q width × ℕ :=
  let encoded := encode L m t q width side input
  let stored := CachedLowQuery.storePairs encoded.leaves .empty
  (stored.1,encoded.coefficientWork+encoded.capWork+stored.2+encoded.leaves.length*(q*width))

theorem prepare_refines {L m t q width : ℕ} [NeZero q] (side : Bool)
    (input : PolyData q (2*L) (rootDims L side)) :
    prepare (m := m) (t := t) side (lowerData (width := width) (2*L) (rootDims L side) input) =
      CachedLowQuery.prepareEncoded (m := m) (t := t) (width := width) side
        (CachedLowIdentity.sourceCacheForms L side) input := by
  unfold prepare
  rw [encode_refines]
  simp only [lowerResult,CachedLowQuery.prepareEncoded,List.length_map]

/-- The sparse coefficient-array execution inherits the complete retained
internal-array and cap-scan bound, with q and the auxiliary width explicit. -/
theorem prepare_work_le {L m t q width : ℕ} [NeZero q] (hw : 1 ≤ width) (side : Bool)
    (input : PolyData q (2*L) (rootDims L side)) :
    (prepare (m := m) (t := t) side
      (lowerData (width := width) (2*L) (rootDims L side) input)).2 ≤
      retainedLeafCount L m t * CachedLowQuery.preparationFactor L q width := by
  rw [prepare_refines]
  exact CachedLowQuery.prepareEncoded_work_le hw side _ input

/-- Source ordering is proof bookkeeping; actual execution starts from
an already materialized normal/opposite raw integer-vector array. -/
noncomputable def sourceVectorInput {q L : ℕ} (side : Bool)
    (X : CompleteThinProduct.SourceWord L → CyclicRing.Cyclic q) :
    SharedEncoder.Dense (R := Vector ℤ q) (2*L) (rootDims L side) :=
  match side with
  | true => SourceCoordinates.leftVectorInput X
  | false => SourceCoordinates.rightVectorInput X

theorem sourceInput_refines {q width L : ℕ} [NeZero q] (side : Bool)
    (X : CompleteThinProduct.SourceWord L → CyclicRing.Cyclic q) :
    constantInput (width := width) (2*L) (rootDims L side) (sourceVectorInput side X) =
      lowerData (2*L) (rootDims L side) (CachedLowIdentity.sourceCacheInput L side X) := by
  cases side <;> apply dense_ext <;> intro a
  · simp only [constantInput,SharedEncoder.read_materialize,read_lowerData,
      CachedLowIdentity.sourceCacheInput,SourceCoordinates.rightInput,SharedEncoder.read_materialize]
    have h : (fun r => (SharedEncoder.read (2*L) (rootDims L false)
        (sourceVectorInput false X) a).get r : CyclicRing.Cyclic q) = X (SourceCoordinates.toSourceFalse a) := by
      funext r
      exact SourceCoordinates.rightVectorInput_read X a r
    rw [h]
    exact constantBlock_refines _
  · simp only [constantInput,SharedEncoder.read_materialize,read_lowerData,
      CachedLowIdentity.sourceCacheInput,SourceCoordinates.leftInput,SharedEncoder.read_materialize]
    have h : (fun r => (SharedEncoder.read (2*L) (rootDims L true)
        (sourceVectorInput true X) a).get r : CyclicRing.Cyclic q) = X (SourceCoordinates.toSourceTrue a) := by
      funext r
      exact SourceCoordinates.leftVectorInput_read X a r
    rw [h]
    exact constantBlock_refines _

noncomputable def prepareSource {L m t q width : ℕ} (side : Bool)
    (X : CompleteThinProduct.SourceWord L → CyclicRing.Cyclic q) :
    CachedLowQuery.Prepared (2*L) q width × ℕ :=
  prepare (m := m) (t := t) side
    (constantInput (2*L) (rootDims L side) (sourceVectorInput side X))

theorem prepareSource_refines {L m t q width : ℕ} [NeZero q] (side : Bool)
    (X : CompleteThinProduct.SourceWord L → CyclicRing.Cyclic q) :
    prepareSource (m := m) (t := t) (width := width) side X =
      CachedLowQuery.prepareEncoded (m := m) (t := t) (width := width) side
        (CachedLowIdentity.sourceCacheForms L side) (CachedLowIdentity.sourceCacheInput L side X) := by
  rw [prepareSource,sourceInput_refines,prepare_refines]

theorem prepareSource_work_le {L m t q width : ℕ} [NeZero q] (hw : 1 ≤ width) (side : Bool)
    (X : CompleteThinProduct.SourceWord L → CyclicRing.Cyclic q) :
    (prepareSource (m := m) (t := t) (width := width) side X).2 ≤
      retainedLeafCount L m t * CachedLowQuery.preparationFactor L q width := by
  rw [prepareSource_refines]
  exact CachedLowQuery.prepareEncoded_work_le hw side _ _

theorem read_prepareSource_left {L m t q width : ℕ} [NeZero q]
    (X : CompleteThinProduct.SourceWord L → CyclicRing.Cyclic q)
    (word : Word (2*L)) (hw : Retained L m t word) :
    CachedLowQuery.readBlock (prepareSource (m := m) (t := t) (width := width) true X).1 word =
      CachedLowQuery.extractedBlock (CachedLowIdentity.leftCachePolynomial X word) := by
  rw [prepareSource_refines,CachedLowQuery.read_prepareEncoded_block _ _ _ _ hw,
    CachedLowIdentity.left_cache_tensorValue]

theorem read_prepareSource_right {L m t q width : ℕ} [NeZero q]
    (Y : CompleteThinProduct.SourceWord L → CyclicRing.Cyclic q)
    (word : Word (2*L)) (hw : Retained L m t word) :
    CachedLowQuery.readBlock (prepareSource (m := m) (t := t) (width := width) false Y).1 word =
      CachedLowQuery.extractedBlock (CachedLowIdentity.rightCachePolynomial Y word) := by
  rw [prepareSource_refines,CachedLowQuery.read_prepareEncoded_block _ _ _ _ hw,
    CachedLowIdentity.right_cache_tensorValue]

/-- Genuine source cache contents, sufficient for the actual LOW query's
producer-independent correctness theorem. -/
theorem sourceCacheValid {L m t q width : ℕ} [NeZero q]
    (X Y : CompleteThinProduct.SourceWord L → CyclicRing.Cyclic q) :
    CachedLowQuery.SourceCacheValid (m := m) (t := t) X Y
      ((prepareSource (m := m) (t := t) (width := width) true X).1,
       (prepareSource (m := m) (t := t) (width := width) false Y).1) := by
  intro word hw
  exact ⟨read_prepareSource_left X word hw,read_prepareSource_right Y word hw⟩


/-- Row execution plus one shared zero-padding block per accepted child.
Four-input reads are executed by the sparse thirteen-instruction program. -/
def childScalarWork {n : ℕ} (q width L : ℕ) (side : Bool) (d : ℕ)
    (dims : Fin (n+1) → ℕ) (row : Label) : ℕ :=
  volume n (fun i => dims i.succ) * materializeScalarCost q width (normalHere L side d) row + q*width

/-- This includes current-array formation and all six possible children,
so rejected labels only decrease the required scalar instruction work. -/
def parentScalarWork {n : ℕ} (q width L : ℕ) (side : Bool) (d : ℕ)
    (dims : Fin (n+1) → ℕ) : ℕ :=
  q*width*volume (n+1) dims + ∑ row : Label, childScalarWork q width L side d dims row

theorem volume_succ {n : ℕ} (dims : Fin (n+1) → ℕ) :
    volume (n+1) dims = dims 0 * volume n (fun i => dims i.succ) := by
  exact Fin.prod_univ_succ dims

theorem childScalarWork_eq {n : ℕ} (q width L : ℕ) (side : Bool) (d : ℕ)
    (dims : Fin (n+1) → ℕ) (row : Label) :
    childScalarWork q width L side d dims row =
      14*q*width*volume n (fun i => dims i.succ)+q*width := by
  rw [childScalarWork,materializeScalarCost_eq]
  ring

/-- The advertised 84qwidth charge is an upper bound for the literal row
program and padding allocation, not a unit price for polynomial products. -/
theorem parentScalarWork_le {n : ℕ} (q width L : ℕ) (side : Bool) (d : ℕ)
    (dims : Fin (n+1) → ℕ) (hs : Shape L side d (n+1) dims) :
    parentScalarWork q width L side d dims ≤ 84*q*width*volume (n+1) dims := by
  have hdim : 3 ≤ dims 0 := by
    rw [hs.2 0]
    unfold rawDim
    split <;> omega
  have hv : 1 ≤ volume n (fun i => dims i.succ) := by
    rw [shape_volume L side (d+1) n (fun i => dims i.succ)
      (shape_tail L side d n dims hs)]
    exact rawVolume_pos L (d+1) side
  have hbasic : dims 0*volume n (fun i => dims i.succ) +
      84*volume n (fun i => dims i.succ)+6 ≤
      84*(dims 0*volume n (fun i => dims i.succ)) := by nlinarith
  simp only [parentScalarWork,childScalarWork_eq,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,smul_eq_mul,volume_succ]
  calc
    _ = q*width*(dims 0*volume n (fun i => dims i.succ)+
        84*volume n (fun i => dims i.succ)+6) := by ring
    _ ≤ q*width*(84*(dims 0*volume n (fun i => dims i.succ))) :=
      Nat.mul_le_mul_left _ hbasic
    _ = _ := by ring

/-- Local scalar-work allowance at an actually stored prefix array.
The terminal case charges its already materialized payload once. -/
def storedScalarWork {q width N : ℕ} (L : ℕ) (side : Bool)
    (s : SharedEncoder.Stored (Block q width) N) : ℕ :=
  match s.remaining,s.dims with
  | 0,dims => q*width*volume 0 dims
  | _n+1,dims => parentScalarWork q width L side s.depth dims

/-- Explicit maximum number of nested suffix vector reads per sparse
coefficient read. Machine-address and bit costs require their own adapters. -/
def nestedReadFactor (L : ℕ) : ℕ := 2*L+1

/-- The full concrete row schedule is bounded by the advertised stored
array ledger whenever those arrays have the actual source suffix shapes. -/
theorem storedScalarWork_le {q width N : ℕ} (L : ℕ) (side : Bool)
    (s : SharedEncoder.Stored (Block q width) N)
    (hs : Shape L side s.depth s.remaining s.dims) :
    storedScalarWork L side s ≤ 84*q*width*volume s.remaining s.dims := by
  rcases s with ⟨depth,remaining,dims,node⟩
  cases remaining with
  | zero =>
      simp only [storedScalarWork]
      nlinarith [Nat.zero_le (q*width*volume 0 dims)]
  | succ n => exact parentScalarWork_le q width L side depth dims hs

theorem reference_formed_shape {q : ℕ} [NeZero q] (L m t width : ℕ) (side : Bool)
    (input : PolyData q (2*L) (rootDims L side)) :
    ∀ s ∈ (SharedEncoder.encode L m t q width side
      (CachedLowIdentity.sourceCacheForms L side) input).formed,
      Shape L side s.depth s.remaining s.dims := by
  apply SharedEncoder.run_invariant L m t q width
    (CachedLowIdentity.sourceCacheForms L side)
    (fun d n dims _ => Shape L side d n dims)
  · intro d n hd dims parent hs child _
    exact shape_tail L side d n dims hs
  · intro parent hp
    simp only [List.mem_singleton] at hp
    exact root_shape L side

theorem encoded_formed_shape {q width : ℕ} [NeZero q] (L m t : ℕ) (side : Bool)
    (input : PolyData q (2*L) (rootDims L side)) :
    ∀ s ∈ (encode L m t q width side (lowerData (2*L) (rootDims L side) input)).formed,
      Shape L side s.depth s.remaining s.dims := by
  rw [encode_refines]
  intro s hs
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hs
  exact reference_formed_shape L m t width side input a ha

theorem encoded_scalarWork_le {q width : ℕ} [NeZero q] (L m t : ℕ) (side : Bool)
    (input : PolyData q (2*L) (rootDims L side)) :
    ((encode L m t q width side (lowerData (2*L) (rootDims L side) input)).formed.map
      (storedScalarWork L side)).sum ≤
      (encode L m t q width side (lowerData (2*L) (rootDims L side) input)).coefficientWork := by
  have hsum : ∀ (ss : List (SharedEncoder.Stored (Block q width) (2*L))),
      (∀ s ∈ ss, Shape L side s.depth s.remaining s.dims) →
      (ss.map (storedScalarWork L side)).sum ≤ 84*SharedEncoder.formedCells q width ss := by
    intro ss hshape
    induction ss with
    | nil => simp [SharedEncoder.formedCells]
    | cons s ss ih =>
        have ha := storedScalarWork_le L side s (hshape s (by simp))
        have hb := ih (fun a ha => hshape a (by simp [ha]))
        simp only [List.map_cons,List.sum_cons,SharedEncoder.formedCells] at *
        nlinarith
  have h := hsum _ (encoded_formed_shape L m t side input)
  rw [encode_refines] at h ⊢
  have hf : SharedEncoder.formedCells q width
      ((SharedEncoder.encode L m t q width side (CachedLowIdentity.sourceCacheForms L side) input).formed.map
        (lowerStored (width := width))) =
      SharedEncoder.formedCells q width
        (SharedEncoder.encode L m t q width side (CachedLowIdentity.sourceCacheForms L side) input).formed := by
    simp [SharedEncoder.formedCells,List.map_map,lowerStored,Function.comp_def]
  change _ ≤ (SharedEncoder.encode L m t q width side (CachedLowIdentity.sourceCacheForms L side) input).coefficientWork
  have hc := SharedEncoder.run_cells_eq_formed L m t q width
    (CachedLowIdentity.sourceCacheForms L side) (2*L) (rootDims L side) 0 [⟨zeroWord (2*L),input⟩]
  have hw := SharedEncoder.run_work_eq_cells L m t q width
    (CachedLowIdentity.sourceCacheForms L side) (2*L) (rootDims L side) 0 [⟨zeroWord (2*L),input⟩]
  change _ ≤ 84*SharedEncoder.formedCells q width _ at h
  simp only [lowerResult] at h
  rw [hf] at h
  exact h.trans_eq (by simpa only [SharedEncoder.encode] using (hw.trans (congrArg (84*·) hc)).symm)


/-- Actual leaf arrays are precisely the retained polynomial coefficients;
this also certifies that no full-word sweep is executed separately per leaf. -/
theorem encode_lowered_correct {q width : ℕ} [NeZero q] (L m t : ℕ) (side : Bool)
    (input : PolyData q (2*L) (rootDims L side)) :
    (encode L m t q width side (lowerData (2*L) (rootDims L side) input)).leaves.map Prod.fst =
        CappedEnumeration.generate L m t (2*L) ∧
    ∀ leaf ∈ (encode L m t q width side (lowerData (2*L) (rootDims L side) input)).leaves,
      leaf.2 = CachedLowQuery.extractedBlock
        (SharedEncoder.tensorValue L side (CachedLowIdentity.sourceCacheForms L side) input leaf.1) := by
  rw [encode_refines]
  constructor
  · simpa only [lowerResult,List.map_map,Function.comp_def] using
      (SharedEncoder.encode_correct L m t q width side (CachedLowIdentity.sourceCacheForms L side) input).1
  · intro leaf hleaf
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hleaf
    exact congrArg (CachedLowQuery.extractedBlock (width := width))
      ((SharedEncoder.encode_correct L m t q width side
        (CachedLowIdentity.sourceCacheForms L side) input).2 a ha)

theorem encodeVectors_cells_le {q width : ℕ} [NeZero q] (L m t : ℕ) (side : Bool)
    (input : SharedEncoder.Dense (R := Vector ℤ q) (2*L) (rootDims L side)) :
    (encodeVectors L m t q width side input).coefficientCells ≤
      q*width*(2*L+1)*retainedLeafCount L m t := by
  rw [encodeVectors_refines]
  exact SharedEncoder.encode_cells_le L m t q width side
    (CachedLowIdentity.sourceCacheForms L side) (inputPolynomial (2*L) (rootDims L side) input)

/-- Computable preparation from an already stored raw vector array. The
source/Walsh pipeline supplies this array in either physical orientation. -/
def prepareVectors {L m t q width : ℕ} (side : Bool)
    (input : SharedEncoder.Dense (R := Vector ℤ q) (2*L) (rootDims L side)) :
    CachedLowQuery.Prepared (2*L) q width × ℕ :=
  prepare (m := m) (t := t) side (constantInput (2*L) (rootDims L side) input)

theorem prepareVectors_refines {L m t q width : ℕ} [NeZero q] (side : Bool)
    (input : SharedEncoder.Dense (R := Vector ℤ q) (2*L) (rootDims L side)) :
    prepareVectors (m := m) (t := t) (width := width) side input =
      CachedLowQuery.prepareEncoded (m := m) (t := t) (width := width) side
        (CachedLowIdentity.sourceCacheForms L side) (inputPolynomial (2*L) (rootDims L side) input) := by
  rw [prepareVectors,constantInput_refines,prepare_refines]

theorem prepareVectors_work_le {L m t q width : ℕ} [NeZero q] (hw : 1 ≤ width) (side : Bool)
    (input : SharedEncoder.Dense (R := Vector ℤ q) (2*L) (rootDims L side)) :
    (prepareVectors (m := m) (t := t) (width := width) side input).2 ≤
      retainedLeafCount L m t * CachedLowQuery.preparationFactor L q width := by
  rw [prepareVectors_refines]
  exact CachedLowQuery.prepareEncoded_work_le hw side _ _

/-- Multiplying the proven scalar visit ledger by this factor conservatively
pays the nested suffix-vector indexing depth as well. This is still a finite
scalar-access ledger; binary addressing and integer bits are not unit cost. -/
theorem encoded_nestedRead_work_le {q width : ℕ} [NeZero q] (L m t : ℕ) (side : Bool)
    (input : PolyData q (2*L) (rootDims L side)) :
    nestedReadFactor L *
      ((encode L m t q width side (lowerData (2*L) (rootDims L side) input)).formed.map
        (storedScalarWork L side)).sum ≤
      nestedReadFactor L * (84*q*width*(2*L+1)*retainedLeafCount L m t) := by
  apply Nat.mul_le_mul_left
  apply (encoded_scalarWork_le L m t side input).trans
  rw [encode_refines]
  exact SharedEncoder.encode_coefficientWork_le L m t q width side
    (CachedLowIdentity.sourceCacheForms L side) input


/-- The source-facing wrapper calls exactly the concrete vector program;
its noncomputability annotation is confined to the source-coordinate model. -/
theorem prepareSource_is_vectorProgram {L m t q width : ℕ} (side : Bool)
    (X : CompleteThinProduct.SourceWord L → CyclicRing.Cyclic q) :
    prepareSource (m := m) (t := t) (width := width) side X =
      prepareVectors (m := m) (t := t) (width := width) side (sourceVectorInput side X) := rfl

/-- Both genuine-source producers satisfy the local read contract consumed
by CachedLowQuery. The scalar work bound charges each encoder separately. -/
theorem paired_source_contract {L m t q width : ℕ} [NeZero q] (hw : 1 ≤ width)
    (X Y : CompleteThinProduct.SourceWord L → CyclicRing.Cyclic q) :
    CachedLowQuery.SourceCacheValid (m := m) (t := t) X Y
      ((prepareSource (m := m) (t := t) (width := width) true X).1,
       (prepareSource (m := m) (t := t) (width := width) false Y).1) ∧
    (prepareSource (m := m) (t := t) (width := width) true X).2 +
      (prepareSource (m := m) (t := t) (width := width) false Y).2 ≤
        2*retainedLeafCount L m t*CachedLowQuery.preparationFactor L q width := by
  refine ⟨sourceCacheValid X Y,?_⟩
  have hl := prepareSource_work_le (m := m) (t := t) hw true X
  have hr := prepareSource_work_le (m := m) (t := t) hw false Y
  nlinarith

/- Executable sanity audit of the coefficient-array loop, with no polynomial
objects in the evaluated expression. General correctness is proved above. -/
#eval let input := SharedEncoder.materialize 2 (rootDims 1 true) (fun a =>
    Vector.ofFn (fun residue : Fin 3 =>
      ((1+residue.val+∑ i : Fin 2,(a i).val : ℕ) : ℤ)))
  let encoded := encodeVectors 1 1 1 3 2 true input
  (encoded.leaves.length,encoded.formed.length,encoded.coefficientCells,
    encoded.coefficientWork,encoded.capWork)

#print axioms contract_refines
#print axioms run_refines
#print axioms encodeVectors_refines
#print axioms constantInput_refines
#print axioms prepare_refines
#print axioms prepareSource_work_le
#print axioms sourceCacheValid
#print axioms encode_lowered_correct
#print axioms encodeVectors_cells_le
#print axioms prepareVectors_work_le
#print axioms paired_source_contract
#print axioms encoded_nestedRead_work_le
#print axioms parentScalarWork_le
#print axioms encoded_formed_shape
#print axioms encoded_scalarWork_le

end ThinMatrix.CacheDenseLowering
