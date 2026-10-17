import SharedEncoder
import StoredHighDP
import SparseLocalForms
import CompleteThinProduct
import CacheCardinality
import ArrayKeys
import CachedLowIdentity
import LowChannelEnumeration

/-!
# Materialized cache reads for the aligned LOW query

The cache dictionary is the already proved six-way array trie. Preparing
it inserts actual retained encoder leaves and stores materialized dense
integer coefficient blocks. A query reads those blocks through its physical
channel word and evaluates only the requested cyclic coefficient by literal
length-q dot products. The formal auxiliary variable and cyclic residue
index remain separate.
-/

namespace ThinMatrix.CachedLowQuery

open CacheBounds CappedEnumeration SharedEncoder SparseLocalForms
open scoped BigOperators

universe u v

/-- Batch insertion consumes the materialized payload directly from each
record; it never searches the leaf list again to recompute a value. -/
def storePairs {A : Type u} {N : ℕ} :
    List (Word N × A) → StoredHighDP.Trie A → StoredHighDP.Trie A × ℕ
  | [], table => (table, 0)
  | (word, value) :: rows, table =>
      let written := table.writeCounted (StoredHighDP.key word) value
      let tail := storePairs rows written.1
      (tail.1, written.2 + N + tail.2)

theorem storePairs_work {A : Type u} {N : ℕ} (rows : List (Word N × A))
    (table : StoredHighDP.Trie A) :
    (storePairs rows table).2 = rows.length * (9 * N + 7) := by
  induction rows generalizing table with
  | nil => simp [storePairs]
  | cons row rows ih =>
      rcases row with ⟨word, value⟩
      simp only [storePairs, ih, StoredHighDP.Trie.writeCounted_work, StoredHighDP.key_length,
        List.length_cons]
      ring

theorem read_storePairs_absent {A : Type u} {N : ℕ} (rows : List (Word N × A))
    (table : StoredHighDP.Trie A) (word : Word N) (hnot : word ∉ rows.map Prod.fst) :
    (storePairs rows table).1.read (StoredHighDP.key word) = table.read (StoredHighDP.key word) := by
  induction rows generalizing table with
  | nil => rfl
  | cons row rows ih =>
      rcases row with ⟨w, value⟩
      have hw : word ≠ w := by intro he; exact hnot (by simp [he])
      have ht : word ∉ rows.map Prod.fst := by intro hm; exact hnot (by simp [hm])
      simp only [storePairs]
      rw [ih _ ht, StoredHighDP.Trie.writeCounted_value]
      exact StoredHighDP.Trie.read_write_other table (StoredHighDP.key w)
        (StoredHighDP.key word) value (fun he => hw (StoredHighDP.key_injective N he))

theorem read_storePairs {A : Type u} {N : ℕ} (rows : List (Word N × A))
    (table : StoredHighDP.Trie A) (hnd : (rows.map Prod.fst).Nodup)
    {word : Word N} {value : A} (hmem : (word, value) ∈ rows) :
    (storePairs rows table).1.read (StoredHighDP.key word) = some value := by
  induction rows generalizing table with
  | nil => simp at hmem
  | cons row rows ih =>
      rcases row with ⟨w, x⟩
      have hnd' := List.nodup_cons.mp hnd
      obtain he | hm := List.mem_cons.mp hmem
      · cases he
        simp only [storePairs]
        rw [read_storePairs_absent _ _ _ hnd'.1, StoredHighDP.Trie.writeCounted_value]
        exact StoredHighDP.Trie.read_write_same _ _ _
      · exact ih _ hnd'.2 hm

abbrev Prepared (_N q width : ℕ) := StoredHighDP.Trie (DenseVector q width)

def zeroBlock (q width : ℕ) : DenseVector q width :=
  Vector.replicate width (Vector.replicate q 0)

def readBlock {N q width : ℕ} (table : Prepared N q width) (word : Word N) : DenseVector q width :=
  (table.read (StoredHighDP.key word)).getD (zeroBlock q width)

def readBlockCounted {N q width : ℕ} (table : Prepared N q width) (word : Word N) :
    DenseVector q width × ℕ :=
  let result := table.readCounted (StoredHighDP.key word)
  (result.1.getD (zeroBlock q width), N + result.2 + q * width)

@[simp] theorem readBlockCounted_value {N q width : ℕ} (table : Prepared N q width) (word : Word N) :
    (readBlockCounted table word).1 = readBlock table word := by
  simp [readBlockCounted, readBlock]

@[simp] theorem readBlockCounted_work {N q width : ℕ} (table : Prepared N q width) (word : Word N) :
    (readBlockCounted table word).2 = 2 * N + 1 + q * width := by
  simp [readBlockCounted]
  omega

def blockCoeff {q width : ℕ} (block : DenseVector q width) (degree : ℕ) (residue : Fin q) : ℤ :=
  if h : degree < width then (block.get ⟨degree, h⟩).get residue else 0

noncomputable def extractedBlock {q width : ℕ} [NeZero q]
    (p : Polynomial (CyclicRing.Cyclic q)) : DenseVector q width := toDense (extract p)

theorem extractedBlock_coeff {q width : ℕ} [NeZero q]
    (p : Polynomial (CyclicRing.Cyclic q)) (degree : ℕ) (hd : degree < width) (residue : Fin q) :
    blockCoeff (extractedBlock (width := width) p) degree residue = p.coeff degree residue := by
  simp [blockCoeff, hd, extractedBlock, toDense, extract, Vector.get_ofFn]

/-- Generic reference preparation over polynomial denotations. Its encoder
counter is the SharedEncoder weighted scalar counter. SparseLocalForms and
CacheDenseLowering supply the integer-array realization for the fixed six
source rows; arbitrary polynomial forms do not have this implementation cost. -/
noncomputable def prepareEncoded {L m t q width : ℕ} [NeZero q] (side : Bool)
    (forms : LocalForms (Polynomial (CyclicRing.Cyclic q)))
    (input : Dense (R := Polynomial (CyclicRing.Cyclic q)) (2 * L) (rootDims L side)) :
    Prepared (2 * L) q width × ℕ :=
  let encoded := encode L m t q width side forms input
  let rows := encoded.leaves.map (fun leaf => (leaf.1, extractedBlock (width := width) leaf.2))
  let stored := storePairs rows .empty
  (stored.1, encoded.coefficientWork + encoded.capWork + stored.2 + rows.length * (q * width))

/-- Preparing from the returned encoder list costs one dense block and
one trie insertion per actual retained leaf. -/
theorem prepareEncoded_work_eq {L m t q width : ℕ} [NeZero q] (side : Bool)
    (forms : LocalForms (Polynomial (CyclicRing.Cyclic q)))
    (input : Dense (R := Polynomial (CyclicRing.Cyclic q)) (2 * L) (rootDims L side)) :
    (prepareEncoded (m := m) (t := t) (width := width) side forms input).2 =
      (encode L m t q width side forms input).coefficientWork +
      (encode L m t q width side forms input).capWork +
      retainedLeafCount L m t * (9 * (2 * L) + 7 + q * width) := by
  simp only [prepareEncoded, storePairs_work, List.length_map]
  have hlen := congrArg List.length (encode_correct L m t q width side forms input).1
  simp only [List.length_map, generate_leaf_length] at hlen
  rw [hlen]
  ring

def preparationFactor (L q width : ℕ) : ℕ :=
  (84*(2*L+1)+12*L*(1+6*L))*q*width + 9*(2*L)+7+q*width

theorem prepareEncoded_work_le {L m t q width : ℕ} [NeZero q] (hw : 1 ≤ width) (side : Bool)
    (forms : LocalForms (Polynomial (CyclicRing.Cyclic q)))
    (input : Dense (R := Polynomial (CyclicRing.Cyclic q)) (2*L) (rootDims L side)) :
    (prepareEncoded (m := m) (t := t) (width := width) side forms input).2 ≤
      retainedLeafCount L m t * preparationFactor L q width := by
  rw [prepareEncoded_work_eq]
  have he := encode_work_le L m t q width side forms input (Nat.pos_of_neZero q) hw
  unfold preparationFactor
  nlinarith

/-- A cache read refers to a materialized retained encoder leaf, not a
fresh tensor contraction performed during the query. -/
theorem read_prepareEncoded {L m t q width : ℕ} [NeZero q] (side : Bool)
    (forms : LocalForms (Polynomial (CyclicRing.Cyclic q)))
    (input : Dense (R := Polynomial (CyclicRing.Cyclic q)) (2 * L) (rootDims L side))
    (word : Word (2 * L)) (hword : Retained L m t word)
    (degree : ℕ) (hd : degree < width) (residue : Fin q) :
    blockCoeff (readBlock (prepareEncoded (m := m) (t := t) (width := width) side forms input).1 word)
      degree residue = (tensorValue L side forms input word).coeff degree residue := by
  have hkey : word ∈ (encode L m t q width side forms input).leaves.map Prod.fst := by
    rw [(encode_correct L m t q width side forms input).1]
    exact (mem_generate_leaf L m t word).mpr hword
  obtain ⟨leaf, hleaf, hwordeq⟩ := List.mem_map.mp hkey
  have hvalue := (encode_correct L m t q width side forms input).2 leaf hleaf
  have hnd : (((encode L m t q width side forms input).leaves.map
      (fun leaf => (leaf.1, extractedBlock (width := width) leaf.2))).map Prod.fst).Nodup := by
    simpa only [List.map_map, Function.comp_def] using encode_keys_nodup L m t q width side forms input
  have hread := read_storePairs
    ((encode L m t q width side forms input).leaves.map
      (fun leaf => (leaf.1, extractedBlock (width := width) leaf.2))) .empty hnd
    (List.mem_map.mpr ⟨leaf, hleaf, rfl⟩)
  unfold readBlock prepareEncoded
  rw [← hwordeq, hread, Option.getD_some, extractedBlock_coeff leaf.2 degree hd residue, hvalue]

theorem read_prepareEncoded_block {L m t q width : ℕ} [NeZero q] (side : Bool)
    (forms : LocalForms (Polynomial (CyclicRing.Cyclic q)))
    (input : Dense (R := Polynomial (CyclicRing.Cyclic q)) (2 * L) (rootDims L side))
    (word : Word (2 * L)) (hword : Retained L m t word) :
    readBlock (prepareEncoded (m := m) (t := t) (width := width) side forms input).1 word =
      extractedBlock (width := width) (tensorValue L side forms input word) := by
  apply Vector.ext
  intro degree hdegree
  apply Vector.ext
  intro residue hresidue
  have h := read_prepareEncoded side forms input word hword degree hdegree ⟨residue,hresidue⟩
  simpa [blockCoeff, hdegree, extractedBlock, toDense, extract, Vector.get] using h

/-- One requested cyclic coefficient, with a literal finite dot loop. -/
def selectedDot {q : ℕ} [NeZero q] (left right : Fin q → ℤ) (target : Fin q) : ℤ × ℕ :=
  (((List.finRange q).map (fun r => left r * right (target - r))).sum, 5 * q)

theorem selectedDot_value {q : ℕ} [NeZero q] (left right : CyclicRing.Cyclic q) (target : Fin q) :
    (selectedDot left right target).1 = (left * right) target := by
  rw [CyclicRing.mul_coeff]
  change ((List.finRange q).map (fun r => left r * right (target - r))).sum = _
  rw [← List.ofFn_eq_map]
  exact List.sum_ofFn

def polynomialDot {q width : ℕ} [NeZero q] (left right : DenseVector q width)
    (degree : ℕ) (target : Fin q) : ℤ × ℕ :=
  let rows := (List.range (degree + 1)).map (fun a =>
    selectedDot (blockCoeff left a) (blockCoeff right (degree - a)) target)
  ((rows.map Prod.fst).sum, (rows.map Prod.snd).sum)

theorem polynomialDot_work {q width : ℕ} [NeZero q] (left right : DenseVector q width)
    (degree : ℕ) (target : Fin q) :
    (polynomialDot left right degree target).2 = 5 * q * (degree + 1) := by
  unfold polynomialDot
  simp only [List.map_map, Function.comp_def, selectedDot]
  change ((List.range (degree + 1)).map (fun _ => 5 * q)).sum = _
  simp
  ring

theorem polynomialDot_value {q width : ℕ} [NeZero q]
    (left right : Polynomial (CyclicRing.Cyclic q)) (degree : ℕ) (hd : degree < width)
    (target : Fin q) :
    (polynomialDot (extractedBlock (width := width) left) (extractedBlock right) degree target).1 =
      ((left * right).coeff degree) target := by
  unfold polynomialDot
  simp only [List.map_map, Function.comp_def]
  rw [Polynomial.coeff_mul, CyclicRing.sum_coeff,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  rw [← List.sum_toFinset _ (List.nodup_range (n := degree + 1))]
  simp only [List.toFinset_range]
  apply Finset.sum_congr rfl
  intro a ha
  have ha' : a ≤ degree := by have := Finset.mem_range.mp ha; omega
  change (selectedDot _ _ target).1 = _
  have hleft : blockCoeff (extractedBlock (width := width) left) a = left.coeff a := by
    funext r
    exact extractedBlock_coeff left a (by omega) r
  have hright : blockCoeff (extractedBlock (width := width) right) (degree - a) =
      right.coeff (degree - a) := by
    funext r
    exact extractedBlock_coeff right (degree - a) (by omega) r
  rw [hleft, hright, selectedDot_value]

/-- The semantic normal source contraction is the literal sparse
six-row operator, including its single p1 auxiliary shift. -/
theorem normal_cache_localPolynomial {R : Type*} [CommRing R] (row : Fin 6)
    (children : Fin 4 → Polynomial R) :
    (∑ a : Fin 4, CachedLowIdentity.normalCacheForm (SourceCoordinates.normalEquiv a) row * children a) =
      SparseLocalForms.localPolynomial true row children := by
  change (∑ a : Fin 4, CachedLowIdentity.normalCacheForm
    (![.x1,.x2,.p1,.p2] a) row * children a) = _
  rw [congrFun (SparseLocalForms.normal_localPolynomial children) row]
  fin_cases row <;>
    simp [Fin.sum_univ_succ,CachedLowIdentity.normalCacheForm,
      CompleteThinProduct.normalForm,TensorContraction.alignedLeft,CompleteThinProduct.letterIndicator] <;> ring

/-- The opposite contraction pads its absent fourth coordinate with
literal zero before invoking the same materialized sparse-row primitive. -/
theorem opposite_cache_localPolynomial {R : Type*} [CommRing R] (row : Fin 6)
    (children : Fin 3 → Polynomial R) :
    (∑ a : Fin 3, CachedLowIdentity.oppositeCacheForm (SourceCoordinates.oppositeEquiv a) row * children a) =
      SparseLocalForms.localPolynomial false row (fun a => if h : a.val < 3 then children ⟨a.val,h⟩ else 0) := by
  change (∑ a : Fin 3, CachedLowIdentity.oppositeCacheForm (![.s,.v,.w] a) row * children a) = _
  rw [congrFun (SparseLocalForms.opposite_localPolynomial
    (fun a : Fin 4 => if h : a.val < 3 then children ⟨a.val,h⟩ else 0)) row]
  fin_cases row <;>
    simp [Fin.sum_univ_succ,CachedLowIdentity.oppositeCacheForm,
      CompleteThinProduct.oppositeForm,TensorContraction.alignedRight,CompleteThinProduct.letterIndicator,
      Polynomial.C_ofNat] <;> ring

/-- Linear factorial loop used only to construct binomial query weights.
This avoids evaluating the exponential Pascal specification recursively. -/
def factorialCounted : ℕ → ℕ × ℕ
  | 0 => (1, 1)
  | n+1 => let prev := factorialCounted n; ((n+1)*prev.1, prev.2+3)

@[simp] theorem factorialCounted_value (n : ℕ) : (factorialCounted n).1 = n.factorial := by
  induction n with
  | zero => rfl
  | succ n ih => simp [factorialCounted, Nat.factorial_succ, ih]

@[simp] theorem factorialCounted_work (n : ℕ) : (factorialCounted n).2 = 3*n+1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [factorialCounted, ih]; omega

def chooseCounted (n h : ℕ) : ℕ × ℕ :=
  if h ≤ n then
    let a := factorialCounted n
    let b := factorialCounted h
    let c := factorialCounted (n-h)
    (a.1/(b.1*c.1),a.2+b.2+c.2+4)
  else (0,1)

@[simp] theorem chooseCounted_value (n h : ℕ) : (chooseCounted n h).1 = n.choose h := by
  unfold chooseCounted
  split
  · simpa only [factorialCounted_value] using (Nat.choose_eq_factorial_div_factorial ‹h ≤ n›).symm
  · exact (Nat.choose_eq_zero_of_lt (by omega)).symm

theorem chooseCounted_work_le (n h : ℕ) : (chooseCounted n h).2 ≤ 7*(n+1) := by
  unfold chooseCounted
  split
  · simp only [factorialCounted_work]
    omega
  · omega

def signCounted : ℕ → ℤ × ℕ
  | 0 => (1,1)
  | n+1 => let prev := signCounted n; (-prev.1,prev.2+2)

@[simp] theorem signCounted_value (n : ℕ) : (signCounted n).1 = (-1:ℤ)^n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [signCounted,ih,pow_succ]

@[simp] theorem signCounted_work (n : ℕ) : (signCounted n).2 = 2*n+1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [signCounted,ih]; omega

def weightCounted (k t degree : ℕ) : ℤ × ℕ :=
  let a := signCounted (t-degree-1)
  let b := chooseCounted (k-degree-1) (t-degree-1)
  (a.1*b.1,a.2+b.2+2)

@[simp] theorem weightCounted_value (k t degree : ℕ) :
    (weightCounted k t degree).1 = (TensorContraction.residualWeight k t degree : ℤ) := by
  simp [weightCounted,TensorContraction.residualWeight]

def weightWork (k t : ℕ) : ℕ := 7*(k+1)+2*t+3

theorem weightCounted_work_le (k t degree : ℕ) :
    (weightCounted k t degree).2 ≤ weightWork k t := by
  unfold weightCounted weightWork
  simp only [signCounted_work]
  have := chooseCounted_work_le (k-degree-1) (t-degree-1)
  omega

/-- The actual finite integer step for one channel and one degree. -/
def lowTerm {q width : ℕ} [NeZero q] (k t : ℕ)
    (left right : DenseVector q width) (channelCard degree : ℕ) (target : Fin q) : ℤ × ℕ :=
  if channelCard ≤ degree then
    let dot := polynomialDot left right (degree - channelCard) target
    let weight := weightCounted k t degree
    (weight.1 * dot.1, dot.2 + weight.2 + 4)
  else (0, 1)

theorem lowTerm_value {q width : ℕ} [NeZero q] (k t : ℕ)
    (left right : Polynomial (CyclicRing.Cyclic q)) (channelCard degree : ℕ)
    (hd : degree < width) (target : Fin q) :
    (lowTerm k t (extractedBlock (width := width) left) (extractedBlock right)
      channelCard degree target).1 =
      if channelCard ≤ degree then (TensorContraction.residualWeight k t degree : ℤ) *
        ((left * right).coeff (degree-channelCard)) target else 0 := by
  unfold lowTerm
  split
  · dsimp only
    rw [weightCounted_value, polynomialDot_value left right _ (by omega)]
  · rfl

theorem lowTerm_work_le {q width : ℕ} [NeZero q] (k t : ℕ)
    (left right : DenseVector q width) (channelCard degree : ℕ)
    (hd : degree < t) (target : Fin q) :
    (lowTerm k t left right channelCard degree target).2 ≤ 5 * q * t + weightWork k t + 4 := by
  unfold lowTerm
  split
  · dsimp only
    rw [polynomialDot_work]
    have hdegree : degree - channelCard + 1 ≤ t := by omega
    have hdot := Nat.mul_le_mul_left (5*q) hdegree
    have hweight := weightCounted_work_le k t degree
    omega
  · omega

/-- Both blocks are looked up once, and all required auxiliary degrees
then use scalar cyclic dot loops on these materialized blocks. -/
def channelQuery {N q width : ℕ} [NeZero q] (k t : ℕ)
    (left right : Prepared N q width) (word : Word N) (channelCard : ℕ) (target : Fin q) : ℤ × ℕ :=
  let a := readBlockCounted left word
  let b := readBlockCounted right word
  let rows := (List.range t).map (fun degree => lowTerm k t a.1 b.1 channelCard degree target)
  ((rows.map Prod.fst).sum, a.2 + b.2 + t + (rows.map Prod.snd).sum)

theorem channelQuery_value {N q width : ℕ} [NeZero q] (k t : ℕ)
    (left right : Prepared N q width) (word : Word N) (channelCard : ℕ)
    (p r : Polynomial (CyclicRing.Cyclic q))
    (hl : readBlock left word = extractedBlock (width := width) p)
    (hr : readBlock right word = extractedBlock (width := width) r)
    (ht : t ≤ width) (target : Fin q) :
    (channelQuery k t left right word channelCard target).1 =
      ∑ degree ∈ Finset.range t,
        if channelCard ≤ degree then (TensorContraction.residualWeight k t degree : ℤ) *
          ((p*r).coeff (degree-channelCard)) target else 0 := by
  unfold channelQuery
  simp only [readBlockCounted_value, List.map_map, Function.comp_def, hl, hr]
  rw [← List.sum_toFinset _ (List.nodup_range (n := t))]
  simp only [List.toFinset_range]
  apply Finset.sum_congr rfl
  intro degree hd
  exact lowTerm_value k t p r channelCard degree (by have := Finset.mem_range.mp hd; omega) target

theorem channelQuery_work_le {N q width : ℕ} [NeZero q] (k t : ℕ)
    (left right : Prepared N q width) (word : Word N) (channelCard : ℕ) (target : Fin q) :
    (channelQuery k t left right word channelCard target).2 ≤
      2*(2*N+1+q*width) + t + t*(5*q*t+weightWork k t+4) := by
  unfold channelQuery
  simp only [readBlockCounted_work, List.map_map, Function.comp_def]
  have hsum : ((List.range t).map (fun degree =>
      (lowTerm k t (readBlockCounted left word).1 (readBlockCounted right word).1
        channelCard degree target).2)).sum ≤ t*(5*q*t+weightWork k t+4) := by
    calc
      _ ≤ ((List.range t).map (fun _ => 5*q*t+weightWork k t+4)).sum := by
        exact List.sum_le_sum (fun degree hdegree =>
          lowTerm_work_le k t _ _ channelCard degree (List.mem_range.mp hdegree) target)
      _ = _ := by simp
  omega

/-- The list of channel sets is supplied by a direct capped generator.
This loop never constructs an uncapped powerset. The word constructor
is evaluated once per channel, before the two shared-table lookups. -/
def queryChannels {N k q width : ℕ} [NeZero q] (t : ℕ)
    (channels : List (Finset (Fin k))) (keys : Finset (Fin k) → Word N)
    (left right : Prepared N q width) (target : Fin q) : ℤ × ℕ :=
  let rows := channels.map (fun C => channelQuery k t left right (keys C) C.card target)
  ((rows.map Prod.fst).sum, (rows.map Prod.snd).sum)

theorem queryChannels_value {N k q width : ℕ} [NeZero q] (t : ℕ)
    (channels : List (Finset (Fin k))) (hnd : channels.Nodup)
    (keys : Finset (Fin k) → Word N) (left right : Prepared N q width)
    (p r : Finset (Fin k) → Polynomial (CyclicRing.Cyclic q))
    (hl : ∀ C ∈ channels, readBlock left (keys C) = extractedBlock (width := width) (p C))
    (hr : ∀ C ∈ channels, readBlock right (keys C) = extractedBlock (width := width) (r C))
    (ht : t ≤ width) (target : Fin q) :
    (queryChannels t channels keys left right target).1 =
      ∑ C ∈ channels.toFinset, ∑ degree ∈ Finset.range t,
        if C.card ≤ degree then (TensorContraction.residualWeight k t degree : ℤ) *
          (((p C)*(r C)).coeff (degree-C.card)) target else 0 := by
  unfold queryChannels
  simp only [List.map_map, Function.comp_def]
  rw [← List.sum_toFinset _ hnd]
  apply Finset.sum_congr rfl
  intro C hC
  exact channelQuery_value k t left right (keys C) C.card (p C) (r C)
    (hl C (List.mem_toFinset.mp hC)) (hr C (List.mem_toFinset.mp hC)) ht target

theorem queryChannels_work_le {N k q width : ℕ} [NeZero q] (t : ℕ)
    (channels : List (Finset (Fin k))) (keys : Finset (Fin k) → Word N)
    (left right : Prepared N q width) (target : Fin q) :
    (queryChannels t channels keys left right target).2 ≤
      channels.length * (2*(2*N+1+q*width) + t + t*(5*q*t+weightWork k t+4)) := by
  unfold queryChannels
  simp only [List.map_map, Function.comp_def]
  calc
    _ ≤ (channels.map (fun _ => 2*(2*N+1+q*width)+t+t*(5*q*t+weightWork k t+4))).sum := by
      exact List.sum_le_sum (fun C _ => channelQuery_work_le k t left right (keys C) C.card target)
    _ = _ := by simp

/-- A literal scan of stored middle-position addresses. -/
def imageScan {N k : ℕ} (embedding : Vector (Fin N) k) (point : Fin N) :
    List (Fin k) → Bool × ℕ
  | [] => (false,1)
  | j :: js => let tail := imageScan embedding point js
              (decide (embedding.get j = point) || tail.1,tail.2+3)

@[simp] theorem imageScan_value {N k : ℕ} (embedding : Vector (Fin N) k) (point : Fin N)
    (js : List (Fin k)) :
    (imageScan embedding point js).1 = true ↔ ∃ j ∈ js, embedding.get j = point := by
  induction js with
  | nil => simp [imageScan]
  | cons j js ih => simp [imageScan,ih]

@[simp] theorem imageScan_work {N k : ℕ} (embedding : Vector (Fin N) k) (point : Fin N)
    (js : List (Fin k)) : (imageScan embedding point js).2 = 3*js.length+1 := by
  induction js with
  | nil => rfl
  | cons j js ih => simp only [imageScan,ih,List.length_cons]; omega

/-- Explicitly materialized masks use bounded scans; no opaque Word
application occurs in the actual trie address traversal. -/
def imageMask {N k : ℕ} (embedding : Vector (Fin N) k) (js : List (Fin k)) :
    Vector Bool N × ℕ :=
  (Vector.ofFn (fun point => (imageScan embedding point js).1), N*(3*js.length+2))

theorem imageMask_value {N k : ℕ} (embedding : Vector (Fin N) k) (js : List (Fin k))
    (i : Fin N) : (imageMask embedding js).1.get i = true ↔
      ∃ j ∈ js, embedding.get j = i := by
  simp [imageMask]

def physicalKey {N k : ℕ} (embedding : Vector (Fin N) k)
    (ordinary : Vector (Fin 4) N) (cs : List (Fin k)) : ArrayKeys.Key N × ℕ :=
  let distinguished := imageMask embedding (List.finRange k)
  let channel := imageMask embedding cs
  let key := ArrayKeys.queryKeyCounted ordinary distinguished.1 channel.1
  (key.1,distinguished.2+channel.2+key.2)

theorem physicalKey_work_le {N k : ℕ} (embedding : Vector (Fin N) k)
    (ordinary : Vector (Fin 4) N) (cs : List (Fin k)) (hcs : cs.length ≤ k) :
    (physicalKey embedding ordinary cs).2 ≤ N*(6*k+8) := by
  simp only [physicalKey,imageMask,List.length_finRange,
    ArrayKeys.queryKey_work]
  nlinarith

theorem physicalKey_refine {L k : ℕ} (e : Fin k ↪o Fin (2*L))
    (outside : Fin (2*L) → Fin 4) (embedding : Vector (Fin (2*L)) k)
    (ordinary : Vector (Fin 4) (2*L))
    (he : ∀ j, embedding.get j = e j) (ho : ∀ i, ordinary.get i = outside i)
    (cs : List (Fin k)) :
    ArrayKeys.toWord (physicalKey embedding ordinary cs).1 =
      CachedLowIdentity.cacheWord e outside cs.toFinset := by
  funext i
  simp only [physicalKey,ArrayKeys.queryKeyCounted,ArrayKeys.queryKey_refine]
  have hd : (imageMask embedding (List.finRange k)).1.get i = true ↔
      ∃ j, e j = i := by simp only [imageMask_value,List.mem_finRange,true_and,he]
  have hc : (imageMask embedding cs).1.get i = true ↔
      ∃ j ∈ cs, e j = i := by simp only [imageMask_value,he]
  by_cases hi : ∃ j, e j = i
  · obtain ⟨j,rfl⟩ := hi
    have hd' : (imageMask embedding (List.finRange k)).1.get (e j) = true := hd.mpr ⟨j,rfl⟩
    have hc' : (imageMask embedding cs).1.get (e j) = true ↔ j ∈ cs := by
      rw [hc]
      exact ⟨fun ⟨a,ha,heq⟩ => by simpa only [e.injective heq] using ha,
        fun hj => ⟨j,hj,rfl⟩⟩
    rw [CachedLowIdentity.cacheWord_at]
    by_cases hj : j ∈ cs
    · simp [hc'.mpr hj,hj]
    · have hn : (imageMask embedding cs).1.get (e j) = false :=
        Bool.eq_false_iff.mpr (fun ht => hj (hc'.mp ht))
      simp [hd',hn,hj]
  · have hd' : (imageMask embedding (List.finRange k)).1.get i = false :=
      Bool.eq_false_iff.mpr (fun ht => hi (hd.mp ht))
    have hc' : (imageMask embedding cs).1.get i = false :=
      Bool.eq_false_iff.mpr (fun ht => by obtain ⟨j,_,heq⟩ := hc.mp ht; exact hi ⟨j,heq⟩)
    have hnot : i ∉ HighBoxDP.embeddedSupport e := by simpa [HighBoxDP.embeddedSupport] using hi
    rw [CachedLowIdentity.cacheWord_outside e outside cs.toFinset i hnot]
    simp only [hd',hc',Bool.false_eq_true,if_false,ho]
    rfl

def readKeyBlockCounted {N q width : ℕ} (table : Prepared N q width)
    (key : ArrayKeys.Key N) : DenseVector q width × ℕ :=
  let r := ArrayKeys.read table key
  (r.1.getD (zeroBlock q width),r.2+q*width)

@[simp] theorem readKeyBlockCounted_eq {N q width : ℕ} (table : Prepared N q width)
    (key : ArrayKeys.Key N) :
    readKeyBlockCounted table key = readBlockCounted table (ArrayKeys.toWord key) := by
  apply Prod.ext
  · simp [readKeyBlockCounted,readBlockCounted,ArrayKeys.read_value]
  · simp [readKeyBlockCounted,readBlockCounted]
    omega

/-- This production loop uses the materialized vector key directly. -/
def channelKeyQuery {N q width : ℕ} [NeZero q] (k t : ℕ)
    (left right : Prepared N q width) (key : ArrayKeys.Key N) (channelCard : ℕ)
    (target : Fin q) : ℤ × ℕ :=
  let a := readKeyBlockCounted left key
  let b := readKeyBlockCounted right key
  let rows := (List.range t).map (fun degree => lowTerm k t a.1 b.1 channelCard degree target)
  ((rows.map Prod.fst).sum,a.2+b.2+t+(rows.map Prod.snd).sum)

@[simp] theorem channelKeyQuery_eq {N q width : ℕ} [NeZero q] (k t : ℕ)
    (left right : Prepared N q width) (key : ArrayKeys.Key N) (channelCard : ℕ)
    (target : Fin q) :
    channelKeyQuery k t left right key channelCard target =
      channelQuery k t left right (ArrayKeys.toWord key) channelCard target := by
  simp [channelKeyQuery,channelQuery]

def physicalQueryChannels {N k q width : ℕ} [NeZero q] (t : ℕ)
    (channels : List (List (Fin k))) (embedding : Vector (Fin N) k)
    (ordinary : Vector (Fin 4) N) (left right : Prepared N q width) (target : Fin q) : ℤ × ℕ :=
  let rows := channels.map (fun cs =>
    let key := physicalKey embedding ordinary cs
    let query := channelKeyQuery k t left right key.1 cs.length target
    (query.1,key.2+query.2))
  ((rows.map Prod.fst).sum,(rows.map Prod.snd).sum)

theorem physicalQueryChannels_work_le {N k q width : ℕ} [NeZero q] (t : ℕ)
    (channels : List (List (Fin k))) (hc : ∀ cs ∈ channels, cs.length ≤ k)
    (embedding : Vector (Fin N) k)
    (ordinary : Vector (Fin 4) N) (left right : Prepared N q width) (target : Fin q) :
    (physicalQueryChannels t channels embedding ordinary left right target).2 ≤
      channels.length*(N*(6*k+8)+2*(2*N+1+q*width)+t+t*(5*q*t+weightWork k t+4)) := by
  unfold physicalQueryChannels
  simp only [List.map_map,Function.comp_def]
  calc
    _ ≤ (channels.map (fun _ => N*(6*k+8)+2*(2*N+1+q*width)+t+
        t*(5*q*t+weightWork k t+4))).sum := by
      apply List.sum_le_sum
      intro cs hcs
      rw [channelKeyQuery_eq]
      have hkey := physicalKey_work_le embedding ordinary cs (hc cs hcs)
      have hquery := channelQuery_work_le k t left right
        (ArrayKeys.toWord (physicalKey embedding ordinary cs).1) cs.length target
      omega
    _ = _ := by simp

/-- Semantic refinement of the array-key query. Each actual member list
is retained as metadata; no noncomputable Finset-to-list extraction occurs. -/
theorem physicalQueryChannels_value_eq {L k q width : ℕ} [NeZero q] (t : ℕ)
    (channels : List (List (Fin k))) (hcs : ∀ cs ∈ channels, cs.Nodup)
    (e : Fin k ↪o Fin (2*L)) (outside : Fin (2*L) → Fin 4)
    (embedding : Vector (Fin (2*L)) k) (ordinary : Vector (Fin 4) (2*L))
    (he : ∀ j, embedding.get j = e j) (ho : ∀ i, ordinary.get i = outside i)
    (left right : Prepared (2*L) q width) (target : Fin q) :
    (physicalQueryChannels t channels embedding ordinary left right target).1 =
      (queryChannels t (channels.map List.toFinset) (CachedLowIdentity.cacheWord e outside)
        left right target).1 := by
  unfold physicalQueryChannels queryChannels
  simp only [List.map_map,Function.comp_def,channelKeyQuery_eq]
  congr 1
  apply List.map_congr_left
  intro cs hmem
  rw [physicalKey_refine e outside embedding ordinary he ho cs,
    List.toFinset_card_of_nodup (hcs cs hmem)]

abbrev SourceCaches (L q width : ℕ) := Prepared (2*L) q width × Prepared (2*L) q width

/-- Preprocessing is a separate operation, shared by every output-pair
query for this source run. -/
noncomputable def prepareSources {L m t q width : ℕ} [NeZero q]
    (X Y : CompleteThinProduct.SourceWord L → CyclicRing.Cyclic q) :
    SourceCaches L q width × ℕ :=
  let a := prepareEncoded (m := m) (t := t) (width := width) true
    (CachedLowIdentity.sourceCacheForms L true) (CachedLowIdentity.sourceCacheInput L true X)
  let b := prepareEncoded (m := m) (t := t) (width := width) false
    (CachedLowIdentity.sourceCacheForms L false) (CachedLowIdentity.sourceCacheInput L false Y)
  ((a.1,b.1),a.2+b.2)

theorem prepareSources_work_le {L m t q width : ℕ} [NeZero q] (hw : 1 ≤ width)
    (X Y : CompleteThinProduct.SourceWord L → CyclicRing.Cyclic q) :
    (prepareSources (m := m) (t := t) (width := width) X Y).2 ≤
      2*retainedLeafCount L m t*preparationFactor L q width := by
  unfold prepareSources
  dsimp only
  have hl := prepareEncoded_work_le (L := L) (m := m) (t := t) (q := q) hw true
    (CachedLowIdentity.sourceCacheForms L true) (CachedLowIdentity.sourceCacheInput L true X)
  have hr := prepareEncoded_work_le (L := L) (m := m) (t := t) (q := q) hw false
    (CachedLowIdentity.sourceCacheForms L false) (CachedLowIdentity.sourceCacheInput L false Y)
  nlinarith

theorem prepared_left_read {L m t q width : ℕ} [NeZero q]
    (X Y : CompleteThinProduct.SourceWord L → CyclicRing.Cyclic q)
    (word : Word (2*L)) (hw : Retained L m t word) :
    readBlock (prepareSources (m := m) (t := t) (width := width) X Y).1.1 word =
      extractedBlock (width := width) (CachedLowIdentity.leftCachePolynomial X word) := by
  unfold prepareSources
  rw [read_prepareEncoded_block true _ _ word hw,CachedLowIdentity.left_cache_tensorValue]

theorem prepared_right_read {L m t q width : ℕ} [NeZero q]
    (X Y : CompleteThinProduct.SourceWord L → CyclicRing.Cyclic q)
    (word : Word (2*L)) (hw : Retained L m t word) :
    readBlock (prepareSources (m := m) (t := t) (width := width) X Y).1.2 word =
      extractedBlock (width := width) (CachedLowIdentity.rightCachePolynomial Y word) := by
  unfold prepareSources
  rw [read_prepareEncoded_block false _ _ word hw,CachedLowIdentity.right_cache_tensorValue]

/-- Production query consumes already prepared tables. -/
def querySources {L k q width : ℕ} [NeZero q] (t : ℕ)
    (channels : List (List (Fin k))) (embedding : Vector (Fin (2*L)) k)
    (ordinary : Vector (Fin 4) (2*L)) (cache : SourceCaches L q width) (target : Fin q) : ℤ × ℕ :=
  physicalQueryChannels t channels embedding ordinary cache.1 cache.2 target

theorem querySources_correct {L k m t q width : ℕ} [NeZero q]
    (channels : List (List (Fin k)))
    (hcs : ∀ cs ∈ channels, cs.Nodup)
    (hnd : (channels.map List.toFinset).Nodup)
    (hfamily : (channels.map List.toFinset).toFinset =
      (Finset.univ : Finset (Fin k)).powerset.filter (fun C => C.card ≤ t))
    (e : Fin k ↪o Fin (2*L)) (outside : Fin (2*L) → Fin 4)
    (embedding : Vector (Fin (2*L)) k) (ordinary : Vector (Fin 4) (2*L))
    (he : ∀ j, embedding.get j = e j) (ho : ∀ i, ordinary.get i = outside i)
    (hleft : ((HighBoxDP.embeddedSupport e).filter (fun i => i.val < L)).card ≤ m)
    (hright : ((HighBoxDP.embeddedSupport e).filter (fun i => L ≤ i.val)).card ≤ m)
    (X Y : CompleteThinProduct.SourceWord L → CyclicRing.Cyclic q)
    (ht : t ≤ width) (target : Fin q) :
    (querySources t channels embedding ordinary
      (prepareSources (m := m) (t := t) (width := width) X Y).1 target).1 =
      (CompleteThinProduct.lowQuery (t := t) e outside X Y
        CompleteThinProduct.sourceF CompleteThinProduct.sourceG) target := by
  unfold querySources
  rw [physicalQueryChannels_value_eq t channels hcs e outside embedding ordinary he ho]
  have hcap : ∀ C ∈ channels.map List.toFinset, C.card ≤ t := by
    intro C hC
    have := List.mem_toFinset.mpr hC
    rw [hfamily] at this
    exact (Finset.mem_filter.mp this).2
  rw [queryChannels_value t _ hnd _ _ _
    (fun C => CachedLowIdentity.leftCachePolynomial X (CachedLowIdentity.cacheWord e outside C))
    (fun C => CachedLowIdentity.rightCachePolynomial Y (CachedLowIdentity.cacheWord e outside C))
    (fun C hC => prepared_left_read X Y _
      (CachedLowIdentity.cacheWord_retained e outside C hleft hright (hcap C hC)))
    (fun C hC => prepared_right_read X Y _
      (CachedLowIdentity.cacheWord_retained e outside C hleft hright (hcap C hC))) ht target,
    hfamily]
  exact (CachedLowIdentity.lowQuery_cyclic_coefficient e outside X Y target).symm

/-- An explicit polynomial bound for every physical-key channel query. -/
theorem channelCost_poly {N k t q width : ℕ} (hq : 1 ≤ q)
    (hk : k ≤ N) (ht : t ≤ N) (hw : width ≤ N+1) :
    N*(6*k+8)+2*(2*N+1+q*width)+t+t*(5*q*t+weightWork k t+4) ≤
      40*q*(N+1)^2 := by
  have hs : 1 ≤ N+1 := by omega
  have hsq : N+1 ≤ (N+1)^2 := by nlinarith
  have hkey : N*(6*k+8) ≤ 14*q*(N+1)^2 := by
    calc
      _ ≤ (N+1)*(14*(N+1)) := Nat.mul_le_mul (by omega) (by omega)
      _ = 14*(N+1)^2 := by ring
      _ ≤ _ := by nlinarith
  have hplain : 2*N+1 ≤ q*(2*N+1) := by nlinarith
  have hwidth : q*width ≤ q*(N+1) := Nat.mul_le_mul_left q hw
  have hread : 2*(2*N+1+q*width) ≤ 6*q*(N+1)^2 := by
    calc
      _ ≤ 6*q*(N+1) := by nlinarith
      _ ≤ _ := Nat.mul_le_mul_left (6*q) hsq
  have htest : t ≤ q*(N+1)^2 := by nlinarith
  have hweight : weightWork k t+4 ≤ 14*(N+1) := by unfold weightWork; omega
  have hdot : 5*q*t ≤ 5*q*(N+1) := Nat.mul_le_mul_left (5*q) (by omega)
  have hterm : 5*q*t+weightWork k t+4 ≤ 19*q*(N+1) := by nlinarith
  have hloop : t*(5*q*t+weightWork k t+4) ≤ 19*q*(N+1)^2 := by
    calc
      _ ≤ (N+1)*(19*q*(N+1)) := Nat.mul_le_mul (by omega) hterm
      _ = _ := by ring
  nlinarith

theorem querySources_work_poly {L k q width : ℕ} [NeZero q] (t : ℕ)
    (channels : List (List (Fin k))) (hc : ∀ cs ∈ channels, cs.length ≤ k)
    (embedding : Vector (Fin (2*L)) k) (ordinary : Vector (Fin 4) (2*L))
    (cache : SourceCaches L q width) (target : Fin q)
    (hk : k ≤ 2*L) (ht : t ≤ 2*L) (hw : width ≤ 2*L+1) :
    (querySources t channels embedding ordinary cache target).2 ≤
      channels.length * (40*q*(2*L+1)^2) := by
  exact (physicalQueryChannels_work_le t channels hc embedding ordinary cache.1 cache.2 target).trans
    (Nat.mul_le_mul_left channels.length (channelCost_poly (Nat.pos_of_neZero q) hk ht hw))

/-- Integer run r is represented by the array index r+m. -/
def sourceRun {m : ℕ} (i : Fin (2*m+1)) : ℤ := (i.val : ℤ)-(m : ℤ)

abbrev RunCaches (L m q width : ℕ) := Vector (SourceCaches L q width) (2*m+1)

/-- Each run is prepared once into a vector before any output-pair query.
Both sides always use this same index; there is no Cartesian run join. -/
noncomputable def prepareRunSources {L m t q width : ℕ} [NeZero q]
    (X Y : Fin (2*m+1) → CompleteThinProduct.SourceWord L → CyclicRing.Cyclic q) :
    RunCaches L m q width × ℕ :=
  let records := Vector.ofFn (fun i => prepareSources (m := m) (t := t) (width := width) (X i) (Y i))
  (records.map Prod.fst,(records.toList.map Prod.snd).sum)

theorem prepareRunSources_get {L m t q width : ℕ} [NeZero q]
    (X Y : Fin (2*m+1) → CompleteThinProduct.SourceWord L → CyclicRing.Cyclic q)
    (i : Fin (2*m+1)) :
    (prepareRunSources (t := t) (width := width) X Y).1.get i =
      (prepareSources (m := m) (t := t) (width := width) (X i) (Y i)).1 := by
  simp [prepareRunSources,Vector.get_ofFn]

theorem prepareRunSources_work_le {L m t q width : ℕ} [NeZero q] (hw : 1 ≤ width)
    (X Y : Fin (2*m+1) → CompleteThinProduct.SourceWord L → CyclicRing.Cyclic q) :
    (prepareRunSources (t := t) (width := width) X Y).2 ≤
      (2*m+1)*(2*retainedLeafCount L m t*preparationFactor L q width) := by
  unfold prepareRunSources
  dsimp only
  rw [Vector.toList_ofFn,List.ofFn_eq_map]
  simp only [List.map_map,Function.comp_def]
  calc
    _ ≤ ((List.finRange (2*m+1)).map
        (fun _ => 2*retainedLeafCount L m t*preparationFactor L q width)).sum := by
      exact List.sum_le_sum (fun i _ => prepareSources_work_le hw (X i) (Y i))
    _ = _ := by simp

/-- Same-run LOW residual query on the already prepared vector. -/
def queryRuns {L m k q width : ℕ} [NeZero q] (t : ℕ)
    (channels : List (List (Fin k))) (embedding : Vector (Fin (2*L)) k)
    (ordinary : Vector (Fin 4) (2*L)) (caches : RunCaches L m q width) (target : Fin q) : ℤ × ℕ :=
  let records := (List.finRange (2*m+1)).map (fun i =>
    querySources t channels embedding ordinary (caches.get i) target)
  ((records.map Prod.fst).sum, (2*m+1)+(records.map Prod.snd).sum)

theorem queryRuns_work_poly {L m k q width : ℕ} [NeZero q] (t : ℕ)
    (channels : List (List (Fin k))) (hc : ∀ cs ∈ channels, cs.length ≤ k)
    (embedding : Vector (Fin (2*L)) k) (ordinary : Vector (Fin 4) (2*L))
    (caches : RunCaches L m q width) (target : Fin q)
    (hk : k ≤ 2*L) (ht : t ≤ 2*L) (hw : width ≤ 2*L+1) :
    (queryRuns t channels embedding ordinary caches target).2 ≤
      (2*m+1)*(1+channels.length*(40*q*(2*L+1)^2)) := by
  unfold queryRuns
  simp only [List.map_map,Function.comp_def]
  have hsum : ((List.finRange (2*m+1)).map (fun i =>
      (querySources t channels embedding ordinary (caches.get i) target).2)).sum ≤
        (2*m+1)*(channels.length*(40*q*(2*L+1)^2)) := by
    calc
      _ ≤ ((List.finRange (2*m+1)).map (fun _ => channels.length*(40*q*(2*L+1)^2))).sum := by
        exact List.sum_le_sum (fun i _ => querySources_work_poly t channels hc embedding ordinary
          (caches.get i) target hk ht hw)
      _ = _ := by simp
  nlinarith

theorem sum_sourceRun {m : ℕ} (f : ℤ → ℤ) :
    (∑ i : Fin (2*m+1), f (sourceRun i)) = ∑ r ∈ Finset.Icc (-(m:ℤ)) (m:ℤ), f r := by
  apply Finset.sum_bij (fun i _ => sourceRun i)
  · intro i hi
    simp only [Finset.mem_Icc,sourceRun]
    have := i.isLt
    constructor <;> omega
  · intro i hi j hj heq
    apply Fin.ext
    simp only [sourceRun] at heq
    omega
  · intro r hr
    have hr' := Finset.mem_Icc.mp hr
    refine ⟨⟨(r+(m:ℤ)).toNat,by omega⟩,Finset.mem_univ _,?_⟩
    simp only [sourceRun]
    omega
  · intro i hi
    rfl

/-- The actual materialized cache query equals the defined same-degree
run LOW residual for the source query data. -/
theorem queryRuns_correct {L m k t q width : ℕ} [NeZero q]
    (channels : List (List (Fin (2*m))))
    (hcs : ∀ cs ∈ channels, cs.Nodup)
    (hnd : (channels.map List.toFinset).Nodup)
    (hfamily : (channels.map List.toFinset).toFinset =
      (Finset.univ : Finset (Fin (2*m))).powerset.filter (fun C => C.card ≤ t))
    (d : CompleteThinProduct.SourceQueryData L m k (CyclicRing.Cyclic q))
    (embedding : Vector (Fin (2*L)) (2*m)) (ordinary : Vector (Fin 4) (2*L))
    (he : ∀ j, embedding.get j = d.embedding j) (ho : ∀ i, ordinary.get i = d.outside i)
    (ht : t ≤ width) (target : Fin q) :
    (queryRuns (m := m) t channels embedding ordinary
      (prepareRunSources (m := m) (t := t) (width := width)
        (fun i => d.leftRun (sourceRun i)) (fun i => d.rightRun (sourceRun i))).1 target).1 =
      d.residual t target := by
  unfold queryRuns
  simp only [List.map_map,Function.comp_def,prepareRunSources_get]
  have hterm (i : Fin (2*m+1)) :
      (querySources t channels embedding ordinary
        (prepareSources (m := m) (t := t) (width := width)
          (d.leftRun (sourceRun i)) (d.rightRun (sourceRun i))).1 target).1 =
        d.lowRun t (sourceRun i) target := by
    exact querySources_correct channels hcs hnd hfamily d.embedding d.outside embedding ordinary
      he ho d.left_cap d.right_cap _ _ ht target
  simp_rw [hterm]
  rw [←List.ofFn_eq_map,List.sum_ofFn]
  exact (sum_sourceRun (m := m) (fun r => d.lowRun t r target)).trans
    (CyclicRing.sum_coeff _ _ target).symm

/-- Direct capped generation and one physical LOW query, jointly counted. -/
def queryLow {L k q width : ℕ} [NeZero q] (t : ℕ)
    (embedding : Vector (Fin (2*L)) k) (ordinary : Vector (Fin 4) (2*L))
    (cache : SourceCaches L q width) (target : Fin q) : ℤ × ℕ :=
  let generated := LowChannelEnumeration.generate (List.finRange k) t
  let answer := querySources t generated.members embedding ordinary cache target
  (answer.1,8*k+generated.work+answer.2)

@[simp] theorem queryLow_value {L k q width : ℕ} [NeZero q] (t : ℕ)
    (embedding : Vector (Fin (2*L)) k) (ordinary : Vector (Fin 4) (2*L))
    (cache : SourceCaches L q width) (target : Fin q) :
    (queryLow t embedding ordinary cache target).1 =
      (querySources t (LowChannelEnumeration.members k t) embedding ordinary cache target).1 := rfl

theorem channelBall_pos (k t : ℕ) : 1 ≤ CacheCardinality.channelBall k t := by
  rw [←LowChannelEnumeration.members_length]
  have hnil : [] ∈ LowChannelEnumeration.members k t := by
    exact LowChannelEnumeration.nil_mem_generate _ _
  have : (LowChannelEnumeration.members k t).length ≠ 0 := by
    intro hz
    have hempty := List.length_eq_zero_iff.mp hz
    simp only [hempty,List.not_mem_nil] at hnil
  omega

theorem generated_family (k t : ℕ) :
    ((LowChannelEnumeration.members k t).map List.toFinset).toFinset =
      (Finset.univ : Finset (Fin k)).powerset.filter (fun C => C.card ≤ t) := by
  simpa only [LowChannelEnumeration.sets,Finset.powerset_univ] using
    LowChannelEnumeration.sets_toFinset k t

theorem queryLow_correct {L k m t q width : ℕ} [NeZero q]
    (e : Fin k ↪o Fin (2*L)) (outside : Fin (2*L) → Fin 4)
    (embedding : Vector (Fin (2*L)) k) (ordinary : Vector (Fin 4) (2*L))
    (he : ∀ j, embedding.get j = e j) (ho : ∀ i, ordinary.get i = outside i)
    (hleft : ((HighBoxDP.embeddedSupport e).filter (fun i => i.val < L)).card ≤ m)
    (hright : ((HighBoxDP.embeddedSupport e).filter (fun i => L ≤ i.val)).card ≤ m)
    (X Y : CompleteThinProduct.SourceWord L → CyclicRing.Cyclic q)
    (ht : t ≤ width) (target : Fin q) :
    (queryLow t embedding ordinary (prepareSources (m := m) (t := t) (width := width) X Y).1 target).1 =
      (CompleteThinProduct.lowQuery (t := t) e outside X Y
        CompleteThinProduct.sourceF CompleteThinProduct.sourceG) target := by
  rw [queryLow_value]
  exact querySources_correct _ (LowChannelEnumeration.member_nodup k t)
    (LowChannelEnumeration.sets_nodup k t) (generated_family k t)
    e outside embedding ordinary he ho hleft hright X Y ht target

theorem queryLow_work_le {L k q width : ℕ} [NeZero q] (t : ℕ)
    (embedding : Vector (Fin (2*L)) k) (ordinary : Vector (Fin 4) (2*L))
    (cache : SourceCaches L q width) (target : Fin q)
    (hk : k ≤ 2*L) (ht : t ≤ 2*L) (hw : width ≤ 2*L+1) :
    (queryLow t embedding ordinary cache target).2 ≤
      (16*(k+1)+40*(2*L+1)^2)*q*CacheCardinality.channelBall k t := by
  have hg := LowChannelEnumeration.work_le k t
  have hquery := querySources_work_poly t (LowChannelEnumeration.members k t)
    (LowChannelEnumeration.member_length_le_dimension k t) embedding ordinary cache target hk ht hw
  rw [LowChannelEnumeration.members_length] at hquery
  dsimp only [queryLow]
  change LowChannelEnumeration.work k t +
    (querySources t (LowChannelEnumeration.members k t) embedding ordinary cache target).2 ≤ _
  have hq : 1 ≤ q := Nat.pos_of_neZero q
  nlinarith

/-- Direct capped generation is shared by all runs in this actual query. -/
def queryLowRuns {L m k q width : ℕ} [NeZero q] (t : ℕ)
    (embedding : Vector (Fin (2*L)) k) (ordinary : Vector (Fin 4) (2*L))
    (caches : RunCaches L m q width) (target : Fin q) : ℤ × ℕ :=
  let generated := LowChannelEnumeration.generate (List.finRange k) t
  let answer := queryRuns t generated.members embedding ordinary caches target
  (answer.1,8*k+generated.work+answer.2)

@[simp] theorem queryLowRuns_value {L m k q width : ℕ} [NeZero q] (t : ℕ)
    (embedding : Vector (Fin (2*L)) k) (ordinary : Vector (Fin 4) (2*L))
    (caches : RunCaches L m q width) (target : Fin q) :
    (queryLowRuns t embedding ordinary caches target).1 =
      (queryRuns t (LowChannelEnumeration.members k t) embedding ordinary caches target).1 := rfl

theorem queryLowRuns_work_le {L m k q width : ℕ} [NeZero q] (t : ℕ)
    (embedding : Vector (Fin (2*L)) k) (ordinary : Vector (Fin 4) (2*L))
    (caches : RunCaches L m q width) (target : Fin q)
    (hk : k ≤ 2*L) (ht : t ≤ 2*L) (hw : width ≤ 2*L+1) :
    (queryLowRuns t embedding ordinary caches target).2 ≤
      (16*(k+1)+(2*m+1)*(1+40*(2*L+1)^2))*q*CacheCardinality.channelBall k t := by
  have hg := LowChannelEnumeration.work_le k t
  have hquery := queryRuns_work_poly t (LowChannelEnumeration.members k t)
    (LowChannelEnumeration.member_length_le_dimension k t) embedding ordinary caches target hk ht hw
  rw [LowChannelEnumeration.members_length] at hquery
  dsimp only [queryLowRuns]
  change LowChannelEnumeration.work k t +
    (queryRuns t (LowChannelEnumeration.members k t) embedding ordinary caches target).2 ≤ _
  have hq : 1 ≤ q := Nat.pos_of_neZero q
  have hb := channelBall_pos k t
  have hqb : 1 ≤ q*CacheCardinality.channelBall k t := by nlinarith
  have hgen : LowChannelEnumeration.work k t ≤ 16*(k+1)*q*CacheCardinality.channelBall k t := by
    calc
      _ ≤ 16*(k+1)*CacheCardinality.channelBall k t := hg
      _ ≤ _ := by nlinarith
  have hover : (2*m+1) ≤ (2*m+1)*q*CacheCardinality.channelBall k t := by nlinarith
  nlinarith

/-- Joint correctness and actual finite-loop work for all same-degree
runs, with no oracle output or contraction equality supplied as input. -/
theorem queryLowRuns_contract {L m k t q width : ℕ} [NeZero q]
    (d : CompleteThinProduct.SourceQueryData L m k (CyclicRing.Cyclic q))
    (embedding : Vector (Fin (2*L)) (2*m)) (ordinary : Vector (Fin 4) (2*L))
    (he : ∀ j, embedding.get j = d.embedding j) (ho : ∀ i, ordinary.get i = d.outside i)
    (ht : t ≤ width) (htm : t ≤ 2*m) (hm : m ≤ L) (hw : width ≤ 2*L+1) (target : Fin q) :
    let result := queryLowRuns t embedding ordinary
      (prepareRunSources (m := m) (t := t) (width := width)
        (fun i => d.leftRun (sourceRun i)) (fun i => d.rightRun (sourceRun i))).1 target
    result.1 = d.residual t target ∧ result.2 ≤
      (16*(2*m+1)+(2*m+1)*(1+40*(2*L+1)^2))*q*CacheCardinality.channelBall (2*m) t := by
  dsimp only
  constructor
  · rw [queryLowRuns_value]
    exact queryRuns_correct _ (LowChannelEnumeration.member_nodup (2*m) t)
      (LowChannelEnumeration.sets_nodup (2*m) t) (generated_family (2*m) t)
      d embedding ordinary he ho ht target
  · exact queryLowRuns_work_le t embedding ordinary _ target (by omega) (by omega) hw

/-- A producer-facing interface: the two stored arrays must refine the
proved cache polynomials on retained words. This is a local array-content
specification, independent of the requested output coefficient. -/
def SourceCacheValid {L m t q width : ℕ} [NeZero q]
    (X Y : CompleteThinProduct.SourceWord L → CyclicRing.Cyclic q)
    (cache : SourceCaches L q width) : Prop :=
  ∀ word, Retained L m t word →
    readBlock cache.1 word = extractedBlock (width := width) (CachedLowIdentity.leftCachePolynomial X word) ∧
    readBlock cache.2 word = extractedBlock (width := width) (CachedLowIdentity.rightCachePolynomial Y word)

theorem prepareSources_valid {L m t q width : ℕ} [NeZero q]
    (X Y : CompleteThinProduct.SourceWord L → CyclicRing.Cyclic q) :
    SourceCacheValid (m := m) (t := t) X Y
      (prepareSources (m := m) (t := t) (width := width) X Y).1 := by
  intro word hw
  exact ⟨prepared_left_read X Y word hw,prepared_right_read X Y word hw⟩

theorem querySources_correct_of_valid {L k m t q width : ℕ} [NeZero q]
    (channels : List (List (Fin k)))
    (hcs : ∀ cs ∈ channels, cs.Nodup)
    (hnd : (channels.map List.toFinset).Nodup)
    (hfamily : (channels.map List.toFinset).toFinset =
      (Finset.univ : Finset (Fin k)).powerset.filter (fun C => C.card ≤ t))
    (e : Fin k ↪o Fin (2*L)) (outside : Fin (2*L) → Fin 4)
    (embedding : Vector (Fin (2*L)) k) (ordinary : Vector (Fin 4) (2*L))
    (he : ∀ j, embedding.get j = e j) (ho : ∀ i, ordinary.get i = outside i)
    (hleft : ((HighBoxDP.embeddedSupport e).filter (fun i => i.val < L)).card ≤ m)
    (hright : ((HighBoxDP.embeddedSupport e).filter (fun i => L ≤ i.val)).card ≤ m)
    (X Y : CompleteThinProduct.SourceWord L → CyclicRing.Cyclic q)
    (cache : SourceCaches L q width) (hvalid : SourceCacheValid (m := m) (t := t) X Y cache)
    (ht : t ≤ width) (target : Fin q) :
    (querySources t channels embedding ordinary cache target).1 =
      (CompleteThinProduct.lowQuery (t := t) e outside X Y
        CompleteThinProduct.sourceF CompleteThinProduct.sourceG) target := by
  unfold querySources
  rw [physicalQueryChannels_value_eq t channels hcs e outside embedding ordinary he ho]
  have hcap : ∀ C ∈ channels.map List.toFinset, C.card ≤ t := by
    intro C hC
    have := List.mem_toFinset.mpr hC
    rw [hfamily] at this
    exact (Finset.mem_filter.mp this).2
  rw [queryChannels_value t _ hnd _ _ _
    (fun C => CachedLowIdentity.leftCachePolynomial X (CachedLowIdentity.cacheWord e outside C))
    (fun C => CachedLowIdentity.rightCachePolynomial Y (CachedLowIdentity.cacheWord e outside C))
    (fun C hC => (hvalid _
      (CachedLowIdentity.cacheWord_retained e outside C hleft hright (hcap C hC))).1)
    (fun C hC => (hvalid _
      (CachedLowIdentity.cacheWord_retained e outside C hleft hright (hcap C hC))).2) ht target,
    hfamily]
  exact (CachedLowIdentity.lowQuery_cyclic_coefficient e outside X Y target).symm

theorem queryLow_correct_of_valid {L k m t q width : ℕ} [NeZero q]
    (e : Fin k ↪o Fin (2*L)) (outside : Fin (2*L) → Fin 4)
    (embedding : Vector (Fin (2*L)) k) (ordinary : Vector (Fin 4) (2*L))
    (he : ∀ j, embedding.get j = e j) (ho : ∀ i, ordinary.get i = outside i)
    (hleft : ((HighBoxDP.embeddedSupport e).filter (fun i => i.val < L)).card ≤ m)
    (hright : ((HighBoxDP.embeddedSupport e).filter (fun i => L ≤ i.val)).card ≤ m)
    (X Y : CompleteThinProduct.SourceWord L → CyclicRing.Cyclic q)
    (cache : SourceCaches L q width) (hvalid : SourceCacheValid (m := m) (t := t) X Y cache)
    (ht : t ≤ width) (target : Fin q) :
    (queryLow t embedding ordinary cache target).1 =
      (CompleteThinProduct.lowQuery (t := t) e outside X Y
        CompleteThinProduct.sourceF CompleteThinProduct.sourceG) target := by
  rw [queryLow_value]
  exact querySources_correct_of_valid _ (LowChannelEnumeration.member_nodup k t)
    (LowChannelEnumeration.sets_nodup k t) (generated_family k t)
    e outside embedding ordinary he ho hleft hright X Y cache hvalid ht target

theorem queryLowRuns_contract_of_valid {L m k t q width : ℕ} [NeZero q]
    (d : CompleteThinProduct.SourceQueryData L m k (CyclicRing.Cyclic q))
    (embedding : Vector (Fin (2*L)) (2*m)) (ordinary : Vector (Fin 4) (2*L))
    (he : ∀ j, embedding.get j = d.embedding j) (ho : ∀ i, ordinary.get i = d.outside i)
    (caches : RunCaches L m q width)
    (hvalid : ∀ i, SourceCacheValid (m := m) (t := t)
      (d.leftRun (sourceRun i)) (d.rightRun (sourceRun i)) (caches.get i))
    (ht : t ≤ width) (htm : t ≤ 2*m) (hm : m ≤ L) (hw : width ≤ 2*L+1) (target : Fin q) :
    let result := queryLowRuns t embedding ordinary caches target
    result.1 = d.residual t target ∧ result.2 ≤
      (16*(2*m+1)+(2*m+1)*(1+40*(2*L+1)^2))*q*CacheCardinality.channelBall (2*m) t := by
  dsimp only
  constructor
  · rw [queryLowRuns_value]
    unfold queryRuns
    simp only [List.map_map,Function.comp_def]
    have hterm (i : Fin (2*m+1)) :
        (querySources t (LowChannelEnumeration.members (2*m) t) embedding ordinary
          (caches.get i) target).1 = d.lowRun t (sourceRun i) target :=
      querySources_correct_of_valid _ (LowChannelEnumeration.member_nodup (2*m) t)
        (LowChannelEnumeration.sets_nodup (2*m) t) (generated_family (2*m) t)
        d.embedding d.outside embedding ordinary he ho d.left_cap d.right_cap _ _ _ (hvalid i) ht target
    simp_rw [hterm]
    rw [←List.ofFn_eq_map,List.sum_ofFn]
    exact (sum_sourceRun (m := m) (fun r => d.lowRun t r target)).trans
      (CyclicRing.sum_coeff _ _ target).symm
  · exact queryLowRuns_work_le t embedding ordinary caches target (by omega) (by omega) hw

/-- Factorial temporaries used by the executable binomial constructor
have polynomially many bits in the physical query dimension. -/
theorem factorial_temporary_bound (B n : ℕ) (hn : n ≤ B) :
    (factorialCounted n).1 ≤ 2^((B+1)^2) := by
  rw [factorialCounted_value]
  have htwo : ∀ b : ℕ, b+1 ≤ 2^(b+1) := by
    intro b
    induction b with
    | zero => norm_num
    | succ b ih =>
        rw [show b+1+1 = (b+1)+1 by omega,pow_succ]
        nlinarith
  have hbase : n ≤ 2^(B+1) := by have := htwo B; omega
  calc
    n.factorial ≤ n^n := Nat.factorial_le_pow n
    _ ≤ (2^(B+1))^n := Nat.pow_le_pow_left hbase n
    _ = 2^((B+1)*n) := by rw [pow_mul]
    _ ≤ 2^((B+1)^2) := by
      gcongr
      · decide
      · rw [pow_two]
        exact Nat.mul_le_mul_left (B+1) (by omega)

/-- This bound covers the larger factorial denominator as well as its
operands. The actual arithmetic adapter must price these multiword values. -/
theorem weight_factorial_temporaries (k t degree : ℕ) :
    let B := (k+t+2)^2
    let n := k-degree-1
    let h := t-degree-1
    (factorialCounted n).1 ≤ 2^B ∧
    (factorialCounted h).1 ≤ 2^B ∧
    (factorialCounted (n-h)).1 ≤ 2^B ∧
    (factorialCounted h).1*(factorialCounted (n-h)).1 ≤ 2^(2*B) := by
  dsimp only
  have hn := factorial_temporary_bound (k+t+1) (k-degree-1) (by omega)
  have hh := factorial_temporary_bound (k+t+1) (t-degree-1) (by omega)
  have hr := factorial_temporary_bound (k+t+1) (k-degree-1-(t-degree-1)) (by omega)
  have hm : (factorialCounted (t-degree-1)).1*
      (factorialCounted (k-degree-1-(t-degree-1))).1 ≤ 2^(2*(k+t+2)^2) := by
    calc
      _ ≤ 2^((k+t+2)^2)*2^((k+t+2)^2) := Nat.mul_le_mul hh hr
      _ = _ := by rw [←pow_add]; congr 1; omega
  exact ⟨hn,hh,hr,hm⟩

/-- Conservative bit width for all factorial/binomial weight temporaries.
It is polynomial in k+t; it is deliberately not a single-word assertion. -/
def weightBitWidth (k t : ℕ) : ℕ := 2*(k+t+2)^2+2

/-- Site count multiplied by a quadratic multiword arithmetic unit.
The bit-array arithmetic adapter supplies this primitive-unit realization. -/
def weightBitBudget (k t : ℕ) : ℕ := weightWork k t*(weightBitWidth k t+1)^2

theorem weight_bit_work_le (k t degree : ℕ) :
    (weightCounted k t degree).2*(weightBitWidth k t+1)^2 ≤ weightBitBudget k t := by
  exact Nat.mul_le_mul_right _ (weightCounted_work_le k t degree)

/- A concrete run of the integer-array query. This is an execution audit,
not a substitute for the general correctness and work theorems above. -/
private def auditEmbedding : Vector (Fin 2) 2 := Vector.ofFn id
private def auditOrdinary : Vector (Fin 4) 2 := Vector.replicate 2 0
private def auditLeft : DenseVector 3 2 := Vector.ofFn (fun degree =>
  Vector.ofFn (fun residue => (if degree.val = 0 then ![2,3,5] else ![7,11,13]) residue))
private def auditRight : DenseVector 3 2 := Vector.ofFn (fun degree =>
  Vector.ofFn (fun residue => (if degree.val = 0 then ![17,19,23] else ![29,31,37]) residue))

#eval let channels := LowChannelEnumeration.members 2 2
  let keys := channels.map (fun cs => ArrayKeys.toWord (physicalKey auditEmbedding auditOrdinary cs).1)
  let left := (storePairs (keys.map (fun key => (key,auditLeft))) .empty).1
  let right := (storePairs (keys.map (fun key => (key,auditRight))) .empty).1
  queryLow (L := 1) 2 auditEmbedding auditOrdinary (left,right) 1

#print axioms read_storePairs
#print axioms prepareEncoded_work_le
#print axioms read_prepareEncoded_block
#print axioms normal_cache_localPolynomial
#print axioms opposite_cache_localPolynomial
#print axioms selectedDot_value
#print axioms polynomialDot_value
#print axioms weightCounted_value
#print axioms weightCounted_work_le
#print axioms physicalKey_refine
#print axioms querySources_correct
#print axioms prepareRunSources_work_le
#print axioms queryLowRuns_contract
#print axioms queryLowRuns_contract_of_valid
#print axioms factorial_temporary_bound
#print axioms weight_factorial_temporaries
#print axioms weight_bit_work_le

end ThinMatrix.CachedLowQuery
