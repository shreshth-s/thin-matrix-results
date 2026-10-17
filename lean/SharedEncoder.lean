import EncoderCorrectness
import CappedEnumeration

/-!
# Shared retained-prefix dense-array encoder

The program stores a dense suffix array at each retained prefix. To form
the next layer it tries six labels per parent, tests the actual caps, and
materializes each retained child by one local contraction of that parent
array. It neither evaluates a complete sweep separately for every leaf nor
enumerates the Cartesian word family before filtering.

`Dense` is a nested `Vector`, not an unevaluated function. `materialize`
constructs every suffix cell and `contract` reads the stored parent cells.
The tensor/sweep definitions occur only in proofs of the returned values.

The finite ledger counts local scalar arithmetic/read/write visits and
complete array cells. A `q*width` charge is explicit. Realizing that charge
as coefficient arithmetic requires the fixed sparse local-form adapter;
arbitrary multiplication in an arbitrary semiring is not claimed to cost
linear coefficient time. Machine indexing, coefficient bit costs, and the
source/Walsh embedding remain separate interfaces.
-/

namespace ThinMatrix.SharedEncoder

open CacheBounds CappedEnumeration
open scoped BigOperators

universe u
variable {R : Type u} [CommSemiring R]

abbrev Coordinates {n : ℕ} (dims : Fin n → ℕ) := EncoderCorrectness.Coordinates dims

/-- A genuinely stored heterogeneous dense array. -/
def Dense : (n : ℕ) → (Fin n → ℕ) → Type u
  | 0, _ => R
  | n + 1, dims => Vector (Dense n (fun i => dims i.succ)) (dims 0)

def read : (n : ℕ) → (dims : Fin n → ℕ) → Dense (R := R) n dims → Coordinates dims → R
  | 0, _, data, _ => data
  | n + 1, dims, data, a => read n (fun i => dims i.succ) (data.get (a 0)) (fun i => a i.succ)

/-- This recursively allocates vectors. The input function is evaluated
once at every dense cell, rather than retained as a deferred array. -/
def materialize : (n : ℕ) → (dims : Fin n → ℕ) → (Coordinates dims → R) → Dense (R := R) n dims
  | 0, _, f => f (fun i => Fin.elim0 i)
  | n + 1, dims, f => Vector.ofFn (fun a =>
      materialize n (fun i => dims i.succ) (fun rest => f (Fin.cons a rest)))

omit [CommSemiring R] in
theorem read_materialize (n : ℕ) (dims : Fin n → ℕ) (f : Coordinates dims → R)
    (a : Coordinates dims) : read n dims (materialize n dims f) a = f a := by
  induction n with
  | zero =>
      simp only [read, materialize]
      congr 1
      funext i
      exact Fin.elim0 i
  | succ n ih =>
      simp only [read, materialize, Vector.get_ofFn, ih]
      congr 1
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · rfl
      · rfl

/-- One array contraction, actually materialized once for this child. -/
def contract {n : ℕ} (dims : Fin (n + 1) → ℕ)
    (form : Fin (dims 0) → R) (input : Dense (R := R) (n + 1) dims) :
    Dense (R := R) n (fun i => dims i.succ) :=
  materialize n (fun i => dims i.succ) (fun rest =>
    ((List.finRange (dims 0)).map (fun a => form a * read (n + 1) dims input (Fin.cons a rest))).sum)

theorem read_contract {n : ℕ} (dims : Fin (n + 1) → ℕ)
    (form : Fin (dims 0) → R) (input : Dense (R := R) (n + 1) dims)
    (rest : Coordinates (fun i : Fin n => dims i.succ)) :
    read n (fun i => dims i.succ) (contract dims form input) rest =
      EncoderCorrectness.contractFirst dims form (read (n + 1) dims input) rest := by
  rw [contract, read_materialize]
  simpa only [EncoderCorrectness.contractFirst, ← List.ofFn_eq_map] using
    (List.sum_ofFn (f := fun a => form a * read (n + 1) dims input (Fin.cons a rest)))

def volume (n : ℕ) (dims : Fin n → ℕ) : ℕ := ∏ i, dims i

theorem volume_eq_prod (n : ℕ) (dims : Fin n → ℕ) : volume n dims = ∏ i, dims i := by
  rfl

structure Node (N n : ℕ) (dims : Fin n → ℕ) where
  word : Word N
  data : Dense (R := R) n dims

abbrev LocalForms (R : Type u) := ℕ → Label → ℕ → R

/-- Six candidate labels are inspected; rejected children allocate no
dense array. Each retained `(parent,label)` allocates exactly one. -/
def nodeChildren (L m t d n : ℕ) (hd : d < 2 * L) (dims : Fin (n + 1) → ℕ)
    (forms : LocalForms R) (parent : Node (R := R) (2 * L) (n + 1) dims) :
    List (Node (R := R) (2 * L) n (fun i => dims i.succ)) :=
  (List.finRange 6).filterMap (fun a =>
    let w := put d hd parent.word a
    if capTest L m t w then
      some ⟨w, contract dims (fun b => forms d a b.val) parent.data⟩ else none)

def nextLayer (L m t d n : ℕ) (hd : d < 2 * L) (dims : Fin (n + 1) → ℕ)
    (forms : LocalForms R) (parents : List (Node (R := R) (2 * L) (n + 1) dims)) :
    List (Node (R := R) (2 * L) n (fun i => dims i.succ)) :=
  parents.flatMap (nodeChildren L m t d n hd dims forms)

def wordAt {N : ℕ} (w : Word N) (d : ℕ) : Label := if h : d < N then w ⟨d, h⟩ else 0

def Agree {N : ℕ} (d : ℕ) (pref target : Word N) : Prop :=
  ∀ i, i.val < d → pref i = target i

/-- Proof denotation of completing a stored suffix array along one target
word. This function is never called by the encoder program. -/
noncomputable def completion {N : ℕ} (n : ℕ) (dims : Fin n → ℕ) (d : ℕ)
    (forms : LocalForms R) (target : Word N) (data : Dense (R := R) n dims) : R :=
  EncoderCorrectness.sweep n dims
    (fun i a => forms (d + i.val) (wordAt target (d + i.val)) a.val) (read n dims data)

def Valid {N : ℕ} (n : ℕ) (dims : Fin n → ℕ) (d : ℕ) (forms : LocalForms R)
    (denote : Word N → R) (node : Node (R := R) N n dims) : Prop :=
  ∀ target, Agree d node.word target → completion n dims d forms target node.data = denote target

theorem completion_step {N n : ℕ} (dims : Fin (n + 1) → ℕ) (d : ℕ)
    (forms : LocalForms R) (target : Word N) (input : Dense (R := R) (n + 1) dims) :
    completion n (fun i => dims i.succ) (d + 1) forms target
      (contract dims (fun a => forms d (wordAt target d) a.val) input) =
    completion (n + 1) dims d forms target input := by
  unfold completion
  rw [EncoderCorrectness.sweep]
  have hread : read n (fun i => dims i.succ)
      (contract dims (fun a => forms d (wordAt target d) a.val) input) =
      EncoderCorrectness.contractFirst dims
        (fun a => forms d (wordAt target d) a.val) (read (n + 1) dims input) := by
    funext rest
    exact read_contract dims _ input rest
  rw [hread]
  simp only [Fin.val_zero, Nat.add_zero]
  have hforms : (fun (i : Fin n) (a : Fin (dims i.succ)) =>
      forms (d + 1 + i.val) (wordAt target (d + 1 + i.val)) a.val) =
      (fun (i : Fin n) (a : Fin (dims i.succ)) =>
        forms (d + i.succ.val) (wordAt target (d + i.succ.val)) a.val) := by
    funext i a
    simp only [Fin.val_succ]
    have he : d + 1 + i.val = d + (i.val + 1) := by omega
    rw [he]
  rw [hforms]

theorem mem_nodeChildren (L m t d n : ℕ) (hd : d < 2 * L) (dims : Fin (n + 1) → ℕ)
    (forms : LocalForms R) (parent : Node (R := R) (2 * L) (n + 1) dims)
    (child : Node (R := R) (2 * L) n (fun i => dims i.succ)) :
    child ∈ nodeChildren L m t d n hd dims forms parent ↔
      ∃ a : Label, capTest L m t (put d hd parent.word a) = true ∧
        child = ⟨put d hd parent.word a,
          contract dims (fun b => forms d a b.val) parent.data⟩ := by
  simp only [nodeChildren, List.mem_filterMap, List.mem_finRange, true_and]
  constructor
  · rintro ⟨a, hchild⟩
    by_cases hc : capTest L m t (put d hd parent.word a) = true
    · simp only [hc, ↓reduceIte, Option.some.injEq] at hchild
      exact ⟨a, hc, hchild.symm⟩
    · simp [hc] at hchild
  · rintro ⟨a, hc, rfl⟩
    exact ⟨a, by simp [hc]⟩

theorem child_valid (L m t d n : ℕ) (hd : d < 2 * L) (dims : Fin (n + 1) → ℕ)
    (forms : LocalForms R) (denote : Word (2 * L) → R)
    (parent : Node (R := R) (2 * L) (n + 1) dims)
    (child : Node (R := R) (2 * L) n (fun i => dims i.succ))
    (hp : Valid (n + 1) dims d forms denote parent)
    (hc : child ∈ nodeChildren L m t d n hd dims forms parent) :
    Valid n (fun i => dims i.succ) (d + 1) forms denote child := by
  obtain ⟨a, hcap, rfl⟩ := (mem_nodeChildren L m t d n hd dims forms parent child).mp hc
  intro target hagree
  have hparent : Agree d parent.word target := by
    intro i hi
    have he := hagree i (by omega)
    have hne : i ≠ (⟨d, hd⟩ : Fin (2 * L)) := by
      intro h
      have hev : i.val = d := congrArg Fin.val h
      omega
    simpa only [put, Function.update_of_ne hne] using he
  have ha : wordAt target d = a := by
    have he := hagree ⟨d, hd⟩ (by simp)
    simpa [wordAt, hd, put] using he.symm
  change completion n (fun i => dims i.succ) (d + 1) forms target
    (contract dims (fun b => forms d a b.val) parent.data) = _
  rw [← ha, completion_step]
  exact hp target hparent

/-- Arbitrary stored-array invariants may be transported through the
actual layer loop by proving just their local contraction step. -/
theorem nextLayer_invariant (L m t d n : ℕ) (hd : d < 2 * L)
    (dims : Fin (n + 1) → ℕ) (forms : LocalForms R)
    (parents : List (Node (R := R) (2 * L) (n + 1) dims))
    (P : Node (R := R) (2 * L) (n + 1) dims → Prop)
    (Q : Node (R := R) (2 * L) n (fun i => dims i.succ) → Prop)
    (hp : ∀ parent ∈ parents, P parent)
    (hstep : ∀ parent, P parent → ∀ child ∈ nodeChildren L m t d n hd dims forms parent, Q child) :
    ∀ child ∈ nextLayer L m t d n hd dims forms parents, Q child := by
  intro child hc
  obtain ⟨parent, hp', hc⟩ := List.mem_flatMap.mp hc
  exact hstep parent (hp parent hp') child hc

theorem nextLayer_valid (L m t d n : ℕ) (hd : d < 2 * L) (dims : Fin (n + 1) → ℕ)
    (forms : LocalForms R) (denote : Word (2 * L) → R)
    (parents : List (Node (R := R) (2 * L) (n + 1) dims))
    (hp : ∀ parent ∈ parents, Valid (n + 1) dims d forms denote parent) :
    ∀ child ∈ nextLayer L m t d n hd dims forms parents,
      Valid n (fun i => dims i.succ) (d + 1) forms denote child :=
  nextLayer_invariant L m t d n hd dims forms parents _ _ hp
    (fun parent hp child hc => child_valid L m t d n hd dims forms denote parent child hp hc)

theorem nodeChildren_words (L m t d n : ℕ) (hd : d < 2 * L) (dims : Fin (n + 1) → ℕ)
    (forms : LocalForms R) (parent : Node (R := R) (2 * L) (n + 1) dims) :
    (nodeChildren L m t d n hd dims forms parent).map Node.word =
      children L m t d hd parent.word := by
  simp only [nodeChildren, List.map_filterMap, children]
  rw [List.filter_map, ← List.filterMap_eq_filter, List.map_filterMap]
  apply List.filterMap_congr
  intro a ha
  simp only [Function.comp_apply, Option.guard]
  split <;> rfl

theorem nextLayer_words (L m t d n : ℕ) (hd : d < 2 * L) (dims : Fin (n + 1) → ℕ)
    (forms : LocalForms R) (parents : List (Node (R := R) (2 * L) (n + 1) dims))
    (hwords : parents.map Node.word = generate L m t d) :
    (nextLayer L m t d n hd dims forms parents).map Node.word = generate L m t (d + 1) := by
  simp only [nextLayer, List.map_flatMap, nodeChildren_words]
  rw [← List.flatMap_map, hwords]
  simp [generate, hd]

/-- Every retained child key is formed once at its layer. -/
theorem nextLayer_keys_nodup (L m t d n : ℕ) (hd : d < 2 * L) (dims : Fin (n + 1) → ℕ)
    (forms : LocalForms R) (parents : List (Node (R := R) (2 * L) (n + 1) dims))
    (hwords : parents.map Node.word = generate L m t d) :
    ((nextLayer L m t d n hd dims forms parents).map Node.word).Nodup := by
  rw [nextLayer_words L m t d n hd dims forms parents hwords]
  exact generate_nodup L m t (d + 1) (by omega)

structure Stored (R : Type u) (N : ℕ) where
  depth : ℕ
  remaining : ℕ
  dims : Fin remaining → ℕ
  node : Node (R := R) N remaining dims

structure Result (R : Type u) (N : ℕ) where
  leaves : List (Word N × R)
  formed : List (Stored R N)
  coefficientWork : ℕ
  capWork : ℕ
  coefficientCells : ℕ

/-- An actual forward layer program. Parent dense arrays are shared by all
their children; each child uses one `contract` call. The trace retains all
formed arrays, so the cost theorem cannot discard expensive intermediates. -/
def run (L m t q width : ℕ) (forms : LocalForms R) :
    (n : ℕ) → (dims : Fin n → ℕ) → ℕ → List (Node (R := R) (2 * L) n dims) → Result R (2 * L)
  | 0, dims, d, parents =>
      { leaves := parents.map (fun node => (node.word, node.data))
        formed := parents.map (fun node => ⟨d, 0, dims, node⟩)
        coefficientWork := 84 * q * width * parents.length * volume 0 dims
        capWork := 0
        coefficientCells := q * width * parents.length * volume 0 dims }
  | n + 1, dims, d, parents =>
      if hd : d < 2 * L then
        let children := nextLayer L m t d n hd dims forms parents
        let tail := run L m t q width forms n (fun i => dims i.succ) (d + 1) children
        { tail with
          formed := parents.map (fun node => ⟨d, n + 1, dims, node⟩) ++ tail.formed
          coefficientWork := 84 * q * width * parents.length * volume (n + 1) dims + tail.coefficientWork
          capWork := 6 * parents.length * (1 + 3 * (2 * L)) + tail.capWork
          coefficientCells := q * width * parents.length * volume (n + 1) dims + tail.coefficientCells }
      else
        { leaves := []
          formed := parents.map (fun node => ⟨d, n + 1, dims, node⟩)
          coefficientWork := 84 * q * width * parents.length * volume (n + 1) dims
          capWork := 0
          coefficientCells := q * width * parents.length * volume (n + 1) dims }

/-- Every actual stored array satisfies any invariant proved for the root
and preserved by the literal local contraction. This is the public hook
for coefficient bounds, rather than an assumed bound on intermediates. -/
theorem run_invariant (L m t q width : ℕ) (forms : LocalForms R)
    (P : (d n : ℕ) → (dims : Fin n → ℕ) → Node (R := R) (2 * L) n dims → Prop)
    (hstep : ∀ d n (hd : d < 2 * L) dims parent, P d (n + 1) dims parent →
      ∀ child ∈ nodeChildren L m t d n hd dims forms parent,
        P (d + 1) n (fun i => dims i.succ) child)
    (n : ℕ) (dims : Fin n → ℕ) (d : ℕ) (parents : List (Node (R := R) (2 * L) n dims))
    (hp : ∀ parent ∈ parents, P d n dims parent) :
    ∀ s ∈ (run L m t q width forms n dims d parents).formed,
      P s.depth s.remaining s.dims s.node := by
  induction n generalizing d with
  | zero =>
      intro s hs
      obtain ⟨parent, hparent, rfl⟩ := List.mem_map.mp hs
      exact hp parent hparent
  | succ n ih =>
      simp only [run]
      split
      · rename_i hd
        intro s hs
        obtain hs | hs := List.mem_append.mp hs
        · obtain ⟨parent, hparent, rfl⟩ := List.mem_map.mp hs
          exact hp parent hparent
        · exact ih _ _ _ (nextLayer_invariant L m t d n hd dims forms parents _ _ hp
            (fun parent hparent child hc => hstep d n hd dims parent hparent child hc)) s hs
      · intro s hs
        obtain ⟨parent, hparent, rfl⟩ := List.mem_map.mp hs
        exact hp parent hparent

theorem run_correct (L m t q width : ℕ) (forms : LocalForms R)
    (denote : Word (2 * L) → R) (n : ℕ) (dims : Fin n → ℕ) (d : ℕ)
    (parents : List (Node (R := R) (2 * L) n dims))
    (hsum : d + n = 2 * L) (hwords : parents.map Node.word = generate L m t d)
    (hp : ∀ parent ∈ parents, Valid n dims d forms denote parent) :
    ((run L m t q width forms n dims d parents).leaves.map Prod.fst = generate L m t (2 * L)) ∧
      ∀ leaf ∈ (run L m t q width forms n dims d parents).leaves, leaf.2 = denote leaf.1 := by
  induction n generalizing d with
  | zero =>
      refine ⟨?_, ?_⟩
      · have hd : d = 2 * L := by omega
        simpa only [run, List.map_map, Function.comp_def, hd] using hwords
      · intro leaf hleaf
        obtain ⟨parent, hparent, rfl⟩ := List.mem_map.mp hleaf
        have hv := hp parent hparent parent.word (fun i hi => rfl)
        simpa only [completion, EncoderCorrectness.sweep, read] using hv
  | succ n ih =>
      have hd : d < 2 * L := by omega
      simp only [run, dif_pos hd]
      apply ih _ _ _ (by omega)
      · exact nextLayer_words L m t d n hd dims forms parents hwords
      · exact nextLayer_valid L m t d n hd dims forms denote parents hp

/-- Actual physical raw dimensions, with the suffix depth tracked. -/
def Shape (L : ℕ) (firstNormal : Bool) (d n : ℕ) (dims : Fin n → ℕ) : Prop :=
  d + n = 2 * L ∧ ∀ i, dims i = rawDim L firstNormal (d + i.val)

theorem shape_tail (L : ℕ) (firstNormal : Bool) (d n : ℕ) (dims : Fin (n + 1) → ℕ)
    (hs : Shape L firstNormal d (n + 1) dims) :
    Shape L firstNormal (d + 1) n (fun i => dims i.succ) := by
  refine ⟨by have := hs.1; omega, ?_⟩
  intro i
  change dims i.succ = _
  rw [hs.2 i.succ]
  congr 1
  simp only [Fin.val_succ]
  omega

theorem shape_volume (L : ℕ) (firstNormal : Bool) (d n : ℕ) (dims : Fin n → ℕ)
    (hs : Shape L firstNormal d n dims) : volume n dims = rawVolume L d firstNormal := by
  obtain ⟨hsum, hdims⟩ := hs
  have hn : n = 2 * L - d := by omega
  subst n
  unfold volume rawVolume
  exact Finset.prod_congr rfl (fun i hi => hdims i)

omit [CommSemiring R] in
theorem layer_cells_le (L m t : ℕ) (firstNormal : Bool) (d n : ℕ) (dims : Fin n → ℕ)
    (parents : List (Node (R := R) (2 * L) n dims)) (hs : Shape L firstNormal d n dims)
    (hwords : parents.map Node.word = generate L m t d) :
    parents.length * volume n dims ≤ retainedLeafCount L m t := by
  have hd : d ≤ 2 * L := by have := hs.1; omega
  have hlen : parents.length = (generate L m t d).length := by
    simpa only [List.length_map] using congrArg List.length hwords
  rw [hlen, shape_volume L firstNormal d n dims hs, generate_length_eq_prefix_card L m t d hd]
  exact layer_volume_le L m t d hd firstNormal

omit [CommSemiring R] in
theorem layer_records_le (L m t : ℕ) (firstNormal : Bool) (d n : ℕ) (dims : Fin n → ℕ)
    (parents : List (Node (R := R) (2 * L) n dims)) (hs : Shape L firstNormal d n dims)
    (hwords : parents.map Node.word = generate L m t d) :
    parents.length ≤ retainedLeafCount L m t := by
  have hd : d ≤ 2 * L := by have := hs.1; omega
  have hlen : parents.length = (generate L m t d).length := by
    simpa only [List.length_map] using congrArg List.length hwords
  rw [hlen, generate_length_eq_prefix_card L m t d hd]
  exact prefix_count_le_leafCount L m t d hd firstNormal

theorem run_work_eq_cells (L m t q width : ℕ) (forms : LocalForms R)
    (n : ℕ) (dims : Fin n → ℕ) (d : ℕ) (parents : List (Node (R := R) (2 * L) n dims)) :
    (run L m t q width forms n dims d parents).coefficientWork =
      84 * (run L m t q width forms n dims d parents).coefficientCells := by
  induction n generalizing d with
  | zero => simp only [run]; ring
  | succ n ih =>
      simp only [run]
      split
      · rw [ih]
        ring
      · ring

theorem run_cells_le (L m t q width : ℕ) (forms : LocalForms R) (firstNormal : Bool)
    (n : ℕ) (dims : Fin n → ℕ) (d : ℕ) (parents : List (Node (R := R) (2 * L) n dims))
    (hs : Shape L firstNormal d n dims) (hwords : parents.map Node.word = generate L m t d) :
    (run L m t q width forms n dims d parents).coefficientCells ≤
      q * width * (n + 1) * retainedLeafCount L m t := by
  induction n generalizing d with
  | zero =>
      have hc := Nat.mul_le_mul_left (q * width) (layer_cells_le L m t firstNormal d 0 dims parents hs hwords)
      simpa only [run, Nat.zero_add, Nat.mul_one, Nat.mul_assoc] using hc
  | succ n ih =>
      have hd : d < 2 * L := by have := hs.1; omega
      simp only [run, dif_pos hd]
      have ht := ih _ _ _ (shape_tail L firstNormal d n dims hs)
        (nextLayer_words L m t d n hd dims forms parents hwords)
      have hc := Nat.mul_le_mul_left (q * width)
        (layer_cells_le L m t firstNormal d (n + 1) dims parents hs hwords)
      calc
        _ ≤ q * width * retainedLeafCount L m t +
            q * width * (n + 1) * retainedLeafCount L m t := by
          simpa only [Nat.mul_assoc] using Nat.add_le_add hc ht
        _ = _ := by ring

theorem run_capWork_le (L m t q width : ℕ) (forms : LocalForms R) (firstNormal : Bool)
    (n : ℕ) (dims : Fin n → ℕ) (d : ℕ) (parents : List (Node (R := R) (2 * L) n dims))
    (hs : Shape L firstNormal d n dims) (hwords : parents.map Node.word = generate L m t d) :
    (run L m t q width forms n dims d parents).capWork ≤
      6 * n * (1 + 3 * (2 * L)) * retainedLeafCount L m t := by
  induction n generalizing d with
  | zero => simp [run]
  | succ n ih =>
      have hd : d < 2 * L := by have := hs.1; omega
      simp only [run, dif_pos hd]
      have ht := ih _ _ _ (shape_tail L firstNormal d n dims hs)
        (nextLayer_words L m t d n hd dims forms parents hwords)
      have hc := Nat.mul_le_mul_left (6 * (1 + 3 * (2 * L)))
        (layer_records_le L m t firstNormal d (n + 1) dims parents hs hwords)
      calc
        _ ≤ 6 * (1 + 3 * (2 * L)) * retainedLeafCount L m t +
            6 * n * (1 + 3 * (2 * L)) * retainedLeafCount L m t := by
          simpa only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using Nat.add_le_add hc ht
        _ = _ := by ring

/-- Exact coefficient-cell volume of the actual stored-array trace. -/
def formedCells (q width : ℕ) (formed : List (Stored R N)) : ℕ :=
  (formed.map (fun s => q * width * volume s.remaining s.dims)).sum

omit [CommSemiring R] in
theorem formedCells_map (q width d n : ℕ) (dims : Fin n → ℕ)
    (parents : List (Node (R := R) N n dims)) :
    formedCells q width (parents.map (fun node => (⟨d, n, dims, node⟩ : Stored R N))) =
      q * width * parents.length * volume n dims := by
  induction parents with
  | nil => simp [formedCells]
  | cons parent parents ih =>
      simp only [formedCells, List.map_cons, List.sum_cons, List.length_cons] at ih ⊢
      rw [ih]
      ring

omit [CommSemiring R] in
theorem formedCells_append (q width : ℕ) (a b : List (Stored R N)) :
    formedCells q width (a ++ b) = formedCells q width a + formedCells q width b := by
  simp [formedCells]

theorem run_cells_eq_formed (L m t q width : ℕ) (forms : LocalForms R)
    (n : ℕ) (dims : Fin n → ℕ) (d : ℕ) (parents : List (Node (R := R) (2 * L) n dims)) :
    (run L m t q width forms n dims d parents).coefficientCells =
      formedCells q width (run L m t q width forms n dims d parents).formed := by
  induction n generalizing d with
  | zero => simp only [run, formedCells_map]
  | succ n ih =>
      simp only [run]
      split
      · rw [formedCells_append, formedCells_map, ih]
      · exact (formedCells_map q width d (n + 1) dims parents).symm

def rootDims (L : ℕ) (firstNormal : Bool) : Fin (2 * L) → ℕ :=
  fun i => rawDim L firstNormal i.val

/-- The public encoder. The sole root array is reused throughout its
retained-prefix trie. No complete branch sweep is called here. -/
def encode (L m t q width : ℕ) (firstNormal : Bool) (forms : LocalForms R)
    (input : Dense (R := R) (2 * L) (rootDims L firstNormal)) : Result R (2 * L) :=
  run L m t q width forms (2 * L) (rootDims L firstNormal) 0 [⟨zeroWord (2 * L), input⟩]

noncomputable def tensorValue (L : ℕ) (firstNormal : Bool) (forms : LocalForms R)
    (input : Dense (R := R) (2 * L) (rootDims L firstNormal)) (word : Word (2 * L)) : R :=
  EncoderCorrectness.tensorSum (rootDims L firstNormal)
    (fun i a => forms i.val (word i) a.val) (read (2 * L) (rootDims L firstNormal) input)

theorem root_completion_tensor (L : ℕ) (firstNormal : Bool) (forms : LocalForms R)
    (input : Dense (R := R) (2 * L) (rootDims L firstNormal)) (word : Word (2 * L)) :
    completion (2 * L) (rootDims L firstNormal) 0 forms word input =
      tensorValue L firstNormal forms input word := by
  unfold completion tensorValue
  rw [EncoderCorrectness.sweep_eq_tensorSum]
  congr 1
  funext i a
  simp [wordAt, i.isLt]

theorem root_shape (L : ℕ) (firstNormal : Bool) :
    Shape L firstNormal 0 (2 * L) (rootDims L firstNormal) := by
  exact ⟨by omega, fun i => by simp [rootDims]⟩

theorem root_valid (L : ℕ) (firstNormal : Bool) (forms : LocalForms R)
    (input : Dense (R := R) (2 * L) (rootDims L firstNormal)) :
    Valid (2 * L) (rootDims L firstNormal) 0 forms (tensorValue L firstNormal forms input)
      ⟨zeroWord (2 * L), input⟩ := by
  intro target hagree
  exact root_completion_tensor L firstNormal forms input target

/-- Exact retained keys and tensor values of the same returned program. -/
theorem encode_correct (L m t q width : ℕ) (firstNormal : Bool) (forms : LocalForms R)
    (input : Dense (R := R) (2 * L) (rootDims L firstNormal)) :
    (encode L m t q width firstNormal forms input).leaves.map Prod.fst = generate L m t (2 * L) ∧
      ∀ leaf ∈ (encode L m t q width firstNormal forms input).leaves,
        leaf.2 = tensorValue L firstNormal forms input leaf.1 := by
  apply run_correct L m t q width forms (tensorValue L firstNormal forms input)
    (2 * L) (rootDims L firstNormal) 0 [⟨zeroWord (2 * L), input⟩] (by omega) rfl
  intro parent hp
  simp only [List.mem_singleton] at hp
  subst parent
  exact root_valid L firstNormal forms input

theorem encode_keys_nodup (L m t q width : ℕ) (firstNormal : Bool) (forms : LocalForms R)
    (input : Dense (R := R) (2 * L) (rootDims L firstNormal)) :
    ((encode L m t q width firstNormal forms input).leaves.map Prod.fst).Nodup := by
  rw [(encode_correct L m t q width firstNormal forms input).1]
  exact generate_nodup L m t (2 * L) (le_refl _)

theorem encode_cells_le (L m t q width : ℕ) (firstNormal : Bool) (forms : LocalForms R)
    (input : Dense (R := R) (2 * L) (rootDims L firstNormal)) :
    (encode L m t q width firstNormal forms input).coefficientCells ≤
      q * width * (2 * L + 1) * retainedLeafCount L m t :=
  run_cells_le L m t q width forms firstNormal (2 * L) (rootDims L firstNormal) 0
    [⟨zeroWord (2 * L), input⟩] (root_shape L firstNormal) rfl

theorem encode_coefficientWork_le (L m t q width : ℕ) (firstNormal : Bool) (forms : LocalForms R)
    (input : Dense (R := R) (2 * L) (rootDims L firstNormal)) :
    (encode L m t q width firstNormal forms input).coefficientWork ≤
      84 * q * width * (2 * L + 1) * retainedLeafCount L m t := by
  rw [encode, run_work_eq_cells]
  simpa only [encode, Nat.mul_assoc] using Nat.mul_le_mul_left 84
    (encode_cells_le L m t q width firstNormal forms input)

theorem encode_capWork_le (L m t q width : ℕ) (firstNormal : Bool) (forms : LocalForms R)
    (input : Dense (R := R) (2 * L) (rootDims L firstNormal)) :
    (encode L m t q width firstNormal forms input).capWork ≤
      6 * (2 * L) * (1 + 3 * (2 * L)) * retainedLeafCount L m t :=
  run_capWork_le L m t q width forms firstNormal (2 * L) (rootDims L firstNormal) 0
    [⟨zeroWord (2 * L), input⟩] (root_shape L firstNormal) rfl

/-- Full charged finite work, including cap scans. Complete coefficient
widths remain present, with positivity needed to absorb topology metadata. -/
theorem encode_work_le (L m t q width : ℕ) (firstNormal : Bool) (forms : LocalForms R)
    (input : Dense (R := R) (2 * L) (rootDims L firstNormal)) (hq : 1 ≤ q) (hw : 1 ≤ width) :
    (encode L m t q width firstNormal forms input).coefficientWork +
      (encode L m t q width firstNormal forms input).capWork ≤
      (84 * (2 * L + 1) + 6 * (2 * L) * (1 + 3 * (2 * L))) *
        q * width * retainedLeafCount L m t := by
  have hcoeff := encode_coefficientWork_le L m t q width firstNormal forms input
  have hcap := encode_capWork_le L m t q width firstNormal forms input
  have hqw : 1 ≤ q * width := by nlinarith
  have hweight : 6 * (2 * L) * (1 + 3 * (2 * L)) * retainedLeafCount L m t ≤
      (6 * (2 * L) * (1 + 3 * (2 * L)) * retainedLeafCount L m t) * (q * width) := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left
      (6 * (2 * L) * (1 + 3 * (2 * L)) * retainedLeafCount L m t) hqw
  have hcap' := hcap.trans hweight
  calc
    _ ≤ 84 * q * width * (2 * L + 1) * retainedLeafCount L m t +
        (6 * (2 * L) * (1 + 3 * (2 * L)) * retainedLeafCount L m t) * (q * width) := by
      exact Nat.add_le_add hcoeff hcap'
    _ = _ := by ring

/-- Joint correctness and storage/work specification of the implemented
encoder, with no independently evaluated leaf sweeps in its program. -/
theorem encode_contract (L m t q width : ℕ) (firstNormal : Bool) (forms : LocalForms R)
    (input : Dense (R := R) (2 * L) (rootDims L firstNormal)) (hq : 1 ≤ q) (hw : 1 ≤ width) :
    let out := encode L m t q width firstNormal forms input
    (out.leaves.map Prod.fst).Nodup ∧
      (∀ w, w ∈ out.leaves.map Prod.fst ↔ Retained L m t w) ∧
      (∀ leaf ∈ out.leaves, leaf.2 = tensorValue L firstNormal forms input leaf.1) ∧
      formedCells q width out.formed ≤ q * width * (2 * L + 1) * retainedLeafCount L m t ∧
      out.coefficientWork + out.capWork ≤
        (84 * (2 * L + 1) + 6 * (2 * L) * (1 + 3 * (2 * L))) *
          q * width * retainedLeafCount L m t := by
  refine ⟨encode_keys_nodup L m t q width firstNormal forms input, ?_,
    (encode_correct L m t q width firstNormal forms input).2, ?_,
    encode_work_le L m t q width firstNormal forms input hq hw⟩
  · intro w
    rw [(encode_correct L m t q width firstNormal forms input).1]
    exact mem_generate_leaf L m t w
  · rw [encode, ← run_cells_eq_formed]
    simpa only [encode] using encode_cells_le L m t q width firstNormal forms input

/- An actual materialized-array execution audit. This generic example is
not used to prove the tensor or cost theorems. -/
private def auditInput : Dense (R := ℤ) 2 (rootDims 1 true) :=
  materialize 2 (rootDims 1 true) (fun a => ((a 0).val + (a 1).val : ℕ))

private def auditForms : LocalForms ℤ := fun d a b => ((d + 1) * (a.val + 1) * (b + 1) : ℕ)

#eval let out := encode 1 1 0 1 1 true auditForms auditInput
  (out.leaves.length, out.formed.length, out.coefficientCells,
    out.coefficientWork, out.capWork, out.leaves.head?.map Prod.snd)

end ThinMatrix.SharedEncoder

#print axioms ThinMatrix.SharedEncoder.read_contract
#print axioms ThinMatrix.SharedEncoder.run_invariant
#print axioms ThinMatrix.SharedEncoder.run_cells_eq_formed
#print axioms ThinMatrix.SharedEncoder.encode_correct
#print axioms ThinMatrix.SharedEncoder.encode_keys_nodup
#print axioms ThinMatrix.SharedEncoder.encode_cells_le
#print axioms ThinMatrix.SharedEncoder.encode_work_le
#print axioms ThinMatrix.SharedEncoder.encode_contract
