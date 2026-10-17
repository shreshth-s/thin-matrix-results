import SharedEncoder
import HighBoxDP
import SparseLocalForms
import StoredHighDP
import SourceCoordinates
import ArrayKeys

/-!
Direct shared dense-suffix encoding of the HIGH base language. There are
exactly four ordinary letters and one private `H(0)` letter. Both physical
halves have at most `m` private positions and their joint number is at most
`2*m-t`. Prefixes are generated directly; no Cartesian word enumeration or
independent full leaf sweep occurs in the program.
-/

namespace ThinMatrix.HighBaseEncoder

open CacheBounds CappedEnumeration HighBoxDP
open SharedEncoder (Dense read materialize contract read_contract volume Node LocalForms wordAt Agree completion completion_step
  Valid Shape shape_tail shape_volume rootDims root_shape root_valid tensorValue)
open scoped BigOperators

universe u
variable {R : Type u} [CommSemiring R]

def Admissible (L m t : ℕ) (w : Word (2*L)) : Prop :=
  HighBoxDP.Balanced L m t w ∧ ∀ i, (w i).val ≠ 5

noncomputable def baseCount (L m t : ℕ) : ℕ := Fintype.card (BaseStates L m t)

abbrev BasePrefixes (L m t d : ℕ) :=
  {w : Word (2*L) // IsPrefix d w ∧ Admissible L m t w}

noncomputable instance basePrefixesFintype (L m t d : ℕ) :
    Fintype (BasePrefixes L m t d) := Fintype.ofFinite _

def baseLabel (a : Fin 5) : Label := a.castSucc

theorem baseLabel_injective : Function.Injective baseLabel := by
  intro a b h
  apply Fin.ext
  exact congrArg (fun x : Fin 6 => x.val) h

def baseTest (L m t : ℕ) (w : Word (2*L)) : Bool :=
  decide (countBool w (fun i a => decide (i.val < L ∧ 4 ≤ a.val)) ≤ m) &&
  decide (countBool w (fun i a => decide (L ≤ i.val ∧ 4 ≤ a.val)) ≤ m) &&
  decide (countBool w (fun _ a => decide (4 ≤ a.val)) ≤ 2*m-t) &&
  (List.finRange (2*L)).all (fun i => decide ((w i).val ≠ 5))

theorem baseTest_eq_true (L m t : ℕ) (w : Word (2*L)) :
    baseTest L m t w = true ↔ Admissible L m t w := by
  have hc (p : Fin (2*L) → Label → Prop) (dp : ∀ i a, Decidable (p i a)) :
      countBool w (fun i a => @decide (p i a) (dp i a)) = countPositions w p := by
    rw [countBool_eq]
    simp only [decide_eq_true_eq]
  simp only [baseTest, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_finRange, true_implies]
  rw [hc (fun i a => i.val < L ∧ 4 ≤ a.val) (fun i a => inferInstance),
    hc (fun i a => L ≤ i.val ∧ 4 ≤ a.val) (fun i a => inferInstance),
    hc (fun _ a => 4 ≤ a.val) (fun i a => inferInstance)]
  simp only [Admissible, HighBoxDP.Balanced, specialCount, countPositions, true_and, and_assoc]

theorem zero_admissible (L m t : ℕ) : Admissible L m t (zeroWord (2*L)) := by
  simp [Admissible, HighBoxDP.Balanced, specialCount, zeroWord]

theorem trim_admissible {L m t : ℕ} (d : ℕ) (w : Word (2*L))
    (hw : Admissible L m t w) : Admissible L m t (trimWord d w) := by
  have hc (region : Fin (2*L) → Prop) :
      specialCount (trimWord d w) region ≤ specialCount w region := by
    classical
    apply Finset.card_le_card
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    refine ⟨hi.1, ?_⟩
    by_cases h : i.val < d
    · simpa [trimWord, h] using hi.2
    · simp [trimWord, h] at hi
  refine ⟨⟨(hc _).trans hw.1.1, (hc _).trans hw.1.2.1, (hc _).trans hw.1.2.2⟩, ?_⟩
  intro i
  by_cases h : i.val < d
  · simpa [trimWord, h] using hw.2 i
  · simp [trimWord, h]

def children (L m t d : ℕ) (hd : d < 2*L) (w : Word (2*L)) : List (Word (2*L)) :=
  ((List.finRange 5).map (fun a => put d hd w (baseLabel a))).filter (baseTest L m t)

def generate (L m t : ℕ) : ℕ → List (Word (2*L))
  | 0 => [zeroWord (2*L)]
  | d+1 => if hd : d < 2*L then
    (generate L m t d).flatMap (children L m t d hd) else []

theorem mem_children (L m t d : ℕ) (hd : d < 2*L) (w v : Word (2*L)) :
    v ∈ children L m t d hd w ↔
      ∃ a : Fin 5, put d hd w (baseLabel a) = v ∧ Admissible L m t v := by
  simp only [children, List.mem_filter, List.mem_map, List.mem_finRange,
    true_and, baseTest_eq_true]
  aesop

theorem mem_generate (L m t d : ℕ) (hd : d ≤ 2*L) (w : Word (2*L)) :
    w ∈ generate L m t d ↔ IsPrefix d w ∧ Admissible L m t w := by
  induction d generalizing w with
  | zero =>
    simp only [generate, List.mem_singleton]
    constructor
    · intro h; subst w; exact ⟨fun _ _ => rfl, zero_admissible L m t⟩
    · intro h; funext i; exact h.1 i (Nat.zero_le _)
  | succ d ih =>
    have hlt : d < 2*L := by omega
    rw [generate, dif_pos hlt, List.mem_flatMap]
    constructor
    · rintro ⟨p, hp, hc⟩
      obtain ⟨a, rfl, hv⟩ := (mem_children L m t d hlt p w).mp hc
      exact ⟨put_prefix hlt p _ ((ih (by omega) p).mp hp).1, hv⟩
    · rintro ⟨hp, hv⟩
      have ha : (w ⟨d,hlt⟩).val < 5 := by
        have hn := hv.2 ⟨d,hlt⟩
        have hl := (w ⟨d,hlt⟩).isLt
        omega
      refine ⟨trimWord d w, (ih (by omega) _).mpr
        ⟨trim_isPrefix d w, trim_admissible d w hv⟩, ?_⟩
      apply (mem_children L m t d hlt _ w).mpr
      refine ⟨⟨(w ⟨d,hlt⟩).val, ha⟩, ?_, hv⟩
      have he : baseLabel ⟨(w ⟨d,hlt⟩).val, ha⟩ = w ⟨d,hlt⟩ := Fin.ext rfl
      rw [he]
      exact put_trim hlt w hp

theorem generate_nodup (L m t d : ℕ) (hd : d ≤ 2*L) : (generate L m t d).Nodup := by
  induction d with
  | zero => simp [generate]
  | succ d ih =>
    have hlt : d < 2*L := by omega
    rw [generate, dif_pos hlt]
    apply List.nodup_flatMap.mpr
    refine ⟨fun w _ => ((List.nodup_finRange 5).map
      ((put_label_injective hlt w).comp baseLabel_injective)).filter _, ?_⟩
    apply (ih (by omega)).imp_of_mem
    intro w v hw hv hne
    apply List.disjoint_left.mpr
    intro z hzw hzv
    obtain ⟨a, ha, _⟩ := (mem_children L m t d hlt w z).mp hzw
    obtain ⟨b, hb, _⟩ := (mem_children L m t d hlt v z).mp hzv
    exact hne (put_pair_injective hlt w v _ _
      ((mem_generate L m t d (by omega) w).mp hw).1
      ((mem_generate L m t d (by omega) v).mp hv).1 (ha.trans hb.symm)).1

theorem mem_generate_leaf (L m t : ℕ) (w : Word (2*L)) :
    w ∈ generate L m t (2*L) ↔ Admissible L m t w := by
  rw [mem_generate L m t (2*L) (le_refl _) w]
  have hp : IsPrefix (2*L) w := by intro i hi; omega
  exact and_iff_right hp

noncomputable def generatedPrefixEquiv (L m t d : ℕ) (hd : d ≤ 2*L) :
    {w // w ∈ (generate L m t d).toFinset} ≃ BasePrefixes L m t d where
  toFun := fun w => ⟨w.val, (mem_generate L m t d hd w.val).mp (List.mem_toFinset.mp w.property)⟩
  invFun := fun w => ⟨w.val, List.mem_toFinset.mpr ((mem_generate L m t d hd w.val).mpr w.property)⟩
  left_inv := fun w => by apply Subtype.ext; rfl
  right_inv := fun w => by apply Subtype.ext; rfl

theorem generate_length_eq_prefix_card (L m t d : ℕ) (hd : d ≤ 2*L) :
    (generate L m t d).length = Fintype.card (BasePrefixes L m t d) := by
  classical
  have hc := Fintype.card_congr (generatedPrefixEquiv L m t d hd)
  rw [Fintype.card_coe, List.toFinset_card_of_nodup (generate_nodup L m t d hd)] at hc
  exact hc

attribute [local instance] Classical.propDecidable

def asCachePrefix {L m t d : ℕ} (p : BasePrefixes L m t d) : Prefixes L m 0 d := by
  have h₁ : countPositions p.val (fun i a => i.val < L ∧ distinguished a) ≤ m := by
    simpa only [countPositions, specialCount, distinguished] using p.property.2.1.1
  have h₂ : countPositions p.val (fun i a => L ≤ i.val ∧ distinguished a) ≤ m := by
    simpa only [countPositions, specialCount, distinguished] using p.property.2.1.2.1
  refine ⟨p.val, p.property.1, h₁, h₂, ?_⟩
  simp [countPositions, channel, p.property.2.2]

theorem completion_specialCount {L m t d : ℕ} (p : BasePrefixes L m t d)
    {firstNormal : Bool} (a : RawSuffix L d firstNormal) (region : Fin (2*L) → Prop) :
    specialCount (completeWord (asCachePrefix p) a) region = specialCount p.val region := by
  unfold specialCount
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  change (region i ∧ distinguished (completeWord (asCachePrefix p) a i)) ↔
    (region i ∧ distinguished (p.val i))
  rw [complete_distinguished_iff]
  rfl

theorem completion_balanced {L m t d : ℕ} (p : BasePrefixes L m t d)
    {firstNormal : Bool} (a : RawSuffix L d firstNormal) :
    HighBoxDP.Balanced L m t (completeWord (asCachePrefix p) a) := by
  unfold HighBoxDP.Balanced
  simp only [completion_specialCount]
  exact p.property.2.1

theorem completion_nostar {L m t d : ℕ} (p : BasePrefixes L m t d)
    {firstNormal : Bool} (a : RawSuffix L d firstNormal) :
    ∀ i, (completeWord (asCachePrefix p) a i).val ≠ 5 := by
  intro i
  by_cases hi : i.val < d
  · simp only [completeWord_before _ _ _ hi]
    exact p.property.2.2 i
  · have hh := completeWord_after_lt_four (asCachePrefix p) a i (by omega)
    omega

def completeBase {L m t d : ℕ} {firstNormal : Bool}
    (v : BasePrefixes L m t d × RawSuffix L d firstNormal) : BaseStates L m t :=
  ⟨completeWord (asCachePrefix v.1) v.2, completion_balanced v.1 v.2, completion_nostar v.1 v.2⟩

theorem completeBase_injective {L m t d : ℕ} (hd : d ≤ 2*L) (firstNormal : Bool) :
    Function.Injective (@completeBase L m t d firstNormal) := by
  intro x y hxy
  have hword := congrArg Subtype.val hxy
  have hcache : complete (asCachePrefix x.1, x.2) = complete (asCachePrefix y.1, y.2) :=
    Subtype.ext hword
  have hpair := complete_injective hd firstNormal hcache
  apply Prod.ext
  · apply Subtype.ext
    exact congrArg (fun z => z.1.val) hpair
  · exact congrArg (fun z : Prefixes L m 0 d × RawSuffix L d firstNormal => z.2) hpair

theorem base_layer_volume_le (L m t d : ℕ) (hd : d ≤ 2*L) (firstNormal : Bool) :
    Fintype.card (BasePrefixes L m t d) * rawVolume L d firstNormal ≤ baseCount L m t := by
  have h := Fintype.card_le_of_injective (@completeBase L m t d firstNormal)
    (completeBase_injective hd firstNormal)
  simpa only [Fintype.card_prod, rawSuffix_card, baseCount] using h

theorem prefix_count_le_baseCount (L m t d : ℕ) (hd : d ≤ 2*L) (firstNormal : Bool) :
    Fintype.card (BasePrefixes L m t d) ≤ baseCount L m t := by
  have hp : 1 ≤ rawVolume L d firstNormal := rawVolume_pos L d firstNormal
  calc
    _ ≤ Fintype.card (BasePrefixes L m t d) * rawVolume L d firstNormal := by
      simpa only [Nat.mul_one] using Nat.mul_le_mul_left (Fintype.card (BasePrefixes L m t d)) hp
    _ ≤ _ := base_layer_volume_le L m t d hd firstNormal

/-- Five candidate labels are inspected; rejected children allocate no
dense array. Each retained `(parent,label)` allocates exactly one. -/
def nodeChildren (L m t d n : ℕ) (hd : d < 2 * L) (dims : Fin (n + 1) → ℕ)
    (forms : LocalForms R) (parent : Node (R := R) (2 * L) (n + 1) dims) :
    List (Node (R := R) (2 * L) n (fun i => dims i.succ)) :=
  (List.finRange 5).filterMap (fun a =>
    let w := put d hd parent.word (baseLabel a)
    if baseTest L m t w then
      some ⟨w, contract dims (fun b => forms d (baseLabel a) b.val) parent.data⟩ else none)

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
      ∃ a : Fin 5, baseTest L m t (put d hd parent.word (baseLabel a)) = true ∧
        child = ⟨put d hd parent.word (baseLabel a),
          contract dims (fun b => forms d (baseLabel a) b.val) parent.data⟩ := by
  simp only [nodeChildren, List.mem_filterMap, List.mem_finRange, true_and]
  constructor
  · rintro ⟨a, hchild⟩
    by_cases hc : baseTest L m t (put d hd parent.word (baseLabel a)) = true
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
  have ha : wordAt target d = baseLabel a := by
    have he := hagree ⟨d, hd⟩ (by simp)
    simpa [wordAt, hd, put] using he.symm
  change completion n (fun i => dims i.succ) (d + 1) forms target
    (contract dims (fun b => forms d (baseLabel a) b.val) parent.data) = _
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
        coefficientWork := 70 * q * width * parents.length * volume 0 dims
        capWork := 0
        coefficientCells := q * width * parents.length * volume 0 dims }
  | n + 1, dims, d, parents =>
      if hd : d < 2 * L then
        let children := nextLayer L m t d n hd dims forms parents
        let tail := run L m t q width forms n (fun i => dims i.succ) (d + 1) children
        { tail with
          formed := parents.map (fun node => ⟨d, n + 1, dims, node⟩) ++ tail.formed
          coefficientWork := 70 * q * width * parents.length * volume (n + 1) dims + tail.coefficientWork
          capWork := 5 * parents.length * (1 + 4 * (2 * L)) + tail.capWork
          coefficientCells := q * width * parents.length * volume (n + 1) dims + tail.coefficientCells }
      else
        { leaves := []
          formed := parents.map (fun node => ⟨d, n + 1, dims, node⟩)
          coefficientWork := 70 * q * width * parents.length * volume (n + 1) dims
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
        simpa only [completion, EncoderCorrectness.sweep, SharedEncoder.read] using hv
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
    parents.length * volume n dims ≤ baseCount L m t := by
  have hd : d ≤ 2 * L := by have := hs.1; omega
  have hlen : parents.length = (generate L m t d).length := by
    simpa only [List.length_map] using congrArg List.length hwords
  rw [hlen, shape_volume L firstNormal d n dims hs, generate_length_eq_prefix_card L m t d hd]
  exact base_layer_volume_le L m t d hd firstNormal

omit [CommSemiring R] in
theorem layer_records_le (L m t : ℕ) (firstNormal : Bool) (d n : ℕ) (dims : Fin n → ℕ)
    (parents : List (Node (R := R) (2 * L) n dims)) (hs : Shape L firstNormal d n dims)
    (hwords : parents.map Node.word = generate L m t d) :
    parents.length ≤ baseCount L m t := by
  have hd : d ≤ 2 * L := by have := hs.1; omega
  have hlen : parents.length = (generate L m t d).length := by
    simpa only [List.length_map] using congrArg List.length hwords
  rw [hlen, generate_length_eq_prefix_card L m t d hd]
  exact prefix_count_le_baseCount L m t d hd firstNormal

theorem run_work_eq_cells (L m t q width : ℕ) (forms : LocalForms R)
    (n : ℕ) (dims : Fin n → ℕ) (d : ℕ) (parents : List (Node (R := R) (2 * L) n dims)) :
    (run L m t q width forms n dims d parents).coefficientWork =
      70 * (run L m t q width forms n dims d parents).coefficientCells := by
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
      q * width * (n + 1) * baseCount L m t := by
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
        _ ≤ q * width * baseCount L m t +
            q * width * (n + 1) * baseCount L m t := by
          simpa only [Nat.mul_assoc] using Nat.add_le_add hc ht
        _ = _ := by ring

theorem run_capWork_le (L m t q width : ℕ) (forms : LocalForms R) (firstNormal : Bool)
    (n : ℕ) (dims : Fin n → ℕ) (d : ℕ) (parents : List (Node (R := R) (2 * L) n dims))
    (hs : Shape L firstNormal d n dims) (hwords : parents.map Node.word = generate L m t d) :
    (run L m t q width forms n dims d parents).capWork ≤
      5 * n * (1 + 4 * (2 * L)) * baseCount L m t := by
  induction n generalizing d with
  | zero => simp [run]
  | succ n ih =>
      have hd : d < 2 * L := by have := hs.1; omega
      simp only [run, dif_pos hd]
      have ht := ih _ _ _ (shape_tail L firstNormal d n dims hs)
        (nextLayer_words L m t d n hd dims forms parents hwords)
      have hc := Nat.mul_le_mul_left (5 * (1 + 4 * (2 * L)))
        (layer_records_le L m t firstNormal d (n + 1) dims parents hs hwords)
      calc
        _ ≤ 5 * (1 + 4 * (2 * L)) * baseCount L m t +
            5 * n * (1 + 4 * (2 * L)) * baseCount L m t := by
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
      q * width * (2 * L + 1) * baseCount L m t :=
  run_cells_le L m t q width forms firstNormal (2 * L) (rootDims L firstNormal) 0
    [⟨zeroWord (2 * L), input⟩] (root_shape L firstNormal) rfl

theorem encode_coefficientWork_le (L m t q width : ℕ) (firstNormal : Bool) (forms : LocalForms R)
    (input : Dense (R := R) (2 * L) (rootDims L firstNormal)) :
    (encode L m t q width firstNormal forms input).coefficientWork ≤
      70 * q * width * (2 * L + 1) * baseCount L m t := by
  rw [encode, run_work_eq_cells]
  simpa only [encode, Nat.mul_assoc] using Nat.mul_le_mul_left 70
    (encode_cells_le L m t q width firstNormal forms input)

theorem encode_capWork_le (L m t q width : ℕ) (firstNormal : Bool) (forms : LocalForms R)
    (input : Dense (R := R) (2 * L) (rootDims L firstNormal)) :
    (encode L m t q width firstNormal forms input).capWork ≤
      5 * (2 * L) * (1 + 4 * (2 * L)) * baseCount L m t :=
  run_capWork_le L m t q width forms firstNormal (2 * L) (rootDims L firstNormal) 0
    [⟨zeroWord (2 * L), input⟩] (root_shape L firstNormal) rfl

/-- Full charged finite work, including cap scans. Complete coefficient
widths remain present, with positivity needed to absorb topology metadata. -/
theorem encode_work_le (L m t q width : ℕ) (firstNormal : Bool) (forms : LocalForms R)
    (input : Dense (R := R) (2 * L) (rootDims L firstNormal)) (hq : 1 ≤ q) (hw : 1 ≤ width) :
    (encode L m t q width firstNormal forms input).coefficientWork +
      (encode L m t q width firstNormal forms input).capWork ≤
      (70 * (2 * L + 1) + 5 * (2 * L) * (1 + 4 * (2 * L))) *
        q * width * baseCount L m t := by
  have hcoeff := encode_coefficientWork_le L m t q width firstNormal forms input
  have hcap := encode_capWork_le L m t q width firstNormal forms input
  have hqw : 1 ≤ q * width := by nlinarith
  have hweight : 5 * (2 * L) * (1 + 4 * (2 * L)) * baseCount L m t ≤
      (5 * (2 * L) * (1 + 4 * (2 * L)) * baseCount L m t) * (q * width) := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left
      (5 * (2 * L) * (1 + 4 * (2 * L)) * baseCount L m t) hqw
  have hcap' := hcap.trans hweight
  calc
    _ ≤ 70 * q * width * (2 * L + 1) * baseCount L m t +
        (5 * (2 * L) * (1 + 4 * (2 * L)) * baseCount L m t) * (q * width) := by
      exact Nat.add_le_add hcoeff hcap'
    _ = _ := by ring

/-- Joint correctness and storage/work specification of the implemented
encoder, with no independently evaluated leaf sweeps in its program. -/
theorem encode_contract (L m t q width : ℕ) (firstNormal : Bool) (forms : LocalForms R)
    (input : Dense (R := R) (2 * L) (rootDims L firstNormal)) (hq : 1 ≤ q) (hw : 1 ≤ width) :
    let out := encode L m t q width firstNormal forms input
    (out.leaves.map Prod.fst).Nodup ∧
      (∀ w, w ∈ out.leaves.map Prod.fst ↔ Admissible L m t w) ∧
      (∀ leaf ∈ out.leaves, leaf.2 = tensorValue L firstNormal forms input leaf.1) ∧
      formedCells q width out.formed ≤ q * width * (2 * L + 1) * baseCount L m t ∧
      out.coefficientWork + out.capWork ≤
        (70 * (2 * L + 1) + 5 * (2 * L) * (1 + 4 * (2 * L))) *
          q * width * baseCount L m t := by
  refine ⟨encode_keys_nodup L m t q width firstNormal forms input, ?_,
    (encode_correct L m t q width firstNormal forms input).2, ?_,
    encode_work_le L m t q width firstNormal forms input hq hw⟩
  · intro w
    rw [(encode_correct L m t q width firstNormal forms input).1]
    exact mem_generate_leaf L m t w
  · rw [encode, ← run_cells_eq_formed]
    simpa only [encode] using encode_cells_le L m t q width firstNormal forms input


noncomputable def generatedBaseEquiv (L m t : ℕ) :
    {w // w ∈ (generate L m t (2*L)).toFinset} ≃ BaseStates L m t where
  toFun := fun w => ⟨w.val, (mem_generate_leaf L m t w.val).mp (List.mem_toFinset.mp w.property)⟩
  invFun := fun w => ⟨w.val, List.mem_toFinset.mpr ((mem_generate_leaf L m t w.val).mpr w.property)⟩
  left_inv := fun w => by apply Subtype.ext; rfl
  right_inv := fun w => by apply Subtype.ext; rfl

theorem generate_leaf_length (L m t : ℕ) :
    (generate L m t (2*L)).length = baseCount L m t := by
  classical
  have hc := Fintype.card_congr (generatedBaseEquiv L m t)
  rw [Fintype.card_coe, List.toFinset_card_of_nodup
    (generate_nodup L m t (2*L) (le_refl _))] at hc
  exact hc

theorem encode_leaf_count (L m t q width : ℕ) (firstNormal : Bool) (forms : LocalForms R)
    (input : Dense (R := R) (2*L) (rootDims L firstNormal)) :
    (encode L m t q width firstNormal forms input).leaves.length = baseCount L m t := by
  have he := congrArg List.length (encode_correct L m t q width firstNormal forms input).1
  simpa only [List.length_map, generate_leaf_length] using he

/-- Store the already computed payloads; no leaf is re-encoded during insertion. -/
def storeRows {A : Type*} {n : ℕ} :
    StoredHighDP.Trie A → List (Word n × A) → StoredHighDP.Trie A
  | table, [] => table
  | table, row :: rows =>
    storeRows (table.write (StoredHighDP.key row.1) row.2) rows

def storeRowsCounted {A : Type*} {n : ℕ} :
    StoredHighDP.Trie A → List (Word n × A) → StoredHighDP.Trie A × ℕ
  | table, [] => (table, 0)
  | table, row :: rows =>
    let update := table.writeCounted (StoredHighDP.key row.1) row.2
    let tail := storeRowsCounted update.1 rows
    (tail.1, update.2 + tail.2)

theorem storeRowsCounted_value {A : Type*} {n : ℕ}
    (table : StoredHighDP.Trie A) (rows : List (Word n × A)) :
    (storeRowsCounted table rows).1 = storeRows table rows := by
  induction rows generalizing table with
  | nil => rfl
  | cons row rows ih => simp [storeRowsCounted, storeRows, ih]

theorem storeRowsCounted_work {A : Type*} {n : ℕ}
    (table : StoredHighDP.Trie A) (rows : List (Word n × A)) :
    (storeRowsCounted table rows).2 = (8*n+7) * rows.length := by
  induction rows generalizing table with
  | nil => simp [storeRowsCounted]
  | cons row rows ih => simp [storeRowsCounted, ih]; ring

theorem read_storeRows_absent {A : Type*} {n : ℕ}
    (table : StoredHighDP.Trie A) (rows : List (Word n × A)) (w : Word n)
    (hw : w ∉ rows.map Prod.fst) :
    (storeRows table rows).read (StoredHighDP.key w) = table.read (StoredHighDP.key w) := by
  induction rows generalizing table with
  | nil => rfl
  | cons row rows ih =>
    have hne : w ≠ row.1 := by intro h; apply hw; simp [h]
    have ht : w ∉ rows.map Prod.fst := by intro h; apply hw; simp [h]
    rw [storeRows, ih _ ht]
    apply StoredHighDP.Trie.read_write_other
    intro h
    exact hne (StoredHighDP.key_injective n h)

theorem read_storeRows_member {A : Type*} {n : ℕ}
    (table : StoredHighDP.Trie A) (rows : List (Word n × A))
    (hnd : (rows.map Prod.fst).Nodup) (row : Word n × A) (hr : row ∈ rows) :
    (storeRows table rows).read (StoredHighDP.key row.1) = some row.2 := by
  induction rows generalizing table with
  | nil => simp at hr
  | cons first rows ih =>
    have hn := List.nodup_cons.mp hnd
    obtain h | h := List.mem_cons.mp hr
    · subst row
      rw [storeRows, read_storeRows_absent _ _ _ hn.1]
      exact StoredHighDP.Trie.read_write_same _ _ _
    · exact ih _ hn.2 h

structure StoredResult (R : Type u) (N : ℕ) where
  encoding : Result R N
  table : StoredHighDP.Trie R
  trieWork : ℕ

def encodeStored (L m t q width : ℕ) (firstNormal : Bool) (forms : LocalForms R)
    (input : Dense (R := R) (2*L) (rootDims L firstNormal)) : StoredResult R (2*L) :=
  let out := encode L m t q width firstNormal forms input
  let stored := storeRowsCounted .empty out.leaves
  ⟨out, stored.1, stored.2⟩

theorem encodeStored_complete (L m t q width : ℕ) (firstNormal : Bool) (forms : LocalForms R)
    (input : Dense (R := R) (2*L) (rootDims L firstNormal)) (w : BaseStates L m t) :
    (encodeStored L m t q width firstNormal forms input).table.read (StoredHighDP.key w.val) =
      some (tensorValue L firstNormal forms input w.val) := by
  have hw : w.val ∈ (encode L m t q width firstNormal forms input).leaves.map Prod.fst := by
    rw [(encode_correct L m t q width firstNormal forms input).1]
    exact (mem_generate_leaf _ _ _ _).mpr w.property
  obtain ⟨row, hr, he⟩ := List.mem_map.mp hw
  have hv := (encode_correct L m t q width firstNormal forms input).2 row hr
  have ht := read_storeRows_member (StoredHighDP.Trie.empty)
    (encode L m t q width firstNormal forms input).leaves
    (encode_keys_nodup L m t q width firstNormal forms input) row hr
  simpa only [encodeStored, storeRowsCounted_value, he, hv] using ht

theorem encodeStored_trieWork (L m t q width : ℕ) (firstNormal : Bool) (forms : LocalForms R)
    (input : Dense (R := R) (2*L) (rootDims L firstNormal)) :
    (encodeStored L m t q width firstNormal forms input).trieWork =
      (8*(2*L)+7) * baseCount L m t := by
  simp only [encodeStored, storeRowsCounted_work, encode_leaf_count]

/-- Literal degree-zero coefficients: the shifted normal p1 term is absent. -/
def baseCoefficient (normal : Bool) (row : Label) (col : Fin 4) : ℤ :=
  if SparseLocalForms.shifted normal row col then 0
  else SparseLocalForms.rowCoefficients normal row col

theorem base_localRow_zero {q : ℕ} (normal : Bool) (row : Label)
    (children : Fin 4 → Fin q → ℤ) (residue : Fin q) :
    SparseLocalForms.localRow normal row (fun col (_ : Fin 1) r => children col r) 0 residue =
      ∑ col, baseCoefficient normal row col * children col residue := by
  unfold SparseLocalForms.localRow
  apply Finset.sum_congr rfl
  intro col _
  by_cases hs : SparseLocalForms.shifted normal row col = true <;>
    simp [baseCoefficient, SparseLocalForms.readCell, hs]

theorem normal_private_H0 : baseCoefficient true 4 = ![-1,-1,0,0] := by
  funext col
  fin_cases col <;> rfl

theorem opposite_private_H0 : baseCoefficient false 4 = ![2,0,0,0] := by
  funext col
  fin_cases col <;> rfl

/-- Pointwise ring operations are transported back through `Vector.ofFn`.
Thus every coefficient operation returns an allocated coefficient vector. -/
def vectorEquiv (q : ℕ) : Vector ℤ q ≃ (Fin q → ℤ) where
  toFun v := v.get
  invFun f := Vector.ofFn f
  left_inv v := Vector.ofFn_getElem
  right_inv f := by funext i; exact Vector.get_ofFn f i

instance vectorCommRing (q : ℕ) : CommRing (Vector ℤ q) := (vectorEquiv q).commRing

def eval (q : ℕ) (r : Fin q) : Vector ℤ q →+* ℤ :=
  (Pi.evalRingHom (fun _ : Fin q => ℤ) r).comp (vectorEquiv q).ringEquiv.toRingHom

@[simp] theorem eval_apply (q : ℕ) (r : Fin q) (v : Vector ℤ q) : eval q r v = v.get r := rfl

@[simp] theorem get_intCast (q : ℕ) (r : Fin q) (z : ℤ) : (z : Vector ℤ q).get r = z := by
  change eval q r (z : Vector ℤ q) = z
  exact map_intCast (eval q r) z

theorem vector_add_materialized (q : ℕ) (x y : Vector ℤ q) :
    @Add.add (Vector ℤ q) (vectorEquiv q).add x y =
      Vector.ofFn (fun r => x.get r + y.get r) := rfl

theorem vector_mul_materialized (q : ℕ) (x y : Vector ℤ q) :
    x * y = Vector.ofFn (fun r => x.get r * y.get r) := by
  apply (vectorEquiv q).injective
  funext r
  change (x*y).get r = (Vector.ofFn (fun r => x.get r * y.get r)).get r
  simpa only [eval_apply, Vector.get_ofFn] using (map_mul (eval q r) x y)

theorem map_tensorSum {A B : Type*} [CommSemiring A] [CommSemiring B]
    (f : A →+* B) {n : ℕ} (dims : Fin n → ℕ)
    (forms : (i : Fin n) → Fin (dims i) → A)
    (input : EncoderCorrectness.Coordinates dims → A) :
    f (EncoderCorrectness.tensorSum dims forms input) =
      EncoderCorrectness.tensorSum dims (fun i a => f (forms i a)) (fun a => f (input a)) := by
  unfold EncoderCorrectness.tensorSum
  simp only [map_sum, map_mul, map_prod]

theorem tensorValue_get {q : ℕ} (L : ℕ) (b : Bool) (forms : LocalForms ℤ)
    (input : Dense (R := Vector ℤ q) (2*L) (rootDims L b))
    (word : Word (2*L)) (r : Fin q) :
    (tensorValue L b (fun d l a => (forms d l a : Vector ℤ q)) input word).get r =
      SourceCoordinates.vectorTensorValue L b forms input word r := by
  change eval q r (tensorValue L b (fun d l a => (forms d l a : Vector ℤ q)) input word) = _
  unfold tensorValue SourceCoordinates.vectorTensorValue
  rw [map_tensorSum]
  simp only [eval_apply, get_intCast]
  rfl

/-- Width is literally one: no auxiliary channels or positive degrees are stored. -/
def encodeVector (L m t q : ℕ) (firstNormal : Bool) (forms : LocalForms ℤ)
    (input : Dense (R := Vector ℤ q) (2*L) (rootDims L firstNormal)) :
    StoredResult (Vector ℤ q) (2*L) :=
  encodeStored L m t q 1 firstNormal (fun d a col => (forms d a col : Vector ℤ q)) input

def readBase {q L m t : ℕ} (out : StoredResult (Vector ℤ q) (2*L))
    (w : BaseStates L m t) : Vector ℤ q :=
  (out.table.read (StoredHighDP.key w.val)).getD (Vector.replicate q 0)

theorem encodeVector_read {q L m t : ℕ} (firstNormal : Bool) (forms : LocalForms ℤ)
    (input : Dense (R := Vector ℤ q) (2*L) (rootDims L firstNormal))
    (w : BaseStates L m t) (r : Fin q) :
    (readBase (encodeVector L m t q firstNormal forms input) w).get r =
      SourceCoordinates.vectorTensorValue L firstNormal forms input w.val r := by
  rw [readBase, encodeVector, encodeStored_complete, Option.getD_some, tensorValue_get]

theorem encodeVector_cells {q L m t : ℕ} (firstNormal : Bool) (forms : LocalForms ℤ)
    (input : Dense (R := Vector ℤ q) (2*L) (rootDims L firstNormal)) :
    formedCells q 1 (encodeVector L m t q firstNormal forms input).encoding.formed ≤
      q * (2*L+1) * baseCount L m t := by
  change formedCells q 1 (encode L m t q 1 firstNormal
    (fun d a col => (forms d a col : Vector ℤ q)) input).formed ≤ _
  rw [encode, ← run_cells_eq_formed]
  simpa only [encode, Nat.mul_one] using encode_cells_le L m t q 1 firstNormal
    (fun d a col => (forms d a col : Vector ℤ q)) input

theorem encodeVector_work {q L m t : ℕ} (firstNormal : Bool) (forms : LocalForms ℤ)
    (input : Dense (R := Vector ℤ q) (2*L) (rootDims L firstNormal)) (hq : 1 ≤ q) :
    (encodeVector L m t q firstNormal forms input).encoding.coefficientWork +
      (encodeVector L m t q firstNormal forms input).encoding.capWork +
      (encodeVector L m t q firstNormal forms input).trieWork ≤
      (70*(2*L+1) + 5*(2*L)*(1+4*(2*L)) + 8*(2*L)+7) * q * baseCount L m t := by
  have he := encode_work_le L m t q 1 firstNormal
    (fun d a col => (forms d a col : Vector ℤ q)) input hq (le_refl 1)
  have ht := encodeStored_trieWork L m t q 1 firstNormal
    (fun d a col => (forms d a col : Vector ℤ q)) input
  have hw : (8*(2*L)+7) * baseCount L m t ≤ (8*(2*L)+7) * q * baseCount L m t := by
    simpa only [Nat.mul_one, Nat.mul_assoc] using
      Nat.mul_le_mul_right (baseCount L m t) (Nat.mul_le_mul_left (8*(2*L)+7) hq)
  change (encode L m t q 1 firstNormal _ input).coefficientWork +
    (encode L m t q 1 firstNormal _ input).capWork +
    (encodeStored L m t q 1 firstNormal _ input).trieWork ≤ _
  rw [ht]
  simp only [Nat.mul_one] at he
  nlinarith

theorem lift_baseLeaf {L : ℕ} (w : Word (2*L)) (hn : ∀ i, (w i).val ≠ 5) :
    SourceCoordinates.liftLeaf (HighBoxDP.baseLeaf w hn) = w := by
  funext i
  apply Fin.ext
  rfl

noncomputable def encodeLeftSource {q L m t : ℕ}
    (X : CompleteThinProduct.SourceWord L → CyclicRing.Cyclic q) :
    StoredResult (Vector ℤ q) (2*L) :=
  encodeVector L m t q true (SourceCoordinates.leftForms L) (SourceCoordinates.leftVectorInput X)

noncomputable def encodeRightSource {q L m t : ℕ}
    (Y : CompleteThinProduct.SourceWord L → CyclicRing.Cyclic q) :
    StoredResult (Vector ℤ q) (2*L) :=
  encodeVector L m t q false (SourceCoordinates.rightForms L) (SourceCoordinates.rightVectorInput Y)

theorem encodeLeftSource_read {q L m t : ℕ} [NeZero q]
    (X : CompleteThinProduct.SourceWord L → CyclicRing.Cyclic q)
    (w : BaseStates L m t) (r : Fin q) :
    (readBase (encodeLeftSource (m:=m) (t:=t) X) w).get r =
      (∑ a : CompleteThinProduct.SourceWord L, X a *
        ∏ i, CompleteThinProduct.sourceF i (HighBoxDP.baseLeaf w.val w.property.2 i) a) r := by
  rw [encodeLeftSource, encodeVector_read]
  have h := SourceCoordinates.left_vectorTensorValue X (HighBoxDP.baseLeaf w.val w.property.2) r
  simpa only [lift_baseLeaf] using h

theorem encodeRightSource_read {q L m t : ℕ} [NeZero q]
    (Y : CompleteThinProduct.SourceWord L → CyclicRing.Cyclic q)
    (w : BaseStates L m t) (r : Fin q) :
    (readBase (encodeRightSource (m:=m) (t:=t) Y) w).get r =
      (∑ a : CompleteThinProduct.SourceWord L, Y a *
        ∏ i, CompleteThinProduct.sourceG i (HighBoxDP.baseLeaf w.val w.property.2 i) a) r := by
  rw [encodeRightSource, encodeVector_read]
  have h := SourceCoordinates.right_vectorTensorValue Y (HighBoxDP.baseLeaf w.val w.property.2) r
  simpa only [lift_baseLeaf] using h

theorem generateWords_eq (L m t d : ℕ) :
    ArrayKeys.generateWords ((List.finRange 5).map baseLabel) (baseTest L m t) d =
      generate L m t d := by
  induction d with
  | zero => rfl
  | succ d ih =>
    simp only [ArrayKeys.generateWords, generate]
    split
    · simp only [ih, List.map_map, Function.comp_def]
      rfl
    · rfl

/-- A concrete vector-key generator has exactly the same five-letter prefixes. -/
theorem arrayBaseGenerate_refine (L m t d : ℕ) :
    (ArrayKeys.baseGenerate L m t d).map ArrayKeys.toWord = generate L m t d := by
  have h := ArrayKeys.baseGenerate_refine (baseTest L m t)
    (fun w => baseTest_eq_true L m t w) d
  exact h.trans (generateWords_eq L m t d)

end ThinMatrix.HighBaseEncoder

#print axioms ThinMatrix.HighBaseEncoder.mem_generate_leaf
#print axioms ThinMatrix.HighBaseEncoder.completeBase_injective
#print axioms ThinMatrix.HighBaseEncoder.base_layer_volume_le
#print axioms ThinMatrix.HighBaseEncoder.run_invariant
#print axioms ThinMatrix.HighBaseEncoder.encode_contract
#print axioms ThinMatrix.HighBaseEncoder.encodeStored_complete
#print axioms ThinMatrix.HighBaseEncoder.normal_private_H0
#print axioms ThinMatrix.HighBaseEncoder.base_localRow_zero
#print axioms ThinMatrix.HighBaseEncoder.vector_add_materialized
#print axioms ThinMatrix.HighBaseEncoder.vector_mul_materialized
#print axioms ThinMatrix.HighBaseEncoder.tensorValue_get
#print axioms ThinMatrix.HighBaseEncoder.encodeVector_read
#print axioms ThinMatrix.HighBaseEncoder.encodeVector_cells
#print axioms ThinMatrix.HighBaseEncoder.encodeVector_work
#print axioms ThinMatrix.HighBaseEncoder.encodeLeftSource_read
#print axioms ThinMatrix.HighBaseEncoder.encodeRightSource_read
#print axioms ThinMatrix.HighBaseEncoder.arrayBaseGenerate_refine
