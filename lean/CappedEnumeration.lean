import CacheBounds

/-!
# Direct generation of the genuine capped cache prefixes

The generator starts with the zero word. At each depth below `2*L` it
extends each retained parent by the six local labels, then applies an
explicit Boolean cap test. It never enumerates the Cartesian family of
all length-`2*L` words. The counters record local extension attempts and
three linear scans of physical positions for each cap test.

Set/cardinality arguments below are specifications of this program, not
the implementation of the enumeration. Per-word storage and function
updates may be charged another polynomial factor in `L`; no word-RAM
constant-time assumption about functions is made.
-/

namespace ThinMatrix.CappedEnumeration

open CacheBounds

/-- An explicit computable scan of positions, not a family enumeration. -/
def countBool {n : ℕ} (w : Word n) (p : Fin n → Label → Bool) : ℕ :=
  ((List.finRange n).filter (fun i => p i (w i))).length

theorem countBool_eq {n : ℕ} (w : Word n) (p : Fin n → Label → Bool) :
    countBool w p = countPositions w (fun i a => p i a = true) := by
  classical
  let xs := (List.finRange n).filter (fun i => p i (w i))
  have hnd : xs.Nodup := (List.nodup_finRange n).filter _
  have hset : xs.toFinset = Finset.univ.filter (fun i => p i (w i) = true) := by
    ext i
    simp [xs]
  change xs.length = _
  rw [← List.toFinset_card_of_nodup hnd, hset]
  simp only [countPositions]

/-- Three literal position counts implement both half caps and the joint
channel cap. Every invocation scans at most `3*(2*L)` positions. -/
def capTest (L m t : ℕ) (w : Word (2 * L)) : Bool :=
  decide (countBool w (fun i a => decide (i.val < L ∧ 4 ≤ a.val)) ≤ m) &&
  decide (countBool w (fun i a => decide (L ≤ i.val ∧ 4 ≤ a.val)) ≤ m) &&
  decide (countBool w (fun _ a => decide (a.val = 5)) ≤ t)

theorem capTest_eq_true (L m t : ℕ) (w : Word (2 * L)) :
    capTest L m t w = true ↔ Retained L m t w := by
  have hcount (p : Fin (2 * L) → Label → Prop) (dp : ∀ i a, Decidable (p i a)) :
      countBool w (fun i a => @decide (p i a) (dp i a)) = countPositions w p := by
    rw [countBool_eq]
    simp only [decide_eq_true_eq]
  simp only [capTest, Bool.and_eq_true, decide_eq_true_eq]
  rw [hcount (fun i a => i.val < L ∧ 4 ≤ a.val) (fun i a => inferInstance),
    hcount (fun i a => L ≤ i.val ∧ 4 ≤ a.val) (fun i a => inferInstance), hcount (fun _ a => a.val = 5) (fun i a => inferInstance)]
  simp only [Retained, distinguished, channel, and_assoc]

def zeroWord (n : ℕ) : Word n := fun _ => 0

theorem zero_retained (L m t : ℕ) : Retained L m t (zeroWord (2 * L)) := by
  classical
  simp [Retained, countPositions, zeroWord, distinguished, channel]

/-- Extend the unique canonical coordinate at the next depth. -/
def put {n : ℕ} (d : ℕ) (hd : d < n) (w : Word n) (a : Label) : Word n :=
  Function.update w ⟨d, hd⟩ a

theorem put_prefix {n d : ℕ} (hd : d < n) (w : Word n) (a : Label)
    (hp : IsPrefix d w) : IsPrefix (d + 1) (put d hd w a) := by
  intro i hi
  have hne : i ≠ (⟨d, hd⟩ : Fin n) := by intro h; have he : i.val = d := congrArg Fin.val h; omega
  simpa [put, Function.update_of_ne hne] using hp i (by omega)

theorem put_label_injective {n d : ℕ} (hd : d < n) (w : Word n) :
    Function.Injective (put d hd w) := by
  intro a b hab
  have h := congrFun hab ⟨d, hd⟩
  simpa [put] using h

/-- Both the parent and its new label are recoverable from an extension
because the parent is canonically zero at this coordinate. -/
theorem put_pair_injective {n d : ℕ} (hd : d < n) (w v : Word n) (a b : Label)
    (hw : IsPrefix d w) (hv : IsPrefix d v) (heq : put d hd w a = put d hd v b) :
    w = v ∧ a = b := by
  have hab : a = b := by
    have h := congrFun heq ⟨d, hd⟩
    simpa [put] using h
  refine ⟨?_, hab⟩
  funext i
  by_cases hi : i = (⟨d, hd⟩ : Fin n)
  · subst i
    rw [hw _ (by simp), hv _ (by simp)]
  · have h := congrFun heq i
    simpa [put, Function.update_of_ne hi] using h

theorem trim_isPrefix {n : ℕ} (d : ℕ) (w : Word n) : IsPrefix d (trimWord d w) := by
  intro i hi
  simp [trimWord, show ¬i.val < d by omega]

theorem put_trim {n d : ℕ} (hd : d < n) (w : Word n) (hp : IsPrefix (d + 1) w) :
    put d hd (trimWord d w) (w ⟨d, hd⟩) = w := by
  funext i
  by_cases hi : i = (⟨d, hd⟩ : Fin n)
  · subst i
    simp [put]
  · rw [put, Function.update_of_ne hi]
    by_cases hbefore : i.val < d
    · simp [trimWord, hbefore]
    · have hval : i.val ≠ d := by intro h; exact hi (Fin.ext h)
      have hz := hp i (by omega)
      simp [trimWord, hbefore, hz]

def children (L m t d : ℕ) (hd : d < 2 * L) (w : Word (2 * L)) :
    List (Word (2 * L)) :=
  ((List.finRange 6).map (put d hd w)).filter (capTest L m t)

/-- The only recursive construction of the output family. No Cartesian
word enumeration appears in this executable definition. -/
def generate (L m t : ℕ) : ℕ → List (Word (2 * L))
  | 0 => [zeroWord (2 * L)]
  | d + 1 => if hd : d < 2 * L then
      (generate L m t d).flatMap (children L m t d hd) else []

theorem mem_children (L m t d : ℕ) (hd : d < 2 * L) (w v : Word (2 * L)) :
    v ∈ children L m t d hd w ↔ ∃ a : Label, put d hd w a = v ∧ Retained L m t v := by
  simp only [children, List.mem_filter, List.mem_map, List.mem_finRange, true_and,
    capTest_eq_true]
  aesop

theorem mem_generate (L m t d : ℕ) (hd : d ≤ 2 * L) (w : Word (2 * L)) :
    w ∈ generate L m t d ↔ IsPrefix d w ∧ Retained L m t w := by
  induction d generalizing w with
  | zero =>
      simp only [generate, List.mem_singleton]
      constructor
      · intro hw
        subst w
        exact ⟨fun i hi => rfl, zero_retained L m t⟩
      · intro hw
        funext i
        exact hw.1 i (Nat.zero_le _)
  | succ d ih =>
      have hlt : d < 2 * L := by omega
      have hprev : d ≤ 2 * L := by omega
      rw [generate, dif_pos hlt, List.mem_flatMap]
      constructor
      · rintro ⟨p, hp, hc⟩
        obtain ⟨a, rfl, hret⟩ := (mem_children L m t d hlt p w).mp hc
        exact ⟨put_prefix hlt p a ((ih hprev p).mp hp).1, hret⟩
      · rintro ⟨hp, hret⟩
        have htrim := trim_retained d (⟨w, hret⟩ : Leaves L m t)
        refine ⟨trimWord d w, (ih hprev _).mpr ⟨trim_isPrefix d w, htrim⟩, ?_⟩
        apply (mem_children L m t d hlt _ w).mpr
        exact ⟨w ⟨d, hlt⟩, put_trim hlt w hp, hret⟩

theorem children_nodup (L m t d : ℕ) (hd : d < 2 * L) (w : Word (2 * L)) :
    (children L m t d hd w).Nodup := by
  exact ((List.nodup_finRange 6).map (put_label_injective hd w)).filter _

theorem generate_nodup (L m t d : ℕ) (hd : d ≤ 2 * L) :
    (generate L m t d).Nodup := by
  induction d with
  | zero => simp [generate]
  | succ d ih =>
      have hlt : d < 2 * L := by omega
      have hprev : d ≤ 2 * L := by omega
      rw [generate, dif_pos hlt]
      apply List.nodup_flatMap.mpr
      refine ⟨fun w hw => children_nodup L m t d hlt w, ?_⟩
      apply (ih hprev).imp_of_mem
      intro w v hw hv hne
      apply List.disjoint_left.mpr
      intro z hzw hzv
      obtain ⟨a, ha, _⟩ := (mem_children L m t d hlt w z).mp hzw
      obtain ⟨b, hb, _⟩ := (mem_children L m t d hlt v z).mp hzv
      have hpw := ((mem_generate L m t d hprev w).mp hw).1
      have hpv := ((mem_generate L m t d hprev v).mp hv).1
      exact hne (put_pair_injective hlt w v a b hpw hpv (ha.trans hb.symm)).1

/-- Exact set specification of the generated list at every legal depth. -/
theorem generated_set_exact (L m t d : ℕ) (hd : d ≤ 2 * L) :
    {w | w ∈ generate L m t d} =
      {w : Word (2 * L) | IsPrefix d w ∧ Retained L m t w} := by
  ext w
  exact mem_generate L m t d hd w

/-- The specification equivalence does not enumerate all words; the only
finite set used here is the list already produced by the program. -/
noncomputable def generatedPrefixEquiv (L m t d : ℕ) (hd : d ≤ 2 * L) :
    {w // w ∈ (generate L m t d).toFinset} ≃ Prefixes L m t d where
  toFun := fun w => ⟨w.val, (mem_generate L m t d hd w.val).mp (List.mem_toFinset.mp w.property)⟩
  invFun := fun w => ⟨w.val, List.mem_toFinset.mpr ((mem_generate L m t d hd w.val).mpr w.property)⟩
  left_inv := fun w => by apply Subtype.ext; rfl
  right_inv := fun w => by apply Subtype.ext; rfl

theorem generate_length_eq_prefix_card (L m t d : ℕ) (hd : d ≤ 2 * L) :
    (generate L m t d).length = Fintype.card (Prefixes L m t d) := by
  classical
  have hc := Fintype.card_congr (generatedPrefixEquiv L m t d hd)
  rw [Fintype.card_coe, List.toFinset_card_of_nodup (generate_nodup L m t d hd)] at hc
  exact hc

theorem mem_generate_leaf (L m t : ℕ) (w : Word (2 * L)) :
    w ∈ generate L m t (2 * L) ↔ Retained L m t w := by
  rw [mem_generate L m t (2 * L) (le_refl _) w]
  have hp : IsPrefix (2 * L) w := by intro i hi; omega
  exact and_iff_right hp

noncomputable def generatedLeafEquiv (L m t : ℕ) :
    {w // w ∈ (generate L m t (2 * L)).toFinset} ≃ Leaves L m t where
  toFun := fun w => ⟨w.val, (mem_generate_leaf L m t w.val).mp (List.mem_toFinset.mp w.property)⟩
  invFun := fun w => ⟨w.val, List.mem_toFinset.mpr ((mem_generate_leaf L m t w.val).mpr w.property)⟩
  left_inv := fun w => by apply Subtype.ext; rfl
  right_inv := fun w => by apply Subtype.ext; rfl

theorem generate_leaf_length (L m t : ℕ) :
    (generate L m t (2 * L)).length = retainedLeafCount L m t := by
  classical
  have hc := Fintype.card_congr (generatedLeafEquiv L m t)
  rw [Fintype.card_coe, List.toFinset_card_of_nodup (generate_nodup L m t (2 * L) (le_refl _))] at hc
  exact hc

/-- Joint value/cost result of the same generation recursion. -/
structure Generated (L : ℕ) where
  words : List (Word (2 * L))
  extensions : ℕ
  positionTests : ℕ

def generateWithWork (L m t : ℕ) : ℕ → Generated L
  | 0 => ⟨[zeroWord (2 * L)], 0, 0⟩
  | d + 1 =>
      let previous := generateWithWork L m t d
      if hd : d < 2 * L then
        { words := previous.words.flatMap (children L m t d hd)
          extensions := previous.extensions + 6 * previous.words.length
          positionTests := previous.positionTests + (3 * (2 * L)) * (6 * previous.words.length) }
      else { words := [], extensions := previous.extensions, positionTests := previous.positionTests }

theorem generateWithWork_words (L m t d : ℕ) :
    (generateWithWork L m t d).words = generate L m t d := by
  induction d with
  | zero => rfl
  | succ d ih =>
      simp only [generateWithWork, generate]
      split <;> simp [ih]

/-- There are exactly six cap tests per retained parent, including tests
of children that are rejected. No filtering cost is charged only to leaves. -/
theorem extensions_eq (L m t d : ℕ) (hd : d ≤ 2 * L) :
    (generateWithWork L m t d).extensions =
      6 * ∑ j ∈ Finset.range d, (generate L m t j).length := by
  induction d with
  | zero => simp [generateWithWork]
  | succ d ih =>
      have hlt : d < 2 * L := by omega
      have hprev : d ≤ 2 * L := by omega
      simp only [generateWithWork, dif_pos hlt, ih hprev, generateWithWork_words,
        Finset.sum_range_succ]
      ring

theorem positionTests_eq (L m t d : ℕ) :
    (generateWithWork L m t d).positionTests =
      (3 * (2 * L)) * (generateWithWork L m t d).extensions := by
  induction d with
  | zero => simp [generateWithWork]
  | succ d ih =>
      simp only [generateWithWork]
      split
      · simp only [ih]
        ring
      · exact ih

theorem extensions_le (L m t d : ℕ) (hd : d ≤ 2 * L) :
    (generateWithWork L m t d).extensions ≤ 6 * d * retainedLeafCount L m t := by
  rw [extensions_eq L m t d hd]
  calc
    _ ≤ 6 * ∑ _j ∈ Finset.range d, retainedLeafCount L m t := by
      apply Nat.mul_le_mul_left
      apply Finset.sum_le_sum
      intro j hj
      have hj' : j ≤ 2 * L := by have := Finset.mem_range.mp hj; omega
      rw [generate_length_eq_prefix_card L m t j hj']
      exact prefix_count_le_leafCount L m t j hj' true
    _ = _ := by simp; ring

/-- The complete enumeration costs a polynomial in L times the actual
retained leaf count S. This includes all rejected local children. -/
theorem enumeration_work_le (L m t : ℕ) :
    (generateWithWork L m t (2 * L)).extensions +
      (generateWithWork L m t (2 * L)).positionTests ≤
        (1 + 3 * (2 * L)) * (6 * (2 * L)) * retainedLeafCount L m t := by
  rw [positionTests_eq]
  calc
    _ = (1 + 3 * (2 * L)) * (generateWithWork L m t (2 * L)).extensions := by ring
    _ ≤ (1 + 3 * (2 * L)) * (6 * (2 * L) * retainedLeafCount L m t) :=
      Nat.mul_le_mul_left _ (extensions_le L m t (2 * L) (le_refl _))
    _ = _ := by ring

/-- Total retained prefix records, including the root and leaves. -/
theorem all_prefix_records_le (L m t : ℕ) :
    (∑ d ∈ Finset.range (2 * L + 1), (generate L m t d).length) ≤
      (2 * L + 1) * retainedLeafCount L m t := by
  calc
    _ ≤ ∑ _d ∈ Finset.range (2 * L + 1), retainedLeafCount L m t := by
      apply Finset.sum_le_sum
      intro d hd
      have hd' : d ≤ 2 * L := by have := Finset.mem_range.mp hd; omega
      rw [generate_length_eq_prefix_card L m t d hd']
      exact prefix_count_le_leafCount L m t d hd' true
    _ = _ := by simp

theorem leafCount_pos (L m t : ℕ) : 0 < retainedLeafCount L m t := by
  apply Fintype.card_pos_iff.mpr
  exact ⟨⟨zeroWord (2 * L), zero_retained L m t⟩⟩

/-- Include creation of the zero root even in the boundary case L=0. -/
theorem enumeration_work_with_root_le (L m t : ℕ) :
    1 + (generateWithWork L m t (2 * L)).extensions +
      (generateWithWork L m t (2 * L)).positionTests ≤
        (1 + (1 + 3 * (2 * L)) * (6 * (2 * L))) * retainedLeafCount L m t := by
  have hroot : 1 ≤ retainedLeafCount L m t := leafCount_pos L m t
  have hw := enumeration_work_le L m t
  calc
    _ = 1 + ((generateWithWork L m t (2 * L)).extensions +
        (generateWithWork L m t (2 * L)).positionTests) := by omega
    _ ≤ retainedLeafCount L m t +
        (1 + 3 * (2 * L)) * (6 * (2 * L)) * retainedLeafCount L m t := Nat.add_le_add hroot hw
    _ = _ := by ring

/-- The returned program value is itself a duplicate-free exact leaf
enumeration, with its own root-inclusive work counter bounded by S. -/
theorem cache_program_contract (L m t : ℕ) :
    let out := generateWithWork L m t (2 * L)
    out.words.Nodup ∧
      (∀ w, w ∈ out.words ↔ Retained L m t w) ∧
      out.words.length = retainedLeafCount L m t ∧
      1 + out.extensions + out.positionTests ≤
        (1 + (1 + 3 * (2 * L)) * (6 * (2 * L))) * retainedLeafCount L m t := by
  refine ⟨?_, ?_, ?_, enumeration_work_with_root_le L m t⟩
  · simpa only [generateWithWork_words] using generate_nodup L m t (2 * L) (le_refl _)
  · intro w
    rw [generateWithWork_words]
    exact mem_generate_leaf L m t w
  · rw [generateWithWork_words]
    exact generate_leaf_length L m t

/- Actual execution examples; the general correctness/resource theorems
above do not depend on these finite evaluations. -/
#eval let out := generateWithWork 1 1 1 2
  (out.words.length, out.extensions, out.positionTests)
#eval let out := generateWithWork 2 0 0 4
  (out.words.length, out.extensions, out.positionTests)
#eval let out := generateWithWork 0 0 0 0
  (out.words.length, out.extensions, out.positionTests)

end ThinMatrix.CappedEnumeration

#print axioms ThinMatrix.CappedEnumeration.mem_generate
#print axioms ThinMatrix.CappedEnumeration.generate_nodup
#print axioms ThinMatrix.CappedEnumeration.generate_leaf_length
#print axioms ThinMatrix.CappedEnumeration.enumeration_work_le
#print axioms ThinMatrix.CappedEnumeration.enumeration_work_with_root_le
#print axioms ThinMatrix.CappedEnumeration.cache_program_contract
