import Mathlib

/-!
# Finite storage bound for the genuine aligned capped cache language

Labels 0,1,2,3 are ordinary, 4 is the distinguished baseline, and 5 is
its channel alternative. A retained word has at most `m` distinguished
letters in each physical half and at most `t` channel letters jointly.
Prefixes are represented by their canonical zero extension. Raw suffix
coordinates have dimension four on a normal position and three on an
opposite position; the roles swap on the second source.

The completion map below is an actual injection of every prefix/remaining
raw-array coordinate into a retained leaf. Its construction does not assume
an asserted leaf count, the binomial formula, an entropy estimate, or a
cost bound. The resulting bound covers every intermediate array and their
sum over all `2*L+1` depths.

This file does not yet identify the leaf cardinality with formula (A8),
prove entropy/word-RAM asymptotics, or establish an APSP algorithm.
-/

namespace ThinMatrix.CacheBounds

abbrev Label := Fin 6
abbrev Word (n : ℕ) := Fin n → Label

/-- The actual distinguished-position predicate. -/
def distinguished (a : Label) : Prop := 4 ≤ a.val
/-- The actual unique channel label. -/
def channel (a : Label) : Prop := a.val = 5

/-- Count a predicate in a genuine finite word. -/
noncomputable def countPositions {n : ℕ} (w : Word n)
    (p : Fin n → Label → Prop) : ℕ := by
  classical
  exact (Finset.univ.filter (fun i => p i (w i))).card

/-- The exact two half caps and joint channel cap. -/
def Retained (L m t : ℕ) (w : Word (2 * L)) : Prop :=
  countPositions w (fun i a => i.val < L ∧ distinguished a) ≤ m ∧
  countPositions w (fun i a => L ≤ i.val ∧ distinguished a) ≤ m ∧
  countPositions w (fun _ a => channel a) ≤ t

abbrev Leaves (L m t : ℕ) := {w : Word (2 * L) // Retained L m t w}

/-- A genuine length-d prefix, stored by its canonical zero extension. -/
def IsPrefix {n : ℕ} (d : ℕ) (w : Word n) : Prop :=
  ∀ i, d ≤ i.val → w i = 0

abbrev Prefixes (L m t d : ℕ) :=
  {w : Word (2 * L) // IsPrefix d w ∧ Retained L m t w}

/-- True selects the source normal on the first physical half. -/
def rawDim (L : ℕ) (firstNormal : Bool) (pos : ℕ) : ℕ :=
  if (pos < L) = (firstNormal = true) then 4 else 3

@[simp] theorem rawDim_le_four (L : ℕ) (firstNormal : Bool) (pos : ℕ) :
    rawDim L firstNormal pos ≤ 4 := by
  unfold rawDim
  split <;> omega

@[simp] theorem rawDim_pos (L : ℕ) (firstNormal : Bool) (pos : ℕ) :
    0 < rawDim L firstNormal pos := by
  unfold rawDim
  split <;> omega

/-- All actual remaining raw input coordinates, including structural zeros. -/
abbrev RawSuffix (L d : ℕ) (firstNormal : Bool) :=
  (i : Fin (2 * L - d)) → Fin (rawDim L firstNormal (d + i.val))

noncomputable instance leavesFintype (L m t : ℕ) : Fintype (Leaves L m t) :=
  Fintype.ofFinite _
noncomputable instance prefixesFintype (L m t d : ℕ) :
    Fintype (Prefixes L m t d) := Fintype.ofFinite _

/-- Embed a raw coordinate as an ordinary label, with no distinguished or
channel contribution. -/
def ordinaryLabel {L d : ℕ} {firstNormal : Bool} (i : Fin (2 * L - d))
    (a : Fin (rawDim L firstNormal (d + i.val))) : Label :=
  ⟨a.val, lt_of_lt_of_le a.isLt (le_trans (rawDim_le_four _ _ _) (by omega))⟩

theorem ordinaryLabel_lt_four {L d : ℕ} {firstNormal : Bool}
    (i : Fin (2 * L - d))
    (a : Fin (rawDim L firstNormal (d + i.val))) :
    (ordinaryLabel i a).val < 4 :=
  lt_of_lt_of_le a.isLt (rawDim_le_four _ _ _)

/-- Complete the prefix with the actual raw suffix, encoded as ordinary
labels. The cap-preservation proof is below. -/
def completeWord {L m t d : ℕ} (p : Prefixes L m t d)
    {firstNormal : Bool} (a : RawSuffix L d firstNormal) : Word (2 * L) :=
  fun i => if h : i.val < d then p.val i else
    ordinaryLabel ⟨i.val - d, by omega⟩ (a ⟨i.val - d, by omega⟩)

@[simp] theorem completeWord_before {L m t d : ℕ} (p : Prefixes L m t d)
    {firstNormal : Bool} (a : RawSuffix L d firstNormal) (i : Fin (2 * L))
    (h : i.val < d) : completeWord p a i = p.val i := by
  simp [completeWord, h]

theorem completeWord_after_lt_four {L m t d : ℕ} (p : Prefixes L m t d)
    {firstNormal : Bool} (a : RawSuffix L d firstNormal) (i : Fin (2 * L))
    (h : d ≤ i.val) : (completeWord p a i).val < 4 := by
  simp only [completeWord, dif_neg (by omega : ¬ i.val < d)]
  exact ordinaryLabel_lt_four _ _

/-- Ordinary completion preserves exactly the distinguished support. -/
theorem complete_distinguished_iff {L m t d : ℕ} (p : Prefixes L m t d)
    {firstNormal : Bool} (a : RawSuffix L d firstNormal) (i : Fin (2 * L)) :
    distinguished (completeWord p a i) ↔ distinguished (p.val i) := by
  by_cases h : i.val < d
  · simp [completeWord_before p a i h]
  · have hi : d ≤ i.val := by omega
    have hraw := completeWord_after_lt_four p a i hi
    have hp := p.property.1 i hi
    simp only [distinguished]
    rw [hp]
    simp only [Fin.val_zero]
    omega

/-- Ordinary completion preserves exactly the channel support. -/
theorem complete_channel_iff {L m t d : ℕ} (p : Prefixes L m t d)
    {firstNormal : Bool} (a : RawSuffix L d firstNormal) (i : Fin (2 * L)) :
    channel (completeWord p a i) ↔ channel (p.val i) := by
  by_cases h : i.val < d
  · simp [completeWord_before p a i h]
  · have hi : d ≤ i.val := by omega
    have hraw := completeWord_after_lt_four p a i hi
    have hp := p.property.1 i hi
    simp only [channel]
    rw [hp]
    simp only [Fin.val_zero]
    omega

/-- The completion belongs to the actual capped language. -/
theorem complete_retained {L m t d : ℕ} (p : Prefixes L m t d)
    {firstNormal : Bool} (a : RawSuffix L d firstNormal) :
    Retained L m t (completeWord p a) := by
  classical
  have h₁ : countPositions (completeWord p a)
      (fun i x => i.val < L ∧ distinguished x) =
      countPositions p.val (fun i x => i.val < L ∧ distinguished x) := by
    unfold countPositions
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [complete_distinguished_iff]
  have h₂ : countPositions (completeWord p a)
      (fun i x => L ≤ i.val ∧ distinguished x) =
      countPositions p.val (fun i x => L ≤ i.val ∧ distinguished x) := by
    unfold countPositions
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [complete_distinguished_iff]
  have h₃ : countPositions (completeWord p a) (fun _ x => channel x) =
      countPositions p.val (fun _ x => channel x) := by
    unfold countPositions
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact complete_channel_iff p a i
  rcases p.property.2 with ⟨hp₁, hp₂, hp₃⟩
  exact ⟨h₁ ▸ hp₁, h₂ ▸ hp₂, h₃ ▸ hp₃⟩

/-- Every intermediate raw array cell maps to a retained leaf. -/
def complete {L m t d : ℕ} {firstNormal : Bool}
    (v : Prefixes L m t d × RawSuffix L d firstNormal) : Leaves L m t :=
  ⟨completeWord v.1 v.2, complete_retained v.1 v.2⟩

/-- Prefixes at a fixed depth have disjoint ordinary completions, and the
raw-coordinate embedding within each completion is injective. -/
theorem complete_injective {L m t d : ℕ} (hd : d ≤ 2 * L)
    (firstNormal : Bool) :
    Function.Injective (@complete L m t d firstNormal) := by
  intro x y hxy
  have h : completeWord x.1 x.2 = completeWord y.1 y.2 := congrArg Subtype.val hxy
  have hp : x.1 = y.1 := by
    apply Subtype.ext
    funext i
    by_cases hi : i.val < d
    · have he := congrFun h i
      simpa only [completeWord_before _ _ _ hi] using he
    · have hi' : d ≤ i.val := by omega
      rw [x.1.property.1 i hi', y.1.property.1 i hi']
  have ha : x.2 = y.2 := by
    funext j
    have hj : d + j.val < 2 * L := by omega
    have he := congrFun h ⟨d + j.val, hj⟩
    simp only [completeWord, show ¬ d + j.val < d by omega, dite_false] at he
    have hev := congrArg Fin.val he
    simp only [ordinaryLabel] at hev
    have hidx (hproof : d + j.val - d < 2 * L - d) :
        (⟨d + j.val - d, hproof⟩ : Fin (2 * L - d)) = j := by
      apply Fin.ext
      change d + j.val - d = j.val
      omega
    apply Fin.ext
    let jj : Fin (2 * L - d) := ⟨d + j.val - d, by omega⟩
    change (x.2 jj).val = (y.2 jj).val at hev
    have hjj : jj = j := hidx jj.isLt
    rw [hjj] at hev
    exact hev
  exact Prod.ext hp ha

/-- S is the cardinality of genuine retained words, not an assumed
numerical or asymptotic bound. -/
noncomputable def retainedLeafCount (L m t : ℕ) : ℕ :=
  Fintype.card (Leaves L m t)

/-- The genuine raw array volume is its product of local dimensions. -/
noncomputable def rawVolume (L d : ℕ) (firstNormal : Bool) : ℕ :=
  ∏ i : Fin (2 * L - d), rawDim L firstNormal (d + i.val)

theorem rawSuffix_card (L d : ℕ) (firstNormal : Bool) :
    Fintype.card (RawSuffix L d firstNormal) = rawVolume L d firstNormal := by
  simp [RawSuffix, rawVolume, Fintype.card_pi]

/-- Every intermediate layer's sum of raw array volumes is bounded by the
actual retained leaf count, for both source orientations. -/
theorem layer_volume_le (L m t d : ℕ) (hd : d ≤ 2 * L)
    (firstNormal : Bool) :
    Fintype.card (Prefixes L m t d) * rawVolume L d firstNormal ≤
      retainedLeafCount L m t := by
  have h := Fintype.card_le_of_injective
    (@complete L m t d firstNormal) (complete_injective hd firstNormal)
  simpa only [Fintype.card_prod, rawSuffix_card, retainedLeafCount] using h

/-- Total stored/formed intermediate cells through all depths. -/
noncomputable def totalVolume (L m t : ℕ) (firstNormal : Bool) : ℕ :=
  ∑ d : Fin (2 * L + 1),
    Fintype.card (Prefixes L m t d.val) * rawVolume L d.val firstNormal

/-- All intermediate arrays and leaves together cost at most (2L+1)S
raw coefficient cells. Auxiliary-polynomial and cyclic widths multiply
this finite bound; they are not hidden unit-cost objects. -/
theorem total_volume_le (L m t : ℕ) (firstNormal : Bool) :
    totalVolume L m t firstNormal ≤ (2 * L + 1) * retainedLeafCount L m t := by
  unfold totalVolume
  calc
    _ ≤ ∑ _d : Fin (2 * L + 1), retainedLeafCount L m t := by
      apply Finset.sum_le_sum
      intro d _
      exact layer_volume_le L m t d.val (by omega) firstNormal
    _ = _ := by simp

/-- A complete ordinary word is retained for all nonnegative caps. -/
def ordinaryWord {n : ℕ} (a : Fin n → Fin 4) : Word n :=
  fun i => ⟨(a i).val, lt_trans (a i).isLt (by omega)⟩

theorem ordinary_retained (L m t : ℕ) (a : Fin (2 * L) → Fin 4) :
    Retained L m t (ordinaryWord a) := by
  classical
  have hd (i : Fin (2 * L)) : ¬ distinguished (ordinaryWord a i) := by
    have hi := (a i).isLt
    dsimp [distinguished, ordinaryWord]
    omega
  have hc (i : Fin (2 * L)) : ¬ channel (ordinaryWord a i) := by
    have hi := (a i).isLt
    dsimp [channel, ordinaryWord]
    omega
  simp [Retained, countPositions, hd, hc]

/-- The dense ordinary output family injects into the cache. -/
def ordinaryLeaf (L m t : ℕ) (a : Fin (2 * L) → Fin 4) : Leaves L m t :=
  ⟨ordinaryWord a, ordinary_retained L m t a⟩

theorem ordinaryLeaf_injective (L m t : ℕ) :
    Function.Injective (ordinaryLeaf L m t) := by
  intro a b hab
  funext i
  apply Fin.ext
  have h := congrArg (fun w : Leaves L m t => (w.val i).val) hab
  exact h

/-- In particular the full ordinary family of size 4^(2L) is paid. -/
theorem ordinary_power_le_leafCount (L m t : ℕ) :
    4 ^ (2 * L) ≤ retainedLeafCount L m t := by
  have h := Fintype.card_le_of_injective (ordinaryLeaf L m t)
    (ordinaryLeaf_injective L m t)
  simpa [retainedLeafCount] using h

/-- The actual root raw volume for the first source is 4^L*3^L. -/
theorem rawVolume_root_left (L : ℕ) : rawVolume L 0 true = 4 ^ L * 3 ^ L := by
  simp only [rawVolume, Nat.sub_zero, Nat.zero_add]
  rw [show 2 * L = L + L by omega, Fin.prod_univ_add]
  have h₁ (i : Fin L) : rawDim L true (Fin.castAdd L i).val = 4 := by
    simp [rawDim, i.isLt]
  have h₂ (i : Fin L) : rawDim L true (Fin.natAdd L i).val = 3 := by
    simp [rawDim]
  simp only [h₁, h₂, Fin.prod_const]

/-- Swapping source orientations preserves the root volume. -/
theorem rawVolume_root_right (L : ℕ) : rawVolume L 0 false = 3 ^ L * 4 ^ L := by
  simp only [rawVolume, Nat.sub_zero, Nat.zero_add]
  rw [show 2 * L = L + L by omega, Fin.prod_univ_add]
  have h₁ (i : Fin L) : rawDim L false (Fin.castAdd L i).val = 3 := by
    simp [rawDim, i.isLt]
  have h₂ (i : Fin L) : rawDim L false (Fin.natAdd L i).val = 4 := by
    simp [rawDim]
  simp only [h₁, h₂, Fin.prod_const]

/-- The dense raw source array 12^L also fits the genuine retained cache. -/
theorem source_power_le_leafCount (L m t : ℕ) :
    12 ^ L ≤ retainedLeafCount L m t := by
  calc
    12 ^ L ≤ 16 ^ L := Nat.pow_le_pow_left (by omega) _
    _ = 4 ^ (2 * L) := by rw [pow_mul]; norm_num
    _ ≤ _ := ordinary_power_le_leafCount L m t

/-- Auxiliary and cyclic coefficient slots are explicitly charged. -/
theorem total_coefficient_cells_le (L m t auxiliaryWidth cyclicWidth : ℕ)
    (firstNormal : Bool) :
    auxiliaryWidth * cyclicWidth * totalVolume L m t firstNormal ≤
      auxiliaryWidth * cyclicWidth * ((2 * L + 1) * retainedLeafCount L m t) :=
  Nat.mul_le_mul_left _ (total_volume_le L m t firstNormal)

/-- Genuine coordinates of every intermediate array, with its depth and
prefix retained. This is a disjoint union, not just a numerical sum. -/
abbrev IntermediateEntries (L m t : ℕ) (firstNormal : Bool) :=
  (d : Fin (2 * L + 1)) × (Prefixes L m t d.val × RawSuffix L d.val firstNormal)

theorem intermediateEntries_card (L m t : ℕ) (firstNormal : Bool) :
    Fintype.card (IntermediateEntries L m t firstNormal) =
      totalVolume L m t firstNormal := by
  simp [IntermediateEntries, totalVolume, rawVolume, Fintype.card_sigma,
    Fintype.card_prod]

/-- Every auxiliary-polynomial/cyclic slot is an actual finite coordinate. -/
abbrev CoefficientEntries (L m t auxiliaryWidth cyclicWidth : ℕ)
    (firstNormal : Bool) :=
  Fin auxiliaryWidth × Fin cyclicWidth × IntermediateEntries L m t firstNormal

theorem coefficientEntries_card_le (L m t auxiliaryWidth cyclicWidth : ℕ)
    (firstNormal : Bool) :
    Fintype.card (CoefficientEntries L m t auxiliaryWidth cyclicWidth firstNormal) ≤
      auxiliaryWidth * cyclicWidth * ((2 * L + 1) * retainedLeafCount L m t) := by
  simp only [CoefficientEntries, Fintype.card_prod, Fintype.card_fin]
  rw [intermediateEntries_card]
  simpa only [Nat.mul_assoc] using
    total_coefficient_cells_le L m t auxiliaryWidth cyclicWidth firstNormal

/-- Replacing distinguished/channel positions only by ordinary positions
cannot violate a retained cap. -/
theorem retained_of_support_subset {L m t : ℕ} (w v : Word (2 * L))
    (hw : Retained L m t w)
    (hdist : ∀ i, distinguished (v i) → distinguished (w i))
    (hchan : ∀ i, channel (v i) → channel (w i)) : Retained L m t v := by
  classical
  rcases hw with ⟨hw₁, hw₂, hw₃⟩
  have h₁ : countPositions v (fun i a => i.val < L ∧ distinguished a) ≤
      countPositions w (fun i a => i.val < L ∧ distinguished a) := by
    apply Finset.card_le_card
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact ⟨hi.1, hdist i hi.2⟩
  have h₂ : countPositions v (fun i a => L ≤ i.val ∧ distinguished a) ≤
      countPositions w (fun i a => L ≤ i.val ∧ distinguished a) := by
    apply Finset.card_le_card
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact ⟨hi.1, hdist i hi.2⟩
  have h₃ : countPositions v (fun _ a => channel a) ≤
      countPositions w (fun _ a => channel a) := by
    apply Finset.card_le_card
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact hchan i hi
  exact ⟨h₁.trans hw₁, h₂.trans hw₂, h₃.trans hw₃⟩

/-- Canonically erase the unprocessed suffix of a word. -/
def trimWord {n : ℕ} (d : ℕ) (w : Word n) : Word n :=
  fun i => if i.val < d then w i else 0

theorem trim_retained {L m t : ℕ} (d : ℕ) (w : Leaves L m t) :
    Retained L m t (trimWord d w.val) := by
  apply retained_of_support_subset w.val (trimWord d w.val) w.property
  · intro i hi
    by_cases h : i.val < d
    · simpa [trimWord, h] using hi
    · simp [trimWord, h, distinguished] at hi
  · intro i hi
    by_cases h : i.val < d
    · simpa [trimWord, h] using hi
    · simp [trimWord, h, channel] at hi

/-- Every retained leaf has retained predecessors at every depth. -/
def leafPrefix {L m t : ℕ} (d : ℕ) (w : Leaves L m t) : Prefixes L m t d :=
  ⟨trimWord d w.val, ⟨by
    intro i hi
    simp [trimWord, show ¬ i.val < d by omega], trim_retained d w⟩⟩

/-- Erasing an ordinary completion recovers its genuine prefix. -/
theorem leafPrefix_complete {L m t d : ℕ} {firstNormal : Bool}
    (p : Prefixes L m t d) (a : RawSuffix L d firstNormal) :
    leafPrefix d (complete (p, a)) = p := by
  apply Subtype.ext
  funext i
  by_cases hi : i.val < d
  · simp [leafPrefix, trimWord, complete, completeWord, hi]
  · have hp := p.property.1 i (by omega)
    simp [leafPrefix, trimWord, hi, hp]

/-- A legal zero raw suffix exists in either orientation. -/
def zeroSuffix (L d : ℕ) (firstNormal : Bool) : RawSuffix L d firstNormal :=
  fun i => ⟨0, rawDim_pos L firstNormal (d + i.val)⟩

/-- The capped-prefix family is exactly the family of retained-leaf
prefixes, rather than a collection of inaccessible extra states. -/
theorem leafPrefix_surjective (L m t d : ℕ) :
    Function.Surjective (@leafPrefix L m t d) := by
  intro p
  exact ⟨complete (p, zeroSuffix L d true), leafPrefix_complete p _⟩

theorem rawVolume_pos (L d : ℕ) (firstNormal : Bool) :
    0 < rawVolume L d firstNormal := by
  unfold rawVolume
  exact Finset.prod_pos (fun i _ => rawDim_pos _ _ _)

/-- Prefix/trie metadata is also paid: no array has zero raw volume. -/
theorem prefix_count_le_leafCount (L m t d : ℕ) (hd : d ≤ 2 * L)
    (firstNormal : Bool) :
    Fintype.card (Prefixes L m t d) ≤ retainedLeafCount L m t := by
  have hv : 1 ≤ rawVolume L d firstNormal := rawVolume_pos L d firstNormal
  calc
    _ = Fintype.card (Prefixes L m t d) * 1 := by simp
    _ ≤ Fintype.card (Prefixes L m t d) * rawVolume L d firstNormal :=
      Nat.mul_le_mul_left _ hv
    _ ≤ _ := layer_volume_le L m t d hd firstNormal

#print axioms complete_retained
#print axioms complete_injective
#print axioms layer_volume_le
#print axioms total_volume_le
#print axioms ordinary_power_le_leafCount
#print axioms source_power_le_leafCount
#print axioms total_coefficient_cells_le
#print axioms coefficientEntries_card_le
#print axioms trim_retained
#print axioms leafPrefix_surjective
#print axioms prefix_count_le_leafCount

end ThinMatrix.CacheBounds
