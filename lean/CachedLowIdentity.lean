import SourceCoordinates

/-!
# Physical LOW channel caches

The normal side uses H(z) and p2, the opposite side uses 2s and w.
The second physical half swaps these roles. Both inputs use the same channel
set, and coefficient extraction applies its shift only once.
-/
namespace ThinMatrix.CachedLowIdentity

open scoped BigOperators
open CompleteThinProduct TensorContraction WalshEmbedding
open CacheBounds SourceCoordinates SharedEncoder HighBoxDP

attribute [local instance] Classical.propDecidable

variable {R : Type*} [CommRing R]
noncomputable section

noncomputable def cacheWord {L k : ℕ} (e : Fin k ↪o Fin (2*L))
    (outside : Fin (2*L) → Fin 4) (C : Finset (Fin k)) : Word (2*L) := fun i =>
  if h : ∃ j, e j = i then
    if Classical.choose h ∈ C then 5 else 4
  else (outside i).castSucc.castSucc

@[simp] theorem cacheWord_at {L k : ℕ} (e : Fin k ↪o Fin (2*L))
    (outside : Fin (2*L) → Fin 4) (C : Finset (Fin k)) (j : Fin k) :
    cacheWord e outside C (e j) = if j ∈ C then 5 else 4 := by
  have h : ∃ a, e a = e j := ⟨j, rfl⟩
  simp only [cacheWord, dif_pos h]
  have he : Classical.choose h = j := e.injective (Classical.choose_spec h)
  rw [he]

@[simp] theorem cacheWord_outside {L k : ℕ} (e : Fin k ↪o Fin (2*L))
    (outside : Fin (2*L) → Fin 4) (C : Finset (Fin k)) (i : Fin (2*L))
    (hi : i ∉ embeddedSupport e) :
    cacheWord e outside C i = (outside i).castSucc.castSucc := by
  have hn : ¬ ∃ j, e j = i := by simpa [embeddedSupport] using hi
  simp [cacheWord, hn]

theorem cacheWord_distinguished_iff {L k : ℕ} (e : Fin k ↪o Fin (2*L))
    (outside : Fin (2*L) → Fin 4) (C : Finset (Fin k)) (i : Fin (2*L)) :
    distinguished (cacheWord e outside C i) ↔ i ∈ embeddedSupport e := by
  classical
  by_cases hi : i ∈ embeddedSupport e
  · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hi
    rw [cacheWord_at]
    simp only [distinguished]
    split_ifs <;> simp [embeddedSupport]
  · rw [cacheWord_outside e outside C i hi]
    have hlt := (outside i).isLt
    simp only [distinguished, Fin.val_castSucc]
    exact ⟨fun h => False.elim (by omega), fun h => False.elim (hi h)⟩

theorem cacheWord_channel_iff {L k : ℕ} (e : Fin k ↪o Fin (2*L))
    (outside : Fin (2*L) → Fin 4) (C : Finset (Fin k)) (i : Fin (2*L)) :
    channel (cacheWord e outside C i) ↔ i ∈ C.image e := by
  classical
  by_cases hi : i ∈ embeddedSupport e
  · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hi
    rw [cacheWord_at]
    simp only [channel]
    by_cases hj : j ∈ C
    · simp [hj]
    · simp only [hj, if_false]
      constructor
      · norm_num
      · intro h
        obtain ⟨a, ha, hea⟩ := Finset.mem_image.mp h
        exact False.elim (hj (e.injective hea ▸ ha))
  · rw [cacheWord_outside e outside C i hi]
    have hlt := (outside i).isLt
    simp only [channel, Fin.val_castSucc]
    constructor
    · intro h
      omega
    · intro h
      obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp h
      apply False.elim
      apply hi
      exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, hji⟩

theorem cacheWord_channel_support {L k : ℕ} (e : Fin k ↪o Fin (2*L))
    (outside : Fin (2*L) → Fin 4) (C : Finset (Fin k)) :
    Finset.univ.filter (fun i => channel (cacheWord e outside C i)) = C.image e := by
  classical
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, cacheWord_channel_iff]

theorem cacheWord_distinguished_count {L k : ℕ} (e : Fin k ↪o Fin (2*L))
    (outside : Fin (2*L) → Fin 4) (C : Finset (Fin k)) (region : Fin (2*L) → Prop) :
    countPositions (cacheWord e outside C) (fun i a => region i ∧ distinguished a) =
      ((embeddedSupport e).filter region).card := by
  classical
  unfold countPositions
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    cacheWord_distinguished_iff, and_comm]

theorem cacheWord_channel_count {L k : ℕ} (e : Fin k ↪o Fin (2*L))
    (outside : Fin (2*L) → Fin 4) (C : Finset (Fin k)) :
    countPositions (cacheWord e outside C) (fun _ a => channel a) = C.card := by
  classical
  unfold countPositions
  rw [cacheWord_channel_support, Finset.card_image_of_injective _ e.injective]

theorem cacheWord_retained {L k m t : ℕ} (e : Fin k ↪o Fin (2*L))
    (outside : Fin (2*L) → Fin 4) (C : Finset (Fin k))
    (hleft : ((embeddedSupport e).filter (fun i => i.val < L)).card ≤ m)
    (hright : ((embeddedSupport e).filter (fun i => L ≤ i.val)).card ≤ m)
    (hC : C.card ≤ t) : Retained L m t (cacheWord e outside C) := by
  refine ⟨?_, ?_, ?_⟩
  · calc
      _ = ((embeddedSupport e).filter (fun i => i.val < L)).card := by
        unfold countPositions
        congr 1
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and,
          cacheWord_distinguished_iff, and_comm]
      _ ≤ m := hleft
  · calc
      _ = ((embeddedSupport e).filter (fun i => L ≤ i.val)).card := by
        unfold countPositions
        congr 1
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and,
          cacheWord_distinguished_iff, and_comm]
      _ ≤ m := hright
  · rw [cacheWord_channel_count]
    exact hC


/-- Four ordinary forms, H(z), and its unshifted p2 channel. -/
def normalCacheForm (n : NormalLetter) (label : Fin 6) : Polynomial R :=
  if hl : label.val < 4 then
    Polynomial.C (normalForm n ⟨label.val, by omega⟩)
  else if label = 4 then
    Polynomial.C (-letterIndicator n .x1-letterIndicator n .x2) +
      Polynomial.X * Polynomial.C (letterIndicator n .p1)
  else Polynomial.C (letterIndicator n .p2)

/-- The opposite cache has the unshifted 2s baseline and w channel. -/
def oppositeCacheForm (o : OppositeLetter) (label : Fin 6) : Polynomial R :=
  if hl : label.val < 4 then
    Polynomial.C (oppositeForm o ⟨label.val, by omega⟩)
  else if label = 4 then Polynomial.C (2*letterIndicator o .s)
  else Polynomial.C (letterIndicator o .w)

def sourceCacheF {L : ℕ} : Fin (2*L) → Fin 6 → SourceWord L → Polynomial R :=
  halfLift (fun i l a => normalCacheForm (a.1 i) l)
    (fun i l a => oppositeCacheForm (a.2 i) l)

def sourceCacheG {L : ℕ} : Fin (2*L) → Fin 6 → SourceWord L → Polynomial R :=
  halfLift (fun i l a => oppositeCacheForm (a.2 i) l)
    (fun i l a => normalCacheForm (a.1 i) l)

@[simp] theorem normalCacheForm_ordinary (n : NormalLetter) (l : Fin 4) :
    normalCacheForm (R := R) n l.castSucc.castSucc = Polynomial.C (normalForm n l.castSucc) := by
  simp only [normalCacheForm, Fin.val_castSucc, l.isLt, dite_true]
  congr 2

@[simp] theorem oppositeCacheForm_ordinary (o : OppositeLetter) (l : Fin 4) :
    oppositeCacheForm (R := R) o l.castSucc.castSucc = Polynomial.C (oppositeForm o l.castSucc) := by
  simp only [oppositeCacheForm, Fin.val_castSucc, l.isLt, dite_true]
  congr 2

@[simp] theorem sourceCacheF_ordinary {L : ℕ} (i : Fin (2*L)) (l : Fin 4)
    (a : SourceWord L) : sourceCacheF (R := R) i l.castSucc.castSucc a =
      Polynomial.C (sourceF i l.castSucc a) := by
  unfold sourceCacheF sourceF halfLift
  split <;> simp

@[simp] theorem sourceCacheG_ordinary {L : ℕ} (i : Fin (2*L)) (l : Fin 4)
    (a : SourceWord L) : sourceCacheG (R := R) i l.castSucc.castSucc a =
      Polynomial.C (sourceG i l.castSucc a) := by
  unfold sourceCacheG sourceG halfLift
  split <;> simp

/-- The local normal/opposite pencil has one common channel shift. -/
theorem local_cache_pencil (n : NormalLetter) (o : OppositeLetter) :
    Polynomial.C (normalForm n 4 * oppositeForm o 4) +
      Polynomial.X * Polynomial.C (∑ l : Fin 5, normalForm (R := R) n l * oppositeForm o l) =
      normalCacheForm n 4 * oppositeCacheForm o 4 +
        Polynomial.X * normalCacheForm n 5 * oppositeCacheForm o 5 := by
  simp only [normalForm, oppositeForm, aligned_label_sum]
  simpa [normalCacheForm, oppositeCacheForm, alignedLeft, alignedRight] using
    aligned_polynomial_pencil (letterIndicator (R := R) n .x1) (letterIndicator n .x2)
      (letterIndicator n .p1) (letterIndicator n .p2) (letterIndicator o .s) (letterIndicator o .w)

/-- The swapped half has the same physical channel, with the H form on G. -/
theorem swapped_cache_pencil (n : NormalLetter) (o : OppositeLetter) :
    Polynomial.C (oppositeForm o 4 * normalForm n 4) +
      Polynomial.X * Polynomial.C (∑ l : Fin 5, oppositeForm (R := R) o l * normalForm n l) =
      oppositeCacheForm o 4 * normalCacheForm n 4 +
        Polynomial.X * oppositeCacheForm o 5 * normalCacheForm n 5 := by
  simpa only [mul_comm, mul_left_comm, mul_assoc] using local_cache_pencil (R := R) n o

/-- Pointwise physical identity for the actual source operators. -/
theorem physical_cache_pencil {L : ℕ} (i : Fin (2*L)) (a b : SourceWord L) :
    Polynomial.C (privateKernel sourceF sourceG i a b) +
      Polynomial.X * Polynomial.C (fullKernel sourceF sourceG i a b) =
      sourceCacheF (R := R) i 4 a * sourceCacheG i 4 b +
        Polynomial.X * sourceCacheF i 5 a * sourceCacheG i 5 b := by
  unfold privateKernel fullKernel sourceF sourceG sourceCacheF sourceCacheG halfLift
  split
  · exact local_cache_pencil _ _
  · exact swapped_cache_pencil _ _

/-- Local forms used by the actual heterogeneous shared encoder. -/
def sourceCacheForms (L : ℕ) (normalFirst : Bool) : LocalForms (Polynomial R) :=
  fun d label raw =>
    if (d < L) = (normalFirst = true) then
      if ha : raw < 4 then normalCacheForm (normalEquiv ⟨raw,ha⟩) label else 0
    else if ha : raw < 3 then oppositeCacheForm (oppositeEquiv ⟨raw,ha⟩) label else 0

lemma sourceCacheForms_leftTrue {L : ℕ} (a : Coordinates (rootDims L true))
    (j : Fin L) (l : Fin 6) :
    sourceCacheForms (R := R) L true (physicalLeft j).val l (a (physicalLeft j)).val =
      sourceCacheF (physicalLeft j) l (toSourceTrue a) := by
  have ha : (a (physicalLeft j)).val < 4 := by simpa using (a (physicalLeft j)).isLt
  simp only [physicalLeft] at ha
  simp [sourceCacheForms, physicalLeft, j.isLt, ha, sourceCacheF, halfLift, toSourceTrue]
  congr 2

lemma sourceCacheForms_rightTrue {L : ℕ} (a : Coordinates (rootDims L true))
    (j : Fin L) (l : Fin 6) :
    sourceCacheForms (R := R) L true (physicalRight j).val l (a (physicalRight j)).val =
      sourceCacheF (physicalRight j) l (toSourceTrue a) := by
  have ha : (a (physicalRight j)).val < 3 := by simpa using (a (physicalRight j)).isLt
  simp only [physicalRight] at ha
  simp [sourceCacheForms, physicalRight, Nat.not_lt.mpr (Nat.le_add_right L j.val),
    ha, sourceCacheF, halfLift, toSourceTrue]
  congr 2

lemma sourceCacheForms_leftFalse {L : ℕ} (a : Coordinates (rootDims L false))
    (j : Fin L) (l : Fin 6) :
    sourceCacheForms (R := R) L false (physicalLeft j).val l (a (physicalLeft j)).val =
      sourceCacheG (physicalLeft j) l (toSourceFalse a) := by
  have ha : (a (physicalLeft j)).val < 3 := by simpa using (a (physicalLeft j)).isLt
  simp only [physicalLeft] at ha
  simp [sourceCacheForms, physicalLeft, j.isLt, ha, sourceCacheG, halfLift, toSourceFalse]
  congr 2

lemma sourceCacheForms_rightFalse {L : ℕ} (a : Coordinates (rootDims L false))
    (j : Fin L) (l : Fin 6) :
    sourceCacheForms (R := R) L false (physicalRight j).val l (a (physicalRight j)).val =
      sourceCacheG (physicalRight j) l (toSourceFalse a) := by
  have ha : (a (physicalRight j)).val < 4 := by simpa using (a (physicalRight j)).isLt
  simp only [physicalRight] at ha
  simp [sourceCacheForms, physicalRight, Nat.not_lt.mpr (Nat.le_add_right L j.val),
    ha, sourceCacheG, halfLift, toSourceFalse]
  congr 2

lemma sourceCacheForms_at_true {L : ℕ} (a : Coordinates (rootDims L true))
    (i : Fin (2*L)) (l : Fin 6) :
    sourceCacheForms (R := R) L true i.val l (a i).val = sourceCacheF i l (toSourceTrue a) := by
  by_cases hi : i.val < L
  · have he : physicalLeft (⟨i.val,hi⟩ : Fin L) = i := by apply Fin.ext; rfl
    rw [← he]
    exact sourceCacheForms_leftTrue a _ _
  · have he : physicalRight (⟨i.val-L,by omega⟩ : Fin L) = i := by
      apply Fin.ext
      simp [physicalRight]
      omega
    rw [← he]
    exact sourceCacheForms_rightTrue a _ _

lemma sourceCacheForms_at_false {L : ℕ} (a : Coordinates (rootDims L false))
    (i : Fin (2*L)) (l : Fin 6) :
    sourceCacheForms (R := R) L false i.val l (a i).val = sourceCacheG i l (toSourceFalse a) := by
  by_cases hi : i.val < L
  · have he : physicalLeft (⟨i.val,hi⟩ : Fin L) = i := by apply Fin.ext; rfl
    rw [← he]
    exact sourceCacheForms_leftFalse a _ _
  · have he : physicalRight (⟨i.val-L,by omega⟩ : Fin L) = i := by
      apply Fin.ext
      simp [physicalRight]
      omega
    rw [← he]
    exact sourceCacheForms_rightFalse a _ _

/-- Actual complete polynomial cache transforms of the physical raw sources. -/
def leftCachePolynomial {L : ℕ} (X : SourceWord L → R) (word : Word (2*L)) : Polynomial R :=
  ∑ a, Polynomial.C (X a) * ∏ i, sourceCacheF i (word i) a

def rightCachePolynomial {L : ℕ} (Y : SourceWord L → R) (word : Word (2*L)) : Polynomial R :=
  ∑ a, Polynomial.C (Y a) * ∏ i, sourceCacheG i (word i) a

/-- The lifted roots store constant-in-z raw source entries. -/
def sourceCacheInput (L : ℕ) (normalFirst : Bool) (X : SourceWord L → R) :
    Dense (R := Polynomial R) (2*L) (rootDims L normalFirst) :=
  match normalFirst with
  | true => leftInput (fun a => Polynomial.C (X a))
  | false => rightInput (fun a => Polynomial.C (X a))

theorem left_cache_tensorValue {L : ℕ} (X : SourceWord L → R) (word : Word (2*L)) :
    tensorValue L true (sourceCacheForms L true) (sourceCacheInput L true X) word =
      leftCachePolynomial X word := by
  unfold tensorValue EncoderCorrectness.tensorSum sourceCacheInput leftInput leftCachePolynomial
  simp_rw [read_materialize, sourceCacheForms_at_true]
  exact (coordinateEquivTrue L).sum_comp
    (fun a => Polynomial.C (X a) * ∏ i, sourceCacheF i (word i) a)

theorem right_cache_tensorValue {L : ℕ} (Y : SourceWord L → R) (word : Word (2*L)) :
    tensorValue L false (sourceCacheForms L false) (sourceCacheInput L false Y) word =
      rightCachePolynomial Y word := by
  unfold tensorValue EncoderCorrectness.tensorSum sourceCacheInput rightInput rightCachePolynomial
  simp_rw [read_materialize, sourceCacheForms_at_false]
  exact (coordinateEquivFalse L).sum_comp
    (fun a => Polynomial.C (Y a) * ∏ i, sourceCacheG i (word i) a)

/-- Products of baseline/channel forms split on the same local channel set. -/
theorem channel_product {M : Type*} [CommMonoid M] {k : ℕ}
    (C : Finset (Fin k)) (F : Fin k → Fin 6 → M) :
    (∏ j ∈ C, F j 5) * (∏ j ∈ Finset.univ \ C, F j 4) =
      ∏ j, F j (if j ∈ C then 5 else 4) := by
  classical
  symm
  simp_rw [apply_ite]
  rw [Finset.prod_ite]
  simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
  have he : (Finset.univ.filter (fun j : Fin k => j ∉ C)) = Finset.univ \ C := by
    ext j
    simp
  rw [he]

/-- Combining the absorbed ordinary outside factors with the selected
baseline/channel forms gives one complete physical cache word. -/
theorem outside_mul_channels_eq_global {L k : ℕ} {M : Type*} [CommMonoid M]
    (e : Fin k ↪o Fin (2*L)) (outside : Fin (2*L) → Fin 4) (C : Finset (Fin k))
    (F : Fin (2*L) → Fin 6 → M) :
    (∏ i ∈ (embeddedSupport e)ᶜ, F i (outside i).castSucc.castSucc) *
      ((∏ j ∈ C, F (e j) 5) * (∏ j ∈ Finset.univ \ C, F (e j) 4)) =
      ∏ i, F i (cacheWord e outside C i) := by
  classical
  rw [channel_product C (fun j => F (e j))]
  have hs : (∏ i ∈ embeddedSupport e, F i (cacheWord e outside C i)) =
      ∏ j, F (e j) (if j ∈ C then 5 else 4) := by
    rw [embeddedSupport, Finset.prod_image (fun a _ b _ h => e.injective h)]
    simp only [cacheWord_at]
  have ho : (∏ i ∈ (embeddedSupport e)ᶜ, F i (cacheWord e outside C i)) =
      ∏ i ∈ (embeddedSupport e)ᶜ, F i (outside i).castSucc.castSucc := by
    apply Finset.prod_congr rfl
    intro i hi
    rw [cacheWord_outside e outside C i (Finset.mem_compl.mp hi)]
  rw [← ho, ← hs]
  exact Finset.prod_compl_mul_prod _ _

theorem left_channel_cache_eq_polynomial {L k : ℕ}
    (e : Fin k ↪o Fin (2*L)) (outside : Fin (2*L) → Fin 4)
    (C : Finset (Fin k)) (X : SourceWord L → R) :
    leftCache Finset.univ C (fun a => Polynomial.C (absorbedInput e outside X sourceF a))
      (fun j a => sourceCacheF (e j) 4 a) (fun j a => sourceCacheF (e j) 5 a) =
      leftCachePolynomial X (cacheWord e outside C) := by
  unfold leftCache leftCachePolynomial absorbedInput
  apply Finset.sum_congr rfl
  intro a _
  dsimp only
  rw [map_mul, map_prod, mul_assoc]
  simp_rw [← sourceCacheF_ordinary]
  rw [outside_mul_channels_eq_global e outside C (fun i l => sourceCacheF i l a)]

theorem right_channel_cache_eq_polynomial {L k : ℕ}
    (e : Fin k ↪o Fin (2*L)) (outside : Fin (2*L) → Fin 4)
    (C : Finset (Fin k)) (Y : SourceWord L → R) :
    rightCache Finset.univ C (fun a => Polynomial.C (absorbedInput e outside Y sourceG a))
      (fun j a => sourceCacheG (e j) 4 a) (fun j a => sourceCacheG (e j) 5 a) =
      rightCachePolynomial Y (cacheWord e outside C) := by
  unfold rightCache rightCachePolynomial absorbedInput
  apply Finset.sum_congr rfl
  intro a _
  dsimp only
  rw [map_mul, map_prod, mul_assoc]
  simp_rw [← sourceCacheG_ordinary]
  rw [outside_mul_channels_eq_global e outside C (fun i l => sourceCacheG i l a)]

/-- The polynomial used by the actual LOW query is the physical shared
channel contraction, including ordinary outside absorption. -/
theorem physical_pencil_channel_contraction {L k : ℕ}
    (e : Fin k ↪o Fin (2*L)) (outside : Fin (2*L) → Fin 4)
    (X Y : SourceWord L → R) :
    pencilQuery k (absorbedInput e outside X sourceF) (absorbedInput e outside Y sourceG)
      (privateKernel (fun j => sourceF (e j)) (fun j => sourceG (e j)))
      (fullKernel (fun j => sourceF (e j)) (fun j => sourceG (e j))) =
      ∑ C ∈ (Finset.univ : Finset (Fin k)).powerset,
        Polynomial.X^C.card * leftCachePolynomial X (cacheWord e outside C) *
          rightCachePolynomial Y (cacheWord e outside C) := by
  unfold pencilQuery
  change bilinear (fun a => Polynomial.C (absorbedInput e outside X sourceF a))
    (fun b => Polynomial.C (absorbedInput e outside Y sourceG b))
    (fun a b => ∏ j, (Polynomial.C (privateKernel sourceF sourceG (e j) a b) +
      Polynomial.X * Polynomial.C (fullKernel sourceF sourceG (e j) a b))) = _
  simp_rw [physical_cache_pencil]
  have h := polynomial_channel_contraction Finset.univ
    (fun a => Polynomial.C (absorbedInput e outside X sourceF a))
    (fun b => Polynomial.C (absorbedInput e outside Y sourceG b))
    (fun j a => sourceCacheF (e j) 4 a) (fun j a => sourceCacheF (e j) 5 a)
    (fun j b => sourceCacheG (e j) 4 b) (fun j b => sourceCacheG (e j) 5 b)
  unfold TensorContraction.tensorKernel at h
  rw [h]
  simp_rw [left_channel_cache_eq_polynomial, right_channel_cache_eq_polynomial]

/-- Exact physical LOW formula. The shared physical C contributes one shift,
and the cached coefficient is j-|C|, with the normal H form on either half. -/
theorem lowQuery_eq_cached_channels {L k t : ℕ}
    (e : Fin k ↪o Fin (2*L)) (outside : Fin (2*L) → Fin 4)
    (X Y : SourceWord L → R) :
    lowQuery (t := t) e outside X Y sourceF sourceG =
      ∑ C ∈ (Finset.univ : Finset (Fin k)).powerset.filter (fun C => C.card < t),
        ∑ j ∈ Finset.range t,
          if C.card ≤ j then residualWeight k t j *
            (leftCachePolynomial X (cacheWord e outside C) *
              rightCachePolynomial Y (cacheWord e outside C)).coeff (j-C.card)
          else 0 := by
  unfold lowQuery pencilQuery
  change weightedLow k t (bilinear
    (fun a => Polynomial.C (absorbedInput e outside X sourceF a))
    (fun b => Polynomial.C (absorbedInput e outside Y sourceG b))
    (fun a b => ∏ j, (Polynomial.C (privateKernel sourceF sourceG (e j) a b) +
      Polynomial.X * Polynomial.C (fullKernel sourceF sourceG (e j) a b)))) = _
  simp_rw [physical_cache_pencil]
  have h := weighted_low_uses_small_channel_sets Finset.univ
    (fun a => Polynomial.C (absorbedInput e outside X sourceF a))
    (fun b => Polynomial.C (absorbedInput e outside Y sourceG b))
    (fun j a => sourceCacheF (e j) 4 a) (fun j a => sourceCacheF (e j) 5 a)
    (fun j b => sourceCacheG (e j) 4 b) (fun j b => sourceCacheG (e j) 5 b) k t
  unfold TensorContraction.tensorKernel at h
  rw [h]
  simp_rw [left_channel_cache_eq_polynomial, right_channel_cache_eq_polynomial]

/-- Including channel sets of size exactly t adds zero terms, and aligns
with the cache's weak joint cap. -/
theorem lowQuery_eq_cached_channels_le {L k t : ℕ}
    (e : Fin k ↪o Fin (2*L)) (outside : Fin (2*L) → Fin 4)
    (X Y : SourceWord L → R) :
    lowQuery (t := t) e outside X Y sourceF sourceG =
      ∑ C ∈ (Finset.univ : Finset (Fin k)).powerset.filter (fun C => C.card ≤ t),
        ∑ j ∈ Finset.range t,
          if C.card ≤ j then residualWeight k t j *
            (leftCachePolynomial X (cacheWord e outside C) *
              rightCachePolynomial Y (cacheWord e outside C)).coeff (j-C.card)
          else 0 := by
  rw [lowQuery_eq_cached_channels]
  apply Finset.sum_subset
  · intro C hC
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hC).1,
      (Finset.mem_filter.mp hC).2.le⟩
  · intro C hC hnot
    have hlarge : ¬ C.card < t := by
      intro hsmall
      exact hnot (Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hC).1, hsmall⟩)
    apply Finset.sum_eq_zero
    intro j hj
    have hjt := Finset.mem_range.mp hj
    have hnotj : ¬ C.card ≤ j := by omega
    simp only [hnotj, if_false]

/-- Binomial residual weights are ordinary integer scalars in every ring. -/
theorem residualWeight_intCast (k t j : ℕ) :
    residualWeight (R := R) k t j = ((residualWeight (R := ℤ) k t j : ℤ) : R) := by
  simp [residualWeight]

/-- Exact selected cyclic coefficient of the physical LOW query. Formal z
and the cyclic variable remain distinct, and the channel shift occurs once. -/
theorem lowQuery_cyclic_coefficient {q L k t : ℕ} [NeZero q]
    (e : Fin k ↪o Fin (2*L)) (outside : Fin (2*L) → Fin 4)
    (X Y : SourceWord L → CyclicRing.Cyclic q) (target : Fin q) :
    (lowQuery (t := t) e outside X Y sourceF sourceG) target =
      ∑ C ∈ (Finset.univ : Finset (Fin k)).powerset.filter (fun C => C.card ≤ t),
        ∑ j ∈ Finset.range t,
          if C.card ≤ j then (residualWeight (R := ℤ) k t j) *
            ((leftCachePolynomial X (cacheWord e outside C) *
              rightCachePolynomial Y (cacheWord e outside C)).coeff (j-C.card)) target
          else 0 := by
  rw [lowQuery_eq_cached_channels_le]
  simp only [CyclicRing.sum_coeff]
  apply Finset.sum_congr rfl
  intro C _
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : C.card ≤ j
  · simp only [hj, if_true]
    rw [residualWeight_intCast (R := CyclicRing.Cyclic q)]
    exact CyclicRing.intCast_mul_coeff _ _ _
  · simp only [hj, if_false, CyclicRing.zero_coeff]

#print axioms cacheWord_retained
#print axioms cacheWord_channel_count
#print axioms physical_cache_pencil
#print axioms left_cache_tensorValue
#print axioms right_cache_tensorValue
#print axioms physical_pencil_channel_contraction
#print axioms lowQuery_eq_cached_channels
#print axioms lowQuery_eq_cached_channels_le
#print axioms lowQuery_cyclic_coefficient

end
end ThinMatrix.CachedLowIdentity
