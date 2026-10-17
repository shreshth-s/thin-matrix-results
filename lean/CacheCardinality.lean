import CacheBounds

/-!
# Exact finite cardinality of the capped six-letter cache language

The counting objects in this file are genuine finite words from
`CacheBounds`; numerical estimates are separated from the cardinality
identification. All statements are finite, with no asymptotic assumption.
-/

open scoped BigOperators

namespace ThinMatrix.CacheCardinality

open ThinMatrix.CacheBounds

/-- Number of subsets of at most `t` positions in an `n`-element set. -/
def channelBall (n t : ℕ) : ℕ := ∑ h ∈ Finset.range (t + 1), n.choose h

@[simp] theorem channelBall_zero (n : ℕ) : channelBall n 0 = 1 := by
  simp [channelBall]

/-- Number of four-ordinary-letter half words with at most `m` special positions. -/
def ordinaryHalfCount (L m : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (m + 1), L.choose j * 4 ^ (L - j)

/-- Formula A8, first expressed with zero-extended binomial tails. -/
def countFormula (L m t : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (m + 1), ∑ k ∈ Finset.range (m + 1),
    L.choose j * L.choose k * 4 ^ (2 * L - j - k) * channelBall (j + k) t

theorem channelBall_mono {a b : ℕ} (h : a ≤ b) (t : ℕ) :
    channelBall a t ≤ channelBall b t := by
  unfold channelBall
  exact Finset.sum_le_sum (fun _ _ => Nat.choose_mono _ h)

theorem channelBall_eq_min (n t : ℕ) :
    channelBall n t = ∑ h ∈ Finset.range (min t n + 1), n.choose h := by
  unfold channelBall
  symm
  apply Finset.sum_subset
  · exact Finset.range_mono (by omega)
  · intro h ht hn
    have h₁ := Finset.mem_range.mp ht
    have h₂ : ¬ h < min t n + 1 := fun hh => hn (Finset.mem_range.mpr hh)
    apply Nat.choose_eq_zero_of_lt
    omega

theorem formula_lower (L m t : ℕ) (hm : m ≤ L) :
    (L.choose m * 4 ^ (L - m)) ^ 2 * channelBall (2 * m) t ≤
      countFormula L m t := by
  have hpow : 4 ^ (2 * L - m - m) = 4 ^ (L - m) * 4 ^ (L - m) := by
    rw [← pow_add]
    congr 1
    omega
  have hinner :
      L.choose m * L.choose m * 4 ^ (2 * L - m - m) * channelBall (m + m) t ≤
      ∑ k ∈ Finset.range (m + 1),
        L.choose m * L.choose k * 4 ^ (2 * L - m - k) * channelBall (m + k) t :=
    Finset.single_le_sum (a := m)
      (f := fun k => L.choose m * L.choose k * 4 ^ (2 * L - m - k) *
        channelBall (m + k) t) (fun _ _ => Nat.zero_le _)
      (Finset.mem_range.mpr (Nat.lt_succ_self m))
  have houter :
      (∑ k ∈ Finset.range (m + 1),
        L.choose m * L.choose k * 4 ^ (2 * L - m - k) * channelBall (m + k) t) ≤
      countFormula L m t := by
    unfold countFormula
    exact Finset.single_le_sum (a := m)
      (f := fun j => ∑ k ∈ Finset.range (m + 1),
        L.choose j * L.choose k * 4 ^ (2 * L - j - k) * channelBall (j + k) t)
      (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr (Nat.lt_succ_self m))
  have heq : (L.choose m * 4 ^ (L - m)) ^ 2 * channelBall (2 * m) t =
      L.choose m * L.choose m * 4 ^ (2 * L - m - m) * channelBall (m + m) t := by
    rw [hpow, two_mul]
    ring
  exact heq ▸ le_trans hinner houter

theorem formula_upper (L m t : ℕ) (hm : m ≤ L) :
    countFormula L m t ≤ ordinaryHalfCount L m ^ 2 * channelBall (2 * m) t := by
  calc
    countFormula L m t ≤
        ∑ j ∈ Finset.range (m + 1), ∑ k ∈ Finset.range (m + 1),
          (L.choose j * 4 ^ (L - j)) * (L.choose k * 4 ^ (L - k)) *
            channelBall (2 * m) t := by
      apply Finset.sum_le_sum
      intro j hj
      apply Finset.sum_le_sum
      intro k hk
      have hjm : j ≤ m := by simpa using Finset.mem_range.mp hj
      have hkm : k ≤ m := by simpa using Finset.mem_range.mp hk
      have hpow : 4 ^ (2 * L - j - k) = 4 ^ (L - j) * 4 ^ (L - k) := by
        rw [← pow_add]
        congr 1
        omega
      rw [hpow]
      have hc := channelBall_mono (show j + k ≤ 2 * m by omega) t
      calc
        _ = ((L.choose j * 4 ^ (L - j)) * (L.choose k * 4 ^ (L - k))) *
            channelBall (j + k) t := by ring
        _ ≤ _ := Nat.mul_le_mul_left _ hc
    _ = ordinaryHalfCount L m ^ 2 * channelBall (2 * m) t := by
      simp only [ordinaryHalfCount, Finset.sum_mul, Finset.mul_sum, pow_two]
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro k hk
      ring

#print axioms formula_lower
#print axioms formula_upper

/-- Actual finite subsets satisfying a cardinality cap. -/
abbrev CappedSubsets (α : Type*) [Fintype α] (m : ℕ) :=
  {s : Finset α // s.card ≤ m}

noncomputable instance cappedSubsetsFintype (α : Type*) [Fintype α] (m : ℕ) :
    Fintype (CappedSubsets α m) := Fintype.ofFinite _

theorem sum_capped_subsets (α : Type*) [Fintype α] (m : ℕ) (f : ℕ → ℕ) :
    (∑ s : CappedSubsets α m, f s.val.card) =
      ∑ j ∈ Finset.range (m + 1), (Fintype.card α).choose j * f j := by
  classical
  let s : Finset (Finset α) := Finset.univ.filter (fun a => a.card ≤ m)
  have hs : ∀ a : Finset α, a ∈ s ↔ a.card ≤ m := by simp [s]
  calc
    _ = ∑ a ∈ s, f a.card := (Finset.sum_subtype s hs (fun a => f a.card)).symm
    _ = ∑ j ∈ Finset.range (m + 1), ∑ a ∈ s.filter (fun a => a.card = j),
        f a.card := by
      symm
      apply Finset.sum_fiberwise_of_maps_to
      intro a ha
      exact Finset.mem_range.mpr (by have := (hs a).mp ha; omega)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      have hjm : j ≤ m := by have := Finset.mem_range.mp hj; omega
      have he : s.filter (fun a => a.card = j) =
          (Finset.univ : Finset α).powersetCard j := by
        ext a
        simp only [s, Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_powersetCard, Finset.subset_univ, true_and]
        omega
      rw [he, Finset.sum_powersetCard]
      simp

theorem capped_subsets_card (α : Type*) [Fintype α] (t : ℕ) :
    Fintype.card (CappedSubsets α t) = channelBall (Fintype.card α) t := by
  have h := sum_capped_subsets α t (fun _ => 1)
  simpa [channelBall] using h

/-- Distinguished support with the two actual physical-half caps. -/
abbrev CappedSupport (L m : ℕ) := {s : Finset (Fin (2 * L)) //
  (s.filter (fun i => i.val < L)).card ≤ m ∧
  (s.filter (fun i => L ≤ i.val)).card ≤ m}

/-- A channel subset of a specified distinguished support. -/
abbrev SupportedChannels {α : Type*} (s : Finset α) (t : ℕ) :=
  {c : Finset α // c ⊆ s ∧ c.card ≤ t}

noncomputable instance cappedSupportFintype (L m : ℕ) : Fintype (CappedSupport L m) :=
  Fintype.ofFinite _
noncomputable instance supportedChannelsFintype {α : Type*} [Fintype α]
    (s : Finset α) (t : ℕ) : Fintype (SupportedChannels s t) := Fintype.ofFinite _

/-- The concrete support/channel/ordinary-label description of a retained word. -/
abbrev LeafData (L m t : ℕ) := (s : CappedSupport L m) ×
  SupportedChannels s.val t × ({i : Fin (2 * L) // i ∉ s.val} → Fin 4)

noncomputable def wordSupport {n : ℕ} (w : Word n) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun i => distinguished (w i))

noncomputable def wordChannels {n : ℕ} (w : Word n) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun i => channel (w i))

theorem wordChannels_subset {n : ℕ} (w : Word n) : wordChannels w ⊆ wordSupport w := by
  classical
  intro i hi
  simp only [wordChannels, Finset.mem_filter, Finset.mem_univ, true_and, channel] at hi
  simp only [wordSupport, Finset.mem_filter, Finset.mem_univ, true_and, distinguished]
  omega

noncomputable def leafToData {L m t : ℕ} (w : Leaves L m t) : LeafData L m t := by
  classical
  refine ⟨⟨wordSupport w.val, ?_⟩, ⟨wordChannels w.val, wordChannels_subset w.val, ?_⟩,
    fun i => ⟨(w.val i.val).val, ?_⟩⟩
  · rcases w.property with ⟨h₁, h₂, _⟩
    constructor
    · simpa [wordSupport, countPositions, Finset.filter_filter, and_comm] using h₁
    · simpa [wordSupport, countPositions, Finset.filter_filter, and_comm] using h₂
  · simpa [wordChannels, countPositions] using w.property.2.2
  · have hi := i.property
    simp only [wordSupport, Finset.mem_filter, Finset.mem_univ, true_and, distinguished,
      not_le] at hi
    exact hi

noncomputable def dataWord {L m t : ℕ} (v : LeafData L m t) : Word (2 * L) := by
  classical
  exact fun i => if hc : i ∈ v.2.1.val then 5 else if hs : i ∈ v.1.val then 4 else
    ⟨(v.2.2 ⟨i, hs⟩).val, by have := (v.2.2 ⟨i, hs⟩).isLt; omega⟩

theorem dataWord_distinguished {L m t : ℕ} (v : LeafData L m t) (i : Fin (2 * L)) :
    distinguished (dataWord v i) ↔ i ∈ v.1.val := by
  classical
  unfold dataWord distinguished
  split_ifs with hc hs
  · have := v.2.1.property.1 hc
    simp_all
  · simp_all
  · have := (v.2.2 ⟨i, hs⟩).isLt
    simp only [hs, iff_false]
    omega

theorem dataWord_channel {L m t : ℕ} (v : LeafData L m t) (i : Fin (2 * L)) :
    channel (dataWord v i) ↔ i ∈ v.2.1.val := by
  classical
  unfold dataWord channel
  split_ifs with hc hs
  · simp_all
  · simp_all
  · have := (v.2.2 ⟨i, hs⟩).isLt
    simp_all
    omega

theorem dataWord_retained {L m t : ℕ} (v : LeafData L m t) : Retained L m t (dataWord v) := by
  classical
  unfold Retained countPositions
  simp_rw [dataWord_distinguished, dataWord_channel]
  have h₁ : (Finset.univ.filter (fun i : Fin (2 * L) => i.val < L ∧ i ∈ v.1.val)) =
      v.1.val.filter (fun i => i.val < L) := by ext i; simp [and_comm]
  have h₂ : (Finset.univ.filter (fun i : Fin (2 * L) => L ≤ i.val ∧ i ∈ v.1.val)) =
      v.1.val.filter (fun i => L ≤ i.val) := by ext i; simp [and_comm]
  rw [h₁, h₂]
  simpa using And.intro v.1.property.1 (And.intro v.1.property.2 v.2.1.property.2)

noncomputable def dataToLeaf {L m t : ℕ} (v : LeafData L m t) : Leaves L m t :=
  ⟨dataWord v, dataWord_retained v⟩

theorem dataToLeaf_leafToData {L m t : ℕ} (w : Leaves L m t) :
    dataToLeaf (leafToData w) = w := by
  classical
  apply Subtype.ext
  funext i
  apply Fin.ext
  simp only [dataToLeaf, dataWord, leafToData]
  split_ifs with hc hs
  · have hv : (w.val i).val = 5 := by simpa [wordChannels, channel] using hc
    exact hv.symm
  · have hsi : 4 ≤ (w.val i).val := by simpa [wordSupport, distinguished] using hs
    have hci : (w.val i).val ≠ 5 := by simpa [wordChannels, channel] using hc
    have := (w.val i).isLt
    omega
  · rfl

theorem leafData_ext {L m t : ℕ} {u v : LeafData L m t}
    (hs : u.1 = v.1) (hc : u.2.1.val = v.2.1.val)
    (hf : ∀ i (hu : i ∉ u.1.val) (hv : i ∉ v.1.val),
      (u.2.2 ⟨i, hu⟩).val = (v.2.2 ⟨i, hv⟩).val) : u = v := by
  cases u with
  | mk su xu =>
    cases v with
    | mk sv xv =>
      dsimp at hs hc hf
      cases hs
      congr 1
      apply Prod.ext
      · exact Subtype.ext hc
      · funext i
        apply Fin.ext
        exact hf i.val i.property i.property

theorem leafToData_dataToLeaf {L m t : ℕ} (v : LeafData L m t) :
    leafToData (dataToLeaf v) = v := by
  classical
  have hs : wordSupport (dataWord v) = v.1.val := by
    ext i
    simp only [wordSupport, Finset.mem_filter, Finset.mem_univ, true_and]
    exact dataWord_distinguished v i
  have hc : wordChannels (dataWord v) = v.2.1.val := by
    ext i
    simp only [wordChannels, Finset.mem_filter, Finset.mem_univ, true_and]
    exact dataWord_channel v i
  apply leafData_ext (Subtype.ext hs) hc
  intro i hi₁ hi₂
  have hi : i ∉ v.2.1.val := fun h => hi₂ (v.2.1.property.1 h)
  simp [leafToData, dataToLeaf, dataWord, hi, hi₂]

/-- A proved equivalence from genuine retained words to support/channel data. -/
noncomputable def leavesEquivData (L m t : ℕ) : Leaves L m t ≃ LeafData L m t where
  toFun := leafToData
  invFun := dataToLeaf
  left_inv := dataToLeaf_leafToData
  right_inv := leafToData_dataToLeaf

#print axioms leavesEquivData

theorem supported_channels_card {α : Type*} [Fintype α] (s : Finset α) (t : ℕ) :
    Fintype.card (SupportedChannels s t) = channelBall s.card t := by
  classical
  let a : Finset (Finset α) := s.powerset.filter (fun c => c.card ≤ t)
  have ha : ∀ c : Finset α, c ∈ a ↔ c ⊆ s ∧ c.card ≤ t := by simp [a]
  rw [Fintype.card_of_subtype a ha]
  rw [Finset.card_eq_sum_card_fiberwise
    (f := Finset.card) (t := Finset.range (t + 1))]
  · apply Finset.sum_congr rfl
    intro h hh
    have hht : h ≤ t := by have := Finset.mem_range.mp hh; omega
    have he : a.filter (fun c => c.card = h) = s.powersetCard h := by
      ext c
      simp only [a, Finset.mem_filter, Finset.mem_powerset, Finset.mem_powersetCard]
      constructor
      · intro hc
        exact ⟨hc.1.1, hc.2⟩
      · intro hc
        exact ⟨⟨hc.1, by omega⟩, hc.2⟩
    rw [he, Finset.card_powersetCard]
  · intro c hc
    exact Finset.mem_range.mpr (by have := ((ha c).mp hc).2; omega)

/-- Actual retained-word cardinality as the support sum; no numerical count
is assumed in this theorem. -/
theorem retainedLeafCount_eq_support_sum (L m t : ℕ) :
    retainedLeafCount L m t = ∑ s : CappedSupport L m,
      channelBall s.val.card t * 4 ^ (2 * L - s.val.card) := by
  classical
  unfold retainedLeafCount
  rw [Fintype.card_congr (leavesEquivData L m t)]
  simp only [LeafData, Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro s hs
  rw [Fintype.card_prod, supported_channels_card, Fintype.card_fun]
  congr 2
  rw [Fintype.card_subtype_compl]
  simp

#print axioms retainedLeafCount_eq_support_sum

abbrev FirstHalf (L : ℕ) := {i : Fin (2 * L) // i.val < L}
abbrev SecondHalf (L : ℕ) := {i : Fin (2 * L) // ¬i.val < L}

theorem firstHalf_card (L : ℕ) : Fintype.card (FirstHalf L) = L := by
  rw [Fintype.card_subtype]
  change (Finset.univ.filter (fun i : Fin (2 * L) => i.val < L)).card = L
  rw [Fin.card_filter_val_lt]
  omega

theorem secondHalf_card (L : ℕ) : Fintype.card (SecondHalf L) = L := by
  rw [Fintype.card_subtype_compl, firstHalf_card, Fintype.card_fin]
  omega

/-- Split an actual position subset into its two disjoint physical halves. -/
noncomputable def splitPositions (L : ℕ) : Finset (Fin (2 * L)) ≃
    Finset (FirstHalf L) × Finset (SecondHalf L) :=
  ((Equiv.sumCompl (fun i : Fin (2 * L) => i.val < L)).symm.finsetCongr).trans
    Finset.sumEquiv.toEquiv

theorem splitPositions_first (L : ℕ) (s : Finset (Fin (2 * L))) :
    (splitPositions L s).1 = s.subtype (fun i => i.val < L) := by
  classical
  ext i
  change i ∈ (s.map (Equiv.sumCompl (fun i : Fin (2 * L) => i.val < L)).symm.toEmbedding).toLeft ↔
    i ∈ s.subtype (fun i : Fin (2 * L) => i.val < L)
  simp

theorem splitPositions_second (L : ℕ) (s : Finset (Fin (2 * L))) :
    (splitPositions L s).2 = s.subtype (fun i => ¬i.val < L) := by
  classical
  ext i
  change i ∈ (s.map (Equiv.sumCompl (fun i : Fin (2 * L) => i.val < L)).symm.toEmbedding).toRight ↔
    i ∈ s.subtype (fun i : Fin (2 * L) => ¬i.val < L)
  simp

theorem splitPositions_card (L : ℕ) (s : Finset (Fin (2 * L))) :
    (splitPositions L s).1.card + (splitPositions L s).2.card = s.card := by
  classical
  rw [splitPositions_first, splitPositions_second, Finset.card_subtype,
    Finset.card_subtype]
  exact Finset.card_filter_add_card_filter_not _

noncomputable def cappedSupportEquiv (L m : ℕ) : CappedSupport L m ≃
    CappedSubsets (FirstHalf L) m × CappedSubsets (SecondHalf L) m :=
  (Equiv.subtypeEquiv (splitPositions L) (by
    intro s
    simp [splitPositions_first, splitPositions_second, Finset.card_subtype,
      not_lt])).trans Equiv.subtypeProdEquivProd

theorem cappedSupportEquiv_card (L m : ℕ) (s : CappedSupport L m) :
    (cappedSupportEquiv L m s).1.val.card +
      (cappedSupportEquiv L m s).2.val.card = s.val.card :=
  splitPositions_card L s.val

theorem sum_capped_support (L m : ℕ) (f : ℕ → ℕ) :
    (∑ s : CappedSupport L m, f s.val.card) =
      ∑ j ∈ Finset.range (m + 1), ∑ k ∈ Finset.range (m + 1),
        L.choose j * L.choose k * f (j + k) := by
  classical
  calc
    _ = ∑ p : CappedSubsets (FirstHalf L) m × CappedSubsets (SecondHalf L) m,
        f (p.1.val.card + p.2.val.card) := by
      apply Fintype.sum_equiv (cappedSupportEquiv L m)
      intro s
      rw [cappedSupportEquiv_card]
    _ = ∑ a : CappedSubsets (FirstHalf L) m,
        ∑ b : CappedSubsets (SecondHalf L) m, f (a.val.card + b.val.card) := by
      rw [Fintype.sum_prod_type]
    _ = ∑ a : CappedSubsets (FirstHalf L) m,
        ∑ k ∈ Finset.range (m + 1), L.choose k * f (a.val.card + k) := by
      apply Finset.sum_congr rfl
      intro a ha
      have h := sum_capped_subsets (SecondHalf L) m (fun k => f (a.val.card + k))
      rw [secondHalf_card] at h
      exact h
    _ = ∑ j ∈ Finset.range (m + 1), L.choose j *
        (∑ k ∈ Finset.range (m + 1), L.choose k * f (j + k)) := by
      simpa [firstHalf_card] using sum_capped_subsets (FirstHalf L) m
        (fun j => ∑ k ∈ Finset.range (m + 1), L.choose k * f (j + k))
    _ = _ := by
      simp only [Finset.mul_sum, mul_assoc]

/-- Exact formula A8 for the cardinality of genuine retained six-letter words. -/
theorem retainedLeafCount_eq_formula (L m t : ℕ) :
    retainedLeafCount L m t = countFormula L m t := by
  rw [retainedLeafCount_eq_support_sum,
    sum_capped_support L m (fun n => channelBall n t * 4 ^ (2 * L - n))]
  unfold countFormula
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  rw [Nat.sub_add_eq]
  ring

#print axioms retainedLeafCount_eq_formula

/-- Formula A8 with its explicitly truncated channel sum. -/
theorem retainedLeafCount_eq_A8 (L m t : ℕ) :
    retainedLeafCount L m t =
      ∑ j ∈ Finset.range (m + 1), ∑ k ∈ Finset.range (m + 1),
        L.choose j * L.choose k * 4 ^ (2 * L - j - k) *
          (∑ h ∈ Finset.range (min t (j + k) + 1), (j + k).choose h) := by
  rw [retainedLeafCount_eq_formula]
  simp only [countFormula, channelBall_eq_min]

/-- The actual word count includes the entire exactly-m-per-half family. -/
theorem retainedLeafCount_lower (L m t : ℕ) (hm : m ≤ L) :
    (L.choose m * 4 ^ (L - m)) ^ 2 * channelBall (2 * m) t ≤
      retainedLeafCount L m t := by
  rw [retainedLeafCount_eq_formula]
  exact formula_lower L m t hm

/-- The actual word count is bounded by the product of the two capped
ordinary half counts and the common joint channel ball. -/
theorem retainedLeafCount_upper (L m t : ℕ) (hm : m ≤ L) :
    retainedLeafCount L m t ≤ ordinaryHalfCount L m ^ 2 * channelBall (2 * m) t := by
  rw [retainedLeafCount_eq_formula]
  exact formula_upper L m t hm

#print axioms retainedLeafCount_eq_A8
#print axioms retainedLeafCount_lower
#print axioms retainedLeafCount_upper

/-- Genuine no-channel retained words with an additional total special cap. -/
abbrev TotalCappedLeaves (L m u : ℕ) := {w : Leaves L m 0 //
  countPositions w.val (fun _ a => distinguished a) ≤ u}

noncomputable instance totalCappedLeavesFintype (L m u : ℕ) :
    Fintype (TotalCappedLeaves L m u) := Fintype.ofFinite _

theorem no_channels_iff {n : ℕ} (w : Word n) :
    countPositions w (fun _ a => channel a) = 0 ↔ ∀ i, (w i).val ≠ 5 := by
  classical
  simp [countPositions, Finset.card_eq_zero, Finset.filter_eq_empty_iff, channel]

theorem count_distinguished_eq_support {n : ℕ} (w : Word n) :
    countPositions w (fun _ a => distinguished a) = (wordSupport w).card := rfl

theorem dataWord_support {L m t : ℕ} (v : LeafData L m t) :
    wordSupport (dataWord v) = v.1.val := by
  classical
  ext i
  simp only [wordSupport, Finset.mem_filter, Finset.mem_univ, true_and]
  exact dataWord_distinguished v i

/-- Exact base-family cardinality with a total distinguished cap. -/
theorem totalCappedLeaves_card (L m u : ℕ) :
    Fintype.card (TotalCappedLeaves L m u) =
      ∑ j ∈ Finset.range (m + 1), ∑ k ∈ Finset.range (m + 1),
        if j + k ≤ u then L.choose j * L.choose k * 4 ^ (2 * L - j - k) else 0 := by
  classical
  calc
    _ = ∑ w : Leaves L m 0,
        if countPositions w.val (fun _ a => distinguished a) ≤ u then 1 else 0 := by
      rw [Fintype.card_subtype, Finset.card_eq_sum_ones, Finset.sum_filter]
    _ = ∑ v : LeafData L m 0, if v.1.val.card ≤ u then 1 else 0 := by
      apply Fintype.sum_equiv (leavesEquivData L m 0)
      intro w
      rfl
    _ = ∑ s : CappedSupport L m, if s.val.card ≤ u then 4 ^ (2 * L - s.val.card) else 0 := by
      rw [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro s hs
      by_cases h : s.val.card ≤ u
      · simp only [h, ite_true, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one]
        rw [Fintype.card_prod, supported_channels_card, Fintype.card_fun]
        simp only [channelBall_zero, one_mul, Fintype.card_fin]
        congr 1
        rw [Fintype.card_subtype_compl]
        simp
      · simp [h]
    _ = _ := by
      rw [sum_capped_support L m (fun n => if n ≤ u then 4 ^ (2 * L - n) else 0)]
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro k hk
      by_cases h : j + k ≤ u
      · simp only [h, ite_true, Nat.sub_add_eq]
      · simp [h]

#print axioms totalCappedLeaves_card
#print axioms no_channels_iff

end ThinMatrix.CacheCardinality
