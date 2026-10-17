import GoodSets

/-!
# Uniform conditional-expectation construction of binary good-set maps

The column schedule uses finite zero-kernel tests and exact rational
conditional rank potentials. The finite candidate-column and coefficient-vector
loops are counted; the remaining rational and vector operations are polynomial
in L. GoodSets is imported unchanged.
-/

set_option maxHeartbeats 2000000

namespace ThinMatrix.GoodSetConstruction
open scoped BigOperators
open GoodSets

/-- Explicit lexicographic enumeration. No choice is used in this definition. -/
def binaryColumns : (m : ℕ) → List (Fin m → F₂)
  | 0 => [fun i => Fin.elim0 i]
  | m+1 => (binaryColumns m).map (Fin.cons 0) ++
      (binaryColumns m).map (Fin.cons 1)

@[simp] theorem binaryColumns_length (m : ℕ) :
    (binaryColumns m).length = 2^m := by
  induction m with
  | zero => simp [binaryColumns]
  | succ m ih => simp [binaryColumns, ih, pow_succ]; omega

theorem mem_binaryColumns (m : ℕ) (x : Fin m → F₂) :
    x ∈ binaryColumns m := by
  induction m with
  | zero => simp [binaryColumns, Subsingleton.elim x (fun i => Fin.elim0 i)]
  | succ m ih =>
    have hx : x 0 = 0 ∨ x 0 = 1 := by
      generalize x 0 = a
      fin_cases a
      · exact Or.inl rfl
      · exact Or.inr rfl
    rcases hx with hx | hx
    · apply List.mem_append_left
      apply List.mem_map.mpr
      exact ⟨Fin.tail x, ih (Fin.tail x), by simpa [hx] using Fin.cons_self_tail x⟩
    · apply List.mem_append_right
      apply List.mem_map.mpr
      exact ⟨Fin.tail x, ih (Fin.tail x), by simpa [hx] using Fin.cons_self_tail x⟩

/-- Every column occurs exactly once: the full cardinality is already 2^m. -/
theorem binaryColumns_nodup (m : ℕ) : (binaryColumns m).Nodup := by
  classical
  have heq : (binaryColumns m).toFinset = Finset.univ := by
    ext x
    simp [mem_binaryColumns]
  apply Multiset.coe_nodup.mp
  apply Multiset.toFinset_card_eq_card_iff_nodup.mp
  change (binaryColumns m).toFinset.card = (binaryColumns m).length
  rw [heq, Finset.card_univ, binaryColumns_length]
  simp [F₂]

/-- One traversal records one score per candidate and counts those calls. -/
def cacheScores {A : Type*} (score : A → ℚ) : List A → List (A × ℚ) × ℕ
  | [] => ([], 0)
  | a :: as =>
      let tail := cacheScores score as
      ((a, score a) :: tail.1, tail.2 + 1)

@[simp] theorem cacheScores_entries {A : Type*} (score : A → ℚ) (xs : List A) :
    (cacheScores score xs).1 = xs.map (fun a => (a, score a)) := by
  induction xs with
  | nil => rfl
  | cons a as ih => simp [cacheScores, ih]

@[simp] theorem cacheScores_calls {A : Type*} (score : A → ℚ) (xs : List A) :
    (cacheScores score xs).2 = xs.length := by
  induction xs with
  | nil => rfl
  | cons a as ih => simp [cacheScores, ih]

/-- Compare cached rationals only; the scoring function is absent. -/
def cachedMaxFrom {A : Type*} (best : A × ℚ) : List (A × ℚ) → A × ℚ
  | [] => best
  | entry :: rest => cachedMaxFrom (if best.2 < entry.2 then entry else best) rest

theorem cachedMaxFrom_ge_start {A : Type*} (best : A × ℚ) (entries : List (A × ℚ)) :
    best.2 ≤ (cachedMaxFrom best entries).2 := by
  induction entries generalizing best with
  | nil => exact le_rfl
  | cons entry rest ih =>
    simp only [cachedMaxFrom]
    split_ifs with h
    · exact (le_of_lt h).trans (ih entry)
    · exact ih best

theorem cachedMaxFrom_ge_mem {A : Type*} (best entry : A × ℚ)
    (entries : List (A × ℚ)) (hentry : entry ∈ entries) :
    entry.2 ≤ (cachedMaxFrom best entries).2 := by
  induction entries generalizing best with
  | nil => simp at hentry
  | cons head rest ih =>
    rcases List.mem_cons.mp hentry with rfl | hentry
    · simp only [cachedMaxFrom]
      split_ifs with h
      · exact cachedMaxFrom_ge_start entry rest
      · exact (le_of_not_gt h).trans (cachedMaxFrom_ge_start best rest)
    · simp only [cachedMaxFrom]
      exact ih _ hentry

theorem cachedMaxFrom_mem {A : Type*} (best : A × ℚ) (entries : List (A × ℚ)) :
    cachedMaxFrom best entries ∈ best :: entries := by
  induction entries generalizing best with
  | nil => simp [cachedMaxFrom]
  | cons entry rest ih =>
    simp only [cachedMaxFrom]
    split_ifs with h
    · rcases List.mem_cons.mp (ih entry) with he | he
      · exact List.mem_cons_of_mem best (List.mem_cons.mpr (Or.inl he))
      · exact List.mem_cons_of_mem best (List.mem_cons_of_mem entry he)
    · rcases List.mem_cons.mp (ih best) with he | he
      · exact List.mem_cons.mpr (Or.inl he)
      · exact List.mem_cons_of_mem best (List.mem_cons_of_mem entry he)

/-- The default is used only for an empty list. -/
def cachedMax {A : Type*} (fallback : A × ℚ) : List (A × ℚ) → A × ℚ
  | [] => fallback
  | best :: rest => cachedMaxFrom best rest

theorem cachedMax_mem {A : Type*} (fallback : A × ℚ) (entries : List (A × ℚ))
    (hne : entries ≠ []) : cachedMax fallback entries ∈ entries := by
  cases entries with
  | nil => exact (hne rfl).elim
  | cons best rest => exact cachedMaxFrom_mem best rest

theorem cachedMax_ge_mem {A : Type*} (fallback entry : A × ℚ)
    (entries : List (A × ℚ)) (hentry : entry ∈ entries) :
    entry.2 ≤ (cachedMax fallback entries).2 := by
  cases entries with
  | nil => simp at hentry
  | cons best rest =>
    rcases List.mem_cons.mp hentry with rfl | hentry
    · exact cachedMaxFrom_ge_start entry rest
    · exact cachedMaxFrom_ge_mem best entry rest hentry

/-- Fully computable deterministic maximizer of all binary-column scores. -/
def selectColumn (m : ℕ) (score : (Fin m → F₂) → ℚ) : Fin m → F₂ :=
  (cachedMax (0, 0) (cacheScores score (binaryColumns m)).1).1

theorem selectColumn_max (m : ℕ) (score : (Fin m → F₂) → ℚ)
    (x : Fin m → F₂) : score x ≤ score (selectColumn m score) := by
  let entries := (cacheScores score (binaryColumns m)).1
  have hx : (x, score x) ∈ entries := by
    simp only [entries, cacheScores_entries]
    exact List.mem_map.mpr ⟨x, mem_binaryColumns m x, rfl⟩
  have hne : entries ≠ [] := by
    intro h
    simp [h] at hx
  have hmem := cachedMax_mem (0, 0) entries hne
  have hscore : (cachedMax (0, 0) entries).2 =
      score (cachedMax (0, 0) entries).1 := by
    have hmem' : cachedMax (0, 0) entries ∈
        (binaryColumns m).map (fun a => (a, score a)) := by
      simpa only [entries, cacheScores_entries] using hmem
    obtain ⟨a, _, ha⟩ := List.mem_map.mp hmem'
    rw [← ha]
  rw [selectColumn]
  exact (cachedMax_ge_mem (0, 0) (x, score x) entries hx).trans_eq hscore

/-- Exactly 2^m scoring calls, including m=0; comparisons read stored scores. -/
theorem selectColumn_score_calls (m : ℕ) (score : (Fin m → F₂) → ℚ) :
    (cacheScores score (binaryColumns m)).2 = 2^m := by simp

/-- A proved nondecreasing child can be replaced by the computed maximum. -/
theorem selectColumn_ge_child (m : ℕ) (score : (Fin m → F₂) → ℚ)
    (parent : ℚ) (h : ∃ x, parent ≤ score x) :
    parent ≤ score (selectColumn m score) := by
  obtain ⟨x, hx⟩ := h
  exact hx.trans (selectColumn_max m score x)

/-- Convert a proved finite child-average into the executable choice. -/
theorem selectColumn_ge_average (m : ℕ) (score : (Fin m → F₂) → ℚ)
    (parent : ℚ)
    (h : (2:ℚ)^m * parent = ∑ x, score x) :
    parent ≤ score (selectColumn m score) := by
  obtain ⟨x, hx⟩ := choose_finite_child score parent (by simpa [F₂] using h)
  exact hx.trans (selectColumn_max m score x)


/-- Actual queried columns already fixed by the physical prefixSet. -/
def prefixSet {L : ℕ} (Q : Finset (Fin L)) (ell : ℕ) : Finset (Fin L) :=
  Q.filter (fun i => i.val < ell)

@[simp] theorem mem_prefixSet {L : ℕ} (Q : Finset (Fin L)) (ell : ℕ)
    (i : Fin L) : i ∈ prefixSet Q ell ↔ i ∈ Q ∧ i.val < ell := by
  simp [prefixSet]

@[simp] theorem prefixSet_zero {L : ℕ} (Q : Finset (Fin L)) :
    prefixSet Q 0 = ∅ := by
  ext i
  simp

@[simp] theorem prefixSet_full {L : ℕ} (Q : Finset (Fin L)) :
    prefixSet Q L = Q := by
  ext i
  simp [i.isLt]

theorem prefixSet_subset {L : ℕ} (Q : Finset (Fin L)) (ell : ℕ) :
    prefixSet Q ell ⊆ Q := Finset.filter_subset _ _

theorem column_not_mem_prefixSet {L ell : ℕ} (Q : Finset (Fin L))
    (he : ell < L) : (⟨ell, he⟩ : Fin L) ∉ prefixSet Q ell := by
  simp

theorem prefixSet_succ_of_mem {L ell : ℕ} (Q : Finset (Fin L))
    (he : ell < L) (hq : (⟨ell, he⟩ : Fin L) ∈ Q) :
    prefixSet Q (ell+1) = insert ⟨ell, he⟩ (prefixSet Q ell) := by
  ext i
  simp only [mem_prefixSet, Finset.mem_insert]
  constructor
  · intro hi
    by_cases h : i.val < ell
    · exact Or.inr ⟨hi.1, h⟩
    · apply Or.inl
      apply Fin.ext
      change i.val = ell
      omega
  · rintro (rfl | hi)
    · exact ⟨hq, Nat.lt_succ_self _⟩
    · exact ⟨hi.1, by omega⟩

theorem prefixSet_succ_of_not_mem {L ell : ℕ} (Q : Finset (Fin L))
    (he : ell < L) (hq : (⟨ell, he⟩ : Fin L) ∉ Q) :
    prefixSet Q (ell+1) = prefixSet Q ell := by
  ext i
  simp only [mem_prefixSet]
  constructor
  · intro hi
    refine ⟨hi.1, ?_⟩
    by_contra hn
    have heq : i = ⟨ell, he⟩ := by
      apply Fin.ext
      change i.val = ell
      omega
    exact hq (heq ▸ hi.1)
  · intro hi
    exact ⟨hi.1, by omega⟩

theorem prefixSet_card_succ_of_mem {L ell : ℕ} (Q : Finset (Fin L))
    (he : ell < L) (hq : (⟨ell, he⟩ : Fin L) ∈ Q) :
    (prefixSet Q (ell+1)).card = (prefixSet Q ell).card + 1 := by
  rw [prefixSet_succ_of_mem Q he hq,
    Finset.card_insert_of_notMem (column_not_mem_prefixSet Q he)]

theorem prefixSet_card_succ_of_not_mem {L ell : ℕ} (Q : Finset (Fin L))
    (he : ell < L) (hq : (⟨ell, he⟩ : Fin L) ∉ Q) :
    (prefixSet Q (ell+1)).card = (prefixSet Q ell).card := by
  rw [prefixSet_succ_of_not_mem Q he hq]

theorem prefixSet_card_lt_of_mem {L ell : ℕ} (Q : Finset (Fin L))
    (he : ell < L) (hq : (⟨ell, he⟩ : Fin L) ∈ Q) :
    (prefixSet Q ell).card < Q.card := by
  have hsub : insert (⟨ell, he⟩ : Fin L) (prefixSet Q ell) ⊆ Q := by
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact hq
    · exact prefixSet_subset Q ell hi
  have hc := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem (column_not_mem_prefixSet Q he)] at hc
  omega

theorem update_eqOn_prefixSet {L ell : ℕ} {V : Type*}
    (Q : Finset (Fin L)) (he : ell < L) (Γ : Fin L → V) (x : V) :
    Set.EqOn (Function.update Γ ⟨ell, he⟩ x) Γ (prefixSet Q ell) := by
  intro i hi
  have hne : i ≠ ⟨ell, he⟩ := by
    intro heq
    exact column_not_mem_prefixSet Q he (heq ▸ hi)
  exact Function.update_of_ne hne x Γ

theorem prefix_restrict_update {L ell : ℕ} {V : Type*}
    (Q : Finset (Fin L)) (he : ell < L) (Γ : Fin L → V) (x : V) :
    (fun i : prefixSet Q ell => Function.update Γ ⟨ell, he⟩ x i) =
      (fun i : prefixSet Q ell => Γ i) := by
  funext i
  exact update_eqOn_prefixSet Q he Γ x i.property

theorem prefix_update_independent_of_mem {L m ell : ℕ}
    (Q : Finset (Fin L)) (he : ell < L)
    (hq : (⟨ell, he⟩ : Fin L) ∈ Q) (Γ : BinaryMap m L)
    (x : Fin m → F₂) :
    LinearIndependent F₂
        (fun i : prefixSet Q (ell+1) => Function.update Γ ⟨ell, he⟩ x i) ↔
      LinearIndependent F₂ (fun i : prefixSet Q ell => Γ i) ∧
      x ∉ Submodule.span F₂ (Set.range (fun i : prefixSet Q ell => Γ i)) := by
  classical
  change LinearIndepOn F₂ (Function.update Γ ⟨ell, he⟩ x)
    (prefixSet Q (ell+1) : Set (Fin L)) ↔ _
  rw [prefixSet_succ_of_mem Q he hq, Finset.coe_insert,
    linearIndepOn_insert (column_not_mem_prefixSet Q he)]
  have hres := prefix_restrict_update Q he Γ x
  have himage : (Function.update Γ ⟨ell, he⟩ x) '' (prefixSet Q ell : Set (Fin L)) =
      Set.range (fun i : prefixSet Q ell => Γ i) := by
    rw [Set.image_eq_range]
    congr 1
  change LinearIndependent F₂
      (fun i : prefixSet Q ell => Function.update Γ ⟨ell, he⟩ x i) ∧ _ ↔ _
  rw [hres, himage]
  simp

theorem prefix_update_independent_of_not_mem {L m ell : ℕ}
    (Q : Finset (Fin L)) (he : ell < L)
    (hq : (⟨ell, he⟩ : Fin L) ∉ Q) (Γ : BinaryMap m L)
    (x : Fin m → F₂) :
    LinearIndependent F₂
        (fun i : prefixSet Q (ell+1) => Function.update Γ ⟨ell, he⟩ x i) ↔
      LinearIndependent F₂ (fun i : prefixSet Q ell => Γ i) := by
  rw [prefixSet_succ_of_not_mem Q he hq, prefix_restrict_update Q he Γ x]


/-- Executable zero-kernel test on the actual restricted column set. -/
def restrictionTest {L r : ℕ} (Γ : BinaryMap r L) (Q : Finset (Fin L)) : Bool :=
  decide (∀ c : Q → F₂, (∑ i : Q, c i • Γ i) = 0 → c = 0)

lemma restrictionTest_correct {L r : ℕ} (Γ : BinaryMap r L) (Q : Finset (Fin L)) :
    restrictionTest Γ Q = true ↔ LinearIndependent F₂ (fun i : Q => Γ i) := by
  simp only [restrictionTest, decide_eq_true_eq]
  rw [linearIndependent_iff_injective_fintypeLinearCombination,
    ← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  simp only [Fintype.linearCombination_apply]

/-- The computable conditional probability of an independent completion. -/
def potential {L r : ℕ} (Γ : BinaryMap r L) (Q : Finset (Fin L)) (ell : ℕ) : ℚ :=
  if restrictionTest Γ (prefixSet Q ell) then binarySuccess (r-(prefixSet Q ell).card) else 0

lemma potential_eq {L r : ℕ} (Γ : BinaryMap r L) (Q : Finset (Fin L)) (ell : ℕ) :
    potential Γ Q ell = @ite ℚ (LinearIndependent F₂ (fun i : prefixSet Q ell => Γ i))
      (Classical.propDecidable _) (binarySuccess (r-(prefixSet Q ell).card)) 0 := by
  classical
  simp only [potential, restrictionTest_correct]

lemma prefix_zero {L : ℕ} (Q : Finset (Fin L)) : prefixSet Q 0 = ∅ := by
  simp [prefixSet]

lemma prefix_full {L : ℕ} (Q : Finset (Fin L)) : prefixSet Q L = Q := by
  ext i
  simp [prefixSet]

lemma potential_zero {L r : ℕ} (Γ : BinaryMap r L) (Q : Finset (Fin L)) :
    potential Γ Q 0 = binarySuccess r := by
  classical
  rw [potential_eq, prefix_zero]
  simp

lemma potential_full {L r : ℕ} (Γ : BinaryMap r L) (Q : Finset (Fin L))
    (hQ : Q.card = r) :
    potential Γ Q L = @ite ℚ (LinearIndependent F₂ (fun i : Q => Γ i))
      (Classical.propDecidable _) 1 0 := by
  classical
  rw [potential_eq, prefix_full, hQ]
  simp [binarySuccess]

/-- Exact extension count for an arbitrary finite independent index set. -/
lemma independent_extension_card {I : Type*} [Fintype I] (r : ℕ)
    (v : I → (Fin r → F₂)) (hv : LinearIndependent F₂ v) :
    Nat.card {x : Fin r → F₂ // x ∉ Submodule.span F₂ (Set.range v)} =
      2^r - 2^(Fintype.card I) := by
  classical
  let S : Set (Fin r → F₂) := Submodule.span F₂ (Set.range v)
  change Nat.card (Sᶜ : Set (Fin r → F₂)) = _
  rw [Nat.card_eq_fintype_card, Fintype.card_compl_set]
  have hc : Fintype.card S = 2^(Fintype.card I) := by
    change Fintype.card (Submodule.span F₂ (Set.range v)) = _
    rw [Module.card_eq_pow_finrank (K := F₂), finrank_span_eq_card hv]
    simp [F₂]
  rw [hc]
  simp [F₂]

/-- Weighted potential shared by every subset at this column stage. -/
def score {A : Type*} [Fintype A] {L r : ℕ}
    (sets : A → Finset (Fin L)) (weights : A → ℚ)
    (Γ : BinaryMap r L) (ell : ℕ) : ℚ :=
  ∑ a, weights a * potential Γ (sets a) ell

lemma score_zero {A : Type*} [Fintype A] {L r : ℕ}
    (sets : A → Finset (Fin L)) (weights : A → ℚ) (Γ : BinaryMap r L) :
    score sets weights Γ 0 = binarySuccess r * ∑ a, weights a := by
  simp only [score, potential_zero]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  ring


lemma potential_column_average {L r ell : ℕ} (Q : Finset (Fin L))
    (hQ : Q.card = r) (he : ell < L) (Γ : BinaryMap r L) :
    (∑ x : Fin r → F₂, potential (Function.update Γ ⟨ell,he⟩ x) Q (ell+1)) =
      (2:ℚ)^r * potential Γ Q ell := by
  classical
  by_cases hq : (⟨ell,he⟩ : Fin L) ∈ Q
  · have hcard := prefixSet_card_succ_of_mem Q he hq
    have hr : (prefixSet Q ell).card < r := by
      simpa [hQ] using prefixSet_card_lt_of_mem Q he hq
    by_cases hv : LinearIndependent F₂ (fun i : prefixSet Q ell => Γ i)
    · have hsum : (∑ x : Fin r → F₂,
          potential (Function.update Γ ⟨ell,he⟩ x) Q (ell+1)) =
          (Nat.card {x : Fin r → F₂ // x ∉ Submodule.span F₂
            (Set.range (fun i : prefixSet Q ell => Γ i))} : ℚ) *
            binarySuccess (r-((prefixSet Q ell).card+1)) := by
        simp only [potential_eq, hcard, prefix_update_independent_of_mem Q he hq,
          hv, true_and, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul,
          Nat.card_eq_fintype_card, Fintype.card_subtype]
      rw [hsum, independent_extension_card r _ hv]
      simp only [Fintype.card_coe]
      rw [binary_factor r (prefixSet Q ell).card hr, potential_eq, if_pos hv]
      have hk : r-(prefixSet Q ell).card = (r-((prefixSet Q ell).card+1))+1 := by omega
      rw [hk, binarySuccess_succ]
      ring
    · simp only [potential_eq, prefix_update_independent_of_mem Q he hq, hv,
        false_and, ite_false, Finset.sum_const_zero, mul_zero]
  · have hpoint (x : Fin r → F₂) :
        potential (Function.update Γ ⟨ell,he⟩ x) Q (ell+1) = potential Γ Q ell := by
      simp only [potential_eq, prefixSet_card_succ_of_not_mem Q he hq,
        prefix_update_independent_of_not_mem Q he hq]
    simp only [hpoint, Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fun,
      Fintype.card_fin, F₂, ZMod.card, Nat.cast_pow, Nat.cast_ofNat]

lemma score_column_average {A : Type*} [Fintype A] {L r ell : ℕ}
    (sets : A → Finset (Fin L)) (hsets : ∀ a, (sets a).card = r)
    (weights : A → ℚ) (he : ell < L) (Γ : BinaryMap r L) :
    (∑ x : Fin r → F₂, score sets weights (Function.update Γ ⟨ell,he⟩ x) (ell+1)) =
      (2:ℚ)^r * score sets weights Γ ell := by
  classical
  simp only [score]
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [← Finset.mul_sum, potential_column_average (sets a) (hsets a) he Γ]
  ring


/-- Fix the next physical column by the computed maximum of the actual score. -/
def columnStep {A : Type*} [Fintype A] {L r : ℕ}
    (sets : A → Finset (Fin L)) (weights : A → ℚ)
    (ell : ℕ) (Γ : BinaryMap r L) : BinaryMap r L :=
  if he : ell < L then
    let child := fun x => score sets weights (Function.update Γ ⟨ell,he⟩ x) (ell+1)
    Function.update Γ ⟨ell,he⟩ (selectColumn r child)
  else Γ

/-- Exactly L successive physical-column choices; no enumeration of all maps. -/
def buildMap {A : Type*} [Fintype A] {L r : ℕ}
    (sets : A → Finset (Fin L)) (weights : A → ℚ) : ℕ → BinaryMap r L
  | 0 => 0
  | n+1 => columnStep sets weights n (buildMap (r := r) sets weights n)

lemma columnStep_nondecreasing {A : Type*} [Fintype A] {L r ell : ℕ}
    (sets : A → Finset (Fin L)) (hsets : ∀ a, (sets a).card = r)
    (weights : A → ℚ) (he : ell < L) (Γ : BinaryMap r L) :
    score sets weights Γ ell ≤ score sets weights (columnStep sets weights ell Γ) (ell+1) := by
  unfold columnStep
  rw [dif_pos he]
  dsimp only
  exact selectColumn_ge_average r
    (fun x => score sets weights (Function.update Γ ⟨ell,he⟩ x) (ell+1))
    (score sets weights Γ ell) (score_column_average sets hsets weights he Γ).symm

lemma buildMap_nondecreasing {A : Type*} [Fintype A] {L r : ℕ}
    (sets : A → Finset (Fin L)) (hsets : ∀ a, (sets a).card = r)
    (weights : A → ℚ) (n : ℕ) (hn : n ≤ L) :
    score sets weights (0 : BinaryMap r L) 0 ≤
      score sets weights (buildMap (r := r) sets weights n) n := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    exact (ih (by omega)).trans
      (columnStep_nondecreasing sets hsets weights (by omega) (buildMap (r := r) sets weights n))

def constructMap {A : Type*} [Fintype A] {L r : ℕ}
    (sets : A → Finset (Fin L)) (weights : A → ℚ) : BinaryMap r L :=
  buildMap (r := r) sets weights L

/-- Uniform weighted construction guarantee, proved from the actual column code. -/
lemma constructMap_weighted {A : Type*} [Fintype A] {L r : ℕ}
    (sets : A → Finset (Fin L)) (hsets : ∀ a, (sets a).card = r)
    (weights : A → ℚ) :
    binarySuccess r * (∑ a, weights a) ≤
      ∑ a, weights a * potential (constructMap (r := r) sets weights) (sets a) L := by
  have h := buildMap_nondecreasing sets hsets weights L le_rfl
  rw [score_zero] at h
  exact h

def gammaMap (L m : ℕ) : BinaryMap m L :=
  constructMap (fun Q : Candidate L m => (Q : Finset (Fin L))) (fun _ => 1)

def gammaWeight (L m : ℕ) (Q : Candidate L m) : ℚ :=
  if restrictionTest (gammaMap L m) Q then 1 else 0

def deltaWith (L m : ℕ) (Γ : BinaryMap m L) : BinaryMap (L-m) L :=
  constructMap (fun Q : Candidate L m => ((Q : Finset (Fin L))ᶜ))
    (fun Q => if restrictionTest Γ Q then 1 else 0)

def deltaMap (L m : ℕ) : BinaryMap (L-m) L :=
  let Γ := gammaMap L m
  deltaWith L m Γ

/-- The program evaluates Γ once and captures it in the Δ pass. -/
def constructGoodMaps (L m : ℕ) : BinaryMap m L × BinaryMap (L-m) L :=
  let Γ := gammaMap L m
  (Γ, deltaWith L m Γ)

lemma candidate_size {L m : ℕ} (Q : Candidate L m) :
    (Q : Finset (Fin L)).card = m := (Finset.mem_powersetCard.mp Q.2).2

lemma candidate_compl_size {L m : ℕ} (Q : Candidate L m) :
    ((Q : Finset (Fin L))ᶜ).card = L-m := by
  rw [Finset.card_compl]
  simp [candidate_size Q]

lemma gammaWeight_eq_potential (L m : ℕ) (Q : Candidate L m) :
    gammaWeight L m Q = potential (gammaMap L m) Q L := by
  classical
  rw [potential_full _ _ (candidate_size Q)]
  simp only [gammaWeight, restrictionTest_correct]

lemma gamma_guarantee (L m : ℕ) :
    binarySuccess m * (Nat.choose L m : ℚ) ≤ ∑ Q, gammaWeight L m Q := by
  let sets := fun Q : Candidate L m => (Q : Finset (Fin L))
  have h := constructMap_weighted (r := m) sets
    (fun Q : Candidate L m => candidate_size Q) (fun _ => (1:ℚ))
  have hc : Fintype.card (Candidate L m) = Nat.choose L m := by
    simpa only [Nat.card_eq_fintype_card] using candidate_card L m
  have hr : (∑ Q : Candidate L m,
      (1:ℚ) * potential (constructMap (r := m) sets (fun _ => (1:ℚ))) (sets Q) L) =
      ∑ Q : Candidate L m, gammaWeight L m Q := by
    apply Finset.sum_congr rfl
    intro Q _
    rw [one_mul, gammaWeight_eq_potential]
    rfl
  rw [hr] at h
  simpa only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, hc, mul_one] using h

lemma delta_guarantee (L m : ℕ) :
    binarySuccess (L-m) * (∑ Q, gammaWeight L m Q) ≤
      ∑ Q : Candidate L m, gammaWeight L m Q *
        potential (deltaMap L m) ((Q : Finset (Fin L))ᶜ) L := by
  exact constructMap_weighted _ candidate_compl_size (gammaWeight L m)

/-- The actual constructed pair preserves the full initial expected count. -/
theorem constructed_pair_expected_count (L m : ℕ) :
    (binarySuccess m * binarySuccess (L-m)) * (Nat.choose L m : ℚ) ≤
      (Nat.card {Q : Candidate L m // Good (gammaMap L m) (deltaMap L m) Q} : ℚ) := by
  classical
  have hg := gamma_guarantee L m
  have hd := delta_guarantee L m
  have hμ : 0 ≤ binarySuccess (L-m) := le_of_lt (lt_trans (by norm_num) (binarySuccess_gt_quarter (L-m)))
  have hprod := mul_le_mul_of_nonneg_left hg hμ
  have hleft : (binarySuccess m * binarySuccess (L-m)) * (Nat.choose L m : ℚ) ≤
      ∑ Q : Candidate L m, gammaWeight L m Q *
        potential (deltaMap L m) ((Q : Finset (Fin L))ᶜ) L := by
    nlinarith [hd]
  convert hleft using 1
  simp only [gammaWeight, potential_full _ _ (candidate_compl_size _),
    restrictionTest_correct, Good, candidate_size, true_and]
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_eq_sum_ones,
    Finset.sum_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  apply Finset.sum_congr rfl
  intro Q _
  split_ifs <;> simp_all

/-- The executable Γ/Δ column schedule yields at least binom(L,m)/16 good sets. -/
theorem constructed_pair_good_count (L m : ℕ) :
    Nat.choose L m ≤ 16 * Nat.card
      {Q : Candidate L m // Good (gammaMap L m) (deltaMap L m) Q} := by
  have h := constructed_pair_expected_count L m
  have hμ := binarySuccess_gt_quarter m
  have hν := binarySuccess_gt_quarter (L-m)
  have hmul : (1/16:ℚ) ≤ binarySuccess m * binarySuccess (L-m) := by nlinarith
  have hn : (0:ℚ) ≤ Nat.choose L m := by positivity
  have hk := mul_le_mul_of_nonneg_right hmul hn
  have hout : (Nat.choose L m : ℚ) ≤ 16 *
      (Nat.card {Q : Candidate L m // Good (gammaMap L m) (deltaMap L m) Q} : ℚ) := by
    linarith
  exact_mod_cast hout


/-- The pair returned by the actual two-pass program has the claimed density. -/
theorem constructGoodMaps_correct (L m : ℕ) :
    Nat.choose L m ≤ 16 * Nat.card {Q : Candidate L m //
      Good (constructGoodMaps L m).1 (constructGoodMaps L m).2 Q} :=
  constructed_pair_good_count L m

/-- Potential evaluations in one actual column pass: all candidate columns,
all subsets, and all binary coefficients of the newly restricted frame.
`extra` charges evaluation of the fixed Γ weight in the Δ pass. -/
def columnKernelSites {A : Type*} [Fintype A] {L r : ℕ}
    (sets : A → Finset (Fin L)) (extra ell : ℕ) : ℕ :=
  2^r * ∑ a, (2^((prefixSet (sets a) (ell+1)).card) + extra)

/-- Instrument the same physical-column schedule as buildMap. -/
def buildKernelSites {A : Type*} [Fintype A] {L r : ℕ}
    (sets : A → Finset (Fin L)) (extra : ℕ) : ℕ → ℕ
  | 0 => 0
  | n+1 => buildKernelSites (r := r) sets extra n +
      if n < L then columnKernelSites (r := r) sets extra n else 0

lemma columnKernelSites_bound {A : Type*} [Fintype A] {L r : ℕ}
    (sets : A → Finset (Fin L)) (hsets : ∀ a, (sets a).card = r)
    (extra ell : ℕ) :
    columnKernelSites (r := r) sets extra ell ≤
      2^r * Fintype.card A * (2^r+extra) := by
  have hsum : (∑ a, (2^((prefixSet (sets a) (ell+1)).card)+extra)) ≤
      Fintype.card A * (2^r+extra) := by
    calc
      _ ≤ ∑ _a : A, (2^r+extra) := by
        apply Finset.sum_le_sum
        intro a _
        have hc : (prefixSet (sets a) (ell+1)).card ≤ r := by
          rw [← hsets a]
          exact Finset.card_le_card (prefixSet_subset (sets a) (ell+1))
        exact Nat.add_le_add_right (Nat.pow_le_pow_right (by omega) hc) extra
      _ = _ := by simp
  exact (Nat.mul_le_mul_left (2^r) hsum).trans_eq (by ring)

lemma buildKernelSites_bound {A : Type*} [Fintype A] {L r : ℕ}
    (sets : A → Finset (Fin L)) (hsets : ∀ a, (sets a).card = r)
    (extra n : ℕ) (hn : n ≤ L) :
    buildKernelSites (r := r) sets extra n ≤
      n * (2^r * Fintype.card A * (2^r+extra)) := by
  induction n with
  | zero => simp [buildKernelSites]
  | succ n ih =>
    rw [buildKernelSites, if_pos (show n<L by omega)]
    have h := Nat.add_le_add (ih (by omega)) (columnKernelSites_bound sets hsets extra n)
    exact h.trans_eq (by ring)

/-- Γ is captured once; only its finite LI weight is re-tested in Δ scores. -/
def constructionKernelSites (L m : ℕ) : ℕ :=
  buildKernelSites (r := m)
    (fun Q : Candidate L m => (Q : Finset (Fin L))) 0 L +
  buildKernelSites (r := L-m)
    (fun Q : Candidate L m => ((Q : Finset (Fin L))ᶜ)) (2^m) L

lemma binary_square (r : ℕ) : 2^r * 2^r = 4^r := by
  rw [← mul_pow]
  norm_num

lemma binary_cross_bound (m k : ℕ) : 2^(m+k) ≤ 4^m+4^k := by
  rw [pow_add]
  by_cases h : 2^m ≤ 2^k
  · calc
      2^m * 2^k ≤ 2^k * 2^k := Nat.mul_le_mul_right _ h
      _ = 4^k := binary_square k
      _ ≤ _ := Nat.le_add_left _ _
  · have h' : 2^k ≤ 2^m := le_of_not_ge h
    calc
      2^m * 2^k ≤ 2^m * 2^m := Nat.mul_le_mul_left _ h'
      _ = 4^m := binary_square m
      _ ≤ _ := Nat.le_add_right _ _

lemma constructionKernelSites_bound (L m : ℕ) :
    constructionKernelSites L m ≤ 2 * Nat.card (RankWorksites L m) := by
  have hg := buildKernelSites_bound (r := m)
    (fun Q : Candidate L m => (Q : Finset (Fin L))) candidate_size 0 L le_rfl
  have hd := buildKernelSites_bound (r := L-m)
    (fun Q : Candidate L m => ((Q : Finset (Fin L))ᶜ)) candidate_compl_size (2^m) L le_rfl
  have hc : Fintype.card (Candidate L m) = Nat.choose L m := by
    simpa only [Nat.card_eq_fintype_card] using candidate_card L m
  rw [hc] at hg hd
  calc
    constructionKernelSites L m ≤
        L*(2^m * Nat.choose L m * (2^m+0)) +
        L*(2^(L-m) * Nat.choose L m * (2^(L-m)+2^m)) := Nat.add_le_add hg hd
    _ = L*Nat.choose L m * ((2^m*2^m)+(2^(L-m)*2^(L-m))+(2^m*2^(L-m))) := by ring
    _ = L*Nat.choose L m * (4^m+4^(L-m)+2^(m+(L-m))) := by
      rw [binary_square, binary_square, pow_add]
    _ ≤ L*Nat.choose L m * (2*(4^m+4^(L-m))) := by
      exact Nat.mul_le_mul_left _ (by have h := binary_cross_bound m (L-m); omega)
    _ = 2 * Nat.card (RankWorksites L m) := by rw [rank_worksite_card]; ring

/-- Finite kernel-test visits of the actual uniform construction fit formation.
Comparisons, vector sums and exact rational arithmetic add polynomial(L) work.
The counter charges full coefficient enumeration even when a test stops early. -/
theorem constructionKernelSites_fit (L m N : ℕ) (hm : m ≤ L)
    (hN : Nat.choose L m * 4^(L-m) ≤ N) :
    constructionKernelSites L m ≤ 4*L*N*4^m := by
  exact (constructionKernelSites_bound L m).trans
    ((Nat.mul_le_mul_left 2 (rank_worksites_fit L m N hm hN)).trans_eq (by ring))

#print axioms constructGoodMaps
#print axioms constructGoodMaps_correct
#print axioms constructed_pair_expected_count
#print axioms potential_column_average
#print axioms selectColumn_score_calls
#print axioms constructionKernelSites_bound
#print axioms constructionKernelSites_fit

end ThinMatrix.GoodSetConstruction
