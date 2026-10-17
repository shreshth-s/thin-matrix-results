import Mathlib

/-!
# Binary good-set construction: finite interfaces

Binary matrices are represented by their columns. `Good` is the actual
restricted-column independence predicate; no independence between different
subsets is assumed. This file separates finite averaging from the rank-count
and computational-cost obligations.
-/
namespace ThinMatrix.GoodSets

open scoped BigOperators

abbrev F₂ := ZMod 2
abbrev BinaryMap (rows cols : ℕ) := Fin cols → (Fin rows → F₂)

def Good {L m : ℕ} (Γ : BinaryMap m L) (Δ : BinaryMap (L-m) L)
    (Q : Finset (Fin L)) : Prop :=
  Q.card = m ∧ LinearIndependent F₂ (fun i : Q => Γ i) ∧
    LinearIndependent F₂ (fun i : (Qᶜ : Finset (Fin L)) => Δ i)

/-- The exact number of candidate m-subsets, without any randomness. -/
theorem subset_count (L m : ℕ) :
    (Finset.univ.powersetCard m : Finset (Finset (Fin L))).card = Nat.choose L m := by
  simp

/-- The finite averaging step does not need independent events across Q. -/
theorem finite_averaging {Ω A : Type*} [Fintype Ω] [Nonempty Ω]
    [Fintype A] (R : Ω → A → Prop) [DecidableRel R]
    (h : ∀ a, Fintype.card Ω ≤ 16 * Fintype.card {ω // R ω a}) :
    ∃ ω, Fintype.card A ≤ 16 * Fintype.card {a // R ω a} := by
  classical
  let count : Ω → ℕ := fun ω => Fintype.card {a // R ω a}
  have swap : (∑ ω, count ω) = ∑ a, Fintype.card {ω // R ω a} := by
    simp only [count, Fintype.card_subtype, Finset.card_eq_sum_ones, Finset.sum_filter]
    exact Finset.sum_comm
  have total : Fintype.card Ω * Fintype.card A ≤ 16 * ∑ ω, count ω := by
    calc
      Fintype.card Ω * Fintype.card A = ∑ _ : A, Fintype.card Ω := by simp [mul_comm]
      _ ≤ ∑ a : A, 16 * Fintype.card {ω // R ω a} := Finset.sum_le_sum (fun a _ => h a)
      _ = 16 * ∑ ω, count ω := by rw [← Finset.mul_sum, ← swap]
  by_contra hn
  push Not at hn
  have strict : 16 * ∑ ω, count ω < Fintype.card Ω * Fintype.card A := by
    calc
      16 * ∑ ω, count ω = ∑ ω, 16 * count ω := by rw [Finset.mul_sum]
      _ < ∑ _ : Ω, Fintype.card A := by
        apply Finset.sum_lt_sum_of_nonempty (Finset.univ_nonempty)
        intro ω _
        exact hn ω
      _ = Fintype.card Ω * Fintype.card A := by simp
  omega

/-- One exact conditional-expectation decision: a nondecreasing child exists. -/
theorem choose_binary_child (left right parent : ℚ)
    (h : parent = (left + right) / 2) : parent ≤ left ∨ parent ≤ right := by
  by_contra hn
  push Not at hn
  linarith

/-- Repeated exact conditional decisions preserve the initial expectation.
This theorem concerns the invariant, not a rank-computation running time. -/
theorem conditional_expectation_path (score : List Bool → ℚ) (n : ℕ)
    (average : ∀ s, s.length < n →
      score s = (score (s ++ [false]) + score (s ++ [true])) / 2) :
    ∃ s, s.length = n ∧ score [] ≤ score s := by
  suffices step : ∀ k, k ≤ n → ∃ s, s.length = k ∧ score [] ≤ score s by
    exact step n le_rfl
  intro k hk
  induction k with
  | zero => exact ⟨[], rfl, le_rfl⟩
  | succ k ih =>
    obtain ⟨s, hs, hscore⟩ := ih (by omega)
    have hlen : s.length < n := by omega
    rcases choose_binary_child _ _ _ (average s hlen) with hleft | hright
    · exact ⟨s ++ [false], by simp [hs], hscore.trans hleft⟩
    · exact ⟨s ++ [true], by simp [hs], hscore.trans hright⟩

/-- Mathlib's exact finite-field general-linear-group count, specialized to F₂. -/
theorem binary_GL_card (r : ℕ) :
    Nat.card (GL (Fin r) F₂) =
      ∏ i : Fin r, (2^r - 2^(i : ℕ)) := by
  simpa [F₂] using (Matrix.card_GL_field (𝔽 := ZMod 2) r)


/-- Restricting a function to a subset and its complement is a bijection. -/
def restrictionEquiv {I V : Type*} (p : I → Prop) [DecidablePred p] :
    (I → V) ≃ ({i // p i} → V) × ({i // ¬p i} → V) :=
  Equiv.piEquivPiSubtypeProd p (fun _ => V)

/-- Predicate on the first component: the unused columns are genuinely free. -/
def subtypeFirstEquiv {A B : Type*} (p : A → Prop) :
    {ab : A × B // p ab.1} ≃ {a : A // p a} × B where
  toFun ab := (⟨ab.1.1, ab.2⟩, ab.1.2)
  invFun ab := ⟨(ab.1.1, ab.2), ab.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Exact extension count for any column predicate. -/
theorem restriction_count {I V : Type*} [Fintype I] [Fintype V] [DecidableEq I]
    (p : I → Prop) [DecidablePred p]
    (C : ({i // p i} → V) → Prop) [DecidablePred C] :
    Fintype.card {f : I → V // C (fun i => f i)} =
      Fintype.card {f : {i // p i} → V // C f} *
        Fintype.card V ^ Fintype.card {i // ¬p i} := by
  classical
  let e := (restrictionEquiv (V := V) p).subtypeEquiv
    (p := fun f : I → V => C (fun i => f i))
    (q := fun fg : ({i // p i} → V) × ({i // ¬p i} → V) => C fg.1)
    (fun _ => Iff.rfl)
  calc
    _ = Fintype.card {fg : ({i // p i} → V) × ({i // ¬p i} → V) // C fg.1} :=
      Fintype.card_congr e
    _ = Fintype.card ({f : {i // p i} → V // C f} × ({i // ¬p i} → V)) :=
      Fintype.card_congr (subtypeFirstEquiv C)
    _ = _ := by simp

/-- Reindexing columns by an equivalence preserves linear independence. -/
theorem independent_count {I : Type*} [Fintype I] (r : ℕ)
    (hi : Fintype.card I = r) :
    Nat.card {f : I → (Fin r → F₂) // LinearIndependent F₂ f} =
      ∏ j : Fin r, (2^r - 2^(j : ℕ)) := by
  classical
  let e : I ≃ Fin r := Fintype.equivFinOfCardEq hi
  let a := Equiv.arrowCongr e (Equiv.refl (Fin r → F₂))
  have he (f : I → (Fin r → F₂)) :
      LinearIndependent F₂ f ↔ LinearIndependent F₂ (a f) := by
    exact (linearIndependent_equiv e.symm).symm
  rw [Nat.card_congr (a.subtypeEquiv (q := fun f : Fin r → (Fin r → F₂) => LinearIndependent F₂ f) he)]
  simpa [F₂, Module.finrank_fintype_fun_eq_card] using
    (card_linearIndependent (K := F₂) (V := Fin r → F₂) (k := r) (by simp))


/-- Uniform extensions of any square restriction have the same exact count. -/
theorem restricted_independent_count (L r : ℕ) (Q : Finset (Fin L))
    (hQ : Q.card = r) :
    Nat.card {f : BinaryMap r L // LinearIndependent F₂ (fun i : Q => f i)} =
      (∏ j : Fin r, (2^r - 2^(j : ℕ))) * 2^(r*(L-r)) := by
  classical
  rw [Nat.card_eq_fintype_card]
  rw [restriction_count (fun i : Fin L => i ∈ Q)
    (fun f => LinearIndependent F₂ f)]
  have hi : Fintype.card Q = r := by simpa using hQ
  have hc := independent_count (I := Q) r hi
  rw [Nat.card_eq_fintype_card] at hc
  have hfirst : Fintype.card {f : {i : Fin L // i ∈ Q} → (Fin r → F₂) //
      LinearIndependent F₂ f} = ∏ j : Fin r, (2^r - 2^(j : ℕ)) := by
    simpa using hc
  simp only [← Nat.card_eq_fintype_card] at hfirst ⊢
  rw [hfirst]
  have hcompl : Fintype.card {i : Fin L // i ∉ Q} = L-r := by
    rw [Fintype.card_subtype_compl]
    simp [hQ]
  simp only [← Nat.card_eq_fintype_card] at hcompl
  simp [hQ, F₂, ← pow_mul]


/-- Invertibility probability of a uniform square binary matrix. -/
def binarySuccess (n : ℕ) : ℚ :=
  ∏ i ∈ Finset.range n, (1 - (1/2 : ℚ)^(i+1))

lemma binarySuccess_succ (n : ℕ) : binarySuccess (n+1) =
    binarySuccess n * (1-(1/2:ℚ)^(n+1)) := by
  simp [binarySuccess, Finset.prod_range_succ]

/-- A uniform, strict bound; no numerical approximation to the infinite product. -/
theorem binarySuccess_lower (n : ℕ) :
    (1/4:ℚ)+(1/2:ℚ)^(n+2) ≤ binarySuccess (n+1) := by
  induction n with
  | zero => norm_num [binarySuccess]
  | succ n ih =>
    rw [binarySuccess_succ]
    have ha : 0 ≤ (1/2:ℚ)^(n+2) := by positivity
    have hb : (1/2:ℚ)^(n+2) ≤ 1/4 := by
      calc
        (1/2:ℚ)^(n+2) = (1/2:ℚ)^n * (1/4) := by rw [pow_add]; norm_num
        _ ≤ 1 * (1/4:ℚ) := mul_le_mul_of_nonneg_right (pow_le_one₀ (by norm_num) (by norm_num)) (by norm_num)
        _ = _ := by norm_num
    have hm := mul_le_mul_of_nonneg_right ih (show 0 ≤ 1-(1/2:ℚ)^(n+2) by linarith)
    rw [show n+1+2 = (n+2)+1 by omega, pow_succ]
    nlinarith

theorem binarySuccess_gt_quarter (n : ℕ) : (1/4:ℚ) < binarySuccess n := by
  cases n with
  | zero => norm_num [binarySuccess]
  | succ n =>
    have h := binarySuccess_lower n
    have hp : (0:ℚ) < (1/2:ℚ)^(n+2) := by positivity
    linarith


lemma binary_factor (r i : ℕ) (hi : i < r) :
    ((2^r - 2^i : ℕ) : ℚ) = (2:ℚ)^r * (1-(1/2:ℚ)^(r-i)) := by
  rw [Nat.cast_sub (Nat.pow_le_pow_right (by omega) (Nat.le_of_lt hi))]
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  have hp : (2:ℚ)^r = (2:ℚ)^i * (2:ℚ)^(r-i) := by
    rw [← pow_add, Nat.add_sub_of_le (Nat.le_of_lt hi)]
  rw [div_pow]
  simp only [one_pow]
  field_simp
  nlinarith [hp]

/-- Exact normalization of the finite-field GL count. -/
theorem binary_GL_normalization (r : ℕ) :
    ((Nat.card (GL (Fin r) F₂) : ℕ) : ℚ) =
      (2:ℚ)^(r*r) * binarySuccess r := by
  rw [binary_GL_card, Nat.cast_prod]
  change (∏ i : Fin r, (fun j : ℕ => ((2^r-2^j:ℕ):ℚ)) i) = _
  rw [Fin.prod_univ_eq_prod_range (fun j : ℕ => ((2^r-2^j:ℕ):ℚ)) r]
  have hf : (∏ i ∈ Finset.range r, ((2^r-2^i:ℕ):ℚ)) =
      ∏ i ∈ Finset.range r, ((2:ℚ)^r * (1-(1/2:ℚ)^(r-i))) := by
    apply Finset.prod_congr rfl
    intro i hi
    exact binary_factor r i (Finset.mem_range.mp hi)
  rw [hf, Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_range, ← pow_mul]
  congr 1
  unfold binarySuccess
  rw [← Finset.prod_range_reflect (fun i => 1-(1/2:ℚ)^(i+1)) r]
  apply Finset.prod_congr rfl
  intro i hi
  have hir : i < r := Finset.mem_range.mp hi
  congr 2
  omega


/-- Good Γ and Δ restrictions are independent because the two maps are separate
finite choices; no independence among the different Q is involved. -/
def goodPairEquiv {L m : ℕ} (Q : Finset (Fin L)) (hQ : Q.card = m) :
    {gd : BinaryMap m L × BinaryMap (L-m) L // Good gd.1 gd.2 Q} ≃
      {g : BinaryMap m L // LinearIndependent F₂ (fun i : Q => g i)} ×
      {d : BinaryMap (L-m) L // LinearIndependent F₂
        (fun i : (Qᶜ : Finset (Fin L)) => d i)} where
  toFun gd := (⟨gd.1.1, gd.2.2.1⟩, ⟨gd.1.2, gd.2.2.2⟩)
  invFun gd := ⟨(gd.1.1, gd.2.1), hQ, gd.1.2, gd.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem good_pair_count (L m : ℕ) (hm : m ≤ L)
    (Q : Finset (Fin L)) (hQ : Q.card = m) :
    Nat.card {gd : BinaryMap m L × BinaryMap (L-m) L // Good gd.1 gd.2 Q} =
      (Nat.card (GL (Fin m) F₂) * 2^(m*(L-m))) *
      (Nat.card (GL (Fin (L-m)) F₂) * 2^((L-m)*m)) := by
  rw [Nat.card_congr (goodPairEquiv Q hQ), Nat.card_prod]
  rw [restricted_independent_count L m Q hQ]
  have hc : (Qᶜ : Finset (Fin L)).card = L-m := by
    rw [Finset.card_compl]
    simp [hQ]
  rw [restricted_independent_count L (L-m) Qᶜ hc]
  rw [binary_GL_card, binary_GL_card]
  rw [show L-(L-m) = m by omega]


theorem binary_map_pair_card (L m : ℕ) (hm : m ≤ L) :
    Nat.card (BinaryMap m L × BinaryMap (L-m) L) = 2^(L*L) := by
  simp only [BinaryMap, Nat.card_prod, Nat.card_fun, Nat.card_fin, Nat.card_zmod,
    ← pow_mul, ← pow_add]
  congr 1
  have he : m+(L-m)=L := Nat.add_sub_of_le hm
  nlinarith [congrArg (fun x => x*L) he]

/-- The exact marginal probability at any fixed m-subset. -/
theorem good_pair_probability (L m : ℕ) (hm : m ≤ L)
    (Q : Finset (Fin L)) (hQ : Q.card = m) :
    ((Nat.card {gd : BinaryMap m L × BinaryMap (L-m) L // Good gd.1 gd.2 Q} : ℕ) : ℚ) =
      (2:ℚ)^(L*L) * (binarySuccess m * binarySuccess (L-m)) := by
  rw [good_pair_count L m hm Q hQ]
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, binary_GL_normalization]
  calc
    _ = ((2:ℚ)^(m*m) * (2:ℚ)^(m*(L-m)) *
        (2:ℚ)^((L-m)*(L-m)) * (2:ℚ)^((L-m)*m)) *
          (binarySuccess m * binarySuccess (L-m)) := by ring
    _ = _ := by
      rw [← pow_add, ← pow_add, ← pow_add]
      congr 2
      have he : m+(L-m)=L := Nat.add_sub_of_le hm
      nlinarith [sq_nonneg (m+(L-m)-L : ℤ)]


abbrev Candidate (L m : ℕ) :=
  ↥(Finset.univ.powersetCard m : Finset (Finset (Fin L)))

theorem candidate_card (L m : ℕ) : Nat.card (Candidate L m) = Nat.choose L m := by
  simp [Candidate]

/-- Unconditional good-set existence, with a fully proved constant density.
The integer inequality is equivalent to at least binom(L,m)/16 good sets. -/
theorem exists_good_maps (L m : ℕ) (hm : m ≤ L) :
    ∃ (Γ : BinaryMap m L) (Δ : BinaryMap (L-m) L),
      Nat.choose L m ≤ 16 * Nat.card {Q : Candidate L m // Good Γ Δ Q} := by
  classical
  let Ω := BinaryMap m L × BinaryMap (L-m) L
  have marginal (Q : Candidate L m) :
      Fintype.card Ω ≤ 16 * Fintype.card {gd : Ω // Good gd.1 gd.2 Q} := by
    have hQ : (Q : Finset (Fin L)).card = m :=
      (Finset.mem_powersetCard.mp Q.2).2
    have hprob := good_pair_probability L m hm Q hQ
    have hμ := binarySuccess_gt_quarter m
    have hν := binarySuccess_gt_quarter (L-m)
    have hmul : (1/16:ℚ) < binarySuccess m * binarySuccess (L-m) := by
      nlinarith
    have hpos : (0:ℚ) < (2:ℚ)^(L*L) := by positivity
    have hcast : (Nat.card Ω : ℚ) ≤
        16 * (Nat.card {gd : Ω // Good gd.1 gd.2 Q} : ℚ) := by
      change (Nat.card (BinaryMap m L × BinaryMap (L-m) L) : ℚ) ≤ _
      rw [binary_map_pair_card L m hm, hprob]
      simp only [Nat.cast_pow, Nat.cast_ofNat]
      nlinarith
    have hnat : Nat.card Ω ≤ 16 * Nat.card {gd : Ω // Good gd.1 gd.2 Q} := by
      exact_mod_cast hcast
    simpa only [Nat.card_eq_fintype_card] using hnat
  obtain ⟨gd, hg⟩ := finite_averaging
    (fun (gd : Ω) (Q : Candidate L m) => Good gd.1 gd.2 Q) marginal
  refine ⟨gd.1, gd.2, ?_⟩
  have hc := candidate_card L m
  rw [Nat.card_eq_fintype_card] at hc
  rw [← hc]
  simpa only [Nat.card_eq_fintype_card] using hg


/-- A constructive finite independence test needs only all binary coefficient
vectors, rather than a separately formalized elimination routine. -/
theorem independent_iff_zero_test {r m : ℕ} (v : Fin r → (Fin m → F₂)) :
    LinearIndependent F₂ v ↔
      ∀ c : Fin r → F₂, (∑ i, c i • v i) = 0 → c = 0 := by
  rw [linearIndependent_iff_injective_fintypeLinearCombination,
    ← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  simp only [Fintype.linearCombination_apply]

/-- One column-candidate/coefficient-test site for each subset and level.
Vector sums, rational arithmetic, and comparisons cost an additional polynomial
in L; this declaration counts the finite loops only. -/
abbrev RankWorksites (L m : ℕ) := Candidate L m × Fin L ×
  (((Fin m → F₂) × (Fin m → F₂)) ⊕
   ((Fin (L-m) → F₂) × (Fin (L-m) → F₂)))

theorem rank_worksite_card (L m : ℕ) :
    Nat.card (RankWorksites L m) =
      Nat.choose L m * L * (4^m + 4^(L-m)) := by
  simp only [RankWorksites, Nat.card_prod, Nat.card_sum, Nat.card_fun,
    Nat.card_fin, Nat.card_zmod, candidate_card]
  have hpow (r : ℕ) : 2^r * 2^r = 4^r := by
    rw [← mul_pow]
    norm_num
  rw [hpow, hpow]
  ring

/-- The brute-force rank-test loop still fits the original formation budget.
This is a finite loop-count theorem, not a RAM semantics or bit-cost theorem. -/
theorem rank_worksites_fit (L m N : ℕ) (hm : m ≤ L)
    (hN : Nat.choose L m * 4^(L-m) ≤ N) :
    Nat.card (RankWorksites L m) ≤ 2*L*N*4^m := by
  rw [rank_worksite_card]
  have hmPow : 4^m ≤ 4^L := Nat.pow_le_pow_right (by omega) hm
  have hkPow : 4^(L-m) ≤ 4^L := Nat.pow_le_pow_right (by omega) (Nat.sub_le ..)
  have hs : 4^m + 4^(L-m) ≤ 2*4^L := by omega
  have hf : Nat.choose L m * 4^L ≤ N*4^m := by
    calc
      Nat.choose L m * 4^L = (Nat.choose L m * 4^(L-m))*4^m := by
        rw [mul_assoc, ← pow_add, Nat.sub_add_cancel hm]
      _ ≤ _ := Nat.mul_le_mul_right _ hN
  calc
    Nat.choose L m * L * (4^m+4^(L-m)) ≤
        Nat.choose L m * L * (2*4^L) := Nat.mul_le_mul_left _ hs
    _ = (2*L)*(Nat.choose L m * 4^L) := by ring
    _ ≤ (2*L)*(N*4^m) := Nat.mul_le_mul_left _ hf
    _ = _ := by ring


/-- Exact number of columns that extend a fixed independent r-frame.
This is the rank-count step used by conditional expectations. -/
theorem independent_extension_count (m r : ℕ) (v : Fin r → (Fin m → F₂))
    (hv : LinearIndependent F₂ v) :
    Nat.card {x : Fin m → F₂ // LinearIndependent F₂ (Fin.snoc v x)} =
      2^m - 2^r := by
  classical
  let S : Set (Fin m → F₂) := Submodule.span F₂ (Set.range v)
  have he : {x : Fin m → F₂ // LinearIndependent F₂ (Fin.snoc v x)} ≃
      {x : Fin m → F₂ // x ∉ S} :=
    (Equiv.refl _).subtypeEquiv (fun x => by
      simpa [S, hv] using (linearIndependent_finSnoc (K := F₂) (v := v) (x := x)))
  rw [Nat.card_congr he]
  change Nat.card (Sᶜ : Set (Fin m → F₂)) = _
  rw [Nat.card_eq_fintype_card, Fintype.card_compl_set]
  have hc : Fintype.card S = 2^r := by
    change Fintype.card (Submodule.span F₂ (Set.range v)) = _
    rw [Module.card_eq_pow_finrank (K := F₂), finrank_span_eq_card hv]
    simp [F₂]
  rw [hc]
  simp [F₂]


noncomputable def framePotential (m r : ℕ) (v : Fin r → (Fin m → F₂)) : ℚ := by
  classical
  exact if LinearIndependent F₂ v then binarySuccess (m-r) else 0

/-- The actual conditional-rank potential has the required child-average.
All 2^m possible next columns are included. -/
theorem framePotential_average (m r : ℕ) (hr : r < m)
    (v : Fin r → (Fin m → F₂)) :
    (∑ x : Fin m → F₂, framePotential m (r+1) (Fin.snoc v x)) =
      (2:ℚ)^m * framePotential m r v := by
  classical
  by_cases hv : LinearIndependent F₂ v
  · have hsum : (∑ x : Fin m → F₂, framePotential m (r+1) (Fin.snoc v x)) =
        (Nat.card {x : Fin m → F₂ // LinearIndependent F₂ (Fin.snoc v x)} : ℚ) *
          binarySuccess (m-(r+1)) := by
      simp only [framePotential, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul,
        Nat.card_eq_fintype_card, Fintype.card_subtype]
    rw [hsum, independent_extension_count m r v hv, binary_factor m r hr,
      framePotential, if_pos hv]
    have hk : m-r = (m-(r+1))+1 := by omega
    rw [hk, binarySuccess_succ]
    ring
  · have hnone (x : Fin m → F₂) : ¬ LinearIndependent F₂ (Fin.snoc v x) := by
      simp only [linearIndependent_finSnoc, hv, false_and, not_false_eq_true]
    simp [framePotential, hv, hnone]

/-- A deterministic conditional decision among every column value. -/
theorem choose_finite_child {A : Type*} [Fintype A] [Nonempty A]
    (children : A → ℚ) (parent : ℚ)
    (h : (Fintype.card A : ℚ)*parent = ∑ a, children a) :
    ∃ a, parent ≤ children a := by
  obtain ⟨a, _, ha⟩ := Finset.exists_le_of_sum_le
    (s := Finset.univ) (f := fun _ : A => parent) (g := children)
    Finset.univ_nonempty (by simpa using le_of_eq h)
  exact ⟨a, ha⟩

/-- The conditional-rank rule always offers a nondecreasing column. -/
theorem framePotential_choose (m r : ℕ) (hr : r < m)
    (v : Fin r → (Fin m → F₂)) :
    ∃ x, framePotential m r v ≤ framePotential m (r+1) (Fin.snoc v x) := by
  apply choose_finite_child
  simpa [F₂] using (framePotential_average m r hr v).symm


/-- Executable finite zero-kernel test (2^r coefficient vectors). -/
def independenceTest {m r : ℕ} (v : Fin r → (Fin m → F₂)) : Bool :=
  decide (∀ c : Fin r → F₂, (∑ i, c i • v i) = 0 → c = 0)

theorem independenceTest_correct {m r : ℕ} (v : Fin r → (Fin m → F₂)) :
    independenceTest v = true ↔ LinearIndependent F₂ v := by
  simp only [independenceTest, decide_eq_true_eq]
  exact (independent_iff_zero_test v).symm

/-- Executable potential evaluation, with no rank oracle assumed. -/
def computableFramePotential (m r : ℕ) (v : Fin r → (Fin m → F₂)) : ℚ :=
  if independenceTest v then binarySuccess (m-r) else 0

theorem computableFramePotential_eq (m r : ℕ) (v : Fin r → (Fin m → F₂)) :
    computableFramePotential m r v = framePotential m r v := by
  classical
  unfold computableFramePotential framePotential
  simp only [independenceTest_correct]

/-- One common column can be chosen for an arbitrary family of subset frames.
Each component carries its actual rank potential; the average is proved,
rather than assumed. `affected` records which subsets contain this column. -/
theorem common_column_choose {A : Type*} [Fintype A] (m : ℕ)
    (r : A → ℕ) (v : ∀ a, Fin (r a) → (Fin m → F₂))
    (affected : A → Bool) (hr : ∀ a, affected a = true → r a < m) :
    ∃ x : Fin m → F₂,
      (∑ a, framePotential m (r a) (v a)) ≤
        ∑ a, if affected a then framePotential m (r a+1) (Fin.snoc (v a) x)
          else framePotential m (r a) (v a) := by
  classical
  apply choose_finite_child
  simp only [Fintype.card_fun, Fintype.card_fin, F₂, ZMod.card, Nat.cast_pow,
    Nat.cast_ofNat]
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  cases ha : affected a with
  | false => simp
  | true => simpa only [ha, Bool.true_eq, ite_true] using
      (framePotential_average m (r a) (hr a ha) (v a)).symm

/-!
## Remaining construction obligations

`exists_good_maps` is unconditional. The actual one-column rank-potential
average and a common nondecreasing column are proved, and the finite brute-force
rank-test worksite count fits `2 L N D` under the original tile condition.
The global prefix-index schedule that assembles those column choices into Γ
and Δ, and a machine-level execution/bit-cost proof for that schedule, are not
formalized here. `conditional_expectation_path` is a generic invariant;
`common_column_choose` is the proved rank-potential step that would instantiate
it. Neither declaration silently assumes a good-set density or a rank oracle.
-/

#print axioms exists_good_maps
#print axioms binarySuccess_gt_quarter
#print axioms good_pair_probability
#print axioms conditional_expectation_path
#print axioms framePotential_average
#print axioms common_column_choose
#print axioms independenceTest_correct
#print axioms rank_worksites_fit

end ThinMatrix.GoodSets
