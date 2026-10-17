import ThreeSumApsp.Lang.Lib.Pass
import ThreeSumApsp.Lang.Tactics

namespace Light.DenseMarkPass

abbrev Len : ℕ := 0
abbrev Pairs : ℕ := 1
abbrev Active : ℕ := 2
abbrev Yes : ℕ := 3
abbrev Pair : ℕ := 4
abbrev Mark : ℕ := 5
abbrev Idx : ℕ := 6

def roundBody : Stmt :=
  .ite (M (v Active +' v Idx) =' k 1)
    (.ite (M (v Yes +' v Idx) =' k 1)
      (.store (v Mark +' M (v Pair +' v Idx)) (k 1))
      .skip)
    .skip

def body : Stmt := .for Idx (v Len) roundBody

def bit (b : Bool) : ℤ := if b then 1 else 0

@[simp] theorem bit_eq_one (b : Bool) : bit b = 1 ↔ b = true := by
  cases b <;> simp [bit]

def Qualifies (active yes : ℕ → Bool) (i : ℕ) : Prop :=
  active i = true ∧ yes i = true

instance (active yes : ℕ → Bool) (i : ℕ) : Decidable (Qualifies active yes i) := by
  unfold Qualifies
  infer_instance

noncomputable def markPrefix (μ : ℕ → ℤ) (active yes : ℕ → Bool)
    (pair : ℕ → ℕ) (mark j : ℕ) : ℕ → ℤ := by
  classical
  exact fun a => if ∃ i, i < j ∧ Qualifies active yes i ∧ mark + pair i = a
    then 1 else μ a

theorem markPrefix_zero (μ : ℕ → ℤ) (active yes : ℕ → Bool)
    (pair : ℕ → ℕ) (mark : ℕ) : markPrefix μ active yes pair mark 0 = μ := by
  classical
  funext a
  simp [markPrefix]

theorem markPrefix_succ (μ : ℕ → ℤ) (active yes : ℕ → Bool)
    (pair : ℕ → ℕ) (mark j : ℕ) :
    markPrefix μ active yes pair mark (j + 1) =
      if Qualifies active yes j then
        Function.update (markPrefix μ active yes pair mark j) (mark + pair j) 1
      else markPrefix μ active yes pair mark j := by
  classical
  funext a
  have hex : (∃ i, i < j + 1 ∧ Qualifies active yes i ∧ mark + pair i = a) ↔
      (∃ i, i < j ∧ Qualifies active yes i ∧ mark + pair i = a) ∨
        (Qualifies active yes j ∧ mark + pair j = a) := by
    constructor
    · rintro ⟨i, hi, hq, hp⟩
      by_cases hij : i < j
      · exact Or.inl ⟨i, hij, hq, hp⟩
      · have : i = j := by omega
        subst i
        exact Or.inr ⟨hq, hp⟩
    · rintro (⟨i, hi, hq, hp⟩ | ⟨hq, hp⟩)
      · exact ⟨i, by omega, hq, hp⟩
      · exact ⟨j, by omega, hq, hp⟩
  by_cases hq : Qualifies active yes j
  · rw [if_pos hq]
    simp only [markPrefix]
    simp only [hex]
    by_cases ha : a = mark + pair j
    · simp [ha, hq]
    · have ha' : mark + pair j ≠ a := Ne.symm ha
      simp only [hq, ha', and_false, or_false, Function.update_apply, ha, if_false, markPrefix]
  · rw [if_neg hq]
    simp only [markPrefix]
    simp only [hex]
    simp only [hq, false_and, or_false]

theorem markPrefix_outside {μ : ℕ → ℤ} {active yes : ℕ → Bool}
    {pair : ℕ → ℕ} {mark j I Q : ℕ}
    (hj : j ≤ I) (hp : ∀ i < I, pair i < Q) :
    SameOutside μ (markPrefix μ active yes pair mark j) mark Q := by
  classical
  intro a ha
  have hn : ¬ ∃ i, i < j ∧ Qualifies active yes i ∧ mark + pair i = a := by
    rintro ⟨i, hi, _, rfl⟩
    have := hp i (by omega)
    rcases ha with ha | ha <;> omega
  simp [markPrefix, hn]

theorem markPrefix_mark_iff {μ : ℕ → ℤ} {active yes : ℕ → Bool}
    {pair : ℕ → ℕ} {mark j q : ℕ} :
    markPrefix μ active yes pair mark j (mark + q) = 1 ↔
      μ (mark + q) = 1 ∨ ∃ i, i < j ∧ Qualifies active yes i ∧ pair i = q := by
  classical
  simp only [markPrefix, Nat.add_left_cancel_iff]
  split_ifs <;> simp_all

/-- A Boolean mark remains Boolean; qualifying incidences only change it to one. -/
theorem markPrefix_boolean {μ : ℕ → ℤ} {active yes : ℕ → Bool}
    {pair : ℕ → ℕ} {mark j Q : ℕ}
    (hbool : ∀ q < Q, μ (mark + q) = 0 ∨ μ (mark + q) = 1) :
    ∀ q < Q, markPrefix μ active yes pair mark j (mark + q) = 0 ∨
      markPrefix μ active yes pair mark j (mark + q) = 1 := by
  classical
  intro q hq
  unfold markPrefix
  split_ifs
  · exact Or.inr rfl
  · exact hbool q hq

/-- Exact values, including zero marks, rather than only the predicate of being marked. -/
theorem markPrefix_mark_value {μ : ℕ → ℤ} {active yes : ℕ → Bool}
    {pair : ℕ → ℕ} {mark j q : ℕ} :
    markPrefix μ active yes pair mark j (mark + q) =
      if ∃ i, i < j ∧ Qualifies active yes i ∧ pair i = q then 1
      else μ (mark + q) := by
  classical
  simp only [markPrefix, Nat.add_left_cancel_iff]

theorem round_cost : roundBody.blockCost = 22 := by rfl

theorem ends {lim : Limits} {P : Program} {d : ℕ}
    {μ : ℕ → ℤ} {active yes : ℕ → Bool} {pair : ℕ → ℕ}
    {I Q ab yb pb mb : ℕ}
    (ha : ∀ i < I, μ (ab + i) = bit (active i))
    (hy : ∀ i < I, μ (yb + i) = bit (yes i))
    (hp : ∀ i < I, μ (pb + i) = pair i)
    (hq : ∀ i < I, pair i < Q)
    (hw : (lim.space : ℤ) ≤ lim.word) (h1 : 1 ≤ lim.word)
    (hab : ab + I ≤ lim.space) (hyb : yb + I ≤ lim.space)
    (hpb : pb + I ≤ lim.space) (hmb : mb + Q ≤ lim.space)
    (hsepA : Apart ab I mb Q) (hsepY : Apart yb I mb Q)
    (hsepP : Apart pb I mb Q) :
    Ends lim P d body ⟨frame [I, Q, ab, yb, pb, mb], μ⟩ (30 * I + 6)
      (fun σ => σ.mem = markPrefix μ active yes pair mb I) := by
  classical
  unfold body
  refine Ends.forFrame (fun j μ' => μ' = markPrefix μ active yes pair mb j) I
    (markPrefix_zero μ active yes pair mb).symm ?round ?done
    (hn := by omega) (hT := by simp [round_cost]; omega)
  case round =>
    intro j μ' hj hμ
    have hout := markPrefix_outside (μ := μ) (active := active) (yes := yes) (mark := mb) (j := j) (le_of_lt hj) hq
    have hra : μ' (ab + j) = bit (active j) := by
      rw [hμ, hout _ (by rcases hsepA with h | h <;> omega)]
      exact ha j hj
    have hry : μ' (yb + j) = bit (yes j) := by
      rw [hμ, hout _ (by rcases hsepY with h | h <;> omega)]
      exact hy j hj
    have hrp : μ' (pb + j) = pair j := by
      rw [hμ, hout _ (by rcases hsepP with h | h <;> omega)]
      exact hp j hj
    have hpj := hq j hj
    unfold roundBody
    refine Ends.iteLast (fun hcA => ?_) (fun hcA => ?_) (by light_side)
    · have hA : active j = true := by simpa [hra] using hcA
      refine Ends.iteLast (fun hcY => ?_) (fun hcY => ?_) (by light_side)
      · have hY : yes j = true := by simpa [hry] using hcY
        have hn : Function.update μ' (mb + pair j) 1 =
            markPrefix μ active yes pair mb (j + 1) := by
          rw [markPrefix_succ, if_pos ⟨hA, hY⟩, hμ]
        light_store (mb + pair j) 1 using hrp
        exact ⟨rfl, hn⟩
      · have hY : yes j ≠ true := by simpa [hry] using hcY
        apply Ends.skip
        refine ⟨rfl, ?_⟩
        rw [markPrefix_succ, if_neg (by simp [Qualifies, hY])]
        exact hμ
    · have hA : active j ≠ true := by simpa [hra] using hcA
      apply Ends.skip
      refine ⟨rfl, ?_⟩
      rw [markPrefix_succ, if_neg (by simp [Qualifies, hA])]
      exact hμ
  case done =>
    intro μ' hμ
    exact hμ

theorem meets {lim : Limits} {P : Program} {d p : ℕ}
    (hbody : P[p]? = some body)
    {μ : ℕ → ℤ} {active yes : ℕ → Bool} {pair : ℕ → ℕ}
    {I Q ab yb pb mb : ℕ}
    (ha : ∀ i < I, μ (ab + i) = bit (active i))
    (hy : ∀ i < I, μ (yb + i) = bit (yes i))
    (hp : ∀ i < I, μ (pb + i) = pair i)
    (hq : ∀ i < I, pair i < Q)
    (hw : (lim.space : ℤ) ≤ lim.word) (h1 : 1 ≤ lim.word)
    (hab : ab + I ≤ lim.space) (hyb : yb + I ≤ lim.space)
    (hpb : pb + I ≤ lim.space) (hmb : mb + Q ≤ lim.space)
    (hsepA : Apart ab I mb Q) (hsepY : Apart yb I mb Q)
    (hsepP : Apart pb I mb Q) :
    Meets lim P p d [I, Q, ab, yb, pb, mb] μ (30 * I + 6) fun _ μ' =>
      SameOutside μ μ' mb Q ∧
      (∀ q < Q, μ' (mb + q) = 1 ↔
        μ (mb + q) = 1 ∨ ∃ i, i < I ∧ Qualifies active yes i ∧ pair i = q) := by
  refine .of_body hbody ?_
  refine (ends ha hy hp hq hw h1 hab hyb hpb hmb hsepA hsepY hsepP).mono le_rfl ?_
  intro σ hσ
  rw [hσ]
  exact ⟨markPrefix_outside le_rfl hq, fun _ _ => markPrefix_mark_iff⟩

/-- For a nonempty incidence table the complete procedure costs at most 36I steps. -/
theorem meets_of_pos {lim : Limits} {P : Program} {d p : ℕ}
    (hbody : P[p]? = some body)
    {μ : ℕ → ℤ} {active yes : ℕ → Bool} {pair : ℕ → ℕ}
    {I Q ab yb pb mb : ℕ}
    (ha : ∀ i < I, μ (ab + i) = bit (active i))
    (hy : ∀ i < I, μ (yb + i) = bit (yes i))
    (hp : ∀ i < I, μ (pb + i) = pair i)
    (hq : ∀ i < I, pair i < Q)
    (hw : (lim.space : ℤ) ≤ lim.word) (h1 : 1 ≤ lim.word)
    (hab : ab + I ≤ lim.space) (hyb : yb + I ≤ lim.space)
    (hpb : pb + I ≤ lim.space) (hmb : mb + Q ≤ lim.space)
    (hsepA : Apart ab I mb Q) (hsepY : Apart yb I mb Q)
    (hsepP : Apart pb I mb Q) (hI : 0 < I) :
    Meets lim P p d [I, Q, ab, yb, pb, mb] μ (36 * I) fun _ μ' =>
      SameOutside μ μ' mb Q ∧
      (∀ q < Q, μ' (mb + q) = 1 ↔
        μ (mb + q) = 1 ∨ ∃ i, i < I ∧ Qualifies active yes i ∧ pair i = q) := by
  exact (meets hbody ha hy hp hq hw h1 hab hyb hpb hmb hsepA hsepY hsepP).mono_time
    (by omega)

/-- Boolean-array form: the final marks are the old marks OR a qualifying incidence. -/
theorem meets_boolean {lim : Limits} {P : Program} {d p : ℕ}
    (hbody : P[p]? = some body)
    {μ : ℕ → ℤ} {active yes marked : ℕ → Bool} {pair : ℕ → ℕ}
    {I Q ab yb pb mb : ℕ}
    (ha : ∀ i < I, μ (ab + i) = bit (active i))
    (hy : ∀ i < I, μ (yb + i) = bit (yes i))
    (hp : ∀ i < I, μ (pb + i) = pair i)
    (hq : ∀ i < I, pair i < Q)
    (hmarked : ∀ q < Q, μ (mb + q) = bit (marked q))
    (hw : (lim.space : ℤ) ≤ lim.word) (h1 : 1 ≤ lim.word)
    (hab : ab + I ≤ lim.space) (hyb : yb + I ≤ lim.space)
    (hpb : pb + I ≤ lim.space) (hmb : mb + Q ≤ lim.space)
    (hsepA : Apart ab I mb Q) (hsepY : Apart yb I mb Q)
    (hsepP : Apart pb I mb Q) :
    Meets lim P p d [I, Q, ab, yb, pb, mb] μ (30 * I + 6) fun _ μ' =>
      SameOutside μ μ' mb Q ∧
      (∀ q < Q, μ' (mb + q) =
        if marked q = true ∨ ∃ i, i < I ∧ Qualifies active yes i ∧ pair i = q
        then 1 else 0) := by
  classical
  refine .of_body hbody ?_
  refine (ends ha hy hp hq hw h1 hab hyb hpb hmb hsepA hsepY hsepP).mono le_rfl ?_
  intro σ hσ
  rw [hσ]
  refine ⟨markPrefix_outside le_rfl hq, ?_⟩
  intro q hq'
  rw [markPrefix_mark_value, hmarked q hq']
  by_cases hex : ∃ i, i < I ∧ Qualifies active yes i ∧ pair i = q
  · simp [hex]
  · simp [hex, bit]

end Light.DenseMarkPass

#print axioms Light.DenseMarkPass.ends
#print axioms Light.DenseMarkPass.meets
#print axioms Light.DenseMarkPass.meets_of_pos
#print axioms Light.DenseMarkPass.meets_boolean
