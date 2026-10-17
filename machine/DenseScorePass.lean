import ThreeSumApsp.Lang.Lib.Pass
import ThreeSumApsp.Lang.Tactics

namespace Light.DenseScorePass

abbrev Len : ℕ := 0
abbrev Height : ℕ := 1
abbrev Active : ℕ := 2
abbrev Row : ℕ := 3
abbrev Idx : ℕ := 4
abbrev Acc : ℕ := 5

def bit (b : Bool) : ℤ := if b then 1 else 0

@[simp] theorem bit_eq_one (b : Bool) : bit b = 1 ↔ b = true := by
  cases b <;> simp [bit]

def roundBody : Stmt :=
  .ite (M (v Active +' v Idx) =' k 1)
    (.set Acc (v Acc +' M (v Row +' v Idx)))
    .skip

def body : Stmt :=
  .set Acc (k 0) ;; .for Idx (v Len) roundBody ;; .set Len (v Acc)

def score (active : ℕ → Bool) (row : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | j + 1 => score active row j + if active j then row j else 0

theorem score_bound {active : ℕ → Bool} {row : ℕ → ℕ} {I h : ℕ}
    (hrow : ∀ i < I, row i ≤ h) : ∀ j ≤ I, score active row j ≤ j * h := by
  intro j
  induction j with
  | zero => simp [score]
  | succ j ih =>
    intro hj
    have hs := ih (by omega)
    have hr : (if active j then row j else 0) ≤ h := by
      split_ifs
      · exact hrow j (by omega)
      · exact Nat.zero_le _
    simpa only [score, Nat.succ_mul] using Nat.add_le_add hs hr

/-- The specification sum; this Finset is only in a theorem, never in the Light program. -/
theorem score_eq_sum (active : ℕ → Bool) (row : ℕ → ℕ) (I : ℕ) :
    score active row I = ∑ i ∈ Finset.range I, if active i then row i else 0 := by
  induction I with
  | zero => simp [score]
  | succ I ih => simp [score, Finset.sum_range_succ, ih]

theorem round_cost : roundBody.blockCost = 14 := by rfl

theorem loop_ends {lim : Limits} {P : Program} {d : ℕ}
    {μ : ℕ → ℤ} {active : ℕ → Bool} {row : ℕ → ℕ}
    {I h ab rb : ℕ}
    (ha : ∀ i < I, μ (ab + i) = bit (active i))
    (hr : ∀ i < I, μ (rb + i) = row i)
    (hrow : ∀ i < I, row i ≤ h)
    (hw : (lim.space : ℤ) ≤ lim.word) (h1 : 1 ≤ lim.word)
    (hsum : ((I * h : ℕ) : ℤ) ≤ lim.word)
    (hab : ab + I ≤ lim.space) (hrb : rb + I ≤ lim.space) :
    Ends lim P d (.for Idx (v Len) roundBody)
      ⟨frame [I, h, ab, rb, 0, 0], μ⟩ (22 * I + 6)
      (fun σ => σ = ⟨frame [I, h, ab, rb, I, score active row I], μ⟩) := by
  refine Ends.for
    (fun j σ => σ = ⟨frame [I, h, ab, rb, j, score active row j], μ⟩)
    I roundBody.blockCost ?start ?round ?done ?bound
    (hn := by omega) (hT := by simp [round_cost]; omega)
  case start => simp [update_frame_setLocal, score]
  case round =>
    intro j σ hj _ hσ
    subst σ
    have hra := ha j hj
    have hrr := hr j hj
    have hscore : ((score active row (j + 1) : ℕ) : ℤ) ≤ lim.word := by
      have hb := score_bound (active := active) hrow (j + 1) (by omega)
      have hm : (j + 1) * h ≤ I * h := Nat.mul_le_mul_right h (by omega)
      exact le_trans (by exact_mod_cast hb.trans hm) hsum
    unfold roundBody
    refine Ends.iteLast (fun hc => ?_) (fun hc => ?_) (by light_side)
    · have hac : active j = true := by simpa [hra] using hc
      have heq : score active row (j + 1) = score active row j + row j := by
        simp [score, hac]
      refine Ends.setTo (score active row (j + 1) : ℕ) ?_ ?_ (by light_time)
      · exact ⟨by simp, by simp [update_frame_setLocal, Nat.cast_add]⟩
      · light_side [hrr, heq]
    · have hac : active j ≠ true := by simpa [hra] using hc
      have heq : score active row (j + 1) = score active row j := by
        simp [score, hac]
      apply Ends.skip
      exact ⟨by simp, by simp [update_frame_setLocal, Nat.cast_add, heq]⟩
  case done =>
    intro σ _ hσ
    exact hσ
  case bound =>
    intro j σ hj _ hσ
    subst σ
    light_side

theorem ends {lim : Limits} {P : Program} {d : ℕ}
    {μ : ℕ → ℤ} {active : ℕ → Bool} {row : ℕ → ℕ}
    {I h ab rb : ℕ}
    (ha : ∀ i < I, μ (ab + i) = bit (active i))
    (hr : ∀ i < I, μ (rb + i) = row i)
    (hrow : ∀ i < I, row i ≤ h)
    (hw : (lim.space : ℤ) ≤ lim.word) (h1 : 1 ≤ lim.word)
    (hsum : ((I * h : ℕ) : ℤ) ≤ lim.word)
    (hab : ab + I ≤ lim.space) (hrb : rb + I ≤ lim.space) :
    Ends lim P d body ⟨frame [I, h, ab, rb], μ⟩ (22 * I + 10)
      (fun σ => σ.loc 0 = score active row I ∧ σ.mem = μ) := by
  unfold body
  refine Ends.setToThen (0 : ℕ) ?_ (by light_side) (by light_time)
  refine Ends.next (22 * I + 6) ?_ (by light_time)
  refine (loop_ends ha hr hrow hw h1 hsum hab hrb).mono le_rfl ?_
  intro σ hσ
  subst σ
  refine Ends.setTo (score active row I : ℕ) ?_ (by light_side) (by light_time)
  exact ⟨by simp, rfl⟩

theorem meets {lim : Limits} {P : Program} {d p : ℕ}
    (hbody : P[p]? = some body)
    {μ : ℕ → ℤ} {active : ℕ → Bool} {row : ℕ → ℕ}
    {I h ab rb : ℕ}
    (ha : ∀ i < I, μ (ab + i) = bit (active i))
    (hr : ∀ i < I, μ (rb + i) = row i)
    (hrow : ∀ i < I, row i ≤ h)
    (hw : (lim.space : ℤ) ≤ lim.word) (h1 : 1 ≤ lim.word)
    (hsum : ((I * h : ℕ) : ℤ) ≤ lim.word)
    (hab : ab + I ≤ lim.space) (hrb : rb + I ≤ lim.space) :
    Meets lim P p d [I, h, ab, rb] μ (22 * I + 10) fun result μ' =>
      result = score active row I ∧ μ' = μ := by
  exact .of_body hbody (ends ha hr hrow hw h1 hsum hab hrb)

theorem meets_of_pos {lim : Limits} {P : Program} {d p : ℕ}
    (hbody : P[p]? = some body)
    {μ : ℕ → ℤ} {active : ℕ → Bool} {row : ℕ → ℕ}
    {I h ab rb : ℕ}
    (ha : ∀ i < I, μ (ab + i) = bit (active i))
    (hr : ∀ i < I, μ (rb + i) = row i)
    (hrow : ∀ i < I, row i ≤ h)
    (hw : (lim.space : ℤ) ≤ lim.word) (h1 : 1 ≤ lim.word)
    (hsum : ((I * h : ℕ) : ℤ) ≤ lim.word)
    (hab : ab + I ≤ lim.space) (hrb : rb + I ≤ lim.space) (hI : 0 < I) :
    Meets lim P p d [I, h, ab, rb] μ (32 * I) fun result μ' =>
      result = score active row I ∧ μ' = μ := by
  exact (meets hbody ha hr hrow hw h1 hsum hab hrb).mono_time (by omega)

end Light.DenseScorePass

#print axioms Light.DenseScorePass.score_eq_sum
#print axioms Light.DenseScorePass.ends
#print axioms Light.DenseScorePass.meets
#print axioms Light.DenseScorePass.meets_of_pos
