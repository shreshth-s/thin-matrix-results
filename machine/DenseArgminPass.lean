import ThreeSumApsp.Lang.Lib.Pass
import ThreeSumApsp.Lang.Tactics

namespace Light.DenseArgminPass

abbrev Len : ℕ := 0
abbrev MaxScore : ℕ := 1
abbrev Remain : ℕ := 2
abbrev Scores : ℕ := 3
abbrev Idx : ℕ := 4
abbrev BestIdx : ℕ := 5
abbrev BestScore : ℕ := 6

def bit (b : Bool) : ℤ := if b then 1 else 0

@[simp] theorem bit_eq_one (b : Bool) : bit b = 1 ↔ b = true := by
  cases b <;> simp [bit]

def roundBody : Stmt :=
  .ite (M (v Remain +' v Idx) =' k 1)
    (.ite (M (v Scores +' v Idx) <' v BestScore)
      (.set BestIdx (v Idx) ;; .set BestScore (M (v Scores +' v Idx)))
      .skip)
    .skip

def body : Stmt :=
  .set BestIdx (k 0) ;;
  .set BestScore (v MaxScore +' k 1) ;;
  .for Idx (v Len) roundBody ;;
  .set Len (v BestIdx)

/-- Pure specification of the prefix scan, with a genuinely larger sentinel. -/
def scan (remaining : ℕ → Bool) (scores : ℕ → ℕ) (H : ℕ) : ℕ → ℕ × ℕ
  | 0 => (0, H + 1)
  | j + 1 =>
      let old := scan remaining scores H j
      if remaining j = true ∧ scores j < old.2 then (j, scores j) else old

def ScanSpec (remaining : ℕ → Bool) (scores : ℕ → ℕ) (H j : ℕ) : Prop :=
  (scan remaining scores H j).2 ≤ H + 1 ∧
  (((scan remaining scores H j).2 = H + 1 ∧ (scan remaining scores H j).1 = 0) ∨
    ((scan remaining scores H j).1 < j ∧
      remaining (scan remaining scores H j).1 = true ∧
      (scan remaining scores H j).2 = scores (scan remaining scores H j).1)) ∧
  (∀ q < j, remaining q = true → (scan remaining scores H j).2 ≤ scores q)

theorem scan_spec {remaining : ℕ → Bool} {scores : ℕ → ℕ} {H N : ℕ}
    (hscores : ∀ q < N, scores q ≤ H) : ∀ j ≤ N, ScanSpec remaining scores H j := by
  intro j
  induction j with
  | zero => simp [ScanSpec, scan]
  | succ j ih =>
    intro hj
    have hi := ih (by omega)
    rcases hi with ⟨hbound, hwitness, hlower⟩
    by_cases hu : remaining j = true ∧ scores j < (scan remaining scores H j).2
    · simp only [ScanSpec, scan, if_pos hu]
      refine ⟨?_, Or.inr ⟨by omega, hu.1, True.intro⟩, ?_⟩
      · have := hscores j (by omega)
        omega
      · intro q hq hrem
        by_cases heq : q = j
        · subst q
          exact le_rfl
        · exact hu.2.le.trans (hlower q (by omega) hrem)
    · simp only [ScanSpec, scan, if_neg hu]
      refine ⟨hbound, ?_, ?_⟩
      · rcases hwitness with hw | ⟨hb, hr, hs⟩
        · exact Or.inl hw
        · exact Or.inr ⟨by omega, hr, hs⟩
      · intro q hq hrem
        by_cases heq : q = j
        · subst q
          have hn : ¬ scores j < (scan remaining scores H j).2 := by
            intro hh
            exact hu ⟨hrem, hh⟩
          omega
        · exact hlower q (by omega) hrem

def IsArgmin (remaining : ℕ → Bool) (scores : ℕ → ℕ) (N p : ℕ) : Prop :=
  p < N ∧ remaining p = true ∧ ∀ q < N, remaining q = true → scores p ≤ scores q

theorem scan_isArgmin {remaining : ℕ → Bool} {scores : ℕ → ℕ} {H N : ℕ}
    (hscores : ∀ q < N, scores q ≤ H)
    (hne : ∃ q, q < N ∧ remaining q = true) :
    IsArgmin remaining scores N (scan remaining scores H N).1 := by
  obtain ⟨q, hq, hrem⟩ := hne
  obtain ⟨_, hwitness, hlower⟩ := scan_spec (remaining := remaining) hscores N le_rfl
  rcases hwitness with ⟨hsentinel, _⟩ | ⟨hp, hr, hs⟩
  · have := hlower q hq hrem
    have := hscores q hq
    omega
  · refine ⟨hp, hr, ?_⟩
    intro r hrr hremain
    rw [← hs]
    exact hlower r hrr hremain

theorem round_cost : roundBody.blockCost = 21 := by rfl

theorem loop_ends {lim : Limits} {P : Program} {d : ℕ}
    {μ : ℕ → ℤ} {remaining : ℕ → Bool} {scores : ℕ → ℕ}
    {N H rb sb : ℕ}
    (hr : ∀ i < N, μ (rb + i) = bit (remaining i))
    (hs : ∀ i < N, μ (sb + i) = scores i)
    (hscores : ∀ i < N, scores i ≤ H)
    (hw : (lim.space : ℤ) ≤ lim.word) (h1 : 1 ≤ lim.word)
    (hsentinel : ((H + 1 : ℕ) : ℤ) ≤ lim.word)
    (hrb : rb + N ≤ lim.space) (hsb : sb + N ≤ lim.space) :
    Ends lim P d (.for Idx (v Len) roundBody)
      ⟨frame [N, H, rb, sb, 0, 0, H + 1], μ⟩ (29 * N + 6)
      (fun σ => σ = ⟨frame [N, H, rb, sb, N,
        (scan remaining scores H N).1, (scan remaining scores H N).2], μ⟩) := by
  refine Ends.for
    (fun j σ => σ = ⟨frame [N, H, rb, sb, j,
      (scan remaining scores H j).1, (scan remaining scores H j).2], μ⟩)
    N roundBody.blockCost ?start ?round ?done ?bound
    (hn := by omega) (hT := by simp [round_cost]; omega)
  case start => simp [update_frame_setLocal, scan]
  case round =>
    intro j σ hj _ hσ
    subst σ
    have hrr := hr j hj
    have hrs := hs j hj
    have hwordScore : (scores j : ℤ) ≤ lim.word := by
      have := hscores j hj
      omega
    unfold roundBody
    refine Ends.iteLast (fun hcR => ?_) (fun hcR => ?_) (by light_side)
    · have hR : remaining j = true := by simpa [hrr] using hcR
      refine Ends.iteLast (fun hcS => ?_) (fun hcS => ?_) (by light_side)
      · have hS : scores j < (scan remaining scores H j).2 := by
          exact_mod_cast (show (scores j : ℤ) < (scan remaining scores H j).2 by
            simpa [hrs] using hcS)
        have hnext : scan remaining scores H (j + 1) = (j, scores j) := by
          simp [scan, hR, hS]
        refine Ends.setToThen (j : ℕ) ?_ (by light_side) (by light_time)
        refine Ends.setTo (scores j : ℕ) ?_ (by light_side [hrs]) (by light_time)
        exact ⟨by simp, by simp [update_frame_setLocal, Nat.cast_add, hnext]⟩
      · have hS : ¬ scores j < (scan remaining scores H j).2 := by
          intro hh
          apply hcS
          have : (scores j : ℤ) < (scan remaining scores H j).2 := by exact_mod_cast hh
          simpa [hrs] using this
        have hnext : scan remaining scores H (j + 1) = scan remaining scores H j := by
          simp [scan, hS]
        apply Ends.skip
        exact ⟨by simp, by simp [update_frame_setLocal, Nat.cast_add, hnext]⟩
    · have hR : remaining j ≠ true := by simpa [hrr] using hcR
      have hnext : scan remaining scores H (j + 1) = scan remaining scores H j := by
        simp [scan, hR]
      apply Ends.skip
      exact ⟨by simp, by simp [update_frame_setLocal, Nat.cast_add, hnext]⟩
  case done =>
    intro σ _ hσ
    exact hσ
  case bound =>
    intro j σ hj _ hσ
    subst σ
    light_side

theorem ends {lim : Limits} {P : Program} {d : ℕ}
    {μ : ℕ → ℤ} {remaining : ℕ → Bool} {scores : ℕ → ℕ}
    {N H rb sb : ℕ}
    (hr : ∀ i < N, μ (rb + i) = bit (remaining i))
    (hs : ∀ i < N, μ (sb + i) = scores i)
    (hscores : ∀ i < N, scores i ≤ H)
    (hw : (lim.space : ℤ) ≤ lim.word) (h1 : 1 ≤ lim.word)
    (hsentinel : ((H + 1 : ℕ) : ℤ) ≤ lim.word)
    (hrb : rb + N ≤ lim.space) (hsb : sb + N ≤ lim.space) :
    Ends lim P d body ⟨frame [N, H, rb, sb], μ⟩ (29 * N + 14)
      (fun σ => σ.loc 0 = (scan remaining scores H N).1 ∧ σ.mem = μ) := by
  unfold body
  refine Ends.setToThen (0 : ℕ) ?_ (by light_side) (by light_time)
  refine Ends.setToThen (H + 1 : ℕ) ?_ (by light_side) (by light_time)
  refine Ends.next (29 * N + 6) ?_ (by light_time)
  refine (loop_ends hr hs hscores hw h1 hsentinel hrb hsb).mono le_rfl ?_
  intro σ hσ
  subst σ
  refine Ends.setTo ((scan remaining scores H N).1 : ℕ) ?_ (by light_side) (by light_time)
  exact ⟨by simp, rfl⟩

theorem meets {lim : Limits} {P : Program} {d p : ℕ}
    (hbody : P[p]? = some body)
    {μ : ℕ → ℤ} {remaining : ℕ → Bool} {scores : ℕ → ℕ}
    {N H rb sb : ℕ}
    (hr : ∀ i < N, μ (rb + i) = bit (remaining i))
    (hs : ∀ i < N, μ (sb + i) = scores i)
    (hscores : ∀ i < N, scores i ≤ H)
    (hne : ∃ q, q < N ∧ remaining q = true)
    (hw : (lim.space : ℤ) ≤ lim.word) (h1 : 1 ≤ lim.word)
    (hsentinel : ((H + 1 : ℕ) : ℤ) ≤ lim.word)
    (hrb : rb + N ≤ lim.space) (hsb : sb + N ≤ lim.space) :
    Meets lim P p d [N, H, rb, sb] μ (29 * N + 14) fun result μ' =>
      μ' = μ ∧ ∃ chosen : ℕ, result = chosen ∧ IsArgmin remaining scores N chosen := by
  refine .of_body hbody ?_
  refine (ends hr hs hscores hw h1 hsentinel hrb hsb).mono le_rfl ?_
  intro σ hσ
  exact ⟨hσ.2, (scan remaining scores H N).1, hσ.1, scan_isArgmin hscores hne⟩

theorem meets_linear {lim : Limits} {P : Program} {d p : ℕ}
    (hbody : P[p]? = some body)
    {μ : ℕ → ℤ} {remaining : ℕ → Bool} {scores : ℕ → ℕ}
    {N H rb sb : ℕ}
    (hr : ∀ i < N, μ (rb + i) = bit (remaining i))
    (hs : ∀ i < N, μ (sb + i) = scores i)
    (hscores : ∀ i < N, scores i ≤ H)
    (hne : ∃ q, q < N ∧ remaining q = true)
    (hw : (lim.space : ℤ) ≤ lim.word) (h1 : 1 ≤ lim.word)
    (hsentinel : ((H + 1 : ℕ) : ℤ) ≤ lim.word)
    (hrb : rb + N ≤ lim.space) (hsb : sb + N ≤ lim.space) :
    Meets lim P p d [N, H, rb, sb] μ (43 * N) fun result μ' =>
      μ' = μ ∧ ∃ chosen : ℕ, result = chosen ∧ IsArgmin remaining scores N chosen := by
  have hN : 0 < N := by obtain ⟨q, hq, _⟩ := hne; omega
  exact (meets hbody hr hs hscores hne hw h1 hsentinel hrb hsb).mono_time (by omega)

end Light.DenseArgminPass

#print axioms Light.DenseArgminPass.scan_isArgmin
#print axioms Light.DenseArgminPass.ends
#print axioms Light.DenseArgminPass.meets
#print axioms Light.DenseArgminPass.meets_linear
