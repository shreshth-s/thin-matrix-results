import ThreeSumApsp.Lang.Lib.Pass
import ThreeSumApsp.Lang.Tactics
import ThreeSumApsp.Lang.PolyBounded

/-!
# Actual candidate-pool cardinality and deletion

The cardinality routine scans the supplied Boolean memory vector. It does
not trust a caller-supplied count and does not modify memory. All loop and
initialization steps are charged. Its closed task contract is stable under
appending procedures to the finite program.
-/

namespace Light.DensePoolPass

abbrev Len : ℕ := 0
abbrev Pool : ℕ := 1
abbrev Idx : ℕ := 2
abbrev Acc : ℕ := 3

def bit (b : Bool) : ℤ := if b then 1 else 0

@[simp] theorem bit_eq_one (b : Bool) : bit b = 1 ↔ b = true := by
  cases b <;> simp [bit]

def count (remaining : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | j + 1 => count remaining j + if remaining j then 1 else 0

theorem count_bound (remaining : ℕ → Bool) (N : ℕ) : count remaining N ≤ N := by
  induction N with
  | zero => simp [count]
  | succ N ih => simp only [count]; split_ifs <;> omega

theorem count_eq_sum (remaining : ℕ → Bool) (N : ℕ) :
    count remaining N = ∑ j ∈ Finset.range N, if remaining j then 1 else 0 := by
  induction N with
  | zero => simp [count]
  | succ N ih => simp only [count, Finset.sum_range_succ, ih]

/-- The result is the cardinality of the current mask, including an empty pool. -/
theorem count_eq_card (remaining : ℕ → Bool) (N : ℕ) :
    count remaining N = ((Finset.range N).filter (fun j => remaining j = true)).card := by
  rw [count_eq_sum]
  simp only [Finset.sum_boole, Nat.cast_id]

theorem count_pos_iff (remaining : ℕ → Bool) (N : ℕ) :
    0 < count remaining N ↔ ∃ j, j < N ∧ remaining j = true := by
  rw [count_eq_card, Finset.card_pos]
  simp only [Finset.filter_nonempty_iff, Finset.mem_range]

def roundBody : Stmt :=
  .ite (M (v Pool +' v Idx) =' k 1)
    (.set Acc (v Acc +' k 1)) .skip

def body : Stmt :=
  .set Acc (k 0) ;; .for Idx (v Len) roundBody ;; .set Len (v Acc)

theorem round_cost : roundBody.blockCost = 11 := by rfl

def time (N : ℕ) : ℕ := 19 * N + 10

/-- `fr` is the trailing free-pointer argument, overwritten only in a local
register. The whole memory, including every pool flag, remains unchanged. -/
theorem ends {lim : Limits} {Prog : Program} {d : ℕ}
    {μ : ℕ → ℤ} {remaining : ℕ → Bool} {N rb : ℕ} (fr : ℤ)
    (hr : ∀ j < N, μ (rb + j) = bit (remaining j))
    (hw : (lim.space : ℤ) ≤ lim.word) (h1 : 1 ≤ lim.word)
    (hN : (N : ℤ) ≤ lim.word) (hrb : rb + N ≤ lim.space) :
    Ends lim Prog d body ⟨frame [N, rb, fr], μ⟩ (time N)
      (fun σ => σ.loc 0 = count remaining N ∧ σ.mem = μ) := by
  unfold body time
  refine Ends.setToThen (0 : ℕ) ?_ (by light_side) (by light_time)
  refine Ends.next (19 * N + 6) ?_ (by light_time)
  refine Ends.for
    (fun j σ => σ = ⟨frame [N, rb, j, count remaining j], μ⟩)
    N roundBody.blockCost ?start ?round ?done ?bound
    (hn := by omega) (hT := by simp [round_cost]; omega)
  case start =>
    simp only [update_frame_setLocal, count, setLocal]
    rfl
  case round =>
    intro j σ hj _ hσ
    subst σ
    have hrr := hr j hj
    have hc : ((count remaining (j + 1) : ℕ) : ℤ) ≤ lim.word := by
      have hb := count_bound remaining (j + 1)
      have hjN : j + 1 ≤ N := by omega
      have hh : count remaining (j + 1) ≤ N := hb.trans hjN
      exact (by exact_mod_cast hh : (count remaining (j + 1) : ℤ) ≤ N).trans hN
    unfold roundBody
    refine Ends.iteLast (fun hflag => ?_) (fun hflag => ?_) (by light_side)
    · have hrem : remaining j = true := by simpa [hrr] using hflag
      have hstep : (count remaining j : ℤ) + 1 ≤ lim.word := by
        simpa only [count, hrem, if_true, Nat.cast_add, Nat.cast_one] using hc
      refine Ends.setTo (count remaining (j + 1) : ℕ) ?_
        (by light_side [count, hrem]) (by light_time)
      exact ⟨by simp, by simp [update_frame_setLocal, count, hrem]⟩
    · have hrem : remaining j ≠ true := by simpa [hrr] using hflag
      apply Ends.skip
      exact ⟨by simp, by simp [update_frame_setLocal, count, hrem]⟩
  case done =>
    intro σ _ hσ
    subst σ
    refine Ends.setTo (count remaining N : ℕ) ?_ (by light_side) (by light_time)
    exact ⟨by simp, rfl⟩
  case bound =>
    intro j σ hj _ hσ
    subst σ
    light_side

theorem meets {lim : Limits} {Prog : Program} {d p : ℕ}
    (hbody : Prog[p]? = some body)
    {μ : ℕ → ℤ} {remaining : ℕ → Bool} {N rb : ℕ} (fr : ℤ)
    (hr : ∀ j < N, μ (rb + j) = bit (remaining j))
    (hw : (lim.space : ℤ) ≤ lim.word) (h1 : 1 ≤ lim.word)
    (hN : (N : ℤ) ≤ lim.word) (hrb : rb + N ≤ lim.space) :
    Meets lim Prog p d [N, rb, fr] μ (time N) fun result μ' =>
      result = count remaining N ∧ μ' = μ := by
  exact .of_body hbody (ends fr hr hw h1 hN hrb)

structure Instance where
  length : ℕ
  poolBase : ℕ
  remaining : ℕ → Bool

structure Pre (x : Instance) (μ : ℕ → ℤ) (fr : ℕ) : Prop where
  pool_read : ∀ j < x.length, μ (x.poolBase + j) = bit (x.remaining j)
  pool_below : x.poolBase + x.length ≤ fr

def task : Task where
  Inst := Instance
  size x := x.length
  bound _ := 1
  args x := [x.length, x.poolBase]
  Pre := Pre
  Post x μ _ result μ' := result = count x.remaining x.length ∧ μ' = μ

def need (n _U : ℕ) : Need where
  word := n + 1
  cells := 0
  depth := 0

def taskTime (n _U : ℕ) : ℕ := time n

def program : Program := [body]

theorem body_in_program : program[0]? = some body := rfl

theorem task_solved : Solves task program 0 taskTime need := by
  refine ⟨body, body_in_program, ?_⟩
  intro R lim d x μ fr hpre hok
  have hfr : fr ≤ lim.space := by simpa only [need, add_zero] using hok.cells
  have hw := hok.word
  change ((x.length + 1 : ℕ) : ℤ) ≤ lim.word at hw
  have h1 : 1 ≤ lim.word := by omega
  have hN : (x.length : ℤ) ≤ lim.word := by omega
  change Ends lim (program ++ R) d body
    ⟨frame [x.length, x.poolBase, fr], μ⟩ (time x.length) _
  exact ends (fr : ℤ) hpre.pool_read hok.space h1 hN (hpre.pool_below.trans hfr)

theorem need_polynomial : PolyNeed need := by
  unfold need
  poly_need []

theorem solvedIn : SolvedIn task (fun n _ => 19 * n + 10) := by
  refine ⟨program, 0, taskTime, need, need_polynomial, task_solved, ?_⟩
  intros
  simp only [taskTime, time, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, le_refl]

theorem task_solved_append (R : Program) : Solves task (program ++ R) 0 taskTime need :=
  task_solved.append R

/-- Clearing is Boolean deletion, rather than arithmetic decrement of a flag. -/
def cleared (remaining : ℕ → Bool) (chosen : ℕ) : ℕ → Bool :=
  Function.update remaining chosen false

theorem cleared_at (remaining : ℕ → Bool) (chosen : ℕ) :
    cleared remaining chosen chosen = false := by simp [cleared]

theorem cleared_elsewhere (remaining : ℕ → Bool) (chosen j : ℕ) (hj : j ≠ chosen) :
    cleared remaining chosen j = remaining j := by simp [cleared, hj]

theorem cleared_filter (remaining : ℕ → Bool) (chosen N : ℕ) :
    (Finset.range N).filter (fun j => cleared remaining chosen j = true) =
      ((Finset.range N).filter (fun j => remaining j = true)).erase chosen := by
  ext j
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_erase]
  by_cases hj : j = chosen
  · subst j
    simp [cleared]
  · simp [cleared, hj]

/-- A chosen remaining candidate removes exactly one current member. This
connects an actual flag-clear store to the next scan's cardinality, provided
selection has already proved membership. -/
theorem count_cleared_add_one {remaining : ℕ → Bool} {chosen N : ℕ}
    (hchosen : chosen < N) (hremaining : remaining chosen = true) :
    count (cleared remaining chosen) N + 1 = count remaining N := by
  rw [count_eq_card, count_eq_card, cleared_filter]
  exact Finset.card_erase_add_one (by simp [hchosen, hremaining])

theorem count_cleared {remaining : ℕ → Bool} {chosen N : ℕ}
    (hchosen : chosen < N) (hremaining : remaining chosen = true) :
    count (cleared remaining chosen) N = count remaining N - 1 := by
  have := count_cleared_add_one hchosen hremaining
  omega

/-- A single zero store has exactly the intended post-deletion mask. -/
theorem cleared_read {μ : ℕ → ℤ} {remaining : ℕ → Bool} {N rb chosen : ℕ}
    (hr : ∀ j < N, μ (rb + j) = bit (remaining j)) :
    ∀ j < N, Function.update μ (rb + chosen) 0 (rb + j) =
      bit (cleared remaining chosen j) := by
  intro j hj
  by_cases heq : j = chosen
  · subst j
    simp [cleared, bit]
  · simp [cleared, heq, hr j hj]

end Light.DensePoolPass

#print axioms Light.DensePoolPass.count_eq_card
#print axioms Light.DensePoolPass.count_pos_iff
#print axioms Light.DensePoolPass.ends
#print axioms Light.DensePoolPass.meets
#print axioms Light.DensePoolPass.task_solved
#print axioms Light.DensePoolPass.need_polynomial
#print axioms Light.DensePoolPass.solvedIn
#print axioms Light.DensePoolPass.task_solved_append

#print axioms Light.DensePoolPass.count_cleared_add_one
#print axioms Light.DensePoolPass.count_cleared
#print axioms Light.DensePoolPass.cleared_read
