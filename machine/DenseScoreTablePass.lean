import DenseScorePass
import DenseArgminPass
import ThreeSumApsp.Lang.Calls
import ThreeSumApsp.Lang.PolyBounded

/-!
# Actual cached-score table construction

The finite Light routine below calls the proved active-row sum for each row
of a flat row-major count table, then stores its scalar result. The proof
charges argument evaluation, procedure calls, stores and the outer loop.
This is one controller component, not an improved min-plus solver.
-/

namespace Light.DenseScoreTablePass

abbrev Candidates : ℕ := 0
abbrev Len : ℕ := 1
abbrev Height : ℕ := 2
abbrev Active : ℕ := 3
abbrev Rows : ℕ := 4
abbrev Out : ℕ := 5
abbrev Candidate : ℕ := 6
abbrev Score : ℕ := 7

def roundBody (scoreProc : ℕ) : Stmt :=
  .call scoreProc [v Len, v Height, v Active, v Rows +' v Candidate *' v Len] Score ;;
  .store (v Out +' v Candidate) (v Score)

def body (scoreProc : ℕ) : Stmt := .for Candidate (v Candidates) (roundBody scoreProc)

def scores (active : ℕ → Bool) (rows : ℕ → ℕ → ℕ) (I p : ℕ) : ℕ :=
  DenseScorePass.score active (rows p) I

theorem scores_eq_sum (active : ℕ → Bool) (rows : ℕ → ℕ → ℕ) (I p : ℕ) :
    scores active rows I p = ∑ i ∈ Finset.range I, if active i then rows p i else 0 :=
  DenseScorePass.score_eq_sum active (rows p) I

def time (P I : ℕ) : ℕ := P * (22 * I + 33) + 6

/-- This statement is uniform in the initial trailing frame cell, including
the free-memory pointer appended by `Solves`. It proves actual executions. -/
theorem ends {lim : Limits} {Prog : Program} {d scoreProc : ℕ}
    (hscore : Prog[scoreProc]? = some DenseScorePass.body)
    {μ : ℕ → ℤ} {active : ℕ → Bool} {rows : ℕ → ℕ → ℕ}
    {P I h ab rb out : ℕ} (fr : ℤ)
    (ha : ∀ i < I, μ (ab + i) = DenseScorePass.bit (active i))
    (hr : ∀ p < P, ∀ i < I, μ (rb + p * I + i) = rows p i)
    (hrow : ∀ p < P, ∀ i < I, rows p i ≤ h)
    (hw : (lim.space : ℤ) ≤ lim.word) (h1 : 1 ≤ lim.word)
    (hh : (h : ℤ) ≤ lim.word) (hsum : ((I * h : ℕ) : ℤ) ≤ lim.word)
    (hab : ab + I ≤ lim.space) (hrb : rb + P * I ≤ lim.space)
    (hout : out + P ≤ lim.space)
    (hsepA : Apart ab I out P) (hsepR : Apart rb (P * I) out P)
    (hdepth : d < lim.depth) :
    Ends lim Prog d (body scoreProc) ⟨frame [P, I, h, ab, rb, out, fr], μ⟩
      (time P I) fun σ =>
        σ.mem = wrote μ out (fun p => (scores active rows I p : ℤ)) P := by
  unfold body time
  refine Ends.forShape
    (fun p (z : ℤ) μ' => ⟨frame [P, I, h, ab, rb, out, p, z], μ'⟩)
    (fun p μ' => μ' = wrote μ out (fun p => (scores active rows I p : ℤ)) p)
    P (22 * I + 25) 0 wrote_zero.symm ?round ?done
    (first := by
      simp only [update_frame_setLocal, setLocal]
      congr 1
      exact (frame_append_zeros [P, I, h, ab, rb, out, 0] 1).symm)
    (hn := by omega) (hT := by simp only [Expr.cost]; ring_nf; omega)
  case round =>
    intro p z μ' hp hμ
    have hra : ∀ i < I, μ' (ab + i) = DenseScorePass.bit (active i) := by
      intro i hi
      rw [hμ, wrote_rest (by rcases hsepA with hs | hs <;> omega)]
      exact ha i hi
    have hrp : ∀ i < I, μ' (rb + p * I + i) = rows p i := by
      intro i hi
      have hpi : p * I + i < P * I := by nlinarith
      rw [hμ, wrote_rest (by rcases hsepR with hs | hs <;> omega)]
      exact hr p hp i hi
    have hrowp := hrow p hp
    have hrowaddr : rb + p * I + I ≤ lim.space := by
      have : (p + 1) * I ≤ P * I := Nat.mul_le_mul_right I (by omega)
      nlinarith
    have hmul : ((p * I : ℕ) : ℤ) ≤ lim.word := by
      have : p * I ≤ P * I := Nat.mul_le_mul_right I hp.le
      omega
    have hrowbase : ((rb + p * I : ℕ) : ℤ) ≤ lim.word := by omega
    have hval : ((scores active rows I p : ℕ) : ℤ) ≤ lim.word := by
      have hb : scores active rows I p ≤ I * h := DenseScorePass.score_bound hrowp I le_rfl
      exact (by exact_mod_cast hb : (scores active rows I p : ℤ) ≤ (I * h : ℕ)).trans hsum
    unfold roundBody
    refine Ends.callToThen
      (DenseScorePass.meets hscore hra hrp hrowp hw h1 hsum hab hrowaddr)
      (fun r μ'' hresult => ?_)
      (ha := by light_side [Nat.cast_add, Nat.cast_mul])
      (hd := hdepth) (hT := by light_time)
    obtain ⟨hresult, rfl⟩ := hresult
    change r = (scores active rows I p : ℤ) at hresult
    subst r
    light_store (out + p) (scores active rows I p : ℕ)
    refine ⟨(scores active rows I p : ℤ),
      Function.update μ'' (out + p) (scores active rows I p : ℤ), ?_, ?_⟩
    · rfl
    · rw [hμ]
      exact wrote_succ
  case done =>
    intro z μ' hμ
    exact hμ

theorem meets {lim : Limits} {Prog : Program} {d proc scoreProc : ℕ}
    (hbody : Prog[proc]? = some (body scoreProc))
    (hscore : Prog[scoreProc]? = some DenseScorePass.body)
    {μ : ℕ → ℤ} {active : ℕ → Bool} {rows : ℕ → ℕ → ℕ}
    {P I h ab rb out : ℕ} (fr : ℤ)
    (ha : ∀ i < I, μ (ab + i) = DenseScorePass.bit (active i))
    (hr : ∀ p < P, ∀ i < I, μ (rb + p * I + i) = rows p i)
    (hrow : ∀ p < P, ∀ i < I, rows p i ≤ h)
    (hw : (lim.space : ℤ) ≤ lim.word) (h1 : 1 ≤ lim.word)
    (hh : (h : ℤ) ≤ lim.word) (hsum : ((I * h : ℕ) : ℤ) ≤ lim.word)
    (hab : ab + I ≤ lim.space) (hrb : rb + P * I ≤ lim.space)
    (hout : out + P ≤ lim.space)
    (hsepA : Apart ab I out P) (hsepR : Apart rb (P * I) out P)
    (hdepth : d < lim.depth) :
    Meets lim Prog proc d [P, I, h, ab, rb, out, fr] μ (time P I) fun _ μ' =>
      SameOutside μ μ' out P ∧ ∀ p < P,
        μ' (out + p) = (scores active rows I p : ℤ) ∧ scores active rows I p ≤ I * h := by
  refine .of_body hbody ?_
  refine (ends hscore fr ha hr hrow hw h1 hh hsum hab hrb hout hsepA hsepR hdepth).mono
    le_rfl ?_
  intro σ hσ
  rw [hσ]
  refine ⟨sameOutside_wrote le_rfl, ?_⟩
  intro p hp
  exact ⟨wrote_done hp, DenseScorePass.score_bound (hrow p hp) I le_rfl⟩

/-- The shape size counts the flat input table, mask and caller-provided
score vector. The program needs no further memory cells. -/
structure Instance where
  candidates : ℕ
  length : ℕ
  height : ℕ
  activeBase : ℕ
  rowsBase : ℕ
  scoresBase : ℕ
  active : ℕ → Bool
  rows : ℕ → ℕ → ℕ

def instanceSize (x : Instance) : ℕ :=
  x.candidates * x.length + x.candidates + x.length

structure Pre (x : Instance) (μ : ℕ → ℤ) (fr : ℕ) : Prop where
  active_read : ∀ i < x.length,
    μ (x.activeBase + i) = DenseScorePass.bit (x.active i)
  rows_read : ∀ p < x.candidates, ∀ i < x.length,
    μ (x.rowsBase + p * x.length + i) = x.rows p i
  rows_bound : ∀ p < x.candidates, ∀ i < x.length, x.rows p i ≤ x.height
  active_below : x.activeBase + x.length ≤ fr
  rows_below : x.rowsBase + x.candidates * x.length ≤ fr
  scores_below : x.scoresBase + x.candidates ≤ fr
  active_separate : Apart x.activeBase x.length x.scoresBase x.candidates
  rows_separate : Apart x.rowsBase (x.candidates * x.length) x.scoresBase x.candidates

def task : Task where
  Inst := Instance
  size := instanceSize
  bound x := x.height
  args x := [x.candidates, x.length, x.height, x.activeBase, x.rowsBase, x.scoresBase]
  Pre := Pre
  Post x μ _ _ μ' := SameOutside μ μ' x.scoresBase x.candidates ∧
    ∀ p < x.candidates,
      μ' (x.scoresBase + p) = (scores x.active x.rows x.length p : ℤ)

def need (n U : ℕ) : Need where
  word := (n + 1) * (U + 1)
  cells := 0
  depth := 1

def taskTime (n _U : ℕ) : ℕ := 33 * n + 6

/-- A fixed, finite program; the table routine calls the row scorer at 0. -/
def program : Program := [DenseScorePass.body, body 0]

theorem score_in_program : program[0]? = some DenseScorePass.body := rfl

theorem table_in_program : program[1]? = some (body 0) := rfl

theorem time_le_taskTime (x : Instance) :
    time x.candidates x.length ≤ taskTime (instanceSize x) x.height := by
  unfold time taskTime instanceSize
  nlinarith

/-- The closed task has real bounded executions for every appended program,
with frozen inputs and arbitrary surrounding memory. No solver or execution
premise is assumed. -/
theorem task_solved : Solves task program 1 taskTime need := by
  refine ⟨body 0, table_in_program, ?_⟩
  intro R lim d x μ fr hpre hok
  have hfr : fr ≤ lim.space := by simpa only [need, add_zero] using hok.cells
  have hn : x.length ≤ instanceSize x := by unfold instanceSize; omega
  have hheight : x.height ≤ (instanceSize x + 1) * (x.height + 1) := by nlinarith
  have hsum : x.length * x.height ≤ (instanceSize x + 1) * (x.height + 1) := by
    nlinarith
  have hone : 1 ≤ (instanceSize x + 1) * (x.height + 1) := by nlinarith
  have hw := hok.word
  change (((instanceSize x + 1) * (x.height + 1) : ℕ) : ℤ) ≤ lim.word at hw
  have h1 : 1 ≤ lim.word :=
    (by exact_mod_cast hone : (1 : ℤ) ≤ ((instanceSize x + 1) * (x.height + 1) : ℕ)).trans hw
  have hh : (x.height : ℤ) ≤ lim.word :=
    (by exact_mod_cast hheight : (x.height : ℤ) ≤ ((instanceSize x + 1) * (x.height + 1) : ℕ)).trans hw
  have hs : ((x.length * x.height : ℕ) : ℤ) ≤ lim.word :=
    (by exact_mod_cast hsum : ((x.length * x.height : ℕ) : ℤ) ≤
      ((instanceSize x + 1) * (x.height + 1) : ℕ)).trans hw
  have hd : d < lim.depth := by
    have := hok.depth
    change d + 1 ≤ lim.depth at this
    omega
  change Ends lim (program ++ R) d (body 0)
    ⟨frame [x.candidates, x.length, x.height, x.activeBase, x.rowsBase, x.scoresBase, fr], μ⟩
    (taskTime (instanceSize x) x.height) _
  refine (ends (getElem?_append_of_eq_some score_in_program R) (fr : ℤ)
    hpre.active_read hpre.rows_read hpre.rows_bound hok.space h1 hh hs
    (hpre.active_below.trans hfr) (hpre.rows_below.trans hfr)
    (hpre.scores_below.trans hfr) hpre.active_separate hpre.rows_separate hd).mono
    (time_le_taskTime x) ?_
  intro σ hσ
  change SameOutside μ σ.mem x.scoresBase x.candidates ∧ _
  rw [hσ]
  exact ⟨sameOutside_wrote le_rfl, fun p hp => wrote_done hp⟩

theorem need_polynomial : PolyNeed need := by
  unfold need
  poly_need []

theorem solvedIn : SolvedIn task (fun n _ => 33 * n + 6) := by
  refine ⟨program, 1, taskTime, need, need_polynomial, task_solved, ?_⟩
  intros
  simp only [taskTime, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, le_refl]

#print axioms ends
#print axioms meets
#print axioms scores_eq_sum
#print axioms time_le_taskTime
#print axioms task_solved
#print axioms need_polynomial
#print axioms solvedIn

namespace Selection

/-- Compute every active-row score and choose its minimum over the remaining
candidates. The cached-score array is the only modified memory region. -/
def body (tableProc argminProc : ℕ) : Stmt :=
  .call tableProc [v 0, v 1, v 2, v 3, v 4, v 5, v 7] 8 ;;
  .call argminProc [v 0, v 1 *' v 2, v 6, v 5] 0

def time (P I : ℕ) : ℕ := DenseScoreTablePass.time P I + 29 * P + 31

theorem ends {lim : Limits} {Prog : Program} {d tableProc scoreProc argminProc : ℕ}
    (htable : Prog[tableProc]? = some (DenseScoreTablePass.body scoreProc))
    (hscore : Prog[scoreProc]? = some DenseScorePass.body)
    (hargmin : Prog[argminProc]? = some DenseArgminPass.body)
    {μ : ℕ → ℤ} {active remaining : ℕ → Bool} {rows : ℕ → ℕ → ℕ}
    {P I h ab rb out rem fr : ℕ}
    (ha : ∀ i < I, μ (ab + i) = DenseScorePass.bit (active i))
    (hr : ∀ p < P, ∀ i < I, μ (rb + p * I + i) = rows p i)
    (hrow : ∀ p < P, ∀ i < I, rows p i ≤ h)
    (hrem : ∀ p < P, μ (rem + p) = DenseArgminPass.bit (remaining p))
    (hne : ∃ p, p < P ∧ remaining p = true)
    (hw : (lim.space : ℤ) ≤ lim.word) (h1 : 1 ≤ lim.word)
    (hh : (h : ℤ) ≤ lim.word)
    (hsentinel : ((I * h + 1 : ℕ) : ℤ) ≤ lim.word)
    (hab : ab + I ≤ lim.space) (hrb : rb + P * I ≤ lim.space)
    (hout : out + P ≤ lim.space) (hremb : rem + P ≤ lim.space)
    (_hfr : fr ≤ lim.space)
    (hsepA : Apart ab I out P) (hsepR : Apart rb (P * I) out P)
    (hsepRem : Apart rem P out P) (hdepth : d + 2 ≤ lim.depth) :
    Ends lim Prog d (body tableProc argminProc)
      ⟨frame [P, I, h, ab, rb, out, rem, fr], μ⟩ (time P I) fun σ =>
        SameOutside μ σ.mem out P ∧
        (∀ p < P, σ.mem (out + p) = (scores active rows I p : ℤ)) ∧
        ∃ chosen : ℕ, σ.loc 0 = chosen ∧
          DenseArgminPass.IsArgmin remaining (scores active rows I) P chosen := by
  have hsum : ((I * h : ℕ) : ℤ) ≤ lim.word := by omega
  unfold body
  refine Ends.callToThen
    (DenseScoreTablePass.meets htable hscore (fr : ℤ) ha hr hrow hw h1 hh hsum
      hab hrb hout hsepA hsepR (by omega))
    (fun r μ' htableResult => ?_)
    (ha := by light_side) (hd := by omega) (hT := by light_time [time])
  obtain ⟨hkeep, hscores⟩ := htableResult
  have hr' : ∀ p < P, μ' (rem + p) = DenseArgminPass.bit (remaining p) := by
    intro p hp
    rw [hkeep (rem + p) (by rcases hsepRem with hs | hs <;> omega)]
    exact hrem p hp
  refine Ends.callTo
    (DenseArgminPass.meets hargmin hr' (fun p hp => (hscores p hp).1)
      (fun p hp => (hscores p hp).2) hne hw h1 hsentinel hremb hout)
    (fun result μ'' hresult => ?_)
    (ha := by light_side [Nat.cast_mul]) (hd := by omega)
    (hT := by light_time [time])
  obtain ⟨rfl, chosen, hresult, hchosen⟩ := hresult
  exact ⟨hkeep, fun p hp => (hscores p hp).1, chosen, by simpa using hresult, hchosen⟩

/-- No abstract callback occurs in this finite program. -/
def program : Program :=
  [DenseScorePass.body, DenseScoreTablePass.body 0, DenseArgminPass.body, body 1 2]

theorem score_in_program : program[0]? = some DenseScorePass.body := rfl
theorem table_in_program : program[1]? = some (DenseScoreTablePass.body 0) := rfl
theorem argmin_in_program : program[2]? = some DenseArgminPass.body := rfl
theorem selection_in_program : program[3]? = some (body 1 2) := rfl

structure Instance extends DenseScoreTablePass.Instance where
  remainingBase : ℕ
  remaining : ℕ → Bool

def instanceSize (x : Instance) : ℕ :=
  DenseScoreTablePass.instanceSize x.toInstance + x.candidates

structure Pre (x : Instance) (μ : ℕ → ℤ) (fr : ℕ) : Prop extends
    DenseScoreTablePass.Pre x.toInstance μ fr where
  remaining_read : ∀ p < x.candidates,
    μ (x.remainingBase + p) = DenseArgminPass.bit (x.remaining p)
  remaining_below : x.remainingBase + x.candidates ≤ fr
  remaining_separate : Apart x.remainingBase x.candidates x.scoresBase x.candidates
  nonempty : ∃ p, p < x.candidates ∧ x.remaining p = true

def task : Task where
  Inst := Instance
  size := instanceSize
  bound x := x.height
  args x := [x.candidates, x.length, x.height, x.activeBase,
    x.rowsBase, x.scoresBase, x.remainingBase]
  Pre := Pre
  Post x μ _ r μ' := SameOutside μ μ' x.scoresBase x.candidates ∧
    (∀ p < x.candidates,
      μ' (x.scoresBase + p) = (scores x.active x.rows x.length p : ℤ)) ∧
    ∃ chosen : ℕ, r = chosen ∧
      DenseArgminPass.IsArgmin x.remaining (scores x.active x.rows x.length) x.candidates chosen

def need (n U : ℕ) : Need where
  word := (n + 1) * (U + 1) + 1
  cells := 0
  depth := 2

def taskTime (n _U : ℕ) : ℕ := 62 * n + 37

theorem time_le_taskTime (x : Instance) :
    time x.candidates x.length ≤ taskTime (instanceSize x) x.height := by
  unfold time DenseScoreTablePass.time taskTime instanceSize DenseScoreTablePass.instanceSize
  nlinarith

theorem task_solved : Solves task program 3 taskTime need := by
  refine ⟨body 1 2, selection_in_program, ?_⟩
  intro R lim d x μ fr hpre hok
  have hfr : fr ≤ lim.space := by simpa only [need, add_zero] using hok.cells
  have hn : x.length ≤ instanceSize x := by
    unfold instanceSize DenseScoreTablePass.instanceSize
    omega
  have hheight : x.height ≤ (instanceSize x + 1) * (x.height + 1) + 1 := by nlinarith
  have hsum : x.length * x.height + 1 ≤ (instanceSize x + 1) * (x.height + 1) + 1 := by
    nlinarith
  have hone : 1 ≤ (instanceSize x + 1) * (x.height + 1) + 1 := by omega
  have hw := hok.word
  change ((((instanceSize x + 1) * (x.height + 1) + 1 : ℕ)) : ℤ) ≤ lim.word at hw
  have h1 : 1 ≤ lim.word :=
    (by exact_mod_cast hone : (1 : ℤ) ≤ ((instanceSize x + 1) * (x.height + 1) + 1 : ℕ)).trans hw
  have hh : (x.height : ℤ) ≤ lim.word :=
    (by exact_mod_cast hheight : (x.height : ℤ) ≤
      ((instanceSize x + 1) * (x.height + 1) + 1 : ℕ)).trans hw
  have hs : ((x.length * x.height + 1 : ℕ) : ℤ) ≤ lim.word :=
    (by exact_mod_cast hsum : ((x.length * x.height + 1 : ℕ) : ℤ) ≤
      ((instanceSize x + 1) * (x.height + 1) + 1 : ℕ)).trans hw
  have hd : d + 2 ≤ lim.depth := hok.depth
  change Ends lim (program ++ R) d (body 1 2)
    ⟨frame [x.candidates, x.length, x.height, x.activeBase,
      x.rowsBase, x.scoresBase, x.remainingBase, fr], μ⟩
    (taskTime (instanceSize x) x.height) _
  exact (ends (getElem?_append_of_eq_some table_in_program R)
    (getElem?_append_of_eq_some score_in_program R)
    (getElem?_append_of_eq_some argmin_in_program R)
    hpre.active_read hpre.rows_read hpre.rows_bound hpre.remaining_read hpre.nonempty
    hok.space h1 hh hs (hpre.active_below.trans hfr) (hpre.rows_below.trans hfr)
    (hpre.scores_below.trans hfr) (hpre.remaining_below.trans hfr) hfr
    hpre.active_separate hpre.rows_separate hpre.remaining_separate hd).mono
    (time_le_taskTime x) (fun _ h => h)

theorem need_polynomial : PolyNeed need := by
  unfold need
  poly_need []

theorem solvedIn : SolvedIn task (fun n _ => 62 * n + 37) := by
  refine ⟨program, 3, taskTime, need, need_polynomial, task_solved, ?_⟩
  intros
  simp only [taskTime, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, le_refl]

/-- The chosen candidate minimizes the actual active incidence multiplicity
sum, including the case in which every candidate has score zero. -/
theorem isArgmin_sums {active remaining : ℕ → Bool} {rows : ℕ → ℕ → ℕ} {P I chosen : ℕ}
    (h : DenseArgminPass.IsArgmin remaining (scores active rows I) P chosen) :
    chosen < P ∧ remaining chosen = true ∧ ∀ q < P, remaining q = true →
      (∑ i ∈ Finset.range I, if active i then rows chosen i else 0) ≤
        ∑ i ∈ Finset.range I, if active i then rows q i else 0 := by
  refine ⟨h.1, h.2.1, ?_⟩
  intro q hq hremaining
  simpa only [scores_eq_sum] using h.2.2 q hq hremaining

#print axioms ends
#print axioms time_le_taskTime
#print axioms task_solved
#print axioms need_polynomial
#print axioms solvedIn
#print axioms isArgmin_sums

end Selection

end Light.DenseScoreTablePass
