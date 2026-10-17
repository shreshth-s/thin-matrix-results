import DenseScoreTablePass
import DenseMinimumUpdatePass
import ThreeSumApsp.Lang.Calls

/-!
# One actual dense conditional-selection round

This finite Light caller scores the original active incidences for every
candidate, selects a minimum among the original remaining candidates, folds
the chosen row into the minima, and removes exactly that candidate. Argument
evaluation, calls, row-major address arithmetic, stores and the return are
included in the bound. Input layout and a nonempty current pool are explicit.
-/
namespace Light.DenseSelectionRound

abbrev Candidates : ℕ := 0
abbrev Len : ℕ := 1
abbrev Height : ℕ := 2
abbrev Active : ℕ := 3
abbrev Rows : ℕ := 4
abbrev Scores : ℕ := 5
abbrev Remaining : ℕ := 6
abbrev Minima : ℕ := 7
abbrev Free : ℕ := 8
abbrev Chosen : ℕ := 9
abbrev Unused : ℕ := 10

def body (selectionProc updateProc : ℕ) : Stmt :=
  .call selectionProc
    [v Candidates, v Len, v Height, v Active, v Rows, v Scores, v Remaining, v Free] Chosen ;;
  .call updateProc [v Len, v Rows +' v Chosen *' v Len, v Minima] Unused ;;
  .store (v Remaining +' v Chosen) (k 0) ;;
  .set Candidates (v Chosen)

def time (P I : ℕ) : ℕ := DenseScoreTablePass.Selection.time P I + 26 * I + 50

/-- The result refers to the original active mask, rows, minima and pool.
The three mutable buffers are the cached scores, minima and remaining flags. -/
def Result (μ : ℕ → ℤ) (active remaining : ℕ → Bool)
    (rows : ℕ → ℕ → ℕ) (initial : ℕ → ℕ) (P I sb mb rem : ℕ)
    (r : ℤ) (μ' : ℕ → ℤ) : Prop :=
  SameOutside3 μ μ' sb P mb I rem P ∧
  (∀ p < P, μ' (sb + p) = (DenseScoreTablePass.scores active rows I p : ℤ)) ∧
  ∃ chosen : ℕ, r = chosen ∧
    DenseArgminPass.IsArgmin remaining (DenseScoreTablePass.scores active rows I) P chosen ∧
    (∀ i < I, μ' (mb + i) = (min (initial i) (rows chosen i) : ℕ)) ∧
    (∀ p < P, μ' (rem + p) =
      DenseArgminPass.bit (if p = chosen then false else remaining p))

theorem ends {lim : Limits} {Prog : Program} {d sel table score argmin update : ℕ}
    (hsel : Prog[sel]? = some (DenseScoreTablePass.Selection.body table argmin))
    (htable : Prog[table]? = some (DenseScoreTablePass.body score))
    (hscore : Prog[score]? = some DenseScorePass.body)
    (hargmin : Prog[argmin]? = some DenseArgminPass.body)
    (hupdate : Prog[update]? = some DenseMinimumUpdatePass.body)
    {μ : ℕ → ℤ} {active remaining : ℕ → Bool} {rows : ℕ → ℕ → ℕ}
    {initial : ℕ → ℕ} {P I h ab rb sb rem mb fr : ℕ}
    (ha : ∀ i < I, μ (ab + i) = DenseScorePass.bit (active i))
    (hr : ∀ p < P, ∀ i < I, μ (rb + p * I + i) = rows p i)
    (hrow : ∀ p < P, ∀ i < I, rows p i ≤ h)
    (hrem : ∀ p < P, μ (rem + p) = DenseArgminPass.bit (remaining p))
    (hm : ∀ i < I, μ (mb + i) = initial i)
    (hinitial : ∀ i < I, initial i ≤ h)
    (hne : ∃ p, p < P ∧ remaining p = true)
    (hw : (lim.space : ℤ) ≤ lim.word) (h1 : 1 ≤ lim.word)
    (hh : (h : ℤ) ≤ lim.word) (hsentinel : ((I * h + 1 : ℕ) : ℤ) ≤ lim.word)
    (hlayout : InOrder lim.space [(ab,I),(rb,P*I),(sb,P),(mb,I),(rem,P)])
    (hfr : fr ≤ lim.space) (hdepth : d + 3 ≤ lim.depth) :
    Ends lim Prog d (body sel update)
      ⟨frame [P,I,h,ab,rb,sb,rem,mb,fr], μ⟩ (time P I)
      fun σ => Result μ active remaining rows initial P I sb mb rem (σ.loc 0) σ.mem := by
  rcases hlayout with ⟨hAR,hRS,hSM,hMR,hend⟩
  have hab : ab + I ≤ lim.space := by omega
  have hrb : rb + P * I ≤ lim.space := by omega
  have hsb : sb + P ≤ lim.space := by omega
  have hmb : mb + I ≤ lim.space := by omega
  have hSel : Meets lim Prog sel (d+1) [P,I,h,ab,rb,sb,rem,fr] μ
      (DenseScoreTablePass.Selection.time P I) (fun r μ' =>
        SameOutside μ μ' sb P ∧
        (∀ p < P, μ' (sb+p) = (DenseScoreTablePass.scores active rows I p : ℤ)) ∧
        ∃ chosen : ℕ, r = chosen ∧
          DenseArgminPass.IsArgmin remaining (DenseScoreTablePass.scores active rows I) P chosen) := by
    exact Meets.of_body hsel (DenseScoreTablePass.Selection.ends htable hscore hargmin
      ha hr hrow hrem hne hw h1 hh hsentinel hab hrb hsb hend hfr
      (by left; omega) (by left; omega) (by right; omega) (by omega))
  unfold body
  refine Ends.callToThen hSel (fun r μ₁ hselResult => ?_)
    (ha := by light_side) (hd := by omega) (hT := by light_time [time])
  obtain ⟨same₁,scores₁,chosen,rfl,hchosen⟩ := hselResult
  have hc : chosen < P := hchosen.1
  have hprod : (chosen + 1) * I ≤ P * I := Nat.mul_le_mul_right I hc
  have hr₁ : ∀ i < I, μ₁ (rb + chosen * I + i) = rows chosen i := by
    intro i hi
    have hpi : chosen * I + i < P * I := by nlinarith [hchosen.1]
    exact (same₁ _ (by left; omega)).trans (hr chosen hchosen.1 i hi)
  have hm₁ : ∀ i < I, μ₁ (mb+i) = initial i := by
    intro i hi
    exact (same₁ _ (by right; omega)).trans (hm i hi)
  have hchosenRow : rb + chosen * I + I ≤ lim.space := by
    have : (chosen + 1) * I ≤ P * I := Nat.mul_le_mul_right I hchosen.1
    nlinarith
  have hmul : ((chosen * I : ℕ) : ℤ) ≤ lim.word := by
    have : chosen * I ≤ P * I := Nat.mul_le_mul_right I hchosen.1.le
    omega
  have hrowbase : ((rb + chosen * I : ℕ) : ℤ) ≤ lim.word := by omega
  refine Ends.callToThen
    (DenseMinimumUpdatePass.meets hupdate hr₁ hm₁ (hrow chosen hchosen.1) hinitial
      hw hh hchosenRow hmb (by left; nlinarith))
    (fun _ μ₂ hupdateResult => ?_)
    (ha := by light_side [Nat.cast_add, Nat.cast_mul]) (hd := by omega)
    (hT := by light_time [time])
  obtain ⟨same₂,minima₂⟩ := hupdateResult
  have hchosenAddr : rem + chosen < lim.space := by omega
  have hchosenWord : (chosen : ℤ) ≤ lim.word := by omega
  light_store (rem + chosen) (0 : ℤ) using time
  light_set (chosen : ℤ) using time
  change Result μ active remaining rows initial P I sb mb rem (chosen : ℤ)
    (Function.update μ₂ (rem + chosen) 0)
  refine ⟨?_,?_,chosen,rfl,hchosen,?_,?_⟩
  · intro x hx
    rw [Function.update_of_ne (by rcases hx.2.2 with h | h <;> omega)]
    exact (same₂ x hx.2.1).trans (same₁ x hx.1)
  · intro p hp
    rw [Function.update_of_ne (by omega)]
    exact (same₂ _ (by left; omega)).trans (scores₁ p hp)
  · intro i hi
    rw [Function.update_of_ne (by omega)]
    exact (minima₂ i hi).1
  · intro p hp
    by_cases heq : p = chosen
    · subst p
      simp [DenseArgminPass.bit]
    · rw [if_neg heq, Function.update_of_ne (by omega)]
      exact (same₂ _ (by right; omega)).trans
        ((same₁ _ (by right; omega)).trans (hrem p hp))

/-- All callees are included in this fixed finite Light program. -/
def program : Program :=
  [DenseScorePass.body, DenseScoreTablePass.body 0, DenseArgminPass.body,
    DenseScoreTablePass.Selection.body 1 2, DenseMinimumUpdatePass.body, body 3 4]

/-- A closed operational contract: the premises describe the current input
and admissible machine resources, with no solver or execution premise. -/
theorem meets {lim : Limits} {d : ℕ}
    {μ : ℕ → ℤ} {active remaining : ℕ → Bool} {rows : ℕ → ℕ → ℕ}
    {initial : ℕ → ℕ} {P I h ab rb sb rem mb fr : ℕ}
    (ha : ∀ i < I, μ (ab + i) = DenseScorePass.bit (active i))
    (hr : ∀ p < P, ∀ i < I, μ (rb + p * I + i) = rows p i)
    (hrow : ∀ p < P, ∀ i < I, rows p i ≤ h)
    (hrem : ∀ p < P, μ (rem + p) = DenseArgminPass.bit (remaining p))
    (hm : ∀ i < I, μ (mb + i) = initial i)
    (hinitial : ∀ i < I, initial i ≤ h)
    (hne : ∃ p, p < P ∧ remaining p = true)
    (hw : (lim.space : ℤ) ≤ lim.word) (h1 : 1 ≤ lim.word)
    (hh : (h : ℤ) ≤ lim.word) (hsentinel : ((I * h + 1 : ℕ) : ℤ) ≤ lim.word)
    (hlayout : InOrder lim.space [(ab,I),(rb,P*I),(sb,P),(mb,I),(rem,P)])
    (hfr : fr ≤ lim.space) (hdepth : d + 3 ≤ lim.depth) :
    Meets lim program 5 d [P,I,h,ab,rb,sb,rem,mb,fr] μ (time P I)
      (Result μ active remaining rows initial P I sb mb rem) := by
  exact Meets.of_body rfl (ends (Prog:=program) rfl rfl rfl rfl rfl
    ha hr hrow hrem hm hinitial hne hw h1 hh hsentinel hlayout hfr hdepth)

/-- The displayed count includes every caller operation, with a constant
allowance for the two calls, row indexing, the flag store and the return. -/
theorem time_eq (P I : ℕ) :
    time P I = 22 * P * I + 62 * P + 26 * I + 87 := by
  unfold time DenseScoreTablePass.Selection.time DenseScoreTablePass.time
  ring

structure Instance where
  candidates : ℕ
  length : ℕ
  height : ℕ
  activeBase : ℕ
  rowsBase : ℕ
  scoresBase : ℕ
  remainingBase : ℕ
  minimaBase : ℕ
  active : ℕ → Bool
  remaining : ℕ → Bool
  rows : ℕ → ℕ → ℕ
  initial : ℕ → ℕ

def instanceSize (x : Instance) : ℕ :=
  x.candidates * x.length + 2 * x.candidates + 2 * x.length

structure Pre (x : Instance) (μ : ℕ → ℤ) (fr : ℕ) : Prop where
  active_read : ∀ i < x.length,
    μ (x.activeBase+i) = DenseScorePass.bit (x.active i)
  rows_read : ∀ p < x.candidates, ∀ i < x.length,
    μ (x.rowsBase+p*x.length+i) = x.rows p i
  rows_bound : ∀ p < x.candidates, ∀ i < x.length, x.rows p i ≤ x.height
  remaining_read : ∀ p < x.candidates,
    μ (x.remainingBase+p) = DenseArgminPass.bit (x.remaining p)
  minima_read : ∀ i < x.length, μ (x.minimaBase+i) = x.initial i
  minima_bound : ∀ i < x.length, x.initial i ≤ x.height
  nonempty : ∃ p, p < x.candidates ∧ x.remaining p = true
  layout : InOrder fr [(x.activeBase,x.length),
    (x.rowsBase,x.candidates*x.length),(x.scoresBase,x.candidates),
    (x.minimaBase,x.length),(x.remainingBase,x.candidates)]

def task : Task where
  Inst := Instance
  size := instanceSize
  bound x := x.height
  args x := [x.candidates,x.length,x.height,x.activeBase,x.rowsBase,
    x.scoresBase,x.remainingBase,x.minimaBase]
  Pre := Pre
  Post x μ _ := Result μ x.active x.remaining x.rows x.initial
    x.candidates x.length x.scoresBase x.minimaBase x.remainingBase

def need (n U : ℕ) : Need where
  word := (n+1)*(U+1)+1
  cells := 0
  depth := 3

def taskTime (n _U : ℕ) : ℕ := 31*n+87

theorem time_le_taskTime (x : Instance) :
    time x.candidates x.length ≤ taskTime (instanceSize x) x.height := by
  rw [time_eq]
  unfold taskTime instanceSize
  nlinarith

/-- This round has a closed solver contract for every appended program.
The minima postcondition is the selected-row update; it does not assert a
minimum over every still-remaining candidate. -/
theorem task_solved : Solves task program 5 taskTime need := by
  refine ⟨body 3 4, rfl, ?_⟩
  intro R lim d x μ fr hpre hok
  have hfr : fr ≤ lim.space := by simpa only [need, add_zero] using hok.cells
  have hn : x.length ≤ instanceSize x := by unfold instanceSize; omega
  have hheight : x.height ≤ (instanceSize x+1)*(x.height+1)+1 := by nlinarith
  have hsum : x.length*x.height+1 ≤ (instanceSize x+1)*(x.height+1)+1 := by
    nlinarith
  have hone : 1 ≤ (instanceSize x+1)*(x.height+1)+1 := by omega
  have hw := hok.word
  change (((instanceSize x+1)*(x.height+1)+1 : ℕ) : ℤ) ≤ lim.word at hw
  have h1 : 1 ≤ lim.word :=
    (by exact_mod_cast hone : (1 : ℤ) ≤ ((instanceSize x+1)*(x.height+1)+1 : ℕ)).trans hw
  have hh : (x.height : ℤ) ≤ lim.word :=
    (by exact_mod_cast hheight : (x.height : ℤ) ≤
      ((instanceSize x+1)*(x.height+1)+1 : ℕ)).trans hw
  have hs : ((x.length*x.height+1 : ℕ) : ℤ) ≤ lim.word :=
    (by exact_mod_cast hsum : ((x.length*x.height+1 : ℕ) : ℤ) ≤
      ((instanceSize x+1)*(x.height+1)+1 : ℕ)).trans hw
  have hd : d+3 ≤ lim.depth := hok.depth
  have hlayout : InOrder lim.space [(x.activeBase,x.length),
      (x.rowsBase,x.candidates*x.length),(x.scoresBase,x.candidates),
      (x.minimaBase,x.length),(x.remainingBase,x.candidates)] := by
    rcases hpre.layout with ⟨h₁,h₂,h₃,h₄,h₅⟩
    exact ⟨h₁,h₂,h₃,h₄,h₅.trans hfr⟩
  change Ends lim (program++R) d (body 3 4)
    ⟨frame [x.candidates,x.length,x.height,x.activeBase,x.rowsBase,
      x.scoresBase,x.remainingBase,x.minimaBase,fr], μ⟩
    (taskTime (instanceSize x) x.height) _
  exact (ends
    (getElem?_append_of_eq_some (show program[3]? = some (DenseScoreTablePass.Selection.body 1 2) from rfl) R)
    (getElem?_append_of_eq_some (show program[1]? = some (DenseScoreTablePass.body 0) from rfl) R)
    (getElem?_append_of_eq_some (show program[0]? = some DenseScorePass.body from rfl) R)
    (getElem?_append_of_eq_some (show program[2]? = some DenseArgminPass.body from rfl) R)
    (getElem?_append_of_eq_some (show program[4]? = some DenseMinimumUpdatePass.body from rfl) R)
    hpre.active_read hpre.rows_read hpre.rows_bound hpre.remaining_read
    hpre.minima_read hpre.minima_bound hpre.nonempty hok.space h1 hh hs hlayout hfr hd).mono
    (time_le_taskTime x) (fun _ h => h)

theorem need_polynomial : PolyNeed need := by
  unfold need
  poly_need []

theorem solvedIn : SolvedIn task (fun n _ => 31*n+87) := by
  refine ⟨program, 5, taskTime, need, need_polynomial, task_solved, ?_⟩
  intros
  simp only [taskTime, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, le_refl]

end Light.DenseSelectionRound

#print axioms Light.DenseSelectionRound.ends
#print axioms Light.DenseSelectionRound.meets

#print axioms Light.DenseSelectionRound.time_eq
#print axioms Light.DenseSelectionRound.time_le_taskTime
#print axioms Light.DenseSelectionRound.task_solved
#print axioms Light.DenseSelectionRound.need_polynomial
#print axioms Light.DenseSelectionRound.solvedIn
