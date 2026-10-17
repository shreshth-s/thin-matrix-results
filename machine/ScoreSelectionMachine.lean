import DenseScoreTablePass
import ThreeSumApsp.Lang.ToMachine

/-!
# A compiled score-selection RAM component

A fixed top procedure reads the eight-cell metadata header and calls the
closed score-selection solver. The pinned verified compiler supplies an
actual word-RAM execution, its time bound and its workspace bound. Input
data must satisfy the ordinary header, array-layout and word-representation
contracts; no solver or execution hypothesis is assumed.
-/

namespace ThinMatrix.ScoreSelectionMachine

open Light ThreeSumApsp ThreeSumApsp.WordRam
open Light.DenseScoreTablePass

abbrev Instance := Selection.Instance

def header (x : Instance) (fr : ℕ) : List ℤ :=
  [x.candidates, x.length, x.height, x.activeBase,
    x.rowsBase, x.scoresBase, x.remainingBase, fr]

def Header (x : Instance) (μ : ℕ → ℤ) (fr : ℕ) : Prop :=
  ∀ i < 8, μ i = (header x fr).getD i 0

/-- The compiler's main entry takes two arguments. This top procedure uses
the fixed metadata header in cells 0 through 7 instead. -/
def topBody : Stmt :=
  .call 3 [M (k 0), M (k 1), M (k 2), M (k 3),
    M (k 4), M (k 5), M (k 6), M (k 7)] 0

def program : Light.Program := Selection.program ++ [topBody]

theorem top_in_program : program[4]? = some topBody := rfl

def limits (x : Instance) (fr : ℕ) : Limits where
  word := ((Selection.need (Selection.instanceSize x) x.height).word + fr + 8 : ℕ)
  space := fr
  depth := 4

def resourceSize (x : Instance) (fr : ℕ) : ℕ :=
  Selection.instanceSize x + x.height + fr + 8

theorem need_ok (x : Instance) (fr : ℕ) :
    (Selection.need (Selection.instanceSize x) x.height).Ok (limits x fr) fr 2 := by
  constructor <;> simp only [limits, Selection.need] <;> omega

theorem small (x : Instance) (fr : ℕ) : Small 0 2 [resourceSize x fr] (limits x fr) := by
  have hn : Selection.instanceSize x ≤ resourceSize x fr := by unfold resourceSize; omega
  have hh : x.height ≤ resourceSize x fr := by unfold resourceSize; omega
  have hf : fr + 8 ≤ resourceSize x fr := by unfold resourceSize; omega
  constructor
  · simp only [limits]
    positivity
  · change (((Selection.instanceSize x + 1) * (x.height + 1) + 1 + fr + 8 : ℕ) : ℤ) ≤ _
    norm_num [polyBound]
    exact_mod_cast (show (Selection.instanceSize x + 1) * (x.height + 1) + 1 + fr + 8 ≤
      (resourceSize x fr + 1)^2 by unfold resourceSize; nlinarith)
  · norm_num [limits, polyBound]
    nlinarith
  · norm_num [limits, polyBound]
    nlinarith

theorem top_meets {x : Instance} {μ : ℕ → ℤ} {fr : ℕ}
    (hheader : Header x μ fr) (hpre : Selection.Pre x μ fr) (hfr : 8 ≤ fr) :
    Meets (limits x fr) program 4 1 [0, 0] μ
      (Selection.taskTime (Selection.instanceSize x) x.height + 18)
      (Selection.task.Post x μ fr) := by
  have h0 : μ 0 = x.candidates := by simpa [header] using hheader 0 (by omega)
  have h1 : μ 1 = x.length := by simpa [header] using hheader 1 (by omega)
  have h2 : μ 2 = x.height := by simpa [header] using hheader 2 (by omega)
  have h3 : μ 3 = x.activeBase := by simpa [header] using hheader 3 (by omega)
  have h4 : μ 4 = x.rowsBase := by simpa [header] using hheader 4 (by omega)
  have h5 : μ 5 = x.scoresBase := by simpa [header] using hheader 5 (by omega)
  have h6 : μ 6 = x.remainingBase := by simpa [header] using hheader 6 (by omega)
  have h7 : μ 7 = fr := by simpa [header] using hheader 7 (by omega)
  have hc : x.candidates ≤ fr := by have := hpre.scores_below; omega
  have hi : x.length ≤ fr := by have := hpre.active_below; omega
  have ha : x.activeBase ≤ fr := by have := hpre.active_below; omega
  have hr : x.rowsBase ≤ fr := by have := hpre.rows_below; omega
  have hs : x.scoresBase ≤ fr := by have := hpre.scores_below; omega
  have hm : x.remainingBase ≤ fr := by have := hpre.remaining_below; omega
  have hf : (fr : ℤ) ≤ (limits x fr).word := by simp only [limits]; omega
  have hh : (x.height : ℤ) ≤ (limits x fr).word := by
    have : x.height ≤ (Selection.instanceSize x + 1) * (x.height + 1) + 1 + fr + 8 := by
      nlinarith
    change (x.height : ℤ) ≤ (((Selection.instanceSize x + 1) * (x.height + 1) + 1 + fr + 8 : ℕ) : ℤ)
    exact_mod_cast this
  refine Meets.of_body top_in_program ?_
  unfold topBody
  refine Ends.callTo
    (Selection.task_solved.meets [topBody] x fr hpre (need_ok x fr))
    (fun _ _ h => h)
    (ha := by light_side [Selection.task, limits, h0, h1, h2, h3, h4, h5, h6, h7])
    (hd := by simp [limits]) (hT := by light_time [Selection.task])

def sourceTime (x : Instance) : ℕ :=
  Selection.taskTime (Selection.instanceSize x) x.height + 22

theorem main_execution {x : Instance} {μ : ℕ → ℤ} {fr : ℕ}
    (hheader : Header x μ fr) (hpre : Selection.Pre x μ fr) (hfr : 8 ≤ fr) :
    ∃ σ' c, Light.Exec (limits x fr) program 0 (mainStmt 4)
      ⟨frame [0, 0, 0], μ⟩ σ' c ∧ c ≤ sourceTime x ∧
        Selection.task.Post x μ fr (σ'.loc 0) σ'.mem := by
  have hmain : Ends (limits x fr) program 0 (mainStmt 4)
      ⟨frame [0, 0, 0], μ⟩ (sourceTime x)
      (fun σ => Selection.task.Post x μ fr (σ.loc 0) σ.mem) := by
    exact Ends.callTo (top_meets hheader hpre hfr) (fun _ _ h => h)
      (hd := by simp [limits]) (hT := by light_time [sourceTime])
  exact hmain

def compiled : List EndStatement.Instr := compileProgram program 4 false

def slope : ℕ := slopeOf program false 0 2 1

/-- The compiled program uses a fixed number of negative cells: every run
has at most the four source-language call levels specified above. -/
def workspace : ℕ := Light.Compiler.lowCell program false ⟨0, 0, 4⟩

theorem lowCell_eq (x : Instance) (fr : ℕ) :
    Light.Compiler.lowCell program false (limits x fr) = workspace := rfl

/-- Actual RAM execution at every admissible word size, with the chosen
index in the compiler result cell and all cached scores in the output array.
Only the score vector and fixed negative compiler workspace may change. -/
theorem compiled_execution {x : Instance} {μ : ℕ → ℤ} {fr W : ℕ} {m : ℤ → BitVec W}
    (hheader : Header x μ fr) (hpre : Selection.Pre x μ fr) (hfr : 8 ≤ fr)
    (hinput : Light.Compiler.Input (limits x fr) μ 0 0 m)
    (hadm : Admissible slope [resourceSize x fr] W) :
    ∃ (m' : ℤ → BitVec W) (chosen : ℕ),
      EndStatement.exec compiled (ramSteps program false (sourceTime x)) 0 m = some (true, m') ∧
      (m' Light.Compiler.cRESULT).toInt = chosen ∧
      DenseArgminPass.IsArgmin x.remaining (scores x.active x.rows x.length) x.candidates chosen ∧
      (∀ p < x.candidates, output m' x.scoresBase p = (scores x.active x.rows x.length p : ℤ)) ∧
      (∀ a : ℕ, a < x.scoresBase ∨ x.scoresBase + x.candidates ≤ a → output m' 0 a = μ a) ∧
      (∀ a : ℤ, a < -(workspace : ℤ) ∨ (fr : ℤ) ≤ a → m' a = m a) := by
  obtain ⟨σ', c, hexec, hc, hpost⟩ := main_execution hheader hpre hfr
  have hfit := fits_of_small program false (small x fr) hadm (by simp) le_rfl
  obtain ⟨m', hrun, hout⟩ := Light.Compiler.compileProgram_correct (dec := false) hexec hfit hinput
  obtain ⟨hkeep, hscores, chosen, hchosen, hargmin⟩ := hpost
  refine ⟨m', chosen, ?_, hout.result.trans hchosen, hargmin, ?_, ?_, ?_⟩
  · change EndStatement.exec (compileProgram program 4 false) _ _ _ = _
    apply exec_mono (c := ⟨0, m⟩) (by simpa only [verdictOf, Bool.not_false, Bool.true_or] using hrun)
    exact Nat.add_le_add_left (Nat.mul_le_mul_left _ hc) _
  · intro p hp
    rw [hout.holds.output hfit]
    exact hscores p hp
  · intro a ha
    rw [hout.holds.output hfit]
    simpa only [Nat.zero_add] using hkeep a ha
  · intro a ha
    apply hout.far a
    change a < -(Light.Compiler.lowCell program false (limits x fr) : ℤ) ∨ (fr : ℤ) ≤ a
    simpa only [lowCell_eq] using ha

theorem compiled_time_bound (x : Instance) :
    (ramSteps program false (sourceTime x) : ℝ) ≤
      (timeConst program false : ℝ) * (62 * Selection.instanceSize x + 59) +
        timeConst program false := by
  have heq : (sourceTime x : ℝ) = 62 * Selection.instanceSize x + 59 := by
    simp only [sourceTime, Selection.taskTime, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    ring
  simpa only [heq] using ramSteps_le program false (sourceTime x)

#print axioms need_ok
#print axioms small
#print axioms top_meets
#print axioms main_execution
#print axioms lowCell_eq
#print axioms compiled_execution
#print axioms compiled_time_bound

end ThinMatrix.ScoreSelectionMachine
