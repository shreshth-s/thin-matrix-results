import CertificationFinishTask
import ThreeSumApsp.Lang.ToMachine

/-!
A fixed RAM instruction list for the actual three-pass certification finish.
The twelve-cell header supplies the exact current-pool cardinality specified
by the physical remaining-candidate mask. The component does not calculate
that cardinality or establish the number-theoretic meaning of its count
arrays. Those are obligations of the enclosing controller.
-/
namespace ThinMatrix.CertificationFinishMachine

open Light ThreeSumApsp ThreeSumApsp.WordRam
open Light.DenseCertificationTask

abbrev Instance := DenseCertificationTask.Instance

def header (x : Instance) (fr : ℕ) : List ℤ :=
  [x.length,x.pairCount,currentPool x,x.lambda,x.activeBase,x.ownerBase,
    x.markBase,x.baseBase,x.minimaBase,x.yesBase,x.outBase,fr]

def Header (x : Instance) (μ : ℕ → ℤ) (fr : ℕ) : Prop :=
  ∀ i < 12, μ i = (header x fr).getD i 0

def topBody : Stmt :=
  .call 3 [M (k 0),M (k 1),M (k 2),M (k 3),M (k 4),M (k 5),
    M (k 6),M (k 7),M (k 8),M (k 9),M (k 10),M (k 11)] 0

def program : Light.Program := DenseCertificationTask.program ++ [topBody]

theorem top_in_program : program[4]? = some topBody := rfl

def limits (x : Instance) (fr : ℕ) : Limits where
  word := ((need (instanceSize x) x.height).word + fr + 12 : ℕ)
  space := fr
  depth := 3

def resourceSize (x : Instance) (fr : ℕ) : ℕ := instanceSize x+x.height+fr+12

theorem need_ok (x : Instance) (fr : ℕ) :
    (need (instanceSize x) x.height).Ok (limits x fr) fr 2 := by
  constructor <;> simp only [limits,need] <;> omega

theorem small (x : Instance) (fr : ℕ) : Small 0 2 [resourceSize x fr] (limits x fr) := by
  constructor
  · simp only [limits]
    positivity
  · change ((((instanceSize x+x.height+1)^2+fr+12 : ℕ)) : ℤ) ≤ _
    norm_num [polyBound]
    exact_mod_cast (show (instanceSize x+x.height+1)^2+fr+12 ≤
      (resourceSize x fr+1)^2 by
        have hmul : fr+12 ≤ (fr+12)*(2*(instanceSize x+x.height+1)+fr+12) :=
          Nat.le_mul_of_pos_right _ (by omega)
        calc
          _ ≤ (instanceSize x+x.height+1)^2+
              (fr+12)*(2*(instanceSize x+x.height+1)+fr+12) := by omega
          _ = _ := by unfold resourceSize; ring)
  · norm_num [limits,polyBound]
    have hpow : resourceSize x fr+1 ≤ (resourceSize x fr+1)^2 :=
      Nat.le_self_pow (by decide) _
    have hfr : fr ≤ resourceSize x fr+1 := by unfold resourceSize; omega
    exact_mod_cast (hfr.trans hpow)
  · norm_num [limits,polyBound]
    have hpow : resourceSize x fr+1 ≤ (resourceSize x fr+1)^2 :=
      Nat.le_self_pow (by decide) _
    have hh : 3 ≤ resourceSize x fr+1 := by unfold resourceSize; omega
    exact_mod_cast (hh.trans hpow)

theorem top_meets {x : Instance} {μ : ℕ → ℤ} {fr : ℕ}
    (hheader : Header x μ fr) (hpre : Pre x μ fr) (hfr : 12 ≤ fr) :
    Meets (limits x fr) program 4 1 [0,0] μ (taskTime (instanceSize x) x.height+26)
      (task.Post x μ fr) := by
  have h0 : μ 0 = x.length := by simpa [header] using hheader 0 (by omega)
  have h1 : μ 1 = x.pairCount := by simpa [header] using hheader 1 (by omega)
  have h2 : μ 2 = currentPool x := by simpa [header] using hheader 2 (by omega)
  have h3 : μ 3 = x.lambda := by simpa [header] using hheader 3 (by omega)
  have h4 : μ 4 = x.activeBase := by simpa [header] using hheader 4 (by omega)
  have h5 : μ 5 = x.ownerBase := by simpa [header] using hheader 5 (by omega)
  have h6 : μ 6 = x.markBase := by simpa [header] using hheader 6 (by omega)
  have h7 : μ 7 = x.baseBase := by simpa [header] using hheader 7 (by omega)
  have h8 : μ 8 = x.minimaBase := by simpa [header] using hheader 8 (by omega)
  have h9 : μ 9 = x.yesBase := by simpa [header] using hheader 9 (by omega)
  have h10 : μ 10 = x.outBase := by simpa [header] using hheader 10 (by omega)
  have h11 : μ 11 = fr := by simpa [header] using hheader 11 (by omega)
  rcases hpre.layout with ⟨hRA,hAO,hOB,hBN,hNY,hYM,hMO,hout⟩
  have hi : x.length ≤ fr := by omega
  have hq : x.pairCount ≤ fr := by omega
  have hp : currentPool x ≤ fr := (currentPool_le x).trans (by omega)
  have ha : x.activeBase ≤ fr := by omega
  have ho : x.ownerBase ≤ fr := by omega
  have hm : x.markBase ≤ fr := by omega
  have hb : x.baseBase ≤ fr := by omega
  have hn : x.minimaBase ≤ fr := by omega
  have hy : x.yesBase ≤ fr := by omega
  have houtb : x.outBase ≤ fr := by omega
  have hf : (fr : ℤ) ≤ (limits x fr).word := by simp only [limits]; omega
  have hl : (x.lambda : ℤ) ≤ (limits x fr).word := by
    have hpow : x.height ≤ (instanceSize x+x.height+1)^2 := by
      have : instanceSize x+x.height+1 ≤ (instanceSize x+x.height+1)^2 :=
        Nat.le_self_pow (by decide) _
      omega
    change (x.lambda : ℤ) ≤ ((((instanceSize x+x.height+1)^2+fr+12 : ℕ)) : ℤ)
    exact_mod_cast (show x.lambda ≤ (instanceSize x+x.height+1)^2+fr+12 by
      have := hpre.lambda_bound
      omega)
  refine Meets.of_body top_in_program ?_
  unfold topBody
  refine Ends.callTo (task_solved.meets [topBody] x fr hpre (need_ok x fr))
    (fun _ _ h => h)
    (ha := by light_side [task,limits,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11])
    (hd := by simp [limits]) (hT := by light_time [task])

def sourceTime (x : Instance) : ℕ := taskTime (instanceSize x) x.height+30

theorem main_execution {x : Instance} {μ : ℕ → ℤ} {fr : ℕ}
    (hheader : Header x μ fr) (hpre : Pre x μ fr) (hfr : 12 ≤ fr) :
    ∃ σ' c, Light.Exec (limits x fr) program 0 (mainStmt 4)
      ⟨frame [0,0,0],μ⟩ σ' c ∧ c ≤ sourceTime x ∧
      task.Post x μ fr (σ'.loc 0) σ'.mem := by
  have hmain : Ends (limits x fr) program 0 (mainStmt 4) ⟨frame [0,0,0],μ⟩
      (sourceTime x) (fun σ => task.Post x μ fr (σ.loc 0) σ.mem) := by
    exact Ends.callTo (top_meets hheader hpre hfr) (fun _ _ h => h)
      (hd := by simp [limits]) (hT := by light_time [sourceTime])
  exact hmain

def compiled : List EndStatement.Instr := compileProgram program 4 false

def slope : ℕ := slopeOf program false 0 2 1

def workspace : ℕ := Light.Compiler.lowCell program false ⟨0,0,3⟩

theorem lowCell_eq (x : Instance) (fr : ℕ) :
    Light.Compiler.lowCell program false (limits x fr) = workspace := rfl

/-- Actual compiled execution with complete flag semantics, the exact
current-pool scalar, preserved input mask and explicit workspace framing.
There is no solver or execution premise. -/
theorem compiled_execution {x : Instance} {μ : ℕ → ℤ} {fr W : ℕ} {m : ℤ → BitVec W}
    (hheader : Header x μ fr) (hpre : Pre x μ fr) (hfr : 12 ≤ fr)
    (hinput : Light.Compiler.Input (limits x fr) μ 0 0 m)
    (hadm : Admissible slope [resourceSize x fr] W) :
    ∃ m' : ℤ → BitVec W,
      EndStatement.exec compiled (ramSteps program false (sourceTime x)) 0 m = some (true,m') ∧
      (∀ i < x.length, output m' x.yesBase i = DenseAffirmativePass.bit
        (DenseAffirmativePass.affirmative x.active x.base x.minima (currentPool x) x.lambda i)) ∧
      (∀ q < x.pairCount, output m' x.markBase q = DenseSurvivorPass.bit (finalMarks x q)) ∧
      (∀ i < x.length, output m' x.outBase i = DenseSurvivorPass.bit
        (DenseSurvivorPass.survives x.active (finalMarks x) x.owner x.base x.minima
          (currentPool x) x.lambda i)) ∧
      (∀ p < x.candidates, output m' x.remainingBase p = DenseArgminPass.bit (x.remaining p)) ∧
      (∀ a : ℕ, Outside x.yesBase x.length a ∧ Outside x.markBase x.pairCount a ∧
        Outside x.outBase x.length a → output m' 0 a = μ a) ∧
      (∀ a : ℤ, a < -(workspace : ℤ) ∨ (fr : ℤ) ≤ a → m' a = m a) := by
  obtain ⟨σ',c,hexec,hc,hpost⟩ := main_execution hheader hpre hfr
  have hfit := fits_of_small program false (small x fr) hadm (by simp) le_rfl
  obtain ⟨m',hrun,hout⟩ := Light.Compiler.compileProgram_correct (dec := false) hexec hfit hinput
  have hremaining := (remaining_preserved (r := σ'.loc 0) hpre hpost).1
  obtain ⟨hkeep,hyes,hmark,hsurvivor⟩ := hpost
  refine ⟨m',?_,?_,?_,?_,?_,?_,?_⟩
  · change EndStatement.exec (compileProgram program 4 false) _ _ _ = _
    apply exec_mono (c := ⟨0,m⟩) (by simpa only [verdictOf,Bool.not_false,Bool.true_or] using hrun)
    exact Nat.add_le_add_left (Nat.mul_le_mul_left _ hc) _
  · intro i hi
    rw [hout.holds.output hfit]
    exact hyes i hi
  · intro q hq
    rw [hout.holds.output hfit]
    exact hmark q hq
  · intro i hi
    rw [hout.holds.output hfit]
    exact hsurvivor i hi
  · intro p hp
    rw [hout.holds.output hfit]
    exact hremaining p hp
  · intro a ha
    rw [hout.holds.output hfit]
    simpa only [Nat.zero_add] using hkeep a ha
  · intro a ha
    apply hout.far a
    change a < -(Light.Compiler.lowCell program false (limits x fr) : ℤ) ∨ (fr : ℤ) ≤ a
    simpa only [lowCell_eq] using ha

theorem compiled_time_bound (x : Instance) :
    (ramSteps program false (sourceTime x) : ℝ) ≤
      (timeConst program false : ℝ)*(115*instanceSize x+77)+timeConst program false := by
  have heq : (sourceTime x : ℝ) = 115*instanceSize x+77 := by
    simp only [sourceTime,taskTime,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
    ring
  simpa only [heq] using ramSteps_le program false (sourceTime x)

#print axioms need_ok
#print axioms small
#print axioms top_meets
#print axioms main_execution
#print axioms lowCell_eq
#print axioms compiled_execution
#print axioms compiled_time_bound

end ThinMatrix.CertificationFinishMachine
