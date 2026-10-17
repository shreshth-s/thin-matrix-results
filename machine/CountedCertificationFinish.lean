import DensePoolPass
import CertificationFinishTask

/-!
# Certification with an actually computed current-pool count

This fixed finite Light program first scans the physical remaining-candidate
mask, then runs affirmative flags, pair marking and survivor filtering with
that returned cardinality. The calling convention contains no pool scalar.
Both calls, all arguments and every callee step are charged. This is a
controller component, not a complete min-plus solver.
-/

namespace Light.CountedCertificationFinish

abbrev Instance := DenseCertificationTask.Instance
abbrev Pre := DenseCertificationTask.Pre
abbrev Post := DenseCertificationTask.Post
abbrev instanceSize := DenseCertificationTask.instanceSize
abbrev currentPool := DenseCertificationTask.currentPool

/-- The first eleven locals retain the three-pass convention, with local 2
now holding the candidate-vector length. Locals 11 and 12 are its base and
the free pointer. The returned, freshly counted pool occupies local 13. -/
def body (poolProc finishProc : ℕ) : Stmt :=
  .call poolProc [v 2, v 11, v 12] 13 ;;
  .call finishProc [v 0, v 1, v 13, v 3, v 4, v 5, v 6, v 7,
    v 8, v 9, v 10, v 12] 0

def args (x : Instance) : List ℤ :=
  [x.length,x.pairCount,x.candidates,x.lambda,x.activeBase,
   x.ownerBase,x.markBase,x.baseBase,x.minimaBase,x.yesBase,x.outBase,x.remainingBase]

def time (P I : ℕ) : ℕ := 19*P + 115*I + 76

/-- The actual programs for all called routines precede the wrapper. -/
def program : Program :=
  DenseCertificationFinish.program ++ [DensePoolPass.body, body 4 3]

theorem pool_in_program : program[4]? = some DensePoolPass.body := rfl

theorem body_in_program : program[5]? = some (body 4 3) := rfl

def need (n U : ℕ) : Need where
  word := (n+U+1)^2
  cells := 0
  depth := 2

/-- The sharp three-pass bound specialized to the mask-based input, with
all word and layout preconditions derived from the task's polynomial need. -/
theorem finish_meets {lim : Limits} {d : ℕ} (R : Program)
    (x : Instance) (μ : ℕ → ℤ) (fr : ℕ)
    (hpre : Pre x μ fr)
    (hok : (need (instanceSize x) x.height).Ok lim fr d) :
    Meets lim (program ++ R) 3 (d+1)
      (DenseCertificationTask.task.args x ++ [(fr : ℤ)]) μ (115*x.length+47)
      (Post x μ fr) := by
  have hfr : fr ≤ lim.space := by simpa only [need, add_zero] using hok.cells
  have hp : currentPool x ≤ instanceSize x :=
    (DenseCertificationTask.currentPool_le x).trans (by unfold instanceSize DenseCertificationTask.instanceSize; omega)
  have hword := hok.word
  change (((instanceSize x+x.height+1)^2 : ℕ) : ℤ) ≤ lim.word at hword
  have hlift : ∀ a : ℕ, a ≤ (instanceSize x+x.height+1)^2 → (a : ℤ) ≤ lim.word := by
    intro a ha
    exact (by exact_mod_cast ha : (a : ℤ) ≤ ((instanceSize x+x.height+1)^2 : ℕ)).trans hword
  have htotal : 1 ≤ instanceSize x+x.height+1 := by omega
  have hsq : instanceSize x+x.height+1 ≤ (instanceSize x+x.height+1)^2 :=
    Nat.le_self_pow (by decide) _
  have h1 : (1 : ℤ) ≤ lim.word := hlift 1 (htotal.trans hsq)
  have hpool : (currentPool x : ℤ) ≤ lim.word := hlift _ ((hp.trans (by omega)).trans hsq)
  have hlambda : (x.lambda : ℤ) ≤ lim.word := hlift _ (by have := hpre.lambda_bound; nlinarith)
  have hbase : ∀ i < x.length, (x.base i : ℤ) ≤ lim.word := by
    intro i hi
    exact hlift _ (by have := hpre.base_bound i hi; nlinarith)
  have hmin : ∀ i < x.length, (x.minima i : ℤ) ≤ lim.word := by
    intro i hi
    exact hlift _ (by have := hpre.minima_bound i hi; nlinarith)
  have hpm : ∀ i < x.length, ((currentPool x*x.minima i : ℕ) : ℤ) ≤ lim.word := by
    intro i hi
    apply hlift
    have hprod := Nat.mul_le_mul hp (hpre.minima_bound i hi)
    nlinarith
  have hpb : ∀ i < x.length, ((x.lambda*x.base i : ℕ) : ℤ) ≤ lim.word := by
    intro i hi
    apply hlift
    have hprod := Nat.mul_le_mul hpre.lambda_bound (hpre.base_bound i hi)
    nlinarith
  have hlayout : InOrder lim.space
      [(x.activeBase,x.length),(x.ownerBase,x.length),(x.baseBase,x.length),
       (x.minimaBase,x.length),(x.yesBase,x.length),(x.markBase,x.pairCount),
       (x.outBase,x.length)] := by
    rcases hpre.layout with ⟨_,hAO,hOB,hBN,hNY,hYM,hMO,hout⟩
    exact ⟨hAO,hOB,hBN,hNY,hYM,hMO,hout.trans hfr⟩
  have hd : d+1 < lim.depth := by
    have := hok.depth
    change d+2 ≤ lim.depth at this
    omega
  refine Meets.of_body (show (program ++ R)[3]? = some (DenseCertificationFinish.body 0 1 2) from
    getElem?_append_of_eq_some (show program[3]? = some (DenseCertificationFinish.body 0 1 2) from rfl) R) ?_
  exact DenseCertificationTask.ends_with_free
    (P := program ++ R) (fr := fr)
    (getElem?_append_of_eq_some (show program[0]? = some DenseAffirmativePass.body from rfl) R)
    (getElem?_append_of_eq_some (show program[1]? = some DenseMarkPass.body from rfl) R)
    (getElem?_append_of_eq_some (show program[2]? = some DenseSurvivorPass.body from rfl) R)
    hpre.active_read hpre.owner_read hpre.mark_read hpre.base_read hpre.minima_read
    hpre.owner_bound hok.space h1 hpool hlambda hbase hmin hpm hpb hlayout hd

/-- Closed execution for the wrapper, with no correctness or execution
hypothesis for either callee. Its only hypotheses concern physical inputs,
layout and representable words. -/
theorem ends {lim : Limits} {d : ℕ} (R : Program)
    (x : Instance) (μ : ℕ → ℤ) (fr : ℕ)
    (hpre : Pre x μ fr)
    (hok : (need (instanceSize x) x.height).Ok lim fr d) :
    Ends lim (program ++ R) d (body 4 3) ⟨frame (args x ++ [(fr : ℤ)]),μ⟩
      (time x.candidates x.length)
      (fun σ => Post x μ fr (σ.loc 0) σ.mem) := by
  have hfr : fr ≤ lim.space := by simpa only [need, add_zero] using hok.cells
  have hword := hok.word
  change (((instanceSize x+x.height+1)^2 : ℕ) : ℤ) ≤ lim.word at hword
  have hsq : instanceSize x+x.height+1 ≤ (instanceSize x+x.height+1)^2 :=
    Nat.le_self_pow (by decide) _
  have hPsize : x.candidates ≤ instanceSize x := by
    unfold instanceSize DenseCertificationTask.instanceSize
    omega
  have h1 : (1 : ℤ) ≤ lim.word := by
    have hh : 1 ≤ (instanceSize x+x.height+1)^2 := (by omega : 1 ≤ instanceSize x+x.height+1).trans hsq
    exact (by exact_mod_cast hh : (1 : ℤ) ≤ ((instanceSize x+x.height+1)^2 : ℕ)).trans hword
  have hP : (x.candidates : ℤ) ≤ lim.word := by
    have hh : x.candidates ≤ (instanceSize x+x.height+1)^2 := (hPsize.trans (by omega)).trans hsq
    exact (by exact_mod_cast hh : (x.candidates : ℤ) ≤ ((instanceSize x+x.height+1)^2 : ℕ)).trans hword
  have hrb : x.remainingBase+x.candidates ≤ lim.space := by
    rcases hpre.layout with ⟨hRA,hAO,hOB,hBN,hNY,hYM,hMO,hout⟩
    omega
  have hd : d < lim.depth := by have := hok.depth; change d+2 ≤ lim.depth at this; omega
  have hcount : ∀ j < x.candidates, μ (x.remainingBase+j) = DensePoolPass.bit (x.remaining j) := by
    intro j hj
    exact hpre.remaining_read j hj
  unfold body time
  refine Ends.callToThen
    (DensePoolPass.meets (getElem?_append_of_eq_some pool_in_program R)
      (fr : ℤ) hcount hok.space h1 hP hrb)
    ?_ (ha := by light_side [args]) (hd := hd) (hT := by light_time [DensePoolPass.time])
  rintro r μ' ⟨hcountResult,rfl⟩
  have hcard : r = (currentPool x : ℤ) := by
    rw [hcountResult, DensePoolPass.count_eq_card]
    rfl
  clear hcountResult
  subst r
  have hcardBound := DenseCertificationTask.currentPool_le x
  change currentPool x ≤ x.candidates at hcardBound
  refine Ends.callLast (finish_meets R x μ' fr hpre hok) ?_
    (ha := by light_side [args, DenseCertificationTask.task, currentPool]) (hd := hd)
    (hT := by light_time [DensePoolPass.time])
  intro r μ'' hpost
  exact hpost

theorem meets {lim : Limits} {d : ℕ} (R : Program)
    (x : Instance) (μ : ℕ → ℤ) (fr : ℕ)
    (hpre : Pre x μ fr)
    (hok : (need (instanceSize x) x.height).Ok lim fr d) :
    Meets lim (program ++ R) 5 d (args x ++ [(fr : ℤ)]) μ
      (time x.candidates x.length) (Post x μ fr) := by
  exact Meets.of_body (getElem?_append_of_eq_some body_in_program R) (ends R x μ fr hpre hok)

def task : Task where
  Inst := Instance
  size := instanceSize
  bound x := x.height
  args := args
  Pre := Pre
  Post := Post

def taskTime (n _U : ℕ) : ℕ := 115*n+76

theorem time_le_taskTime (x : Instance) :
    time x.candidates x.length ≤ taskTime (instanceSize x) x.height := by
  unfold time taskTime instanceSize DenseCertificationTask.instanceSize
  omega

theorem task_solved : Solves task program 5 taskTime need := by
  refine ⟨body 4 3, body_in_program, ?_⟩
  intro R lim d x μ fr hpre hok
  exact (ends R x μ fr hpre hok).mono (time_le_taskTime x) (fun _ h => h)

theorem need_polynomial : PolyNeed need := by
  unfold need
  poly_need []

theorem solvedIn : SolvedIn task (fun n _ => 115*n+76) := by
  refine ⟨program,5,taskTime,need,need_polynomial,task_solved,?_⟩
  intros
  simp only [taskTime, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, le_refl]

theorem task_solved_append (R : Program) : Solves task (program ++ R) 5 taskTime need :=
  task_solved.append R

/-- The count used for both threshold comparisons comes from the preserved
physical candidate mask, even when that mask has no remaining member. -/
theorem remaining_preserved {x : Instance} {μ μ' : ℕ → ℤ} {fr : ℕ} {r : ℤ}
    (hpre : Pre x μ fr) (hpost : Post x μ fr r μ') :
    ∀ p < x.candidates, μ' (x.remainingBase+p) = DensePoolPass.bit (x.remaining p) :=
  (DenseCertificationTask.remaining_preserved hpre hpost).1

#print axioms finish_meets
#print axioms ends
#print axioms meets
#print axioms time_le_taskTime
#print axioms task_solved
#print axioms need_polynomial
#print axioms solvedIn
#print axioms task_solved_append
#print axioms remaining_preserved

end Light.CountedCertificationFinish
