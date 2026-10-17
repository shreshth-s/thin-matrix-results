import DenseArgminPass
import ThreeSumApsp.Lang.PolyBounded

/-! Actual per-incidence minima over the remaining pool. Every column scan
visits every candidate and consults its Boolean mask, independently of the
aggregate-score argmin. No solver callback or uncharged table operation occurs. -/
namespace Light.DensePoolMinimumPass

abbrev minimum (remaining : ℕ → Bool) (rows : ℕ → ℕ → ℕ)
    (H P i : ℕ) : ℕ :=
  (DenseArgminPass.scan remaining (fun p => rows p i) H P).2

def IsMinimum (remaining : ℕ → Bool) (rows : ℕ → ℕ → ℕ)
    (P i value : ℕ) : Prop :=
  (∃ p, p < P ∧ remaining p = true ∧ value = rows p i) ∧
    ∀ p < P, remaining p = true → value ≤ rows p i

theorem minimum_spec {remaining : ℕ → Bool} {rows : ℕ → ℕ → ℕ}
    {H P i : ℕ} (hrow : ∀ p < P, rows p i ≤ H)
    (hne : ∃ p, p < P ∧ remaining p = true) :
    IsMinimum remaining rows P i (minimum remaining rows H P i) ∧
      minimum remaining rows H P i ≤ H := by
  obtain ⟨_, hwitness, hlower⟩ :=
    DenseArgminPass.scan_spec (remaining := remaining) hrow P le_rfl
  dsimp only at hwitness hlower
  rcases hwitness with ⟨hsentinel, _⟩ | ⟨hp, hr, hs⟩
  · obtain ⟨p, hp, hr⟩ := hne
    have := hlower p hp hr
    have := hrow p hp
    change IsMinimum remaining rows P i _ ∧ _
    omega
  · refine ⟨⟨⟨_, hp, hr, hs⟩, hlower⟩, ?_⟩
    change (DenseArgminPass.scan remaining (fun p => rows p i) H P).2 ≤ H
    rw [hs]
    exact hrow _ hp

namespace Column
abbrev Candidates : ℕ := 0
abbrev Len : ℕ := 1
abbrev Height : ℕ := 2
abbrev Remain : ℕ := 3
abbrev Rows : ℕ := 4
abbrev Incidence : ℕ := 5
abbrev Candidate : ℕ := 6
abbrev Best : ℕ := 7

def roundBody : Stmt :=
  .ite (M (v Remain +' v Candidate) =' k 1)
    (.ite (M (v Rows +' v Candidate *' v Len +' v Incidence) <' v Best)
      (.set Best (M (v Rows +' v Candidate *' v Len +' v Incidence))) .skip)
    .skip

def body : Stmt :=
  .set Best (v Height +' k 1) ;;
  .for Candidate (v Candidates) roundBody ;;
  .set Candidates (v Best)

theorem round_cost : roundBody.blockCost = 27 := by rfl

def time (P : ℕ) : ℕ := 35 * P + 12

theorem loop_ends {lim : Limits} {Prog : Program} {d : ℕ}
    {μ : ℕ → ℤ} {remaining : ℕ → Bool} {rows : ℕ → ℕ → ℕ}
    {P I H rem rb i : ℕ}
    (hrem : ∀ p < P, μ (rem + p) = DenseArgminPass.bit (remaining p))
    (hr : ∀ p < P, μ (rb + p * I + i) = rows p i)
    (hrow : ∀ p < P, rows p i ≤ H) (hi : i < I)
    (hw : (lim.space : ℤ) ≤ lim.word) (h1 : 1 ≤ lim.word)
    (hsentinel : ((H + 1 : ℕ) : ℤ) ≤ lim.word)
    (hremb : rem + P ≤ lim.space) (hrb : rb + P * I ≤ lim.space) :
    Ends lim Prog d (.for Candidate (v Candidates) roundBody)
      ⟨frame [P, I, H, rem, rb, i, 0, H + 1], μ⟩ (35 * P + 6)
      (fun σ => σ = ⟨frame [P, I, H, rem, rb, i, P,
        minimum remaining rows H P i], μ⟩) := by
  refine Ends.for
    (fun j σ => σ = ⟨frame [P, I, H, rem, rb, i, j,
      minimum remaining rows H j i], μ⟩)
    P roundBody.blockCost ?start ?round ?done ?bound
    (hn := by omega) (hT := by simp [round_cost]; omega)
  case start => simp [update_frame_setLocal, minimum, DenseArgminPass.scan]
  case round =>
    intro p σ hp _ hσ
    subst σ
    have hrr := hrem p hp
    have hrs := hr p hp
    have hrsC : μ ((↑rb + ↑p * ↑I + ↑i : ℤ).toNat) = rows p i := by
      simpa only [← Nat.cast_mul, ← Nat.cast_add, Int.toNat_natCast] using hrs
    have hrowaddr : rb + p * I + i < lim.space := by
      have : (p + 1) * I ≤ P * I := Nat.mul_le_mul_right I (by omega)
      nlinarith
    have hproduct : p * I ≤ lim.space := by omega
    have hwordScore : (rows p i : ℤ) ≤ lim.word := by
      have := hrow p hp
      omega
    unfold roundBody
    refine Ends.iteLast (fun hcR => ?_) (fun hcR => ?_) (by light_side)
    · have hR : remaining p = true := by simpa [hrr] using hcR
      refine Ends.iteLast (fun hcS => ?_) (fun hcS => ?_) (by light_side)
      · have hS : rows p i < minimum remaining rows H p i := by
          exact_mod_cast (show (rows p i : ℤ) < minimum remaining rows H p i by
            simpa [hrsC] using hcS)
        have hnext : minimum remaining rows H (p + 1) i = rows p i := by
          simp [minimum, DenseArgminPass.scan, hR, hS]
        refine Ends.setTo (rows p i : ℕ) ?_
          (by light_side [hrsC]) (by light_time)
        exact ⟨by simp, by simp [update_frame_setLocal, Nat.cast_add, hnext]⟩
      · have hS : ¬ rows p i < minimum remaining rows H p i := by
          intro hh
          apply hcS
          have : (rows p i : ℤ) < minimum remaining rows H p i := by exact_mod_cast hh
          simpa [hrsC] using this
        have hnext : minimum remaining rows H (p + 1) i = minimum remaining rows H p i := by
          simp [minimum, DenseArgminPass.scan, hS]
        apply Ends.skip
        exact ⟨by simp, by simp [update_frame_setLocal, Nat.cast_add, hnext]⟩
    · have hR : remaining p ≠ true := by simpa [hrr] using hcR
      have hnext : minimum remaining rows H (p + 1) i = minimum remaining rows H p i := by
        simp [minimum, DenseArgminPass.scan, hR]
      apply Ends.skip
      exact ⟨by simp, by simp [update_frame_setLocal, Nat.cast_add, hnext]⟩
  case done =>
    intro σ _ hσ
    exact hσ
  case bound =>
    intro p σ hp _ hσ
    subst σ
    light_side

theorem ends {lim : Limits} {Prog : Program} {d : ℕ}
    {μ : ℕ → ℤ} {remaining : ℕ → Bool} {rows : ℕ → ℕ → ℕ}
    {P I H rem rb i : ℕ}
    (hrem : ∀ p < P, μ (rem + p) = DenseArgminPass.bit (remaining p))
    (hr : ∀ p < P, μ (rb + p * I + i) = rows p i)
    (hrow : ∀ p < P, rows p i ≤ H) (hi : i < I)
    (hw : (lim.space : ℤ) ≤ lim.word) (h1 : 1 ≤ lim.word)
    (hsentinel : ((H + 1 : ℕ) : ℤ) ≤ lim.word)
    (hremb : rem + P ≤ lim.space) (hrb : rb + P * I ≤ lim.space) :
    Ends lim Prog d body ⟨frame [P, I, H, rem, rb, i], μ⟩ (time P)
      (fun σ => σ.loc 0 = minimum remaining rows H P i ∧ σ.mem = μ) := by
  unfold body time
  refine Ends.setToThen (H + 1 : ℕ) ?_ (by light_side) (by light_time)
  refine Ends.next (35 * P + 6) ?_ (by light_time)
  refine (loop_ends hrem hr hrow hi hw h1 hsentinel hremb hrb).mono le_rfl ?_
  intro σ hσ
  subst σ
  refine Ends.setTo (minimum remaining rows H P i : ℕ) ?_ (by light_side) (by light_time)
  exact ⟨by simp, rfl⟩

theorem meets {lim : Limits} {Prog : Program} {d proc : ℕ}
    (hbody : Prog[proc]? = some body)
    {μ : ℕ → ℤ} {remaining : ℕ → Bool} {rows : ℕ → ℕ → ℕ}
    {P I H rem rb i : ℕ}
    (hrem : ∀ p < P, μ (rem + p) = DenseArgminPass.bit (remaining p))
    (hr : ∀ p < P, μ (rb + p * I + i) = rows p i)
    (hrow : ∀ p < P, rows p i ≤ H) (hi : i < I)
    (hw : (lim.space : ℤ) ≤ lim.word) (h1 : 1 ≤ lim.word)
    (hsentinel : ((H + 1 : ℕ) : ℤ) ≤ lim.word)
    (hremb : rem + P ≤ lim.space) (hrb : rb + P * I ≤ lim.space) :
    Meets lim Prog proc d [P, I, H, rem, rb, i] μ (time P) fun result μ' =>
      result = minimum remaining rows H P i ∧ μ' = μ :=
  .of_body hbody (ends hrem hr hrow hi hw h1 hsentinel hremb hrb)
end Column

abbrev Candidates : ℕ := 0
abbrev Len : ℕ := 1
abbrev Height : ℕ := 2
abbrev Remain : ℕ := 3
abbrev Rows : ℕ := 4
abbrev Out : ℕ := 5
abbrev Incidence : ℕ := 6
abbrev Result : ℕ := 7

def roundBody (columnProc : ℕ) : Stmt :=
  .call columnProc [v Candidates, v Len, v Height, v Remain, v Rows, v Incidence] Result ;;
  .store (v Out +' v Incidence) (v Result)

def body (columnProc : ℕ) : Stmt := .for Incidence (v Len) (roundBody columnProc)

def time (P I : ℕ) : ℕ := I * (35 * P + 33) + 6

/-- The output vector is the only memory region modified. The trailing frame
cell is unrestricted and can be the free pointer appended by a task contract. -/
theorem ends {lim : Limits} {Prog : Program} {d columnProc : ℕ}
    (hcolumn : Prog[columnProc]? = some Column.body)
    {μ : ℕ → ℤ} {remaining : ℕ → Bool} {rows : ℕ → ℕ → ℕ}
    {P I H rem rb out : ℕ} (fr : ℤ)
    (hrem : ∀ p < P, μ (rem + p) = DenseArgminPass.bit (remaining p))
    (hr : ∀ p < P, ∀ i < I, μ (rb + p * I + i) = rows p i)
    (hrow : ∀ p < P, ∀ i < I, rows p i ≤ H)
    (hw : (lim.space : ℤ) ≤ lim.word) (h1 : 1 ≤ lim.word)
    (hsentinel : ((H + 1 : ℕ) : ℤ) ≤ lim.word)
    (hremb : rem + P ≤ lim.space) (hrb : rb + P * I ≤ lim.space)
    (hout : out + I ≤ lim.space)
    (hsepRem : Apart rem P out I) (hsepRows : Apart rb (P * I) out I)
    (hdepth : d < lim.depth) :
    Ends lim Prog d (body columnProc) ⟨frame [P, I, H, rem, rb, out, fr], μ⟩
      (time P I) fun σ =>
        σ.mem = wrote μ out (fun i => (minimum remaining rows H P i : ℤ)) I := by
  unfold body time
  refine Ends.forShape
    (fun i (z : ℤ) μ' => ⟨frame [P, I, H, rem, rb, out, i, z], μ'⟩)
    (fun i μ' => μ' = wrote μ out (fun i => (minimum remaining rows H P i : ℤ)) i)
    I (35 * P + 25) 0 wrote_zero.symm ?round ?done
    (first := by
      simp only [update_frame_setLocal, setLocal]
      congr 1
      exact (frame_append_zeros [P, I, H, rem, rb, out, 0] 1).symm)
    (hn := by omega) (hT := by simp only [Expr.cost]; ring_nf; omega)
  case round =>
    intro i z μ' hi hμ
    have hrm : ∀ p < P, μ' (rem + p) = DenseArgminPass.bit (remaining p) := by
      intro p hp
      rw [hμ, wrote_rest (by rcases hsepRem with hs | hs <;> omega)]
      exact hrem p hp
    have hrp : ∀ p < P, μ' (rb + p * I + i) = rows p i := by
      intro p hp
      have hpi : p * I + i < P * I := by nlinarith
      rw [hμ, wrote_rest (by rcases hsepRows with hs | hs <;> omega)]
      exact hr p hp i hi
    have hrowi : ∀ p < P, rows p i ≤ H := fun p hp => hrow p hp i hi
    have hval : (minimum remaining rows H P i : ℤ) ≤ lim.word := by
      have hb := (DenseArgminPass.scan_spec (remaining := remaining) hrowi P le_rfl).1
      change minimum remaining rows H P i ≤ H + 1 at hb
      exact (by exact_mod_cast hb : (minimum remaining rows H P i : ℤ) ≤
        (H + 1 : ℕ)).trans hsentinel
    unfold roundBody
    refine Ends.callToThen
      (Column.meets hcolumn hrm hrp hrowi hi hw h1 hsentinel hremb hrb)
      (fun result μ'' hresult => ?_)
      (ha := by light_side) (hd := hdepth) (hT := by light_time [Column.time])
    obtain ⟨hresult, rfl⟩ := hresult
    subst result
    light_store (out + i) (minimum remaining rows H P i : ℕ) using Column.time
    refine ⟨(minimum remaining rows H P i : ℤ),
      Function.update μ'' (out + i) (minimum remaining rows H P i : ℤ), ?_, ?_⟩
    · rfl
    · rw [hμ]
      exact wrote_succ
  case done =>
    intro z μ' hμ
    exact hμ

theorem meets {lim : Limits} {Prog : Program} {d proc columnProc : ℕ}
    (hbody : Prog[proc]? = some (body columnProc))
    (hcolumn : Prog[columnProc]? = some Column.body)
    {μ : ℕ → ℤ} {remaining : ℕ → Bool} {rows : ℕ → ℕ → ℕ}
    {P I H rem rb out : ℕ} (fr : ℤ)
    (hrem : ∀ p < P, μ (rem + p) = DenseArgminPass.bit (remaining p))
    (hr : ∀ p < P, ∀ i < I, μ (rb + p * I + i) = rows p i)
    (hrow : ∀ p < P, ∀ i < I, rows p i ≤ H)
    (hne : ∃ p, p < P ∧ remaining p = true)
    (hw : (lim.space : ℤ) ≤ lim.word) (h1 : 1 ≤ lim.word)
    (hsentinel : ((H + 1 : ℕ) : ℤ) ≤ lim.word)
    (hremb : rem + P ≤ lim.space) (hrb : rb + P * I ≤ lim.space)
    (hout : out + I ≤ lim.space)
    (hsepRem : Apart rem P out I) (hsepRows : Apart rb (P * I) out I)
    (hdepth : d < lim.depth) :
    Meets lim Prog proc d [P, I, H, rem, rb, out, fr] μ (time P I) fun _ μ' =>
      SameOutside μ μ' out I ∧ ∀ i < I,
        μ' (out + i) = (minimum remaining rows H P i : ℤ) ∧
        IsMinimum remaining rows P i (minimum remaining rows H P i) ∧
        minimum remaining rows H P i ≤ H := by
  refine .of_body hbody ?_
  refine (ends hcolumn fr hrem hr hrow hw h1 hsentinel hremb hrb hout
    hsepRem hsepRows hdepth).mono le_rfl ?_
  intro σ hσ
  rw [hσ]
  refine ⟨sameOutside_wrote le_rfl, ?_⟩
  intro i hi
  exact ⟨wrote_done hi, minimum_spec (fun p hp => hrow p hp i hi) hne⟩


structure Instance where
  candidates : ℕ
  length : ℕ
  height : ℕ
  remainingBase : ℕ
  rowsBase : ℕ
  minimaBase : ℕ
  remaining : ℕ → Bool
  rows : ℕ → ℕ → ℕ

def instanceSize (x : Instance) : ℕ :=
  x.candidates * x.length + x.candidates + x.length

structure Pre (x : Instance) (μ : ℕ → ℤ) (fr : ℕ) : Prop where
  remaining_read : ∀ p < x.candidates,
    μ (x.remainingBase + p) = DenseArgminPass.bit (x.remaining p)
  rows_read : ∀ p < x.candidates, ∀ i < x.length,
    μ (x.rowsBase + p * x.length + i) = x.rows p i
  rows_bound : ∀ p < x.candidates, ∀ i < x.length, x.rows p i ≤ x.height
  remaining_below : x.remainingBase + x.candidates ≤ fr
  rows_below : x.rowsBase + x.candidates * x.length ≤ fr
  minima_below : x.minimaBase + x.length ≤ fr
  remaining_separate : Apart x.remainingBase x.candidates x.minimaBase x.length
  rows_separate : Apart x.rowsBase (x.candidates * x.length) x.minimaBase x.length
  nonempty : ∃ p, p < x.candidates ∧ x.remaining p = true

/-- This closed task is deliberately scoped to a nonempty remaining pool.
The internal scanner's empty-pool value is the sentinel H+1, not a claim
about the canonical algorithm's separately handled empty-pool convention. -/
def task : Task where
  Inst := Instance
  size := instanceSize
  bound x := x.height
  args x := [x.candidates, x.length, x.height, x.remainingBase, x.rowsBase, x.minimaBase]
  Pre := Pre
  Post x μ _ _ μ' := SameOutside μ μ' x.minimaBase x.length ∧
    ∀ i < x.length,
      μ' (x.minimaBase + i) = (minimum x.remaining x.rows x.height x.candidates i : ℤ) ∧
      IsMinimum x.remaining x.rows x.candidates i
        (minimum x.remaining x.rows x.height x.candidates i) ∧
      minimum x.remaining x.rows x.height x.candidates i ≤ x.height

def need (n U : ℕ) : Need where
  word := (n + 1) * (U + 1) + 1
  cells := 0
  depth := 1

def taskTime (n _U : ℕ) : ℕ := 35 * n + 6

/-- A fixed finite program: procedure zero scans one column and procedure
one loops over all incidences. Only the supplied minima array is modified. -/
def program : Program := [Column.body, body 0]

theorem column_in_program : program[0]? = some Column.body := rfl

theorem table_in_program : program[1]? = some (body 0) := rfl

theorem time_le_taskTime (x : Instance) :
    time x.candidates x.length ≤ taskTime (instanceSize x) x.height := by
  unfold time taskTime instanceSize
  nlinarith

theorem task_solved : Solves task program 1 taskTime need := by
  refine ⟨body 0, table_in_program, ?_⟩
  intro R lim d x μ fr hpre hok
  have hfr : fr ≤ lim.space := by simpa only [need, add_zero] using hok.cells
  have hsentinel : x.height + 1 ≤ (instanceSize x + 1) * (x.height + 1) + 1 := by
    nlinarith
  have hone : 1 ≤ (instanceSize x + 1) * (x.height + 1) + 1 := by omega
  have hw := hok.word
  change ((((instanceSize x + 1) * (x.height + 1) + 1 : ℕ)) : ℤ) ≤ lim.word at hw
  have h1 : 1 ≤ lim.word :=
    (by exact_mod_cast hone : (1 : ℤ) ≤
      ((instanceSize x + 1) * (x.height + 1) + 1 : ℕ)).trans hw
  have hs : ((x.height + 1 : ℕ) : ℤ) ≤ lim.word :=
    (by exact_mod_cast hsentinel : ((x.height + 1 : ℕ) : ℤ) ≤
      ((instanceSize x + 1) * (x.height + 1) + 1 : ℕ)).trans hw
  have hd : d < lim.depth := by
    have := hok.depth
    change d + 1 ≤ lim.depth at this
    omega
  change Ends lim (program ++ R) d (body 0)
    ⟨frame [x.candidates, x.length, x.height, x.remainingBase,
      x.rowsBase, x.minimaBase, fr], μ⟩
    (taskTime (instanceSize x) x.height) _
  refine (ends (getElem?_append_of_eq_some column_in_program R) (fr : ℤ)
    hpre.remaining_read hpre.rows_read hpre.rows_bound hok.space h1 hs
    (hpre.remaining_below.trans hfr) (hpre.rows_below.trans hfr)
    (hpre.minima_below.trans hfr) hpre.remaining_separate hpre.rows_separate hd).mono
    (time_le_taskTime x) ?_
  intro σ hσ
  change SameOutside μ σ.mem x.minimaBase x.length ∧ _
  rw [hσ]
  refine ⟨sameOutside_wrote le_rfl, ?_⟩
  intro i hi
  exact ⟨wrote_done hi,
    minimum_spec (fun p hp => hpre.rows_bound p hp i hi) hpre.nonempty⟩

theorem need_polynomial : PolyNeed need := by
  unfold need
  poly_need []

theorem solvedIn : SolvedIn task (fun n _ => 35 * n + 6) := by
  refine ⟨program, 1, taskTime, need, need_polynomial, task_solved, ?_⟩
  intros
  simp only [taskTime, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, le_refl]

theorem task_solved_append (R : Program) : Solves task (program ++ R) 1 taskTime need :=
  task_solved.append R

#print axioms minimum_spec
#print axioms Column.loop_ends
#print axioms Column.ends
#print axioms Column.meets
#print axioms ends
#print axioms meets
#print axioms time_le_taskTime
#print axioms task_solved
#print axioms need_polynomial
#print axioms solvedIn
#print axioms task_solved_append

end Light.DensePoolMinimumPass
