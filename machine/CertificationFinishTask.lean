import DenseCertificationFinish
import DenseArgminPass
import ThreeSumApsp.Lang.PolyBounded

/-!
A closed task for the actual three-pass certification program. The input
contains the current candidate mask, and its supplied pool argument is the
exact cardinality of that mask. The component uses this scalar; computing
it remains the responsibility of the enclosing controller. All arrays,
including the three output buffers, are charged in the instance size.
-/
namespace Light.DenseCertificationTask

open DenseCertificationFinish

/-- The free-pointer calling convention occupies the caller's otherwise
unused local 11. The first call overwrites that local, so this proof repeats
the execution derivation with its actual initial value rather than assuming
it is zero. -/
theorem ends_with_free {lim : Limits} {P : Program} {d pa pm ps : ℕ}
    (hpa : P[pa]? = some DenseAffirmativePass.body)
    (hpm : P[pm]? = some DenseMarkPass.body)
    (hps : P[ps]? = some DenseSurvivorPass.body)
    {μ : ℕ → ℤ} {active marked : ℕ → Bool} {owner base minima : ℕ → ℕ}
    {I Q pool lambda ab ob mb bb nb yb out fr : ℕ}
    (ha : ∀ i < I, μ (ab+i) = DenseAffirmativePass.bit (active i))
    (ho : ∀ i < I, μ (ob+i) = owner i)
    (hm : ∀ q < Q, μ (mb+q) = DenseMarkPass.bit (marked q))
    (hb : ∀ i < I, μ (bb+i) = base i)
    (hn : ∀ i < I, μ (nb+i) = minima i)
    (hq : ∀ i < I, owner i < Q)
    (hw : (lim.space : ℤ) ≤ lim.word) (h1 : 1 ≤ lim.word)
    (hpool : (pool : ℤ) ≤ lim.word) (hlambda : (lambda : ℤ) ≤ lim.word)
    (hbase : ∀ i < I, (base i : ℤ) ≤ lim.word)
    (hminima : ∀ i < I, (minima i : ℤ) ≤ lim.word)
    (hprodMin : ∀ i < I, ((pool*minima i : ℕ) : ℤ) ≤ lim.word)
    (hprodBase : ∀ i < I, ((lambda*base i : ℕ) : ℤ) ≤ lim.word)
    (hlayout : InOrder lim.space
      [(ab,I),(ob,I),(bb,I),(nb,I),(yb,I),(mb,Q),(out,I)])
    (hd : d < lim.depth) :
    Ends lim P d (body pa pm ps)
      ⟨frame [I,Q,pool,lambda,ab,ob,mb,bb,nb,yb,out,fr], μ⟩ (115*I+47)
      fun σ =>
        SameOutside3 μ σ.mem yb I mb Q out I ∧
        (∀ i < I, σ.mem (yb+i) = DenseAffirmativePass.bit
          (DenseAffirmativePass.affirmative active base minima pool lambda i)) ∧
        (∀ q < Q, σ.mem (mb+q) = DenseSurvivorPass.bit
          (markedAfter I active marked owner base minima pool lambda q)) ∧
        (∀ i < I, σ.mem (out+i) = DenseSurvivorPass.bit
          (DenseSurvivorPass.survives active
            (markedAfter I active marked owner base minima pool lambda)
            owner base minima pool lambda i)) := by
  rcases hlayout with ⟨hAO,hOB,hBN,hNY,hYM,hMO,hout⟩
  have hab : ab+I ≤ lim.space := by omega
  have hob : ob+I ≤ lim.space := by omega
  have hbb : bb+I ≤ lim.space := by omega
  have hnb : nb+I ≤ lim.space := by omega
  have hyb : yb+I ≤ lim.space := by omega
  have hmb : mb+Q ≤ lim.space := by omega
  unfold body
  refine Ends.callThen
    (DenseAffirmativePass.meets hpa ha hb hn hw h1 hpool hlambda hbase hminima
      hprodMin hprodBase hab hbb hnb hyb (by left; omega) (by left; omega) (by left; omega))
    ?_ (by light_side) hd (by light_time)
  rintro _ μ₁ ⟨same₁,yes₁⟩
  have ha₁ : ∀ i < I, μ₁ (ab+i) = DenseMarkPass.bit (active i) := by
    intro i hi
    exact (same₁ _ (by left; omega)).trans (ha i hi)
  have ho₁ : ∀ i < I, μ₁ (ob+i) = owner i := by
    intro i hi
    exact (same₁ _ (by left; omega)).trans (ho i hi)
  have hm₁ : ∀ q < Q, μ₁ (mb+q) = DenseMarkPass.bit (marked q) := by
    intro q hq'
    exact (same₁ _ (by right; omega)).trans (hm q hq')
  refine Ends.callThen
    (DenseMarkPass.meets_boolean hpm ha₁ yes₁ ho₁ hq hm₁ hw h1 hab hyb hob hmb
      (by left; omega) (by left; omega) (by left; omega))
    ?_ (by light_side) hd (by light_time)
  rintro _ μ₂ ⟨same₂,marks₂⟩
  have ha₂ : ∀ i < I, μ₂ (ab+i) = DenseSurvivorPass.bit (active i) := by
    intro i hi
    exact (same₂ _ (by left; omega)).trans (ha₁ i hi)
  have ho₂ : ∀ i < I, μ₂ (ob+i) = owner i := by
    intro i hi
    exact (same₂ _ (by left; omega)).trans (ho₁ i hi)
  have hb₂ : ∀ i < I, μ₂ (bb+i) = base i := by
    intro i hi
    exact (same₂ _ (by left; omega)).trans ((same₁ _ (by left; omega)).trans (hb i hi))
  have hn₂ : ∀ i < I, μ₂ (nb+i) = minima i := by
    intro i hi
    exact (same₂ _ (by left; omega)).trans ((same₁ _ (by left; omega)).trans (hn i hi))
  have hm₂ : ∀ q < Q, μ₂ (mb+q) = DenseSurvivorPass.bit
      (markedAfter I active marked owner base minima pool lambda q) := by
    intro q hq'
    rw [markedAfter_value]
    exact marks₂ q hq'
  refine Ends.callLast
    (DenseSurvivorPass.meets hps ha₂ ho₂ hm₂ hb₂ hn₂ hq hw h1 hpool hlambda hbase hminima
      hprodMin hprodBase hab hob hmb hbb hnb hout
      (by left; omega) (by left; omega) (by left; omega) (by left; omega) (by left; omega))
    ?_ (by light_side) hd (by light_time)
  rintro _ μ₃ ⟨same₃,kept₃⟩
  refine ⟨?_,?_,?_,kept₃⟩
  · intro x hx
    exact (same₃ x hx.2.2).trans ((same₂ x hx.2.1).trans (same₁ x hx.1))
  · intro i hi
    exact (same₃ _ (by left; omega)).trans ((same₂ _ (by left; omega)).trans (yes₁ i hi))
  · intro q hq'
    exact (same₃ _ (by left; omega)).trans (hm₂ q hq')


structure Instance where
  length : ℕ
  pairCount : ℕ
  candidates : ℕ
  height : ℕ
  lambda : ℕ
  remainingBase : ℕ
  activeBase : ℕ
  ownerBase : ℕ
  markBase : ℕ
  baseBase : ℕ
  minimaBase : ℕ
  yesBase : ℕ
  outBase : ℕ
  remaining : ℕ → Bool
  active : ℕ → Bool
  marked : ℕ → Bool
  owner : ℕ → ℕ
  base : ℕ → ℕ
  minima : ℕ → ℕ

def currentPool (x : Instance) : ℕ :=
  ((Finset.range x.candidates).filter (fun p => x.remaining p = true)).card

theorem currentPool_le (x : Instance) : currentPool x ≤ x.candidates := by
  exact (Finset.card_filter_le _ _).trans_eq (Finset.card_range _)

/-- Includes all six incidence vectors, pair marks and current candidate mask. -/
def instanceSize (x : Instance) : ℕ := 6*x.length + x.pairCount + x.candidates

def regions (x : Instance) : List (ℕ × ℕ) :=
  [(x.remainingBase,x.candidates),(x.activeBase,x.length),
   (x.ownerBase,x.length),(x.baseBase,x.length),(x.minimaBase,x.length),
   (x.yesBase,x.length),(x.markBase,x.pairCount),(x.outBase,x.length)]

structure Pre (x : Instance) (μ : ℕ → ℤ) (fr : ℕ) : Prop where
  remaining_read : ∀ p < x.candidates,
    μ (x.remainingBase+p) = DenseArgminPass.bit (x.remaining p)
  active_read : ∀ i < x.length,
    μ (x.activeBase+i) = DenseAffirmativePass.bit (x.active i)
  owner_read : ∀ i < x.length, μ (x.ownerBase+i) = x.owner i
  mark_read : ∀ q < x.pairCount,
    μ (x.markBase+q) = DenseMarkPass.bit (x.marked q)
  base_read : ∀ i < x.length, μ (x.baseBase+i) = x.base i
  minima_read : ∀ i < x.length, μ (x.minimaBase+i) = x.minima i
  owner_bound : ∀ i < x.length, x.owner i < x.pairCount
  base_bound : ∀ i < x.length, x.base i ≤ x.height
  minima_bound : ∀ i < x.length, x.minima i ≤ x.height
  lambda_bound : x.lambda ≤ x.height
  layout : InOrder fr (regions x)

def finalMarks (x : Instance) : ℕ → Bool :=
  markedAfter x.length x.active x.marked x.owner x.base x.minima (currentPool x) x.lambda

def Post (x : Instance) (μ : ℕ → ℤ) (_fr : ℕ) (_r : ℤ) (μ' : ℕ → ℤ) : Prop :=
  SameOutside3 μ μ' x.yesBase x.length x.markBase x.pairCount x.outBase x.length ∧
  (∀ i < x.length, μ' (x.yesBase+i) = DenseAffirmativePass.bit
    (DenseAffirmativePass.affirmative x.active x.base x.minima (currentPool x) x.lambda i)) ∧
  (∀ q < x.pairCount, μ' (x.markBase+q) = DenseSurvivorPass.bit (finalMarks x q)) ∧
  (∀ i < x.length, μ' (x.outBase+i) = DenseSurvivorPass.bit
    (DenseSurvivorPass.survives x.active (finalMarks x) x.owner x.base x.minima
      (currentPool x) x.lambda i))

def task : Task where
  Inst := Instance
  size := instanceSize
  bound x := x.height
  args x := [x.length,x.pairCount,currentPool x,x.lambda,x.activeBase,
    x.ownerBase,x.markBase,x.baseBase,x.minimaBase,x.yesBase,x.outBase]
  Pre := Pre
  Post := Post

abbrev program := DenseCertificationFinish.program

def need (n U : ℕ) : Need where
  word := (n+U+1)^2
  cells := 0
  depth := 1

def taskTime (n _U : ℕ) : ℕ := 115*n+47

theorem task_solved : Solves task program 3 taskTime need := by
  refine ⟨body 0 1 2, rfl, ?_⟩
  intro R lim d x μ fr hpre hok
  have hfr : fr ≤ lim.space := by simpa only [need, add_zero] using hok.cells
  have hn : x.length ≤ instanceSize x := by unfold instanceSize; omega
  have hp : currentPool x ≤ instanceSize x :=
    (currentPool_le x).trans (by unfold instanceSize; omega)
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
  have hd : d < lim.depth := by have := hok.depth; change d+1 ≤ lim.depth at this; omega
  change Ends lim (program ++ R) d (body 0 1 2)
    ⟨frame [x.length,x.pairCount,currentPool x,x.lambda,x.activeBase,
      x.ownerBase,x.markBase,x.baseBase,x.minimaBase,x.yesBase,x.outBase,fr],μ⟩
    (taskTime (instanceSize x) x.height) _
  exact (ends_with_free
    (P := program ++ R) (fr := fr)
    (getElem?_append_of_eq_some (show program[0]? = some DenseAffirmativePass.body from rfl) R)
    (getElem?_append_of_eq_some (show program[1]? = some DenseMarkPass.body from rfl) R)
    (getElem?_append_of_eq_some (show program[2]? = some DenseSurvivorPass.body from rfl) R)
    hpre.active_read hpre.owner_read hpre.mark_read hpre.base_read hpre.minima_read
    hpre.owner_bound hok.space h1 hpool hlambda hbase hmin hpm hpb hlayout hd).mono
      (by unfold taskTime; omega) (fun _ h => h)

theorem need_polynomial : PolyNeed need := by
  unfold need
  poly_need []

theorem solvedIn : SolvedIn task (fun n _ => 115*n+47) := by
  refine ⟨program,3,taskTime,need,need_polynomial,task_solved,?_⟩
  intros
  simp only [taskTime, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, le_refl]

/-- The supplied pool cardinality is the cardinality of the physical mask,
and that mask is preserved by every certified execution. -/
theorem remaining_preserved {x : Instance} {μ μ' : ℕ → ℤ} {fr : ℕ} {r : ℤ}
    (hpre : Pre x μ fr) (hpost : Post x μ fr r μ') :
    (∀ p < x.candidates, μ' (x.remainingBase+p) = DenseArgminPass.bit (x.remaining p)) ∧
    currentPool x = ((Finset.range x.candidates).filter (fun p => x.remaining p = true)).card := by
  refine ⟨?_,rfl⟩
  intro p hp
  rcases hpre.layout with ⟨hRA,hAO,hOB,hBN,hNY,hYM,hMO,_⟩
  exact (hpost.1 _ ⟨Or.inl (by omega),Or.inl (by omega),Or.inl (by omega)⟩).trans
    (hpre.remaining_read p hp)

#print axioms ends_with_free
#print axioms currentPool_le
#print axioms task_solved
#print axioms need_polynomial
#print axioms solvedIn
#print axioms remaining_preserved

end Light.DenseCertificationTask
