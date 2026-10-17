import DenseAffirmativePass
import DenseMarkPass
import DenseSurvivorPass
import ThreeSumApsp.Lang.Calls

/-!
An actual Light composition of the three certification passes.  The scratch
YES array, in-place pair marks and separate survivor array have one explicit
ordered layout.  The time includes evaluation of all call arguments and the
three call instructions; the three callee bounds alone are not the total.
-/
namespace Light.DenseCertificationFinish

abbrev Len : ℕ := 0
abbrev PairCount : ℕ := 1
abbrev Pool : ℕ := 2
abbrev Lambda : ℕ := 3
abbrev Active : ℕ := 4
abbrev Owner : ℕ := 5
abbrev Mark : ℕ := 6
abbrev Base : ℕ := 7
abbrev Minima : ℕ := 8
abbrev Yes : ℕ := 9
abbrev Out : ℕ := 10
abbrev Unused : ℕ := 11

def body (pa pm ps : ℕ) : Stmt :=
  .call pa [v Len, v Pool, v Lambda, v Active, v Base, v Minima, v Yes] Unused ;;
  .call pm [v Len, v PairCount, v Active, v Yes, v Owner, v Mark] Unused ;;
  .call ps [v Len, v PairCount, v Pool, v Lambda, v Active, v Owner,
    v Mark, v Base, v Minima, v Out] Unused

/-- A fixed finite program: three kernels followed by their caller. -/
def program : Program :=
  [DenseAffirmativePass.body, DenseMarkPass.body, DenseSurvivorPass.body, body 0 1 2]

/-- Existential witnesses range over the original incidence table. -/
def markedAfter (I : ℕ) (active marked : ℕ → Bool) (owner base minima : ℕ → ℕ)
    (pool lambda q : ℕ) : Bool :=
  marked q || decide (∃ i : Fin I,
    DenseMarkPass.Qualifies active
      (DenseAffirmativePass.affirmative active base minima pool lambda) i.val ∧ owner i.val = q)

theorem markedAfter_value (I : ℕ) (active marked : ℕ → Bool)
    (owner base minima : ℕ → ℕ) (pool lambda q : ℕ) :
    DenseSurvivorPass.bit (markedAfter I active marked owner base minima pool lambda q) =
      if marked q = true ∨ ∃ i, i < I ∧
        DenseMarkPass.Qualifies active
          (DenseAffirmativePass.affirmative active base minima pool lambda) i ∧ owner i = q
      then 1 else 0 := by
  have hex :
      (∃ i : Fin I, DenseMarkPass.Qualifies active
        (DenseAffirmativePass.affirmative active base minima pool lambda) i.val ∧ owner i.val = q) ↔
      ∃ i, i < I ∧ DenseMarkPass.Qualifies active
        (DenseAffirmativePass.affirmative active base minima pool lambda) i ∧ owner i = q := by
    constructor
    · rintro ⟨i,hi⟩
      exact ⟨i.val,i.isLt,hi⟩
    · rintro ⟨i,hi,hp⟩
      exact ⟨⟨i,hi⟩,hp⟩
  unfold markedAfter DenseSurvivorPass.bit
  apply if_congr ?_ rfl rfl
  rw [Bool.or_eq_true, decide_eq_true_eq]
  exact or_congr Iff.rfl hex

/-- The complete three-call execution, including exact output semantics and
framing outside all three mutable buffers.  `pool` is the current pool size. -/
theorem ends {lim : Limits} {P : Program} {d pa pm ps : ℕ}
    (hpa : P[pa]? = some DenseAffirmativePass.body)
    (hpm : P[pm]? = some DenseMarkPass.body)
    (hps : P[ps]? = some DenseSurvivorPass.body)
    {μ : ℕ → ℤ} {active marked : ℕ → Bool} {owner base minima : ℕ → ℕ}
    {I Q pool lambda ab ob mb bb nb yb out : ℕ}
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
      ⟨frame [I,Q,pool,lambda,ab,ob,mb,bb,nb,yb,out], μ⟩ (115*I+47)
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

/-- Closed entry-point contract for `program[3]`; no callee correctness or
execution-time premise is assumed.  Layout and word bounds remain explicit. -/
theorem meets {lim : Limits} {d : ℕ}
    {μ : ℕ → ℤ} {active marked : ℕ → Bool} {owner base minima : ℕ → ℕ}
    {I Q pool lambda ab ob mb bb nb yb out : ℕ}
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
    Meets lim program 3 d [I,Q,pool,lambda,ab,ob,mb,bb,nb,yb,out] μ (115*I+47)
      fun _ μ' =>
        SameOutside3 μ μ' yb I mb Q out I ∧
        (∀ i < I, μ' (yb+i) = DenseAffirmativePass.bit
          (DenseAffirmativePass.affirmative active base minima pool lambda i)) ∧
        (∀ q < Q, μ' (mb+q) = DenseSurvivorPass.bit
          (markedAfter I active marked owner base minima pool lambda q)) ∧
        (∀ i < I, μ' (out+i) = DenseSurvivorPass.bit
          (DenseSurvivorPass.survives active
            (markedAfter I active marked owner base minima pool lambda)
            owner base minima pool lambda i)) := by
  exact Meets.of_body rfl (ends (P:=program) rfl rfl rfl ha ho hm hb hn hq hw h1
    hpool hlambda hbase hminima hprodMin hprodBase hlayout hd)

end Light.DenseCertificationFinish

#print axioms Light.DenseCertificationFinish.markedAfter_value
#print axioms Light.DenseCertificationFinish.ends
#print axioms Light.DenseCertificationFinish.meets
