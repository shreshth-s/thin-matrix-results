import ThreeSumApsp.Lang.Lib.Pass
import ThreeSumApsp.Lang.Tactics

namespace Light.DenseAffirmativePass

abbrev Len : ℕ := 0
abbrev Pool : ℕ := 1
abbrev Lambda : ℕ := 2
abbrev Active : ℕ := 3
abbrev Base : ℕ := 4
abbrev Minima : ℕ := 5
abbrev Out : ℕ := 6
abbrev Idx : ℕ := 7

def bit (b : Bool) : ℤ := if b then 1 else 0

@[simp] theorem bit_eq_one (b : Bool) : bit b = 1 ↔ b = true := by
  cases b <;> simp [bit]

def YesPred (active : ℕ → Bool) (base minima : ℕ → ℕ)
    (pool lambda i : ℕ) : Prop :=
  active i = true ∧ lambda * base i < pool * minima i

instance (active : ℕ → Bool) (base minima : ℕ → ℕ) (pool lambda i : ℕ) :
    Decidable (YesPred active base minima pool lambda i) := by
  unfold YesPred
  infer_instance

def yesBit (active : ℕ → Bool) (base minima : ℕ → ℕ) (pool lambda i : ℕ) : ℤ :=
  if YesPred active base minima pool lambda i then 1 else 0

def affirmative (active : ℕ → Bool) (base minima : ℕ → ℕ)
    (pool lambda i : ℕ) : Bool :=
  active i && decide (lambda * base i < pool * minima i)

theorem yesBit_eq_affirmative (active : ℕ → Bool) (base minima : ℕ → ℕ)
    (pool lambda i : ℕ) :
    yesBit active base minima pool lambda i = bit (affirmative active base minima pool lambda i) := by
  simp [yesBit, YesPred, affirmative, bit, Bool.and_eq_true]

def writeZero : Stmt := .store (v Out +' v Idx) (k 0)
def writeOne : Stmt := .store (v Out +' v Idx) (k 1)

def roundBody : Stmt :=
  .ite (M (v Active +' v Idx) =' k 1)
    (.ite ((v Lambda *' M (v Base +' v Idx)) <'
        (v Pool *' M (v Minima +' v Idx)))
      writeOne writeZero)
    writeZero

def body : Stmt := .for Idx (v Len) roundBody

theorem round_cost : roundBody.blockCost = 26 := by rfl

theorem frozen_read {μ : ℕ → ℤ} {f : ℕ → ℤ} {out j I src n i : ℕ}
    (hj : j ≤ I) (hi : i < n) (hsep : Apart src n out I) :
    wrote μ out f j (src + i) = μ (src + i) := by
  apply wrote_rest
  rcases hsep with h | h <;> omega

theorem ends {lim : Limits} {P : Program} {d : ℕ}
    {μ : ℕ → ℤ} {active : ℕ → Bool} {base minima : ℕ → ℕ}
    {I pool lambda ab bb nb out : ℕ}
    (ha : ∀ i < I, μ (ab + i) = bit (active i))
    (hb : ∀ i < I, μ (bb + i) = base i)
    (hn : ∀ i < I, μ (nb + i) = minima i)
    (hw : (lim.space : ℤ) ≤ lim.word) (h1 : 1 ≤ lim.word)
    (_hpool : (pool : ℤ) ≤ lim.word) (_hlambda : (lambda : ℤ) ≤ lim.word)
    (hbase : ∀ i < I, (base i : ℤ) ≤ lim.word)
    (hminima : ∀ i < I, (minima i : ℤ) ≤ lim.word)
    (hprodMin : ∀ i < I, ((pool * minima i : ℕ) : ℤ) ≤ lim.word)
    (hprodBase : ∀ i < I, ((lambda * base i : ℕ) : ℤ) ≤ lim.word)
    (hab : ab + I ≤ lim.space) (hbb : bb + I ≤ lim.space)
    (hnb : nb + I ≤ lim.space) (hout : out + I ≤ lim.space)
    (hsepA : Apart ab I out I) (hsepB : Apart bb I out I)
    (hsepN : Apart nb I out I) :
    Ends lim P d body ⟨frame [I, pool, lambda, ab, bb, nb, out], μ⟩ (34 * I + 6)
      fun σ => σ.mem = wrote μ out (yesBit active base minima pool lambda) I := by
  unfold body
  refine Ends.forFrame (fun j μ' => μ' = wrote μ out (yesBit active base minima pool lambda) j)
    I wrote_zero.symm ?round ?done
    (hn := by omega) (hT := by simp [round_cost]; omega)
  case round =>
    intro j μ' hj hμ
    have hra : μ' (ab + j) = bit (active j) := by
      rw [hμ, frozen_read hj.le hj hsepA]
      exact ha j hj
    have hrb : μ' (bb + j) = base j := by
      rw [hμ, frozen_read hj.le hj hsepB]
      exact hb j hj
    have hrn : μ' (nb + j) = minima j := by
      rw [hμ, frozen_read hj.le hj hsepN]
      exact hn j hj
    have hbasej := hbase j hj
    have hminj := hminima j hj
    have hpm := hprodMin j hj
    have hpb := hprodBase j hj
    have hnext : Function.update μ' (out + j) (yesBit active base minima pool lambda j) =
        wrote μ out (yesBit active base minima pool lambda) (j + 1) := by
      rw [hμ]
      exact wrote_succ
    unfold roundBody
    refine Ends.iteLast (fun hcA => ?_) (fun hcA => ?_) (by light_side)
    · have hA : active j = true := by simpa [hra] using hcA
      refine Ends.iteLast (fun hcY => ?_) (fun hcY => ?_)
        (by light_side [hrb, hrn, Nat.cast_mul])
      · have hY : lambda * base j < pool * minima j := by
          exact_mod_cast (show (lambda : ℤ) * base j < (pool : ℤ) * minima j by
            simpa [hrb, hrn] using hcY)
        have hy : YesPred active base minima pool lambda j := ⟨hA, hY⟩
        rw [yesBit, if_pos hy] at hnext
        unfold writeOne
        light_store (out + j) 1
        exact ⟨rfl, hnext⟩
      · have hY : ¬ lambda * base j < pool * minima j := by
          intro hh
          apply hcY
          have : (lambda : ℤ) * base j < (pool : ℤ) * minima j := by exact_mod_cast hh
          simpa [hrb, hrn] using this
        have hy : ¬ YesPred active base minima pool lambda j := by simp [YesPred, hY]
        rw [yesBit, if_neg hy] at hnext
        unfold writeZero
        light_store (out + j) 0
        exact ⟨rfl, hnext⟩
    · have hA : active j ≠ true := by simpa [hra] using hcA
      have hy : ¬ YesPred active base minima pool lambda j := by simp [YesPred, hA]
      rw [yesBit, if_neg hy] at hnext
      unfold writeZero
      light_store (out + j) 0
      exact ⟨rfl, hnext⟩
  case done =>
    intro μ' hμ
    exact hμ

theorem meets {lim : Limits} {P : Program} {d p : ℕ}
    (hbody : P[p]? = some body)
    {μ : ℕ → ℤ} {active : ℕ → Bool} {base minima : ℕ → ℕ}
    {I pool lambda ab bb nb out : ℕ}
    (ha : ∀ i < I, μ (ab + i) = bit (active i))
    (hb : ∀ i < I, μ (bb + i) = base i)
    (hn : ∀ i < I, μ (nb + i) = minima i)
    (hw : (lim.space : ℤ) ≤ lim.word) (h1 : 1 ≤ lim.word)
    (_hpool : (pool : ℤ) ≤ lim.word) (_hlambda : (lambda : ℤ) ≤ lim.word)
    (hbase : ∀ i < I, (base i : ℤ) ≤ lim.word)
    (hminima : ∀ i < I, (minima i : ℤ) ≤ lim.word)
    (hprodMin : ∀ i < I, ((pool * minima i : ℕ) : ℤ) ≤ lim.word)
    (hprodBase : ∀ i < I, ((lambda * base i : ℕ) : ℤ) ≤ lim.word)
    (hab : ab + I ≤ lim.space) (hbb : bb + I ≤ lim.space)
    (hnb : nb + I ≤ lim.space) (hout : out + I ≤ lim.space)
    (hsepA : Apart ab I out I) (hsepB : Apart bb I out I)
    (hsepN : Apart nb I out I) :
    Meets lim P p d [I, pool, lambda, ab, bb, nb, out] μ (34 * I + 6)
      fun _ μ' => SameOutside μ μ' out I ∧
        ∀ i < I, μ' (out + i) = bit (affirmative active base minima pool lambda i) := by
  refine .of_body hbody ?_
  refine (ends ha hb hn hw h1 _hpool _hlambda hbase hminima hprodMin hprodBase
    hab hbb hnb hout hsepA hsepB hsepN).mono le_rfl ?_
  intro σ hσ
  rw [hσ]
  refine ⟨sameOutside_wrote le_rfl, ?_⟩
  intro i hi
  rw [wrote_done hi, yesBit_eq_affirmative]

theorem meets_of_pos {lim : Limits} {P : Program} {d p : ℕ}
    (hbody : P[p]? = some body)
    {μ : ℕ → ℤ} {active : ℕ → Bool} {base minima : ℕ → ℕ}
    {I pool lambda ab bb nb out : ℕ}
    (ha : ∀ i < I, μ (ab + i) = bit (active i))
    (hb : ∀ i < I, μ (bb + i) = base i)
    (hn : ∀ i < I, μ (nb + i) = minima i)
    (hw : (lim.space : ℤ) ≤ lim.word) (h1 : 1 ≤ lim.word)
    (_hpool : (pool : ℤ) ≤ lim.word) (_hlambda : (lambda : ℤ) ≤ lim.word)
    (hbase : ∀ i < I, (base i : ℤ) ≤ lim.word)
    (hminima : ∀ i < I, (minima i : ℤ) ≤ lim.word)
    (hprodMin : ∀ i < I, ((pool * minima i : ℕ) : ℤ) ≤ lim.word)
    (hprodBase : ∀ i < I, ((lambda * base i : ℕ) : ℤ) ≤ lim.word)
    (hab : ab + I ≤ lim.space) (hbb : bb + I ≤ lim.space)
    (hnb : nb + I ≤ lim.space) (hout : out + I ≤ lim.space)
    (hsepA : Apart ab I out I) (hsepB : Apart bb I out I)
    (hsepN : Apart nb I out I) (hI : 0 < I) :
    Meets lim P p d [I, pool, lambda, ab, bb, nb, out] μ (40 * I)
      fun _ μ' => SameOutside μ μ' out I ∧
        ∀ i < I, μ' (out + i) = bit (affirmative active base minima pool lambda i) := by
  exact (meets hbody ha hb hn hw h1 _hpool _hlambda hbase hminima hprodMin hprodBase
    hab hbb hnb hout hsepA hsepB hsepN).mono_time (by omega)

end Light.DenseAffirmativePass

#print axioms Light.DenseAffirmativePass.ends
#print axioms Light.DenseAffirmativePass.meets
#print axioms Light.DenseAffirmativePass.meets_of_pos
