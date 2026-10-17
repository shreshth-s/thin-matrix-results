import ThreeSumApsp.Lang.Lib.Pass
import ThreeSumApsp.Lang.Tactics

namespace Light.DenseSurvivorPass

abbrev Len : ℕ := 0
abbrev PairCount : ℕ := 1
abbrev Pool : ℕ := 2
abbrev Lambda : ℕ := 3
abbrev Active : ℕ := 4
abbrev Owner : ℕ := 5
abbrev Mark : ℕ := 6
abbrev Base : ℕ := 7
abbrev Minima : ℕ := 8
abbrev Out : ℕ := 9
abbrev Idx : ℕ := 10

def bit (b : Bool) : ℤ := if b then 1 else 0

@[simp] theorem bit_eq_one (b : Bool) : bit b = 1 ↔ b = true := by
  cases b <;> simp [bit]

def Keep (active marked : ℕ → Bool) (owner base minima : ℕ → ℕ)
    (pool lambda i : ℕ) : Prop :=
  active i = true ∧ minima i ≠ 0 ∧
    pool * minima i ≤ lambda * base i ∧ marked (owner i) ≠ true

instance (active marked : ℕ → Bool) (owner base minima : ℕ → ℕ)
    (pool lambda i : ℕ) : Decidable (Keep active marked owner base minima pool lambda i) := by
  unfold Keep
  infer_instance

def keepBit (active marked : ℕ → Bool) (owner base minima : ℕ → ℕ)
    (pool lambda i : ℕ) : ℤ :=
  if Keep active marked owner base minima pool lambda i then 1 else 0

def survives (active marked : ℕ → Bool) (owner base minima : ℕ → ℕ)
    (pool lambda i : ℕ) : Bool :=
  active i && decide (minima i ≠ 0) &&
    decide (pool * minima i ≤ lambda * base i) && !(marked (owner i))

theorem keepBit_eq_survives (active marked : ℕ → Bool) (owner base minima : ℕ → ℕ)
    (pool lambda i : ℕ) :
    keepBit active marked owner base minima pool lambda i =
      bit (survives active marked owner base minima pool lambda i) := by
  simp [keepBit, Keep, survives, bit, Bool.and_eq_true, and_assoc]

def writeZero : Stmt := .store (v Out +' v Idx) (k 0)
def writeOne : Stmt := .store (v Out +' v Idx) (k 1)

def roundBody : Stmt :=
  .ite (M (v Active +' v Idx) =' k 1)
    (.ite (M (v Minima +' v Idx) =' k 0)
      writeZero
      (.ite ((v Lambda *' M (v Base +' v Idx)) <'
          (v Pool *' M (v Minima +' v Idx)))
        writeZero
        (.ite (M (v Mark +' M (v Owner +' v Idx)) =' k 1)
          writeZero writeOne)))
    writeZero

def body : Stmt := .for Idx (v Len) roundBody

theorem round_cost : roundBody.blockCost = 43 := by rfl

theorem frozen_read {μ : ℕ → ℤ} {f : ℕ → ℤ} {out j I src n i : ℕ}
    (hj : j ≤ I) (hi : i < n) (hsep : Apart src n out I) :
    wrote μ out f j (src + i) = μ (src + i) := by
  apply wrote_rest
  rcases hsep with h | h <;> omega

theorem keepBit_boolean (active marked : ℕ → Bool) (owner base minima : ℕ → ℕ)
    (pool lambda i : ℕ) :
    keepBit active marked owner base minima pool lambda i = 0 ∨
      keepBit active marked owner base minima pool lambda i = 1 := by
  unfold keepBit
  split_ifs
  · exact Or.inr rfl
  · exact Or.inl rfl

theorem ends {lim : Limits} {P : Program} {d : ℕ}
    {μ : ℕ → ℤ} {active marked : ℕ → Bool} {owner base minima : ℕ → ℕ}
    {I Q pool lambda ab ob mb bb nb out : ℕ}
    (ha : ∀ i < I, μ (ab + i) = bit (active i))
    (ho : ∀ i < I, μ (ob + i) = owner i)
    (hm : ∀ q < Q, μ (mb + q) = bit (marked q))
    (hb : ∀ i < I, μ (bb + i) = base i)
    (hn : ∀ i < I, μ (nb + i) = minima i)
    (hq : ∀ i < I, owner i < Q)
    (hw : (lim.space : ℤ) ≤ lim.word) (h1 : 1 ≤ lim.word)
    (hpool : (pool : ℤ) ≤ lim.word) (_hlambda : (lambda : ℤ) ≤ lim.word)
    (hbase : ∀ i < I, (base i : ℤ) ≤ lim.word)
    (hminima : ∀ i < I, (minima i : ℤ) ≤ lim.word)
    (hprodMin : ∀ i < I, ((pool * minima i : ℕ) : ℤ) ≤ lim.word)
    (hprodBase : ∀ i < I, ((lambda * base i : ℕ) : ℤ) ≤ lim.word)
    (hab : ab + I ≤ lim.space) (hob : ob + I ≤ lim.space)
    (hmb : mb + Q ≤ lim.space) (hbb : bb + I ≤ lim.space)
    (hnb : nb + I ≤ lim.space) (hout : out + I ≤ lim.space)
    (hsepA : Apart ab I out I) (hsepO : Apart ob I out I)
    (hsepM : Apart mb Q out I) (hsepB : Apart bb I out I)
    (hsepN : Apart nb I out I) :
    Ends lim P d body ⟨frame [I, Q, pool, lambda, ab, ob, mb, bb, nb, out], μ⟩
      (51 * I + 6) fun σ =>
        σ.mem = wrote μ out (keepBit active marked owner base minima pool lambda) I := by
  unfold body
  refine Ends.forFrame
    (fun j μ' => μ' = wrote μ out (keepBit active marked owner base minima pool lambda) j)
    I wrote_zero.symm ?round ?done
    (hn := by omega) (hT := by simp [round_cost]; omega)
  case round =>
    intro j μ' hj hμ
    have hra : μ' (ab + j) = bit (active j) := by
      rw [hμ, frozen_read hj.le hj hsepA]
      exact ha j hj
    have hro : μ' (ob + j) = owner j := by
      rw [hμ, frozen_read hj.le hj hsepO]
      exact ho j hj
    have hrb : μ' (bb + j) = base j := by
      rw [hμ, frozen_read hj.le hj hsepB]
      exact hb j hj
    have hrn : μ' (nb + j) = minima j := by
      rw [hμ, frozen_read hj.le hj hsepN]
      exact hn j hj
    have howner := hq j hj
    have hrm : μ' (mb + owner j) = bit (marked (owner j)) := by
      rw [hμ, frozen_read hj.le howner hsepM]
      exact hm _ howner
    have hbasej := hbase j hj
    have hminj := hminima j hj
    have hpm := hprodMin j hj
    have hpb := hprodBase j hj
    have hnext : Function.update μ' (out + j)
        (keepBit active marked owner base minima pool lambda j) =
        wrote μ out (keepBit active marked owner base minima pool lambda) (j + 1) := by
      rw [hμ]
      exact wrote_succ
    unfold roundBody
    refine Ends.iteLast (fun hcA => ?_) (fun hcA => ?_) (by light_side)
    · have hA : active j = true := by simpa [hra] using hcA
      refine Ends.iteLast (fun hcN => ?_) (fun hcN => ?_) (by light_side)
      · have hN : minima j = 0 := by exact_mod_cast (show (minima j : ℤ) = 0 by simpa [hrn] using hcN)
        have hk : ¬ Keep active marked owner base minima pool lambda j := by simp [Keep, hN]
        rw [keepBit, if_neg hk] at hnext
        unfold writeZero
        light_store (out + j) 0
        exact ⟨rfl, hnext⟩
      · have hN : minima j ≠ 0 := by
          intro hz
          apply hcN
          simp [hrn, hz]
        refine Ends.iteLast (fun hcBad => ?_) (fun hcBad => ?_)
          (by light_side [hrb, hrn, Nat.cast_mul] )
        · have hBad : lambda * base j < pool * minima j := by
            exact_mod_cast (show (lambda : ℤ) * base j < (pool : ℤ) * minima j by
              simpa [hrb, hrn] using hcBad)
          have hk : ¬ Keep active marked owner base minima pool lambda j := by
            intro hk
            exact Nat.not_le_of_gt hBad hk.2.2.1
          rw [keepBit, if_neg hk] at hnext
          unfold writeZero
          light_store (out + j) 0
          exact ⟨rfl, hnext⟩
        · have hGood : pool * minima j ≤ lambda * base j := by
            have hh : ¬ lambda * base j < pool * minima j := by
              intro hh
              apply hcBad
              have : (lambda : ℤ) * base j < (pool : ℤ) * minima j := by exact_mod_cast hh
              simpa [hrb, hrn] using this
            omega
          refine Ends.iteLast (fun hcM => ?_) (fun hcM => ?_)
            (by light_side [hro])
          · have hM : marked (owner j) = true := by simpa [hro, hrm] using hcM
            have hk : ¬ Keep active marked owner base minima pool lambda j := by simp [Keep, hM]
            rw [keepBit, if_neg hk] at hnext
            unfold writeZero
            light_store (out + j) 0
            exact ⟨rfl, hnext⟩
          · have hM : marked (owner j) ≠ true := by simpa [hro, hrm] using hcM
            have hk : Keep active marked owner base minima pool lambda j := ⟨hA, hN, hGood, hM⟩
            rw [keepBit, if_pos hk] at hnext
            unfold writeOne
            light_store (out + j) 1
            exact ⟨rfl, hnext⟩
    · have hA : active j ≠ true := by simpa [hra] using hcA
      have hk : ¬ Keep active marked owner base minima pool lambda j := by simp [Keep, hA]
      rw [keepBit, if_neg hk] at hnext
      unfold writeZero
      light_store (out + j) 0
      exact ⟨rfl, hnext⟩
  case done =>
    intro μ' hμ
    exact hμ

/-- Completed Boolean output and preservation of every cell outside the output array. -/
theorem meets {lim : Limits} {P : Program} {d p : ℕ}
    (hbody : P[p]? = some body)
    {μ : ℕ → ℤ} {active marked : ℕ → Bool} {owner base minima : ℕ → ℕ}
    {I Q pool lambda ab ob mb bb nb out : ℕ}
    (ha : ∀ i < I, μ (ab + i) = bit (active i))
    (ho : ∀ i < I, μ (ob + i) = owner i)
    (hm : ∀ q < Q, μ (mb + q) = bit (marked q))
    (hb : ∀ i < I, μ (bb + i) = base i)
    (hn : ∀ i < I, μ (nb + i) = minima i)
    (hq : ∀ i < I, owner i < Q)
    (hw : (lim.space : ℤ) ≤ lim.word) (h1 : 1 ≤ lim.word)
    (hpool : (pool : ℤ) ≤ lim.word) (_hlambda : (lambda : ℤ) ≤ lim.word)
    (hbase : ∀ i < I, (base i : ℤ) ≤ lim.word)
    (hminima : ∀ i < I, (minima i : ℤ) ≤ lim.word)
    (hprodMin : ∀ i < I, ((pool * minima i : ℕ) : ℤ) ≤ lim.word)
    (hprodBase : ∀ i < I, ((lambda * base i : ℕ) : ℤ) ≤ lim.word)
    (hab : ab + I ≤ lim.space) (hob : ob + I ≤ lim.space)
    (hmb : mb + Q ≤ lim.space) (hbb : bb + I ≤ lim.space)
    (hnb : nb + I ≤ lim.space) (hout : out + I ≤ lim.space)
    (hsepA : Apart ab I out I) (hsepO : Apart ob I out I)
    (hsepM : Apart mb Q out I) (hsepB : Apart bb I out I)
    (hsepN : Apart nb I out I) :
    Meets lim P p d [I, Q, pool, lambda, ab, ob, mb, bb, nb, out] μ
      (51 * I + 6) fun _ μ' => SameOutside μ μ' out I ∧
        ∀ i < I, μ' (out + i) =
          bit (survives active marked owner base minima pool lambda i) := by
  refine .of_body hbody ?_
  refine (ends ha ho hm hb hn hq hw h1 hpool _hlambda hbase hminima hprodMin hprodBase
    hab hob hmb hbb hnb hout hsepA hsepO hsepM hsepB hsepN).mono le_rfl ?_
  intro σ hσ
  rw [hσ]
  refine ⟨sameOutside_wrote le_rfl, ?_⟩
  intro i hi
  rw [wrote_done hi, keepBit_eq_survives]

/-- A nonempty survivor scan costs at most 57I steps. -/
theorem meets_of_pos {lim : Limits} {P : Program} {d p : ℕ}
    (hbody : P[p]? = some body)
    {μ : ℕ → ℤ} {active marked : ℕ → Bool} {owner base minima : ℕ → ℕ}
    {I Q pool lambda ab ob mb bb nb out : ℕ}
    (ha : ∀ i < I, μ (ab + i) = bit (active i))
    (ho : ∀ i < I, μ (ob + i) = owner i)
    (hm : ∀ q < Q, μ (mb + q) = bit (marked q))
    (hb : ∀ i < I, μ (bb + i) = base i)
    (hn : ∀ i < I, μ (nb + i) = minima i)
    (hq : ∀ i < I, owner i < Q)
    (hw : (lim.space : ℤ) ≤ lim.word) (h1 : 1 ≤ lim.word)
    (hpool : (pool : ℤ) ≤ lim.word) (_hlambda : (lambda : ℤ) ≤ lim.word)
    (hbase : ∀ i < I, (base i : ℤ) ≤ lim.word)
    (hminima : ∀ i < I, (minima i : ℤ) ≤ lim.word)
    (hprodMin : ∀ i < I, ((pool * minima i : ℕ) : ℤ) ≤ lim.word)
    (hprodBase : ∀ i < I, ((lambda * base i : ℕ) : ℤ) ≤ lim.word)
    (hab : ab + I ≤ lim.space) (hob : ob + I ≤ lim.space)
    (hmb : mb + Q ≤ lim.space) (hbb : bb + I ≤ lim.space)
    (hnb : nb + I ≤ lim.space) (hout : out + I ≤ lim.space)
    (hsepA : Apart ab I out I) (hsepO : Apart ob I out I)
    (hsepM : Apart mb Q out I) (hsepB : Apart bb I out I)
    (hsepN : Apart nb I out I) (hI : 0 < I) :
    Meets lim P p d [I, Q, pool, lambda, ab, ob, mb, bb, nb, out] μ
      (57 * I) fun _ μ' => SameOutside μ μ' out I ∧
        ∀ i < I, μ' (out + i) =
          bit (survives active marked owner base minima pool lambda i) := by
  exact (meets hbody ha ho hm hb hn hq hw h1 hpool _hlambda hbase hminima hprodMin hprodBase
    hab hob hmb hbb hnb hout hsepA hsepO hsepM hsepB hsepN).mono_time (by omega)

end Light.DenseSurvivorPass

#print axioms Light.DenseSurvivorPass.ends
#print axioms Light.DenseSurvivorPass.meets
#print axioms Light.DenseSurvivorPass.meets_of_pos
