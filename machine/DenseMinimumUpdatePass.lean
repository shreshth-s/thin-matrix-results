import ThreeSumApsp.Lang.Lib.Pass
import ThreeSumApsp.Lang.Tactics

namespace Light.DenseMinimumUpdatePass

abbrev Len : ℕ := 0
abbrev Row : ℕ := 1
abbrev Minima : ℕ := 2
abbrev Idx : ℕ := 3

def roundBody : Stmt :=
  .ite (M (v Row +' v Idx) <' M (v Minima +' v Idx))
    (.store (v Minima +' v Idx) (M (v Row +' v Idx)))
    (.store (v Minima +' v Idx) (M (v Minima +' v Idx)))

def body : Stmt := .for Idx (v Len) roundBody

theorem round_cost : roundBody.blockCost = 18 := by rfl

theorem ends {lim : Limits} {P : Program} {d : ℕ}
    {μ : ℕ → ℤ} {row initial : ℕ → ℕ} {I rb mb : ℕ}
    (hr : ∀ i < I, μ (rb + i) = row i)
    (hm : ∀ i < I, μ (mb + i) = initial i)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hrb : rb + I ≤ lim.space) (hmb : mb + I ≤ lim.space)
    (hsep : Apart rb I mb I) :
    Ends lim P d body ⟨frame [I, rb, mb], μ⟩ (26 * I + 6)
      fun σ => σ.mem = wrote μ mb (fun i => (min (initial i) (row i) : ℕ)) I := by
  unfold body
  refine Ends.forFrame
    (fun j μ' => μ' = wrote μ mb (fun i => (min (initial i) (row i) : ℕ)) j)
    I wrote_zero.symm ?round ?done
    (hn := by omega) (hT := by simp [round_cost]; omega)
  case round =>
    intro j μ' hj hμ
    have hrr : μ' (rb + j) = row j := by
      rw [hμ, wrote_rest (by rcases hsep with h | h <;> omega)]
      exact hr j hj
    -- Destination cell j has not been overwritten by any earlier round.
    have hrm : μ' (mb + j) = initial j := by
      rw [hμ, wrote_rest (by right; omega)]
      exact hm j hj
    have hnext : Function.update μ' (mb + j) (min (initial j) (row j) : ℕ) =
        wrote μ mb (fun i => (min (initial i) (row i) : ℕ)) (j + 1) := by
      rw [hμ]
      exact wrote_succ
    unfold roundBody
    refine Ends.iteLast (fun hc => ?_) (fun hc => ?_) (by light_side)
    · have hlt : row j < initial j := by
        exact_mod_cast (show (row j : ℤ) < initial j by simpa [hrr, hrm] using hc)
      rw [min_eq_right hlt.le] at hnext
      light_store (mb + j) (row j : ℕ) using hrr
      exact ⟨rfl, hnext⟩
    · have hle : initial j ≤ row j := by
        have hnlt : ¬ row j < initial j := by
          intro hlt
          apply hc
          have : (row j : ℤ) < initial j := by exact_mod_cast hlt
          simpa [hrr, hrm] using this
        omega
      rw [min_eq_left hle] at hnext
      light_store (mb + j) (initial j : ℕ) using hrm
      exact ⟨rfl, hnext⟩
  case done =>
    intro μ' hμ
    exact hμ

theorem meets {lim : Limits} {P : Program} {d p : ℕ}
    (hbody : P[p]? = some body)
    {μ : ℕ → ℤ} {row initial : ℕ → ℕ} {I h rb mb : ℕ}
    (hr : ∀ i < I, μ (rb + i) = row i)
    (hm : ∀ i < I, μ (mb + i) = initial i)
    (hrow : ∀ i < I, row i ≤ h)
    (hinitial : ∀ i < I, initial i ≤ h)
    (hw : (lim.space : ℤ) ≤ lim.word) (hword : (h : ℤ) ≤ lim.word)
    (hrb : rb + I ≤ lim.space) (hmb : mb + I ≤ lim.space)
    (hsep : Apart rb I mb I) :
    Meets lim P p d [I, rb, mb] μ (26 * I + 6) fun _ μ' =>
      SameOutside μ μ' mb I ∧ ∀ i < I,
        μ' (mb + i) = (min (initial i) (row i) : ℕ) ∧
        0 ≤ μ' (mb + i) ∧ μ' (mb + i) ≤ h ∧ μ' (mb + i) ≤ lim.word := by
  refine .of_body hbody ?_
  refine (ends hr hm hw hrb hmb hsep).mono le_rfl ?_
  intro σ hσ
  rw [hσ]
  refine ⟨sameOutside_wrote le_rfl, ?_⟩
  intro i hi
  rw [wrote_done hi]
  have hv : min (initial i) (row i) ≤ h := by
    rcases Nat.le_total (initial i) (row i) with hh | hh
    · simpa [min_eq_left hh] using hinitial i hi
    · simpa [min_eq_right hh] using hrow i hi
  have hval : ((min (initial i) (row i) : ℕ) : ℤ) ≤ h := by exact_mod_cast hv
  exact ⟨rfl, Int.natCast_nonneg _, hval, hval.trans hword⟩

theorem meets_of_pos {lim : Limits} {P : Program} {d p : ℕ}
    (hbody : P[p]? = some body)
    {μ : ℕ → ℤ} {row initial : ℕ → ℕ} {I h rb mb : ℕ}
    (hr : ∀ i < I, μ (rb + i) = row i)
    (hm : ∀ i < I, μ (mb + i) = initial i)
    (hrow : ∀ i < I, row i ≤ h)
    (hinitial : ∀ i < I, initial i ≤ h)
    (hw : (lim.space : ℤ) ≤ lim.word) (hword : (h : ℤ) ≤ lim.word)
    (hrb : rb + I ≤ lim.space) (hmb : mb + I ≤ lim.space)
    (hsep : Apart rb I mb I) (hI : 0 < I) :
    Meets lim P p d [I, rb, mb] μ (32 * I) fun _ μ' =>
      SameOutside μ μ' mb I ∧ ∀ i < I,
        μ' (mb + i) = (min (initial i) (row i) : ℕ) ∧
        0 ≤ μ' (mb + i) ∧ μ' (mb + i) ≤ h ∧ μ' (mb + i) ≤ lim.word := by
  exact (meets hbody hr hm hrow hinitial hw hword hrb hmb hsep).mono_time (by omega)

end Light.DenseMinimumUpdatePass

#print axioms Light.DenseMinimumUpdatePass.ends
#print axioms Light.DenseMinimumUpdatePass.meets
#print axioms Light.DenseMinimumUpdatePass.meets_of_pos
