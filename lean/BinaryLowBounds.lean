import BackendScalarBits
import BitArraySimulation
set_option maxHeartbeats 1000000
open scoped BigOperators
namespace ThinMatrix.BinaryLowBounds

/-- Bounds every prefix, suffix, or generated sublist, without assuming that
different terms occur only once. -/
theorem list_sum_bound {α : Type*} (xs : List α) (f : α → ℤ) (A : ℕ)
    (hf : ∀ x ∈ xs, |f x| ≤ (A : ℤ)) :
    |(xs.map f).sum| ≤ (xs.length*A : ℕ) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := hf x (by simp)
    have ht : |(xs.map f).sum| ≤ (xs.length*A : ℕ) :=
      ih (fun y hy => hf y (by simp [hy]))
    simp only [List.map_cons,List.sum_cons,List.length_cons]
    calc
      |f x+(xs.map f).sum| ≤ |f x|+|(xs.map f).sum| := abs_add_le _ _
      _ ≤ (A:ℤ)+(xs.length*A:ℕ) := add_le_add hx ht
      _ = ((xs.length+1)*A:ℕ) := by push_cast; ring

theorem list_partial_bound {α : Type*} (xs : List α) (f : α → ℤ) (A n : ℕ)
    (hlen : xs.length ≤ n) (hf : ∀ x ∈ xs, |f x| ≤ (A : ℤ)) :
    |(xs.map f).sum| ≤ (n*A : ℕ) := by
  exact (list_sum_bound xs f A hf).trans
    (by exact_mod_cast Nat.mul_le_mul_right A hlen)

theorem residualWeight_bound (k t d : ℕ) :
    |(TensorContraction.residualWeight k t d : ℤ)| ≤ (2^k:ℕ) := by
  change |(-1:ℤ)^(t-d-1)*((k-d-1).choose (t-d-1):ℤ)| ≤ (2^k:ℕ)
  rw [abs_mul,abs_neg_one_pow,one_mul,abs_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast (Nat.choose_le_two_pow (k-d-1) (t-d-1)).trans
    (Nat.pow_le_pow_right (by decide) (by omega : k-d-1 ≤ k))

theorem blockCoeff_bound {q width : ℕ} [NeZero q] (block : SparseLocalForms.DenseVector q width)
    (A : ℕ) (h : ∀ degree residue, |SparseLocalForms.denseRead block degree residue| ≤ (A:ℤ))
    (degree : ℕ) (residue : Fin q) :
    |CachedLowQuery.blockCoeff block degree residue| ≤ (A:ℤ) := by
  unfold CachedLowQuery.blockCoeff
  split
  · exact h _ _
  · simp

theorem qdot_partial_bound {q : ℕ} [NeZero q]
    (left right : Fin q → ℤ) (target : Fin q) (A : ℕ)
    (hl : ∀ j, |left j| ≤ (A:ℤ)) (hr : ∀ j, |right j| ≤ (A:ℤ))
    (xs : List (Fin q)) (hlen : xs.length ≤ q) :
    |(xs.map (fun j => left j*right (target-j))).sum| ≤ (q*A^2:ℕ) := by
  apply list_partial_bound xs _ (A^2) q hlen
  intro j _
  rw [abs_mul]
  have h := mul_le_mul (hl j) (hr (target-j)) (abs_nonneg _) (Nat.cast_nonneg A)
  simpa only [Nat.cast_pow,Nat.cast_mul,pow_two] using h

theorem selectedDot_bound {q : ℕ} [NeZero q]
    (left right : Fin q → ℤ) (target : Fin q) (A : ℕ)
    (hl : ∀ j, |left j| ≤ (A:ℤ)) (hr : ∀ j, |right j| ≤ (A:ℤ)) :
    |(CachedLowQuery.selectedDot left right target).1| ≤ (q*A^2:ℕ) :=
  qdot_partial_bound left right target A hl hr (List.finRange q) (by simp)

theorem polynomialDot_partial_bound {q width : ℕ} [NeZero q]
    (left right : SparseLocalForms.DenseVector q width) (A d : ℕ)
    (hl : ∀ degree residue, |SparseLocalForms.denseRead left degree residue| ≤ (A:ℤ))
    (hr : ∀ degree residue, |SparseLocalForms.denseRead right degree residue| ≤ (A:ℤ))
    (target : Fin q) (degrees : List ℕ) (hlen : degrees.length ≤ d+1) :
    |(degrees.map (fun a => (CachedLowQuery.selectedDot
      (CachedLowQuery.blockCoeff left a)
      (CachedLowQuery.blockCoeff right (d-a)) target).1)).sum| ≤ ((d+1)*q*A^2:ℕ) := by
  have hs := list_partial_bound degrees _ (q*A^2) (d+1) hlen
    (fun a _ => selectedDot_bound _ _ target A
      (fun j => blockCoeff_bound left A hl a j)
      (fun j => blockCoeff_bound right A hr (d-a) j))
  simpa only [Nat.mul_assoc] using hs

theorem polynomialDot_bound {q width : ℕ} [NeZero q]
    (left right : SparseLocalForms.DenseVector q width) (A d : ℕ)
    (hl : ∀ degree residue, |SparseLocalForms.denseRead left degree residue| ≤ (A:ℤ))
    (hr : ∀ degree residue, |SparseLocalForms.denseRead right degree residue| ≤ (A:ℤ))
    (target : Fin q) :
    |(CachedLowQuery.polynomialDot left right d target).1| ≤ ((d+1)*q*A^2:ℕ) := by
  simpa only [CachedLowQuery.polynomialDot,List.map_map,Function.comp_def] using
    polynomialDot_partial_bound left right A d hl hr target (List.range (d+1)) (by simp)

theorem lowTerm_bound {q width : ℕ} [NeZero q] (k t A : ℕ)
    (left right : SparseLocalForms.DenseVector q width)
    (hl : ∀ degree residue, |SparseLocalForms.denseRead left degree residue| ≤ (A:ℤ))
    (hr : ∀ degree residue, |SparseLocalForms.denseRead right degree residue| ≤ (A:ℤ))
    (channelCard degree : ℕ) (hd : degree < t) (target : Fin q) :
    |(CachedLowQuery.lowTerm k t left right channelCard degree target).1| ≤
      (2^k*t*q*A^2:ℕ) := by
  unfold CachedLowQuery.lowTerm
  split
  · dsimp only
    rw [CachedLowQuery.weightCounted_value,abs_mul]
    have hp := polynomialDot_bound left right A (degree-channelCard) hl hr target
    have hd' : degree-channelCard+1 ≤ t := by omega
    have hm : ((degree-channelCard+1)*q*A^2:ℕ) ≤ t*q*A^2 :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hd')
    have hp' : |(CachedLowQuery.polynomialDot left right (degree-channelCard) target).1| ≤
        (t*q*A^2:ℕ) := hp.trans (by exact_mod_cast hm)
    have h := mul_le_mul (residualWeight_bound k t degree) hp'
      (abs_nonneg _) (by positivity : (0:ℤ) ≤ (2^k:ℕ))
    simpa only [Nat.cast_mul,Nat.mul_assoc] using h
  · dsimp only
    positivity

/-- Every partial degree sum inside one channel. -/
theorem degree_sum_partial_bound {q width : ℕ} [NeZero q] (k t A : ℕ)
    (left right : SparseLocalForms.DenseVector q width)
    (hl : ∀ degree residue, |SparseLocalForms.denseRead left degree residue| ≤ (A:ℤ))
    (hr : ∀ degree residue, |SparseLocalForms.denseRead right degree residue| ≤ (A:ℤ))
    (channelCard : ℕ) (target : Fin q) (degrees : List ℕ)
    (hlen : degrees.length ≤ t) (hdeg : ∀ d ∈ degrees, d < t) :
    |(degrees.map (fun d =>
      (CachedLowQuery.lowTerm k t left right channelCard d target).1)).sum| ≤
      (t*(2^k*t*q*A^2):ℕ) :=
  list_partial_bound degrees _ _ t hlen
    (fun d hd => lowTerm_bound k t A left right hl hr channelCard d (hdeg d hd) target)

/-- Every partial list of already evaluated channel sums. Repetition is
allowed; the only hypothesis is the genuine generator's length bound. -/
theorem channel_sum_partial_bound {α : Type*} (channels : List α) (f : α → ℤ)
    (k t q A : ℕ) (hlen : channels.length ≤ 2^k)
    (hf : ∀ c ∈ channels, |f c| ≤ (t*(2^k*t*q*A^2):ℕ)) :
    |(channels.map f).sum| ≤ (2^(2*k)*t^2*q*A^2:ℕ) := by
  have hs := list_partial_bound channels f (t*(2^k*t*q*A^2)) (2^k) hlen hf
  have he : 2^k*(t*(2^k*t*q*A^2)) = 2^(2*k)*t^2*q*A^2 := by
    rw [show 2*k=k+k by omega,pow_add]
    ring
  simpa only [he] using hs

/-- Every partial sum of matching degree runs, including their sequential
accumulator before the final result. -/
theorem run_sum_partial_bound {α : Type*} (runs : List α) (f : α → ℤ)
    (m k t q A : ℕ) (hlen : runs.length ≤ 2*m+1)
    (hf : ∀ r ∈ runs, |f r| ≤ (2^(2*k)*t^2*q*A^2:ℕ)) :
    |(runs.map f).sum| ≤ ((2*m+1)*(2^(2*k)*t^2*q*A^2):ℕ) :=
  list_partial_bound runs f _ _ hlen hf

def lowMagnitude (m k t q A : ℕ) : ℕ :=
  (2*m+1)*2^(2*k)*(t+1)^2*(q+1)*(A+1)^2

def lowBitWidth (m k t q A : ℕ) : ℕ :=
  (2*m+1).size+2*k+2*(t+1).size+(q+1).size+2*(A+1).size+1

theorem low_run_cap (m k t q A : ℕ) :
    (2*m+1)*(2^(2*k)*t^2*q*A^2) ≤ lowMagnitude m k t q A := by
  unfold lowMagnitude
  calc
    _ = (2*m+1)*2^(2*k)*t^2*q*A^2 := by ring
    _ ≤ _ := by gcongr <;> omega

/-- A generic bound for the data intermediates that precede channel/run
sums. All multiplicative overheads are explicitly part of lowMagnitude. -/
theorem data_cap (m k t q A : ℕ) :
    2^k*(t+1)*q*A^2 ≤ lowMagnitude m k t q A := by
  unfold lowMagnitude
  have hrun : 1 ≤ 2*m+1 := by omega
  have hp : 2^k ≤ 2^(2*k) := Nat.pow_le_pow_right (by decide) (by omega)
  have ht : t+1 ≤ (t+1)^2 := by nlinarith
  calc
    _ = 1*2^k*(t+1)*q*A^2 := by ring
    _ ≤ _ := by gcongr <;> omega

/-- The same cap includes each raw cache read and product, each partial
cyclic dot, each partial unweighted degree convolution, and each weighted
term. The t+1 guard also covers the empty-query case. -/
theorem intermediate_caps (m k t q A d : ℕ) (hd : d ≤ t) :
    A ≤ lowMagnitude m k t q A ∧
    A^2 ≤ lowMagnitude m k t q A ∧
    q*A^2 ≤ lowMagnitude m k t q A ∧
    (d+1)*q*A^2 ≤ lowMagnitude m k t q A ∧
    2^k*(d+1)*q*A^2 ≤ lowMagnitude m k t q A := by
  have hpow : 1 ≤ 2^k := Nat.one_le_pow k 2 (by decide)
  have hraw : A ≤ lowMagnitude m k t q A := by
    unfold lowMagnitude
    calc
      _ ≤ 1*1*1*1*(A+1)^2 := by nlinarith
      _ ≤ _ := by gcongr <;> first | omega | exact Nat.one_le_pow _ _ (by omega)
  have hprod : A^2 ≤ 2^k*(t+1)*q*A^2 ∨ q=0 := by
    by_cases hq : q=0
    · exact Or.inr hq
    · apply Or.inl
      have hq' : 1 ≤ q := by omega
      calc
        _ = 1*1*1*A^2 := by ring
        _ ≤ _ := by gcongr; omega
  have hprod' : A^2 ≤ lowMagnitude m k t q A := by
    rcases hprod with hp | hq
    · exact hp.trans (data_cap m k t q A)
    · subst q
      unfold lowMagnitude
      calc
        _ = 1*1*1*1*A^2 := by ring
        _ ≤ _ := by gcongr <;> first | omega | exact Nat.one_le_pow _ _ (by omega)
  have hqdot : q*A^2 ≤ lowMagnitude m k t q A := by
    apply le_trans _ (data_cap m k t q A)
    calc
      _ = 1*1*q*A^2 := by ring
      _ ≤ _ := by gcongr; omega
  have hpoly : (d+1)*q*A^2 ≤ lowMagnitude m k t q A := by
    apply le_trans _ (data_cap m k t q A)
    calc
      _ = 1*(d+1)*q*A^2 := by ring
      _ ≤ _ := by gcongr
  have hterm : 2^k*(d+1)*q*A^2 ≤ lowMagnitude m k t q A := by
    apply le_trans _ (data_cap m k t q A)
    gcongr
  exact ⟨hraw,hprod',hqdot,hpoly,hterm⟩

theorem lowMagnitude_size (m k t q A : ℕ) :
    (lowMagnitude m k t q A).size ≤ lowBitWidth m k t q A := by
  have hp : lowMagnitude m k t q A ≤
      2^((2*m+1).size+2*k+2*(t+1).size+(q+1).size+2*(A+1).size) := by
    calc
      _ ≤ 2^((2*m+1).size)*2^(2*k)*(2^((t+1).size))^2*
        2^((q+1).size)*(2^((A+1).size))^2 :=
        Nat.mul_le_mul
          (Nat.mul_le_mul
            (Nat.mul_le_mul
              (Nat.mul_le_mul_right _ (Nat.lt_size_self (2*m+1)).le)
              (Nat.pow_le_pow_left (Nat.lt_size_self (t+1)).le 2))
            (Nat.lt_size_self (q+1)).le)
          (Nat.pow_le_pow_left (Nat.lt_size_self (A+1)).le 2)
      _ = _ := by rw [←pow_mul,←pow_mul,←pow_add,←pow_add,←pow_add,←pow_add]; congr 1; omega
  apply Nat.size_le.mpr
  exact hp.trans_lt (Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self _))

theorem bounded_integer_width (m k t q A : ℕ) (z : ℤ)
    (hz : |z| ≤ (lowMagnitude m k t q A:ℤ)) :
    z.natAbs.size ≤ lowBitWidth m k t q A := by
  have hn : z.natAbs ≤ lowMagnitude m k t q A := by
    rw [←Int.natCast_natAbs] at hz
    exact_mod_cast hz
  exact (Nat.size_le_size hn).trans (lowMagnitude_size m k t q A)

/-- The final LOW plus HIGH addition is bounded by actual supplied HIGH
magnitude, rather than assuming a final numerator width. -/
theorem numerator_bound (m k t q A H : ℕ) (low high : ℤ)
    (hl : |low| ≤ (lowMagnitude m k t q A:ℤ)) (hh : |high| ≤ (H:ℤ)) :
    |low+high| ≤ (lowMagnitude m k t q A+H:ℕ) := by
  exact (abs_add_le low high).trans (by exact_mod_cast add_le_add hl hh)

theorem numerator_width (m k t q A H : ℕ) (low high : ℤ)
    (hl : |low| ≤ (lowMagnitude m k t q A:ℤ)) (hh : |high| ≤ (H:ℤ)) :
    (low+high).natAbs.size ≤ lowBitWidth m k t q A+H.size+1 := by
  have hp := numerator_bound m k t q A H low high hl hh
  have hn : (low+high).natAbs ≤ lowMagnitude m k t q A+H := by
    rw [←Int.natCast_natAbs] at hp
    exact_mod_cast hp
  have hlow : lowMagnitude m k t q A < 2^(lowBitWidth m k t q A) :=
    Nat.size_le.mp (lowMagnitude_size m k t q A)
  have hhigh : H < 2^H.size := Nat.lt_size_self H
  apply Nat.size_le.mpr
  calc
    _ ≤ lowMagnitude m k t q A+H := hn
    _ < 2^(lowBitWidth m k t q A)+2^H.size := Nat.add_lt_add hlow hhigh
    _ ≤ 2^(lowBitWidth m k t q A+H.size+1) := by
      have ha : 2^(lowBitWidth m k t q A) ≤ 2^(lowBitWidth m k t q A+H.size) :=
        Nat.pow_le_pow_right (by decide) (by omega)
      have hb : 2^H.size ≤ 2^(lowBitWidth m k t q A+H.size) :=
        Nat.pow_le_pow_right (by decide) (by omega)
      rw [pow_succ]
      omega

#print axioms list_sum_bound
#print axioms qdot_partial_bound
#print axioms polynomialDot_partial_bound
#print axioms lowTerm_bound
#print axioms degree_sum_partial_bound
#print axioms channel_sum_partial_bound
#print axioms run_sum_partial_bound
#print axioms intermediate_caps
#print axioms bounded_integer_width
#print axioms numerator_width

end ThinMatrix.BinaryLowBounds
