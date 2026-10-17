import EndToEndAPSP

/-!
Literal factor-table validation. Primality is tested by a trial-divisor
loop, distinctness by charged list scans, and exclusion of three by a
literal comparison. Mathematical primality and nodup propositions appear
only in the correctness theorem; the executable validator does not call
their decision procedures.

The returned work counts scalar remainder/comparison and list/control
sites. Pricing their bounded integer operands or compiling them into a
word machine is separate from this scalar-site ledger.
-/

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace ThinMatrix.FactorValidation

/-- Check all candidates below `fuel`. Both the previous Boolean and its
counter are retained; no short circuit hides a data-dependent loop. -/
def trialDivisors (p : ℕ) : ℕ → Bool × ℕ
  | 0 => (true,1)
  | fuel+1 =>
    let previous := trialDivisors p fuel
    let passes := if fuel<2 then true else decide (p%fuel≠0)
    (previous.1 && passes,previous.2+8)

theorem trialDivisors_correct (p fuel : ℕ) :
    (trialDivisors p fuel).1=true ↔ ∀ i : ℕ, i < fuel → 2 ≤ i → p % i ≠ 0 := by
  induction fuel with
  | zero => simp [trialDivisors]
  | succ fuel ih =>
    simp only [trialDivisors,Bool.and_eq_true,ih]
    constructor
    · rintro ⟨hprev,hnow⟩ i hi hi2
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt|rfl
      · exact hprev i hlt hi2
      · simpa only [if_neg (by omega : ¬i<2),decide_eq_true_eq] using hnow
    · intro h
      constructor
      · exact fun i hi hi2 => h i (Nat.lt_succ_of_lt hi) hi2
      · by_cases hf : fuel<2
        · simp only [if_pos hf]
        · simpa only [if_neg hf,decide_eq_true_eq] using h fuel (by omega) (by omega)

theorem trialDivisors_work (p fuel : ℕ) : (trialDivisors p fuel).2=8*fuel+1 := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simp only [trialDivisors,ih];omega

def trialPrime (p : ℕ) : Bool × ℕ :=
  let divisors := trialDivisors p p
  (decide (2≤p) && divisors.1,divisors.2+4)

theorem trialPrime_correct (p : ℕ) : (trialPrime p).1=true ↔ Nat.Prime p := by
  simp only [trialPrime,Bool.and_eq_true,decide_eq_true_eq,trialDivisors_correct]
  rw [Nat.prime_def_lt']
  constructor
  · rintro ⟨hp,ht⟩
    refine ⟨hp,fun i hi hip hd => ?_⟩
    exact ht i hip hi (Nat.mod_eq_zero_of_dvd hd)
  · rintro ⟨hp,ht⟩
    exact ⟨hp,fun i hip hi hm => ht i hi hip (Nat.dvd_of_mod_eq_zero hm)⟩

theorem trialPrime_work (p : ℕ) : (trialPrime p).2=8*p+5 := by
  simp only [trialPrime,trialDivisors_work]


def notMember (p : ℕ) : List ℕ → Bool × ℕ
  | [] => (true,1)
  | a::as =>
    let rest := notMember p as
    (decide (p≠a) && rest.1,rest.2+4)

theorem notMember_correct (p : ℕ) (as : List ℕ) :
    (notMember p as).1=true ↔ p∉as := by
  induction as with
  | nil => simp [notMember]
  | cons a as ih => simp [notMember,ih]

theorem notMember_work (p : ℕ) (as : List ℕ) :
    (notMember p as).2=4*as.length+1 := by
  induction as with
  | nil => rfl
  | cons a as ih => simp only [notMember,ih,List.length_cons];omega

def validate : List ℕ → Bool × ℕ
  | [] => (true,1)
  | p::ps =>
    let rest := validate ps
    let prime := trialPrime p
    let distinct := notMember p ps
    (prime.1 && distinct.1 && decide (p≠3) && rest.1,
      rest.2+prime.2+distinct.2+8)

theorem validate_correct (factors : List ℕ) :
    (validate factors).1=true ↔ EndToEndAPSP.ValidFactors factors := by
  induction factors with
  | nil => simp [validate,EndToEndAPSP.ValidFactors]
  | cons p ps ih =>
    simp only [validate,Bool.and_eq_true,trialPrime_correct,notMember_correct,
      decide_eq_true_eq,ih,EndToEndAPSP.ValidFactors,List.nodup_cons,List.forall_mem_cons]
    tauto

theorem validate_work_exact (factors : List ℕ) :
    (validate factors).2=8*factors.sum+2*factors.length^2+12*factors.length+1 := by
  induction factors with
  | nil => norm_num [validate]
  | cons p ps ih =>
    simp only [validate,ih,trialPrime_work,notMember_work,List.sum_cons,List.length_cons]
    ring

theorem validate_work (factors : List ℕ) :
    (validate factors).2≤32*(factors.length+1)^2*(factors.sum+1) := by
  rw [validate_work_exact]
  have hsq : 1≤(factors.length+1)^2 := Nat.one_le_pow 2 (factors.length+1) (by omega)
  have hsum : 8*factors.sum≤8*(factors.length+1)^2*(factors.sum+1) := by
    calc
      _≤8*(factors.sum+1) := Nat.mul_le_mul_left 8 (by omega)
      _=8*1*(factors.sum+1) := by ring
      _≤_ := by gcongr
  have hquad : 2*factors.length^2+12*factors.length+1≤24*(factors.length+1)^2 := by
    nlinarith
  have hrest := hquad.trans (Nat.le_mul_of_pos_right _ (by omega : 0<factors.sum+1))
  calc
    _=8*factors.sum+(2*factors.length^2+12*factors.length+1) := by ring
    _≤8*(factors.length+1)^2*(factors.sum+1)+24*(factors.length+1)^2*(factors.sum+1) :=
      Nat.add_le_add hsum hrest
    _=_ := by ring

theorem positive_product (ps : List ℕ) (hpos : ∀ p ∈ ps, 0<p) : 0<ps.prod :=
  List.prod_pos hpos

theorem factor_le_product (ps : List ℕ) (hpos : ∀ p ∈ ps, 0<p)
    {p : ℕ} (hp : p∈ps) : p≤ps.prod :=
  Nat.le_of_dvd (List.prod_pos hpos) (List.dvd_prod hp)

theorem sum_le_length_product (ps : List ℕ) (hpos : ∀ p ∈ ps, 0<p) :
    ps.sum≤ps.length*ps.prod := by
  simpa using List.sum_le_card_nsmul ps ps.prod (fun p hp => factor_le_product ps hpos hp)

theorem valid_factor_positive (ps : List ℕ) (hv : EndToEndAPSP.ValidFactors ps) :
    ∀p∈ps, 0<p := fun p hp => (hv.2 p hp).1.pos

theorem valid_sum_le_length_product (ps : List ℕ) (hv : EndToEndAPSP.ValidFactors ps) :
    ps.sum≤ps.length*ps.prod :=
  sum_le_length_product ps (valid_factor_positive ps hv)

theorem history_sum_le (selected : List ℕ) (candidate S : ℕ)
    (hv : EndToEndAPSP.ValidFactors (selected++[candidate])) :
    (selected++[candidate]).sum≤(selected.length+1)*
      ((selected++[candidate]).take S).prod*((selected++[candidate]).drop S).prod := by
  have h := valid_sum_le_length_product (selected++[candidate]) hv
  simpa only [List.length_append,List.length_singleton,←List.prod_take_mul_prod_drop
    (selected++[candidate]) S,Nat.mul_assoc] using h

theorem history_sum_le_folded_bound (selected : List ℕ) (candidate S D : ℕ)
    (hv : EndToEndAPSP.ValidFactors (selected++[candidate]))
    (hd : ((selected++[candidate]).take S).prod≤D) :
    (selected++[candidate]).sum≤(selected.length+1)*D*((selected++[candidate]).drop S).prod :=
  (history_sum_le selected candidate S hv).trans
    (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hd))

/-- For valid factors the whole trial-division scan costs only a fixed
polynomial in the history length times the product of the factors. -/
theorem validate_work_product (factors : List ℕ) (hv : EndToEndAPSP.ValidFactors factors) :
    (validate factors).2≤32*(factors.length+1)^3*factors.prod := by
  have hsum := valid_sum_le_length_product factors hv
  have hp := positive_product factors (valid_factor_positive factors hv)
  have hs : factors.sum+1≤(factors.length+1)*factors.prod := by nlinarith
  calc
    _≤32*(factors.length+1)^2*(factors.sum+1) := validate_work factors
    _≤32*(factors.length+1)^2*((factors.length+1)*factors.prod) :=
      Nat.mul_le_mul_left _ hs
    _=_ := by ring

theorem validate_history_work (selected : List ℕ) (candidate S D : ℕ)
    (hv : EndToEndAPSP.ValidFactors (selected++[candidate]))
    (hd : ((selected++[candidate]).take S).prod≤D) :
    (validate (selected++[candidate])).2≤
      32*(selected.length+2)^3*D*((selected++[candidate]).drop S).prod := by
  have h := validate_work_product (selected++[candidate]) hv
  rw [←List.prod_take_mul_prod_drop (selected++[candidate]) S] at h
  simp only [List.length_append,List.length_singleton] at h
  calc
    _≤32*(selected.length+1+1)^3*
      (((selected++[candidate]).take S).prod*((selected++[candidate]).drop S).prod) := h
    _≤32*(selected.length+1+1)^3*(D*((selected++[candidate]).drop S).prod) := by gcongr
    _=_ := by ring

/-- Compute both factor products in one physical traversal, without
allocating prefix and suffix lists. -/
def splitProducts : ℕ → List ℕ → (ℕ×ℕ)×ℕ
  | _,[] => ((1,1),1)
  | S,p::ps =>
    let tail := splitProducts (S-1) ps
    if S=0 then ((tail.1.1,p*tail.1.2),tail.2+8)
    else ((p*tail.1.1,tail.1.2),tail.2+8)

theorem splitProducts_value (S : ℕ) (factors : List ℕ) :
    (splitProducts S factors).1=((factors.take S).prod,(factors.drop S).prod) := by
  induction factors generalizing S with
  | nil => simp [splitProducts]
  | cons p ps ih =>
    cases S with
    | zero => simp [splitProducts,ih]
    | succ S => simp [splitProducts,ih]

theorem splitProducts_work (S : ℕ) (factors : List ℕ) :
    (splitProducts S factors).2=8*factors.length+1 := by
  induction factors generalizing S with
  | nil => rfl
  | cons p ps ih =>
    simp only [splitProducts]
    split_ifs <;> simp only [ih,List.length_cons] <;> omega

end ThinMatrix.FactorValidation

#print axioms ThinMatrix.FactorValidation.trialPrime_correct
#print axioms ThinMatrix.FactorValidation.validate_correct
#print axioms ThinMatrix.FactorValidation.validate_work_exact
#print axioms ThinMatrix.FactorValidation.validate_work
#print axioms ThinMatrix.FactorValidation.validate_history_work
#print axioms ThinMatrix.FactorValidation.splitProducts_value
#print axioms ThinMatrix.FactorValidation.splitProducts_work
