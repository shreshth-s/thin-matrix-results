import HalfSourceBinaryScores

set_option autoImplicit false

/-!
# Binary conditional selection on the actual character family

The computable cube enumeration visits all 2^m bit vectors and skips the zero
character. Each nonzero contribution uses the binary score kernel. Selected
bits are stored once. The returned counter covers numerator arithmetic and
comparisons only: enumeration, addresses, Boolean row/sign scans and vector
formation are not silently identified with bit-circuit costs.
-/
namespace ThinMatrix.HalfSourceBinarySelection
open BinaryCell WalshEmbedding HalfSourceGreedy HalfSourceList
open HalfSourceBinaryScores
open scoped BigOperators

theorem sum_nonzero (m : ℕ) (f : Characters m → ℤ) :
    (∑ a : Cube m, if h : a ≠ zeroBits m then f ⟨a,h⟩ else 0) = ∑ a, f a := by
  have h := Fintype.sum_subtype_add_sum_subtype (fun a : Cube m => a ≠ zeroBits m)
    (fun a => if h : a ≠ zeroBits m then f ⟨a,h⟩ else 0)
  rw [← h]
  have hz : (∑ a : {a : Cube m // ¬a ≠ zeroBits m},
      if h : a.val ≠ zeroBits m then f ⟨a.val,h⟩ else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro a _
    exact dif_neg a.property
  rw [hz, add_zero]
  apply Finset.sum_congr rfl
  intro a _
  exact dif_pos a.property

def entry {n : ℕ} (m : ℕ) (ts : Tables) (sums : Characters m → ℤ)
    (rows : Characters m → Cube n) (signs : Characters m → Bool) (i : Fin (2^m)) : Result Cell :=
  let a := (HalfSourceIntegerGreedy.cubeIndex m).symm i
  if h : a ≠ zeroBits m then contribution m ts (sums ⟨a,h⟩) (rows ⟨a,h⟩) (signs ⟨a,h⟩)
  else ⟨zero,0⟩

def score {n : ℕ} (m : ℕ) (ts : Tables) (sums : Characters m → ℤ)
    (rows : Characters m → Cube n) (signs : Characters m → Bool) : Result Cell :=
  sumResults (List.ofFn (entry m ts sums rows signs))

theorem score_view {n : ℕ} (m : ℕ) (sums : Characters m → ℤ)
    (hs : ∀ a, |sums a| ≤ 64*m^3) (rows : Characters m → Cube n) (signs : Characters m → Bool) :
    view (score m (tables m).value sums rows signs).value =
      HalfSourceIntegerScores.score m sums rows signs := by
  let f : Cube m → ℤ := fun a => if h : a ≠ zeroBits m then
    (if rows ⟨a,h⟩ = zeroBits n then HalfSourceIntegerScores.resolved m (sums ⟨a,h⟩) (signs ⟨a,h⟩)
      else HalfSourceIntegerScores.unresolved m (sums ⟨a,h⟩) : ℕ) else 0
  have he (i : Fin (2^m)) : view (entry m (tables m).value sums rows signs i).value =
      f ((HalfSourceIntegerGreedy.cubeIndex m).symm i) := by
    dsimp only [entry, f]
    by_cases h : (HalfSourceIntegerGreedy.cubeIndex m).symm i ≠ zeroBits m
    · simp only [dif_pos h]
      exact contribution_view m _ (hs _) _ _
    · simp only [dif_neg h, zero_view]
  simp only [score, sumResults_view, List.map_ofFn, List.sum_ofFn, Function.comp_apply, he]
  rw [(HalfSourceIntegerGreedy.cubeIndex m).symm.sum_comp f]
  dsimp only [f]
  rw [sum_nonzero m (fun a => (if rows a = zeroBits n then
    HalfSourceIntegerScores.resolved m (sums a) (signs a)
    else HalfSourceIntegerScores.unresolved m (sums a) : ℕ))]
  simp only [HalfSourceIntegerScores.score, Nat.cast_sum]

theorem entry_nonneg {n : ℕ} (m : ℕ) (sums : Characters m → ℤ)
    (hs : ∀ a, |sums a| ≤ 64*m^3) (rows : Characters m → Cube n)
    (signs : Characters m → Bool) (i : Fin (2^m)) :
    0 ≤ view (entry m (tables m).value sums rows signs i).value := by
  dsimp only [entry]
  split_ifs
  · rw [contribution_view m _ (hs _)]
    positivity
  · exact le_rfl

theorem entry_price {n : ℕ} (m : ℕ) (sums : Characters m → ℤ)
    (hs : ∀ a, |sums a| ≤ 64*m^3) (rows : Characters m → Cube n)
    (signs : Characters m → Bool) (i : Fin (2^m)) :
    (entry m (tables m).value sums rows signs i).bitSteps ≤ 8*unit m+1 := by
  dsimp only [entry]
  split_ifs
  · exact contribution_price m _ (hs _) _ _
  · exact Nat.zero_le _

theorem score_price {n : ℕ} (m : ℕ) (sums : Characters m → ℤ)
    (hs : ∀ a, |sums a| ≤ 64*m^3) (rows : Characters m → Cube n) (signs : Characters m → Bool) :
    (score m (tables m).value sums rows signs).bitSteps ≤ 2^m*(9*unit m+1)+1 := by
  let xs := List.ofFn (entry m (tables m).value sums rows signs)
  have hh := sumResults_price m (8*unit m+1) xs
    (by intro x hx; obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx; exact entry_nonneg m sums hs rows signs i)
    (by
      rw [← sumResults_view]
      change view (score m (tables m).value sums rows signs).value ≤ _
      rw [score_view m sums hs]
      have h := HalfSourceIntegerScores.score_le m sums hs rows signs
      rw [characters_card] at h
      exact_mod_cast h.trans (Nat.mul_le_mul_right _ (Nat.sub_le _ _)))
    (by intro x hx; obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx; exact entry_price m sums hs rows signs i)
  have hlen : xs.length = 2^m := List.length_ofFn
  rw [hlen] at hh
  change (sumResults xs).bitSteps ≤ _
  convert hh using 1
  ring

def chosen {n : ℕ} (m : ℕ) (ts : Tables) (sums : Characters m → ℤ)
    (rows : Characters m → Cube (n+1)) (signs : Characters m → Bool) : Result Bool :=
  let left := score m ts sums (tails rows) (updateSigns rows signs false)
  let right := score m ts sums (tails rows) (updateSigns rows signs true)
  let compared := BackendScalarBits.unsignedLessCounted right.value.bits.magnitude left.value.bits.magnitude
  ⟨compared.1,left.bitSteps+right.bitSteps+compared.2⟩

theorem chosen_value {n : ℕ} (m : ℕ) (sums : Characters m → ℤ)
    (hs : ∀ a, |sums a| ≤ 64*m^3) (rows : Characters m → Cube (n+1)) (signs : Characters m → Bool) :
    (chosen m (tables m).value sums rows signs).value =
      HalfSourceIntegerScores.chosen m sums rows signs := by
  apply Bool.eq_iff_iff.mpr
  simp only [chosen, HalfSourceIntegerScores.chosen, BackendScalarBits.unsignedLess_correct,
    decide_eq_true_eq]
  rw [← IntegerArithmetic.signedValue_natAbs, ← IntegerArithmetic.signedValue_natAbs]
  change (view (score m (tables m).value sums _ _).value).natAbs <
      (view (score m (tables m).value sums _ _).value).natAbs ↔ _
  rw [score_view m sums hs, score_view m sums hs, Int.natAbs_natCast, Int.natAbs_natCast]

def choiceBound (m : ℕ) : ℕ := 2*(2^m*(9*unit m+1)+1)+unit m

theorem chosen_price {n : ℕ} (m : ℕ) (sums : Characters m → ℤ)
    (hs : ∀ a, |sums a| ≤ 64*m^3) (rows : Characters m → Cube (n+1)) (signs : Characters m → Bool) :
    (chosen m (tables m).value sums rows signs).bitSteps ≤ choiceBound m := by
  have hl := score_price m sums hs (tails rows) (updateSigns rows signs false)
  have hr := score_price m sums hs (tails rows) (updateSigns rows signs true)
  have hsize (b : Bool) :
      (score m (tables m).value sums (tails rows) (updateSigns rows signs b)).value.bits.magnitude.length ≤ width m := by
    rw [canonical, score_view m sums hs, Int.natAbs_natCast]
    exact HalfSourceIntegerScores.score_bits m sums hs (by rw [characters_card]; exact Nat.sub_le _ _) _ _
  have hc := BackendScalarBits.unsignedLess_price (width m) _ _ (hsize true) (hsize false)
  have hu : BackendScalarBits.scalarUnit (width m) ≤ unit m := by
    unfold unit BackendScalarBits.backendScalarUnit
    omega
  dsimp only [chosen, choiceBound]
  omega

/-- The selected vector retains every comparison's returned Boolean once. -/
def select (m : ℕ) (ts : Tables) (sums : Characters m → ℤ) :
    (n : ℕ) → (Characters m → Cube n) → (Characters m → Bool) → Result (Vector Bool n)
  | 0, _, _ => ⟨Vector.ofFn (fun i => Fin.elim0 i), 1⟩
  | n+1, rows, signs =>
      let b := chosen m ts sums rows signs
      let rest := select m ts sums n (tails rows) (updateSigns rows signs b.value)
      ⟨Vector.ofFn (Fin.cons b.value (HalfSourceIntegerGreedy.vectorBits rest.value)),
        b.bitSteps+rest.bitSteps⟩

theorem select_value (m : ℕ) (hm : 0 < m) (sums : Characters m → ℤ)
    (hs : ∀ a, |sums a| ≤ 64*m^3) (n : ℕ) (rows : Characters m → Cube n)
    (signs : Characters m → Bool) :
    HalfSourceIntegerGreedy.vectorBits (select m (tables m).value sums n rows signs).value =
      HalfSourceGreedy.select (rationalBase m) (fun a => rationalBase m^sums a)
        (fun a => rationalBase m^(-sums a)) n rows signs := by
  induction n generalizing signs with
  | zero => exact Subsingleton.elim _ _
  | succ n ih =>
    simp only [select, HalfSourceIntegerGreedy.vectorBits_ofFn, HalfSourceGreedy.select,
      chosen_value m sums hs, HalfSourceIntegerScores.chosen_eq m hm sums hs, ih]

theorem select_price (m : ℕ) (sums : Characters m → ℤ)
    (hs : ∀ a, |sums a| ≤ 64*m^3) (n : ℕ) (rows : Characters m → Cube n)
    (signs : Characters m → Bool) :
    (select m (tables m).value sums n rows signs).bitSteps ≤ n*choiceBound m+1 := by
  induction n generalizing signs with
  | zero => simp [select]
  | succ n ih =>
    have hc := chosen_price m sums hs rows signs
    have hr := ih (tails rows) (updateSigns rows signs (chosen m (tables m).value sums rows signs).value)
    change (chosen m (tables m).value sums rows signs).bitSteps +
      (select m (tables m).value sums n (tails rows)
        (updateSigns rows signs (chosen m (tables m).value sums rows signs).value)).bitSteps ≤ _
    nlinarith

/-- The state representation and native small signed-sum update are shared
with the integer program. This counter prices the binary score subprograms,
not the remaining state/control operations. -/
def build (m : ℕ) (ts : Tables) : ℕ → Result (HalfSourceIntegerGreedy.State m)
  | 0 => ⟨⟨[], HalfSourceIntegerGreedy.storeSums m (fun _ => 0)⟩, 1⟩
  | j+1 =>
      let prev := build m ts j
      let selected := select m ts prev.value.sums m (fun a => a.val) (fun _ => false)
      let d := HalfSourceIntegerGreedy.vectorBits selected.value
      ⟨⟨d::prev.value.entries, HalfSourceIntegerGreedy.storeSums m
          (fun a => prev.value.sums a+sign (dotBits a.val d))⟩,
        prev.bitSteps+selected.bitSteps⟩

theorem build_length (m : ℕ) (ts : Tables) (j : ℕ) : (build m ts j).value.entries.length = j := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [build, List.length_cons, ih]

theorem build_sums (m : ℕ) (ts : Tables) (j : ℕ) (a : Characters m) :
    (build m ts j).value.sums a = sumSign (build m ts j).value.entries a.val := by
  induction j with
  | zero => simp [build, sumSign]
  | succ j ih => simp only [build, HalfSourceIntegerGreedy.sums_mk, sumSign_cons, ih]

theorem build_sum_bound (m : ℕ) (ts : Tables) (j : ℕ) (hj : j ≤ 64*m^3) (a : Characters m) :
    |(build m ts j).value.sums a| ≤ 64*m^3 := by
  rw [build_sums]
  have h := HalfSourceIntegerGreedy.sumSign_abs_le_length (build m ts j).value.entries a.val
  rw [build_length] at h
  exact h.trans (by exact_mod_cast hj)

theorem build_value (m : ℕ) (hm : 0 < m) (j : ℕ) (hj : j ≤ 64*m^3) :
    (build m (tables m).value j).value.entries = HalfSourceList.build m (rationalBase m) j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have hj' : j ≤ 64*m^3 := by omega
    have hs := build_sum_bound m (tables m).value j hj'
    rw [build, HalfSourceList.build]
    dsimp only
    rw [select_value m hm _ hs]
    have sums_eq : (build m (tables m).value j).value.sums =
        fun a => sumSign (HalfSourceList.build m (rationalBase m) j) a.val := by
      funext a
      rw [build_sums, ih hj']
    rw [sums_eq, ih hj']
    rfl

theorem build_price (m j : ℕ) (hj : j ≤ 64*m^3) :
    (build m (tables m).value j).bitSteps ≤ j*(m*choiceBound m+1)+1 := by
  induction j with
  | zero => simp [build]
  | succ j ih =>
    have hj' : j ≤ 64*m^3 := by omega
    have hi := ih hj'
    have hs := select_price m _ (build_sum_bound m (tables m).value j hj') m
      (fun a => a.val) (fun _ => false)
    change (build m (tables m).value j).bitSteps +
      (select m (tables m).value (build m (tables m).value j).value.sums m
        (fun a => a.val) (fun _ => false)).bitSteps ≤ _
    nlinarith

def translations (m : ℕ) : Result (List (Cube m)) :=
  let ts := tables m
  let result := build m ts.value (64*m^3)
  ⟨result.value.entries,ts.bitSteps+result.bitSteps⟩

theorem translations_value (m : ℕ) (hm : 0 < m) :
    (translations m).value = HalfSourceList.translations m := build_value m hm _ le_rfl

/-- The complete list's numerator arithmetic is 2^m times a polynomial.
This is deliberately not a bound for its uncharged control/state operations. -/
theorem translations_arithmetic_price (m : ℕ) :
    (translations m).bitSteps ≤
      2*(width m+2)+2*((2*HalfSourceIntegerScores.K m+1)*
        (2*HalfSourceIntegerScores.K m*unit m+1))+
      64*m^3*(m*choiceBound m+1)+1 := by
  have ht := tables_price m
  have hb := build_price m (64*m^3) le_rfl
  change (tables m).bitSteps+(build m (tables m).value (64*m^3)).bitSteps ≤ _
  omega

#print axioms sum_nonzero
#print axioms score_view
#print axioms entry_nonneg
#print axioms entry_price
#print axioms score_price
#print axioms chosen_value
#print axioms chosen_price
#print axioms select_value
#print axioms select_price
#print axioms build_length
#print axioms build_sums
#print axioms build_sum_bound
#print axioms build_value
#print axioms build_price
#print axioms translations_value
#print axioms translations_arithmetic_price
end ThinMatrix.HalfSourceBinarySelection
