import BinaryCell
import HalfSourceIntegerGreedy

set_option autoImplicit false

/-!
# Binary arithmetic for the shared-denominator scores

The power tables, products and nonnegative sums use stored binary cells and
the existing charged bit circuits. Only the two public bases are loaded from
natural numbers. The counters in this file count those circuits; table access,
index arithmetic, character enumeration and loop control require separate
charges before this is a bound for the complete translation-list program.
-/
namespace ThinMatrix.HalfSourceBinaryScores
open BinaryCell HalfSourceIntegerScores
open scoped BigOperators

def width (m : ℕ) : ℕ := m+2+A m*(2*K m)+1
def unit (m : ℕ) : ℕ := BackendScalarBits.backendScalarUnit (width m)
def limit (m : ℕ) : ℕ := 2^m*(4*A m^(2*K m))

theorem size_bound (m x : ℕ) (hx : x ≤ limit m) : x.size ≤ width m := by
  have hA : A m ≤ 2^(A m) := (Nat.lt_two_pow_self).le
  have hp : A m^(2*K m) ≤ 2^(A m*(2*K m)) := by
    calc
      _ ≤ (2^(A m))^(2*K m) := Nat.pow_le_pow_left hA _
      _ = _ := (pow_mul _ _ _).symm
  have hb : x ≤ 2^(m+2+A m*(2*K m)) := by
    calc
      _ ≤ 2^m*(4*A m^(2*K m)) := hx
      _ ≤ 2^m*(4*2^(A m*(2*K m))) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hp)
      _ = _ := by rw [pow_add, pow_add]; ring
  apply Nat.size_le.mpr
  exact lt_of_le_of_lt hb (by
    unfold width
    rw [pow_succ]
    have := Nat.two_pow_pos (m+2+A m*(2*K m))
    omega)

theorem power_le_limit (m : ℕ) : A m^(2*K m) ≤ limit m := by
  unfold limit
  have := Nat.two_pow_pos m
  calc
    _ = 1*(A m^(2*K m)) := by ring
    _ ≤ (2^m*4)*(A m^(2*K m)) := Nat.mul_le_mul_right _ (by omega)
    _ = _ := by ring

def one : Cell := ⟨oneBits, by decide⟩
@[simp] theorem one_view : view one = 1 := rfl

/-- Repeated multiplication consumes the stored previous result. -/
def power (base : Cell) : ℕ → Result Cell
  | 0 => ⟨one, 1⟩
  | n+1 =>
      let prev := power base n
      let product := mul prev.value base
      ⟨product.value, prev.bitSteps+product.bitSteps⟩

@[simp] theorem power_view (base : Cell) (n : ℕ) :
    view (power base n).value = view base^n := by
  induction n with
  | zero => simp [power]
  | succ n ih => simp only [power, mul_view, ih, pow_succ]

theorem power_price (m : ℕ) (base : Cell) (b n : ℕ)
    (hb : view base = b) (hbase : b ≤ A m) (hn : n ≤ 2*K m) :
    (power base n).bitSteps ≤ n*unit m+1 := by
  have hp (k : ℕ) (hk : k ≤ 2*K m) : b^k ≤ limit m := by
    exact ((Nat.pow_le_pow_left hbase _).trans
      (Nat.pow_le_pow_right (by unfold A; omega) hk)).trans (power_le_limit m)
  have hbsize : (view base).natAbs.size ≤ width m := by
    rw [hb, Int.natAbs_natCast]
    apply size_bound
    simpa using hp 1 (by unfold K; omega)
  induction n with
  | zero => simp [power]
  | succ n ih =>
    have hn' : n ≤ 2*K m := by omega
    have hsize : (view (power base n).value).natAbs.size ≤ width m := by
      rw [power_view, hb, ← Nat.cast_pow, Int.natAbs_natCast]
      exact size_bound m _ (hp n hn')
    have hc := mul_price (width m) (power base n).value base hsize hbsize
    have hi := ih hn'
    change (power base n).bitSteps + (mul (power base n).value base).bitSteps ≤ _
    dsimp only [unit] at *
    nlinarith

abbrev Tables := Array Cell × Array Cell

/-- Independent powers are each evaluated once and retained. The quadratic
number of multiplications in K still has polynomial cost in m. -/
def tables (m : ℕ) : Result Tables :=
  let a := BinaryArrayFFT.loadInteger (A m)
  let b := BinaryArrayFFT.loadInteger (B m)
  let left := BinaryArrayCosts.tabulate (2*K m+1) (fun i => power a.value i.val)
  let right := BinaryArrayCosts.tabulate (2*K m+1) (fun i => power b.value i.val)
  ⟨(left.value,right.value),a.bitSteps+b.bitSteps+left.bitSteps+right.bitSteps⟩

theorem tables_left (m k : ℕ) (hk : k ≤ 2*K m) :
    view ((tables m).value.1.getD k zero) = (A m:ℤ)^k := by
  dsimp only [tables]
  rw [BinaryArrayCosts.tabulate_getD (2*K m+1) _ k (by omega), power_view]
  simp only [view, BinaryArrayFFT.loadInteger_view]

theorem tables_right (m k : ℕ) (hk : k ≤ 2*K m) :
    view ((tables m).value.2.getD k zero) = (B m:ℤ)^k := by
  dsimp only [tables]
  rw [BinaryArrayCosts.tabulate_getD (2*K m+1) _ k (by omega), power_view]
  simp only [view, BinaryArrayFFT.loadInteger_view]

theorem tables_price (m : ℕ) :
    (tables m).bitSteps ≤ 2*(width m+2)+2*((2*K m+1)*(2*K m*unit m+1)) := by
  have hA : A m ≤ A m := le_rfl
  have hB : B m ≤ A m := by unfold A B; omega
  have hbase (b : ℕ) (hb : b ≤ A m) : b.size ≤ width m := by
    apply size_bound
    exact (hb.trans (by
      simpa using Nat.pow_le_pow_right (show 0 < A m by unfold A; omega)
        (show 1 ≤ 2*K m by unfold K; omega))).trans (power_le_limit m)
  have ha := BinaryArrayCosts.tabulate_bitSteps_bound (2*K m+1)
    (fun i => power (BinaryArrayFFT.loadInteger (A m)).value i.val)
    (2*K m*unit m+1) (fun i => (power_price m _ (A m) i.val
      (BinaryArrayFFT.loadInteger_view _) hA (by omega)).trans (by gcongr; omega))
  have hb := BinaryArrayCosts.tabulate_bitSteps_bound (2*K m+1)
    (fun i => power (BinaryArrayFFT.loadInteger (B m)).value i.val)
    (2*K m*unit m+1) (fun i => (power_price m _ (B m) i.val
      (BinaryArrayFFT.loadInteger_view _) hB (by omega)).trans (by gcongr; omega))
  have hload (b : ℕ) : (BinaryArrayFFT.loadInteger b).bitSteps = b.size+2 := by
    simp [BinaryArrayFFT.loadInteger, FFTBitCost.registerInput]
  simp only [tables, hload]
  have := hbase _ hA
  have := hbase _ hB
  omega

def numerator (m : ℕ) (ts : Tables) (t : ℤ) : Result Cell :=
  mul (ts.1.getD ((K m:ℤ)+t).toNat zero) (ts.2.getD ((K m:ℤ)-t).toNat zero)

theorem numerator_view (m : ℕ) (t : ℤ)
    (ht : -(K m:ℤ) ≤ t ∧ t ≤ K m) :
    view (numerator m (tables m).value t).value = powerNumerator m t := by
  simp only [numerator, mul_view, tables_left m ((K m:ℤ)+t).toNat (by omega),
    tables_right m ((K m:ℤ)-t).toNat (by omega),
    powerNumerator, Nat.cast_mul, Nat.cast_pow]

theorem numerator_price (m : ℕ) (t : ℤ)
    (ht : -(K m:ℤ) ≤ t ∧ t ≤ K m) :
    (numerator m (tables m).value t).bitSteps ≤ unit m := by
  apply mul_price
  · rw [tables_left _ _ (by omega), ← Nat.cast_pow, Int.natAbs_natCast]
    exact size_bound m _ ((Nat.pow_le_pow_right (by unfold A; omega)
      (show ((K m:ℤ)+t).toNat ≤ 2*K m by omega)).trans (power_le_limit m))
  · rw [tables_right _ _ (by omega), ← Nat.cast_pow, Int.natAbs_natCast]
    apply size_bound
    exact ((Nat.pow_le_pow_left (show B m ≤ A m by unfold A B; omega) _).trans
      (Nat.pow_le_pow_right (by unfold A; omega)
        (show ((K m:ℤ)-t).toNat ≤ 2*K m by omega))).trans (power_le_limit m)

theorem cell_size (m : ℕ) (x : Cell) (hx0 : 0 ≤ view x) (hx : view x ≤ limit m) :
    (view x).natAbs.size ≤ width m := by
  apply size_bound
  exact_mod_cast (show ((view x).natAbs:ℤ) ≤ limit m by
    rw [Int.natAbs_of_nonneg hx0]; exact hx)

/-- Accumulate stored results, retaining the recursive sum and every bit count. -/
def sumResults : List (Result Cell) → Result Cell
  | [] => ⟨zero, 1⟩
  | x::xs =>
      let rest := sumResults xs
      let total := add x.value rest.value
      ⟨total.value, x.bitSteps+rest.bitSteps+total.bitSteps⟩

@[simp] theorem sumResults_view (xs : List (Result Cell)) :
    view (sumResults xs).value = (xs.map (fun x => view x.value)).sum := by
  induction xs with
  | nil => simp [sumResults]
  | cons x xs ih => simp only [sumResults, add_view, ih, List.map_cons, List.sum_cons]

theorem sum_nonneg (xs : List (Result Cell))
    (h : ∀ x ∈ xs, 0 ≤ view x.value) : 0 ≤ (xs.map (fun x => view x.value)).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := h x (by simp)
    have ht := ih (fun y hy => h y (by simp [hy]))
    simpa using add_nonneg hx ht

theorem sumResults_price (m C : ℕ) (xs : List (Result Cell))
    (hnonneg : ∀ x ∈ xs, 0 ≤ view x.value)
    (htotal : (xs.map (fun x => view x.value)).sum ≤ limit m)
    (hcost : ∀ x ∈ xs, x.bitSteps ≤ C) :
    (sumResults xs).bitSteps ≤ xs.length*(C+unit m)+1 := by
  induction xs with
  | nil => simp [sumResults]
  | cons x xs ih =>
    have hx0 := hnonneg x (by simp)
    have ht0 := sum_nonneg xs (fun y hy => hnonneg y (by simp [hy]))
    have ht : (xs.map (fun x => view x.value)).sum ≤ limit m := by
      simp only [List.map_cons, List.sum_cons] at htotal
      omega
    have hx : view x.value ≤ limit m := by
      simp only [List.map_cons, List.sum_cons] at htotal
      omega
    have hc := add_price (width m) x.value (sumResults xs).value
      (cell_size m _ hx0 hx)
      (cell_size m _ (by simpa using ht0) (by simpa using ht))
    have hi := ih (fun y hy => hnonneg y (by simp [hy])) ht
      (fun y hy => hcost y (by simp [hy]))
    have hxC := hcost x (by simp)
    change x.bitSteps+(sumResults xs).bitSteps+
      (add x.value (sumResults xs).value).bitSteps ≤ (xs.length+1)*(C+unit m)+1
    dsimp only [unit] at *
    nlinarith

theorem four_power_le_limit (m : ℕ) : 4*A m^(2*K m) ≤ limit m := by
  exact Nat.le_mul_of_pos_left _ (Nat.two_pow_pos m)

theorem signed_window (m : ℕ) (s : ℤ) (hs : |s| ≤ 64*m^3) (b : Bool) :
    -(K m:ℤ) ≤ s+HalfSourceList.sign b ∧ s+HalfSourceList.sign b ≤ K m := by
  have hs' := abs_le.mp hs
  have hb : HalfSourceList.sign b = 1 ∨ HalfSourceList.sign b = -1 := by
    cases b <;> simp [HalfSourceList.sign]
  simp only [K, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow, Nat.cast_one]
  rcases hb with hb | hb <;> omega

theorem neighbor_window (m : ℕ) (s : ℤ) (hs : |s| ≤ 64*m^3) (t : ℤ)
    (ht : t=s+1 ∨ t=s-1 ∨ t=-s+1 ∨ t=-s-1) :
    -(K m:ℤ) ≤ t ∧ t ≤ K m := by
  have hs' := abs_le.mp hs
  simp only [K, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow, Nat.cast_one]
  rcases ht with ht | ht | ht | ht <;> omega

def resolved (m : ℕ) (ts : Tables) (s : ℤ) (b : Bool) : Result Cell :=
  let p := numerator m ts (s+HalfSourceList.sign b)
  let q := numerator m ts (-(s+HalfSourceList.sign b))
  let total := add p.value q.value
  let doubled := add total.value total.value
  ⟨doubled.value, p.bitSteps+q.bitSteps+total.bitSteps+doubled.bitSteps⟩

theorem resolved_view (m : ℕ) (s : ℤ) (hs : |s| ≤ 64*m^3) (b : Bool) :
    view (resolved m (tables m).value s b).value = HalfSourceIntegerScores.resolved m s b := by
  have ht := signed_window m s hs b
  have ht' : -(K m:ℤ) ≤ -(s+HalfSourceList.sign b) ∧ -(s+HalfSourceList.sign b) ≤ K m := by omega
  simp only [resolved, add_view, numerator_view m _ ht, numerator_view m _ ht',
    HalfSourceIntegerScores.resolved, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat]
  ring

theorem resolved_price (m : ℕ) (s : ℤ) (hs : |s| ≤ 64*m^3) (b : Bool) :
    (resolved m (tables m).value s b).bitSteps ≤ 4*unit m := by
  have ht := signed_window m s hs b
  have ht' : -(K m:ℤ) ≤ -(s+HalfSourceList.sign b) ∧ -(s+HalfSourceList.sign b) ≤ K m := by omega
  have hp := numerator_price m _ ht
  have hq := numerator_price m _ ht'
  have hpv := numerator_view m _ ht
  have hqv := numerator_view m _ ht'
  have hpbound := powerNumerator_le m _ ht
  have hqbound := powerNumerator_le m _ ht'
  have hlim := four_power_le_limit m
  have hsum : powerNumerator m (s+HalfSourceList.sign b) +
      powerNumerator m (-(s+HalfSourceList.sign b)) ≤ limit m := by omega
  have hpsize : (view (numerator m (tables m).value (s+HalfSourceList.sign b)).value).natAbs.size ≤ width m := by
    rw [hpv, Int.natAbs_natCast]; exact size_bound m _ (by omega)
  have hqsize : (view (numerator m (tables m).value (-(s+HalfSourceList.sign b))).value).natAbs.size ≤ width m := by
    rw [hqv, Int.natAbs_natCast]; exact size_bound m _ (by omega)
  have hadd := add_price (width m) _ _ hpsize hqsize
  have hzsize : (view (add (numerator m (tables m).value (s+HalfSourceList.sign b)).value
      (numerator m (tables m).value (-(s+HalfSourceList.sign b))).value).value).natAbs.size ≤ width m := by
    rw [add_view, hpv, hqv, ← Nat.cast_add, Int.natAbs_natCast]
    exact size_bound m _ hsum
  have hdouble := add_price (width m) _ _ hzsize hzsize
  dsimp only [resolved]
  dsimp only [unit] at *
  omega

def unresolved (m : ℕ) (ts : Tables) (s : ℤ) : Result Cell :=
  sumResults [numerator m ts (s+1), numerator m ts (s-1),
    numerator m ts (-s+1), numerator m ts (-s-1)]

theorem unresolved_view (m : ℕ) (s : ℤ) (hs : |s| ≤ 64*m^3) :
    view (unresolved m (tables m).value s).value = HalfSourceIntegerScores.unresolved m s := by
  have h1 := numerator_view m _ (neighbor_window m s hs _ (Or.inl rfl))
  have h2 := numerator_view m _ (neighbor_window m s hs _ (Or.inr (Or.inl rfl)))
  have h3 := numerator_view m _ (neighbor_window m s hs _ (Or.inr (Or.inr (Or.inl rfl))))
  have h4 := numerator_view m _ (neighbor_window m s hs _ (Or.inr (Or.inr (Or.inr rfl))))
  simp only [unresolved, sumResults_view, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, h1, h2, h3, h4, HalfSourceIntegerScores.unresolved, Nat.cast_add]
  ring

theorem unresolved_price (m : ℕ) (s : ℤ) (hs : |s| ≤ 64*m^3) :
    (unresolved m (tables m).value s).bitSteps ≤ 8*unit m+1 := by
  let xs := [numerator m (tables m).value (s+1), numerator m (tables m).value (s-1),
    numerator m (tables m).value (-s+1), numerator m (tables m).value (-s-1)]
  have hmem (x : Result Cell) (hx : x ∈ xs) : ∃ t, -(K m:ℤ) ≤ t ∧ t ≤ K m ∧
      x = numerator m (tables m).value t := by
    simp only [xs, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    all_goals refine ⟨_, ?_, ?_, rfl⟩
    all_goals have := abs_le.mp hs; simp only [K, Nat.cast_add, Nat.cast_mul,
      Nat.cast_ofNat, Nat.cast_pow, Nat.cast_one]; omega
  have h := sumResults_price m (unit m) xs
    (by intro x hx; obtain ⟨t,hl,hr,rfl⟩ := hmem x hx; rw [numerator_view m t ⟨hl,hr⟩]; positivity)
    (by
      rw [← sumResults_view]
      change view (unresolved m (tables m).value s).value ≤ _
      rw [unresolved_view m s hs]
      exact_mod_cast (HalfSourceIntegerScores.unresolved_le m s hs).trans (four_power_le_limit m))
    (by intro x hx; obtain ⟨t,hl,hr,rfl⟩ := hmem x hx; exact numerator_price m t ⟨hl,hr⟩)
  change (sumResults xs).bitSteps ≤ 4*(unit m+unit m)+1 at h
  change (sumResults xs).bitSteps ≤ _
  omega

open WalshEmbedding HalfSourceGreedy

def contribution {n : ℕ} (m : ℕ) (ts : Tables) (s : ℤ) (row : Cube n) (b : Bool) : Result Cell :=
  if row = zeroBits n then resolved m ts s b else unresolved m ts s

theorem contribution_view {n : ℕ} (m : ℕ) (s : ℤ) (hs : |s| ≤ 64*m^3)
    (row : Cube n) (b : Bool) :
    view (contribution m (tables m).value s row b).value =
      (if row = zeroBits n then HalfSourceIntegerScores.resolved m s b
        else HalfSourceIntegerScores.unresolved m s : ℕ) := by
  unfold contribution
  split_ifs
  · exact resolved_view m s hs b
  · exact unresolved_view m s hs

theorem contribution_price {n : ℕ} (m : ℕ) (s : ℤ) (hs : |s| ≤ 64*m^3)
    (row : Cube n) (b : Bool) :
    (contribution m (tables m).value s row b).bitSteps ≤ 8*unit m+1 := by
  unfold contribution
  split_ifs
  · exact (resolved_price m s hs b).trans (by omega)
  · exact unresolved_price m s hs

/-- Each character contribution is evaluated and stored once before summation. -/
def score {N n : ℕ} (m : ℕ) (ts : Tables) (sums : Fin N → ℤ)
    (rows : Fin N → Cube n) (signs : Fin N → Bool) : Result Cell :=
  sumResults (List.ofFn (fun i => contribution m ts (sums i) (rows i) (signs i)))

theorem score_view {N n : ℕ} (m : ℕ) (sums : Fin N → ℤ)
    (hs : ∀ i, |sums i| ≤ 64*m^3) (rows : Fin N → Cube n) (signs : Fin N → Bool) :
    view (score m (tables m).value sums rows signs).value =
      HalfSourceIntegerScores.score m sums rows signs := by
  simp only [score, sumResults_view, List.map_ofFn, List.sum_ofFn,
    HalfSourceIntegerScores.score, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact contribution_view m _ (hs i) _ _

theorem score_price {N n : ℕ} (m : ℕ) (sums : Fin N → ℤ)
    (hs : ∀ i, |sums i| ≤ 64*m^3) (hN : N ≤ 2^m)
    (rows : Fin N → Cube n) (signs : Fin N → Bool) :
    (score m (tables m).value sums rows signs).bitSteps ≤ N*(9*unit m+1)+1 := by
  let xs := List.ofFn (fun i => contribution m (tables m).value (sums i) (rows i) (signs i))
  have hh := sumResults_price m (8*unit m+1) xs
    (by
      intro x hx
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
      rw [contribution_view m _ (hs i)]
      positivity)
    (by
      rw [← sumResults_view]
      change view (score m (tables m).value sums rows signs).value ≤ _
      rw [score_view m sums hs]
      have h := HalfSourceIntegerScores.score_le m sums hs rows signs
      simp only [Fintype.card_fin] at h
      exact_mod_cast h.trans (Nat.mul_le_mul_right _ hN))
    (by
      intro x hx
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
      exact contribution_price m _ (hs i) _ _)
  have hlen : xs.length = N := List.length_ofFn
  rw [hlen] at hh
  change (sumResults xs).bitSteps ≤ _
  convert hh using 1
  ring

def chosen {N n : ℕ} (m : ℕ) (ts : Tables) (sums : Fin N → ℤ)
    (rows : Fin N → Cube (n+1)) (signs : Fin N → Bool) : Result Bool :=
  let left := score m ts sums (tails rows) (updateSigns rows signs false)
  let right := score m ts sums (tails rows) (updateSigns rows signs true)
  let compared := BackendScalarBits.unsignedLessCounted right.value.bits.magnitude left.value.bits.magnitude
  ⟨compared.1,left.bitSteps+right.bitSteps+compared.2⟩

theorem chosen_value {N n : ℕ} (m : ℕ) (sums : Fin N → ℤ)
    (hs : ∀ i, |sums i| ≤ 64*m^3) (rows : Fin N → Cube (n+1)) (signs : Fin N → Bool) :
    (chosen m (tables m).value sums rows signs).value =
      HalfSourceIntegerScores.chosen m sums rows signs := by
  apply Bool.eq_iff_iff.mpr
  simp only [chosen, HalfSourceIntegerScores.chosen, BackendScalarBits.unsignedLess_correct,
    decide_eq_true_eq]
  rw [← IntegerArithmetic.signedValue_natAbs, ← IntegerArithmetic.signedValue_natAbs]
  change (view (score m (tables m).value sums _ _).value).natAbs <
      (view (score m (tables m).value sums _ _).value).natAbs ↔ _
  rw [score_view m sums hs, score_view m sums hs, Int.natAbs_natCast, Int.natAbs_natCast]

theorem chosen_price {N n : ℕ} (m : ℕ) (sums : Fin N → ℤ)
    (hs : ∀ i, |sums i| ≤ 64*m^3) (hN : N ≤ 2^m)
    (rows : Fin N → Cube (n+1)) (signs : Fin N → Bool) :
    (chosen m (tables m).value sums rows signs).bitSteps ≤
      2*(N*(9*unit m+1)+1)+unit m := by
  have hl := score_price m sums hs hN (tails rows) (updateSigns rows signs false)
  have hr := score_price m sums hs hN (tails rows) (updateSigns rows signs true)
  have hsize (b : Bool) :
      (score m (tables m).value sums (tails rows) (updateSigns rows signs b)).value.bits.magnitude.length ≤ width m := by
    rw [canonical, score_view m sums hs, Int.natAbs_natCast]
    exact HalfSourceIntegerScores.score_bits m sums hs (by simpa using hN) _ _
  have hc := BackendScalarBits.unsignedLess_price (width m) _ _ (hsize true) (hsize false)
  have hu : BackendScalarBits.scalarUnit (width m) ≤ unit m := by
    unfold unit BackendScalarBits.backendScalarUnit
    omega
  dsimp only [chosen]
  omega

theorem chosen_refines_rational {N n : ℕ} (m : ℕ) (hm : 0 < m) (sums : Fin N → ℤ)
    (hs : ∀ i, |sums i| ≤ 64*m^3) (rows : Fin N → Cube (n+1)) (signs : Fin N → Bool) :
    (chosen m (tables m).value sums rows signs).value =
      chosenBit (HalfSourceList.rationalBase m)
        (fun i => HalfSourceList.rationalBase m^sums i)
        (fun i => HalfSourceList.rationalBase m^(-sums i)) rows signs := by
  rw [chosen_value m sums hs]
  exact HalfSourceIntegerScores.chosen_eq m hm sums hs rows signs

#print axioms size_bound
#print axioms power_le_limit
#print axioms one_view
#print axioms power_view
#print axioms power_price
#print axioms tables_left
#print axioms tables_right
#print axioms tables_price
#print axioms numerator_view
#print axioms numerator_price
#print axioms cell_size
#print axioms sumResults_view
#print axioms sum_nonneg
#print axioms sumResults_price
#print axioms four_power_le_limit
#print axioms signed_window
#print axioms neighbor_window
#print axioms resolved_view
#print axioms resolved_price
#print axioms unresolved_view
#print axioms unresolved_price
#print axioms contribution_view
#print axioms contribution_price
#print axioms score_view
#print axioms score_price
#print axioms chosen_value
#print axioms chosen_price
#print axioms chosen_refines_rational
end ThinMatrix.HalfSourceBinaryScores

