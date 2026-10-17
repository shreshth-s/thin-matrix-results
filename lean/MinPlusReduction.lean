import Mathlib

/-!
Deterministic integer Exact Triangle to min-plus bit scaling.

The only oracle hypothesis is correctness of the indicated equality tests.
No running-time hypothesis or full min-plus reduction is assumed.  `Minimizes`
states the finite integer minimum by its lower-bound and attained-witness
properties.  The middle index type is nonempty; no restriction is imposed on
the outer dimensions or on ties between witnesses.
-/

namespace ThinMatrix.MinPlusReduction

abbrev Matrix (I K : Type*) := I → K → ℤ

def Minimizes {I K J : Type*} (A : Matrix I K) (B : Matrix K J)
    (C : Matrix I J) : Prop :=
  ∀ i j, (∀ k, C i j ≤ A i k + B k j) ∧ ∃ k, C i j = A i k + B k j

abbrev TriangleOracle (I K J : Type*) :=
  Matrix I K → Matrix K J → Matrix I J → I → J → Bool

def OracleCorrect {I K J : Type*} (O : TriangleOracle I K J) : Prop :=
  ∀ A B T i j, O A B T i j = true ↔ ∃ k, A i k + B k j + T i j = 0

def half {I K : Type*} (A : Matrix I K) : Matrix I K := fun i k => A i k / 2

def refine {I K J : Type*} (O : TriangleOracle I K J)
    (A : Matrix I K) (B : Matrix K J) (coarse : Matrix I J) : Matrix I J :=
  let z0 := O A B (fun i j => -(2 * coarse i j))
  let z1 := O A B (fun i j => -(2 * coarse i j + 1))
  fun i j => if z0 i j then 2 * coarse i j
             else if z1 i j then 2 * coarse i j + 1 else 2 * coarse i j + 2

theorem half_remainder (x : ℤ) : 2 * (x / 2) ≤ x ∧ x ≤ 2 * (x / 2) + 1 := by
  omega

theorem coarse_bracket {I K J : Type*} (A : Matrix I K) (B : Matrix K J)
    (C : Matrix I J) (hc : Minimizes (half A) (half B) C) (i : I) (j : J) :
    (∀ k, 2 * C i j ≤ A i k + B k j) ∧
      ∃ k, A i k + B k j ≤ 2 * C i j + 2 := by
  constructor
  · intro k
    have h := (hc i j).1 k
    have ha := half_remainder (A i k)
    have hb := half_remainder (B k j)
    simp only [half] at h
    omega
  · obtain ⟨k, hk⟩ := (hc i j).2
    have ha := half_remainder (A i k)
    have hb := half_remainder (B k j)
    simp only [half] at hk
    exact ⟨k, by omega⟩

theorem refine_correct {I K J : Type*} (O : TriangleOracle I K J)
    (hO : OracleCorrect O) (A : Matrix I K) (B : Matrix K J)
    (C : Matrix I J) (hc : Minimizes (half A) (half B) C) :
    Minimizes A B (refine O A B C) := by
  intro i j
  obtain ⟨hlower, k, hupper⟩ := coarse_bracket A B C hc i j
  have hzero : O A B (fun i j => -(2 * C i j)) i j = true ↔
      ∃ k, A i k + B k j = 2 * C i j := by
    rw [hO]
    constructor <;> rintro ⟨k, hk⟩ <;> exact ⟨k, by omega⟩
  have hone : O A B (fun i j => -(2 * C i j + 1)) i j = true ↔
      ∃ k, A i k + B k j = 2 * C i j + 1 := by
    rw [hO]
    constructor <;> rintro ⟨k, hk⟩ <;> exact ⟨k, by omega⟩
  unfold refine
  split_ifs with hz ho
  · obtain ⟨w, hw⟩ := hzero.mp hz
    exact ⟨hlower, w, hw.symm⟩
  · have hnzero : ¬ ∃ w, A i w + B w j = 2 * C i j := fun h => hz (hzero.mpr h)
    obtain ⟨w, hw⟩ := hone.mp ho
    constructor
    · intro u
      have hu := hlower u
      have hne : A i u + B u j ≠ 2 * C i j := fun h => hnzero ⟨u, h⟩
      omega
    · exact ⟨w, hw.symm⟩
  · have hnzero : ¬ ∃ w, A i w + B w j = 2 * C i j := fun h => hz (hzero.mpr h)
    have hnone : ¬ ∃ w, A i w + B w j = 2 * C i j + 1 := fun h => ho (hone.mpr h)
    have hmin : ∀ u, 2 * C i j + 2 ≤ A i u + B u j := by
      intro u
      have hu := hlower u
      have hne0 : A i u + B u j ≠ 2 * C i j := fun h => hnzero ⟨u, h⟩
      have hne1 : A i u + B u j ≠ 2 * C i j + 1 := fun h => hnone ⟨u, h⟩
      omega
    exact ⟨hmin, k, by have hk := hmin k; omega⟩

def bitScale {I K J : Type*} (O : TriangleOracle I K J) :
    ℕ → Matrix I K → Matrix K J → Matrix I J
  | 0, _, _ => fun _ _ => 0
  | n + 1, A, B => refine O A B (bitScale O n (half A) (half B))

/-- The lower test has priority even if the upper test also succeeds. -/
theorem refine_zero_priority {I K J : Type*} (O : TriangleOracle I K J)
    (A : Matrix I K) (B : Matrix K J) (C : Matrix I J) (i : I) (j : J)
    (hz : O A B (fun i j => -(2 * C i j)) i j = true) :
    refine O A B C i j = 2 * C i j := by
  simp only [refine, hz, if_true]

def scaleBound : ℕ → ℤ
  | 0 => 1
  | n + 1 => 2 * scaleBound n

theorem scaleBound_pos (n : ℕ) : 0 < scaleBound n := by
  induction n with
  | zero => norm_num [scaleBound]
  | succ n ih => simp only [scaleBound]; omega

theorem scaleBound_eq_pow (n : ℕ) : scaleBound n = 2 ^ n := by
  induction n with
  | zero => simp [scaleBound]
  | succ n ih => simp [scaleBound, ih, pow_succ]; ring

theorem bitScale_correct {I K J : Type*} [Nonempty K]
    (O : TriangleOracle I K J) (hO : OracleCorrect O) (n : ℕ)
    (A : Matrix I K) (B : Matrix K J)
    (hA : ∀ i k, 0 ≤ A i k ∧ A i k < scaleBound n)
    (hB : ∀ k j, 0 ≤ B k j ∧ B k j < scaleBound n) :
    Minimizes A B (bitScale O n A B) := by
  induction n generalizing A B with
  | zero =>
    intro i j
    constructor
    · intro k
      have ha := hA i k
      have hb := hB k j
      simp only [scaleBound] at ha hb
      simp only [bitScale]
      omega
    · obtain ⟨k⟩ := ‹Nonempty K›
      have ha := hA i k
      have hb := hB k j
      simp only [scaleBound] at ha hb
      exact ⟨k, by simp only [bitScale]; omega⟩
  | succ n ih =>
    apply refine_correct O hO A B (bitScale O n (half A) (half B))
    apply ih
    · intro i k
      have ha := hA i k
      simp only [scaleBound] at ha
      simp only [half]
      omega

    · intro k j
      have hb := hB k j
      simp only [scaleBound] at hb
      simp only [half]
      omega

theorem minimizes_unique {I K J : Type*} (A : Matrix I K) (B : Matrix K J)
    (C D : Matrix I J) (hC : Minimizes A B C) (hD : Minimizes A B D) : C = D := by
  funext i j
  obtain ⟨k, hk⟩ := (hC i j).2
  obtain ⟨l, hl⟩ := (hD i j).2
  have h₁ := (hC i j).1 l
  have h₂ := (hD i j).1 k
  omega

noncomputable def minPlus {I K J : Type*} [Fintype K] [Nonempty K]
    (A : Matrix I K) (B : Matrix K J) : Matrix I J :=
  fun i j => Finset.univ.inf' Finset.univ_nonempty (fun k => A i k + B k j)

theorem minPlus_minimizes {I K J : Type*} [Fintype K] [Nonempty K]
    (A : Matrix I K) (B : Matrix K J) : Minimizes A B (minPlus A B) := by
  classical
  intro i j
  constructor
  · intro k
    exact Finset.inf'_le _ (Finset.mem_univ k)
  · obtain ⟨k, _, hk⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty
      (fun k => A i k + B k j)
    exact ⟨k, hk⟩

theorem bitScale_eq_minPlus {I K J : Type*} [Fintype K] [Nonempty K]
    (O : TriangleOracle I K J) (hO : OracleCorrect O) (n : ℕ)
    (A : Matrix I K) (B : Matrix K J)
    (hA : ∀ i k, 0 ≤ A i k ∧ A i k < scaleBound n)
    (hB : ∀ k j, 0 ≤ B k j ∧ B k j < scaleBound n) :
    bitScale O n A B = minPlus A B :=
  minimizes_unique A B _ _ (bitScale_correct O hO n A B hA hB)
    (minPlus_minimizes A B)

def shift {I K : Type*} (A : Matrix I K) (u : ℤ) : Matrix I K :=
  fun i k => A i k + u

theorem unshift_minimizes {I K J : Type*} (A : Matrix I K) (B : Matrix K J)
    (u v : ℤ) (C : Matrix I J) (hC : Minimizes (shift A u) (shift B v) C) :
    Minimizes A B (fun i j => C i j - u - v) := by
  intro i j
  constructor
  · intro k
    have h := (hC i j).1 k
    simp only [shift] at h
    change C i j - u - v ≤ A i k + B k j
    omega
  · obtain ⟨k, hk⟩ := (hC i j).2
    simp only [shift] at hk
    refine ⟨k, ?_⟩
    change C i j - u - v = A i k + B k j
    omega

def signedBitScale {I K J : Type*} (O : TriangleOracle I K J) (n : ℕ)
    (A : Matrix I K) (B : Matrix K J) (u v : ℤ) : Matrix I J :=
  fun i j => bitScale O n (shift A u) (shift B v) i j - u - v

theorem signedBitScale_correct {I K J : Type*} [Nonempty K]
    (O : TriangleOracle I K J) (hO : OracleCorrect O) (n : ℕ)
    (A : Matrix I K) (B : Matrix K J) (u v : ℤ)
    (hA : ∀ i k, 0 ≤ A i k + u ∧ A i k + u < scaleBound n)
    (hB : ∀ k j, 0 ≤ B k j + v ∧ B k j + v < scaleBound n) :
    Minimizes A B (signedBitScale O n A B u v) := by
  exact unshift_minimizes A B u v _ (bitScale_correct O hO n _ _ hA hB)

def scheduledCalls : ℕ → ℕ
  | 0 => 0
  | n + 1 => scheduledCalls n + 2

/-- The scheduled adaptive equality queries, including both tests at every level. -/
def queryTrace {I K J : Type*} (O : TriangleOracle I K J) :
    ℕ → Matrix I K → Matrix K J →
      List (Matrix I K × Matrix K J × Matrix I J)
  | 0, _, _ => []
  | n + 1, A, B =>
    let C := bitScale O n (half A) (half B)
    queryTrace O n (half A) (half B) ++
      [(A, B, fun i j => -(2 * C i j)),
       (A, B, fun i j => -(2 * C i j + 1))]

theorem queryTrace_length {I K J : Type*} (O : TriangleOracle I K J)
    (n : ℕ) (A : Matrix I K) (B : Matrix K J) :
    (queryTrace O n A B).length = 2 * n := by
  induction n generalizing A B with
  | zero => rfl
  | succ n ih => simp only [queryTrace, List.length_append, List.length_cons,
      List.length_nil, ih]; omega

theorem scheduledCalls_eq (n : ℕ) : scheduledCalls n = 2 * n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [scheduledCalls, ih]; omega

theorem nat_lt_binary_bound (U : ℕ) : U < 2 ^ (U.log2 + 1) := by
  by_cases h : U = 0
  · simp [h]
  · exact (Nat.log2_lt h).mp (by omega)

def signedLevels (W : ℕ) : ℕ := (2 * W).log2 + 1

theorem signed_levels_bound (W : ℕ) : 2 * (W : ℤ) < scaleBound (signedLevels W) := by
  rw [scaleBound_eq_pow]
  have h := nat_lt_binary_bound (2 * W)
  exact_mod_cast h

theorem bounded_signed_correct {I K J : Type*} [Nonempty K]
    (O : TriangleOracle I K J) (hO : OracleCorrect O)
    (A : Matrix I K) (B : Matrix K J) (W : ℕ)
    (hA : ∀ i k, -(W : ℤ) ≤ A i k ∧ A i k ≤ W)
    (hB : ∀ k j, -(W : ℤ) ≤ B k j ∧ B k j ≤ W) :
    Minimizes A B (signedBitScale O (signedLevels W) A B W W) := by
  apply signedBitScale_correct O hO
  · intro i k
    have h := hA i k
    have hb := signed_levels_bound W
    omega

  · intro k j
    have h := hB k j
    have hb := signed_levels_bound W
    omega

theorem bounded_signed_eq_minPlus {I K J : Type*} [Fintype K] [Nonempty K]
    (O : TriangleOracle I K J) (hO : OracleCorrect O)
    (A : Matrix I K) (B : Matrix K J) (W : ℕ)
    (hA : ∀ i k, -(W : ℤ) ≤ A i k ∧ A i k ≤ W)
    (hB : ∀ k j, -(W : ℤ) ≤ B k j ∧ B k j ≤ W) :
    signedBitScale O (signedLevels W) A B W W = minPlus A B :=
  minimizes_unique A B _ _ (bounded_signed_correct O hO A B W hA hB)
    (minPlus_minimizes A B)
theorem signed_call_count (W : ℕ) :
    scheduledCalls (signedLevels W) = 2 * ((2 * W).log2 + 1) := by
  exact scheduledCalls_eq _

theorem scaleBound_signedLevels_le (W : ℕ) :
    scaleBound (signedLevels W) ≤ 4 * (W : ℤ) + 2 := by
  by_cases hzero : W = 0
  · simp [hzero, signedLevels, scaleBound]
  · have hnz : 2 * W ≠ 0 := by omega
    have hpow : 2 ^ (2 * W).log2 ≤ 2 * W := (Nat.le_log2 hnz).mp (by omega)
    have hpowInt : (2 : ℤ) ^ (2 * W).log2 ≤ 2 * (W : ℤ) := by
      exact_mod_cast hpow
    rw [signedLevels, scaleBound_eq_pow, pow_succ]
    omega

/-- Oracle target weights are polynomially bounded together with their inputs. -/
theorem refine_target_bound {I K J : Type*}
    (A : Matrix I K) (B : Matrix K J) (C : Matrix I J) (U : ℤ)
    (hA : ∀ i k, 0 ≤ A i k ∧ A i k < U)
    (hB : ∀ k j, 0 ≤ B k j ∧ B k j < U)
    (hC : Minimizes (half A) (half B) C) (i : I) (j : J)
    (r : ℤ) (hr : 0 ≤ r ∧ r ≤ 1) :
    -(2 * U + 1) ≤ -(2 * C i j + r) ∧ -(2 * C i j + r) ≤ 0 := by
  obtain ⟨k, hk⟩ := (hC i j).2
  have ha := hA i k
  have hb := hB k j
  simp only [half] at hk
  omega

theorem polynomial_binary_bound (N c W : ℕ) (hW : W ≤ N ^ c) :
    2 * W < 2 ^ (c * (N.log2 + 1) + 2) := by
  have hN : N ≤ 2 ^ (N.log2 + 1) := Nat.le_of_lt (nat_lt_binary_bound N)
  have hp : W ≤ 2 ^ ((N.log2 + 1) * c) := by
    calc
      W ≤ N ^ c := hW
      _ ≤ (2 ^ (N.log2 + 1)) ^ c := Nat.pow_le_pow_left hN c
      _ = 2 ^ ((N.log2 + 1) * c) := by rw [pow_mul]
  have hpos : 0 < 2 ^ ((N.log2 + 1) * c) := by positivity
  rw [Nat.mul_comm c (N.log2 + 1), pow_add]
  norm_num
  omega

theorem polynomial_call_bound (N c W : ℕ) (hW : W ≤ N ^ c) :
    scheduledCalls (signedLevels W) ≤ 2 * (c * (N.log2 + 1) + 2) := by
  have hp := polynomial_binary_bound N c W hW
  have hlevels : signedLevels W ≤ c * (N.log2 + 1) + 2 := by
    unfold signedLevels
    by_cases hzero : 2 * W = 0
    · simp [hzero]
    · have hlog := (Nat.log2_lt hzero).mpr hp
      omega
  rw [scheduledCalls_eq]
  omega

/-- Includes the empty square matrix, whose correctness assertion is vacuous. -/
theorem bounded_signed_square_correct (O : TriangleOracle (Fin N) (Fin N) (Fin N))
    (hO : OracleCorrect O) (A B : Matrix (Fin N) (Fin N)) (W : ℕ)
    (hA : ∀ i k, -(W : ℤ) ≤ A i k ∧ A i k ≤ W)
    (hB : ∀ k j, -(W : ℤ) ≤ B k j ∧ B k j ≤ W) :
    Minimizes A B (signedBitScale O (signedLevels W) A B W W) := by
  cases N with
  | zero => intro i; exact Fin.elim0 i
  | succ n => exact bounded_signed_correct O hO A B W hA hB
def QueryMagnitudeBound {I K J : Type*}
    (q : Matrix I K × Matrix K J × Matrix I J) (M : ℤ) : Prop :=
  (∀ i k, 0 ≤ q.1 i k ∧ q.1 i k < M) ∧
  (∀ k j, 0 ≤ q.2.1 k j ∧ q.2.1 k j < M) ∧
  (∀ i j, -(2 * M + 1) ≤ q.2.2 i j ∧ q.2.2 i j ≤ 0)

theorem queryTrace_bounded {I K J : Type*} [Nonempty K]
    (O : TriangleOracle I K J) (hO : OracleCorrect O) (n : ℕ)
    (A : Matrix I K) (B : Matrix K J)
    (hA : ∀ i k, 0 ≤ A i k ∧ A i k < scaleBound n)
    (hB : ∀ k j, 0 ≤ B k j ∧ B k j < scaleBound n)
    (M : ℤ) (hM : scaleBound n ≤ M) :
    ∀ q ∈ queryTrace O n A B, QueryMagnitudeBound q M := by
  induction n generalizing A B M with
  | zero => simp only [queryTrace, List.not_mem_nil, false_implies, implies_true]
  | succ n ih =>
    have ha : ∀ i k, 0 ≤ half A i k ∧ half A i k < scaleBound n := by
      intro i k
      have h := hA i k
      simp only [scaleBound] at h
      simp only [half]
      omega
    have hb : ∀ k j, 0 ≤ half B k j ∧ half B k j < scaleBound n := by
      intro k j
      have h := hB k j
      simp only [scaleBound] at h
      simp only [half]
      omega
    have hsmall : scaleBound n ≤ M := by
      have hp := scaleBound_pos n
      simp only [scaleBound] at hM
      omega
    have hc := bitScale_correct O hO n (half A) (half B) ha hb
    have hcurrent (r : ℤ) (hr : 0 ≤ r ∧ r ≤ 1) :
        QueryMagnitudeBound
          (A, B, fun i j => -(2 * bitScale O n (half A) (half B) i j + r)) M := by
      constructor
      · intro i k
        exact ⟨(hA i k).1, lt_of_lt_of_le (hA i k).2 hM⟩
      constructor
      · intro k j
        exact ⟨(hB k j).1, lt_of_lt_of_le (hB k j).2 hM⟩
      · intro i j
        have h := refine_target_bound A B _ (scaleBound (n + 1)) hA hB hc i j r hr
        dsimp only
        omega
    intro q hq
    simp only [queryTrace, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with hold | rfl | rfl
    · exact ih (half A) (half B) ha hb M hsmall q hold
    · simpa only [add_zero] using hcurrent 0 (by omega)
    · exact hcurrent 1 (by omega)

/-- Every adaptive oracle weight stays polynomial when the original weight bound does. -/
theorem bounded_signed_query_trace {I K J : Type*} [Nonempty K]
    (O : TriangleOracle I K J) (hO : OracleCorrect O)
    (A : Matrix I K) (B : Matrix K J) (W : ℕ)
    (hA : ∀ i k, -(W : ℤ) ≤ A i k ∧ A i k ≤ W)
    (hB : ∀ k j, -(W : ℤ) ≤ B k j ∧ B k j ≤ W) :
    ∀ q ∈ queryTrace O (signedLevels W) (shift A W) (shift B W),
      QueryMagnitudeBound q (4 * (W : ℤ) + 2) := by
  apply queryTrace_bounded O hO
  · intro i k
    have h := hA i k
    have hb := signed_levels_bound W
    simp only [shift]
    omega
  · intro k j
    have h := hB k j
    have hb := signed_levels_bound W
    simp only [shift]
    omega
  · exact scaleBound_signedLevels_le W

def encode (S : ℤ) : Option ℤ → ℤ
  | none => S
  | some a => a

def encodeMatrix {I K : Type*} (A : I → K → Option ℤ) (S : ℤ) : Matrix I K :=
  fun i k => encode S (A i k)

def FiniteBound {I K : Type*} (A : I → K → Option ℤ) (W : ℤ) : Prop :=
  ∀ i k a, A i k = some a → -W ≤ a ∧ a ≤ W

theorem sentinel_pair (u v : Option ℤ) (W S : ℤ) (hW : 0 ≤ W) (hS : 3 * W < S)
    (hu : ∀ a, u = some a → -W ≤ a ∧ a ≤ W)
    (hv : ∀ b, v = some b → -W ≤ b ∧ b ≤ W) :
    encode S u + encode S v ≤ 2 * W ↔ ∃ a b, u = some a ∧ v = some b := by
  cases u with
  | none =>
    cases v with
    | none => simp only [encode, reduceCtorEq, false_and, exists_false, iff_false]; omega
    | some b =>
      have hb := hv b rfl
      simp only [encode, reduceCtorEq, false_and, exists_false, iff_false]
      omega
  | some a =>
    have ha := hu a rfl
    cases v with
    | none =>
      simp only [encode, reduceCtorEq, and_false, exists_false, iff_false]
      omega
    | some b =>
      have hb := hv b rfl
      constructor
      · intro _; exact ⟨a, b, rfl, rfl⟩
      · intro _; simp only [encode]; omega

theorem sentinel_minimum_finite {I K J : Type*}
    (A : I → K → Option ℤ) (B : K → J → Option ℤ) (W S : ℤ)
    (hW : 0 ≤ W) (hS : 3 * W < S) (hA : FiniteBound A W) (hB : FiniteBound B W)
    (C : Matrix I J) (hC : Minimizes (encodeMatrix A S) (encodeMatrix B S) C)
    (i : I) (j : J) :
    C i j ≤ 2 * W ↔ ∃ k a b, A i k = some a ∧ B k j = some b := by
  constructor
  · intro hc
    obtain ⟨k, hk⟩ := (hC i j).2
    have hp : encode S (A i k) + encode S (B k j) ≤ 2 * W := by
      simpa only [encodeMatrix, hk] using hc
    obtain ⟨a, b, ha, hb⟩ := (sentinel_pair (A i k) (B k j) W S hW hS
      (hA i k) (hB k j)).mp hp
    exact ⟨k, a, b, ha, hb⟩
  · rintro ⟨k, a, b, ha, hb⟩
    have hc := (hC i j).1 k
    have hfinite := (sentinel_pair (A i k) (B k j) W S hW hS
      (hA i k) (hB k j)).mpr ⟨a, b, ha, hb⟩
    simp only [encodeMatrix] at hc
    omega

def restore {I J : Type*} (C : Matrix I J) (W : ℤ) : I → J → Option ℤ :=
  fun i j => if 2 * W < C i j then none else some (C i j)

def OptionalMinimizes {I K J : Type*} (A : I → K → Option ℤ)
    (B : K → J → Option ℤ) (C : I → J → Option ℤ) : Prop :=
  ∀ i j,
    (C i j = none ↔ ¬ ∃ k a b, A i k = some a ∧ B k j = some b) ∧
    (∀ c, C i j = some c →
      (∀ k a b, A i k = some a → B k j = some b → c ≤ a + b) ∧
      ∃ k a b, A i k = some a ∧ B k j = some b ∧ c = a + b)

theorem restore_correct {I K J : Type*}
    (A : I → K → Option ℤ) (B : K → J → Option ℤ) (W S : ℤ)
    (hW : 0 ≤ W) (hS : 3 * W < S) (hA : FiniteBound A W) (hB : FiniteBound B W)
    (C : Matrix I J) (hC : Minimizes (encodeMatrix A S) (encodeMatrix B S) C) :
    OptionalMinimizes A B (restore C W) := by
  intro i j
  have hf := sentinel_minimum_finite A B W S hW hS hA hB C hC i j
  constructor
  · by_cases hgt : 2 * W < C i j
    · have hn : ¬ ∃ k a b, A i k = some a ∧ B k j = some b := by
        intro he
        have hc := hf.mpr he
        omega
      simp only [restore, if_pos hgt, hn, not_false_eq_true]
    · have he : ∃ k a b, A i k = some a ∧ B k j = some b := hf.mp (by omega)
      simp only [restore, if_neg hgt, reduceCtorEq, he, not_true_eq_false]
  · intro c hc
    have hvalue : C i j = c := by
      by_cases hgt : 2 * W < C i j
      · simp only [restore, if_pos hgt, reduceCtorEq] at hc
      · exact Option.some.inj (by simpa only [restore, if_neg hgt] using hc)
    have hthreshold : C i j ≤ 2 * W := by
      by_cases hgt : 2 * W < C i j
      · simp only [restore, if_pos hgt, reduceCtorEq] at hc
      · omega
    constructor
    · intro k a b ha hb
      have hk := (hC i j).1 k
      simpa only [encodeMatrix, ha, hb, encode, hvalue] using hk

    · obtain ⟨k, hk⟩ := (hC i j).2
      have hp : encode S (A i k) + encode S (B k j) ≤ 2 * W := by
        simpa only [encodeMatrix, hk] using hthreshold
      obtain ⟨a, b, ha, hb⟩ := (sentinel_pair (A i k) (B k j) W S hW hS
        (hA i k) (hB k j)).mp hp
      refine ⟨k, a, b, ha, hb, ?_⟩
      simpa only [encodeMatrix, ha, hb, encode, hvalue] using hk

def optionalBitScale {I K J : Type*} (O : TriangleOracle I K J)
    (A : I → K → Option ℤ) (B : K → J → Option ℤ)
    (W S : ℤ) (M : ℕ) : I → J → Option ℤ :=
  restore (signedBitScale O (signedLevels M) (encodeMatrix A S)
    (encodeMatrix B S) M M) W

theorem optionalBitScale_correct {I K J : Type*} [Nonempty K]
    (O : TriangleOracle I K J) (hO : OracleCorrect O)
    (A : I → K → Option ℤ) (B : K → J → Option ℤ)
    (W S : ℤ) (M : ℕ) (hW : 0 ≤ W) (hS : 3 * W < S)
    (hWM : W ≤ (M : ℤ)) (hSM : -(M : ℤ) ≤ S ∧ S ≤ M)
    (hA : FiniteBound A W) (hB : FiniteBound B W) :
    OptionalMinimizes A B (optionalBitScale O A B W S M) := by
  apply restore_correct A B W S hW hS hA hB
  apply bounded_signed_correct O hO
  · intro i k
    cases ha : A i k with
    | none => simpa only [encodeMatrix, ha, encode] using hSM
    | some a =>
      have h := hA i k a ha
      simp only [encodeMatrix, ha, encode]
      exact ⟨le_trans (neg_le_neg hWM) h.1, le_trans h.2 hWM⟩
  · intro k j
    cases hb : B k j with
    | none => simpa only [encodeMatrix, hb, encode] using hSM
    | some b =>
      have h := hB k j b hb
      simp only [encodeMatrix, hb, encode]
      exact ⟨le_trans (neg_le_neg hWM) h.1, le_trans h.2 hWM⟩
/-- Lower bound for the sum of a walk whose individual edges are bounded below. -/
theorem list_sum_lower (xs : List ℤ) (W : ℤ)
    (h : ∀ x ∈ xs, -W ≤ x) : -(xs.length : ℤ) * W ≤ xs.sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx : -W ≤ x := h x (by simp)
    have ht : ∀ y ∈ xs, -W ≤ y := by intro y hy; exact h y (by simp [hy])
    have hs := ih ht
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one, List.sum_cons]
    nlinarith

theorem list_sum_upper (xs : List ℤ) (W : ℤ)
    (h : ∀ x ∈ xs, x ≤ W) : xs.sum ≤ (xs.length : ℤ) * W := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx : x ≤ W := h x (by simp)
    have ht : ∀ y ∈ xs, y ≤ W := by intro y hy; exact h y (by simp [hy])
    have hs := ih ht
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one, List.sum_cons]
    nlinarith

theorem finite_walk_bound (xs : List ℤ) (n : ℕ) (W : ℤ) (hW : 0 ≤ W)
    (hlength : xs.length ≤ 2 * n)
    (hedges : ∀ x ∈ xs, -W ≤ x ∧ x ≤ W) :
    -(2 * (n : ℤ) * W) ≤ xs.sum ∧ xs.sum ≤ 2 * (n : ℤ) * W := by
  have hl := list_sum_lower xs W (fun x hx => (hedges x hx).1)
  have hu := list_sum_upper xs W (fun x hx => (hedges x hx).2)
  have hlen : (xs.length : ℤ) ≤ 2 * (n : ℤ) := by exact_mod_cast hlength
  constructor <;> nlinarith

def canonicalSentinel (n : ℕ) (W : ℤ) : ℤ := 4 * (n : ℤ) * W + 2

theorem canonicalSentinel_threshold (n : ℕ) (W : ℤ) :
    4 * (n : ℤ) * W + 1 < canonicalSentinel n W := by
  unfold canonicalSentinel
  omega

theorem canonicalSentinel_pair_threshold (n : ℕ) (W : ℤ)
    (hn : 0 < n) (hW : 0 ≤ W) : 3 * W < canonicalSentinel n W := by
  have hnInt : 1 ≤ (n : ℤ) := by exact_mod_cast hn
  unfold canonicalSentinel
  nlinarith

/-- The canonical APSP sentinel threshold for walks of at most `2*n` edges. -/
theorem sentinel_walk_separated (xs : List ℤ) (n : ℕ) (W S : ℤ)
    (hW : 0 ≤ W) (hn : 0 < n) (hS : 4 * (n : ℤ) * W + 1 < S)
    (hlength : xs.length ≤ 2 * n) (hmem : S ∈ xs)
    (hedges : ∀ x ∈ xs, x = S ∨ (-W ≤ x ∧ x ≤ W)) :
    2 * (n : ℤ) * W < xs.sum := by
  have hnInt : 1 ≤ (n : ℤ) := by exact_mod_cast hn
  have hSlo : -W ≤ S := by nlinarith
  have hremaining : ∀ x ∈ xs.erase S, -W ≤ x := by
    intro x hx
    rcases hedges x (List.mem_of_mem_erase hx) with h | h
    · simpa only [h] using hSlo
    · exact h.1
  have hsum := list_sum_lower (xs.erase S) W hremaining
  have herase := List.length_erase_add_one hmem
  have hsumEq := List.sum_erase hmem
  have hlenInt : (xs.length : ℤ) ≤ 2 * (n : ℤ) := by exact_mod_cast hlength
  have heraseInt : ((xs.erase S).length : ℤ) + 1 = (xs.length : ℤ) := by
    exact_mod_cast herase
  nlinarith

end ThinMatrix.MinPlusReduction

/- Public dependency reports consumed by the standalone Lean verifier. -/
#print axioms ThinMatrix.MinPlusReduction.bitScale_correct
#print axioms ThinMatrix.MinPlusReduction.signedBitScale_correct
#print axioms ThinMatrix.MinPlusReduction.bounded_signed_correct
#print axioms ThinMatrix.MinPlusReduction.optionalBitScale_correct
#print axioms ThinMatrix.MinPlusReduction.queryTrace_length
#print axioms ThinMatrix.MinPlusReduction.signed_call_count
#print axioms ThinMatrix.MinPlusReduction.polynomial_call_bound
#print axioms ThinMatrix.MinPlusReduction.bounded_signed_query_trace
#print axioms ThinMatrix.MinPlusReduction.canonicalSentinel_threshold
#print axioms ThinMatrix.MinPlusReduction.sentinel_walk_separated
