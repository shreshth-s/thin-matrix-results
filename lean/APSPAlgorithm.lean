import APSPReduction
import MinPlusReduction

/-!
# Actual bit-scaled APSP implementation from an Exact Triangle oracle

The algorithm calls `MinPlusReduction.optionalBitScale` at each squaring stage.
Finite/infinite entries are encoded with a proved separating sentinel and
restored after each product. Correctness assumes only the equality-oracle
contract, an input magnitude bound, and no negative closed walks.

Cost equations count scheduled matrix-level oracle calls and dense entry
materializations with intermediate matrices shared. They do not model the raw
evaluation cost of Lean's function representation or certify extracted runtime.
-/
namespace ThinMatrix.APSPAlgorithm
variable {V : Type*}

/-- Computable initialization, including empty walks and optional self edges. -/
def initial [DecidableEq V] (w : APSPReduction.Graph V) (a b : V) : Option ℤ :=
  if a = b then
    match w a b with
    | none => some 0
    | some z => some (min 0 z)
  else w a b

theorem initial_eq [DecidableEq V] (w : APSPReduction.Graph V) : initial w = APSPReduction.initial w := by
  funext a b
  unfold initial APSPReduction.initial
  by_cases hab : a = b
  · rw [if_pos hab, if_pos hab]
    cases w a b <;> rfl
  · rw [if_neg hab, if_neg hab]
    cases w a b <;> rfl

/-- Bridge from optional-integer minimum semantics to the infinity-aware product. -/
theorem optional_eq_minPlus [Fintype V] {A B C : APSPReduction.Matrix V}
    (h : MinPlusReduction.OptionalMinimizes A B C) : C = APSPReduction.minPlus A B := by
  classical
  funext a b
  cases hc : C a b with
  | none =>
      have hn := (h a b).1.mp hc
      change (⊤ : APSPReduction.Distance) = APSPReduction.minPlus A B a b
      apply le_antisymm
      · apply Finset.le_inf
        intro k hk
        cases ha : A a k <;> cases hb : B k b <;>
          simp_all [WithTop.none_eq_top, WithTop.some_eq_coe]
        exact hn k _ ha _ hb
      · exact le_top
  | some z =>
      obtain ⟨hl, k, x, y, hx, hy, hz⟩ := (h a b).2 z hc
      change (z : APSPReduction.Distance) = APSPReduction.minPlus A B a b
      apply le_antisymm
      · apply Finset.le_inf
        intro middle hm
        cases ha : A a middle with
        | none => simp [WithTop.none_eq_top]
        | some x' =>
            cases hb : B middle b with
            | none =>
                change (z : APSPReduction.Distance) ≤ (x' : APSPReduction.Distance) + ⊤
                rw [WithTop.add_top]
                exact le_top
            | some y' =>
                simpa [ha, hb, WithTop.some_eq_coe] using (show (z : APSPReduction.Distance) ≤ ((x'+y' : ℤ) : APSPReduction.Distance) by
                  exact_mod_cast hl middle x' y' ha hb)
      · calc
          APSPReduction.minPlus A B a b ≤ A a k + B k b := Finset.inf_le (by simp)
          _ = (z : APSPReduction.Distance) := by simp [hx, hy, hz, WithTop.some_eq_coe]

/-- Uniform finite-entry bound throughout all logarithmic squaring stages. -/
def globalBound (n W : ℕ) : ℕ := 2*n*W

def sentinel (B : ℕ) : ℕ := 4*B+1

def step (O : MinPlusReduction.TriangleOracle V V V) (B : ℕ) (A : APSPReduction.Matrix V) : APSPReduction.Matrix V :=
  MinPlusReduction.optionalBitScale O A A B (sentinel B) (sentinel B)

theorem step_eq_minPlus [Fintype V] [Nonempty V]
    (O : MinPlusReduction.TriangleOracle V V V) (hO : MinPlusReduction.OracleCorrect O)
    (B : ℕ) (A : APSPReduction.Matrix V) (hA : MinPlusReduction.FiniteBound A B) :
    step O B A = APSPReduction.minPlus A A := by
  apply optional_eq_minPlus
  apply MinPlusReduction.optionalBitScale_correct O hO A A B (sentinel B) (sentinel B)
  · positivity
  · simp only [sentinel, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    omega
  · simp only [sentinel, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    omega
  · simp only [sentinel, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    constructor <;> omega
  · exact hA
  · exact hA

/-- Actual implementation: the previous optional matrix is bound once. -/
def fastSquared [DecidableEq V] (O : MinPlusReduction.TriangleOracle V V V)
    (w : APSPReduction.Graph V) (B : ℕ) : ℕ → APSPReduction.Matrix V
  | 0 => initial w
  | k+1 => let previous := fastSquared O w B k; step O B previous

theorem semantic_finite_bound [Fintype V] {w : APSPReduction.Graph V} {W : ℕ}
    (hw : APSPReduction.EdgeBound w W) (k : ℕ) (hk : k ≤ APSPReduction.rounds (Fintype.card V)) :
    MinPlusReduction.FiniteBound (APSPReduction.squared w k) (globalBound (Fintype.card V) W) := by
  intro a b z hz
  let : Nonempty V := ⟨a⟩
  have hn : Fintype.card V ≠ 0 := Fintype.card_ne_zero
  have hpow : 2^k ≤ 2^APSPReduction.rounds (Fintype.card V) := Nat.pow_le_pow_right (by decide) hk
  have hb := APSPReduction.squared_entry_bound hw k hz
  have hup := APSPReduction.budget_upper hn
  have hzabs : z.natAbs ≤ globalBound (Fintype.card V) W :=
    hb.trans (Nat.mul_le_mul_right W (hpow.trans hup))
  have habs : (z.natAbs : ℤ) ≤ (globalBound (Fintype.card V) W : ℤ) := by exact_mod_cast hzabs
  have hhi := Int.le_natAbs (a := z)
  have hlo : -z ≤ (z.natAbs : ℤ) := by simpa using (Int.le_natAbs (a := -z))
  constructor <;> omega

theorem fastSquared_eq [Fintype V] [DecidableEq V] [Nonempty V]
    (O : MinPlusReduction.TriangleOracle V V V) (hO : MinPlusReduction.OracleCorrect O)
    (w : APSPReduction.Graph V) (W : ℕ) (hw : APSPReduction.EdgeBound w W)
    (k : ℕ) (hk : k ≤ APSPReduction.rounds (Fintype.card V)) :
    fastSquared O w (globalBound (Fintype.card V) W) k = APSPReduction.squared w k := by
  induction k with
  | zero => exact initial_eq w
  | succ k ih =>
      have hk' : k ≤ APSPReduction.rounds (Fintype.card V) := by omega
      simp only [fastSquared, APSPReduction.squared]
      rw [ih hk']
      exact step_eq_minPlus O hO _ _ (semantic_finite_bound hw k hk')

def fastAPSP [Fintype V] [DecidableEq V] (O : MinPlusReduction.TriangleOracle V V V)
    (w : APSPReduction.Graph V) (W : ℕ) : APSPReduction.Matrix V :=
  fastSquared O w (globalBound (Fintype.card V) W) (APSPReduction.rounds (Fintype.card V))

/-- No correctness hypothesis about min-plus is assumed: its bit-scaling
implementation is substituted via the equality-oracle correctness theorem. -/
theorem fastAPSP_correct [Fintype V] [DecidableEq V]
    (O : MinPlusReduction.TriangleOracle V V V) (hO : MinPlusReduction.OracleCorrect O)
    (w : APSPReduction.Graph V) (W : ℕ) (hw : APSPReduction.EdgeBound w W)
    (hno : APSPReduction.NoNegativeCycles w) : APSPReduction.IsAPSP w (fastAPSP O w W) := by
  cases isEmpty_or_nonempty V with
  | inl h =>
      let : IsEmpty V := h
      intro a
      exact isEmptyElim a
  | inr h =>
      let : Nonempty V := h
      unfold fastAPSP
      rw [fastSquared_eq O hO w W hw _ le_rfl]
      exact APSPReduction.apsp_correct w hno

abbrev IntMatrix (V : Type*) := MinPlusReduction.Matrix V V
abbrev Query (V : Type*) := IntMatrix V × IntMatrix V × IntMatrix V

/-- The actual adaptive bit-scaling query trace at one sentinel-restored stage. -/
def stepTrace (O : MinPlusReduction.TriangleOracle V V V) (B : ℕ)
    (A : APSPReduction.Matrix V) : List (Query V) :=
  let M := sentinel B
  let encoded := MinPlusReduction.encodeMatrix A M
  MinPlusReduction.queryTrace O (MinPlusReduction.signedLevels M)
    (MinPlusReduction.shift encoded M) (MinPlusReduction.shift encoded M)

theorem stepTrace_length (O : MinPlusReduction.TriangleOracle V V V) (B : ℕ)
    (A : APSPReduction.Matrix V) :
    (stepTrace O B A).length = 2*MinPlusReduction.signedLevels (sentinel B) := by
  exact MinPlusReduction.queryTrace_length _ _ _ _

def fastTrace [DecidableEq V] (O : MinPlusReduction.TriangleOracle V V V)
    (w : APSPReduction.Graph V) (B : ℕ) : ℕ → List (Query V)
  | 0 => []
  | k+1 => fastTrace O w B k ++ stepTrace O B (fastSquared O w B k)

theorem fastTrace_length [DecidableEq V] (O : MinPlusReduction.TriangleOracle V V V)
    (w : APSPReduction.Graph V) (B k : ℕ) :
    (fastTrace O w B k).length = k*(2*MinPlusReduction.signedLevels (sentinel B)) := by
  induction k with
  | zero => simp [fastTrace]
  | succ k ih => simp only [fastTrace, List.length_append, ih, stepTrace_length]; ring

theorem encoded_bound (B : ℕ) (A : APSPReduction.Matrix V)
    (hA : MinPlusReduction.FiniteBound A B) :
    ∀ i j, -(sentinel B : ℤ) ≤ MinPlusReduction.encodeMatrix A (sentinel B) i j ∧
      MinPlusReduction.encodeMatrix A (sentinel B) i j ≤ sentinel B := by
  intro i j
  cases ha : A i j with
  | none =>
      simp only [MinPlusReduction.encodeMatrix, ha, MinPlusReduction.encode]
      constructor <;> omega
  | some z =>
      have hz := hA i j z ha
      simp only [MinPlusReduction.encodeMatrix, ha, MinPlusReduction.encode,
        sentinel, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
      constructor <;> omega

theorem stepTrace_bounded [Nonempty V]
    (O : MinPlusReduction.TriangleOracle V V V) (hO : MinPlusReduction.OracleCorrect O)
    (B : ℕ) (A : APSPReduction.Matrix V) (hA : MinPlusReduction.FiniteBound A B) :
    ∀ q ∈ stepTrace O B A,
      MinPlusReduction.QueryMagnitudeBound q (4*(sentinel B : ℤ)+2) := by
  exact MinPlusReduction.bounded_signed_query_trace O hO _ _ _
    (encoded_bound B A hA) (encoded_bound B A hA)

/-- All adaptive equality queries made by the implementation have a uniform
polynomial magnitude bound. The assertion concerns the actual query trace. -/
theorem fastTrace_bounded [Fintype V] [DecidableEq V] [Nonempty V]
    (O : MinPlusReduction.TriangleOracle V V V) (hO : MinPlusReduction.OracleCorrect O)
    (w : APSPReduction.Graph V) (W : ℕ) (hw : APSPReduction.EdgeBound w W)
    (k : ℕ) (hk : k ≤ APSPReduction.rounds (Fintype.card V)) :
    ∀ q ∈ fastTrace O w (globalBound (Fintype.card V) W) k,
      MinPlusReduction.QueryMagnitudeBound q
        (4*(sentinel (globalBound (Fintype.card V) W) : ℤ)+2) := by
  induction k with
  | zero => simp [fastTrace]
  | succ k ih =>
      have hk' : k ≤ APSPReduction.rounds (Fintype.card V) := by omega
      intro q hq
      rcases List.mem_append.mp hq with hprev | hcurrent
      · exact ih hk' q hprev
      · apply stepTrace_bounded O hO _ _ _ q hcurrent
        rw [fastSquared_eq O hO w W hw k hk']
        exact semantic_finite_bound hw k hk'

/-- Dense integer arrays in the shared bit-scaling schedule: each level
forms two halves, two targets, and one refined result. Base zero is also stored.
Oracle answer arrays are charged inside each oracle call, not silently free.
-/
def bitFormationTrace (O : MinPlusReduction.TriangleOracle V V V) :
    ℕ → IntMatrix V → IntMatrix V → List (IntMatrix V)
  | 0, _, _ => [fun _ _ => 0]
  | d+1, A, B =>
      let C := MinPlusReduction.bitScale O d (MinPlusReduction.half A) (MinPlusReduction.half B)
      bitFormationTrace O d (MinPlusReduction.half A) (MinPlusReduction.half B) ++
        [MinPlusReduction.half A, MinPlusReduction.half B,
         (fun i j => -(2*C i j)), (fun i j => -(2*C i j+1)),
         MinPlusReduction.refine O A B C]

theorem bitFormationTrace_length (O : MinPlusReduction.TriangleOracle V V V)
    (d : ℕ) (A B : IntMatrix V) : (bitFormationTrace O d A B).length = 5*d+1 := by
  induction d generalizing A B with
  | zero => rfl
  | succ d ih => simp only [bitFormationTrace, List.length_append, List.length_cons,
      List.length_nil, ih]; omega

/-- Each array is charged n² entry writes. Six additional arrays are the two
sentinel encodings, two shifts, unshifted result, and restored optional result.
No whole-matrix formation is treated as a constant-time operation.
-/
def stageWrites (n B : ℕ) : ℕ :=
  (5*MinPlusReduction.signedLevels (sentinel B)+7)*n^2

theorem stageWrites_from_trace (O : MinPlusReduction.TriangleOracle V V V)
    (n B : ℕ) (A C : IntMatrix V) :
    (bitFormationTrace O (MinPlusReduction.signedLevels (sentinel B)) A C).length*n^2 +
      6*n^2 = stageWrites n B := by
  rw [bitFormationTrace_length]
  unfold stageWrites
  ring

/-- Joint value and schedule ledger, charging adaptive query-trace lengths and
dense array-materialization writes at each bit-scaled squaring stage.
-/
def execution [Fintype V] [DecidableEq V] (O : MinPlusReduction.TriangleOracle V V V)
    (w : APSPReduction.Graph V) (B : ℕ) : ℕ → APSPReduction.Matrix V × ℕ × ℕ
  | 0 => (initial w, 0, (Fintype.card V)^2)
  | k+1 =>
      let previous := execution O w B k
      (step O B previous.1,
       previous.2.1+(stepTrace O B previous.1).length,
       previous.2.2+stageWrites (Fintype.card V) B)

theorem execution_value [Fintype V] [DecidableEq V]
    (O : MinPlusReduction.TriangleOracle V V V) (w : APSPReduction.Graph V) (B k : ℕ) :
    (execution O w B k).1 = fastSquared O w B k := by
  induction k with
  | zero => rfl
  | succ k ih => exact congrArg (step O B) ih

theorem execution_calls [Fintype V] [DecidableEq V]
    (O : MinPlusReduction.TriangleOracle V V V) (w : APSPReduction.Graph V) (B k : ℕ) :
    (execution O w B k).2.1 = k*(2*MinPlusReduction.signedLevels (sentinel B)) := by
  induction k with
  | zero => simp [execution]
  | succ k ih => simp only [execution, ih, stepTrace_length]; ring

theorem execution_writes [Fintype V] [DecidableEq V]
    (O : MinPlusReduction.TriangleOracle V V V) (w : APSPReduction.Graph V) (B k : ℕ) :
    (execution O w B k).2.2 = (Fintype.card V)^2+k*stageWrites (Fintype.card V) B := by
  induction k with
  | zero => simp [execution]
  | succ k ih => simp only [execution, ih]; ring

theorem sentinel_polynomial_bound {n W degree : ℕ} (hn : 2 ≤ n) (hW : W ≤ n^degree) :
    sentinel (globalBound n W) ≤ n^(degree+5) := by
  have hp : 1 ≤ n^(degree+1) := Nat.one_le_pow _ _ (by omega)
  have hnp : n*W ≤ n^(degree+1) := by
    calc
      n*W ≤ n*n^degree := Nat.mul_le_mul_left n hW
      _ = n^(degree+1) := by rw [Nat.pow_succ]; ring
  have hfour : 9 ≤ n^4 := by
    have h := Nat.pow_le_pow_left hn 4
    norm_num at h
    omega
  calc
    sentinel (globalBound n W) = 8*(n*W)+1 := by unfold sentinel globalBound; ring
    _ ≤ 9*n^(degree+1) := by omega
    _ ≤ n^4*n^(degree+1) := Nat.mul_le_mul_right _ hfour
    _ = n^(4+(degree+1)) := (Nat.pow_add _ _ _).symm
    _ = n^(degree+5) := by congr 1; omega

/-- Actual adaptive equality-oracle calls are O(log² n) for a fixed input
weight exponent. The bound includes both equality tests at every bit level. -/
theorem polylog_oracle_calls [Fintype V] [DecidableEq V]
    (O : MinPlusReduction.TriangleOracle V V V) (w : APSPReduction.Graph V)
    (W degree : ℕ) (hn : 2 ≤ Fintype.card V) (hW : W ≤ (Fintype.card V)^degree) :
    (execution O w (globalBound (Fintype.card V) W)
      (APSPReduction.rounds (Fintype.card V))).2.1 ≤
      (Nat.log2 (Fintype.card V)+1)*
        (2*((degree+5)*(Nat.log2 (Fintype.card V)+1)+2)) := by
  have h := MinPlusReduction.polynomial_call_bound (Fintype.card V) (degree+5)
    (sentinel (globalBound (Fintype.card V) W)) (sentinel_polynomial_bound hn hW)
  rw [MinPlusReduction.scheduledCalls_eq] at h
  rw [execution_calls, APSPReduction.rounds]
  exact Nat.mul_le_mul_left _ h

/-- Dense formation is charged by n² writes for every scheduled array. For fixed
input weight degree this is O(n² log² n), separate from equality-oracle work. -/
theorem polylog_formation_writes [Fintype V] [DecidableEq V]
    (O : MinPlusReduction.TriangleOracle V V V) (w : APSPReduction.Graph V)
    (W degree : ℕ) (hn : 2 ≤ Fintype.card V) (hW : W ≤ (Fintype.card V)^degree) :
    (execution O w (globalBound (Fintype.card V) W)
      (APSPReduction.rounds (Fintype.card V))).2.2 ≤
      (1+(Nat.log2 (Fintype.card V)+1)*
        (5*((degree+5)*(Nat.log2 (Fintype.card V)+1)+2)+7))*(Fintype.card V)^2 := by
  have h := MinPlusReduction.polynomial_call_bound (Fintype.card V) (degree+5)
    (sentinel (globalBound (Fintype.card V) W)) (sentinel_polynomial_bound hn hW)
  rw [MinPlusReduction.scheduledCalls_eq] at h
  have hd : MinPlusReduction.signedLevels (sentinel (globalBound (Fintype.card V) W)) ≤
      (degree+5)*(Nat.log2 (Fintype.card V)+1)+2 := by omega
  have hs : stageWrites (Fintype.card V) (globalBound (Fintype.card V) W) ≤
      (5*((degree+5)*(Nat.log2 (Fintype.card V)+1)+2)+7)*(Fintype.card V)^2 := by
    unfold stageWrites
    exact Nat.mul_le_mul_right _ (by omega)
  rw [execution_writes]
  calc
    (Fintype.card V)^2+APSPReduction.rounds (Fintype.card V)*
        stageWrites (Fintype.card V) (globalBound (Fintype.card V) W) ≤
      (Fintype.card V)^2+APSPReduction.rounds (Fintype.card V)*
        ((5*((degree+5)*(Nat.log2 (Fintype.card V)+1)+2)+7)*(Fintype.card V)^2) :=
      Nat.add_le_add_left (Nat.mul_le_mul_left _ hs) _
    _ = _ := by unfold APSPReduction.rounds; ring

def SymmetricQueryBound (q : Query V) (P : ℤ) : Prop :=
  (∀ i k, -P ≤ q.1 i k ∧ q.1 i k ≤ P) ∧
  (∀ k j, -P ≤ q.2.1 k j ∧ q.2.1 k j ≤ P) ∧
  (∀ i j, -P ≤ q.2.2 i j ∧ q.2.2 i j ≤ P)

theorem query_symmetric (q : Query V) (K : ℤ) (hK : 0 ≤ K)
    (h : MinPlusReduction.QueryMagnitudeBound q K) : SymmetricQueryBound q (2*K+1) := by
  constructor
  · intro i k
    have ha := h.1 i k
    constructor <;> omega
  constructor
  · intro k j
    have hb := h.2.1 k j
    constructor <;> omega
  · intro i j
    have hc := h.2.2 i j
    constructor <;> omega

/-- All actual adaptive oracle inputs, including the signed target matrix,
have magnitude at most 64*n*W+13. -/
theorem fastTrace_weight_bound [Fintype V] [DecidableEq V] [Nonempty V]
    (O : MinPlusReduction.TriangleOracle V V V) (hO : MinPlusReduction.OracleCorrect O)
    (w : APSPReduction.Graph V) (W : ℕ) (hw : APSPReduction.EdgeBound w W)
    (k : ℕ) (hk : k ≤ APSPReduction.rounds (Fintype.card V)) :
    ∀ q ∈ fastTrace O w (globalBound (Fintype.card V) W) k,
      SymmetricQueryBound q ((64*Fintype.card V*W+13 : ℕ) : ℤ) := by
  intro q hq
  have h := fastTrace_bounded O hO w W hw k hk q hq
  have hs := query_symmetric q _ (by positivity) h
  have he : 2*(4*(sentinel (globalBound (Fintype.card V) W) : ℤ)+2)+1 =
      ((64*Fintype.card V*W+13 : ℕ) : ℤ) := by
    simp only [sentinel, globalBound, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    ring
  rwa [he] at hs

/-- Final actual algorithm values have the same polynomial magnitude guarantee
as the semantic squaring reduction; no output-bound assumption is introduced. -/
theorem fastAPSP_entry_bound [Fintype V] [DecidableEq V]
    (O : MinPlusReduction.TriangleOracle V V V) (hO : MinPlusReduction.OracleCorrect O)
    (w : APSPReduction.Graph V) (W : ℕ) (hw : APSPReduction.EdgeBound w W)
    {a b : V} {z : ℤ} (hz : fastAPSP O w W a b = (z : APSPReduction.Distance)) :
    z.natAbs ≤ 2*Fintype.card V*W := by
  let : Nonempty V := ⟨a⟩
  have he : fastAPSP O w W = APSPReduction.apsp w :=
    fastSquared_eq O hO w W hw _ le_rfl
  rw [he] at hz
  exact APSPReduction.apsp_entry_bound hw hz

/-- Correctness and both scheduled charges refer to this same recursive program. -/
theorem execution_correct [Fintype V] [DecidableEq V]
    (O : MinPlusReduction.TriangleOracle V V V) (hO : MinPlusReduction.OracleCorrect O)
    (w : APSPReduction.Graph V) (W : ℕ) (hw : APSPReduction.EdgeBound w W)
    (hno : APSPReduction.NoNegativeCycles w) :
    APSPReduction.IsAPSP w
      ((execution O w (globalBound (Fintype.card V) W)
        (APSPReduction.rounds (Fintype.card V))).1) := by
  rw [execution_value]
  exact fastAPSP_correct O hO w W hw hno

#print axioms optional_eq_minPlus
#print axioms fastSquared_eq
#print axioms fastAPSP_correct
#print axioms fastTrace_bounded
#print axioms execution_calls
#print axioms execution_writes
#print axioms polylog_oracle_calls
#print axioms polylog_formation_writes
#print axioms fastTrace_weight_bound
#print axioms fastAPSP_entry_bound
#print axioms execution_correct
end ThinMatrix.APSPAlgorithm
