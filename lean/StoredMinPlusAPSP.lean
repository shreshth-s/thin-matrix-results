import APSPAlgorithm

/-!
# Stored min-plus bit scaling and repeated squaring

Every matrix in this executable reduction is an array-backed nested Vector.
Each oracle invocation returns its complete stored Boolean answer table and
its own payload/resources. The same recursion returns values, actual calls,
and dense formation counters; no queryTrace, fastTrace, or trace-length
computation executes the oracle again. Functional matrices below occur only
as decoded specifications and correctness interfaces.

The callback contract is correctness of a materialized Exact Triangle answer
matrix. Its work field is retained as supplied, not asserted to be a proved
fast running time. Concrete callback implementations must supply and price
their own computation/resource payloads.
-/

namespace ThinMatrix.StoredMinPlusAPSP

abbrev Table (n : ℕ) (α : Type) := Vector (Vector α n) n
abbrev IntTable (n : ℕ) := Table n ℤ
abbrev BoolTable (n : ℕ) := Table n Bool
abbrev OptionalTable (n : ℕ) := Table n (Option ℤ)

def decode {n : ℕ} {α : Type} (A : Table n α) : Fin n → Fin n → α :=
  fun i j => (A.get i).get j

def store {n : ℕ} {α : Type} (A : Fin n → Fin n → α) : Table n α :=
  Vector.ofFn (fun i => Vector.ofFn (fun j => A i j))

@[simp] theorem decode_store {n : ℕ} {α : Type} (A : Fin n → Fin n → α) :
    decode (store A) = A := by
  funext i j
  simp [decode, store]

@[simp] theorem store_decode {n : ℕ} {α : Type} (A : Table n α) : store (decode A) = A := by
  apply Vector.ext
  intro i hi
  apply Vector.ext
  intro j hj
  simp [store, decode, Vector.get]

structure OracleOutput (n : ℕ) (Payload : Type) where
  answers : BoolTable n
  payload : Payload
  work : ℕ
  answerWrites : ℕ

abbrev DenseOracle (n : ℕ) (Payload : Type) :=
  IntTable n → IntTable n → IntTable n → OracleOutput n Payload

def DenseOracleCorrect {n : ℕ} {Payload : Type} (O : DenseOracle n Payload) : Prop :=
  ∀ A B T i j, decode (O A B T).answers i j = true ↔
    ∃ k, decode A i k + decode B k j + decode T i j = 0

/-- This conversion is a specification; the stored program calls O directly. -/
def semanticOracle {n : ℕ} {Payload : Type} (O : DenseOracle n Payload) :
    MinPlusReduction.TriangleOracle (Fin n) (Fin n) (Fin n) :=
  fun A B T => decode (O (store A) (store B) (store T)).answers

theorem semanticOracle_correct {n : ℕ} {Payload : Type} (O : DenseOracle n Payload)
    (hO : DenseOracleCorrect O) : MinPlusReduction.OracleCorrect (semanticOracle O) := by
  intro A B T i j
  simpa only [semanticOracle, decode_store] using hO (store A) (store B) (store T) i j

structure Call (n : ℕ) (Payload : Type) where
  left : IntTable n
  right : IntTable n
  target : IntTable n
  output : OracleOutput n Payload

def Call.query {n : ℕ} {Payload : Type} (c : Call n Payload) : APSPAlgorithm.Query (Fin n) :=
  (decode c.left, decode c.right, decode c.target)

structure Execution (n : ℕ) (α Payload : Type) where
  value : Table n α
  calls : List (Call n Payload)
  formationWrites : ℕ
  oracleWork : ℕ
  answerWrites : ℕ

def half {n : ℕ} (A : IntTable n) : IntTable n := store (fun i j => decode A i j / 2)
def shift {n : ℕ} (A : IntTable n) (u : ℤ) : IntTable n := store (fun i j => decode A i j + u)

def bitScale {n : ℕ} {Payload : Type} (O : DenseOracle n Payload) :
    ℕ → IntTable n → IntTable n → Execution n ℤ Payload
  | 0, _, _ => ⟨store (fun _ _ => 0), [], n ^ 2, 0, 0⟩
  | d + 1, A, B =>
      let Ahalf := half A
      let Bhalf := half B
      let coarse := bitScale O d Ahalf Bhalf
      let target0 := store (fun i j => -(2 * decode coarse.value i j))
      let target1 := store (fun i j => -(2 * decode coarse.value i j + 1))
      let z0 := O A B target0
      let z1 := O A B target1
      let value := store (fun i j =>
        if decode z0.answers i j then 2 * decode coarse.value i j
        else if decode z1.answers i j then 2 * decode coarse.value i j + 1
        else 2 * decode coarse.value i j + 2)
      ⟨value, coarse.calls ++ [⟨A, B, target0, z0⟩, ⟨A, B, target1, z1⟩],
        coarse.formationWrites + 5 * n ^ 2,
        coarse.oracleWork + z0.work + z1.work,
        coarse.answerWrites + z0.answerWrites + z1.answerWrites⟩

theorem bitScale_value {n : ℕ} {Payload : Type} (O : DenseOracle n Payload)
    (d : ℕ) (A B : IntTable n) :
    decode (bitScale O d A B).value =
      MinPlusReduction.bitScale (semanticOracle O) d (decode A) (decode B) := by
  induction d generalizing A B with
  | zero => simp [bitScale, MinPlusReduction.bitScale]
  | succ d ih =>
      simp only [bitScale, decode_store, MinPlusReduction.bitScale, MinPlusReduction.refine,
        semanticOracle, store_decode]
      rw [ih]
      simp only [half, decode_store]
      rfl

theorem bitScale_calls {n : ℕ} {Payload : Type} (O : DenseOracle n Payload)
    (d : ℕ) (A B : IntTable n) : (bitScale O d A B).calls.length = 2 * d := by
  induction d generalizing A B with
  | zero => rfl
  | succ d ih => simp only [bitScale, List.length_append, List.length_cons, List.length_nil, ih]; omega

theorem bitScale_formationWrites {n : ℕ} {Payload : Type} (O : DenseOracle n Payload)
    (d : ℕ) (A B : IntTable n) : (bitScale O d A B).formationWrites = (5 * d + 1) * n ^ 2 := by
  induction d generalizing A B with
  | zero => simp [bitScale]
  | succ d ih => simp only [bitScale, ih]; ring

theorem bitScale_trace {n : ℕ} {Payload : Type} (O : DenseOracle n Payload)
    (d : ℕ) (A B : IntTable n) :
    (bitScale O d A B).calls.map Call.query =
      MinPlusReduction.queryTrace (semanticOracle O) d (decode A) (decode B) := by
  induction d generalizing A B with
  | zero => rfl
  | succ d ih =>
      simp only [bitScale, List.map_append, List.map_cons, List.map_nil, Call.query,
        decode_store, MinPlusReduction.queryTrace, ih, bitScale_value,
        half, decode_store]
      rfl

def signedProduct {n : ℕ} {Payload : Type} (O : DenseOracle n Payload) (d : ℕ)
    (A B : IntTable n) (u v : ℤ) : Execution n ℤ Payload :=
  let shiftedA := shift A u
  let shiftedB := shift B v
  let core := bitScale O d shiftedA shiftedB
  ⟨store (fun i j => decode core.value i j - u - v), core.calls,
    core.formationWrites + 3 * n ^ 2, core.oracleWork, core.answerWrites⟩

theorem signedProduct_value {n : ℕ} {Payload : Type} (O : DenseOracle n Payload) (d : ℕ)
    (A B : IntTable n) (u v : ℤ) :
    decode (signedProduct O d A B u v).value =
      MinPlusReduction.signedBitScale (semanticOracle O) d (decode A) (decode B) u v := by
  simp only [signedProduct, decode_store, bitScale_value, shift, decode_store,
    ]
  rfl

def optionalProduct {n : ℕ} {Payload : Type} (O : DenseOracle n Payload) (W : ℕ)
    (A B : OptionalTable n) : Execution n (Option ℤ) Payload :=
  let S := APSPAlgorithm.sentinel W
  let encodedA := store (fun i j => MinPlusReduction.encode S (decode A i j))
  let encodedB := store (fun i j => MinPlusReduction.encode S (decode B i j))
  let core := signedProduct O (MinPlusReduction.signedLevels S) encodedA encodedB S S
  ⟨store (fun i j => if 2 * (W : ℤ) < decode core.value i j then none else some (decode core.value i j)),
    core.calls, core.formationWrites + 3 * n ^ 2, core.oracleWork, core.answerWrites⟩

theorem optionalProduct_value {n : ℕ} {Payload : Type} (O : DenseOracle n Payload) (W : ℕ)
    (A B : OptionalTable n) :
    decode (optionalProduct O W A B).value =
      MinPlusReduction.optionalBitScale (semanticOracle O) (decode A) (decode B)
        W (APSPAlgorithm.sentinel W) (APSPAlgorithm.sentinel W) := by
  simp only [optionalProduct, decode_store, signedProduct_value, MinPlusReduction.optionalBitScale,
    decode_store]
  rfl

def squared {n : ℕ} {Payload : Type} (O : DenseOracle n Payload) (w : OptionalTable n)
    (B : ℕ) : ℕ → Execution n (Option ℤ) Payload
  | 0 => ⟨store (APSPAlgorithm.initial (decode w)), [], n ^ 2, 0, 0⟩
  | k + 1 =>
      let previous := squared O w B k
      let current := optionalProduct O B previous.value previous.value
      ⟨current.value, previous.calls ++ current.calls,
        previous.formationWrites + current.formationWrites,
        previous.oracleWork + current.oracleWork,
        previous.answerWrites + current.answerWrites⟩

theorem squared_value {n : ℕ} {Payload : Type} (O : DenseOracle n Payload)
    (w : OptionalTable n) (B k : ℕ) :
    decode (squared O w B k).value = APSPAlgorithm.fastSquared (semanticOracle O) (decode w) B k := by
  induction k with
  | zero => simp [squared, APSPAlgorithm.fastSquared]
  | succ k ih =>
      simp only [squared, optionalProduct_value, APSPAlgorithm.fastSquared, APSPAlgorithm.step, ih]

def apsp {n : ℕ} {Payload : Type} (O : DenseOracle n Payload) (w : OptionalTable n) (W : ℕ) :
    Execution n (Option ℤ) Payload :=
  squared O w (APSPAlgorithm.globalBound n W) (APSPReduction.rounds n)

theorem apsp_correct {n : ℕ} {Payload : Type} (O : DenseOracle n Payload)
    (hO : DenseOracleCorrect O) (w : OptionalTable n) (W : ℕ)
    (hw : APSPReduction.EdgeBound (decode w) W) (hno : APSPReduction.NoNegativeCycles (decode w)) :
    APSPReduction.IsAPSP (decode w) (decode (apsp O w W).value) := by
  have hs := squared_value O w (APSPAlgorithm.globalBound n W) (APSPReduction.rounds n)
  have hc : APSPReduction.IsAPSP (decode w)
      (APSPAlgorithm.fastSquared (semanticOracle O) (decode w) (APSPAlgorithm.globalBound n W) (APSPReduction.rounds n)) := by
    simpa only [APSPAlgorithm.fastAPSP, Fintype.card_fin] using
      APSPAlgorithm.fastAPSP_correct (semanticOracle O) (semanticOracle_correct O hO) (decode w) W hw hno
  exact hs.symm ▸ hc


theorem stored_cells {n : ℕ} {α : Type} (A : Table n α) :
    (∑ i : Fin n, (A.get i).toArray.size) = n ^ 2 := by
  simp [pow_two]

theorem optionalProduct_calls {n : ℕ} {Payload : Type} (O : DenseOracle n Payload)
    (W : ℕ) (A B : OptionalTable n) :
    (optionalProduct O W A B).calls.length = 2 * MinPlusReduction.signedLevels (APSPAlgorithm.sentinel W) := by
  exact bitScale_calls _ _ _ _

theorem optionalProduct_formationWrites {n : ℕ} {Payload : Type} (O : DenseOracle n Payload)
    (W : ℕ) (A B : OptionalTable n) :
    (optionalProduct O W A B).formationWrites =
      (5 * MinPlusReduction.signedLevels (APSPAlgorithm.sentinel W) + 7) * n ^ 2 := by
  simp only [optionalProduct, signedProduct, bitScale_formationWrites]
  ring

theorem optionalProduct_stepTrace {n : ℕ} {Payload : Type} (O : DenseOracle n Payload)
    (W : ℕ) (A : OptionalTable n) :
    (optionalProduct O W A A).calls.map Call.query = APSPAlgorithm.stepTrace (semanticOracle O) W (decode A) := by
  simp only [optionalProduct, signedProduct, bitScale_trace, shift, decode_store]
  rfl

theorem squared_calls {n : ℕ} {Payload : Type} (O : DenseOracle n Payload)
    (w : OptionalTable n) (B k : ℕ) :
    (squared O w B k).calls.length = k * (2 * MinPlusReduction.signedLevels (APSPAlgorithm.sentinel B)) := by
  induction k with
  | zero => simp [squared]
  | succ k ih => simp only [squared, List.length_append, ih, optionalProduct_calls]; ring

theorem squared_formationWrites {n : ℕ} {Payload : Type} (O : DenseOracle n Payload)
    (w : OptionalTable n) (B k : ℕ) :
    (squared O w B k).formationWrites =
      (1 + k * (5 * MinPlusReduction.signedLevels (APSPAlgorithm.sentinel B) + 7)) * n ^ 2 := by
  induction k with
  | zero => simp [squared]
  | succ k ih => simp only [squared, ih, optionalProduct_formationWrites]; ring

theorem squared_trace {n : ℕ} {Payload : Type} (O : DenseOracle n Payload)
    (w : OptionalTable n) (B k : ℕ) :
    (squared O w B k).calls.map Call.query = APSPAlgorithm.fastTrace (semanticOracle O) (decode w) B k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [squared, List.map_append, optionalProduct_stepTrace, ih, APSPAlgorithm.fastTrace]
      have hc := congrArg
        (fun C : Fin n → Fin n → Option ℤ => APSPAlgorithm.stepTrace (semanticOracle O) B C)
        (squared_value O w B k)
      exact congrArg (fun qs => APSPAlgorithm.fastTrace (semanticOracle O) (decode w) B k ++ qs) hc

def callWork {n : ℕ} {Payload : Type} (calls : List (Call n Payload)) : ℕ :=
  (calls.map (fun c => c.output.work)).sum

def callAnswerWrites {n : ℕ} {Payload : Type} (calls : List (Call n Payload)) : ℕ :=
  (calls.map (fun c => c.output.answerWrites)).sum

theorem bitScale_oracleWork {n : ℕ} {Payload : Type} (O : DenseOracle n Payload)
    (d : ℕ) (A B : IntTable n) : (bitScale O d A B).oracleWork = callWork (bitScale O d A B).calls := by
  induction d generalizing A B with
  | zero => rfl
  | succ d ih =>
      have hp := ih (half A) (half B)
      unfold callWork at hp
      simp only [bitScale, callWork, List.map_append, List.map_cons, List.map_nil,
        List.sum_append, List.sum_cons, List.sum_nil]
      omega

theorem bitScale_answerWrites {n : ℕ} {Payload : Type} (O : DenseOracle n Payload)
    (d : ℕ) (A B : IntTable n) : (bitScale O d A B).answerWrites = callAnswerWrites (bitScale O d A B).calls := by
  induction d generalizing A B with
  | zero => rfl
  | succ d ih =>
      have hp := ih (half A) (half B)
      unfold callAnswerWrites at hp
      simp only [bitScale, callAnswerWrites, List.map_append, List.map_cons, List.map_nil,
        List.sum_append, List.sum_cons, List.sum_nil]
      omega

theorem optionalProduct_oracleWork {n : ℕ} {Payload : Type} (O : DenseOracle n Payload)
    (W : ℕ) (A B : OptionalTable n) :
    (optionalProduct O W A B).oracleWork = callWork (optionalProduct O W A B).calls :=
  bitScale_oracleWork _ _ _ _

theorem optionalProduct_answerWrites {n : ℕ} {Payload : Type} (O : DenseOracle n Payload)
    (W : ℕ) (A B : OptionalTable n) :
    (optionalProduct O W A B).answerWrites = callAnswerWrites (optionalProduct O W A B).calls :=
  bitScale_answerWrites _ _ _ _

theorem squared_oracleWork {n : ℕ} {Payload : Type} (O : DenseOracle n Payload)
    (w : OptionalTable n) (B k : ℕ) : (squared O w B k).oracleWork = callWork (squared O w B k).calls := by
  induction k with
  | zero => rfl
  | succ k ih =>
      have hs := optionalProduct_oracleWork O B (squared O w B k).value (squared O w B k).value
      unfold callWork at ih hs
      simp only [squared, callWork, List.map_append, List.sum_append]
      omega

theorem squared_answerWrites {n : ℕ} {Payload : Type} (O : DenseOracle n Payload)
    (w : OptionalTable n) (B k : ℕ) : (squared O w B k).answerWrites = callAnswerWrites (squared O w B k).calls := by
  induction k with
  | zero => rfl
  | succ k ih =>
      have hs := optionalProduct_answerWrites O B (squared O w B k).value (squared O w B k).value
      unfold callAnswerWrites at ih hs
      simp only [squared, callAnswerWrites, List.map_append, List.sum_append]
      omega

def Call.Faithful {n : ℕ} {Payload : Type} (O : DenseOracle n Payload) (c : Call n Payload) : Prop :=
  c.output = O c.left c.right c.target

theorem bitScale_calls_faithful {n : ℕ} {Payload : Type} (O : DenseOracle n Payload)
    (d : ℕ) (A B : IntTable n) : ∀ c ∈ (bitScale O d A B).calls, c.Faithful O := by
  induction d generalizing A B with
  | zero => simp [bitScale]
  | succ d ih =>
      intro c hc
      simp only [bitScale, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with hp | rfl | rfl
      · exact ih _ _ c hp
      · rfl
      · rfl

theorem optionalProduct_calls_faithful {n : ℕ} {Payload : Type} (O : DenseOracle n Payload)
    (W : ℕ) (A B : OptionalTable n) : ∀ c ∈ (optionalProduct O W A B).calls, c.Faithful O :=
  bitScale_calls_faithful _ _ _ _

theorem squared_calls_faithful {n : ℕ} {Payload : Type} (O : DenseOracle n Payload)
    (w : OptionalTable n) (B k : ℕ) : ∀ c ∈ (squared O w B k).calls, c.Faithful O := by
  induction k with
  | zero => simp [squared]
  | succ k ih =>
      intro c hc
      rcases List.mem_append.mp hc with hp | hs
      · exact ih c hp
      · exact optionalProduct_calls_faithful _ _ _ _ c hs

theorem sum_callWork_le {n : ℕ} {Payload : Type} (calls : List (Call n Payload)) (M : ℕ)
    (hM : ∀ c ∈ calls, c.output.work ≤ M) : callWork calls ≤ calls.length * M := by
  induction calls with
  | nil => simp [callWork]
  | cons c cs ih =>
      have hc := hM c (by simp)
      have ht := ih (fun t ht => hM t (by simp [ht]))
      simp only [callWork, List.map_cons, List.sum_cons, List.length_cons] at *
      nlinarith

theorem sum_callAnswerWrites_le {n : ℕ} {Payload : Type} (calls : List (Call n Payload)) (M : ℕ)
    (hM : ∀ c ∈ calls, c.output.answerWrites ≤ M) : callAnswerWrites calls ≤ calls.length * M := by
  induction calls with
  | nil => simp [callAnswerWrites]
  | cons c cs ih =>
      have hc := hM c (by simp)
      have ht := ih (fun t ht => hM t (by simp [ht]))
      simp only [callAnswerWrites, List.map_cons, List.sum_cons, List.length_cons] at *
      nlinarith

theorem squared_query_bound {n : ℕ} {Payload : Type} [Nonempty (Fin n)]
    (O : DenseOracle n Payload) (hO : DenseOracleCorrect O) (w : OptionalTable n) (W : ℕ)
    (hw : APSPReduction.EdgeBound (decode w) W) (k : ℕ) (hk : k ≤ APSPReduction.rounds n)
    (c : Call n Payload) (hc : c ∈ (squared O w (APSPAlgorithm.globalBound n W) k).calls) :
    APSPAlgorithm.SymmetricQueryBound c.query ((64 * n * W + 13 : ℕ) : ℤ) := by
  have hm : c.query ∈ APSPAlgorithm.fastTrace (semanticOracle O) (decode w) (APSPAlgorithm.globalBound n W) k := by
    rw [← squared_trace]
    exact List.mem_map.mpr ⟨c, hc, rfl⟩
  have hb := APSPAlgorithm.fastTrace_weight_bound (semanticOracle O) (semanticOracle_correct O hO)
    (decode w) W hw k (by simpa only [Fintype.card_fin] using hk) c.query
  simp only [Fintype.card_fin] at hb
  exact hb hm

theorem squared_original_sum_bound {n : ℕ} {Payload : Type} [Nonempty (Fin n)]
    (O : DenseOracle n Payload) (hO : DenseOracleCorrect O) (w : OptionalTable n) (W : ℕ)
    (hw : APSPReduction.EdgeBound (decode w) W) (k : ℕ) (hk : k ≤ APSPReduction.rounds n)
    (c : Call n Payload) (hc : c ∈ (squared O w (APSPAlgorithm.globalBound n W) k).calls)
    (i j t : Fin n) (r : ℤ) (hr : -1 ≤ r ∧ r ≤ 1) :
    (decode c.left i t + decode c.right t j + decode c.target i j - r).natAbs ≤ 192 * n * W + 40 := by
  have hb := squared_query_bound O hO w W hw k hk c hc
  have ha := hb.1 i t
  have hbb := hb.2.1 t j
  have ht := hb.2.2 i j
  simp only [Call.query] at ha hbb ht
  have hs : |decode c.left i t + decode c.right t j + decode c.target i j - r| ≤
      ((192 * n * W + 40 : ℕ) : ℤ) := by
    apply abs_le.mpr
    push_cast at *
    constructor <;> nlinarith [ha.1, ha.2, hbb.1, hbb.2, ht.1, ht.2]
  rw [← Int.natCast_natAbs] at hs
  exact_mod_cast hs



theorem apsp_calls {n : ℕ} {Payload : Type} (O : DenseOracle n Payload) (w : OptionalTable n) (W : ℕ) :
    (apsp O w W).calls.length =
      APSPReduction.rounds n * (2 * MinPlusReduction.signedLevels
        (APSPAlgorithm.sentinel (APSPAlgorithm.globalBound n W))) :=
  squared_calls _ _ _ _

theorem apsp_formationWrites {n : ℕ} {Payload : Type} (O : DenseOracle n Payload) (w : OptionalTable n) (W : ℕ) :
    (apsp O w W).formationWrites =
      (1 + APSPReduction.rounds n * (5 * MinPlusReduction.signedLevels
        (APSPAlgorithm.sentinel (APSPAlgorithm.globalBound n W)) + 7)) * n ^ 2 :=
  squared_formationWrites _ _ _ _

theorem apsp_calls_faithful {n : ℕ} {Payload : Type} (O : DenseOracle n Payload)
    (w : OptionalTable n) (W : ℕ) : ∀ c ∈ (apsp O w W).calls, c.Faithful O :=
  squared_calls_faithful _ _ _ _

theorem apsp_query_bound {n : ℕ} {Payload : Type} (O : DenseOracle n Payload)
    (hO : DenseOracleCorrect O) (w : OptionalTable n) (W : ℕ)
    (hw : APSPReduction.EdgeBound (decode w) W)
    (c : Call n Payload) (hc : c ∈ (apsp O w W).calls) :
    APSPAlgorithm.SymmetricQueryBound c.query ((64 * n * W + 13 : ℕ) : ℤ) := by
  cases n with
  | zero =>
      refine ⟨?_, ?_, ?_⟩ <;> intro i <;> exact Fin.elim0 i
  | succ n => exact squared_query_bound O hO w W hw _ le_rfl c hc

theorem apsp_original_sum_bound {n : ℕ} {Payload : Type} (O : DenseOracle n Payload)
    (hO : DenseOracleCorrect O) (w : OptionalTable n) (W : ℕ)
    (hw : APSPReduction.EdgeBound (decode w) W)
    (c : Call n Payload) (hc : c ∈ (apsp O w W).calls)
    (i j t : Fin n) (r : ℤ) (hr : -1 ≤ r ∧ r ≤ 1) :
    (decode c.left i t + decode c.right t j + decode c.target i j - r).natAbs ≤ 192 * n * W + 40 := by
  letI : Nonempty (Fin n) := ⟨i⟩
  exact squared_original_sum_bound O hO w W hw _ le_rfl c hc i j t r hr

theorem sentinelLevels_polynomial_bound {n W degree : ℕ} (hn : 2 ≤ n) (hW : W ≤ n ^ degree) :
    MinPlusReduction.signedLevels (APSPAlgorithm.sentinel (APSPAlgorithm.globalBound n W)) ≤
      (degree + 5) * (n.log2 + 1) + 2 := by
  have h := MinPlusReduction.polynomial_call_bound n (degree + 5)
    (APSPAlgorithm.sentinel (APSPAlgorithm.globalBound n W))
    (APSPAlgorithm.sentinel_polynomial_bound hn hW)
  rw [MinPlusReduction.scheduledCalls_eq] at h
  omega

theorem apsp_calls_polylog {n : ℕ} {Payload : Type} (O : DenseOracle n Payload)
    (w : OptionalTable n) (W degree : ℕ) (hn : 2 ≤ n) (hW : W ≤ n ^ degree) :
    (apsp O w W).calls.length ≤
      (n.log2 + 1) * (2 * ((degree + 5) * (n.log2 + 1) + 2)) := by
  rw [apsp_calls, APSPReduction.rounds]
  exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left 2 (sentinelLevels_polynomial_bound hn hW))

theorem apsp_formationWrites_polylog {n : ℕ} {Payload : Type} (O : DenseOracle n Payload)
    (w : OptionalTable n) (W degree : ℕ) (hn : 2 ≤ n) (hW : W ≤ n ^ degree) :
    (apsp O w W).formationWrites ≤
      (1 + (n.log2 + 1) * (5 * ((degree + 5) * (n.log2 + 1) + 2) + 7)) * n ^ 2 := by
  rw [apsp_formationWrites, APSPReduction.rounds]
  have hd := sentinelLevels_polynomial_bound hn hW
  exact Nat.mul_le_mul_right _ (Nat.add_le_add_left (Nat.mul_le_mul_left _ (by omega)) _)

/-- A contract prices the resources returned by each bounded actual callback.
It does not postulate a fast implementation or instruction-level cost. -/
structure CostContract {n : ℕ} {Payload : Type} (O : DenseOracle n Payload) (P M R : ℕ) : Prop where
  work : ∀ A B T, APSPAlgorithm.SymmetricQueryBound (decode A, decode B, decode T) (P : ℤ) →
    (O A B T).work ≤ M
  answerWrites : ∀ A B T, APSPAlgorithm.SymmetricQueryBound (decode A, decode B, decode T) (P : ℤ) →
    (O A B T).answerWrites ≤ R

theorem apsp_costed_resources {n : ℕ} {Payload : Type} (O : DenseOracle n Payload)
    (hO : DenseOracleCorrect O) (w : OptionalTable n) (W M R : ℕ)
    (hw : APSPReduction.EdgeBound (decode w) W)
    (contract : CostContract O (64 * n * W + 13) M R) :
    (apsp O w W).oracleWork ≤ (apsp O w W).calls.length * M ∧
      (apsp O w W).answerWrites ≤ (apsp O w W).calls.length * R := by
  have hwork : ∀ c ∈ (apsp O w W).calls, c.output.work ≤ M := by
    intro c hc
    have hf := apsp_calls_faithful O w W c hc
    have hb := apsp_query_bound O hO w W hw c hc
    change c.output = O c.left c.right c.target at hf
    rw [hf]
    exact contract.work _ _ _ hb
  have hwrites : ∀ c ∈ (apsp O w W).calls, c.output.answerWrites ≤ R := by
    intro c hc
    have hf := apsp_calls_faithful O w W c hc
    have hb := apsp_query_bound O hO w W hw c hc
    change c.output = O c.left c.right c.target at hf
    rw [hf]
    exact contract.answerWrites _ _ _ hb
  exact ⟨(squared_oracleWork O w _ _).trans_le (sum_callWork_le _ M hwork),
    (squared_answerWrites O w _ _).trans_le (sum_callAnswerWrites_le _ R hwrites)⟩

theorem apsp_correct_and_resources {n : ℕ} {Payload : Type} (O : DenseOracle n Payload)
    (hO : DenseOracleCorrect O) (w : OptionalTable n) (W M R degree : ℕ)
    (hw : APSPReduction.EdgeBound (decode w) W) (hno : APSPReduction.NoNegativeCycles (decode w))
    (hn : 2 ≤ n) (hW : W ≤ n ^ degree) (contract : CostContract O (64 * n * W + 13) M R) :
    APSPReduction.IsAPSP (decode w) (decode (apsp O w W).value) ∧
      (apsp O w W).calls.length ≤ (n.log2 + 1) * (2 * ((degree + 5) * (n.log2 + 1) + 2)) ∧
      (apsp O w W).formationWrites ≤
        (1 + (n.log2 + 1) * (5 * ((degree + 5) * (n.log2 + 1) + 2) + 7)) * n ^ 2 ∧
      (apsp O w W).oracleWork ≤ (apsp O w W).calls.length * M ∧
      (apsp O w W).answerWrites ≤ (apsp O w W).calls.length * R :=
  ⟨apsp_correct O hO w W hw hno, apsp_calls_polylog O w W degree hn hW,
    apsp_formationWrites_polylog O w W degree hn hW, apsp_costed_resources O hO w W M R hw contract⟩


#print axioms apsp_correct
#print axioms bitScale_value
#print axioms bitScale_trace
#print axioms squared_trace
#print axioms squared_calls
#print axioms squared_formationWrites
#print axioms squared_oracleWork
#print axioms squared_answerWrites
#print axioms squared_calls_faithful
#print axioms squared_query_bound
#print axioms squared_original_sum_bound
#print axioms apsp_calls_faithful
#print axioms apsp_query_bound
#print axioms apsp_original_sum_bound
#print axioms apsp_calls_polylog
#print axioms apsp_formationWrites_polylog
#print axioms apsp_costed_resources
#print axioms apsp_correct_and_resources

end ThinMatrix.StoredMinPlusAPSP
