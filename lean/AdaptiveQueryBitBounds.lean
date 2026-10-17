import StoredMinPlusAPSP

/-!
# Bit widths of actual adaptive APSP queries

The hypotheses concern the original stored graph and its polynomial edge
bound. Query widths are derived from the recorded calls of the joint stored
execution, rather than assumed as a property of its oracle or final output.
Widths below count magnitude bits; one further bit represents the sign.
-/

namespace ThinMatrix.AdaptiveQueryBitBounds

open StoredMinPlusAPSP

def exponent (n degree : ℕ) : ℕ := (degree + 1) * n.size
def queryWidth (n degree : ℕ) : ℕ := exponent n degree + 7
def sumWidth (n degree : ℕ) : ℕ := exponent n degree + 8

/-- One common budget for query magnitude bits and reduction metadata. -/
def budget (n degree : ℕ) : ℕ := (degree + 1) * (n.size + 1) + 8

theorem budget_bounds (n degree : ℕ) :
    n.size + 1 ≤ budget n degree ∧ exponent n degree + 8 ≤ budget n degree := by
  have hn : n.size + 1 ≤ (degree + 1) * (n.size + 1) :=
    Nat.le_mul_of_pos_left _ (by omega)
  unfold budget exponent
  constructor <;> nlinarith

theorem original_bound_size (n degree W : ℕ) (hW : W ≤ n ^ degree) :
    W.size ≤ degree * n.size + 1 := by
  have hp : W ≤ 2 ^ (degree * n.size) := by
    calc
      W ≤ n ^ degree := hW
      _ ≤ (2 ^ n.size) ^ degree :=
        Nat.pow_le_pow_left (Nat.lt_size_self n).le _
      _ = _ := by rw [← pow_mul]; congr 1; ring
  apply Nat.size_le.mpr
  rw [pow_succ]
  have hpos : 0 < (2 : ℕ) ^ (degree * n.size) := by positivity
  omega

theorem symmetric_natAbs {z : ℤ} {P : ℕ} (hz : -(P : ℤ) ≤ z ∧ z ≤ P) : z.natAbs ≤ P := by
  have h : |z| ≤ (P : ℤ) := abs_le.mpr hz
  rw [← Int.natCast_natAbs] at h
  exact_mod_cast h

theorem polynomial_product_binary (n degree W : ℕ) (hW : W ≤ n ^ degree) :
    n * W ≤ 2 ^ exponent n degree := by
  have hn : n ≤ 2 ^ n.size := (Nat.lt_size_self n).le
  calc
    n * W ≤ n * n ^ degree := Nat.mul_le_mul_left n hW
    _ = n ^ (degree + 1) := by rw [pow_succ]; ring
    _ ≤ (2 ^ n.size) ^ (degree + 1) := Nat.pow_le_pow_left hn _
    _ = _ := by rw [← pow_mul]; unfold exponent; congr 1; ring

theorem query_magnitude_binary (n degree W : ℕ) (hW : W ≤ n ^ degree) :
    64 * n * W + 13 < 2 ^ queryWidth n degree := by
  have hp := polynomial_product_binary n degree W hW
  have hpos : 0 < (2 : ℕ) ^ exponent n degree := by positivity
  unfold queryWidth
  rw [pow_add]
  norm_num
  nlinarith

theorem original_sum_magnitude_binary (n degree W : ℕ) (hW : W ≤ n ^ degree) :
    192 * n * W + 40 < 2 ^ sumWidth n degree := by
  have hp := polynomial_product_binary n degree W hW
  have hpos : 0 < (2 : ℕ) ^ exponent n degree := by positivity
  unfold sumWidth
  rw [pow_add]
  norm_num
  nlinarith

def QueryBits {n : ℕ} (q : APSPAlgorithm.Query (Fin n)) (bits : ℕ) : Prop :=
  (∀ i k, (q.1 i k).natAbs.size ≤ bits) ∧
  (∀ k j, (q.2.1 k j).natAbs.size ≤ bits) ∧
  (∀ i j, (q.2.2 i j).natAbs.size ≤ bits)

theorem symmetric_query_bits {n : ℕ} (q : APSPAlgorithm.Query (Fin n)) (P bits : ℕ)
    (hq : APSPAlgorithm.SymmetricQueryBound q (P : ℤ)) (hP : P < 2 ^ bits) : QueryBits q bits := by
  refine ⟨?_, ?_, ?_⟩
  · intro i k
    exact Nat.size_le.mpr ((symmetric_natAbs (hq.1 i k)).trans_lt hP)
  · intro k j
    exact Nat.size_le.mpr ((symmetric_natAbs (hq.2.1 k j)).trans_lt hP)
  · intro i j
    exact Nat.size_le.mpr ((symmetric_natAbs (hq.2.2 i j)).trans_lt hP)

theorem apsp_call_query_bits {n : ℕ} {Payload : Type} (O : DenseOracle n Payload)
    (hO : DenseOracleCorrect O) (w : OptionalTable n) (W degree : ℕ)
    (hw : APSPReduction.EdgeBound (decode w) W) (hW : W ≤ n ^ degree)
    (c : Call n Payload) (hc : c ∈ (apsp O w W).calls) : QueryBits c.query (queryWidth n degree) :=
  symmetric_query_bits c.query _ _ (apsp_query_bound O hO w W hw c hc)
    (query_magnitude_binary n degree W hW)

/-- Concrete stored callback operands, including the signed target. -/
theorem apsp_call_components_size {n : ℕ} {Payload : Type} (O : DenseOracle n Payload)
    (hO : DenseOracleCorrect O) (w : OptionalTable n) (W degree : ℕ)
    (hw : APSPReduction.EdgeBound (decode w) W) (hW : W ≤ n ^ degree)
    (c : Call n Payload) (hc : c ∈ (apsp O w W).calls) :
    (∀ i k, (decode c.left i k).natAbs.size ≤ (degree + 1) * n.size + 7) ∧
      (∀ k j, (decode c.right k j).natAbs.size ≤ (degree + 1) * n.size + 7) ∧
      (∀ i j, (decode c.target i j).natAbs.size ≤ (degree + 1) * n.size + 7) := by
  simpa only [QueryBits, Call.query, queryWidth, exponent] using
    apsp_call_query_bits O hO w W degree hw hW c hc

/-- Original signed-window sums acquire only one additional magnitude bit. -/
theorem apsp_call_original_sum_size {n : ℕ} {Payload : Type} (O : DenseOracle n Payload)
    (hO : DenseOracleCorrect O) (w : OptionalTable n) (W degree : ℕ)
    (hw : APSPReduction.EdgeBound (decode w) W) (hW : W ≤ n ^ degree)
    (c : Call n Payload) (hc : c ∈ (apsp O w W).calls)
    (i j k : Fin n) (r : ℤ) (hr : -1 ≤ r ∧ r ≤ 1) :
    (decode c.left i k + decode c.right k j + decode c.target i j - r).natAbs.size ≤
      (degree + 1) * n.size + 8 := by
  apply Nat.size_le.mpr
  exact (apsp_original_sum_bound O hO w W hw c hc i j k r hr).trans_lt
    (original_sum_magnitude_binary n degree W hW)

theorem globalBound_size (n degree W : ℕ) (hW : W ≤ n ^ degree) :
    (APSPAlgorithm.globalBound n W).size ≤ exponent n degree + 2 := by
  apply Nat.size_le.mpr
  have hp := polynomial_product_binary n degree W hW
  have hpos : 0 < (2 : ℕ) ^ exponent n degree := by positivity
  unfold APSPAlgorithm.globalBound
  rw [pow_add]
  norm_num
  nlinarith

theorem sentinel_size (n degree W : ℕ) (hW : W ≤ n ^ degree) :
    (APSPAlgorithm.sentinel (APSPAlgorithm.globalBound n W)).size ≤ exponent n degree + 4 := by
  apply Nat.size_le.mpr
  have hp := polynomial_product_binary n degree W hW
  have hpos : 0 < (2 : ℕ) ^ exponent n degree := by positivity
  unfold APSPAlgorithm.sentinel APSPAlgorithm.globalBound
  rw [pow_add]
  norm_num
  nlinarith

theorem bit_depth_bound (n degree W : ℕ) (hW : W ≤ n ^ degree) :
    MinPlusReduction.signedLevels (APSPAlgorithm.sentinel (APSPAlgorithm.globalBound n W)) ≤
      exponent n degree + 5 := by
  have hp := polynomial_product_binary n degree W hW
  have hpos : 0 < (2 : ℕ) ^ exponent n degree := by positivity
  have ht : 2 * APSPAlgorithm.sentinel (APSPAlgorithm.globalBound n W) <
      2 ^ (exponent n degree + 5) := by
    unfold APSPAlgorithm.sentinel APSPAlgorithm.globalBound
    rw [pow_add]
    norm_num
    nlinarith
  have hnz : 2 * APSPAlgorithm.sentinel (APSPAlgorithm.globalBound n W) ≠ 0 := by
    unfold APSPAlgorithm.sentinel
    omega
  have hl := (Nat.log2_lt hnz).mpr ht
  unfold MinPlusReduction.signedLevels
  omega

theorem rounds_bound (n : ℕ) : APSPReduction.rounds n ≤ n.size + 1 := by
  unfold APSPReduction.rounds
  by_cases hn : n = 0
  · simp [hn]
  · have hl := (Nat.log2_lt hn).mpr (Nat.lt_size_self n)
    omega

theorem apsp_calls_size_bound {n : ℕ} {Payload : Type} (O : DenseOracle n Payload)
    (w : OptionalTable n) (W degree : ℕ) (hW : W ≤ n ^ degree) :
    (apsp O w W).calls.length ≤ 2 * (n.size + 1) * (exponent n degree + 5) := by
  rw [apsp_calls]
  have hr := rounds_bound n
  have hd := bit_depth_bound n degree W hW
  have h := Nat.mul_le_mul hr (Nat.mul_le_mul_left 2 hd)
  nlinarith

theorem apsp_formation_size_bound {n : ℕ} {Payload : Type} (O : DenseOracle n Payload)
    (w : OptionalTable n) (W degree : ℕ) (hW : W ≤ n ^ degree) :
    (apsp O w W).formationWrites ≤
      (1 + (n.size + 1) * (5 * (exponent n degree + 5) + 7)) * n ^ 2 := by
  rw [apsp_formationWrites]
  have hr := rounds_bound n
  have hd := bit_depth_bound n degree W hW
  apply Nat.mul_le_mul_right
  exact Nat.add_le_add_left (Nat.mul_le_mul hr (by omega)) _

/-- Every actual oracle operand fits the common linear bit budget. -/
theorem apsp_call_budget {n : ℕ} {Payload : Type} (O : DenseOracle n Payload)
    (hO : DenseOracleCorrect O) (w : OptionalTable n) (W degree : ℕ)
    (hw : APSPReduction.EdgeBound (decode w) W) (hW : W ≤ n ^ degree)
    (c : Call n Payload) (hc : c ∈ (apsp O w W).calls) :
    QueryBits c.query (budget n degree) := by
  have h := apsp_call_query_bits O hO w W degree hw hW c hc
  have hb := (budget_bounds n degree).2
  unfold QueryBits at h ⊢
  unfold queryWidth at h
  exact ⟨fun i k => (h.1 i k).trans (by omega),
    fun k j => (h.2.1 k j).trans (by omega),
    fun i j => (h.2.2 i j).trans (by omega)⟩

theorem apsp_calls_budget {n : ℕ} {Payload : Type} (O : DenseOracle n Payload)
    (w : OptionalTable n) (W degree : ℕ) (hW : W ≤ n ^ degree) :
    (apsp O w W).calls.length ≤ 2 * (budget n degree) ^ 2 := by
  have hb := budget_bounds n degree
  calc
    _ ≤ 2 * (n.size + 1) * (exponent n degree + 5) :=
      apsp_calls_size_bound O w W degree hW
    _ ≤ 2 * budget n degree * budget n degree :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ hb.1) (by omega)
    _ = _ := by ring

theorem apsp_formation_budget {n : ℕ} {Payload : Type} (O : DenseOracle n Payload)
    (w : OptionalTable n) (W degree : ℕ) (hW : W ≤ n ^ degree) :
    (apsp O w W).formationWrites ≤ 13 * (budget n degree) ^ 2 * n ^ 2 := by
  have hb := budget_bounds n degree
  have hpos : 1 ≤ budget n degree := by unfold budget; omega
  have hmul : (n.size + 1) * (5 * (exponent n degree + 5) + 7) ≤
      budget n degree * (5 * budget n degree + 7) :=
    Nat.mul_le_mul hb.1 (by omega)
  calc
    _ ≤ (1 + (n.size + 1) * (5 * (exponent n degree + 5) + 7)) * n ^ 2 :=
      apsp_formation_size_bound O w W degree hW
    _ ≤ 13 * (budget n degree) ^ 2 * n ^ 2 :=
      Nat.mul_le_mul_right _ (by nlinarith)

#print axioms apsp_call_components_size
#print axioms apsp_call_original_sum_size
#print axioms sentinel_size
#print axioms bit_depth_bound
#print axioms apsp_calls_size_bound
#print axioms apsp_formation_size_bound
#print axioms apsp_call_budget
#print axioms apsp_calls_budget
#print axioms apsp_formation_budget

end ThinMatrix.AdaptiveQueryBitBounds
