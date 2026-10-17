import Mathlib

/-!
Finite tiling and shared band storage for one genuine integer matrix product.

The two input matrices are padded and split by quotient/remainder. Encoder
vectors are formed once per row or column band; the grid of tiles reads these
vectors. Costs of encoder and tile primitives remain explicit parameters.
In particular no independent-product batching or cache-size estimate is assumed.
-/

namespace ThinMatrix.TilingCosts

open scoped BigOperators

def bandCount (N B : ℕ) : ℕ := N ⌈/⌉ B
def paddedSize (N B : ℕ) : ℕ := bandCount N B * B
def fullGridWidth (goodCount k : ℕ) : ℕ := goodCount * 4 ^ k

theorem fullGridWidth_pos (goodCount k : ℕ) (hg : 0 < goodCount) :
    0 < fullGridWidth goodCount k := by
  exact Nat.mul_pos hg (pow_pos (by norm_num) _)

theorem padding_lower (N B : ℕ) (hB : 0 < B) : N ≤ paddedSize N B := by
  have h := le_smul_ceilDiv (b := N) hB
  simpa [paddedSize, bandCount, nsmul_eq_mul, Nat.mul_comm] using h

theorem padding_upper (N B : ℕ) (hB : 0 < B) (hBN : B ≤ N) :
    paddedSize N B ≤ 2 * N := by
  have h := Nat.div_mul_le_self (N + B - 1) B
  simp only [paddedSize, bandCount, Nat.ceilDiv_eq_add_pred_div]
  omega

theorem bandCount_pos (N B : ℕ) (hN : 0 < N) (hB : 0 < B) :
    0 < bandCount N B := by
  have h := padding_lower N B hB
  unfold paddedSize at h
  nlinarith

def flatten {R B : ℕ} (b : Fin R) (r : Fin B) : Fin (R * B) :=
  ⟨b.val * B + r.val, by
    have h := Nat.mul_le_mul_right B (Nat.succ_le_of_lt b.isLt)
    nlinarith [r.isLt]⟩

def splitIndex {R B : ℕ} (hB : 0 < B) (i : Fin (R * B)) : Fin R × Fin B :=
  (⟨i.val / B, (Nat.div_lt_iff_lt_mul hB).mpr i.isLt⟩,
   ⟨i.val % B, Nat.mod_lt _ hB⟩)

theorem flatten_split {R B : ℕ} (hB : 0 < B) (i : Fin (R * B)) :
    flatten (splitIndex hB i).1 (splitIndex hB i).2 = i := by
  apply Fin.ext
  exact Nat.div_add_mod' i.val B

theorem split_flatten {R B : ℕ} (hB : 0 < B) (b : Fin R) (r : Fin B) :
    splitIndex hB (flatten b r) = (b, r) := by
  apply Prod.ext <;> apply Fin.ext
  · change (b.val * B + r.val) / B = b.val
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hB,
      Nat.div_eq_of_lt r.isLt, Nat.zero_add]
  · simp [splitIndex, flatten, Nat.add_mod, Nat.mod_eq_of_lt r.isLt]

def originalIndex {N B : ℕ} (hB : 0 < B) (i : Fin N) : Fin (paddedSize N B) :=
  ⟨i.val, lt_of_lt_of_le i.isLt (padding_lower N B hB)⟩

def locate {N B : ℕ} (hB : 0 < B) (i : Fin N) :
    Fin (bandCount N B) × Fin B :=
  splitIndex hB (originalIndex hB i)

theorem locate_quotient {N B : ℕ} (hB : 0 < B) (i : Fin N) :
    (locate hB i).1.val = i.val / B := rfl

theorem locate_remainder {N B : ℕ} (hB : 0 < B) (i : Fin N) :
    (locate hB i).2.val = i.val % B := rfl

theorem locate_reconstruct {N B : ℕ} (hB : 0 < B) (i : Fin N) :
    flatten (locate hB i).1 (locate hB i).2 = originalIndex hB i :=
  flatten_split hB _

def padLeft {N D B : ℕ} (A : Fin N → Fin D → ℤ) :
    Fin (paddedSize N B) → Fin D → ℤ :=
  fun i d => if hi : i.val < N then A ⟨i.val, hi⟩ d else 0

def padRight {N D B : ℕ} (C : Fin D → Fin N → ℤ) :
    Fin D → Fin (paddedSize N B) → ℤ :=
  fun d j => if hj : j.val < N then C d ⟨j.val, hj⟩ else 0

def rowBand {N D B : ℕ} (A : Fin N → Fin D → ℤ)
    (b : Fin (bandCount N B)) : Fin B → Fin D → ℤ :=
  fun r d => padLeft A (flatten b r) d

def columnBand {N D B : ℕ} (C : Fin D → Fin N → ℤ)
    (b : Fin (bandCount N B)) : Fin D → Fin B → ℤ :=
  fun d r => padRight C d (flatten b r)

theorem rowBand_original {N D B : ℕ} (hB : 0 < B)
    (A : Fin N → Fin D → ℤ) (i : Fin N) (d : Fin D) :
    rowBand A (locate hB i).1 (locate hB i).2 d = A i d := by
  simp only [rowBand, locate_reconstruct, padLeft, originalIndex]
  simp [i.isLt]

theorem columnBand_original {N D B : ℕ} (hB : 0 < B)
    (C : Fin D → Fin N → ℤ) (d : Fin D) (j : Fin N) :
    columnBand C (locate hB j).1 d (locate hB j).2 = C d j := by
  simp only [columnBand, locate_reconstruct, padRight, originalIndex]
  simp [j.isLt]

theorem genuine_tile_product {N D B : ℕ} (hB : 0 < B)
    (A : Fin N → Fin D → ℤ) (C : Fin D → Fin N → ℤ) (i j : Fin N) :
    (∑ d : Fin D, rowBand A (locate hB i).1 (locate hB i).2 d *
      columnBand C (locate hB j).1 d (locate hB j).2) =
      ∑ d : Fin D, A i d * C d j := by
  apply Finset.sum_congr rfl
  intro d _
  rw [rowBand_original, columnBand_original]

/-- Concrete vectors store the encoder outputs before the tile grid is built. -/
structure SharedStorage (EL ER T : Type*) (R : ℕ) where
  left : List.Vector EL R
  right : List.Vector ER R
  tiles : List.Vector (List.Vector T R) R

def buildShared {EL ER T : Type*} {N D B : ℕ}
    (leftEncode : (Fin B → Fin D → ℤ) → EL)
    (rightEncode : (Fin D → Fin B → ℤ) → ER)
    (tileDP : EL → ER → T)
    (A : Fin N → Fin D → ℤ) (C : Fin D → Fin N → ℤ) :
    SharedStorage EL ER T (bandCount N B) :=
  let left := List.Vector.ofFn (fun b => leftEncode (rowBand A b))
  let right := List.Vector.ofFn (fun b => rightEncode (columnBand C b))
  ⟨left, right, List.Vector.ofFn (fun b => List.Vector.ofFn
    (fun c => tileDP (left.get b) (right.get c)))⟩

theorem buildShared_tile {EL ER T : Type*} {N D B : ℕ}
    (leftEncode : (Fin B → Fin D → ℤ) → EL)
    (rightEncode : (Fin D → Fin B → ℤ) → ER) (tileDP : EL → ER → T)
    (A : Fin N → Fin D → ℤ) (C : Fin D → Fin N → ℤ)
    (b c : Fin (bandCount N B)) :
    ((buildShared leftEncode rightEncode tileDP A C).tiles.get b).get c =
      tileDP ((buildShared leftEncode rightEncode tileDP A C).left.get b)
        ((buildShared leftEncode rightEncode tileDP A C).right.get c) := by
  simp [buildShared]

theorem locate_injective {N B : ℕ} (hB : 0 < B) :
    Function.Injective (@locate N B hB) := by
  intro i j h
  have hf := congrArg (fun p => (flatten p.1 p.2).val) h
  apply Fin.ext
  simpa only [locate_reconstruct, originalIndex] using hf

/-- A request already contains its unique folded outer position and coefficient. -/
structure Request (N q : ℕ) where
  row : Fin N
  column : Fin N
  coefficient : Fin q

def requestTile {N B q : ℕ} (hB : 0 < B) (r : Request N q) :
    Fin (bandCount N B) × Fin (bandCount N B) :=
  ((locate hB r.row).1, (locate hB r.column).1)

def requestLocal {N B q : ℕ} (hB : 0 < B) (r : Request N q) : Fin B × Fin B :=
  ((locate hB r.row).2, (locate hB r.column).2)

/-- Residual evaluation returns one coefficient; each box read uses that same coefficient. -/
def answer {EL ER T : Type*} {N B q reads : ℕ} (hB : 0 < B)
    (storage : SharedStorage EL ER T (bandCount N B))
    (residual : EL → ER → Fin B → Fin B → Fin q → ℤ)
    (storedRead : T → Fin B → Fin B → Fin reads → Fin q → ℤ)
    (r : Request N q) : ℤ :=
  let tile := requestTile hB r
  let position := requestLocal hB r
  residual (storage.left.get tile.1) (storage.right.get tile.2)
      position.1 position.2 r.coefficient +
    ∑ box : Fin reads, storedRead ((storage.tiles.get tile.1).get tile.2)
      position.1 position.2 box r.coefficient

def readLocations {N B q reads : ℕ} (hB : 0 < B) (r : Request N q) :
    List ((Fin (bandCount N B) × Fin (bandCount N B)) ×
      (Fin B × Fin B) × Fin reads × Fin q) :=
  List.ofFn (fun box : Fin reads =>
    (requestTile hB r, requestLocal hB r, box, r.coefficient))

theorem readLocations_length {N B q reads : ℕ} (hB : 0 < B) (r : Request N q) :
    (@readLocations N B q reads hB r).length = reads := by
  simp [readLocations]

theorem readLocations_same_position {N B q reads : ℕ} (hB : 0 < B)
    (r : Request N q) (x) (hx : x ∈ @readLocations N B q reads hB r) :
    x.1 = requestTile hB r ∧ x.2.1 = requestLocal hB r ∧
      x.2.2.2 = r.coefficient := by
  simp only [readLocations, List.mem_ofFn] at hx
  obtain ⟨box, rfl⟩ := hx
  exact ⟨rfl, rfl, rfl⟩

/-- All loops are over bands or genuine requests. No coefficient loop occurs in a query. -/
structure LoopCosts (R Q reads : ℕ) where
  leftEncoder : Fin R → ℕ
  rightEncoder : Fin R → ℕ
  tileDP : Fin R → Fin R → ℕ
  residual : Fin Q → ℕ
  storedRead : Fin Q → Fin reads → ℕ

def loopLedger {R Q reads : ℕ} (cost : LoopCosts R Q reads) : ℕ :=
  (∑ b, cost.leftEncoder b) + (∑ b, cost.rightEncoder b) +
  (∑ b, ∑ c, cost.tileDP b c) +
  (∑ request, cost.residual request) +
  (∑ request, ∑ box, cost.storedRead request box)

/-- The instruction names of the concrete nested loops. -/
inductive Event (R Q reads : ℕ)
  | leftEncoder (band : Fin R)
  | rightEncoder (band : Fin R)
  | tileDP (rowBand columnBand : Fin R)
  | residual (request : Fin Q)
  | storedRead (request : Fin Q) (box : Fin reads)
  deriving DecidableEq

def programSchedule (R Q reads : ℕ) : List (Event R Q reads) :=
  List.ofFn Event.leftEncoder ++ List.ofFn Event.rightEncoder ++
    (List.ofFn (fun b : Fin R => List.ofFn (fun c : Fin R => Event.tileDP b c))).flatten ++
    List.ofFn Event.residual ++
    (List.ofFn (fun r : Fin Q => List.ofFn (fun b : Fin reads => Event.storedRead r b))).flatten

def eventCost {R Q reads : ℕ} (cost : LoopCosts R Q reads) : Event R Q reads → ℕ
  | .leftEncoder b => cost.leftEncoder b
  | .rightEncoder b => cost.rightEncoder b
  | .tileDP b c => cost.tileDP b c
  | .residual r => cost.residual r
  | .storedRead r b => cost.storedRead r b

def executionCost {R Q reads : ℕ} (cost : LoopCosts R Q reads) : ℕ :=
  ((programSchedule R Q reads).map (eventCost cost)).sum

theorem executionCost_eq {R Q reads : ℕ} (cost : LoopCosts R Q reads) :
    executionCost cost = loopLedger cost := by
  simp [executionCost, programSchedule, loopLedger, eventCost, List.sum_ofFn,
    List.map_flatten, List.sum_flatten, Function.comp_def, add_assoc]

/-- Evaluation uses the completed encoder vectors for every tile and every request. -/
def runShared {EL ER T : Type*} {N D B q reads Q : ℕ} (hB : 0 < B)
    (leftEncode : (Fin B → Fin D → ℤ) → EL)
    (rightEncode : (Fin D → Fin B → ℤ) → ER) (tileDP : EL → ER → T)
    (residual : EL → ER → Fin B → Fin B → Fin q → ℤ)
    (storedRead : T → Fin B → Fin B → Fin reads → Fin q → ℤ)
    (A : Fin N → Fin D → ℤ) (C : Fin D → Fin N → ℤ)
    (requests : Fin Q → Request N q) :
    SharedStorage EL ER T (bandCount N B) × List.Vector ℤ Q ×
      List (Event (bandCount N B) Q reads) :=
  let storage := buildShared leftEncode rightEncode tileDP A C
  (storage, List.Vector.ofFn (fun r => answer hB storage residual storedRead (requests r)),
    programSchedule (bandCount N B) Q reads)

theorem runShared_answer {EL ER T : Type*} {N D B q reads Q : ℕ} (hB : 0 < B)
    (leftEncode : (Fin B → Fin D → ℤ) → EL)
    (rightEncode : (Fin D → Fin B → ℤ) → ER) (tileDP : EL → ER → T)
    (residual : EL → ER → Fin B → Fin B → Fin q → ℤ)
    (storedRead : T → Fin B → Fin B → Fin reads → Fin q → ℤ)
    (A : Fin N → Fin D → ℤ) (C : Fin D → Fin N → ℤ)
    (requests : Fin Q → Request N q) (r : Fin Q) :
    ((runShared hB leftEncode rightEncode tileDP residual storedRead A C requests).2.1).get r =
      answer hB (buildShared leftEncode rightEncode tileDP A C)
        residual storedRead (requests r) := by
  simp [runShared]

theorem runShared_cost {EL ER T : Type*} {N D B q reads Q : ℕ} (hB : 0 < B)
    (leftEncode : (Fin B → Fin D → ℤ) → EL)
    (rightEncode : (Fin D → Fin B → ℤ) → ER) (tileDP : EL → ER → T)
    (residual : EL → ER → Fin B → Fin B → Fin q → ℤ)
    (storedRead : T → Fin B → Fin B → Fin reads → Fin q → ℤ)
    (A : Fin N → Fin D → ℤ) (C : Fin D → Fin N → ℤ)
    (requests : Fin Q → Request N q) (cost : LoopCosts (bandCount N B) Q reads) :
    (((runShared hB leftEncode rightEncode tileDP residual storedRead A C requests).2.2).map
      (eventCost cost)).sum = loopLedger cost := by
  change executionCost cost = loopLedger cost
  exact executionCost_eq cost

def encoderCount (R : ℕ) : ℕ := (∑ _ : Fin R, 1) + (∑ _ : Fin R, 1)
def tileCount (R : ℕ) : ℕ := ∑ _ : Fin R, ∑ _ : Fin R, 1
def storedReadCount (Q reads : ℕ) : ℕ := ∑ _ : Fin Q, ∑ _ : Fin reads, 1

theorem encoderCount_eq (R : ℕ) : encoderCount R = 2 * R := by simp [encoderCount]; omega
theorem tileCount_eq (R : ℕ) : tileCount R = R ^ 2 := by simp [tileCount, pow_two]
theorem storedReadCount_eq (Q reads : ℕ) : storedReadCount Q reads = Q * reads := by
  simp [storedReadCount]

theorem actual_encoder_count (R Q reads : ℕ) :
    executionCost (⟨fun _ => 1, fun _ => 1, fun _ _ => 0,
      fun _ => 0, fun _ _ => 0⟩ : LoopCosts R Q reads) = 2 * R := by
  rw [executionCost_eq]
  simp [loopLedger]
  omega

theorem actual_tile_count (R Q reads : ℕ) :
    executionCost (⟨fun _ => 0, fun _ => 0, fun _ _ => 1,
      fun _ => 0, fun _ _ => 0⟩ : LoopCosts R Q reads) = R ^ 2 := by
  rw [executionCost_eq]
  simp [loopLedger, pow_two]

theorem actual_query_count (R Q reads : ℕ) :
    executionCost (⟨fun _ => 0, fun _ => 0, fun _ _ => 0,
      fun _ => 1, fun _ _ => 0⟩ : LoopCosts R Q reads) = Q := by
  rw [executionCost_eq]
  simp [loopLedger]

theorem actual_storedRead_count (R Q reads : ℕ) :
    executionCost (⟨fun _ => 0, fun _ => 0, fun _ _ => 0,
      fun _ => 0, fun _ _ => 1⟩ : LoopCosts R Q reads) = Q * reads := by
  rw [executionCost_eq]
  simp [loopLedger]

def uniformLedger (R Q reads encCost boxCost residualCost readCost : ℕ) : ℕ :=
  2 * R * encCost + R ^ 2 * boxCost + Q * (residualCost + reads * readCost)

theorem loopLedger_le {R Q reads : ℕ} (cost : LoopCosts R Q reads)
    (encCost boxCost residualCost readCost : ℕ)
    (hL : ∀ b, cost.leftEncoder b ≤ encCost)
    (hR : ∀ b, cost.rightEncoder b ≤ encCost)
    (hT : ∀ b c, cost.tileDP b c ≤ boxCost)
    (hQ : ∀ r, cost.residual r ≤ residualCost)
    (hS : ∀ r b, cost.storedRead r b ≤ readCost) :
    loopLedger cost ≤ uniformLedger R Q reads encCost boxCost residualCost readCost := by
  have hl := Finset.sum_le_sum (fun b (_ : b ∈ Finset.univ) => hL b)
  have hr := Finset.sum_le_sum (fun b (_ : b ∈ Finset.univ) => hR b)
  have ht := Finset.sum_le_sum (fun b (_ : b ∈ Finset.univ) =>
    Finset.sum_le_sum (fun c (_ : c ∈ Finset.univ) => hT b c))
  have hq := Finset.sum_le_sum (fun r (_ : r ∈ Finset.univ) => hQ r)
  have hs := Finset.sum_le_sum (fun r (_ : r ∈ Finset.univ) =>
    Finset.sum_le_sum (fun b (_ : b ∈ Finset.univ) => hS r b))
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hl hr ht hq hs
  unfold loopLedger uniformLedger
  nlinarith

theorem executionCost_le {R Q reads : ℕ} (cost : LoopCosts R Q reads)
    (encCost boxCost residualCost readCost : ℕ)
    (hL : ∀ b, cost.leftEncoder b ≤ encCost)
    (hR : ∀ b, cost.rightEncoder b ≤ encCost)
    (hT : ∀ b c, cost.tileDP b c ≤ boxCost)
    (hQ : ∀ r, cost.residual r ≤ residualCost)
    (hS : ∀ r b, cost.storedRead r b ≤ readCost) :
    executionCost cost ≤ uniformLedger R Q reads encCost boxCost residualCost readCost := by
  rw [executionCost_eq]
  exact loopLedger_le cost _ _ _ _ hL hR hT hQ hS

/-- Concrete retained cyclic arrays, indexed by the actual number of leaves. -/
abbrev CyclicEncodedBand (S q : ℕ) := List.Vector (List.Vector ℤ q) S

abbrev LeafCyclicEncodedBand (Leaf : Type*) [Fintype Leaf] (q : ℕ) :=
  CyclicEncodedBand (Fintype.card Leaf) q

theorem cyclic_entry_count (S q : ℕ) :
    Fintype.card (Fin S × Fin q) = S * q := by simp

theorem actual_leaf_entry_count (Leaf : Type*) [Fintype Leaf] (q : ℕ) :
    Fintype.card (Leaf × Fin q) = Fintype.card Leaf * q := by simp

/-- Encoder charges include their source formation and all internal arrays.
Complete cyclic vectors are charged with the actual leaf count `S`; no bound on `S`
is used in this module. -/
def cyclicEncoderCost (polyL S q : ℕ) : ℕ := polyL * S * q
def cyclicBoxCost (boxUnits q : ℕ) : ℕ := boxUnits * q

theorem cyclic_loopLedger_le {R Q reads : ℕ} (cost : LoopCosts R Q reads)
    (polyL S q boxUnits residualCost readCost : ℕ)
    (hL : ∀ b, cost.leftEncoder b ≤ cyclicEncoderCost polyL S q)
    (hR : ∀ b, cost.rightEncoder b ≤ cyclicEncoderCost polyL S q)
    (hT : ∀ b c, cost.tileDP b c ≤ cyclicBoxCost boxUnits q)
    (hQ : ∀ r, cost.residual r ≤ residualCost)
    (hS : ∀ r b, cost.storedRead r b ≤ readCost) :
    loopLedger cost ≤ 2 * R * (polyL * S * q) + R ^ 2 * (boxUnits * q) +
      Q * (residualCost + reads * readCost) :=
  loopLedger_le cost _ _ _ _ hL hR hT hQ hS

theorem bandCount_real_bound (N B : ℕ) (hB : 0 < B) (hBN : B ≤ N) :
    (bandCount N B : ℝ) ≤ 2 * (N : ℝ) / (B : ℝ) := by
  apply (le_div_iff₀ (by exact_mod_cast hB)).2
  exact_mod_cast padding_upper N B hB hBN

theorem padded_ratio (N B : ℕ) (hB : 0 < B) :
    (paddedSize N B : ℝ) / (B : ℝ) = bandCount N B := by
  have hb : (B : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hB
  simp [paddedSize, Nat.cast_mul, hb]

/-- Exact ledger in terms of the padded dimension. -/
theorem padded_ledger (N B Q reads encCost boxCost residualCost readCost : ℕ)
    (hB : 0 < B) :
    (uniformLedger (bandCount N B) Q reads encCost boxCost residualCost readCost : ℝ) =
      (2 * (paddedSize N B : ℝ) / B) * encCost +
      ((paddedSize N B : ℝ) / B) ^ 2 * boxCost +
      Q * (residualCost + reads * readCost) := by
  rw [mul_div_assoc, padded_ratio N B hB]
  simp [uniformLedger]

/-- Ceiling factors are explicit when expressed using the original dimension. -/
theorem original_ledger_bound (N B Q reads encCost boxCost residualCost readCost : ℕ)
    (hB : 0 < B) (hBN : B ≤ N) :
    (uniformLedger (bandCount N B) Q reads encCost boxCost residualCost readCost : ℝ) ≤
      (4 * (N : ℝ) / B) * encCost +
      4 * ((N : ℝ) / B) ^ 2 * boxCost +
      Q * (residualCost + reads * readCost) := by
  have hr := bandCount_real_bound N B hB hBN
  rw [mul_div_assoc] at hr
  have hn : 0 ≤ (N : ℝ) / B := by positivity
  have hsq : (bandCount N B : ℝ) ^ 2 ≤ 4 * ((N : ℝ) / B) ^ 2 := by
    have hb : 0 ≤ (bandCount N B : ℝ) := Nat.cast_nonneg _
    nlinarith
  have he := mul_le_mul_of_nonneg_right hr (Nat.cast_nonneg encCost : (0 : ℝ) ≤ encCost)
  have ht := mul_le_mul_of_nonneg_right hsq (Nat.cast_nonneg boxCost : (0 : ℝ) ≤ boxCost)
  simp only [uniformLedger, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]
  simp only [mul_div_assoc]
  nlinarith

theorem fullyChargedPadded {N B Q reads : ℕ}
    (cost : LoopCosts (bandCount N B) Q reads)
    (encCost boxCost residualCost readCost : ℕ) (hB : 0 < B)
    (hL : ∀ b, cost.leftEncoder b ≤ encCost)
    (hR : ∀ b, cost.rightEncoder b ≤ encCost)
    (hT : ∀ b c, cost.tileDP b c ≤ boxCost)
    (hQ : ∀ r, cost.residual r ≤ residualCost)
    (hS : ∀ r b, cost.storedRead r b ≤ readCost) :
    (executionCost cost : ℝ) ≤
      (2 * (paddedSize N B : ℝ) / B) * encCost +
      ((paddedSize N B : ℝ) / B) ^ 2 * boxCost +
      Q * (residualCost + reads * readCost) := by
  rw [← padded_ledger N B Q reads encCost boxCost residualCost readCost hB]
  exact_mod_cast executionCost_le cost _ _ _ _ hL hR hT hQ hS

theorem fullyChargedOriginal {N B Q reads : ℕ}
    (cost : LoopCosts (bandCount N B) Q reads)
    (encCost boxCost residualCost readCost : ℕ) (hB : 0 < B) (hBN : B ≤ N)
    (hL : ∀ b, cost.leftEncoder b ≤ encCost)
    (hR : ∀ b, cost.rightEncoder b ≤ encCost)
    (hT : ∀ b c, cost.tileDP b c ≤ boxCost)
    (hQ : ∀ r, cost.residual r ≤ residualCost)
    (hS : ∀ r b, cost.storedRead r b ≤ readCost) :
    (executionCost cost : ℝ) ≤
      (4 * (N : ℝ) / B) * encCost + 4 * ((N : ℝ) / B) ^ 2 * boxCost +
      Q * (residualCost + reads * readCost) := by
  have hc : (executionCost cost : ℝ) ≤
      uniformLedger (bandCount N B) Q reads encCost boxCost residualCost readCost := by
    exact_mod_cast executionCost_le cost _ _ _ _ hL hR hT hQ hS
  exact hc.trans (original_ledger_bound _ _ _ _ _ _ _ _ hB hBN)

/-- Actual finite leaf cardinality is substituted without an entropy estimate. -/
theorem cyclicFullyCharged {Leaf : Type*} [Fintype Leaf] {N B Q reads : ℕ}
    (cost : LoopCosts (bandCount N B) Q reads)
    (polyL q boxUnits residualCost readCost : ℕ) (hB : 0 < B) (hBN : B ≤ N)
    (hL : ∀ b, cost.leftEncoder b ≤ polyL * Fintype.card Leaf * q)
    (hR : ∀ b, cost.rightEncoder b ≤ polyL * Fintype.card Leaf * q)
    (hT : ∀ b c, cost.tileDP b c ≤ boxUnits * q)
    (hQ : ∀ r, cost.residual r ≤ residualCost)
    (hS : ∀ r b, cost.storedRead r b ≤ readCost) :
    (executionCost cost : ℝ) ≤
      (4 * (N : ℝ) / B) * (polyL * Fintype.card Leaf * q : ℕ) +
      4 * ((N : ℝ) / B) ^ 2 * (boxUnits * q : ℕ) +
      Q * (residualCost + reads * readCost) :=
  fullyChargedOriginal cost _ _ _ _ hB hBN hL hR hT hQ hS

/-- The geometric band width is the full good-slot grid, rather than an encoder count. -/
theorem fullGrid_padding (N goodCount k : ℕ) (hg : 0 < goodCount)
    (hgeometry : fullGridWidth goodCount k ≤ N) :
    N ≤ paddedSize N (fullGridWidth goodCount k) ∧
      paddedSize N (fullGridWidth goodCount k) ≤ 2 * N :=
  ⟨padding_lower _ _ (fullGridWidth_pos _ _ hg),
   padding_upper _ _ (fullGridWidth_pos _ _ hg) hgeometry⟩

def slotWithinBand {goodCount k : ℕ} (r : Fin (fullGridWidth goodCount k)) :
    Fin goodCount × Fin (4 ^ k) :=
  splitIndex (by positivity) r

theorem slotWithinBand_reconstruct {goodCount k : ℕ}
    (r : Fin (fullGridWidth goodCount k)) :
    flatten (slotWithinBand r).1 (slotWithinBand r).2 = r :=
  flatten_split _ _

end ThinMatrix.TilingCosts

#print axioms ThinMatrix.TilingCosts.padding_upper
#print axioms ThinMatrix.TilingCosts.genuine_tile_product
#print axioms ThinMatrix.TilingCosts.buildShared_tile
#print axioms ThinMatrix.TilingCosts.executionCost_eq
#print axioms ThinMatrix.TilingCosts.runShared_cost
#print axioms ThinMatrix.TilingCosts.actual_encoder_count
#print axioms ThinMatrix.TilingCosts.actual_tile_count
#print axioms ThinMatrix.TilingCosts.actual_query_count
#print axioms ThinMatrix.TilingCosts.actual_storedRead_count
#print axioms ThinMatrix.TilingCosts.readLocations_same_position
#print axioms ThinMatrix.TilingCosts.fullyChargedPadded
#print axioms ThinMatrix.TilingCosts.cyclicFullyCharged
#print axioms ThinMatrix.TilingCosts.fullGrid_padding
