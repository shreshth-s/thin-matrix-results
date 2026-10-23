import HalfSourceStoredKeys

set_option autoImplicit false

/-! Binary character-sum state for the translation generator. Each update
adds a literal signed one to stored bits, then explicitly decodes the result
for the score kernel's small integer index. Both operations are charged.
The row scan and retained-array traversal have indexed control counts;
these are not binary address costs or costs for the selection kernel. -/
namespace ThinMatrix.HalfSourceBinaryState
open WalshEmbedding HalfSourceList BinaryCell BinaryGroupedCoordinates BinaryGroupedPreparation

abbrev Entry := Cell × ℤ

def signedOne (b : Bool) : Cell :=
  if b then ⟨negOneBits,by decide⟩ else ⟨oneBits,by decide⟩

theorem signedOne_view (b : Bool) : view (signedOne b)=sign b := by cases b <;> rfl

def update {m : ℕ} (key : HalfSourceStoredKeys.Key m) (d : Vector Bool m) (old : Entry) : Run Entry :=
  if key.active then
    let dot := HalfSourceMaskWork.dotRun m key.row.get d.get
    let added := add old.1 (signedOne dot.1)
    let decoded := BinaryMultiplierAdapter.decodeInteger added.value
    ⟨(added.value,decoded.value),added.bitSteps+decoded.bitSteps,dot.2+12⟩
  else ⟨(zero,0),0,4⟩

theorem update_cached {m : ℕ} (key : HalfSourceStoredKeys.Key m) (d : Vector Bool m) (old : Entry) :
    (update key d old).value.2=view (update key d old).value.1 := by
  simp only [update]
  split
  · exact BinaryMultiplierAdapter.decodeInteger_value _
  · rfl

theorem update_view {m : ℕ} (key : HalfSourceStoredKeys.Key m) (d : Vector Bool m) (old : Entry) :
    view (update key d old).value.1 =
      if key.active then view old.1+sign (dotBits key.row.get d.get) else 0 := by
  simp only [update]
  split <;> simp [signedOne_view,HalfSourceMaskWork.dotRun_value]

theorem update_abs {m : ℕ} (j : ℕ) (key : HalfSourceStoredKeys.Key m) (d : Vector Bool m)
    (old : Entry) (ho : (view old.1).natAbs≤j) :
    (view (update key d old).value.1).natAbs≤j+1 := by
  rw [update_view]
  split
  · have hs : (sign (dotBits key.row.get d.get)).natAbs=1 := by cases dotBits key.row.get d.get <;> rfl
    exact (Int.natAbs_add_le _ _).trans (by omega)
  · simp

def updateBudget (j : ℕ) : ℕ := BackendScalarBits.backendScalarUnit (j+1).size+10*((j+1).size+1)^2

theorem update_bits {m : ℕ} (j : ℕ) (key : HalfSourceStoredKeys.Key m) (d : Vector Bool m)
    (old : Entry) (ho : (view old.1).natAbs≤j) :
    (update key d old).bitSteps≤updateBudget j := by
  have ha := update_abs j key d old ho
  unfold update
  split
  · rename_i h
    have ho' := Nat.size_le_size (ho.trans (Nat.le_succ j))
    have hs : (view (signedOne (HalfSourceMaskWork.dotRun m key.row.get d.get).1)).natAbs.size≤(j+1).size := by
      rw [signedOne_view]
      apply Nat.size_le_size
      cases (HalfSourceMaskWork.dotRun m key.row.get d.get).1 <;> simp [sign]
    have hp := add_price (j+1).size old.1 _ ho' hs
    have hd := BinaryMultiplierAdapter.decodeInteger_cost (add old.1 (signedOne (HalfSourceMaskWork.dotRun m key.row.get d.get).1)).value
    simp only [update,h,↓reduceIte] at ha
    have hw := Nat.size_le_size ha
    have hh : 10*((view (add old.1 (signedOne (HalfSourceMaskWork.dotRun m key.row.get d.get).1)).value).natAbs.size+1)^2≤10*((j+1).size+1)^2 := by gcongr
    change _≤updateBudget j
    unfold updateBudget
    change _≤10*((view _).natAbs.size+1)^2 at hd
    dsimp only
    omega
  · exact Nat.zero_le _

theorem update_control {m : ℕ} (key : HalfSourceStoredKeys.Key m) (d : Vector Bool m) (old : Entry) :
    (update key d old).control≤6*m+13 := by
  simp only [update]
  split <;> simp only [HalfSourceMaskWork.dotRun_work] <;> omega

def advance {m : ℕ} (keys : Vector (HalfSourceStoredKeys.Key m) (2^m))
    (d : Vector Bool m) (old : Vector Entry (2^m)) : Run (Vector Entry (2^m)) :=
  tabulate keys (fun i => update (keys.get i) d (old.get i))

theorem advance_cached {m : ℕ} (keys : Vector (HalfSourceStoredKeys.Key m) (2^m))
    (d : Vector Bool m) (old : Vector Entry (2^m)) (i : Fin (2^m)) :
    ((advance keys d old).value.get i).2=view ((advance keys d old).value.get i).1 := by
  simp only [advance,tabulate_get,update_cached]

theorem advance_abs {m : ℕ} (j : ℕ) (keys : Vector (HalfSourceStoredKeys.Key m) (2^m))
    (d : Vector Bool m) (old : Vector Entry (2^m)) (ho : ∀ i,(view (old.get i).1).natAbs≤j)
    (i : Fin (2^m)) : (view ((advance keys d old).value.get i).1).natAbs≤j+1 := by
  simp only [advance,tabulate_get]
  exact update_abs j _ _ _ (ho i)

theorem advance_bits {m : ℕ} (j : ℕ) (keys : Vector (HalfSourceStoredKeys.Key m) (2^m))
    (d : Vector Bool m) (old : Vector Entry (2^m)) (ho : ∀ i,(view (old.get i).1).natAbs≤j) :
    (advance keys d old).bitSteps≤2^m*updateBudget j :=
  tabulate_bits _ _ (fun i => update_bits j _ _ _ (ho i))

theorem advance_control {m : ℕ} (keys : Vector (HalfSourceStoredKeys.Key m) (2^m))
    (d : Vector Bool m) (old : Vector Entry (2^m)) :
    (advance keys d old).control≤2^m*(6*m+45)+8 :=
  tabulate_control _ _ (fun _ => update_control _ _ _)

#print axioms signedOne_view
#print axioms update_cached
#print axioms update_view
#print axioms update_abs
#print axioms update_bits
#print axioms update_control
#print axioms advance_cached
#print axioms advance_abs
#print axioms advance_bits
#print axioms advance_control
end ThinMatrix.HalfSourceBinaryState
