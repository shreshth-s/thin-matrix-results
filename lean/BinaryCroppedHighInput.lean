import BinaryHighCost
import BinaryModularCell
import CroppedSourceContraction

set_option autoImplicit false

/-! Cropping is executed before the shared HIGH encoder. The rare-letter
count and cap comparison consume retained binary cells; the cap is serialized
once for the complete root. Rejected cells still allocate their full zero
coefficient vectors. Counters use the repository's binary-arithmetic plus
bounded indexed-array/control model, not Lean evaluator or machine time. -/
namespace ThinMatrix.BinaryCroppedHighInput
open BinaryCell WalshEmbedding BinaryHighExecution
open SharedEncoder (Coordinates read volume)
open scoped BigOperators

def countBits : List Bool → Result Cell
  | [] => ⟨zero,1⟩
  | b::bs =>
      let rest := countBits bs
      if b then
        let out := add BinaryModularCell.one rest.value
        ⟨out.value,rest.bitSteps+out.bitSteps+4⟩
      else ⟨rest.value,rest.bitSteps+4⟩

def bitCount (bs : List Bool) : ℕ := (bs.map (fun b => if b then 1 else 0)).sum

theorem countBits_view (bs : List Bool) : view (countBits bs).value = (bitCount bs : ℤ) := by
  induction bs with
  | nil => rfl
  | cons b bs ih => cases b <;> simp [countBits,bitCount,ih]

theorem bitCount_le (bs : List Bool) : bitCount bs ≤ bs.length := by
  induction bs with
  | nil => simp [bitCount]
  | cons b bs ih => cases b <;> simp only [bitCount,List.map_cons,List.sum_cons,List.length_cons,Bool.false_eq_true,↓reduceIte] at * <;> omega

theorem countBits_price (bs : List Bool) (N : ℕ) (h : bs.length ≤ N) :
    (countBits bs).bitSteps ≤ bs.length*(BackendScalarBits.backendScalarUnit (N.size+1)+4)+1 := by
  induction bs with
  | nil => simp [countBits]
  | cons b bs ih =>
    have hlen : bs.length ≤ N := by simp only [List.length_cons] at h; omega
    have ht := ih hlen
    have hw : (view (countBits bs).value).natAbs.size ≤ N.size+1 := by
      rw [countBits_view,Int.natAbs_natCast]
      exact (Nat.size_le_size ((bitCount_le bs).trans hlen)).trans (by omega)
    have hc := add_price (N.size+1) BinaryModularCell.one (countBits bs).value (by simp) hw
    cases b <;> simp only [countBits,Bool.false_eq_true,↓reduceIte,List.length_cons] <;> nlinarith

theorem bitCount_ofFn {L : ℕ} (b : Cube L) : bitCount (List.ofFn b) = ones b := by
  simp only [bitCount,List.map_ofFn,List.sum_ofFn,Function.comp_apply,ones,Finset.card_eq_sum_ones,Finset.sum_filter]

def test {L : ℕ} (capCell : Cell) (opposite : Fin L → OppositeLetter) : Result Bool :=
  let count := countBits (List.ofFn (oppositeWBits opposite))
  let out := BinaryModularCell.signedLess capCell count.value
  ⟨!out.value,count.bitSteps+out.bitSteps+8*L+8⟩

theorem test_value {L : ℕ} (cap : ℕ) (capCell : Cell) (hc : view capCell = (cap : ℤ))
    (opposite : Fin L → OppositeLetter) :
    (test capCell opposite).value = decide (ones (oppositeWBits opposite) ≤ cap) := by
  simp only [test,BinaryModularCell.signedLess_view,countBits_view,bitCount_ofFn,hc]
  by_cases h : ones (oppositeWBits opposite) ≤ cap
  · have hn : ¬ (cap : ℤ) < (ones (oppositeWBits opposite) : ℤ) := by omega
    simp [h,hn]
  · have hn : (cap : ℤ) < (ones (oppositeWBits opposite) : ℤ) := by omega
    simp [h,hn]

def testBudget (L cap : ℕ) : ℕ :=
  L*(BackendScalarBits.backendScalarUnit (L.size+1)+4)+1+100000*(cap.size+L.size+2)^3+8*L+8

theorem test_price {L : ℕ} (cap : ℕ) (capCell : Cell) (hc : view capCell = (cap : ℤ))
    (opposite : Fin L → OppositeLetter) : (test capCell opposite).bitSteps ≤ testBudget L cap := by
  have ht := countBits_price (List.ofFn (oppositeWBits opposite)) L (by simp)
  have hs := BinaryModularCell.signedLess_price (cap.size+L.size+1) capCell
    (countBits (List.ofFn (oppositeWBits opposite))).value
    (by rw [hc,Int.natAbs_natCast]; omega)
    (by rw [countBits_view,bitCount_ofFn,Int.natAbs_natCast]; exact (Nat.size_le_size (ones_le _)).trans (by omega))
  simp only [List.length_ofFn] at ht
  rw [show cap.size+L.size+1+1=cap.size+L.size+2 by omega] at hs
  simp only [test,testBudget]
  omega

def payload {L q : ℕ} (b : Bool) (capCell : Cell) (raw : BinarySourceFormation.RawStore L q)
    (a : Coordinates (HighBaseEncoder.rootDims L b)) : Result (Payload q) :=
  let accepted := test capCell (decodeSource b a).2
  let out := if accepted.value then rawPayload b raw a else ⟨BinaryCell.vectorZero q,2*q+1⟩
  ⟨out.value,accepted.bitSteps+out.bitSteps+8*L+8⟩

theorem payload_view {L q : ℕ} (b : Bool) (cap : ℕ) (capCell : Cell) (hc : view capCell = (cap : ℤ))
    (raw : BinarySourceFormation.RawStore L q) (a : Coordinates (HighBaseEncoder.rootDims L b)) (r : Fin q) :
    view ((payload b capCell raw a).value.get r) =
      CroppedSourceContraction.crop cap (fun n o => view (BinarySourceFormation.readRaw raw n o r))
        (decodeSource b a).1 (decodeSource b a).2 := by
  simp only [payload,test_value cap capCell hc]
  by_cases h : ones (oppositeWBits (decodeSource b a).2) ≤ cap
  · simp only [h,decide_true,↓reduceIte,rawPayload_get_view,CroppedSourceContraction.crop]
  · simp [h,CroppedSourceContraction.crop,BinaryCell.vectorZero]

theorem payload_magnitude {L q : ℕ} (b : Bool) (capCell : Cell)
    (raw : BinarySourceFormation.RawStore L q) (A : ℕ) (hA : RawBound raw A)
    (a : Coordinates (HighBaseEncoder.rootDims L b)) (r : Fin q) :
    |view ((payload b capCell raw a).value.get r)| ≤ (A : ℤ) := by
  dsimp only [payload]
  split
  · rw [rawPayload_get_view]; exact hA _ _ _
  · simp [BinaryCell.vectorZero]

def payloadBudget (L q cap A : ℕ) : ℕ :=
  testBudget L cap+q*(BackendScalarBits.backendScalarUnit A.size+2*L+5)+8*L+9

theorem payload_price {L q : ℕ} (b : Bool) (cap : ℕ) (capCell : Cell) (hc : view capCell = (cap : ℤ))
    (raw : BinarySourceFormation.RawStore L q) (A : ℕ) (hA : RawBound raw A)
    (a : Coordinates (HighBaseEncoder.rootDims L b)) :
    (payload b capCell raw a).bitSteps ≤ payloadBudget L q cap A := by
  have ht := test_price cap capCell hc (decodeSource b a).2
  have hr := rawPayload_bit_price b raw A hA a
  simp only [payload,payloadBudget]
  split <;> nlinarith

def input {L q : ℕ} (b : Bool) (cap : ℕ) (raw : BinarySourceFormation.RawStore L q) :
    Result (BinaryDense q (2*L) (HighBaseEncoder.rootDims L b)) :=
  let encodedCap := BinaryMultiplierAdapter.encodeInteger (cap : ℤ)
  let out := materialize (2*L) (HighBaseEncoder.rootDims L b) (payload b encodedCap.value raw)
  ⟨out.value,encodedCap.bitSteps+out.bitSteps+2⟩

theorem input_read {L q : ℕ} (b : Bool) (cap : ℕ) (raw : BinarySourceFormation.RawStore L q)
    (a : Coordinates (HighBaseEncoder.rootDims L b)) (r : Fin q) :
    view ((read (2*L) (HighBaseEncoder.rootDims L b) (input b cap raw).value a).get r) =
      CroppedSourceContraction.crop cap (fun n o => view (BinarySourceFormation.readRaw raw n o r))
        (decodeSource b a).1 (decodeSource b a).2 := by
  simp only [input,BinaryHighExecution.read_materialize_value]
  exact payload_view b cap _ (BinaryMultiplierAdapter.encodeInteger_view _) raw a r

theorem input_magnitude {L q : ℕ} (b : Bool) (cap : ℕ) (raw : BinarySourceFormation.RawStore L q)
    (A : ℕ) (hA : RawBound raw A) : BinaryHighCost.DenseBound (input b cap raw).value A := by
  intro a r
  simp only [input,BinaryHighExecution.read_materialize_value]
  exact payload_magnitude b _ raw A hA a r

def inputBudget (L q cap A : ℕ) (b : Bool) : ℕ :=
  10*(cap.size+1)^2+volume (2*L) (HighBaseEncoder.rootDims L b)*(payloadBudget L q cap A+4*L)+2

theorem input_price {L q : ℕ} (b : Bool) (cap : ℕ) (raw : BinarySourceFormation.RawStore L q)
    (A : ℕ) (hA : RawBound raw A) : (input b cap raw).bitSteps ≤ inputBudget L q cap A b := by
  have he := BinaryMultiplierAdapter.encodeInteger_cost (cap : ℤ)
  simp only [Int.natAbs_natCast] at he
  have hm := materialize_steps_le (2*L) (HighBaseEncoder.rootDims L b)
    (payload b (BinaryMultiplierAdapter.encodeInteger (cap : ℤ)).value raw) (payloadBudget L q cap A)
    (payload_price b cap _ (BinaryMultiplierAdapter.encodeInteger_view _) raw A hA)
    (fun i => (shape_dims_bounds L b 0 (2*L) _ (HighBaseEncoder.root_shape L b) i).1)
  rw [show 2*(2*L)=4*L by omega] at hm
  simp only [input,inputBudget]
  omega

#print axioms countBits_view
#print axioms bitCount_le
#print axioms countBits_price
#print axioms bitCount_ofFn
#print axioms test_value
#print axioms test_price
#print axioms payload_view
#print axioms payload_magnitude
#print axioms payload_price
#print axioms input_read
#print axioms input_magnitude
#print axioms input_price
end ThinMatrix.BinaryCroppedHighInput
