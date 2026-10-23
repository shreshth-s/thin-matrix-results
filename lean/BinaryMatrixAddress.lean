import BinaryMatrixSetup

set_option autoImplicit false

/-! Binary product-address arithmetic, including both boundary conversions.
These routines replace the natural multiply/add and quotient/remainder used
by recursive table layouts. They do not price array access or claim a complete
lowering of the matrix evaluator. -/
namespace ThinMatrix.BinaryMatrixAddress
open BinaryCell BinaryModularCell BinaryMultiplierAdapter

/-- A row-major product address. All three public words are serialized,
the arithmetic uses retained cells, and the final address is decoded once. -/
def join (radix high low : ℕ) : Result ℕ :=
  let r := encodeInteger (radix:ℤ)
  let h := encodeInteger (high:ℤ)
  let l := encodeInteger (low:ℤ)
  let product := mul r.value h.value
  let sum := add product.value l.value
  let out := decodeUnsigned sum.value
  ⟨out.value,r.bitSteps+h.bitSteps+l.bitSteps+product.bitSteps+sum.bitSteps+out.bitSteps+8⟩

theorem join_value (radix high low : ℕ) : (join radix high low).value = low+radix*high := by
  simp only [join,decodeUnsigned_value,add_view,mul_view]
  change (((encodeInteger (radix:ℤ)).value.view*(encodeInteger (high:ℤ)).value.view+
    (encodeInteger (low:ℤ)).value.view):ℤ).natAbs=_
  rw [encodeInteger_view,encodeInteger_view,encodeInteger_view,←Nat.cast_mul,←Nat.cast_add,Int.natAbs_natCast]
  omega

theorem join_bits (radix high low W : ℕ)
    (hr : radix.size ≤ W) (hh : high.size ≤ W) (hl : low.size ≤ W) :
    (join radix high low).bitSteps ≤ 4096*(W+1)^2 := by
  let r := (encodeInteger (radix:ℤ)).value
  let h := (encodeInteger (high:ℤ)).value
  let l := (encodeInteger (low:ℤ)).value
  have vr : view r = radix := encodeInteger_view _
  have vh : view h = high := encodeInteger_view _
  have vl : view l = low := encodeInteger_view _
  have wr : (view r).natAbs.size ≤ W := by simpa only [vr,Int.natAbs_natCast] using hr
  have wh : (view h).natAbs.size ≤ W := by simpa only [vh,Int.natAbs_natCast] using hh
  have wl : (view l).natAbs.size ≤ W := by simpa only [vl,Int.natAbs_natCast] using hl
  have er := encodeInteger_cost (radix:ℤ)
  have eh := encodeInteger_cost (high:ℤ)
  have el := encodeInteger_cost (low:ℤ)
  simp only [Int.natAbs_natCast] at er eh el
  have bm := mul_price W r h wr wh
  have wm : (view (mul r h).value).natAbs.size ≤ 2*W := (mul_size r h).trans (by omega)
  have ba := add_price (2*W) (mul r h).value l wm (wl.trans (by omega))
  have wa : (view (add (mul r h).value l).value).natAbs.size ≤ 2*W+1 :=
    (add_size _ _).trans (by omega)
  have bd := decodeUnsigned_price (2*W+1) (add (mul r h).value l).value wa
  have er' := er.trans (Nat.mul_le_mul_left 10 (Nat.pow_le_pow_left (Nat.add_le_add_right hr 1) 2))
  have eh' := eh.trans (Nat.mul_le_mul_left 10 (Nat.pow_le_pow_left (Nat.add_le_add_right hh 1) 2))
  have el' := el.trans (Nat.mul_le_mul_left 10 (Nat.pow_le_pow_left (Nat.add_le_add_right hl 1) 2))
  dsimp only [join]
  change _+_+_+(mul r h).bitSteps+(add (mul r h).value l).bitSteps+
    (decodeUnsigned (add (mul r h).value l).value).bitSteps+8 ≤ _
  unfold BackendScalarBits.backendScalarUnit BackendScalarBits.scalarUnit at bm ba
  nlinarith

/-- Both components of the inverse product address are returned by the same
binary long division; neither component is obtained from a free native div. -/
def split (radix index : ℕ) : Result (ℕ×ℕ) :=
  let r := encodeNat radix
  let i := encodeNat index
  let out := UnsignedBits.unsignedSplit r.value i.value
  ⟨out.value,r.bitSteps+i.bitSteps+out.bitSteps+4⟩

theorem split_value (radix index : ℕ) (hr : 0 < radix) :
    (split radix index).value = (index/radix,index%radix) := by
  simp only [split,encodeNat_value]
  simpa only [IntegerArithmetic.value_bits] using
    UnsignedBits.unsignedSplit_value radix.bits index.bits (by simpa only [IntegerArithmetic.value_bits] using hr)

theorem split_bits (radix index W : ℕ) (hr : radix.size ≤ W) (hi : index.size ≤ W) :
    (split radix index).bitSteps ≤ 128*(W+1)^2 := by
  have he := encodeNat_cost radix
  have hi' := encodeNat_cost index
  have hd := UnsignedBits.unsignedSplit_price_quadratic W (encodeNat radix).value (encodeNat index).value
    (by simpa only [encodeNat_value,←Nat.size_eq_bits_len] using hi)
    (by simpa only [encodeNat_value,←Nat.size_eq_bits_len] using hr)
  have he' := he.trans (Nat.mul_le_mul_left 8 (Nat.pow_le_pow_left (Nat.add_le_add_right hr 1) 2))
  have hi'' := hi'.trans (Nat.mul_le_mul_left 8 (Nat.pow_le_pow_left (Nat.add_le_add_right hi 1) 2))
  unfold split
  nlinarith

/-- The exact finite product layout used by every retained recursive table. -/
theorem join_layout {m n : ℕ} (i : Fin m × Fin n) :
    (join n i.1.val i.2.val).value = (finProdFinEquiv i).val := by
  rw [join_value]
  rfl

theorem split_layout {m n : ℕ} (i : Fin (m*n)) :
    (split n i.val).value = ((finProdFinEquiv.symm i).1.val,(finProdFinEquiv.symm i).2.val) := by
  have hn : 0 < n := by
    have hp := i.isLt
    by_contra h
    have : n=0 := by omega
    simp [this] at hp
  rw [split_value n i.val hn]
  rfl

#print axioms join_value
#print axioms join_bits
#print axioms split_value
#print axioms split_bits
#print axioms join_layout
#print axioms split_layout
end ThinMatrix.BinaryMatrixAddress
