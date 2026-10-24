import BinaryMatrixAddress
import RectangularBatch

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! Binary addresses used by the outer rectangular batching adapter.
The produced binary join/split results select the actual retained cells.
Indexed loads/stores remain explicitly separate control operations; this
module does not claim a compiler theorem for Lean's Vector implementation. -/
namespace ThinMatrix.BinaryChunkAddress
open BinaryCell BinaryMultiplierAdapter BinaryModularCell
open RecursiveTable (Table read)
open CompactBlocks (blockCount index blockOf slotOf)

def less (a b : ℕ) : Result Bool :=
  let x := encodeInteger (a:ℤ)
  let y := encodeInteger (b:ℤ)
  let r := lessUnsigned x.value y.value
  ⟨r.value,x.bitSteps+y.bitSteps+r.bitSteps+4⟩

theorem less_true (a b : ℕ) : (less a b).value=true ↔ a<b := by
  have hx : view (encodeInteger (a:ℤ)).value=a := encodeInteger_view _
  have hy : view (encodeInteger (b:ℤ)).value=b := encodeInteger_view _
  change (lessUnsigned _ _).value=true ↔ _
  rw [lessUnsigned_true _ _ (by rw [hx]; positivity) (by rw [hy]; positivity),hx,hy]
  exact Nat.cast_lt

theorem less_bits (a b W : ℕ) (ha : a.size≤W) (hb : b.size≤W) :
    (less a b).bitSteps≤64*(W+1)^2 := by
  have hx := encodeInteger_cost (a:ℤ)
  have hy := encodeInteger_cost (b:ℤ)
  simp only [Int.natAbs_natCast] at hx hy
  have hx' := hx.trans (Nat.mul_le_mul_left 10 (Nat.pow_le_pow_left (Nat.add_le_add_right ha 1) 2))
  have hy' := hy.trans (Nat.mul_le_mul_left 10 (Nat.pow_le_pow_left (Nat.add_le_add_right hb 1) 2))
  have hm : max a.size b.size≤W := max_le ha hb
  have vx : view (encodeInteger (a:ℤ)).value=a := encodeInteger_view _
  have vy : view (encodeInteger (b:ℤ)).value=b := encodeInteger_view _
  simp only [less,lessUnsigned_price,vx,vy,Int.natAbs_natCast]
  nlinarith

def locate {n h : ℕ} (hh : 0<h) (i : Fin n) :
    Result (Fin (blockCount n h) × Fin h) :=
  let out := BinaryMatrixAddress.split h i.val
  have hv : out.value=(i.val/h,i.val%h) := BinaryMatrixAddress.split_value _ _ hh
  ⟨(⟨out.value.1,by rw [hv];exact (blockOf hh i).isLt⟩,
    ⟨out.value.2,by rw [hv];exact Nat.mod_lt _ hh⟩),out.bitSteps+4⟩

theorem locate_value {n h : ℕ} (hh : 0<h) (i : Fin n) :
    (locate hh i).value=(blockOf hh i,slotOf hh i) := by
  apply Prod.ext <;> apply Fin.ext
  all_goals simp only [locate,BinaryMatrixAddress.split_value _ _ hh,blockOf,slotOf]

theorem locate_bits {n h : ℕ} (hh : 0<h) (i : Fin n) (W : ℕ)
    (hhw : h.size≤W) (hnw : n.size≤W) :
    (locate hh i).bitSteps≤132*(W+1)^2 := by
  have hb := BinaryMatrixAddress.split_bits h i.val W hhw
    ((Nat.size_le_size i.isLt.le).trans hnw)
  simp only [locate]
  nlinarith

def original {n h : ℕ} (b : Fin (blockCount n h)) (s : Fin h) : Result ℕ :=
  BinaryMatrixAddress.join h b.val s.val

theorem original_value {n h : ℕ} (b : Fin (blockCount n h)) (s : Fin h) :
    (original b s).value=index b s := by
  rw [original,BinaryMatrixAddress.join_value]
  simp only [index]
  ring

theorem original_bits {n h : ℕ} (b : Fin (blockCount n h)) (s : Fin h)
    (W : ℕ) (hh : h.size≤W) (hb : (blockCount n h).size≤W) :
    (original b s).bitSteps≤4096*(W+1)^2 :=
  BinaryMatrixAddress.join_bits _ _ _ _ hh
    ((Nat.size_le_size b.isLt.le).trans hb) ((Nat.size_le_size s.isLt.le).trans hh)

def matrixRead {V : Type} {n d : ℕ} (x : Table (PaddedMatrix.matrix n d) V)
    (i : Fin n) (j : Fin d) : Result V :=
  let address := BinaryMatrixAddress.join d i.val j.val
  have ha : address.value < n*d := by
    rw [BinaryMatrixAddress.join_layout (i,j)]
    exact (finProdFinEquiv (i,j)).isLt
  ⟨x.get ⟨address.value,ha⟩,address.bitSteps+4⟩

theorem matrixRead_value {V : Type} {n d : ℕ} (x : Table (PaddedMatrix.matrix n d) V)
    (i : Fin n) (j : Fin d) : (matrixRead x i j).value=read x (i,j) := by
  dsimp only [matrixRead,RecursiveTable.read]
  apply congrArg x.get
  exact Fin.ext (BinaryMatrixAddress.join_layout (i,j))

theorem matrixRead_bits {V : Type} {n d : ℕ} (x : Table (PaddedMatrix.matrix n d) V)
    (i : Fin n) (j : Fin d) (W : ℕ) (hn : n.size≤W) (hd : d.size≤W) :
    (matrixRead x i j).bitSteps≤4100*(W+1)^2 := by
  have hb := BinaryMatrixAddress.join_bits d i.val j.val W hd
    ((Nat.size_le_size i.isLt.le).trans hn) ((Nat.size_le_size j.isLt.le).trans hd)
  simp only [matrixRead]
  nlinarith

#print axioms less_true
#print axioms less_bits
#print axioms locate_value
#print axioms locate_bits
#print axioms original_value
#print axioms original_bits
#print axioms matrixRead_value
#print axioms matrixRead_bits
end ThinMatrix.BinaryChunkAddress
