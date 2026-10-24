import GraphCallbackStorage

set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace ThinMatrix.GraphCallbackOutputStorage
open GraphOwnBandPriced GraphAdaptiveRootBatch
variable {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
  (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f)

/-- Full q-coefficient LOW rows, both normalized scalar rows, per-block
counts and row IDs are retained. Positive q makes the count-table axis a
subaxis of Q; no dropped cyclic-vector storage is used. -/
def cells := 64*(M (n:=n)+1)*(Q f p+1)*(p.L+p.m+1)

 theorem bound (scheme : RectangularBatch.Scheme) (hh : 0<h) :
    cells f p≤2^(9*GraphOwnBandStorage.scale scheme (GraphOwnBandShapeBounds.width f p)+21) := by
  let U:=GraphOwnBandShapeBounds.width f p
  let V:=GraphOwnBandStorage.scale scheme U
  have huv : U≤V := (GraphOwnBandStorage.scale_bounds scheme U).1
  have hM : M (n:=n)≤2^U := by
    change n*n*3≤_
    calc
      _ ≤ (2^n.size)*(2^n.size)*4 := Nat.mul_le_mul (Nat.mul_le_mul (Nat.lt_size_self n).le (Nat.lt_size_self n).le) (by decide)
      _ = 2^(2*n.size+2) := by ring
      _ ≤ _ := Nat.pow_le_pow_right (by decide) (by unfold U GraphOwnBandShapeBounds.width;omega)
  have hB : CompactBlocks.blockCount n h≤n :=
    (ceilDiv_le_iff_le_mul hh).mpr (Nat.le_mul_of_pos_left _ hh)
  have hQ : Q f p≤2^U := by
    change CompactBlocks.blockCount n h*((p.m+1)*f.cyclic)≤_
    calc
      _ ≤ 2^n.size*(2^(p.m+1)*2^f.cyclic.size) := Nat.mul_le_mul (hB.trans (Nat.lt_size_self _).le)
        (Nat.mul_le_mul Nat.lt_two_pow_self.le (Nat.lt_size_self _).le)
      _ = 2^(n.size+p.m+1+f.cyclic.size) := by rw [pow_add,pow_add,pow_add];ring
      _ ≤ _ := Nat.pow_le_pow_right (by decide) (by unfold U GraphOwnBandShapeBounds.width;omega)
  have hL : p.L+p.m+1≤2^U := Nat.lt_two_pow_self.le.trans
    (Nat.pow_le_pow_right (by decide) (by unfold U GraphOwnBandShapeBounds.width;omega))
  have addpow {x : ℕ} (hx : x≤2^U) : x+1≤2^(U+1) := by
    have h1 : 1≤2^U := one_le_pow₀ (by decide)
    rw [pow_succ];omega
  unfold cells
  calc
    _ ≤ 64*2^(U+1)*2^(U+1)*2^U := Nat.mul_le_mul
      (Nat.mul_le_mul (Nat.mul_le_mul_left 64 (addpow hM)) (addpow hQ)) hL
    _ = 2^(3*U+8) := by ring
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (by change 3*U+8≤9*V+21;omega)

#print axioms bound
end ThinMatrix.GraphCallbackOutputStorage
