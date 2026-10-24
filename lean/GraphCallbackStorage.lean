import GraphOwnBandStorage
import GlobalAddressBitBounds

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 10000
namespace ThinMatrix.GraphCallbackStorage
open GraphAdaptiveRootBatch GraphOwnBandPriced GraphOwnBandTypeRate
variable {n h r S : ℕ} (f : CompactBlocks.PhysicalFactorization r)
  (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f)

/-- Actual two-sided degree/translation/channel root family size. -/
def types := 2*(ExactHalfSourcePlan.J p.m)^2*(2*p.m+1)*ResidualFamilyKeys.channelCount p.m p.t

 theorem types_bound : types f p≤2^(GraphOwnBandShapeBounds.width f p) := by
  have hj : ExactHalfSourcePlan.J p.m≤2^(3*p.m+6) := by
    rw [←ExactHalfSourcePlan.count_eq,ExactHalfSourcePlan.count]
    split
    · exact one_le_pow₀ (by decide)
    · calc
        64*p.m^3 ≤ 64*(2^p.m)^3 := Nat.mul_le_mul_left 64 (Nat.pow_le_pow_left Nat.lt_two_pow_self.le 3)
        _ = 2^(3*p.m+6) := by ring
  have hc : ResidualFamilyKeys.channelCount p.m p.t≤2^(2*p.m) := by
    unfold ResidualFamilyKeys.channelCount
    split
    · exact Nat.zero_le _
    · simpa only [two_mul] using BinaryGroupedCompletion.count_le_power (p.m+p.m) (p.t-1)
  have hr : 2*p.m+1≤2^(2*p.m+1) := Nat.lt_two_pow_self.le
  unfold types
  calc
    _ ≤ 2*(2^(3*p.m+6))^2*2^(2*p.m+1)*2^(2*p.m) :=
      Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left hj 2)) hr) hc
    _ = 2^(10*p.m+14) := by ring
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (by unfold GraphOwnBandShapeBounds.width;omega)

/-- Existing whole-grid layout includes source encoders and metadata. The
new root trees are accounted for separately below. This is a storage upper
bound only; it neither executes nor charges a dense encoder. -/
 theorem grid_bound : GlobalAddressBitBounds.globalAddressCells p.N p.L p.m f.cyclic≤
    2^(17*GraphOwnBandShapeBounds.width f p+9) := by
  let U:=GraphOwnBandShapeBounds.width f p
  have hL : p.L≤U := by unfold U GraphOwnBandShapeBounds.width;omega
  have hm : p.m≤U := by unfold U GraphOwnBandShapeBounds.width;omega
  have hq : f.cyclic≤2^U := (Nat.lt_size_self _).le.trans (Nat.pow_le_pow_right (by decide)
    (by unfold U GraphOwnBandShapeBounds.width;omega))
  have hN : p.N≤2^U := (Nat.lt_size_self _).le.trans (Nat.pow_le_pow_right (by decide)
    (by unfold U GraphOwnBandShapeBounds.width;omega))
  have hLa : 2*p.L+1≤2^(2*U+1) := Nat.lt_two_pow_self.le.trans (Nat.pow_le_pow_right (by decide) (by omega))
  have hma : 2*p.m+1≤2^(2*U+1) := Nat.lt_two_pow_self.le.trans (Nat.pow_le_pow_right (by decide) (by omega))
  have hmeta : AdaptiveBitBounds.metadataCells p.L p.m f.cyclic≤2^(15*U+2) := by
    unfold AdaptiveBitBounds.metadataCells
    calc
      _ ≤ 2^U*2^(2*U+1)*2^(2*U+1)*2^(10*U) :=
        Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul hq hLa) hma)
          (Nat.pow_le_pow_right (by decide) (by omega))
      _ = _ := by rw [←pow_add,←pow_add,←pow_add];congr 1;omega
  have addpow {x e : ℕ} (hx : x≤2^e) : x+1≤2^(e+1) := by
    have h1 : 1≤2^e := one_le_pow₀ (by decide)
    rw [pow_succ];omega
  unfold GlobalAddressBitBounds.globalAddressCells
  calc
    _ ≤ 16*(2^(U+1))^2*2^(15*U+3) := Nat.mul_le_mul
      (Nat.mul_le_mul_left 16 (Nat.pow_le_pow_left (addpow hN) 2)) (addpow hmeta)
    _ = _ := by ring

/-- Retain every original source/grid structure for every block and type,
plus all own-band roots (each including all windows/chunks/coefficients).
Constant-factor record headers and original-ID result arrays are included. -/
def payload (scheme : RectangularBatch.Scheme) :=
  let U:=GraphOwnBandShapeBounds.width f p
  let V:=GraphOwnBandStorage.scale scheme U
  64*(CompactBlocks.blockCount n h+1)*(types f p+1)*
    (GlobalAddressBitBounds.globalAddressCells p.N p.L p.m f.cyclic+1+
      (G f p (S:=S)+1)*(2^(9*V+21)+1))

 theorem payload_bound (scheme : RectangularBatch.Scheme) (hh : 0<h) (hSN : S≤p.N) :
    payload f p scheme (S:=S)≤2^(40*GraphOwnBandStorage.scale scheme (GraphOwnBandShapeBounds.width f p)+40) := by
  let U:=GraphOwnBandShapeBounds.width f p
  let V:=GraphOwnBandStorage.scale scheme U
  have huv : U≤V := (GraphOwnBandStorage.scale_bounds scheme U).1
  have hg0 := (HalfSourceActualVolumes.good_count p.L p.m).trans (Nat.choose_le_two_pow p.L p.m)
  have hg : G f p (S:=S)≤2^U := by
    change S*((GoodMapEmbedding.goodSlots p.L p.m).card*(GoodMapEmbedding.goodSlots p.L p.m).card)≤_
    calc
      _ ≤ 2^p.N.size*(2^p.L*2^p.L) := Nat.mul_le_mul (hSN.trans (Nat.lt_size_self p.N).le) (Nat.mul_le_mul hg0 hg0)
      _ = 2^(p.N.size+2*p.L) := by ring
      _ ≤ _ := Nat.pow_le_pow_right (by decide) (by unfold U GraphOwnBandShapeBounds.width;omega)
  have hB : CompactBlocks.blockCount n h≤2^U := by
    exact ((ceilDiv_le_iff_le_mul hh).mpr (Nat.le_mul_of_pos_left n hh)).trans
      ((Nat.lt_size_self n).le.trans (Nat.pow_le_pow_right (by decide) (by unfold U GraphOwnBandShapeBounds.width;omega)))
  have addpow {x e : ℕ} (hx : x≤2^e) : x+1≤2^(e+1) := by
    have h1 : 1≤2^e := one_le_pow₀ (by decide)
    rw [pow_succ];omega
  have hgrid := addpow (grid_bound f p)
  have hroots : (G f p (S:=S)+1)*(2^(9*V+21)+1)≤2^(U+9*V+23) := by
    exact (Nat.mul_le_mul (addpow hg) (addpow (le_refl (2^(9*V+21))))).trans_eq (by rw [←pow_add];congr 1;omega)
  have hc1 : GlobalAddressBitBounds.globalAddressCells p.N p.L p.m f.cyclic+1≤2^(18*V+30) :=
    hgrid.trans (Nat.pow_le_pow_right (by decide) (by omega))
  have hc2 : (G f p (S:=S)+1)*(2^(9*V+21)+1)≤2^(18*V+30) :=
    hroots.trans (Nat.pow_le_pow_right (by decide) (by omega))
  have hsum : GlobalAddressBitBounds.globalAddressCells p.N p.L p.m f.cyclic+1+
      (G f p (S:=S)+1)*(2^(9*V+21)+1)≤2^(18*V+31) := by
    calc
      _ ≤ 2^(18*V+30)+2^(18*V+30) := Nat.add_le_add hc1 hc2
      _ = _ := by rw [show 18*V+31=(18*V+30)+1 by omega];ring
  unfold payload
  change 64*(_+1)*(_+1)*_≤2^(40*V+40)
  calc
    _ ≤ 64*2^(U+1)*2^(U+1)*2^(18*V+31) := Nat.mul_le_mul
      (Nat.mul_le_mul (Nat.mul_le_mul_left 64 (addpow hB)) (addpow (types_bound f p))) hsum
    _ = 2^(2*U+18*V+39) := by ring
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (by omega)

#print axioms types_bound
#print axioms grid_bound
#print axioms payload_bound
end ThinMatrix.GraphCallbackStorage
