import GraphOwnBandShapeBounds
import SharedPreparedWidths

set_option autoImplicit false
set_option exponentiation.threshold 2048
set_option maxHeartbeats 2200000
set_option maxRecDepth 10000
namespace ThinMatrix.GraphOwnBandStorage
open GraphAdaptiveRootBatch GraphOwnBandPriced GraphOwnBandTypeRate
variable {n h r S : ℕ} (f : CompactBlocks.PhysicalFactorization r)
  (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (base : Index f p)
  (scheme : RectangularBatch.Scheme) (hnum : scheme.num=861) (hden : scheme.den=500) (hz : scheme.z=15)

/-- Fixed-base coefficients affect only this constant multiplier. -/
def scale (scheme : RectangularBatch.Scheme) (U : ℕ) :=
  (SharedPreparedWidths.cellSlope scheme+SharedPreparedWidths.fieldSlope scheme+1)*(3*U+10)

 theorem scale_bounds (scheme : RectangularBatch.Scheme) (U : ℕ) :
    U≤ scale scheme U ∧ SharedPreparedWidths.cellSlope scheme*(U+3)≤ scale scheme U ∧
    SharedPreparedWidths.fieldSlope scheme*(2*U+5)≤ scale scheme U := by
  unfold scale
  constructor
  · nlinarith
  constructor <;> nlinarith

def shape := (SharedMatrixSetup.prepare scheme (CappedSubsetList.count_pos _ _ : 0<D f p base)
  (by rw [hden,hnum];exact SharedCompletionTile.integer_fit (D f p base) (CappedSubsetList.count_pos _ _))
  (by rw [hz];exact le_refl _ : SharedCompletionTile.col (D f p base)≤(D f p base)^scheme.z)
  (A:=SharedCompletionTile.row (D f p base))).value

def cells := SharedPreparedWidths.cells scheme (shape f p base scheme hnum hden hz)
def fields := SharedPreparedWidths.fields scheme (shape f p base scheme hnum hden hz) (H f p base)

def root := SharedPrefixStorage.rootBudget (W f p)
  (WindowPrefixProgram.prefixLength (p.L-p.m) (E f p base))
  (WindowPrefixProgram.length (p.L-p.m) (E f p base)) (M (n:=n)) (D f p base)
  (CompactBlocks.blockCount n h) ((p.m+1)*f.cyclic)
  (SharedCompletionTile.row (D f p base)) (SharedCompletionTile.col (D f p base))
  (cells f p base scheme hnum hden hz)

 theorem recursive_bounds (hh : 0<h) (hSN : S≤p.N) :
    cells f p base scheme hnum hden hz≤2^(scale scheme (GraphOwnBandShapeBounds.width f p)) ∧
    fields f p base scheme hnum hden hz≤ scale scheme (GraphOwnBandShapeBounds.width f p) := by
  have hw := GraphOwnBandShapeBounds.powers f p base hh hSN
  have hs := (Nat.size_le_size hw.2.2.1).trans_eq Nat.size_pow
  have hH := (Nat.size_le_size hw.2.2.2.2.2.2.2.1).trans_eq Nat.size_pow
  have hh0 := scale_bounds scheme (GraphOwnBandShapeBounds.width f p)
  unfold cells fields shape
  apply SharedPreparedWidths.retained_power_bounds
  · exact (Nat.mul_le_mul_left _ (by omega : (D f p base).size+2≤GraphOwnBandShapeBounds.width f p+3)).trans hh0.2.1
  · exact (Nat.mul_le_mul_left _ (by omega : (D f p base).size+(H f p base).size+3≤2*GraphOwnBandShapeBounds.width f p+5)).trans hh0.2.2

 theorem root_bound (hh : 0<h) (hSN : S≤p.N) :
    root f p base scheme hnum hden hz≤2^(9*scale scheme (GraphOwnBandShapeBounds.width f p)+21) := by
  let U:=GraphOwnBandShapeBounds.width f p
  let V:=scale scheme U
  have hw := GraphOwnBandShapeBounds.powers f p base hh hSN
  have huv : U≤V := (scale_bounds scheme U).1
  have pw {x : ℕ} (hx : x≤2^U) : x≤2^V := hx.trans (Nat.pow_le_pow_right (by decide) huv)
  have hdim := WindowPrefixProgram.dimension (p.L-p.m) (E f p base)
  have hlen : WindowPrefixProgram.prefixLength (p.L-p.m) (E f p base)+WindowPrefixProgram.length (p.L-p.m) (E f p base)≤V := by
    rw [hdim]
    have htwo : 2*p.L≤U := by unfold U GraphOwnBandShapeBounds.width;omega
    omega
  have hB : CompactBlocks.blockCount n h≤2^U := by
    have hnU : n.size≤U := by unfold U GraphOwnBandShapeBounds.width;omega
    exact ((ceilDiv_le_iff_le_mul hh).mpr (Nat.le_mul_of_pos_left n hh)).trans
      (Nat.lt_size_self n).le |>.trans (Nat.pow_le_pow_right (by decide) hnU)
  have hC : (p.m+1)*f.cyclic≤2^U := by
    calc
      _ ≤ 2^(p.m+1)*2^f.cyclic.size := Nat.mul_le_mul Nat.lt_two_pow_self.le (Nat.lt_size_self _).le
      _ = 2^(p.m+1+f.cyclic.size) := (pow_add _ _ _).symm
      _ ≤ _ := Nat.pow_le_pow_right (by decide) (by unfold U GraphOwnBandShapeBounds.width;omega)
  have hr := (recursive_bounds f p base scheme hnum hden hz hh hSN).1
  have dims := SharedCompletionTile.dimensions (D f p base) (CappedSubsetList.count_pos _ _)
  exact SharedPrefixStorageBounds.root_bound _ _ _ _ _ _ _ _ _ _ V hlen dims.1 dims.2.1
    (pw hw.2.2.2.2.2.2.2.2) (pw hw.2.1) (pw hw.2.2.1) (pw hB) (pw hC)
    (pw hw.2.2.2.1) (pw hw.2.2.2.2.1) (pw hw.2.2.2.2.2.1) hr

/-- All own-band/mask roots may remain live. This already includes every
window source bank, request router, child matrix tree, and output coefficient.
The masks' original incidence count is retained once in the multiplying G. -/
def allRoots := G f p (S:=S)*root f p base scheme hnum hden hz

attribute [local irreducible] scale root cells fields shape SharedPreparedWidths.cellSlope SharedPreparedWidths.fieldSlope

 theorem all_roots_bound (hh : 0<h) (hSN : S≤p.N) :
    allRoots f p base scheme hnum hden hz (S:=S)≤2^(10*scale scheme (GraphOwnBandShapeBounds.width f p)+21) := by
  have hg := (GraphOwnBandShapeBounds.powers f p base hh hSN).2.2.2.2.2.2.1
  have huv := (scale_bounds scheme (GraphOwnBandShapeBounds.width f p)).1
  have hgV := hg.trans (Nat.pow_le_pow_right (by decide) huv)
  have hr := root_bound f p base scheme hnum hden hz hh hSN
  unfold allRoots
  have hh0 := Nat.mul_le_mul hgV hr
  rw [←pow_add] at hh0
  convert hh0 using 1
  ring

#print axioms scale_bounds
#print axioms recursive_bounds
#print axioms root_bound
#print axioms all_roots_bound
end ThinMatrix.GraphOwnBandStorage
