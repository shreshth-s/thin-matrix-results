import AdaptiveBitBounds

/-!
# Global backend address widths

Local coefficient-array addresses do not by themselves bound global band
and tile indices. This file supplies a separate whole-grid majorant and
bounds the actual computed outer dimension before propagating it through
original-input, band and tile address arithmetic.
-/
namespace ThinMatrix.GlobalAddressBitBounds
open scoped BigOperators
open ThinMatrixBackend AdaptiveBitBounds
noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

def computedOuterConstant : ℕ := 17*AlignedCertificate.R+4

theorem outer_le_pow_size (R S n : ℕ) (hn : 3 ≤ n)
    (call : ComputedPhaseGeometry.Call R n)
    (he : 1+PhaseGeometry.foldExponent S call.factors.length/2 ≤ (2:ℝ))
    (hs : 0 ≤ PhaseGeometry.foldExponent S call.factors.length) :
    PhaseGeometry.outerSize call S n ≤ 2^((17*R+4)*n.size) := by

  have h := (ComputedPhaseGeometry.actual_outer_bounds R
    S n hn call hs).2
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hn0 : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlog : Real.log (n:ℝ) ≤ n := by linarith [Real.log_le_sub_one_of_pos hn0]
  have hlog0 : 0 ≤ Real.log (n:ℝ) := Real.log_nonneg hn1
  have hpow : (n:ℝ)^(1+PhaseGeometry.foldExponent S call.factors.length/2) ≤ (n:ℝ)^2 := by
    exact_mod_cast Real.rpow_le_rpow_of_exponent_le hn1 he
  have hpoly : (PhaseGeometry.outerSize call S n:ℝ) ≤
      4*(8192:ℝ)^R*(n:ℝ)^(4*R+2) := by
    apply h.trans
    unfold ComputedPhaseGeometry.phaseOverhead
    calc
      _ ≤ 4*((8192:ℝ)^R*(n:ℝ)^(4*R))*(n:ℝ)^2 := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlog0 hlog _) (by positivity)) (by norm_num)
        · exact hpow
        · positivity
        · positivity
      _ = _ := by rw [pow_add]; ring
  have hnat : PhaseGeometry.outerSize call S n ≤
      4*8192^R*n^(4*R+2) := by exact_mod_cast hpoly
  have hsize : 1 ≤ n.size := Nat.size_pos.mpr (by omega)
  calc
    _ ≤ 4*8192^R*n^(4*R+2) := hnat
    _ ≤ 4*8192^R*(2^n.size)^(4*R+2) :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (nat_le_pow_size n) _)
    _ = 2^(2+13*R+n.size*(4*R+2)) := by
      rw [show (4:ℕ)=2^2 by norm_num,show (8192:ℕ)=2^13 by norm_num,
        ←pow_mul,←pow_mul,←pow_add,←pow_add]
    _ ≤ _ := by
      apply Nat.pow_le_pow_right (by norm_num)
      nlinarith only [hsize]

theorem computed_outer_le_pow_size (n : ℕ) (hn : 3 ≤ n)
    (call : ComputedPhaseGeometry.Call AlignedCertificate.R n) :
    PhaseGeometry.outerSize call AlignedCertificate.S n ≤
      2^(computedOuterConstant*n.size) := by
  have hs := PhaseGeometry.aligned_fold_exponent_range call.factors.length
  have hu : AsymptoticCosts.u ≤ 1 := by
    norm_num [AsymptoticCosts.u,AlignedCertificate.u,AlignedCertificate.eta,
      AlignedCertificate.b,AlignedCertificate.S,AlignedCertificate.R]
  exact outer_le_pow_size AlignedCertificate.R AlignedCertificate.S n hn call (by linarith) hs.1

/-- A majorant for global original-input cells and for local arrays across
all bands and all band pairs. It does not allocate a new dense tensor. -/
def globalAddressCells (N L m q : ℕ) : ℕ :=
  16*(N+1)^2*(AdaptiveBitBounds.metadataCells L m q+1)

theorem globalAddressCells_le_pow (n N L m q cN cL cm cq : ℕ)
    (hN : N ≤ 2^(cN*n.size)) (hL : L ≤ cL*n.size)
    (hm : m ≤ cm*n.size) (hq : q ≤ 2^(cq*n.size)) :
    globalAddressCells N L m q ≤
      2^((2*cN+cq+12*cL+2*cm+9)*(n.size+1)) := by
  have hpN : 1 ≤ 2^(cN*n.size) := one_le_pow₀ (by decide)
  have hNp : N+1 ≤ 2^(cN*n.size+1) := by
    calc
      _ ≤ 2^(cN*n.size)+2^(cN*n.size) := Nat.add_le_add hN hpN
      _ = _ := by rw [pow_succ]; omega
  let M := cq+12*cL+2*cm+2
  have hlocal := metadataCells_le_pow n L m q cL cm cq hL hm hq
  have hlocal' : metadataCells L m q+1 ≤ 2^(M*(n.size+1)+1) := by
    have hp : 1 ≤ 2^(M*(n.size+1)) := one_le_pow₀ (by decide)
    calc
      _ ≤ 2^(M*(n.size+1))+2^(M*(n.size+1)) := Nat.add_le_add hlocal hp
      _ = _ := by rw [pow_succ]; omega
  unfold globalAddressCells
  calc
    _ ≤ 16*(2^(cN*n.size+1))^2*2^(M*(n.size+1)+1) := by gcongr
    _ = 2^(4+(cN*n.size+1)*2+(M*(n.size+1)+1)) := by
      rw [show (16:ℕ)=2^4 by norm_num,←pow_mul,←pow_add,←pow_add]
    _ ≤ _ := by
      apply Nat.pow_le_pow_right (by norm_num)
      dsimp [M]
      nlinarith

theorem global_index_size (n N L m q cN cL cm cq j : ℕ)
    (hN : N ≤ 2^(cN*n.size)) (hL : L ≤ cL*n.size)
    (hm : m ≤ cm*n.size) (hq : q ≤ 2^(cq*n.size))
    (hj : j ≤ globalAddressCells N L m q) :
    j.size ≤ (2*cN+cq+12*cL+2*cm+9)*(n.size+1)+1 := by
  exact (Nat.size_le_size (hj.trans
    (globalAddressCells_le_pow n N L m q cN cL cm cq hN hL hm hq))).trans_eq Nat.size_pow

/-- Actual global original-array row/column and cyclic-slot flattening. -/
theorem original_cells_le_global (N D L m q : ℕ) (hD : D ≤ 4^m) (hm : m ≤ L) :
    N*D*q ≤ globalAddressCells N L m q := by
  have hD' : D ≤ 2^(10*L) := by
    calc
      _ ≤ 4^m := hD
      _ = 2^(2*m) := by rw [show (4:ℕ)=2^2 by norm_num,←pow_mul]
      _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hl : q*2^(10*L) ≤ metadataCells L m q := by
    unfold metadataCells
    have h1 : 1 ≤ 2*L+1 := by omega
    have h2 : 1 ≤ 2*m+1 := by omega
    have hfirst : q ≤ q*(2*L+1) := Nat.le_mul_of_pos_right q (by omega)
    have hsecond : q*(2*L+1) ≤ q*(2*L+1)*(2*m+1) := Nat.le_mul_of_pos_right _ (by omega)
    exact Nat.mul_le_mul_right _ (hfirst.trans hsecond)
  have hN : N ≤ (N+1)^2 := by nlinarith
  have hlocal : q*2^(10*L) ≤ metadataCells L m q+1 := by omega
  have hprod := Nat.mul_le_mul hN hlocal
  unfold globalAddressCells
  have hinput : N*D*q ≤ (N+1)^2*(metadataCells L m q+1) := by
    calc
      _ ≤ N*2^(10*L)*q := Nat.mul_le_mul_right q (Nat.mul_le_mul_left N hD')
      _ = N*(q*2^(10*L)) := by ring
      _ ≤ _ := hprod
  nlinarith

/-- A local cell flattened across a whole square collection of bands. -/
theorem tile_cells_le_global (N L m q bands localCells : ℕ)
    (hbands : bands ≤ N+1) (hlocal : localCells ≤ metadataCells L m q) :
    bands^2*localCells ≤ globalAddressCells N L m q := by
  have h := Nat.mul_le_mul (Nat.pow_le_pow_left hbands 2) hlocal
  unfold globalAddressCells
  nlinarith


theorem actual_bandCount_le_N (N L m : ℕ) (hm : m ≤ L) :
    TilingCosts.bandCount N (tileWidth L m) ≤ N := by
  unfold TilingCosts.bandCount
  apply (ceilDiv_le_iff_le_smul (tileWidth_pos L m hm)).mpr
  exact Nat.le_mul_of_pos_left N (tileWidth_pos L m hm)

theorem actual_tile_cells_le_global (N L m q localCells : ℕ) (hm : m ≤ L)
    (hlocal : localCells ≤ metadataCells L m q) :
    (TilingCosts.bandCount N (tileWidth L m))^2*localCells ≤ globalAddressCells N L m q := by
  exact tile_cells_le_global N L m q _ localCells
    ((actual_bandCount_le_N N L m hm).trans (by omega)) hlocal

theorem computed_global_index_size (n j : ℕ) (hn : 3 ≤ n)
    (call : ComputedPhaseGeometry.Call AlignedCertificate.R n)
    (hj : j ≤ globalAddressCells (PhaseGeometry.outerSize call AlignedCertificate.S n)
      (Nat.ceil (RealCertificate.c*(ComputedPhaseGeometry.innerPower n call AlignedCertificate.S:ℝ)))
      (ComputedPhaseGeometry.innerPower n call AlignedCertificate.S)
      (call.cyclic AlignedCertificate.S)) :
    j.size ≤ (2*computedOuterConstant+computedCyclicConstant+12*computedLengthConstant+
      2*computedIndexConstant+9)*(n.size+1)+1 := by
  exact global_index_size n _ _ _ _ computedOuterConstant computedLengthConstant
    computedIndexConstant computedCyclicConstant j (computed_outer_le_pow_size n hn call)
    (computed_roundedLength_le_size n hn call) (computed_innerPower_le_size n hn call)
    (computed_cyclic_le_pow_size n hn call) hj

end
end ThinMatrix.GlobalAddressBitBounds

#print axioms ThinMatrix.GlobalAddressBitBounds.computed_outer_le_pow_size
#print axioms ThinMatrix.GlobalAddressBitBounds.globalAddressCells_le_pow
#print axioms ThinMatrix.GlobalAddressBitBounds.global_index_size
#print axioms ThinMatrix.GlobalAddressBitBounds.original_cells_le_global
#print axioms ThinMatrix.GlobalAddressBitBounds.tile_cells_le_global
#print axioms ThinMatrix.GlobalAddressBitBounds.actual_bandCount_le_N
#print axioms ThinMatrix.GlobalAddressBitBounds.actual_tile_cells_le_global
#print axioms ThinMatrix.GlobalAddressBitBounds.computed_global_index_size
