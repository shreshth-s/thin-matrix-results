import HalfSourceHighBandCost
import HalfSourceHighResultCost
import GraphHighBlockProduction

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
namespace ThinMatrix.HalfSourceHighBlockCost
open HalfSourceParameters
open HalfSourceAdaptiveFamilyCost (L t)
open HalfSourceHighScheduleCost (width)
noncomputable section

def constant : ℝ := 10^100*(1+HalfSourceHighVolume.boxConstant+HalfSourceHighResultCost.constant)

def polynomial (N m q : ℕ) : ℕ :=
  width (TilingCosts.bandCount N (ThinMatrixBackend.tileWidth (L m) m)) (L m) m q

def terms (N m M q : ℕ) : ℝ :=
  (q:ℝ)*(N:ℝ)^2*(((4:ℝ)^m)^(-G))+
  (q:ℝ)*(N:ℝ)*(((4:ℝ)^m)^Ebox)+(M:ℝ)*(((4:ℝ)^m)^q2)

theorem constant_nonneg : 0≤constant := by
  unfold constant HalfSourceHighVolume.boxConstant HalfSourceHighResultCost.constant HalfSourceHighQueryCost.constant
  positivity

theorem preprocessing (N m q : ℕ) (hm : 0 < m) (hq : 1≤q)
    (hfit : ThinProductCosts.gridSide (L m) m≤N) :
    (GraphHighPreparation.budget (L m) m (t m) q (HalfSourceHighBandCost.bands N m):ℝ)≤
      10^85*HalfSourceHighVolume.boxConstant*(polynomial N m q:ℝ)^40*
        ((q:ℝ)*(N:ℝ)^2*(((4:ℝ)^m)^(-G))+(q:ℝ)*(N:ℝ)*(((4:ℝ)^m)^Ebox)) := by
  let P := (polynomial N m q:ℝ)
  have hP : 1≤P := by dsimp only[P];exact_mod_cast (show 1≤polynomial N m q by unfold polynomial width;omega)
  have hmP : (m+1:ℝ)≤P := by dsimp[P,polynomial,width];push_cast;linarith [Nat.cast_nonneg (α:=ℝ) (L m),Nat.cast_nonneg (α:=ℝ) q.size,Nat.cast_nonneg (α:=ℝ) ((HalfSourceHighBandCost.bands N m)^2).size]
  have hLP : (L m+1:ℝ)≤P := by dsimp only[P];exact_mod_cast (show L m+1≤polynomial N m q by unfold polynomial width;omega)
  have hw : (HalfSourceHighPolynomials.width (L m) m q:ℝ)≤20*P := by
    dsimp only[P];exact_mod_cast (show HalfSourceHighPolynomials.width (L m) m q≤20*polynomial N m q by unfold polynomial width HalfSourceHighPolynomials.width;omega)
  have hc : 0≤HalfSourceHighVolume.boxConstant := by unfold HalfSourceHighVolume.boxConstant;positivity
  have h5 : P^5≤P^6 := pow_le_pow_right₀ hP (by decide)
  have hh := HalfSourceHighBandCost.budget_bands N m q hm hq hfit
  have h26 : P^26≤P^40 := pow_le_pow_right₀ hP (by decide)
  calc
    _ ≤10^60*q*(m+1:ℝ)^7*(HalfSourceHighPolynomials.width (L m) m q:ℝ)^13*HalfSourceHighVolume.boxConstant*
        (32*N*(L m+1:ℝ)^5*(((4:ℝ)^m)^Ebox)+1024*N^2*(L m+1:ℝ)^6*(((4:ℝ)^m)^(-G))) := hh
    _ ≤10^60*q*P^7*(20*P)^13*HalfSourceHighVolume.boxConstant*
        (32*N*P^6*(((4:ℝ)^m)^Ebox)+1024*N^2*P^6*(((4:ℝ)^m)^(-G))) := by
      gcongr
      exact (pow_le_pow_left₀ (by positivity) hLP 5).trans h5
    _ ≤10^60*20^13*1024*HalfSourceHighVolume.boxConstant*P^26*
        ((q:ℝ)*(N:ℝ)^2*(((4:ℝ)^m)^(-G))+(q:ℝ)*(N:ℝ)*(((4:ℝ)^m)^Ebox)) := by
      nlinarith only [show 0≤(q:ℝ)*P^26*(N:ℝ)*(((4:ℝ)^m)^Ebox)*HalfSourceHighVolume.boxConstant by positivity]
    _ ≤_ := by
      change _ ≤10^85*HalfSourceHighVolume.boxConstant*P^40*_
      gcongr
      norm_num

theorem budget (N m M q B : ℕ) (hm : 0 < m) (hq : 1≤q) (hB : 1≤B)
    (hfit : ThinProductCosts.gridSide (L m) m≤N) :
    let K := HalfSourceHighBandCost.bands N m
    ((B*(GraphHighPreparation.budget (L m) m (t m) q K+
      GraphHighScalarResult.budget K (L m) m (t m) M (HalfSourceHighQueryCost.table (L m) m q)+16)+32*M*(B+1)+16:ℕ):ℝ)≤
      constant*(B:ℝ)*(polynomial N m q:ℝ)^40*terms N m M q := by
  let K := HalfSourceHighBandCost.bands N m
  let P := (polynomial N m q:ℝ)
  let X := (q:ℝ)*(N:ℝ)^2*(((4:ℝ)^m)^(-G))
  let Y := (q:ℝ)*(N:ℝ)*(((4:ℝ)^m)^Ebox)
  let Z := (M:ℝ)*(((4:ℝ)^m)^q2)
  have hP : 1≤P := by dsimp only[P];exact_mod_cast (show 1≤polynomial N m q by unfold polynomial width;omega)
  have hmP : (m+1:ℝ)≤P := by dsimp only[P];exact_mod_cast (show m+1≤polynomial N m q by unfold polynomial width;omega)
  have hqR : (1:ℝ)≤q := by exact_mod_cast hq
  have hBR : (1:ℝ)≤B := by exact_mod_cast hB
  have hX : 0≤X := by dsimp[X];positivity
  have hY : 0≤Y := by dsimp[Y];positivity
  have hZ : 0≤Z := by dsimp[Z];positivity
  have hc : 0≤HalfSourceHighVolume.boxConstant := by unfold HalfSourceHighVolume.boxConstant;positivity
  have hr : 0≤HalfSourceHighResultCost.constant := by unfold HalfSourceHighResultCost.constant HalfSourceHighQueryCost.constant;positivity
  have hprep := preprocessing N m q hm hq hfit
  change _≤10^85*HalfSourceHighVolume.boxConstant*P^40*(X+Y) at hprep
  have hqscale : (N:ℝ)^2*(((4:ℝ)^m)^(-G))≤X := by
    dsimp[X]
    nlinarith only [mul_le_mul_of_nonneg_right hqR (show 0≤(N:ℝ)^2*(((4:ℝ)^m)^(-G)) by positivity)]
  have hres := HalfSourceHighResultCost.budget_bound N m M q hm hfit
  have h37 : P^37≤P^40 := pow_le_pow_right₀ hP (by decide)
  have hres' : (GraphHighScalarResult.budget K (L m) m (t m) M (HalfSourceHighQueryCost.table (L m) m q):ℝ)≤HalfSourceHighResultCost.constant*P^40*(X+Z) := by
    exact hres.trans (by change HalfSourceHighResultCost.constant*P^37*(_+Z)≤_;gcongr)
  have hpair := HalfSourceHighScheduleCost.band_pairs N m hm hfit
  have hbasic : 1≤8*P*X := by
    have hh : 1≤8*(N:ℝ)^2*(m+1:ℝ)*(((4:ℝ)^m)^(-G)) := by nlinarith only [hpair,sq_nonneg (K:ℝ)]
    calc
      _ ≤8*(N:ℝ)^2*(m+1:ℝ)*(((4:ℝ)^m)^(-G)) := hh
      _ ≤8*P*X := by nlinarith only [mul_le_mul_of_nonneg_right hmP (show 0≤8*((N:ℝ)^2*(((4:ℝ)^m)^(-G))) by positivity),mul_le_mul_of_nonneg_left hqscale (show 0≤8*P by positivity)]
  have hP40 : P≤P^40 := by simpa using (pow_le_pow_right₀ hP (show 1≤40 by decide))
  have hbase : 1≤8*P^40*X := hbasic.trans (by gcongr)
  have hq2 : 0≤q2 := by have hh:=QEnclosure.1;norm_num[q2,theta] at *;linarith
  have hM : (M:ℝ)≤Z := by
    exact le_mul_of_one_le_right (by positivity) (Real.one_le_rpow (one_le_pow₀ (by norm_num)) hq2)
  have hM40 : (M:ℝ)≤P^40*Z := hM.trans (le_mul_of_one_le_left hZ (one_le_pow₀ hP))
  have hB0 : 0≤(B:ℝ) := by positivity
  have hover : (B:ℝ)*16+32*(M:ℝ)*((B:ℝ)+1)+16≤1000*(B:ℝ)*P^40*(X+Z) := by
    have hb := mul_le_mul_of_nonneg_left hbase hB0
    have hmB := mul_le_mul_of_nonneg_left hM40 hB0
    have hbm := mul_le_mul_of_nonneg_right hBR (show 0≤P^40*Z by positivity)
    nlinarith only [hbase,hb,hmB,hbm,hM40,hBR,show 0≤(B:ℝ)*P^40*X by positivity,show 0≤(B:ℝ)*P^40*Z by positivity]
  have hpb := mul_le_mul_of_nonneg_left hprep hB0
  have hrb := mul_le_mul_of_nonneg_left hres' hB0
  intro K'
  dsimp only[K']
  push_cast
  change _≤constant*(B:ℝ)*P^40*(X+Y+Z)
  have hc1 : 10^85*HalfSourceHighVolume.boxConstant+HalfSourceHighResultCost.constant+1000≤constant := by
    unfold constant
    nlinarith only[hc,hr]
  calc
    _ ≤(10^85*HalfSourceHighVolume.boxConstant+HalfSourceHighResultCost.constant+1000)*(B:ℝ)*P^40*(X+Y+Z) := by
      nlinarith only[hpb,hrb,hover,
      mul_nonneg hc (show 0≤(B:ℝ)*P^40*Z by positivity),
      mul_nonneg hr (show 0≤(B:ℝ)*P^40*Y by positivity),
      show 0≤(B:ℝ)*P^40*Y by positivity]
    _ ≤ _ := by gcongr

theorem actual {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f)
    (shape : ThinMatrixBackend.ShapePlan p.L p.m)
    (sources : Fin (CompactBlocks.blockCount n h) → GraphRetainedHigh.Sources f p
      (K:=TilingCosts.bandCount p.N (ThinMatrixBackend.tileWidth p.L p.m)))
    (requests : GraphHighRun.Requests n p.L p.m f.cyclic)
    (hb : ∀ i,(requests.get i).bandL<TilingCosts.bandCount p.N (ThinMatrixBackend.tileWidth p.L p.m) ∧
      (requests.get i).bandR<TilingCosts.bandCount p.N (ThinMatrixBackend.tileWidth p.L p.m))
    (input : BinaryFoldedFormation.Inputs n)
    (hc : ∀ b,GraphRetainedHigh.Correct f p b input (Vector.ofFn (fun a => a.val)) (sources b))
    (hL : p.L=L p.m) (ht : p.t=t p.m) (hm : 0 < p.m)
    (hB : 1≤CompactBlocks.blockCount n h) (hfit : ThinProductCosts.gridSide p.L p.m≤p.N) :
    ((GraphHighBlockProduction.execute f p shape sources requests hb).operations:ℝ)≤
      constant*(CompactBlocks.blockCount n h:ℝ)*
        (width (TilingCosts.bandCount p.N (ThinMatrixBackend.tileWidth p.L p.m)) p.L p.m f.cyclic:ℝ)^40*
        terms p.N p.m (FoldedBackendExecution.windowQuerySize n) f.cyclic := by
  have hh : ((GraphHighBlockProduction.execute f p shape sources requests hb).operations:ℝ)≤
      (GraphHighBlockProduction.budget f p (K:=TilingCosts.bandCount p.N (ThinMatrixBackend.tileWidth p.L p.m)):ℝ) := by
    exact_mod_cast GraphHighBlockProduction.work f p shape sources requests hb input hc
  apply hh.trans
  unfold GraphHighBlockProduction.budget
  rw[hL,ht]
  exact budget p.N p.m (FoldedBackendExecution.windowQuerySize n) f.cyclic (CompactBlocks.blockCount n h)
    hm (Nat.one_le_of_lt f.cyclic_pos) hB (by simpa only[←hL] using hfit)

#print axioms constant_nonneg
#print axioms actual
#print axioms preprocessing
#print axioms budget
end
end ThinMatrix.HalfSourceHighBlockCost
