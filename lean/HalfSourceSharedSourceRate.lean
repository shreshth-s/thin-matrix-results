import HalfSourceSharedSourceBudget
import HalfSourceCapPolynomial
import HalfSourceAssemblyAlgebra

namespace ThinMatrix.HalfSourceSharedSourceRate
open HalfSourceParameters HalfSourceSharedSourceBudget
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 16000
noncomputable section

def constant : ℝ := 10^30*(1+HalfSourceRootVolume.rootConstant+HalfSourceAdaptiveBandCost.constant)
def volume (N m q : ℕ) : ℝ :=
  (q:ℝ)*(N:ℝ)^2*(((4:ℝ)^m)^(-G))+(q:ℝ)*(N:ℝ)*(((4:ℝ)^m)^E)+
    (q:ℝ)*(N:ℝ)*(((4:ℝ)^m)^Eroot)+(q:ℝ)*(N:ℝ)*(4:ℝ)^m

theorem constant_bounds : 10^30 ≤ constant ∧
    10^30*HalfSourceRootVolume.rootConstant ≤ constant ∧
    10^30*HalfSourceAdaptiveBandCost.constant ≤ constant := by
  have hr : 0 ≤ HalfSourceRootVolume.rootConstant := by unfold HalfSourceRootVolume.rootConstant;positivity
  have he := HalfSourceAdaptiveBandCost.constant_nonneg
  unfold constant
  constructor
  · nlinarith only[hr,he]
  · constructor <;> nlinarith only[hr,he]



theorem volume_bounds (N m q : ℕ) :
    0 ≤ volume N m q ∧
    (q:ℝ)*(N:ℝ)^2*(((4:ℝ)^m)^(-G)) ≤ volume N m q ∧
    (q:ℝ)*(N:ℝ)*(((4:ℝ)^m)^E) ≤ volume N m q ∧
    (q:ℝ)*(N:ℝ)*(((4:ℝ)^m)^Eroot) ≤ volume N m q ∧
    (q:ℝ)*(N:ℝ)*(((4:ℝ)^m)^Eroot+((4:ℝ)^m)^E) ≤ volume N m q ∧
    (q:ℝ)*(N:ℝ)*(4:ℝ)^m ≤ volume N m q := by
  have hb : 0 ≤ (q:ℝ)*(N:ℝ)^2*(((4:ℝ)^m)^(-G)) := by positivity
  have he : 0 ≤ (q:ℝ)*(N:ℝ)*(((4:ℝ)^m)^E) := by positivity
  have hr : 0 ≤ (q:ℝ)*(N:ℝ)*(((4:ℝ)^m)^Eroot) := by positivity
  have hf : 0 ≤ (q:ℝ)*(N:ℝ)*(4:ℝ)^m := by positivity
  unfold volume
  constructor
  · positivity
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · nlinarith only[hb,hf]
  · linarith



 theorem polynomial (m W V k : ℕ) (hk : k ≤ 17) (C : ℝ) (_hC : 0 ≤ C) (hCc : C ≤ constant) :
    C*(m+1:ℝ)^k ≤ constant*(W+V+m+20:ℝ)^17 := by
  have hc : 0 ≤ constant := le_trans (by positivity) constant_bounds.1
  have hm : (m+1:ℝ) ≤ (W+V+m+20:ℝ) := by linarith only [Nat.cast_nonneg (α:=ℝ) W,Nat.cast_nonneg (α:=ℝ) V]
  have hp : 1 ≤ (W+V+m+20:ℝ) := by exact_mod_cast (show 1 ≤ W+V+m+20 by omega)
  have hpow := (pow_le_pow_left₀ (show 0 ≤ (m+1:ℝ) by positivity) hm k).trans (pow_le_pow_right₀ hp hk)
  exact mul_le_mul hCc hpow (by positivity) hc



variable {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
  (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f)

private theorem three_products (x y : ℝ) : x*y+x*y+x*y=3*x*y := by ring

attribute [local irreducible] HalfSourceDirectSetup.budget HalfSourceRootSetupCost.budget
  HalfSourceEncodedProduction.budget HalfSourceCapSetup.bitBudget

theorem budget (W V : ℕ) (hm : 32 ≤ p.m) (hB : 1 ≤ CompactBlocks.blockCount n h)
    (hL : p.L=OptimizedFoldedPlan.ordinaryLength p.m)
    (hfit : ThinProductCosts.gridSide p.L p.m ≤ p.N)
    (hdirect : (HalfSourceDirectSetup.budget p.L p.m f.cyclic:ℝ)≤(f.cyclic:ℝ)*(((4:ℝ)^p.m)^(T+E))) :
    (HalfSourceSharedSourceBudget.budget f p W V:ℝ)≤
      8*constant*(W+V+p.m+20:ℝ)^17*(CompactBlocks.blockCount n h:ℝ)*volume p.N p.m f.cyclic := by
  let P : ℝ := (W+V+p.m+20:ℝ)
  let B : ℝ := CompactBlocks.blockCount n h
  let F : ℝ := constant*P^17
  let v := volume p.N p.m f.cyclic
  have hF : 0 ≤ F := by dsimp[F];exact mul_nonneg (le_trans (by positivity) constant_bounds.1) (by positivity)
  have hv := volume_bounds p.N p.m f.cyclic
  have hv0 : 0 ≤ v := hv.1
  have hmL : p.m ≤ p.L := by rw[hL];exact OptimizedFoldedPlan.ordinaryLength_lower _
  have htile := (BackendCostRefinement.tileWidth_comparison p.L p.m).1.trans hfit
  have hpad := TilingCosts.padding_upper p.N (ThinMatrixBackend.tileWidth p.L p.m)
    (ThinMatrixBackend.tileWidth_pos p.L p.m hmL) htile
  have hN : 1 ≤ p.N := (ThinMatrixBackend.tileWidth_pos p.L p.m hmL).trans_le htile
  have hq := f.cyclic_pos
  have hLpoly : (p.L+1:ℝ) ≤ 13*(p.m+1:ℝ) := by
    have hh := HalfSourceRootPolynomials.ordinary_bound p.m
    rw[←hL] at hh
    exact_mod_cast(show p.L+1 ≤ 13*(p.m+1) by omega)
  have direct : (bands f p:ℝ)*(HalfSourceDirectSetup.budget p.L p.m f.cyclic:ℝ)≤F*v := by
    have hx := HalfSourceBandVolume.transfer p.N p.m (lt_of_lt_of_le (by decide : 0 < 32) hm) (by simpa only[←hL] using hfit)
      (f.cyclic:ℝ) _ E (Nat.cast_nonneg _) hdirect
    rw[←hL] at hx
    have hp := polynomial p.m W V 1 (by decide) 416 (by norm_num) (by linarith only [constant_bounds.1])
    calc
      _ ≤32*(p.N:ℝ)*(13*(p.m+1:ℝ))*(f.cyclic:ℝ)*(((4:ℝ)^p.m)^E) := hx.trans (by gcongr)
      _ =(416*(p.m+1:ℝ)^1)*((f.cyclic:ℝ)*(p.N:ℝ)*(((4:ℝ)^p.m)^E)) := by ring
      _ ≤F*v := mul_le_mul hp hv.2.2.1 (by positivity) hF
  have root : (bands f p:ℝ)*(HalfSourceRootSetupCost.budget p.m f.cyclic:ℝ)≤F*v := by
    have hx := HalfSourceRootSetupCost.budget_bands p.N p.m f.cyclic (lt_of_lt_of_le (by decide : 0 < 32) hm) hq (by simpa only[←hL] using hfit)
    rw[←hL] at hx
    have hr : 0 ≤ HalfSourceRootVolume.rootConstant := by unfold HalfSourceRootVolume.rootConstant;positivity
    have hp := polynomial p.m W V 14 (by decide) (10^24*HalfSourceRootVolume.rootConstant) (by positivity)
      (le_trans (mul_le_mul_of_nonneg_right (by norm_num : (10:ℝ)^24 ≤ 10^30) hr) constant_bounds.2.1)
    calc
      _ ≤(10^24*HalfSourceRootVolume.rootConstant)*(f.cyclic:ℝ)*(p.N:ℝ)*(p.m+1:ℝ)^14*(((4:ℝ)^p.m)^Eroot) := by simpa only [show (10:ℝ)^24=1000000000000000000000000 by norm_num,bands] using hx
      _ =((10^24*HalfSourceRootVolume.rootConstant)*(p.m+1:ℝ)^14)*((f.cyclic:ℝ)*(p.N:ℝ)*(((4:ℝ)^p.m)^Eroot)) := by ring
      _ ≤F*v := mul_le_mul hp hv.2.2.2.1 (by positivity) hF
  have encoded : (bands f p:ℝ)*(HalfSourceEncodedProduction.budget p.m f.cyclic:ℝ)≤F*v := by
    have hx := HalfSourceEncodedBandCost.budget_bands p.N p.m f.cyclic hm (by simpa only[←hL] using hfit)
    change _≤_ at hx
    have he := HalfSourceAdaptiveBandCost.constant_nonneg
    have hp := polynomial p.m W V 16 (by decide) (10^27*HalfSourceAdaptiveBandCost.constant) (by positivity)
      (le_trans (mul_le_mul_of_nonneg_right (by norm_num : (10:ℝ)^27 ≤ 10^30) he) constant_bounds.2.2)
    have hLm : HalfSourceAdaptiveFamilyCost.L p.m=p.L := hL.symm
    rw[hLm] at hx
    calc
      _ ≤(10^27*HalfSourceAdaptiveBandCost.constant)*(f.cyclic:ℝ)*(p.N:ℝ)*(p.m+1:ℝ)^16*(((4:ℝ)^p.m)^Eroot+((4:ℝ)^p.m)^E) := by simpa only [show (10:ℝ)^27=1000000000000000000000000000 by norm_num,bands] using hx
      _ =((10^27*HalfSourceAdaptiveBandCost.constant)*(p.m+1:ℝ)^16)*((f.cyclic:ℝ)*(p.N:ℝ)*(((4:ℝ)^p.m)^Eroot+((4:ℝ)^p.m)^E)) := by ring
      _ ≤F*v := mul_le_mul hp hv.2.2.2.2.1 (by positivity) hF
  have common : (bands f p:ℝ)*(HalfSourceSharedSourceBudget.common f p:ℝ)≤3*F*v := by
    have hs := add_le_add (add_le_add direct root) encoded
    have he : F*v+F*v+F*v=3*F*v :=
      three_products F v
    apply le_trans _ (le_of_eq he)
    simpa only [HalfSourceSharedSourceBudget.common,Nat.cast_add,mul_add] using hs
  have folded : (bands f p:ℝ)*(foldedBudget f p W V:ℝ)≤F*v := by
    have hx := HalfSourceFoldedSetupCost.band_formation p.N p.m f.cyclic (lt_of_lt_of_le (by decide : 0 < 32) hm) (by simpa only[←hL] using hfit)
    rw[←hL] at hx
    have hD : (p.D:ℝ) ≤ (4:ℝ)^p.m := by exact_mod_cast p.middle_fit
    have hp0 : 0 ≤ P := by dsimp[P];positivity
    have hp1 : 1 ≤ P := by dsimp[P];exact_mod_cast (show 1 ≤ W+V+p.m+20 from (by decide : 1 ≤ 20).trans (Nat.le_add_left 20 _))
    have hpW : (W+V+10:ℝ) ≤ P := by dsimp[P];linarith only [Nat.cast_nonneg (α:=ℝ) p.m]
    have hpm : (p.m+1:ℝ) ≤ P := by dsimp[P];linarith only [Nat.cast_nonneg (α:=ℝ) W,Nat.cast_nonneg (α:=ℝ) V]
    have hpoly : (6000000000000*416)*(W+V+10:ℝ)^3*(p.m+1:ℝ) ≤ F := by
      calc
        _ ≤(6000000000000*416)*P^3*P := by gcongr
        _ =(6000000000000*416)*P^4 := by ring
        _ ≤constant*P^17 := mul_le_mul (by linarith only [constant_bounds.1]) (pow_le_pow_right₀ hp1 (by decide)) (by positivity) (by linarith only [constant_bounds.1])
    have hscaled := mul_le_mul_of_nonneg_left hx (show 0 ≤ 6000000000000*(W+V+10:ℝ)^3 by positivity)
    unfold foldedBudget
    push_cast
    calc
      _ ≤(bands f p:ℝ)*(6000000000000*(W+V+10:ℝ)^3*(f.cyclic:ℝ)*(p.N:ℝ)*(4:ℝ)^p.m) := by gcongr
      _ ≤((6000000000000*416)*(W+V+10:ℝ)^3*(p.m+1:ℝ))*((f.cyclic:ℝ)*(p.N:ℝ)^2*(((4:ℝ)^p.m)^(-G))) := by
        dsimp only [bands]
        convert hscaled using 1 <;> first | rfl | ring
      _ ≤F*v := mul_le_mul hpoly hv.2.1 (by positivity) hF
  have hsimple : 13000*(f.cyclic:ℝ)*(p.N:ℝ)*(4:ℝ)^p.m ≤ F*v := by
    have hp := polynomial p.m W V 0 (by decide) 13000 (by norm_num) (by linarith only [constant_bounds.1])
    simp only[pow_zero,mul_one] at hp
    have hh := mul_le_mul hp hv.2.2.2.2.2 (by positivity) hF
    simpa only [F,P,v,mul_assoc] using hh
  have hcap : (HalfSourceCapSetup.bitBudget p.m (p.L-p.m):ℝ) ≤ B*F*v := by
    have hc := HalfSourceCapPolynomial.budget_direct p.L p.m f.cyclic hmL hq
    have hS : 1 ≤ bands f p := TilingCosts.bandCount_pos _ _ hN (ThinMatrixBackend.tileWidth_pos p.L p.m hmL)
    have hh : HalfSourceCapSetup.bitBudget p.m (p.L-p.m)≤
      CompactBlocks.blockCount n h*bands f p*HalfSourceDirectSetup.budget p.L p.m f.cyclic := by
      have hs : 1 ≤ CompactBlocks.blockCount n h*bands f p := Nat.mul_pos hB hS
      exact hc.trans (Nat.le_mul_of_pos_left _ hs)
    have hhR : (HalfSourceCapSetup.bitBudget p.m (p.L-p.m):ℝ)≤B*((bands f p:ℝ)*(HalfSourceDirectSetup.budget p.L p.m f.cyclic:ℝ)) := by dsimp[B];exact_mod_cast (by simpa only [Nat.mul_assoc] using hh)
    exact hhR.trans (by simpa only[mul_assoc] using mul_le_mul_of_nonneg_left direct (show 0 ≤ B by dsimp[B];positivity))
  have hspine : ((24*bands f p*CompactBlocks.blockCount n h+8*bands f p+8:ℕ):ℝ)≤B*F*v := by
    have hS : bands f p ≤ 2*p.N := by
      have ht := ThinMatrixBackend.tileWidth_pos p.L p.m hmL
      change bands f p*ThinMatrixBackend.tileWidth p.L p.m≤2*p.N at hpad
      exact (Nat.le_mul_of_pos_right _ ht).trans hpad
    have hs : 24*bands f p*CompactBlocks.blockCount n h+8*bands f p+8 ≤
      CompactBlocks.blockCount n h*(13000*f.cyclic*p.N*4^p.m) := by
      have hqN : p.N ≤ f.cyclic*p.N*4^p.m := by
        have hp : 1 ≤ 4^p.m := Nat.one_le_pow _ _ (by decide)
        nlinarith only[Nat.mul_le_mul_right p.N hq,Nat.mul_le_mul_left (f.cyclic*p.N) hp]
      have h1 := Nat.mul_le_mul_right (24*CompactBlocks.blockCount n h) hS
      have h2 := Nat.mul_le_mul_left 8 hS
      have h3 := Nat.mul_le_mul_right p.N hB
      have h4 := Nat.mul_le_mul_left (CompactBlocks.blockCount n h) hqN
      nlinarith only[h1,h2,h3,h4,hN]
    have hsR : ((24*bands f p*CompactBlocks.blockCount n h+8*bands f p+8:ℕ):ℝ)≤B*(13000*(f.cyclic:ℝ)*(p.N:ℝ)*(4:ℝ)^p.m) := by dsimp[B];exact_mod_cast hs
    exact hsR.trans (by simpa only[mul_assoc] using mul_le_mul_of_nonneg_left hsimple (show 0 ≤ B by dsimp[B];positivity))
  have hmain := mul_le_mul_of_nonneg_left (add_le_add (add_le_add common folded) hsimple) (show 0 ≤ B by dsimp[B];positivity)
  have hf := HalfSourceAssemblyAlgebra.sum_seven
    (HalfSourceCapSetup.bitBudget p.m (p.L-p.m):ℝ)
    (B*((bands f p:ℝ)*(HalfSourceSharedSourceBudget.common f p:ℝ)+
      (bands f p:ℝ)*(foldedBudget f p W V:ℝ)+13000*(f.cyclic:ℝ)*(p.N:ℝ)*(4:ℝ)^p.m))
    ((24*bands f p*CompactBlocks.blockCount n h+8*bands f p+8:ℕ):ℝ) B F v
    hcap hmain hspine (by positivity)
  convert hf using 1
  · unfold HalfSourceSharedSourceBudget.budget
    push_cast
    dsimp only [B]
    ring
  · dsimp only [F,P,B,v]
    simp only [mul_assoc]

#print axioms constant_bounds
#print axioms volume_bounds
#print axioms polynomial
#print axioms budget
end
end ThinMatrix.HalfSourceSharedSourceRate
