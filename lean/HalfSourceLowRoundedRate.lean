import HalfSourceLowProductionCost

/-! Convert the completely priced LOW execution envelope to the rounded
query/source monomials. The full cyclic dimension is retained once. -/
namespace ThinMatrix.HalfSourceLowRoundedRate
open HalfSourceParameters HalfSourceAdaptiveFamilyCost
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
noncomputable section
variable {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
  (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f)

 def width (Lw : ℕ) := Lw+p.L+p.m+f.cyclic.size+2
 def coefficient (K : ℝ) := K*HalfSourceCompletionTotal.constant+1000000000000*20^11
 def envelope (K : ℝ) (price Lw : ℕ) : ℝ :=
   2*K*(price+1)*(GraphAdaptiveRootBatch.W f p:ℝ)*(Lw:ℝ)^5*(GraphOwnBandPriced.Q f p:ℝ)*
     (HalfSourceRootFamilyCosts.multiplicity p.m:ℝ)*
       HalfSourceLowTypeVolume.volume p.L p.m p.t
         (TilingCosts.bandCount p.N (ThinMatrixBackend.tileWidth p.L p.m)) (FoldedBackendExecution.windowQuerySize n)+
     (price+1)*(HalfSourceLowCollectionCosts.extra f p (2^(2*p.m))
       (HalfSourceLowProductCosts.rootMagnitude f p):ℝ)

 theorem bound (K : ℝ) (hK : 0≤K) (price Lw : ℕ)
    (hL : p.L=OptimizedFoldedPlan.ordinaryLength p.m)
    (ht : p.t=OptimizedFoldedPlan.channelLength p.m) (hm : 32 ≤ p.m)
    (hB : 1≤CompactBlocks.blockCount n h) (hfit : ThinProductCosts.gridSide p.L p.m≤p.N) :
    envelope f p K price Lw≤coefficient K*(price+1)*(width f p Lw:ℝ)^19*
      ((CompactBlocks.blockCount n h:ℝ)*f.cyclic*
        ((FoldedBackendExecution.windowQuerySize n:ℝ)*(((4:ℝ)^p.m)^q1)+(p.N:ℝ)*(((4:ℝ)^p.m)^E))+(4:ℝ)^p.m) := by
  let X : ℝ := (CompactBlocks.blockCount n h:ℝ)*f.cyclic*
    ((FoldedBackendExecution.windowQuerySize n:ℝ)*(((4:ℝ)^p.m)^q1)+(p.N:ℝ)*(((4:ℝ)^p.m)^E))
  let Y : ℝ := (4:ℝ)^p.m
  let V : ℝ := width f p Lw
  have hV : 1≤V := by dsimp[V,width];push_cast;linarith [Nat.cast_nonneg (α:=ℝ) Lw, Nat.cast_nonneg (α:=ℝ) p.L, Nat.cast_nonneg (α:=ℝ) p.m, Nat.cast_nonneg (α:=ℝ) f.cyclic.size]
  have hLv : (Lw:ℝ)≤V := by dsimp[V,width];push_cast;linarith [Nat.cast_nonneg (α:=ℝ) Lw, Nat.cast_nonneg (α:=ℝ) p.L, Nat.cast_nonneg (α:=ℝ) p.m, Nat.cast_nonneg (α:=ℝ) f.cyclic.size]
  have hmv : (p.m+1:ℝ)≤V := by dsimp[V,width];push_cast;linarith [Nat.cast_nonneg (α:=ℝ) Lw, Nat.cast_nonneg (α:=ℝ) p.L, Nat.cast_nonneg (α:=ℝ) p.m, Nat.cast_nonneg (α:=ℝ) f.cyclic.size]
  have hdv : (p.L+p.m+f.cyclic.size+1:ℝ)≤V := by dsimp[V,width];push_cast;linarith [Nat.cast_nonneg (α:=ℝ) Lw, Nat.cast_nonneg (α:=ℝ) p.L, Nat.cast_nonneg (α:=ℝ) p.m, Nat.cast_nonneg (α:=ℝ) f.cyclic.size]
  have hpoly1 : (Lw:ℝ)^5*(p.m+1:ℝ)^14≤V^19 := by
    calc
      _≤V^5*V^14 := by gcongr
      _=_ := by ring
  have hpoly2 : (p.L+p.m+f.cyclic.size+1:ℝ)^11*(p.m+1:ℝ)^2≤V^19 := by
    calc
      _≤V^11*V^2 := by gcongr
      _=V^13 := by ring
      _≤V^19 := pow_le_pow_right₀ hV (by decide)
  have hv := HalfSourceLowTypeVolume.total p.N p.m (FoldedBackendExecution.windowQuerySize n)
    (CompactBlocks.blockCount n h) f.cyclic hm (by simpa only[←hL] using hfit)
  have hv' := mul_le_mul_of_nonneg_left hv (show 0≤K*(price+1)*(Lw:ℝ)^5 by positivity)
  have hmain :
      2*K*(price+1)*(GraphAdaptiveRootBatch.W f p:ℝ)*(Lw:ℝ)^5*(GraphOwnBandPriced.Q f p:ℝ)*
        (HalfSourceRootFamilyCosts.multiplicity p.m:ℝ)*
        HalfSourceLowTypeVolume.volume p.L p.m p.t
          (TilingCosts.bandCount p.N (ThinMatrixBackend.tileWidth p.L p.m)) (FoldedBackendExecution.windowQuerySize n)≤
      K*HalfSourceCompletionTotal.constant*(price+1)*V^19*X := by
    have hh : 2*K*(price+1)*(GraphAdaptiveRootBatch.W f p:ℝ)*(Lw:ℝ)^5*(GraphOwnBandPriced.Q f p:ℝ)*
        (HalfSourceRootFamilyCosts.multiplicity p.m:ℝ)*
        HalfSourceLowTypeVolume.volume p.L p.m p.t
          (TilingCosts.bandCount p.N (ThinMatrixBackend.tileWidth p.L p.m)) (FoldedBackendExecution.windowQuerySize n)≤K*HalfSourceCompletionTotal.constant*(price+1)*
        ((Lw:ℝ)^5*(p.m+1:ℝ)^14)*X := by
      convert hv' using 1 <;>
        (try simp only[HalfSourceCompletionVolume.repetitions,GraphAdaptiveRootBatch.W,GraphOwnBandPriced.Q,
          GraphOwnBandCollection.C,hL,ht,L,t,Nat.cast_mul,Nat.cast_ofNat,X]) <;> first | rfl | ring
    exact hh.trans (by have hc := HalfSourceCompletionTotal.constant_pos.le; gcongr)
  have he := HalfSourceLowExtraVolume.extra_rate f p ht (by omega) hB (2^(2*p.m)) (HalfSourceLowProductCosts.rootMagnitude f p)
  have hw := HalfSourceLowExtraVolume.canonical_width f p
  have hwR : (HalfSourceLowExtraPolynomials.width f p (2^(2*p.m)) (HalfSourceLowProductCosts.rootMagnitude f p):ℝ)≤
      20*(p.L+p.m+f.cyclic.size+1:ℝ) := by exact_mod_cast hw
  have he' : (HalfSourceLowCollectionCosts.extra f p (2^(2*p.m)) (HalfSourceLowProductCosts.rootMagnitude f p):ℝ)≤
      (1000000000000*20^11)*V^19*(X+Y) := by
    have hh : (FoldedBackendExecution.windowQuerySize n:ℝ)*CompactBlocks.blockCount n h*f.cyclic*(((4:ℝ)^p.m)^q1)+(4:ℝ)^p.m≤X+Y := by
      dsimp[X,Y]
      nlinarith only [show 0≤(CompactBlocks.blockCount n h:ℝ)*f.cyclic*(p.N:ℝ)*(((4:ℝ)^p.m)^E) by positivity]
    calc
      _ ≤1000000000000*(20*(p.L+p.m+f.cyclic.size+1:ℝ))^11*(p.m+1:ℝ)^2*(X+Y) := by
        exact he.trans (by gcongr)
      _ =(1000000000000*20^11)*((p.L+p.m+f.cyclic.size+1:ℝ)^11*(p.m+1:ℝ)^2)*(X+Y) := by ring
      _ ≤_ := by gcongr
  unfold envelope
  change _ ≤coefficient K*(price+1)*V^19*(X+Y)
  have hp := mul_le_mul_of_nonneg_left he' (show 0≤(price+1:ℝ) by positivity)
  have hx : 0≤K*HalfSourceCompletionTotal.constant*(price+1)*V^19*Y := by
    have := HalfSourceCompletionTotal.constant_pos.le
    positivity
  unfold coefficient
  nlinarith only[hmain,hp,hx]

#print axioms bound
end
end ThinMatrix.HalfSourceLowRoundedRate
