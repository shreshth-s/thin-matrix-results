import HalfSourceTargetVolume

set_option autoImplicit false
set_option maxHeartbeats 3500000
set_option maxRecDepth 10000
namespace ThinMatrix.HalfSourceTargetActualCost
open HalfSourceParameters
open HalfSourceAdaptiveFamilyCost (L t)
noncomputable section

theorem budget (N m B M W V : ℕ) (hm : 0 < m) (hB : 1≤B)
    (hfit : ThinProductCosts.gridSide (L m) m≤N) :
    let S := TilingCosts.bandCount N (ThinMatrixBackend.tileWidth (L m) m)
    let P := (HalfSourceTargetPolynomial.width S (L m) m (t m) W V:ℝ)
    (HalfSourceTargetSetupCost.extraBudget S B (L m) m (t m) M W V:ℝ)≤
      1000000000000000*P^7*((B:ℝ)*((N:ℝ)*(((4:ℝ)^m)^E)+(N:ℝ)^2*(((4:ℝ)^m)^(-G)))+
        (M:ℝ)*(((4:ℝ)^m)^q2)) := by
  let S := TilingCosts.bandCount N (ThinMatrixBackend.tileWidth (L m) m)
  let P := (HalfSourceTargetPolynomial.width S (L m) m (t m) W V:ℝ)
  have hP : 1≤P := by dsimp only[P];exact_mod_cast (show 1≤HalfSourceTargetPolynomial.width S (L m) m (t m) W V by unfold HalfSourceTargetPolynomial.width;omega)
  have hmP : (m+1:ℝ)≤P := by dsimp only[P];exact_mod_cast (show m+1≤HalfSourceTargetPolynomial.width S (L m) m (t m) W V by unfold HalfSourceTargetPolynomial.width;omega)
  have hp : (HalfSourceTargetSetupCost.extraBudget S B (L m) m (t m) M W V:ℝ)≤
      10000000000*P^6*(HalfSourceTargetPolynomial.volume S B (L m) m (t m) M:ℝ) := by
    dsimp only[P]
    exact_mod_cast HalfSourceTargetPolynomial.extras S B (L m) m (t m) M W V
  have hv := HalfSourceTargetVolume.volume_bound N m B M hm hB hfit
  have hs := mul_le_mul_of_nonneg_left hv (show 0≤10000000000*P^6 by positivity)
  have h6 : P^6≤P^7 := pow_le_pow_right₀ hP (by decide)
  let A := (B:ℝ)*((N:ℝ)*(((4:ℝ)^m)^E)+(N:ℝ)^2*(((4:ℝ)^m)^(-G)))
  let Qr := (M:ℝ)*(((4:ℝ)^m)^q2)
  have ha : 0≤A := by dsimp[A];positivity
  have hq : 0≤Qr := by dsimp[Qr];positivity
  have hh : 300000000000000*P^6*(m+1:ℝ)*A≤300000000000000*P^7*A := by
    calc
      _ ≤300000000000000*P^6*P*A := by gcongr
      _ = _ := by ring
  have hquery := mul_le_mul_of_nonneg_right h6 (show 0≤10000000000*Qr by positivity)
  change (HalfSourceTargetSetupCost.extraBudget S B (L m) m (t m) M W V:ℝ)≤1000000000000000*P^7*(A+Qr)
  change (HalfSourceTargetPolynomial.volume S B (L m) m (t m) M:ℝ)≤_ at hv
  change 10000000000*P^6*(HalfSourceTargetPolynomial.volume S B (L m) m (t m) M:ℝ)≤_ at hs
  have hs' : 10000000000*P^6*(HalfSourceTargetPolynomial.volume S B (L m) m (t m) M:ℝ)≤
      300000000000000*P^6*(m+1:ℝ)*A+10000000000*P^6*Qr := by
    dsimp[A,Qr]
    nlinarith only [hs]
  nlinarith only [hp,hs',hh,hquery,mul_nonneg (show 0≤P^7 by positivity) ha,
    mul_nonneg (show 0≤P^7 by positivity) hq]

theorem actual {n h r W V : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (hm : p.m≤p.L-p.m)
    (input : BinaryFoldedFormation.Inputs n)
    (hb : BinaryFoldedFormationCost.MetadataBound n h (FoldedBackendExecution.physicalFold f) f.cyclic 0 V)
    (htarget : ∀ i j,(BinaryCell.view ((input.target.get i).get j)).natAbs.size≤W)
    (hm0 : 0 < p.m) (hB : 1≤CompactBlocks.blockCount n h)
    (hL : p.L=L p.m) (ht : p.t=t p.m) (hfit : ThinProductCosts.gridSide p.L p.m≤p.N) :
    let S := GraphHalfSourceSetup.S f p
    let B := CompactBlocks.blockCount n h
    let M := FoldedBackendExecution.windowQuerySize n
    let P := (HalfSourceTargetPolynomial.width S p.L p.m p.t W V:ℝ)
    ((GraphHalfSourceSetup.execute f p hm input).operations:ℝ)≤
      ((GraphSharedSourceProduction.execute f p hm input (S:=S)).operations:ℝ)+
      1000000000000000*P^7*((B:ℝ)*((p.N:ℝ)*(((4:ℝ)^p.m)^E)+(p.N:ℝ)^2*(((4:ℝ)^p.m)^(-G)))+
        (M:ℝ)*(((4:ℝ)^p.m)^q2)) := by
  have hn := HalfSourceTargetSetupCost.execute f p hm input hb htarget
  have hnR : ((GraphHalfSourceSetup.execute f p hm input).operations:ℝ)≤
      ((GraphSharedSourceProduction.execute f p hm input (S:=GraphHalfSourceSetup.S f p)).operations:ℝ)+
      (HalfSourceTargetSetupCost.extraBudget (GraphHalfSourceSetup.S f p) (CompactBlocks.blockCount n h)
        p.L p.m p.t (FoldedBackendExecution.windowQuerySize n) W V:ℝ) := by exact_mod_cast hn
  have hx := budget p.N p.m (CompactBlocks.blockCount n h) (FoldedBackendExecution.windowQuerySize n) W V hm0 hB
    (by simpa only [hL] using hfit)
  rw [←hL,←ht] at hx
  exact hnR.trans (add_le_add (le_refl _) hx)

#print axioms budget
#print axioms actual
end
end ThinMatrix.HalfSourceTargetActualCost
