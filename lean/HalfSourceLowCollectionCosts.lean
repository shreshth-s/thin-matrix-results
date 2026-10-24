import HalfSourceLowProductCosts

/-! Actual scalar LOW family accumulation over J² runs and channels.
The only child-cost quantity is the sum of actual retained root counters. -/
namespace ThinMatrix.HalfSourceLowCollectionCosts
open BinaryCell BinaryGroupedCoordinates ExactHalfSourcePlan ResidualFamilyKeys
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 8000
variable {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
  (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f)

 def extra (W A : ℕ) : ℕ :=
  let M := FoldedBackendExecution.windowQuerySize n
  let B := CompactBlocks.blockCount n h
  let T := GraphOwnLowCollection.T f p
  T*(HalfSourceLowProductCosts.extra f p W A+99)+36+
    M*(T*(B*BackendScalarBits.backendScalarUnit (T*(p.t*(W*SelectedRootProduct.productMagnitude f.cyclic p.t A))).size)+
      T*(40*B+40)+3*B+47)

variable (ws : Vector Cell p.t) (channels : Vector (Channel p.m) (channelCount p.m p.t))
  (requests : GraphOwnRootProduct.Requests f p) (roots : GraphOwnLowProgram.RootFamily f p)

 def rootWork (price : ℕ) (s : Fin (GraphOwnLowCollection.T f p)) : ℕ :=
  let a := finProdFinEquiv.symm s
  let b := finProdFinEquiv.symm a.2
  let c := finProdFinEquiv.symm b.2
  (roots a.1 b.1 c.1 c.2 false).bitSteps+price*(roots a.1 b.1 c.1 c.2 false).control+
  ((roots a.1 b.1 c.1 (ResidualChannelTranspose.locate channels c.2).value true).bitSteps+
    price*(roots a.1 b.1 c.1 (ResidualChannelTranspose.locate channels c.2).value true).control)

 theorem actual_price (W A price : ℕ) (hB : 1 ≤ CompactBlocks.blockCount n h)
    (hw : ∀ d,(view (ws.get d)).natAbs≤W)
    (hr : ∀ u v run c side,SelectedRootRows.RowsBound A (roots u v run c side).value) :
    (GraphOwnLowProgram.execute f p ws channels requests roots).bitSteps+
      price*(GraphOwnLowProgram.execute f p ws channels requests roots).control ≤
      (∑ s,rootWork f p channels roots price s)+(price+1)*extra f p W A := by
  let family := GraphOwnLowProgram.channel f p ws channels requests roots
  let child := GraphOwnLowCollection.child f p family
  let T := GraphOwnLowCollection.T f p
  let M := FoldedBackendExecution.windowQuerySize n
  let B := CompactBlocks.blockCount n h
  let mag := p.t*(W*SelectedRootProduct.productMagnitude f.cyclic p.t A)
  have hb := GraphOwnLowCollection.bits f p family mag (fun s => (child s).bitSteps)
    (fun s j b => HalfSourceLowProductCosts.channel_bound f p ws channels requests roots _ _ _ _ W A hw hr j b)
    (fun _ => le_rfl)
  have hc := GraphOwnLowCollection.control f p family (fun s => (child s).control) (fun _ => le_rfl)
  have hchild (s : Fin T) : (child s).bitSteps+price*(child s).control ≤
      rootWork f p channels roots price s+(price+1)*(HalfSourceLowProductCosts.extra f p W A+64) := by
    have hh := HalfSourceLowProductCosts.channel_price f p ws channels requests roots
      (finProdFinEquiv.symm s).1 (finProdFinEquiv.symm (finProdFinEquiv.symm s).2).1
      (finProdFinEquiv.symm (finProdFinEquiv.symm (finProdFinEquiv.symm s).2).2).1
      (finProdFinEquiv.symm (finProdFinEquiv.symm (finProdFinEquiv.symm s).2).2).2 W A price hB hw hr
    change _ ≤ _ at hh
    dsimp only[child,GraphOwnLowCollection.child,family,rootWork]
    nlinarith only[hh]
  have hs := Finset.sum_le_sum (fun s (_ : s∈Finset.univ) => hchild s)
  simp only[Finset.sum_add_distrib,←Finset.mul_sum,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hs
  have hp := Nat.mul_le_mul_left price hc
  unfold RootProductCollection.bitBudget at hb
  unfold RootProductCollection.controlBudget GraphPrefixProgram.sumControl at hp
  simp only[Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hp
  change _ ≤ _ at hb hp
  change _ ≤ _ at hs
  dsimp only[GraphOwnLowProgram.execute]
  change _ ≤ (∑ s,rootWork f p channels roots price s)+(price+1)*extra f p W A
  unfold extra
  change _ ≤ (∑ s,rootWork f p channels roots price s)+(price+1)*
    (T*(HalfSourceLowProductCosts.extra f p W A+99)+36+
      M*(T*(B*BackendScalarBits.backendScalarUnit (T*mag).size)+T*(40*B+40)+3*B+47))
  have hm0 : 0 ≤ M*(T*(B*BackendScalarBits.backendScalarUnit (T*mag).size)) := Nat.zero_le _
  have hex0 : 0 ≤ 35*T+36+M*(T*(40*B+40)+3*B+47) := Nat.zero_le _
  have hpx : 0 ≤ price*(M*(T*(B*BackendScalarBits.backendScalarUnit (T*mag).size))) := Nat.zero_le _
  change (GraphOwnLowCollection.execute f p family).bitSteps+
    price*(GraphOwnLowCollection.execute f p family).control ≤ _
  change (GraphOwnLowCollection.execute f p family).bitSteps ≤
    (∑ s,(child s).bitSteps)+M*(T*(B*BackendScalarBits.backendScalarUnit (T*mag).size)) at hb
  change price*(GraphOwnLowCollection.execute f p family).control ≤
    price*((∑ s,(child s).control)+T*32+8+(M*(T*(40*B+40)+3*B+44)+8)+3*M+12+3*T+8) at hp
  nlinarith only [hb,hp,hs,hm0,hex0,hpx]

#print axioms actual_price
end ThinMatrix.HalfSourceLowCollectionCosts
