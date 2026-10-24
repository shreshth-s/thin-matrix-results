import GraphOwnBankCopyRate

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 10000
namespace ThinMatrix.GraphOwnBandCompleteRate
open BinaryCell BinaryGroupedCoordinates GraphAdaptiveRootBatch GraphOwnBandPriced
open GraphOwnBandTypeRate SharedCompletionRate
open scoped BigOperators

/-- Actual per-type production including all bank copies. There is no
remaining running-time premise or separate source-bank term. -/
theorem exists_complete_rate : ∃ scheme : RectangularBatch.Scheme,
    ∃ hnum : scheme.num=861, ∃ hden : scheme.den=500, ∃ hz : scheme.z=15,
    scheme.Valid ∧ ∃ K : ℝ, 0 < K ∧
    ∀ n h r S : ℕ, ∀ f : CompactBlocks.PhysicalFactorization r,
    ∀ p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f,
    ∀ hm : p.m ≤ p.L-p.m, ∀ input : BinaryFoldedFormation.Inputs n,
    ∀ base : Index f p, ∀ hD : 0 < D f p base,
    ∀ stored : GraphOwnBandPreparation.Stores f p (S:=S),
    ∀ hc : ∀ a : Fin S,GraphAdaptiveBatchSources.Correct f p hm input a.val a.val (stored.get a),
    ∀ targets : GraphOwnBandTargets.Prepared f p (S:=S),
    ∀ hb : ∀ i,(targets.requests.get i).bandL<S ∧ (targets.requests.get i).bandR<S,
    GraphOwnBandTargets.tree f p targets base.right=(GraphOwnBandRouter.run base.right targets.requests hb).value →
    ∀ price L : ℕ, Fits f p base scheme targets L →
    let out := GraphOwnBandTargets.execute f p input hm base scheme hnum hden hz hD stored hc targets
    (out.bitSteps+price*out.control:ℝ) ≤ K*(price+1)*W f p*(L:ℝ)^5*((M (n:=n):ℝ)*Q f p*(D f p base:ℝ)^beta+
        (G f p (S:=S):ℝ)*F f p base*Q f p*(D f p base:ℝ)^gamma) := by
  obtain ⟨scheme,hnum,hden,hz,hvalid,K,hK,hcost⟩ := GraphOwnBandTypeRate.exists_type_rate
  refine ⟨scheme,hnum,hden,hz,hvalid,K+4000,by positivity,?_⟩
  intro n h r S f p hm input base hD stored hc targets hb htree price L fits
  dsimp only
  let br := GraphOwnBandPreparation.banks f p hm input base stored hc
  let s := D f p base
  let F0 := F f p base
  let V0 := (M (n:=n):ℝ)*Q f p*(s:ℝ)^beta+(G f p (S:=S):ℝ)*F0*Q f p*(s:ℝ)^gamma
  have hW : 1 ≤ W f p := by
    dsimp only [W]
    cases p.L-p.m <;> simp [RetainedRootWindows.slots]
  have hF : 1 ≤ F0 := by change 0 < F0;dsimp [F0,F];positivity
  have hQ : 1 ≤ Q f p := (SharedCompletionTile.dimensions s hD).2.1.trans_le fits.batch
  have hB : 1 ≤ CompactBlocks.blockCount n h := by
    by_contra hx
    have he : CompactBlocks.blockCount n h=0 := by omega
    simp only [Q,GraphOwnBandCollection.C,he,zero_mul] at hQ
    omega
  have hL : 1 ≤ L := by have hh := fits.dimension;omega
  have hP : GraphOwnBankCopyCosts.P f p base+1 ≤ L := by
    have hh := fits.dimension
    have hd := WindowPrefixProgram.dimension (p.L-p.m) (E f p base)
    change WindowPrefixProgram.prefixLength (p.L-p.m) (E f p base)+1 ≤ L
    omega
  have hlen : GraphOwnBankCopyCosts.len f p base+1 ≤ L := by
    have hh := fits.dimension
    have hd := WindowPrefixProgram.dimension (p.L-p.m) (E f p base)
    change WindowPrefixProgram.length (p.L-p.m) (E f p base)+1 ≤ L
    omega
  have hk : p.L-p.m ≤ L := by have hh := fits.dimension;omega
  have hH : (H f p base).size+1 ≤ L := by have hh := fits.valueWidth;omega
  have hwidth : (G f p (S:=S)).size ≤ L := by have hh := fits.groupWidth;omega
  have hb' := GraphOwnBankCopyCosts.banks_bits f p base hm input stored hc
  have hc' := GraphOwnBankCopyCosts.banks_control f p base hm input stored hc hB
  have hbcopy : br.bitSteps ≤ G f p (S:=S)*W f p*Q f p*F0*s*
      BackendScalarBits.backendScalarUnit (H f p base).size := by
    simpa only [br,GraphOwnBankCopyCosts.bits,GraphOwnBankCopyCosts.V,GraphOwnBankCopyCosts.H,
      GraphOwnBankCopyCosts.P,GraphOwnBankCopyCosts.len,GraphOwnBankCopyCosts.cap,HalfSourcePrefixVolume.groups,
      G,Q,GraphOwnBandCollection.C,F0,F,s,D,WindowSharedCompletion.D,H,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using hb'
  have hccopy : br.control ≤ G f p (S:=S)*(W f p*(Q f p*F0*s*
      HalfSourceBatchCopyVolume.batchControlUnit (GraphOwnBankCopyCosts.P f p base) (GraphOwnBankCopyCosts.len f p base))+
      W f p*(256*(p.L-p.m)+99)+32+64*(G f p (S:=S)).size^2+64)+8 := by
    simpa only [br,GraphOwnBankCopyCosts.control,GraphOwnBankCopyCosts.V,
      GraphOwnBankCopyCosts.P,GraphOwnBankCopyCosts.len,GraphOwnBankCopyCosts.cap,HalfSourcePrefixVolume.groups,
      G,Q,GraphOwnBandCollection.C,F0,F,s,D,WindowSharedCompletion.D,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using hc'
  have hcopy := GraphOwnBankCopyRate.rate (G f p (S:=S)) (W f p) (Q f p) F0 s
    (GraphOwnBankCopyCosts.P f p base) (GraphOwnBankCopyCosts.len f p base) (p.L-p.m)
    (H f p base).size L price br.bitSteps br.control fits.groups hW hQ hF hD hL hP hlen hk hH hwidth hbcopy hccopy
  have hall := hcost n h r S f p hm input base hD stored hc targets hb htree price L fits
  change _ ≤ (br.bitSteps+price*br.control:ℝ)+K*(price+1)*W f p*(L:ℝ)^5*V0 at hall
  have hquery : 0 ≤ (M (n:=n):ℝ)*Q f p*(s:ℝ)^beta := by positivity
  have hextra : (G f p (S:=S):ℝ)*F0*Q f p*(s:ℝ)^gamma ≤ V0 := by dsimp [V0];linarith
  have hscale := mul_le_mul_of_nonneg_left hextra (show 0 ≤ (4000:ℝ)*(price+1)*W f p*(L:ℝ)^5 by positivity)
  change _≤(K+4000)*(price+1)*W f p*(L:ℝ)^5*V0
  nlinarith only [hall,hcopy,hscale]

#print axioms exists_complete_rate
end ThinMatrix.GraphOwnBandCompleteRate
