import GraphHalfSourceNormalizeCost
import HalfSourceHighQueryCost
import HalfSourceAdaptivePolynomials
import HalfSourceSelectedRootCost

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2200000

/-! A coarse fixed polynomial bounds normalization bit widths. None of the
exponential magnitudes are charged as arithmetic unit costs. -/
namespace ThinMatrix.GraphHalfSourceNormalizeWidth
open ParameterExecution ExactHalfSourcePlan GoodMapEmbedding ResidualFamilyKeys

def width (L m q : ℕ) := L+m+q.size+10

theorem good_width (L m : ℕ) : (goodSlots L m).card.size≤L+1 := by
  have hc : (goodSlots L m).card≤2^L := (Finset.card_le_univ _).trans_eq (by simp)
  exact (Nat.size_le_size hc).trans_eq Nat.size_pow

theorem channel_width (m t : ℕ) : (channelCount m t).size≤2*m+1 := by
  have hc : channelCount m t≤2^(m+m) := by
    unfold channelCount
    split_ifs
    · exact Nat.zero_le _
    · exact HalfSourcePascal.count_le_power _ _
  have hs := Nat.size_le_size hc
  rw [Nat.size_pow] at hs
  omega

theorem translation_width (m : ℕ) : (J m).size≤64*(m+1)^3 := by
  have hj : J m≤64*(m+1)^3 := by
    rw [←count_eq]
    unfold count
    split_ifs with hm
    · subst m;norm_num
    · gcongr;omega
  exact (HalfSourceAdaptivePolynomials.size_le _).trans hj

theorem root_width (L m : ℕ) : (GraphRootProducts.magnitude L m).size≤5*L+4*m+2 := by
  have hs : RetainedRootWindows.slots (L-m)≤L+1 := by
    cases hk : L-m <;> simp only [RetainedRootWindows.slots] <;> omega
  have hss := (HalfSourceAdaptivePolynomials.size_le (RetainedRootWindows.slots (L-m))).trans hs
  have hm := size_mul (RetainedRootWindows.slots (L-m)) (2^(3*(L-m)+L+4*m))
  rw [Nat.size_pow] at hm
  unfold GraphRootProducts.magnitude
  omega

theorem weighted_width (L m t q : ℕ) (ht : t≤2*m) :
    (GraphWeightedRootProducts.magnitude L m q t).size≤10*L+14*m+q.size+9 := by
  let A := GraphRootProducts.magnitude L m
  have ha := root_width L m
  have ho : (CompletedRootProducts.outputLength (m+1)+1).size≤2*m+3 := by
    exact (HalfSourceAdaptivePolynomials.size_le _).trans (by unfold CompletedRootProducts.outputLength;omega)
  have h1 := size_mul (CompletedRootProducts.outputLength (m+1)+1) q
  have h2 := size_pow A 2
  have h3 := size_mul ((CompletedRootProducts.outputLength (m+1)+1)*q) (A^2)
  have h4 := size_mul (2^(2*m)) (CompletedRootProducts.magnitude (m+1) q A)
  have h5 := size_mul t (2^(2*m)*CompletedRootProducts.magnitude (m+1) q A)
  have ht' := HalfSourceAdaptivePolynomials.size_le t
  rw [Nat.size_pow] at h4
  unfold CompletedRootProducts.magnitude at h4 h5
  change A.size≤5*L+4*m+2 at ha
  unfold GraphWeightedRootProducts.magnitude GraphWeightedRootProducts.productMagnitude CompletedRootProducts.magnitude
  change (t*(2^(2*m)*((CompletedRootProducts.outputLength (m+1)+1)*q*A^2))).size≤_
  omega

theorem low_width (L m t q : ℕ) (ht : t≤2*m) :
    (GraphNormalizedBand.lowMagnitude L m t q).size≤256*(width L m q)^3 := by
  let K := (goodSlots L m).card
  let H := channelCount m t
  let A := GraphWeightedRootProducts.magnitude L m q t
  have hk := good_width L m
  have hc := channel_width m t
  have hj := translation_width m
  have hw := weighted_width L m t q ht
  have hrun := HalfSourceAdaptivePolynomials.size_le (2*m+1)
  have h1 := size_mul H A
  have h2 := size_mul (2*m+1) (H*A)
  have h3 := size_mul (J m) ((2*m+1)*(H*A))
  have h4 := size_mul (J m) (J m*((2*m+1)*(H*A)))
  have h5 := size_mul K (J m*(J m*((2*m+1)*(H*A))))
  have h6 := size_mul K (K*(J m*(J m*((2*m+1)*(H*A)))))
  have hb : (GraphNormalizedBand.lowMagnitude L m t q).size≤128*(m+1)^3+12*L+18*m+q.size+13 := by
    change K.size≤L+1 at hk
    change H.size≤2*m+1 at hc
    change A.size≤_ at hw
    unfold GraphNormalizedBand.lowMagnitude GraphLowMaskAssembly.pairMagnitude
    change (K*(K*(J m*(J m*((2*m+1)*(H*A)))))).size≤_
    omega
  have hP : 1≤width L m q := by unfold width;omega
  have hm : m+1≤width L m q := by unfold width;omega
  have hp := le_self_pow₀ hP (show (3:ℕ)≠0 by decide)
  have hm3 := Nat.pow_le_pow_left hm 3
  have hs : 12*L+18*m+q.size+13≤18*width L m q := by unfold width;omega
  nlinarith only [hb,hp,hm3,hs]

theorem high_width (L m t q : ℕ) (ht : t≤2*m) :
    (GraphNormalizedBand.highMagnitude L m t q).size≤256*(width L m q)^3 := by
  let A := GraphHighRun.magnitude L m t q
  have hw := HalfSourceHighQueryCost.query_width L m t q ht
  change A.size≤20*width L m q at hw
  have hj := translation_width m
  have hrun := HalfSourceAdaptivePolynomials.size_le (2*m+1)
  have h1 := size_mul (2*m+1) A
  have h2 := size_mul (J m) ((2*m+1)*A)
  have h3 := size_mul (J m) (J m*((2*m+1)*A))
  have hb : (GraphNormalizedBand.highMagnitude L m t q).size≤128*(m+1)^3+2*m+1+20*width L m q := by
    unfold GraphNormalizedBand.highMagnitude
    change (J m*(J m*((2*m+1)*A))).size≤_
    omega
  have hP : 1≤width L m q := by unfold width;omega
  have hm : m+1≤width L m q := by unfold width;omega
  have hp := le_self_pow₀ hP (show (3:ℕ)≠0 by decide)
  have hm3 := Nat.pow_le_pow_left hm 3
  have hs : 2*m+1≤2*width L m q := by unfold width;omega
  nlinarith only [hb,hp,hm3,hs]

theorem cell_width (L m t q : ℕ) (ht : t≤2*m) :
    BinaryLowHighNormalize.width L (GraphNormalizedBand.lowMagnitude L m t q)
      (GraphNormalizedBand.highMagnitude L m t q)≤520*(width L m q)^3 := by
  have hl := low_width L m t q ht
  have hh := high_width L m t q ht
  have ha := HalfSourceSelectedRootCost.add_size (GraphNormalizedBand.lowMagnitude L m t q)
    (GraphNormalizedBand.highMagnitude L m t q)
  have hP : 1≤width L m q := by unfold width;omega
  have hp := le_self_pow₀ hP (show (3:ℕ)≠0 by decide)
  have hs : 2*L+4≤4*width L m q := by unfold width;omega
  unfold BinaryLowHighNormalize.width
  omega

theorem cell_budget (L m t q : ℕ) (ht : t≤2*m) :
    BinaryLowHighNormalize.cellBudget L (GraphNormalizedBand.lowMagnitude L m t q)
      (GraphNormalizedBand.highMagnitude L m t q)≤1000000000*(width L m q)^6 := by
  have hw := cell_width L m t q ht
  have hP : 1≤width L m q := by unfold width;omega
  have hp : 1≤(width L m q)^3 := one_le_pow₀ hP
  unfold BinaryLowHighNormalize.cellBudget BackendScalarBits.backendScalarUnit BackendScalarBits.scalarUnit
  calc
    _ ≤ 8*(100*(521*(width L m q)^3)^2)+1024*(521*(width L m q)^3)^2 := by gcongr <;> omega
    _ ≤ _ := by nlinarith only [Nat.zero_le ((width L m q)^6)]

theorem normalized_bits {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) :
    GraphHalfSourceNormalizeCost.bitsBudget f p≤
      1000000000*(FoldedBackendExecution.windowQuerySize n*CompactBlocks.blockCount n h+1)*
        (width p.L p.m f.cyclic)^7 := by
  let P := width p.L p.m f.cyclic
  let M := FoldedBackendExecution.windowQuerySize n
  let B := CompactBlocks.blockCount n h
  have hP : 1≤P := by dsimp [P,width];omega
  have hL : p.L≤P := by dsimp [P,width];omega
  have hsmall : 2*p.L+4≤4*P := by dsimp [P,width];omega
  have hs : BackendScalarBits.backendScalarUnit (2*p.L+3)≤12800*P^2 := by
    unfold BackendScalarBits.backendScalarUnit BackendScalarBits.scalarUnit
    calc
      _ ≤ 8*(100*(4*P)^2) := by gcongr
      _ = _ := by ring
  have hc := cell_budget p.L p.m p.t f.cyclic p.t_le
  change _≤1000000000*P^6 at hc
  have h6 : P^6≤P^7 := Nat.pow_le_pow_right hP (by decide)
  have h3 : P^3≤P^7 := Nat.pow_le_pow_right hP (by decide)
  have ha := Nat.mul_le_mul hL hs
  have hb := Nat.mul_le_mul_left (M*B) hc
  have hd := Nat.mul_le_mul_left (1000000000*M*B) h6
  unfold GraphHalfSourceNormalizeCost.bitsBudget GraphHalfSourceNormalizeCost.lowMagnitude GraphHalfSourceNormalizeCost.highMagnitude
  change p.L*BackendScalarBits.backendScalarUnit (2*p.L+3)+M*(B*_ )≤1000000000*(M*B+1)*P^7
  nlinarith only [ha,hb,hd,h3]

#print axioms cell_width
#print axioms cell_budget
#print axioms normalized_bits
#print axioms good_width
#print axioms channel_width
#print axioms translation_width
#print axioms root_width
#print axioms weighted_width
#print axioms low_width
#print axioms high_width
end ThinMatrix.GraphHalfSourceNormalizeWidth
