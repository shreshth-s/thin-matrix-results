import GraphHalfSourceNormalizeWidth

set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace ThinMatrix.GraphHalfSourceOutputCost
variable {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
  (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f)

def width : ℕ := p.L+p.m+f.cyclic.size+(EndToEndAPSP.incidenceSize n h).size+h.size+12

noncomputable def extra (price : ℕ) : ℕ :=
  GraphHalfSourceNormalizeCost.bitsBudget f p+
  EndToEndAPSP.incidenceSize n h*BackendScalarBits.backendScalarUnit h.size+
  (price+1)*(16*FoldedBackendExecution.windowQuerySize n+48+GraphHalfSourceNormalizeCost.controlBudget f p+
    EndToEndAPSP.incidenceSize n h*(64*(EndToEndAPSP.incidenceSize n h).size^2+54)+21)

theorem incidence_eq : EndToEndAPSP.incidenceSize n h=
    FoldedBackendExecution.windowQuerySize n*CompactBlocks.blockCount n h := by
  unfold EndToEndAPSP.incidenceSize FoldedBackendExecution.windowQuerySize
  ring

theorem extra_polynomial (price : ℕ) (hB : 1≤CompactBlocks.blockCount n h) :
    extra f p price≤10000000000*(price+1)*(EndToEndAPSP.incidenceSize n h+1)*(width f p)^7 := by
  let P := width f p
  let I := EndToEndAPSP.incidenceSize n h
  let M := FoldedBackendExecution.windowQuerySize n
  let B := CompactBlocks.blockCount n h
  have hP : 1≤P := by dsimp [P,width];omega
  have hL : p.L≤P := by dsimp [P,width];omega
  have hh : h.size+1≤P := by dsimp [P,width];omega
  have hI : I.size≤P := by dsimp [I,P,width];omega
  have hW : GraphHalfSourceNormalizeWidth.width p.L p.m f.cyclic≤P := by
    dsimp [P,width,GraphHalfSourceNormalizeWidth.width];omega
  have he : I=M*B := incidence_eq (n:=n) (h:=h)
  have hM : M≤I := he ▸ Nat.le_mul_of_pos_right M hB
  have hp2 : 1≤P^2 := one_le_pow₀ hP
  have hp7 : 1≤P^7 := one_le_pow₀ hP
  have h2 : P^2≤P^7 := Nat.pow_le_pow_right hP (by decide)
  have h1 : P≤P^2 := le_self_pow₀ hP (by decide)
  have hn : GraphHalfSourceNormalizeCost.bitsBudget f p≤1000000000*(I+1)*P^7 := by
    have hn := GraphHalfSourceNormalizeWidth.normalized_bits f p
    rw [←incidence_eq (n:=n) (h:=h)] at hn
    exact hn.trans (by gcongr)
  have hs : BackendScalarBits.backendScalarUnit h.size≤800*P^2 := by
    unfold BackendScalarBits.backendScalarUnit BackendScalarBits.scalarUnit
    calc
      _ ≤ 8*(100*P^2) := by gcongr
      _ = _ := by ring
  have hc : GraphHalfSourceNormalizeCost.controlBudget f p≤8*P+84*I+9 := by
    unfold GraphHalfSourceNormalizeCost.controlBudget
    change 8*p.L+1+M*(44*B+40)+8≤_
    nlinarith only [he,hL,hM]
  have hd : 16*M+48+GraphHalfSourceNormalizeCost.controlBudget f p+I*(64*I.size^2+54)+21≤
      300*(I+1)*P^2 := by
    have hi2 := Nat.mul_le_mul_left (64*I) (Nat.pow_le_pow_left hI 2)
    have hix := Nat.mul_le_mul_left I hp2
    nlinarith only [hc,hM,hi2,hix,h1,hp2]
  have hscalar := Nat.mul_le_mul_left I hs
  have hdecode := Nat.mul_le_mul_left (price+1) hd
  have hnorm := Nat.le_mul_of_pos_left (1000000000*(I+1)*P^7) (show 0<price+1 by omega)
  have hc7 := Nat.mul_le_mul_left (300*(price+1)*(I+1)) h2
  have hs7 := Nat.mul_le_mul_left (800*I) h2
  have hscale := Nat.le_mul_of_pos_left (800*I*P^7) (show 0<price+1 by omega)
  unfold extra
  change GraphHalfSourceNormalizeCost.bitsBudget f p+I*BackendScalarBits.backendScalarUnit h.size+
    (price+1)*(16*M+48+GraphHalfSourceNormalizeCost.controlBudget f p+I*(64*I.size^2+54)+21)≤_
  nlinarith only [hn,hscalar,hdecode,hnorm,hc7,hs7,hscale,Nat.zero_le ((price+1)*P^7)]

variable (hm : p.m≤p.L-p.m) (input : BinaryFoldedFormation.Inputs n)
  (scheme : RectangularBatch.Scheme) (hnum : scheme.num=861) (hden : scheme.den=500) (hz : scheme.z=15)

theorem produce_work (hv : scheme.Valid) (price : ℕ) (hB : 1≤CompactBlocks.blockCount n h) :
    let out := GraphHalfSourceExecution.execute f p hm input scheme hnum hden hz price
    (GraphHalfSourceExecution.produce f p hm input scheme hnum hden hz hv price).work≤
      (price+1)*out.setup.operations+out.low.bitSteps+(price+1)*out.low.control+
      (price+1)*out.high.operations+
      10000000000*(price+1)*(EndToEndAPSP.incidenceSize n h+1)*(width f p)^7 := by
  dsimp only
  have hp := GraphHalfSourceNormalizeCost.produce_work f p hm input scheme hnum hden hz hv price
  have he := extra_polynomial f p price hB
  unfold extra at he
  omega

#print axioms incidence_eq
#print axioms extra_polynomial
#print axioms produce_work
end ThinMatrix.GraphHalfSourceOutputCost
