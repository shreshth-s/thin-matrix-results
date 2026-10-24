import HalfSourceTargetSetupCost

set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace ThinMatrix.HalfSourceTargetPolynomial
open HalfSourceTargetSetupCost

 def width (S L m t W V : ℕ) : ℕ := L+m+t+W+V+(GraphOwnBandRouter.count S L m).size+10
 def volume (S B L m t M : ℕ) : ℕ :=
  12^L*2^(L-m)+(GoodMapEmbedding.goodSlots L m).card+ResidualFamilyKeys.channelCount m t+
    GraphOwnBandRouter.count S L m+M+S*B+S+B+1

theorem weights (L m t W V S : ℕ) :
    WeightedRootProducts.weightBudget (2*m) t≤3000000*(width S L m t W V)^5 := by
  let P := width S L m t W V
  have hP : 1≤P := by dsimp[P,width];omega
  have hk : 2*m+t+2≤2*P := by dsimp[P,width];omega
  have hp2 : 1≤P^2 := one_le_pow₀ hP
  have hbit : CachedLowQuery.weightBitWidth (2*m) t+1≤11*P^2 := by
    unfold CachedLowQuery.weightBitWidth
    have hh := Nat.pow_le_pow_left hk 2
    nlinarith only [hh,hp2]
  unfold WeightedRootProducts.weightBudget BackendScalarBits.scalarUnit
  calc
    _ ≤100*(2*P)*(100*(11*P^2)^2) := by gcongr
    _ ≤3000000*P^5 := by nlinarith

 theorem key_budget (S L m t W V : ℕ) :
    ResidualFamilyKeys.prepareBudget L m t (GoodMapEmbedding.goodSlots L m).card≤
      1000*(width S L m t W V)^3*((GoodMapEmbedding.goodSlots L m).card+ResidualFamilyKeys.channelCount m t+1) := by
  let P := width S L m t W V
  let K := (GoodMapEmbedding.goodSlots L m).card
  let H := ResidualFamilyKeys.channelCount m t
  have hP : 1≤P := by dsimp[P,width];omega
  have hL : L≤P := by dsimp[P,width];omega
  have hm : m≤P := by dsimp[P,width];omega
  have h1 : P≤P^3 := le_self_pow₀ hP (by decide)
  have h2 : P^2≤P^3 := Nat.pow_le_pow_right hP (by decide)
  have h0 : 1≤P^3 := one_le_pow₀ hP
  have hmasks : ResidualFamilyKeys.decodeBudget L+40≤100*P^3 := by
    unfold ResidualFamilyKeys.decodeBudget
    have hh := Nat.pow_le_pow_left hL 2
    nlinarith only [hh,hL,h0,h1,h2]
  have hchannel : (2*m+1)*(16*m+32)+2≤200*P^3 := by
    have hh : (2*m+1)*(16*m+32)+2≤(3*P)*(48*P)+2 := by gcongr <;> omega
    nlinarith only [hh,h0,h2]
  have ha := Nat.mul_le_mul_left K hmasks
  have hb := Nat.mul_le_mul_left H hchannel
  unfold ResidualFamilyKeys.prepareBudget
  change K*(ResidualFamilyKeys.decodeBudget L+40)+8+(2*m+1)*(16*m+32)*H+4+2*H+8≤1000*P^3*(K+H+1)
  nlinarith only [ha,hb,h0]

 theorem router (S L m t M W V : ℕ) :
    routerBudget S L m M≤1000*(width S L m t W V)^3*(GraphOwnBandRouter.count S L m+M+1) := by
  let P := width S L m t W V
  let G := GraphOwnBandRouter.count S L m
  have hP : 1≤P := by dsimp[P,width];omega
  have hsize : G.size+L+m+1≤P := by dsimp[G,P,width];omega
  have hsize' : G.size+1≤P := by omega
  have h2 : P^2≤P^3 := Nat.pow_le_pow_right hP (by decide)
  have h0 : 1≤P^3 := one_le_pow₀ hP
  have hin : 16*(G.size+1)^2+64*(G.size+1)^3+128*(G.size+L+m+1)^3+36≤244*P^3 := by
    have hh : 16*(G.size+1)^2+64*(G.size+1)^3+128*(G.size+L+m+1)^3+36≤16*P^2+192*P^3+36 := by
      calc
        _≤16*P^2+64*P^3+128*P^3+36 := by gcongr
        _=_ := by ring
    omega
  have hh := Nat.mul_le_mul_left M hin
  have hg := Nat.mul_le_mul_left (24*(G+1)+36) h0
  unfold routerBudget
  change 24*(G+1)+M*(16*(G.size+1)^2+64*(G.size+1)^3+128*(G.size+L+m+1)^3+36)+36≤_
  nlinarith only [hh,hg]

 theorem extras (S B L m t M W V : ℕ) :
    extraBudget S B L m t M W V≤10000000000*(width S L m t W V)^6*volume S B L m t M := by
  let P := width S L m t W V
  let U := 12^L*2^(L-m)
  let K := (GoodMapEmbedding.goodSlots L m).card
  let H := ResidualFamilyKeys.channelCount m t
  let G := GraphOwnBandRouter.count S L m
  let X := volume S B L m t M
  have hP : 1≤P := by dsimp[P,width];omega
  have ht : t≤P := by dsimp[P,width];omega
  have hshape : L+m+1≤P := by dsimp[P,width];omega
  have hinput : W+V+10≤P := by dsimp[P,width];omega
  have hmeta : V+1≤P := by omega
  have h0 : 1≤P^6 := one_le_pow₀ hP
  have h1 : P≤P^6 := le_self_pow₀ hP (by decide)
  have h2 : P^2≤P^6 := Nat.pow_le_pow_right hP (by decide)
  have h3 : P^3≤P^6 := Nat.pow_le_pow_right hP (by decide)
  have h5 : P^5≤P^6 := Nat.pow_le_pow_right hP (by decide)
  have hs : 50000*(L+m+1)^6*12^L*2^(L-m)≤50000*P^6*U := by
    calc
      _ =50000*(L+m+1)^6*U := by dsimp[U];ring
      _ ≤50000*P^6*U := Nat.mul_le_mul_right U (Nat.mul_le_mul_left 50000 (Nat.pow_le_pow_left hshape 6))
  have hk := (key_budget S L m t W V).trans
    (Nat.mul_le_mul_right (K+H+1) (Nat.mul_le_mul_left 1000 h3))
  have hr := (router S L m t M W V).trans
    (Nat.mul_le_mul_right (G+M+1) (Nat.mul_le_mul_left 1000 h3))
  have hw := weights L m t W V S
  have htw : t*WeightedRootProducts.weightBudget (2*m) t≤3000000*P^6 := by
    calc
      _ ≤P*(3000000*P^5) := Nat.mul_le_mul ht hw
      _ =_ := by ring
  have hf : 10000*(V+1)^2+2000000*M*(W+V+10)^2≤2010000*P^6*(M+1) := by
    have hA : (V+1)^2≤P^6 := (Nat.pow_le_pow_left hmeta 2).trans h2
    have hB : (W+V+10)^2≤P^6 := (Nat.pow_le_pow_left hinput 2).trans h2
    have hm := Nat.mul_le_mul_left (2000000*M) hB
    have hm2 := Nat.mul_le_mul_left 10000 hA
    nlinarith only [hm,hm2]
  have hp : M*(1000*(L+m+1)^5+32)+8≤1040*P^6*(M+1) := by
    have hh : 1000*(L+m+1)^5+32≤1032*P^6 := by
      have hs := (Nat.pow_le_pow_left hshape 5).trans h5
      omega
    have ha := Nat.mul_le_mul_left M hh
    nlinarith only [ha,h0]
  have hviews := Nat.mul_le_mul_left (48*S*B+8*S+8*B+64) h0
  have htotal : extraBudget S B L m t M W V≤
      100000*P^6*U+2000*P^6*(K+H+1)+2010000*P^6*(M+1)+
      1040*P^6*(M+1)+2000*P^6*(G+M+1)+6000051*P^6+
      (48*S*B+8*S+8*B+64)*P^6+44 := by
    unfold extraBudget targetBudget
    dsimp only [U,K,H,G] at *
    nlinarith only [hs,hk,hr,htw,hf,hp,hviews,Nat.mul_le_mul_left 51 ht,h1]
  apply htotal.trans
  change _≤10000000000*P^6*X
  dsimp[X,volume]
  change _≤10000000000*P^6*(U+K+H+G+M+S*B+S+B+1)
  nlinarith only [h0,
    Nat.zero_le (P^6*U),Nat.zero_le (P^6*K),Nat.zero_le (P^6*H),Nat.zero_le (P^6*G),
    Nat.zero_le (P^6*M),Nat.zero_le (P^6*S*B),Nat.zero_le (P^6*S),Nat.zero_le (P^6*B)]

#print axioms weights
#print axioms key_budget
#print axioms router
#print axioms extras
end ThinMatrix.HalfSourceTargetPolynomial
