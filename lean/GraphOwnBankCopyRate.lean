import GraphOwnBankCopyCosts
import GraphOwnBandTypeRate

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
namespace ThinMatrix.GraphOwnBankCopyRate
open SharedCompletionRate

 theorem natural (G W Q F s P len k H L price bs cs : ℕ)
    (hG : 1 ≤ G) (hW : 1 ≤ W) (hQ : 1 ≤ Q) (hF : 1 ≤ F) (hs : 1 ≤ s)
    (hL : 1 ≤ L) (hP : P+1 ≤ L) (hlen : len+1 ≤ L) (hk : k ≤ L)
    (hH : H+1 ≤ L) (hwidth : G.size ≤ L)
    (hb : bs ≤ G*W*Q*F*s*BackendScalarBits.backendScalarUnit H)
    (hc : cs ≤ G*(W*(Q*F*s*HalfSourceBatchCopyVolume.batchControlUnit P len)+
      W*(256*k+99)+32+64*G.size^2+64)+8) :
    bs+price*cs ≤ 4000*(price+1)*G*W*Q*F*s*L^2 := by
  have hL2 : 1 ≤ L^2 := one_le_pow₀ hL
  have hLle : L ≤ L^2 := Nat.le_self_pow (by decide) _
  have hunit : BackendScalarBits.backendScalarUnit H ≤ 800*L^2 := by
    unfold BackendScalarBits.backendScalarUnit BackendScalarBits.scalarUnit
    nlinarith [Nat.pow_le_pow_left hH 2]
  have hbatch : HalfSourceBatchCopyVolume.batchControlUnit P len ≤ 1000*L^2 := by
    have hm := Nat.mul_le_mul hlen (show 8*len+32 ≤ 40*L by omega)
    unfold HalfSourceBatchCopyVolume.batchControlUnit
    nlinarith
  let X := W*Q*F*s
  have hx : 1 ≤ X := Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hW hQ) hF) hs
  have hwx : W ≤ X := by
    have hm := Nat.mul_pos (Nat.mul_pos hQ hF) hs
    dsimp [X]
    nlinarith
  have hWX : W*L^2 ≤ X*L^2 := Nat.mul_le_mul_right _ hwx
  have h1X : 1 ≤ X*L^2 := Nat.mul_pos hx hL2
  have hL2X : L^2 ≤ X*L^2 := by nlinarith
  have he : W*(256*k+99) ≤ 355*X*L^2 := by
    have hi : 256*k+99 ≤ 355*L^2 := by omega
    have hh := Nat.mul_le_mul_left W hi
    nlinarith only [hh,hWX]
  have hm := Nat.mul_le_mul_left (W*(Q*F*s)) hbatch
  have hd := Nat.pow_le_pow_left hwidth 2
  have hi : W*(Q*F*s*HalfSourceBatchCopyVolume.batchControlUnit P len)+
      W*(256*k+99)+32+64*G.size^2+64 ≤ 1600*X*L^2 := by
    have hdx := hd.trans hL2X
    dsimp [X] at hm he h1X hdx ⊢
    nlinarith only [hm,he,h1X,hdx]
  have hgi := Nat.mul_le_mul_left G hi
  have hgx : 1 ≤ G*X*L^2 := by simpa only [Nat.one_mul,Nat.mul_assoc] using Nat.mul_le_mul hG h1X
  have hcs : cs ≤ 2000*G*X*L^2 := by nlinarith only [hc,hgi,hgx]
  have hbu := Nat.mul_le_mul_left (G*W*Q*F*s) hunit
  have hbs : bs ≤ 800*G*X*L^2 := by dsimp [X];nlinarith only [hb,hbu]
  have hpriced := Nat.mul_le_mul_left price hcs
  dsimp [X] at hbs hpriced
  nlinarith only [hbs,hpriced]

 theorem rate (G W Q F s P len k H L price bs cs : ℕ)
    (hG : 1 ≤ G) (hW : 1 ≤ W) (hQ : 1 ≤ Q) (hF : 1 ≤ F) (hs : 1 ≤ s)
    (hL : 1 ≤ L) (hP : P+1 ≤ L) (hlen : len+1 ≤ L) (hk : k ≤ L)
    (hH : H+1 ≤ L) (hwidth : G.size ≤ L)
    (hb : bs ≤ G*W*Q*F*s*BackendScalarBits.backendScalarUnit H)
    (hc : cs ≤ G*(W*(Q*F*s*HalfSourceBatchCopyVolume.batchControlUnit P len)+
      W*(256*k+99)+32+64*G.size^2+64)+8) :
    (bs+price*cs:ℝ) ≤ 4000*(price+1)*W*(L:ℝ)^5*((G:ℝ)*F*Q*(s:ℝ)^gamma) := by
  have hn : (bs+price*cs:ℝ) ≤ 4000*(price+1)*G*W*Q*F*s*(L:ℝ)^2 := by
    exact_mod_cast natural G W Q F s P len k H L price bs cs hG hW hQ hF hs hL hP hlen hk hH hwidth hb hc
  have hs' : 1 ≤ (s:ℝ) := by exact_mod_cast hs
  have hp : (s:ℝ) ≤ (s:ℝ)^gamma := by
    calc (s:ℝ) = (s:ℝ)^(1:ℝ) := (Real.rpow_one _).symm
         _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hs' (by norm_num [gamma])
  have hl : (L:ℝ)^2 ≤ (L:ℝ)^5 := pow_le_pow_right₀ (by exact_mod_cast hL) (by decide)
  have hh := mul_le_mul hp hl (by positivity) (by positivity)
  have hc' := mul_le_mul_of_nonneg_left hh (show 0 ≤ (4000:ℝ)*(price+1)*G*W*Q*F by positivity)
  nlinarith only [hn,hc']

#print axioms natural
#print axioms rate
end ThinMatrix.GraphOwnBankCopyRate
