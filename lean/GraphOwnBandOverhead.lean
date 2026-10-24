import GraphOwnBandPriced

set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace ThinMatrix.GraphOwnBandOverhead
open SharedCompletionRate

 theorem natural (G M Q W L d k price : ℕ) (hG : 1 ≤ G) (hQ : 1 ≤ Q)
    (hW : 1 ≤ W) (hL : 1 ≤ L) (hd : G.size+1 ≤ L) (hk : k ≤ d) (hp : d ≤ L) :
    price*(G*(16*(G.size+1)^2+64*(G.size+1)^3+48*d+60)+
      M*(32*k+112)+48*G+80*M+16*Q+68) ≤
      1024*(price+1)*W*L^3*Q*(M+G) := by
  have hL3 : 1 ≤ L^3 := one_le_pow₀ hL
  have h13 : L ≤ L^3 := by exact Nat.le_self_pow (by decide) L
  have h23 : L^2 ≤ L^3 := Nat.pow_le_pow_right hL (by decide)
  have ha2 := (Nat.pow_le_pow_left hd 2).trans h23
  have ha3 := Nat.pow_le_pow_left hd 3
  have hpoly : 16*(G.size+1)^2+64*(G.size+1)^3+48*d+60 ≤ 188*L^3 := by omega
  have hentry : 32*k+112 ≤ 144*L^3 := by omega
  have hg := Nat.mul_le_mul_left G hpoly
  have hm := Nat.mul_le_mul_left M hentry
  have hbase : 1 ≤ M+G := by omega
  have hbaseQ := Nat.mul_le_mul_left Q hbase
  have hbaseL := Nat.mul_le_mul_left (M+G) hL3
  have hQle : Q ≤ L^3*Q*(M+G) := by nlinarith
  have h1le : 1 ≤ L^3*Q*(M+G) := by nlinarith
  have hLG : L^3*G ≤ L^3*Q*(M+G) := by nlinarith
  have hLM : L^3*M ≤ L^3*Q*(M+G) := by nlinarith
  have hGle : G ≤ L^3*Q*(M+G) := by nlinarith
  have hMle : M ≤ L^3*Q*(M+G) := by nlinarith
  have hsum : G*(16*(G.size+1)^2+64*(G.size+1)^3+48*d+60)+
      M*(32*k+112)+48*G+80*M+16*Q+68 ≤ 1024*L^3*Q*(M+G) := by
    nlinarith only [hg,hm,hLG,hLM,hGle,hMle,hQle,h1le]
  have hprice := Nat.mul_le_mul_left price hsum
  have hW' := Nat.mul_le_mul_left (1024*(price+1)*L^3*Q*(M+G)) hW
  have hinc := Nat.mul_le_mul_right (1024*L^3*Q*(M+G)) (Nat.le_succ price)
  nlinarith only [hprice,hW',hinc]

 theorem rate (G M Q W L d k price s F : ℕ) (hG : 1 ≤ G) (hQ : 1 ≤ Q)
    (hW : 1 ≤ W) (hL : 1 ≤ L) (hd : G.size+1 ≤ L) (hk : k ≤ d) (hp : d ≤ L)
    (hs : 1 ≤ s) (hF : 1 ≤ F) :
    (price*(G*(16*(G.size+1)^2+64*(G.size+1)^3+48*d+60)+
      M*(32*k+112)+48*G+80*M+16*Q+68):ℝ) ≤
      1024*(price+1)*W*(L:ℝ)^5*((M:ℝ)*Q*(s:ℝ)^beta+(G:ℝ)*F*Q*(s:ℝ)^gamma) := by
  have hn : (price*(G*(16*(G.size+1)^2+64*(G.size+1)^3+48*d+60)+
      M*(32*k+112)+48*G+80*M+16*Q+68):ℝ) ≤
      1024*(price+1)*W*(L:ℝ)^3*Q*(M+G) := by
    exact_mod_cast natural G M Q W L d k price hG hQ hW hL hd hk hp
  have hb : 1 ≤ (s:ℝ)^beta := Real.one_le_rpow (by exact_mod_cast hs) (by norm_num [beta])
  have hg : 1 ≤ (s:ℝ)^gamma := Real.one_le_rpow (by exact_mod_cast hs) (by norm_num [gamma])
  have hm := mul_le_mul_of_nonneg_left hb (show 0 ≤ (M:ℝ)*Q by positivity)
  have hgr := mul_le_mul_of_nonneg_left hg (show 0 ≤ (G:ℝ)*F*Q by positivity)
  have hFr : 1 ≤ (F:ℝ) := by exact_mod_cast hF
  have hf := mul_le_mul_of_nonneg_left hFr (show 0 ≤ (G:ℝ)*Q by positivity)
  have ht : (Q:ℝ)*(M+G) ≤ (M:ℝ)*Q*(s:ℝ)^beta+(G:ℝ)*F*Q*(s:ℝ)^gamma := by nlinarith
  have hl : (L:ℝ)^3 ≤ (L:ℝ)^5 := pow_le_pow_right₀ (by exact_mod_cast hL) (by decide)
  have hh := mul_le_mul hl ht (by positivity) (by positivity)
  have hscale := mul_le_mul_of_nonneg_left hh (show 0 ≤ (1024:ℝ)*(price+1)*W by positivity)
  nlinarith

#print axioms natural
#print axioms rate
end ThinMatrix.GraphOwnBandOverhead
