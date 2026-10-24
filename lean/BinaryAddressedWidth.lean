import BinaryAddressedCosts

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 3000

/-! Explicit address widths for every retained recursive table. Since the
base is fixed, the width grows linearly with recursion depth. -/
namespace ThinMatrix.BinaryAddressedWidth
open BinaryAddressedCosts

def span (a b r t : ℕ) :=
  1+a+b+r+t+a*b+t*(a*b)+(r+t-1)/t+((r+t-1)/t)*t

def width (a b r t K : ℕ) := (K+2)*((span a b r t).size+1)

theorem fits (a b r t K : ℕ) : Fits a b r t K (width a b r t K) := by
  let C := span a b r t
  have hspan (n : ℕ) (hn : n≤C) : n.size≤C.size := Nat.size_le_size hn
  have ha : a.size≤C.size := hspan a (by dsimp [C,span];generalize (r+t-1)/t=g;omega)
  have hb : b.size≤C.size := hspan b (by dsimp [C,span];generalize (r+t-1)/t=g;omega)
  have hr : r.size≤C.size := hspan r (by dsimp [C,span];generalize (r+t-1)/t=g;omega)
  have ht : t.size≤C.size := hspan t (by dsimp [C,span];generalize (r+t-1)/t=g;omega)
  have hp : (a*b).size≤C.size := hspan (a*b) (by dsimp [C,span];generalize (r+t-1)/t=g;omega)
  have hcoeff : (t*(a*b)).size≤C.size := hspan _ (by dsimp [C,span];generalize (r+t-1)/t=g;omega)
  have hg : ((r+t-1)/t).size≤C.size := hspan _ (by dsimp [C,span];generalize (r+t-1)/t=g;omega)
  have hpad : (((r+t-1)/t)*t).size≤C.size := hspan _ (by dsimp [C,span];generalize (r+t-1)/t=g;omega)
  have hw : C.size≤width a b r t K := by dsimp [width,C];nlinarith
  have hpow (k : ℕ) (hk : k≤K) : ((a*b)^k).size≤k*C.size+1 := by
    exact (BinaryRetainedBounds.size_power _ _).trans
      (Nat.add_le_add_right (Nat.mul_le_mul_left k hp) 1)
  have hcp (n : ℕ) (hn : n.size≤C.size) (k : ℕ) (hk : k≤K) :
      (n*(a*b)^k).size≤width a b r t K := by
    have hh := BinaryMultiplierAdapter.size_mul n ((a*b)^k)
    have pp := hpow k hk
    change _≤(K+2)*(C.size+1)
    nlinarith [Nat.mul_le_mul_right C.size hk]
  exact ⟨ha.trans hw,hb.trans hw,hp.trans hw,hr.trans hw,ht.trans hw,hcoeff.trans hw,
    hg.trans hw,hpad.trans hw,
    fun k hk => (hpow k hk).trans (by change _≤(K+2)*(C.size+1);nlinarith [Nat.mul_le_mul_right C.size hk]),
    hcp r hr,hcp t ht⟩

theorem Fits.mono {a b r t K W V : ℕ} (h : Fits a b r t K W) (hWV : W≤V) : Fits a b r t K V :=
  ⟨h.first.trans hWV,h.second.trans hWV,h.pair.trans hWV,h.rank.trans hWV,h.copies.trans hWV,
    h.coefficient.trans hWV,h.group.trans hWV,h.paddedIndex.trans hWV,
    fun k hk => (h.words k hk).trans hWV,fun k hk => (h.rankCells k hk).trans hWV,
    fun k hk => (h.copyCells k hk).trans hWV⟩

def slope (a b c r t : ℕ) :=
  (span a b r t).size+(span b c r t).size+(span c a r t).size+3

def commonWidth (a b c r t K : ℕ) := (K+2)*slope a b c r t

theorem common_fits (a b c r t K : ℕ) :
    Fits a b r t K (commonWidth a b c r t K) ∧
    Fits b c r t K (commonWidth a b c r t K) ∧
    Fits c a r t K (commonWidth a b c r t K) := by
  refine ⟨Fits.mono (fits a b r t K) ?_,Fits.mono (fits b c r t K) ?_,Fits.mono (fits c a r t K) ?_⟩ <;>
    unfold width commonWidth slope <;> nlinarith

theorem unit_bound (a b c r t K : ℕ) :
    unit K (commonWidth a b c r t K)≤131072*(slope a b c r t+1)^2*(K+2)^4 := by
  have hK : K+1≤K+2 := by omega
  have hw : commonWidth a b c r t K+1≤(K+2)*(slope a b c r t+1) := by
    unfold commonWidth; nlinarith
  have hp := Nat.mul_le_mul (Nat.pow_le_pow_left hK 2) (Nat.pow_le_pow_left hw 2)
  unfold unit
  calc
    _=131072*((K+1)^2*(commonWidth a b c r t K+1)^2) := by ring
    _≤131072*((K+2)^2*((K+2)*(slope a b c r t+1))^2) := Nat.mul_le_mul_left 131072 hp
    _=_ := by ring

#print axioms fits
#print axioms Fits.mono
#print axioms common_fits
#print axioms unit_bound
end ThinMatrix.BinaryAddressedWidth
