import GraphOwnBandUniformFit
import HalfSourceActualVolumes

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 10000
namespace ThinMatrix.GraphOwnBandShapeBounds
open GraphAdaptiveRootBatch GraphOwnBandPriced GraphOwnBandTypeRate
variable {n h r S : ℕ} (f : CompactBlocks.PhysicalFactorization r)
  (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (base : Index f p)

def width : ℕ := 32*(p.L+p.m+f.cyclic.size+p.N.size+n.size+1)

 theorem support : D f p base ≤ 2^p.L := by
  have hc := BinaryGroupedCompletion.count_le_power
    (WindowPrefixProgram.length (p.L-p.m) (E f p base))
    (WindowPrefixProgram.cap (p.L-p.m) (E f p base) (p.m/2)
      (GraphWindowCompatibility.counts base.channel).1 (GraphWindowCompatibility.counts base.channel).2)
  apply hc.trans
  apply Nat.pow_le_pow_right (by norm_num)
  unfold WindowPrefixProgram.length
  omega

 theorem group_pos (hS : 1≤S) : 1≤G f p (S:=S) := by
  have hd := GoodMapEmbedding.goodSlots_density p.L p.m
  have hp := Nat.choose_pos p.m_le_L
  have hg : 1≤(GoodMapEmbedding.goodSlots p.L p.m).card := by omega
  exact Nat.mul_le_mul hS (Nat.mul_le_mul hg hg)

 theorem powers (hh : 0<h) (hS : S≤p.N) :
    p.L≤width f p ∧ M (n:=n)≤2^(width f p) ∧ D f p base≤2^(width f p) ∧
    Q f p≤2^(width f p) ∧ SharedCompletionTile.row (D f p base)≤2^(width f p) ∧
    SharedCompletionTile.col (D f p base)≤2^(width f p) ∧ G f p (S:=S)≤2^(width f p) ∧
    H f p base≤2^(width f p) ∧ W f p≤2^(width f p) := by
  have pow_mono {a b : ℕ} (hab : a≤b) : 2^a≤2^b := Nat.pow_le_pow_right (by norm_num) hab
  have sn (x : ℕ) : x≤2^x.size := (Nat.lt_size_self x).le
  have hgeom : p.L≤width f p := by unfold width; omega
  have hs := support f p base
  have hsu := hs.trans (pow_mono hgeom)
  have hM : M (n:=n)≤2^(2*n.size+2) := by
    change n*n*3≤_
    rw [show n*n*3=3*n*n by ring]
    calc
      3*n*n ≤ 4*(2^n.size)*(2^n.size) := Nat.mul_le_mul (Nat.mul_le_mul (by norm_num) (sn n)) (sn n)
      _ = 2^(2*n.size+2) := by ring
  have hB : CompactBlocks.blockCount n h≤n := by
    apply (ceilDiv_le_iff_le_mul hh).mpr
    exact Nat.le_mul_of_pos_left n hh
  have hm : p.m+1≤2^(p.m+1) := Nat.lt_two_pow_self.le
  have hQ : Q f p≤2^(n.size+(p.m+1)+f.cyclic.size) := by
    change CompactBlocks.blockCount n h*((p.m+1)*f.cyclic)≤_
    calc
      _ ≤ 2^n.size*(2^(p.m+1)*2^f.cyclic.size) := Nat.mul_le_mul (hB.trans (sn n)) (Nat.mul_le_mul hm (sn _))
      _ = _ := by rw [pow_add,pow_add]; ring
  have hA : SharedCompletionTile.row (D f p base)≤2^(2*p.L+1) := by
    have hr := ParameterExecution.roundedPower_le 861 1000 ((D f p base)^2)
    change ComputableParameters.roundedPower 861 1000 ((D f p base)^2)≤_
    apply hr.trans
    have hh := Nat.pow_le_pow_left hs 2
    have hone : 1≤(2^p.L)^2 := one_le_pow₀ (one_le_pow₀ (by norm_num))
    calc
      (D f p base)^2+1 ≤ 2*((2^p.L)^2) := by omega
      _ = _ := by ring
  have hZ : SharedCompletionTile.col (D f p base)≤2^(15*p.L) := by
    change (D f p base)^15≤_
    calc
      _ ≤ (2^p.L)^15 := Nat.pow_le_pow_left hs 15
      _ = _ := by rw [←pow_mul]; congr 1; omega
  have hg0 := (HalfSourceActualVolumes.good_count p.L p.m).trans (Nat.choose_le_two_pow p.L p.m)
  have hg : G f p (S:=S)≤2^(p.N.size+2*p.L) := by
    change S*((GoodMapEmbedding.goodSlots p.L p.m).card*(GoodMapEmbedding.goodSlots p.L p.m).card)≤_
    calc
      _ ≤ 2^p.N.size*(2^p.L*2^p.L) := Nat.mul_le_mul (hS.trans (sn p.N)) (Nat.mul_le_mul hg0 hg0)
      _ = _ := by ring
  have hP : WindowPrefixProgram.prefixLength (p.L-p.m) (E f p base)≤2*(p.L-p.m) := by
    unfold WindowPrefixProgram.prefixLength; omega
  have hH : H f p base≤2^(6*p.L) := by
    unfold H GraphAdaptiveBatchSources.windowMagnitude GraphAdaptiveBatchSources.rawMagnitude
    rw [show (4:ℕ)=2^2 by norm_num,←pow_mul]
    rw [←pow_add,←pow_add,←pow_add,←pow_add]
    apply pow_mono
    have := p.m_le_L
    omega
  have hW : W f p≤2^(p.L+1) := by
    have hw : W f p≤p.L+1 := by
      unfold W RetainedRootWindows.slots
      split <;> omega
    exact hw.trans (Nat.lt_two_pow_self.le)
  exact ⟨hgeom,hM.trans (pow_mono (by unfold width; omega)),hsu,
    hQ.trans (pow_mono (by unfold width; omega)),hA.trans (pow_mono (by unfold width; omega)),
    hZ.trans (pow_mono (by unfold width; omega)),hg.trans (pow_mono (by unfold width; omega)),
    hH.trans (pow_mono (by unfold width; omega)),hW.trans (pow_mono (by unfold width; omega))⟩

 theorem fits (hh : 0<h) (hS : 1≤S) (hSN : S≤p.N)
    (scheme : RectangularBatch.Scheme) (targets : GraphOwnBandTargets.Prepared f p (S:=S))
    (hb : ∀ i,(targets.requests.get i).bandL<S ∧ (targets.requests.get i).bandR<S)
    (htree : GraphOwnBandTargets.tree f p targets base.right=(GraphOwnBandRouter.run base.right targets.requests hb).value)
    (hfit : SharedCompletionTile.col (D f p base)≤Q f p) :
    Fits f p base scheme targets (scheme.q.size+3*width f p+30) := by
  have hw := powers f p base hh hSN
  exact GraphOwnBandUniformFit.power_bounds f p base scheme targets (width f p)
    (CappedSubsetList.count_pos _ _) hb htree (group_pos f p hS) hfit
    hw.1 hw.2.1 hw.2.2.1 hw.2.2.2.1 hw.2.2.2.2.1 hw.2.2.2.2.2.1
    hw.2.2.2.2.2.2.1 hw.2.2.2.2.2.2.2.1 hw.2.2.2.2.2.2.2.2

#print axioms support
#print axioms group_pos
#print axioms powers
#print axioms fits
end ThinMatrix.GraphOwnBandShapeBounds
