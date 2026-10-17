import BinaryFoldedFactory
import ComputableParameters

/-!
# Literal public setup for the binary folded producer

The public natural operations below are sites of the finite indexed-array IR.
Each loop returns its value and its scalar/control-site ledger jointly. This
module does not assign unit bit cost to unbounded Nat arithmetic or claim a
Lean runtime bound. Pricing the derived bounded public operands is separate.
No executable definition calls `Nat.sqrt`, `Nat.clog`, `Nat.size` or exponentiation.
-/
namespace ThinMatrix.BinaryTriangleSetupCosts

set_option maxRecDepth 10000
set_option maxHeartbeats 200000

structure Run (α : Type*) where
  value : α
  sites : ℕ

/-- Exhaust the bounded candidates, retaining the largest successful square.
The seven sites charge the square, test, index update and result/control reads. -/
def sqrtScan (x : ℕ) : ℕ → Run ℕ
  | 0 => ⟨0,1⟩
  | k+1 =>
    let previous:=sqrtScan x k
    let candidate:=k+1
    let square:=candidate*candidate
    ⟨if square≤x then candidate else previous.value,previous.sites+7⟩

theorem sqrtScan_value (x fuel : ℕ) : (sqrtScan x fuel).value=min fuel (Nat.sqrt x) := by
  induction fuel with
  | zero => simp [sqrtScan]
  | succ k ih =>
    simp only [sqrtScan]
    by_cases hs : (k+1)*(k+1)≤x
    · have hk : k+1≤Nat.sqrt x := Nat.le_sqrt.mpr hs
      simp [hs,min_eq_left hk]
    · have hk : Nat.sqrt x<k+1 := Nat.lt_of_not_ge (fun h => hs (Nat.le_sqrt.mp h))
      simp [hs,ih,min_eq_right (by omega : Nat.sqrt x≤k),min_eq_right hk.le]

theorem sqrtScan_sites (x fuel : ℕ) : (sqrtScan x fuel).sites=7*fuel+1 := by
  induction fuel with
  | zero => rfl
  | succ k ih => simp only [sqrtScan,ih];omega

def foldWidth (d : ℕ) : Run ℕ :=
  let root:=sqrtScan (d-1) (d-1)
  ⟨root.value+1,root.sites+4⟩

theorem foldWidth_value (d : ℕ) : (foldWidth d).value=FoldedCounts.foldWidth d := by
  simp only [foldWidth,sqrtScan_value,FoldedCounts.foldWidth]
  rw [min_eq_right (Nat.sqrt_le_self _)]

theorem foldWidth_sites (d : ℕ) : (foldWidth d).sites≤7*d+5 := by
  simp only [foldWidth,sqrtScan_sites]
  omega

/-- Literal bounded division-by-two loop. Its public fuel is the input plus
one; early stopping makes the actual iteration count its bit length. -/
def bitLengthLoop : ℕ → ℕ → Run ℕ
  | 0,_ => ⟨0,1⟩
  | fuel+1,x =>
    if x=0 then ⟨0,2⟩ else
      let tail:=bitLengthLoop fuel (x/2)
      ⟨tail.value+1,tail.sites+7⟩

theorem size_step (x : ℕ) (hx : x≠0) : x.size=(x/2).size+1 := by
  induction x using Nat.binaryRec' with
  | zero => exact (hx rfl).elim
  | bit b n h ih =>
    rw [Nat.size_bit (Nat.bit_ne_zero_iff.mpr h),Nat.bit_div_two]

theorem bitLengthLoop_value (fuel x : ℕ) (hf : x≤fuel) :
    (bitLengthLoop fuel x).value=x.size := by
  induction fuel generalizing x with
  | zero =>
    have hx : x=0 := by omega
    subst x
    rfl
  | succ fuel ih =>
    by_cases hx : x=0
    · subst x;simp [bitLengthLoop]
    · have hd : x/2≤fuel := by have := Nat.div_lt_self (by omega : 0<x) (by decide : 1<2);omega
      simp only [bitLengthLoop,if_neg hx]
      rw [ih _ hd,size_step x hx]

theorem bitLengthLoop_sites (fuel x : ℕ) (hf : x≤fuel) :
    (bitLengthLoop fuel x).sites≤7*x.size+2 := by
  induction fuel generalizing x with
  | zero =>
    have hx : x=0 := by omega
    subst x
    decide
  | succ fuel ih =>
    by_cases hx : x=0
    · subst x;simp [bitLengthLoop]
    · have hd : x/2≤fuel := by have := Nat.div_lt_self (by omega : 0<x) (by decide : 1<2);omega
      have ht:=ih _ hd
      simp only [bitLengthLoop,if_neg hx]
      rw [size_step x hx]
      omega

def bitLength (x : ℕ) : Run ℕ :=
  let out:=bitLengthLoop (x+1) x
  ⟨out.value,out.sites+2⟩

theorem bitLength_value (x : ℕ) : (bitLength x).value=x.size :=
  bitLengthLoop_value _ _ (by omega)

theorem bitLength_sites (x : ℕ) : (bitLength x).sites≤7*x.size+4 := by
  have h:=bitLengthLoop_sites (x+1) x (by omega)
  change (bitLengthLoop (x+1) x).sites+2≤_
  omega

/-- Repeated scalar multiplication constructs the complete padded dimension. -/
def power4 : ℕ → Run ℕ
  | 0 => ⟨1,1⟩
  | m+1 => let previous:=power4 m; ⟨4*previous.value,previous.sites+4⟩

theorem power4_value (m : ℕ) : (power4 m).value=4^m := by
  induction m with
  | zero => rfl
  | succ m ih => simp [power4,ih,pow_succ,Nat.mul_comm]

theorem power4_sites (m : ℕ) : (power4 m).sites=4*m+1 := by
  induction m with
  | zero => rfl
  | succ m ih => simp only [power4,ih];omega

/-- The eight sites in a nonterminal round include upward division by four,
the stopping test, the fuel/value updates and retained-result control. -/
def clogLoop : ℕ → ℕ → Run ℕ
  | 0,_ => ⟨0,1⟩
  | fuel+1,x =>
    if x≤1 then ⟨0,2⟩ else
      let child:=clogLoop fuel ((x+3)/4)
      ⟨child.value+1,child.sites+8⟩

theorem clogLoop_value (fuel x : ℕ) (hf : Nat.clog 4 x≤fuel) :
    (clogLoop fuel x).value=Nat.clog 4 x := by
  induction fuel generalizing x with
  | zero => simp only [clogLoop];omega
  | succ fuel ih =>
    by_cases hx : x≤1
    · simp only [clogLoop,if_pos hx]
      exact (Nat.clog_of_right_le_one hx 4).symm
    · have hr : Nat.clog 4 x=Nat.clog 4 ((x+3)/4)+1 := by
        simpa only [show x+4-1=x+3 by omega] using
          (Nat.clog_of_two_le (b:=4) (n:=x) (by decide) (by omega))
      have hc : Nat.clog 4 ((x+3)/4)≤fuel := by omega
      simp only [clogLoop,if_neg hx]
      rw [ih _ hc,←hr]

theorem clogLoop_sites (fuel x : ℕ) : (clogLoop fuel x).sites≤8*fuel+2 := by
  induction fuel generalizing x with
  | zero => simp [clogLoop]
  | succ fuel ih =>
    by_cases hx : x≤1
    · simp [clogLoop,hx]
    · simp only [clogLoop,if_neg hx]
      have hc:=ih ((x+3)/4)
      omega

theorem clog4_le_size (x : ℕ) : Nat.clog 4 x≤x.size := by
  apply Nat.clog_le_of_le_pow
  exact (Nat.lt_size_self x).le.trans (Nat.pow_le_pow_left (by decide : 2≤4) x.size)

/-- Explicit arithmetic spelling of the geometry-dependent LOW width. -/
def runtimeLowWidth (L m qBits : ℕ) : ℕ :=
  let a:=4*m+2
  9*(100*L+106*m+qBits+103+2*(a*a)+20)

theorem runtimeLowWidth_eq_common (L m qBits : ℕ) :
    runtimeLowWidth L m qBits=AdaptiveBitBounds.commonBitWidth 2 0 L m qBits := by
  unfold runtimeLowWidth AdaptiveBitBounds.commonBitWidth CoefficientBudget.budgetConstant
  rw [show (2:ℕ).size=2 by decide]
  norm_num
  ring

/-- Joint actual public setup. Square-root candidates, bit lengths, logarithm
and the padded power are computed by the charged loops above. The remaining
eighty sites cover the fixed straight-line rational parameter arithmetic,
dimensions, width arithmetic and payload construction. -/
def preparePlan (n h : ℕ) {r : ℕ} (f : CompactBlocks.PhysicalFactorization r) :
    Run (BinaryFoldedFactory.Plan (n:=n) (h:=h) f) :=
  let d:=3*f.folded
  let width:=foldWidth d
  let raw:=h*d
  let rawBits:=bitLength raw
  let exponent:=clogLoop (rawBits.value+1) raw
  let padded:=power4 exponent.value
  let L:=ComputableParameters.ordinaryLength exponent.value
  let t:=ComputableParameters.channelLength exponent.value
  let qBits:=bitLength f.cyclic
  have hexponent : exponent.value=FoldedBackendExecution.middleExponent h (FoldedBackendExecution.physicalFold f) := by
    dsimp only [exponent,FoldedBackendExecution.middleExponent,FoldedBackendExecution.rawMiddle,
      FoldedBackendExecution.physicalFold]
    apply clogLoop_value
    rw [bitLength_value]
    exact (clog4_le_size raw).trans (by omega)
  let plan : BinaryFoldedFactory.Plan (n:=n) (h:=h) f :=
    { L:=L,m:=exponent.value,t:=t,foldWidth:=width.value,N:=n*width.value,D:=padded.value,raw:=raw
      lowWidth:=runtimeLowWidth L exponent.value qBits.value
      foldWidth_eq:=foldWidth_value d
      N_eq:=by
        change n*(foldWidth d).value=n*FoldedCounts.foldWidth d
        rw [foldWidth_value]
      D_eq:=by rw [power4_value,hexponent];rfl
      raw_eq:=rfl
      m_le_L:=ComputableParameters.ordinaryLength_lower _
      t_le:=(ComputableParameters.channelLength_upper _).trans (by omega)
      middle_fit:=(power4_value exponent.value).le }
  ⟨plan,width.sites+rawBits.sites+exponent.sites+padded.sites+qBits.sites+80⟩

theorem preparePlan_m (n h : ℕ) {r : ℕ} (f : CompactBlocks.PhysicalFactorization r) :
    (preparePlan n h f).value.m=FoldedBackendExecution.middleExponent h (FoldedBackendExecution.physicalFold f) := by
  change (clogLoop ((bitLength (h*(3*f.folded))).value+1) (h*(3*f.folded))).value=_
  apply clogLoop_value
  rw [bitLength_value]
  exact (clog4_le_size _).trans (by omega)

theorem preparePlan_L (n h : ℕ) {r : ℕ} (f : CompactBlocks.PhysicalFactorization r) :
    (preparePlan n h f).value.L=ComputableParameters.ordinaryLength
      (FoldedBackendExecution.middleExponent h (FoldedBackendExecution.physicalFold f)) := by
  change ComputableParameters.ordinaryLength (preparePlan n h f).value.m=_
  rw [preparePlan_m]

theorem preparePlan_t (n h : ℕ) {r : ℕ} (f : CompactBlocks.PhysicalFactorization r) :
    (preparePlan n h f).value.t=ComputableParameters.channelLength
      (FoldedBackendExecution.middleExponent h (FoldedBackendExecution.physicalFold f)) := by
  change ComputableParameters.channelLength (preparePlan n h f).value.m=_
  rw [preparePlan_m]

theorem preparePlan_lowWidth (n h : ℕ) {r : ℕ} (f : CompactBlocks.PhysicalFactorization r) :
    (preparePlan n h f).value.lowWidth=runtimeLowWidth (preparePlan n h f).value.L
      (preparePlan n h f).value.m f.cyclic.size := by
  exact congrArg (fun qBits => runtimeLowWidth (preparePlan n h f).value.L
    (preparePlan n h f).value.m qBits) (bitLength_value f.cyclic)

theorem preparePlan_lowWidth_common (n h : ℕ) {r : ℕ} (f : CompactBlocks.PhysicalFactorization r) :
    (preparePlan n h f).value.lowWidth=AdaptiveBitBounds.commonBitWidth 2 0
      (preparePlan n h f).value.L (preparePlan n h f).value.m f.cyclic.size := by
  rw [preparePlan_lowWidth,runtimeLowWidth_eq_common]

theorem preparePlan_sites (n h : ℕ) {r : ℕ} (f : CompactBlocks.PhysicalFactorization r) :
    (preparePlan n h f).sites≤7*(3*f.folded)+15*(h*(3*f.folded)).size+
      4*(preparePlan n h f).value.m+7*f.cyclic.size+110 := by
  have hw:=foldWidth_sites (3*f.folded)
  have hr:=bitLength_sites (h*(3*f.folded))
  have hc:=clogLoop_sites ((bitLength (h*(3*f.folded))).value+1) (h*(3*f.folded))
  have hp:=power4_sites (preparePlan n h f).value.m
  have hq:=bitLength_sites f.cyclic
  rw [bitLength_value] at hc
  change (foldWidth (3*f.folded)).sites+(bitLength (h*(3*f.folded))).sites+
    (clogLoop ((bitLength (h*(3*f.folded))).value+1) (h*(3*f.folded))).sites+
    (power4 (preparePlan n h f).value.m).sites+(bitLength f.cyclic).sites+80≤_
  rw [bitLength_value]
  omega

#print axioms sqrtScan_value
#print axioms foldWidth_value
#print axioms bitLength_value
#print axioms bitLength_sites
#print axioms power4_value
#print axioms clogLoop_value
#print axioms runtimeLowWidth_eq_common
#print axioms preparePlan_m
#print axioms preparePlan_lowWidth_common
#print axioms preparePlan_sites

end ThinMatrix.BinaryTriangleSetupCosts
