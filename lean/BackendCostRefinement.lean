import ThinMatrixBackend
import ReductionCosts
import CachedLowQuery
import CacheDenseLowering
import ComputedPhaseGeometry

/-!
# Cost refinement of the stored backend

These bounds concern the counters returned by the same programs that return
their stored vectors and answers. The full-vector multiplication hypothesis
names the concrete `FullMultiplier.run` calls at the actual capped operands;
it is not a premise bounding backend time by an asymptotic ledger.
-/
namespace ThinMatrix.BackendCostRefinement
noncomputable section
open scoped BigOperators
open ThinMatrixBackend HighBoxDP ThinProductCosts
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000

/-- The actual five-way encoder includes trie insertion and every stored
coefficient, including internal dense suffix arrays. -/
def highEncodingFactor (L : ℕ) : ℕ :=
  70*(2*L+1)+5*(2*L)*(1+4*(2*L))+8*(2*L)+7

def highCallbackBudget (L q fullBudget : ℕ) : ℕ :=
  q+fullBudget+2*(4*L+1)+StoredHighDP.guardTests L

def highFiniteFactor (L q fullBudget : ℕ) : ℕ :=
  2*highEncodingFactor L*q+(2*L+1)^2*
    ArrayKeys.highLayerFactor L q (highCallbackBudget L q fullBudget)

/-- No uncapped multiplication value is required: the uniform budget is
only for the exact operand pairs read from the materialized base stores. -/
theorem prepareHigh_operations_le {L m t q : ℕ} [NeZero q]
    (M : FullMultiplier q) (X Y : CompleteThinProduct.SourceWord L → CyclicRing.Cyclic q)
    (fullBudget : ℕ)
    (hmul : ∀ w : BaseStates L m t,
      (M.run (HighBaseEncoder.readBase (HighBaseEncoder.encodeLeftSource (m:=m) (t:=t) X) w)
        (HighBaseEncoder.readBase (HighBaseEncoder.encodeRightSource (m:=m) (t:=t) Y) w)).2 ≤ fullBudget) :
    (prepareHigh (m:=m) (t:=t) M X Y).operations ≤
      highFiniteFactor L q fullBudget*HighBaseEncoder.baseCount L m t := by
  let left := HighBaseEncoder.encodeLeftSource (m:=m) (t:=t) X
  let right := HighBaseEncoder.encodeRightSource (m:=m) (t:=t) Y
  have hq : 1 ≤ q := Nat.pos_of_neZero q
  have hl := HighBaseEncoder.encodeVector_work (m:=m) (t:=t) true (SourceCoordinates.leftForms L)
    (SourceCoordinates.leftVectorInput X) hq
  have hr := HighBaseEncoder.encodeVector_work (m:=m) (t:=t) false (SourceCoordinates.rightForms L)
    (SourceCoordinates.rightVectorInput Y) hq
  have hbase (w : BaseStates L m t) :
      (cachedBaseProduct (m:=m) (t:=t) M left right w).2 ≤ q+fullBudget+2*(4*L+1) := by
    dsimp [cachedBaseProduct, left, right]
    have h := hmul w
    omega
  have hg (v : LeafWord (2*L)) :
      (StoredHighDP.guardedBase (m:=m) (t:=t) (cachedBaseProduct (m:=m) (t:=t) M left right) v).2 ≤ highCallbackBudget L q fullBudget := by
    exact StoredHighDP.guardedBase_work_le (cachedBaseProduct (m:=m) (t:=t) M left right)
      (q+fullBudget+2*(4*L+1)) hbase (by omega) v
  have hh := ArrayKeys.highExecuteCounted_work_le_bases
    (m:=m) (t:=t) (StoredHighDP.guardedBase (m:=m) (t:=t) (cachedBaseProduct (m:=m) (t:=t) M left right))
    (highCallbackBudget L q fullBudget) hg
  change left.encoding.coefficientWork+left.encoding.capWork+left.trieWork+
    right.encoding.coefficientWork+right.encoding.capWork+right.trieWork+
    (ArrayKeys.highExecuteCounted (m:=m) (t:=t)
      (StoredHighDP.guardedBase (m:=m) (t:=t) (cachedBaseProduct (m:=m) (t:=t) M left right)) (2*L+1)).2 ≤ _
  change left.encoding.coefficientWork+left.encoding.capWork+left.trieWork ≤
    highEncodingFactor L*q*HighBaseEncoder.baseCount L m t at hl
  change right.encoding.coefficientWork+right.encoding.capWork+right.trieWork ≤
    highEncodingFactor L*q*HighBaseEncoder.baseCount L m t at hr
  unfold highFiniteFactor
  unfold HighBaseEncoder.baseCount at hl hr
  change _ ≤ (2*highEncodingFactor L*q+(2*L+1)^2*
    ArrayKeys.highLayerFactor L q (highCallbackBudget L q fullBudget))*Fintype.card (BaseStates L m t)
  nlinarith

lemma highEncodingFactor_le (L : ℕ) : highEncodingFactor L ≤ 300*(L+1)^2 := by
  unfold highEncodingFactor
  nlinarith

lemma highLayerFactor_le (L q fullBudget : ℕ) (hq : 1 ≤ q) :
    ArrayKeys.highLayerFactor L q (highCallbackBudget L q fullBudget) ≤
      400*(L+1)^3*(q+fullBudget) := by
  have hp : 1 ≤ q+fullBudget := by omega
  have hx := Nat.le_mul_of_pos_right
    (96*L^3+100*L^2+72*L+15) (show 0<q+fullBudget by omega)
  have hlin : 12*q+fullBudget ≤ 12*(q+fullBudget) := by omega
  have hpoly : 96*L^3+100*L^2+72*L+27 ≤ 400*(L+1)^3 := by nlinarith
  have hpoly' := Nat.mul_le_mul_right (q+fullBudget) hpoly
  unfold ArrayKeys.highLayerFactor highCallbackBudget StoredHighDP.guardTests
  nlinarith

lemma highFiniteFactor_le (L q fullBudget : ℕ) (hq : 1 ≤ q) :
    highFiniteFactor L q fullBudget ≤ 3000*(L+1)^5*(q+fullBudget) := by
  have he := highEncodingFactor_le L
  have hd := highLayerFactor_le L q fullBudget hq
  have hsq : (2*L+1)^2 ≤ 4*(L+1)^2 := by
    calc
      _ ≤ (2*(L+1))^2 := Nat.pow_le_pow_left (by omega) 2
      _ = _ := by ring
  have hp : (L+1)^2 ≤ (L+1)^5 := Nat.pow_le_pow_right (by omega) (by omega)
  have heq := Nat.mul_le_mul_right q (Nat.mul_le_mul_left 2 he)
  have heq' : 2*highEncodingFactor L*q ≤ 600*(L+1)^5*(q+fullBudget) := by
    calc
      _ ≤ 600*(L+1)^2*q := by nlinarith [heq]
      _ ≤ 600*(L+1)^5*(q+fullBudget) := Nat.mul_le_mul (Nat.mul_le_mul_left 600 hp) (by omega)
  have hd' := Nat.mul_le_mul hsq hd
  have hdp : (2*L+1)^2*ArrayKeys.highLayerFactor L q (highCallbackBudget L q fullBudget) ≤
      1600*(L+1)^5*(q+fullBudget) := by
    convert hd' using 1; ring
  unfold highFiniteFactor
  nlinarith

/-- Every genuine base is also a scheduled state. -/
def baseToState {L m t : ℕ} (w : BaseStates L m t) : States L m t :=
  ⟨w.val, w.property.1, by
    intro i j hi _
    have h := w.property.2 i
    omega⟩

lemma baseToState_injective (L m t : ℕ) : Function.Injective (@baseToState L m t) := by
  intro x y h
  apply Subtype.ext
  exact congrArg (fun v : States L m t => v.val) h

lemma baseCount_le_scheduledWork (L m t : ℕ) :
    HighBaseEncoder.baseCount L m t ≤ HighBoxDP.scheduledWork L m t := by
  have hc := Fintype.card_le_of_injective (@baseToState L m t) (baseToState_injective L m t)
  rw [HighBoxDP.scheduledWork_eq]
  apply hc.trans
  calc
    Fintype.card (States L m t) = ∑ _w : States L m t, 1 := by simp
    _ ≤ HighBoxDP.preprocessingWork L m t := by
      apply Finset.sum_le_sum
      intro w _
      unfold HighBoxDP.stateWork
      split_ifs <;> omega

/-- The Array-key HIGH encoder/DP counter refines the older finite schedule
with only a polynomial physical-length factor. Its cyclic q charge is explicit. -/
theorem prepareHigh_le_old_schedule {L m t q : ℕ} [NeZero q]
    (M : FullMultiplier q) (X Y : CompleteThinProduct.SourceWord L → CyclicRing.Cyclic q)
    (fullBudget : ℕ)
    (hmul : ∀ w : BaseStates L m t,
      (M.run (HighBaseEncoder.readBase (HighBaseEncoder.encodeLeftSource (m:=m) (t:=t) X) w)
        (HighBaseEncoder.readBase (HighBaseEncoder.encodeRightSource (m:=m) (t:=t) Y) w)).2 ≤ fullBudget) :
    (prepareHigh (m:=m) (t:=t) M X Y).operations ≤
      3000*(L+1)^5*highPreprocessingCost L m t q 1 fullBudget := by
  have h := (prepareHigh_operations_le M X Y fullBudget hmul).trans
    (Nat.mul_le_mul_right (HighBaseEncoder.baseCount L m t)
      (highFiniteFactor_le L q fullBudget (Nat.pos_of_neZero q)))
  have hb : HighBaseEncoder.baseCount L m t ≤
      HighBoxDP.scheduledWork L m t+HighBoxDP.preprocessingReads L m t := by
    exact (baseCount_le_scheduledWork L m t).trans (Nat.le_add_right _ _)
  have hb' := Nat.mul_le_mul_left (3000*(L+1)^5*(q+fullBudget)) hb
  apply h.trans (hb'.trans_eq ?_)
  unfold highPreprocessingCost vectorUnit
  ring

/-- Full rounded HIGH preprocessing for the same returned table. -/
theorem rounded_prepareHigh_operations (c theta : ℝ) (m q fullBudget : ℕ) [NeZero q]
    (hc : 5 < c) (ht0 : 0 < theta) (ht1 : theta < 1/2) (hm : 0 < m)
    (M : FullMultiplier q)
    (X Y : CompleteThinProduct.SourceWord (Nat.ceil (c*(m:ℝ))) → CyclicRing.Cyclic q)
    (hmul : ∀ w : BaseStates (Nat.ceil (c*(m:ℝ))) m (Nat.ceil (2*theta*(m:ℝ))),
      (M.run (HighBaseEncoder.readBase (HighBaseEncoder.encodeLeftSource (m:=m) (t:=Nat.ceil (2*theta*(m:ℝ))) X) w)
        (HighBaseEncoder.readBase (HighBaseEncoder.encodeRightSource (m:=m) (t:=Nat.ceil (2*theta*(m:ℝ))) Y) w)).2 ≤ fullBudget) :
    let L := Nat.ceil (c*(m:ℝ))
    ((prepareHigh (m:=m) (t:=Nat.ceil (2*theta*(m:ℝ))) M X Y).operations:ℝ) ≤
      3000*(L+1:ℝ)^5*boxFactor c theta m*(EntropyBounds.gridCount L m)^2*
        ((4:ℝ)^m)^(-HighBoxEntropy.boxSaving c theta)*((q:ℝ)+fullBudget) := by
  let L := Nat.ceil (c*(m:ℝ))
  let t := Nat.ceil (2*theta*(m:ℝ))
  have hf := prepareHigh_le_old_schedule (m:=m) (t:=t) M X Y fullBudget hmul
  have hfR : ((prepareHigh (m:=m) (t:=t) M X Y).operations:ℝ) ≤
      3000*(L+1:ℝ)^5*(highPreprocessingCost L m t q 1 fullBudget:ℝ) := by exact_mod_cast hf
  have hr := ThinProductCosts.rounded_highCost c theta m q 1 fullBudget hc ht0 ht1 hm
  have hr' := mul_le_mul_of_nonneg_left hr (show 0≤3000*(L+1:ℝ)^5 by positivity)
  exact hfR.trans (by simpa only [L, t, Nat.cast_one, mul_one, mul_assoc] using hr')

/-- Magnitude selection uses actual stored coefficient cells. -/
theorem productMagnitude_le {q : ℕ} (a b : Vector ℤ q) (A : ℕ)
    (ha : ∀ r, (a.get r).natAbs ≤ A) (hb : ∀ r, (b.get r).natAbs ≤ A) :
    productMagnitude a b ≤ 1+2*q*A := by
  have hleft : ∑ r : Fin q, (a.get r).natAbs ≤ q*A := by
    calc
      _ ≤ ∑ _r : Fin q, A := Finset.sum_le_sum (fun r _ => ha r)
      _ = _ := by simp
  have hright : ∑ r : Fin q, (b.get r).natAbs ≤ q*A := by
    calc
      _ ≤ ∑ _r : Fin q, A := Finset.sum_le_sum (fun r _ => hb r)
      _ = _ := by simp
  unfold productMagnitude
  nlinarith

/-- A concrete allowance for the actual fixed-point array FFT multiplier.
It is a counted arithmetic/array allowance; a bit-machine simulation is a
separate refinement and is not asserted by this definition. -/
def fftMultiplierAllowance (q A : ℕ) : ℕ :=
  46000*(FastConvolution.paddedExponent q+1)*q*
    (FastConvolution.paddedExponent q+(1+2*q*A).log2+100)^2+10*q

theorem fftFullMultiplier_allowance {q : ℕ} [NeZero q]
    (a b : Vector ℤ q) (A : ℕ)
    (ha : ∀ r, (a.get r).natAbs ≤ A) (hb : ∀ r, (b.get r).natAbs ≤ A) :
    ((fftFullMultiplier q).run a b).2 ≤ fftMultiplierAllowance q A := by
  apply (fftFullMultiplier_work a b).trans
  unfold fftMultiplierAllowance
  have hlog : (productMagnitude a b).log2 ≤ (1+2*q*A).log2 := by
    simp only [Nat.log2_eq_log_two]
    exact Nat.log_mono_right (productMagnitude_le a b A ha hb)
  gcongr

/-- The numerical callback premise for HIGH is instantiated by the actual
FFT program once the stored-vector magnitude invariant is supplied. -/
theorem prepareHigh_fft_allowance {L m t q : ℕ} [NeZero q]
    (X Y : CompleteThinProduct.SourceWord L → CyclicRing.Cyclic q) (A : ℕ)
    (ha : ∀ (w : BaseStates L m t) r,
      ((HighBaseEncoder.readBase (HighBaseEncoder.encodeLeftSource (m:=m) (t:=t) X) w).get r).natAbs ≤ A)
    (hb : ∀ (w : BaseStates L m t) r,
      ((HighBaseEncoder.readBase (HighBaseEncoder.encodeRightSource (m:=m) (t:=t) Y) w).get r).natAbs ≤ A) :
    (prepareHigh (m:=m) (t:=t) (fftFullMultiplier q) X Y).operations ≤
      3000*(L+1)^5*highPreprocessingCost L m t q 1 (fftMultiplierAllowance q A) := by
  exact prepareHigh_le_old_schedule (fftFullMultiplier q) X Y (fftMultiplierAllowance q A)
    (fun w => fftFullMultiplier_allowance _ _ A (ha w) (hb w))

namespace SourceCosts
open SourceFormation WalshEmbedding
def nestedBudget (dims : List ℕ) (B : ℕ) : ℕ := dims.foldr binaryTableBudget B

theorem nestedBudget_le (dims : List ℕ) (B : ℕ) :
    nestedBudget dims B ≤ (B+16*dims.sum)*2^dims.sum := by
  induction dims with
  | nil => simp [nestedBudget]
  | cons n ds ih =>
    have hp : 1 ≤ 2^ds.sum := Nat.one_le_pow _ _ (by norm_num)
    have hn : 16*n ≤ 16*n*2^ds.sum := Nat.le_mul_of_pos_right _ hp
    change binaryTableBudget n (nestedBudget ds B) ≤ _
    calc
      _ ≤ binaryTableBudget n ((B+16*ds.sum)*2^ds.sum) := by
        unfold binaryTableBudget
        exact Nat.mul_le_mul_right _ (Nat.add_le_add_right ih _)
      _ ≤ (B+16*(n+ds.sum))*2^(n+ds.sum) := by
        unfold binaryTableBudget
        rw [pow_add]
        have hn' := Nat.mul_le_mul_right (2^n) hn
        nlinarith
      _ = _ := by simp

theorem inputBudget_exp_bound (L m q : ℕ) (hm : m ≤ L) (hq : 1 ≤ q) :
    inputBudget L m q ≤ 256*(L+m+1)^3*q*2^(4*L+m) := by
  have hsum : ([L,L,L-m,m,m]:List ℕ).sum = 3*L+m := by simp; omega
  have h := nestedBudget_le [L,L,L-m,m,m] ((inputEntryAllowance L m+8)*q)
  change inputBudget L m q ≤ _ at h
  rw [hsum] at h
  have hP : 1 ≤ L+m+1 := by omega
  have hP3 : L+m+1 ≤ (L+m+1)^3 := by simpa using pow_le_pow_right₀ hP (show 1≤3 by omega)
  have hp : 1 ≤ 2^L := Nat.one_le_pow _ _ (by norm_num)
  have hpoly : (inputEntryAllowance L m+8)*q+16*(3*L+m) ≤
      256*(L+m+1)^3*q*2^L := by
    unfold inputEntryAllowance
    have h1 : 16*(3*L+m) ≤ 48*(L+m+1)^3 := by nlinarith
    have h2 : 48*(L+m+1)^3 ≤ 48*(L+m+1)^3*q*2^L := by
      calc
        _ ≤ 48*(L+m+1)^3*q := Nat.le_mul_of_pos_right _ hq
        _ ≤ _ := Nat.le_mul_of_pos_right _ hp
    have h3 : 8*q ≤ 8*(L+m+1)^3*q*2^L := by
      have hP31 : 1 ≤ (L+m+1)^3 := one_le_pow₀ hP
      calc
        8*q ≤ 8*q*(L+m+1)^3 := Nat.le_mul_of_pos_right _ hP31
        _ ≤ 8*q*(L+m+1)^3*2^L := Nat.le_mul_of_pos_right _ hp
        _ = _ := by ring
    nlinarith
  calc
    _ ≤ ((inputEntryAllowance L m+8)*q+16*(3*L+m))*2^(3*L+m) := h
    _ ≤ (256*(L+m+1)^3*q*2^L)*2^(3*L+m) := Nat.mul_le_mul_right _ hpoly
    _ = _ := by rw [mul_assoc, ← pow_add, show L+(3*L+m)=4*L+m by omega]


theorem input_exp_le_raw (L m : ℕ) (hm : 4*m ≤ L) :
    2^(4*L+m) ≤ 12^L*2^(L-m) := by
  have hcore : 2^(3*L+2*m) ≤ 12^L := by
    calc
      _ = (2^14)^m*(2^3)^(L-4*m) := by
        rw [← pow_mul, ← pow_mul, ← pow_add]
        congr 1
        omega
      _ ≤ (12^4)^m*12^(L-4*m) := Nat.mul_le_mul
        (Nat.pow_le_pow_left (by norm_num) m)
        (Nat.pow_le_pow_left (by norm_num) (L-4*m))
      _ = 12^L := by rw [← pow_mul, ← pow_add]; congr 1; omega
  calc
    _ = 2^(3*L+2*m)*2^(L-m) := by rw [← pow_add]; congr 1; omega
    _ ≤ _ := Nat.mul_le_mul_right _ hcore

theorem goodMasks_nodup (L m : ℕ) : (goodMasks L m).Nodup := by
  unfold goodMasks
  exact List.Nodup.map (RowIndexing.cubeEquiv L).symm.injective (RowIndexing.goodCodes_nodup L m)

def readerBudget (L m : ℕ) : ℕ := 8*(3*L+m+1)

theorem prepareSources_budget {L m q : ℕ} [NeZero q]
    (A : Matrix (OuterIndex L m) (InnerIndex m) (CyclicRing.Cyclic q))
    (B : Matrix (InnerIndex m) (OuterIndex L m) (CyclicRing.Cyclic q)) :
    (prepareSources A B).operations ≤ 2*inputBudget L m q +
      32*(L+1)^2*4^L+10*(L+1)^2+
      2*(2*m+1)*sourceBudget L m (L-m) q (readerBudget L m) := by
  have hleft := buildLeftInput_cost A
  have hright := buildRightInput_cost B
  have hgood := prepareGood_cost (goodMasks L m) (goodMasks_nodup L m)
  have hl (run : ℤ) :
      (formLeftSource (sourceEnvironment L m) (leftInputReader (buildLeftInput A).value) run).operations ≤
        sourceBudget L m (L-m) q (readerBudget L m) :=
    formLeftSource_cost (L:=L) (m:=m) (k:=L-m) (q:=q) (B:=readerBudget L m)
      (sourceEnvironment L m) (leftInputReader (L:=L) (m:=m) (q:=q) (buildLeftInput A).value)
      (fun _ _ _ _ _ _ => le_rfl) run
  have hr (run : ℤ) :
      (formRightSource (sourceEnvironment L m) (rightInputReader (buildRightInput B).value) run).operations ≤
        sourceBudget L m (L-m) q (readerBudget L m) :=
    formRightSource_cost (L:=L) (m:=m) (k:=L-m) (q:=q) (B:=readerBudget L m)
      (sourceEnvironment L m) (rightInputReader (L:=L) (m:=m) (q:=q) (buildRightInput B).value)
      (fun _ _ _ _ _ _ => le_rfl) run
  unfold prepareSources
  simp only [Vector.get_ofFn]
  have hs : (∑ i : Fin (2*m+1),
      ((formLeftSource (sourceEnvironment L m) (leftInputReader (buildLeftInput A).value)
        (((sourceRunEquiv m).symm i).val)).operations +
      (formRightSource (sourceEnvironment L m) (rightInputReader (buildRightInput B).value)
        (((sourceRunEquiv m).symm i).val)).operations)) ≤
      2*(2*m+1)*sourceBudget L m (L-m) q (readerBudget L m) := by
    calc
      _ ≤ ∑ _i : Fin (2*m+1), 2*sourceBudget L m (L-m) q (readerBudget L m) := by
        apply Finset.sum_le_sum
        intro i _
        simpa only [two_mul] using Nat.add_le_add (hl (((sourceRunEquiv m).symm i).val)) (hr (((sourceRunEquiv m).symm i).val))
      _ = _ := by simp; ring
  omega



theorem prepareSources_polynomial {L m q : ℕ} [NeZero q]
    (A : Matrix (OuterIndex L m) (InnerIndex m) (CyclicRing.Cyclic q))
    (B : Matrix (InnerIndex m) (OuterIndex L m) (CyclicRing.Cyclic q))
    (hm : 4*m ≤ L) :
    (prepareSources A B).operations ≤
      100000*(L+m+1)^4*q*12^L*2^(L-m) := by
  let P := L+m+1
  let W := q*12^L*2^(L-m)
  have hq : 1 ≤ q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hml : m ≤ L := by omega
  have hP : 1 ≤ P := by omega
  have hinput : inputBudget L m q ≤ 256*P^3*W := by
    calc
      _ ≤ 256*P^3*q*2^(4*L+m) := inputBudget_exp_bound L m q hml hq
      _ ≤ 256*P^3*q*(12^L*2^(L-m)) :=
        Nat.mul_le_mul_left _ (input_exp_le_raw L m hm)
      _ = _ := by dsimp [W]; ring
  have hB : readerBudget L m+1 ≤ 25*P := by unfold readerBudget; dsimp [P]; omega
  have hlen : L+m+(L-m)+1 ≤ 2*P := by dsimp [P]; omega
  have hcoefficient : 200*(readerBudget L m+1)*(L+m+(L-m)+1)^2 ≤ 20000*P^3 := by
    calc
      _ ≤ 200*(25*P)*(2*P)^2 := by gcongr
      _ = _ := by ring
  have hsource : sourceBudget L m (L-m) q (readerBudget L m) ≤ 20000*P^3*W := by
    calc
      _ ≤ 200*(readerBudget L m+1)*(L+m+(L-m)+1)^2*q*12^L*2^(L-m) :=
        sourceBudget_polynomial _ _ _ _ _ hq
      _ ≤ (20000*P^3)*q*12^L*2^(L-m) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hcoefficient))
      _ = _ := by dsimp [W]; ring
  have hpow : 4^L ≤ W := by
    calc
      _ ≤ 12^L := Nat.pow_le_pow_left (by norm_num) L
      _ ≤ q*12^L := Nat.le_mul_of_pos_left _ hq
      _ ≤ _ := Nat.le_mul_of_pos_right _ (Nat.one_le_pow _ _ (by norm_num))
  have hW : 1 ≤ W := (Nat.one_le_pow _ _ (by norm_num)).trans hpow
  have hL : L+1 ≤ P := by dsimp [P]; omega
  have hgood : 32*(L+1)^2*4^L ≤ 32*P^2*W := by gcongr
  have hmeta : 10*(L+1)^2 ≤ 10*P^2*W := by
    calc
      _ ≤ 10*P^2 := by gcongr
      _ ≤ _ := Nat.le_mul_of_pos_right _ hW
  have hrun : 2*(2*m+1)*(20000*P^3) ≤ 80000*P^4 := by
    calc
      _ ≤ (4*P)*(20000*P^3) := by
        apply Nat.mul_le_mul_right
        dsimp [P]
        omega
      _ = _ := by ring
  have hP2 : P^2 ≤ P^4 := pow_le_pow_right₀ hP (by omega)
  have hP3 : P^3 ≤ P^4 := pow_le_pow_right₀ hP (by omega)
  have hpoly : 2*(256*P^3)+32*P^2+10*P^2+2*(2*m+1)*(20000*P^3) ≤
      100000*P^4 := by omega
  calc
    _ ≤ 2*inputBudget L m q+32*(L+1)^2*4^L+10*(L+1)^2+
        2*(2*m+1)*sourceBudget L m (L-m) q (readerBudget L m) := prepareSources_budget A B
    _ ≤ 2*(256*P^3*W)+32*P^2*W+10*P^2*W+2*(2*m+1)*(20000*P^3*W) := by
      exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add
        (Nat.mul_le_mul_left 2 hinput) hgood) hmeta) (Nat.mul_le_mul_left _ hsource)
    _ = (2*(256*P^3)+32*P^2+10*P^2+2*(2*m+1)*(20000*P^3))*W := by ring
    _ ≤ (100000*P^4)*W := Nat.mul_le_mul_right _ hpoly
    _ = _ := by dsimp [P, W]; ring



theorem eventual_prepareSources_fit :
    ∀ᶠ m : ℕ in Filter.atTop, ∀ (q : ℕ) [NeZero q]
      (A : Matrix (OuterIndex (Nat.ceil (RealCertificate.c*(m:ℝ))) m) (InnerIndex m) (CyclicRing.Cyclic q))
      (B : Matrix (InnerIndex m) (OuterIndex (Nat.ceil (RealCertificate.c*(m:ℝ))) m) (CyclicRing.Cyclic q)),
      ((prepareSources A B).operations:ℝ) ≤
        (q:ℝ)*(((4:ℝ)^m)^(2*RealCertificate.T-RealCertificate.G)) := by
  let C : ℝ := 100000*(RealCertificate.c+2)^4
  have hC : 0 ≤ C := by unfold C; positivity
  have hfit := eventual_polynomial_source_fit 4 C hC
  filter_upwards [hfit] with m hm
  intro q inst A B
  let L := Nat.ceil (RealCertificate.c*(m:ℝ))
  have hc : 4 ≤ RealCertificate.c := by norm_num [RealCertificate.c]
  have hceil : RealCertificate.c*(m:ℝ) ≤ (L:ℝ) := Nat.le_ceil _
  have hm0 : 0 ≤ (m:ℝ) := Nat.cast_nonneg m
  have h4m : 4*m ≤ L := by exact_mod_cast (show (4:ℝ)*m ≤ (L:ℝ) by nlinarith)
  have hL : (L:ℝ) ≤ RealCertificate.c*(m:ℝ)+1 :=
    (Nat.ceil_lt_add_one (by positivity : 0 ≤ RealCertificate.c*(m:ℝ))).le
  have hP : (L:ℝ)+(m:ℝ)+1 ≤ (RealCertificate.c+2)*((m:ℝ)+1) := by nlinarith
  have hs := prepareSources_polynomial A B h4m
  have hsR : ((prepareSources A B).operations:ℝ) ≤
      100000*((L:ℝ)+(m:ℝ)+1)^4*(q:ℝ)*(12:ℝ)^L*(2:ℝ)^(L-m) := by exact_mod_cast hs
  calc
    _ ≤ 100000*((L:ℝ)+(m:ℝ)+1)^4*(q:ℝ)*(12:ℝ)^L*(2:ℝ)^(L-m) := hsR
    _ ≤ 100000*((RealCertificate.c+2)*((m:ℝ)+1))^4*(q:ℝ)*(12:ℝ)^L*(2:ℝ)^(L-m) := by gcongr
    _ = (q:ℝ)*(C*((m:ℝ)+1)^4*(12:ℝ)^L*(2:ℝ)^(L-m)) := by unfold C; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hm (Nat.cast_nonneg q)

end SourceCosts

/-- The source preparation exponent is charged against the fifth encoder
slot after dividing by the original full grid, not by an augmented grid. -/
theorem source_cost_div_grid_bound (m q : ℕ) (cost : ℝ) (hm : 0 < m)
    (hcost : cost ≤ (q:ℝ)*((4:ℝ)^m)^(2*RealCertificate.T-RealCertificate.G)) :
    cost/EntropyBounds.gridCount (Nat.ceil (RealCertificate.c*(m:ℝ))) m ≤
      (q:ℝ)*(Nat.ceil (RealCertificate.c*(m:ℝ))+1:ℝ)*
        ((4:ℝ)^m)^RealCertificate.Ebox := by
  let L := Nat.ceil (RealCertificate.c*(m:ℝ))
  let D : ℝ := (4:ℝ)^m
  have hgrid := (EntropyBounds.rounded_gridCount RealCertificate.c m
    (by norm_num [RealCertificate.c]) hm).1
  rw [PhaseGeometry.tileExponent_eq_T] at hgrid
  have hL : 0 < (L+1:ℝ) := by positivity
  have hD : 0 < D := by dsimp [D]; positivity
  have hden : 0 < D^RealCertificate.T/(L+1) := by positivity
  have hgridpos : 0 < EntropyBounds.gridCount L m := hden.trans_le hgrid
  have hpow : D^(2*RealCertificate.T-RealCertificate.G)/D^RealCertificate.T =
      D^RealCertificate.Ebox := by
    rw [← Real.rpow_sub hD]
    unfold RealCertificate.Ebox
    congr 1
    ring
  calc
    cost/EntropyBounds.gridCount L m ≤
        ((q:ℝ)*D^(2*RealCertificate.T-RealCertificate.G))/EntropyBounds.gridCount L m :=
      div_le_div_of_nonneg_right hcost hgridpos.le
    _ ≤ ((q:ℝ)*D^(2*RealCertificate.T-RealCertificate.G))/(D^RealCertificate.T/(L+1)) :=
      div_le_div_of_nonneg_left (by positivity) hden hgrid
    _ = (q:ℝ)*(L+1)*(D^(2*RealCertificate.T-RealCertificate.G)/D^RealCertificate.T) := by
      field_simp
    _ = _ := by rw [hpow]

/-- Direct source formation may also be repeated per tile and charged to
stored-box preprocessing, with the explicit squared grid-rounding loss. -/
theorem source_cost_div_grid_sq_bound (m q : ℕ) (cost : ℝ) (hm : 0 < m)
    (hcost : cost ≤ (q:ℝ)*((4:ℝ)^m)^(2*RealCertificate.T-RealCertificate.G)) :
    cost/(EntropyBounds.gridCount (Nat.ceil (RealCertificate.c*(m:ℝ))) m)^2 ≤
      (q:ℝ)*(Nat.ceil (RealCertificate.c*(m:ℝ))+1:ℝ)^2*
        ((4:ℝ)^m)^(-RealCertificate.G) := by
  let L := Nat.ceil (RealCertificate.c*(m:ℝ))
  let D : ℝ := (4:ℝ)^m
  have hgrid := (EntropyBounds.rounded_gridCount RealCertificate.c m
    (by norm_num [RealCertificate.c]) hm).1
  rw [PhaseGeometry.tileExponent_eq_T] at hgrid
  have hL : 0 < (L+1:ℝ) := by positivity
  have hD : 0 < D := by dsimp [D]; positivity
  have hden : 0 < D^RealCertificate.T/(L+1) := by positivity
  have hgridpos : 0 < EntropyBounds.gridCount L m := hden.trans_le hgrid
  have hgridSq : (D^RealCertificate.T/(L+1))^2 ≤ (EntropyBounds.gridCount L m)^2 := by gcongr
  have hpow : D^(2*RealCertificate.T-RealCertificate.G)/(D^RealCertificate.T)^2 = D^(-RealCertificate.G) := by
    rw [← Real.rpow_mul_natCast hD.le, ← Real.rpow_sub hD]
    congr 1
    ring
  calc
    cost/(EntropyBounds.gridCount L m)^2 ≤
        ((q:ℝ)*D^(2*RealCertificate.T-RealCertificate.G))/(EntropyBounds.gridCount L m)^2 :=
      div_le_div_of_nonneg_right hcost (sq_nonneg _)
    _ ≤ ((q:ℝ)*D^(2*RealCertificate.T-RealCertificate.G))/(D^RealCertificate.T/(L+1))^2 :=
      div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hden) hgridSq
    _ = (q:ℝ)*(L+1)^2*(D^(2*RealCertificate.T-RealCertificate.G)/(D^RealCertificate.T)^2) := by
      field_simp
    _ = _ := by rw [hpow]

/-- Trie insertion/extraction adds only a constant factor to the canonical
per-band coefficient budget, before the separately counted degree runs. -/
lemma lowPreparationFactor_le (L q width : ℕ) (hq : 1 ≤ q) (hw : 1 ≤ width) :
    CachedLowQuery.preparationFactor L q width ≤ 2*encoderPolynomial L*q*width := by
  have he : 18*L+7 ≤ encoderPolynomial L := by
    unfold encoderPolynomial capFactor
    nlinarith
  have hqw : 1 ≤ q*width := by nlinarith
  have hes := Nat.le_mul_of_pos_right (encoderPolynomial L) hqw
  have hid : CachedLowQuery.preparationFactor L q width =
      encoderPolynomial L*(q*width)+18*L+7 := by
    unfold CachedLowQuery.preparationFactor encoderPolynomial capFactor
    ring
  rw [hid]
  nlinarith

/-- All same-degree caches are prepared once into actual dense blocks and
tries, including the underlying shared encoder's returned counters. -/
theorem prepareRunSources_le_old_budget {L m t q width : ℕ} [NeZero q]
    (X Y : Fin (2*m+1) → CompleteThinProduct.SourceWord L → CyclicRing.Cyclic q)
    (hw : 1 ≤ width) :
    (CachedLowQuery.prepareRunSources (t:=t) (width:=width) X Y).2 ≤
      (2*(2*m+1))*(2*encoderPolynomial L*q*width*CacheBounds.retainedLeafCount L m t) := by
  have h := CachedLowQuery.prepareRunSources_work_le (m:=m) (t:=t) hw X Y
  have hp := lowPreparationFactor_le L q width (Nat.pos_of_neZero q) hw
  have hp' := Nat.mul_le_mul_left ((2*m+1)*(2*CacheBounds.retainedLeafCount L m t)) hp
  apply h.trans
  simpa only [mul_assoc, mul_left_comm, mul_comm] using hp'

def lowQueryControl (L m : ℕ) : ℕ :=
  16*(2*m+1)+(2*m+1)*(1+40*(2*L+1)^2)

/-- LOW includes direct channel generation, physical vector keys, trie
lookups, scalar weights and selected length-q convolution dot products. -/
theorem queryLowRuns_le_old_budget {L m t q width : ℕ} [NeZero q]
    (embedding : Vector (Fin (2*L)) (2*m)) (ordinary : Vector (Fin 4) (2*L))
    (caches : CachedLowQuery.RunCaches L m q width) (target : Fin q)
    (hm : m ≤ L) (ht : t ≤ 2*L) (hw : 1 ≤ width) (hwL : width ≤ 2*L+1) :
    (CachedLowQuery.queryLowRuns t embedding ordinary caches target).2 ≤
      lowQueryControl L m*lowCoefficientCost m t q width := by
  have h := CachedLowQuery.queryLowRuns_work_le t embedding ordinary caches target (by omega) ht hwL
  have hw2 : 1 ≤ 5*width^2 := by nlinarith
  have hcost : q*CacheCardinality.channelBall (2*m) t ≤ lowCoefficientCost m t q width := by
    rw [lowCoefficientCost_eq]
    have hmul := Nat.mul_le_mul_left (q*CacheCardinality.channelBall (2*m) t) hw2
    nlinarith
  have hmul := Nat.mul_le_mul_left (lowQueryControl L m) hcost
  exact h.trans (by simpa only [lowQueryControl, mul_assoc] using hmul)

lemma lowQueryControl_le (L m : ℕ) (hm : m ≤ L) :
    lowQueryControl L m ≤ 1000*(L+1)^3 := by
  have hlin : 2*m+1 ≤ 2*(L+1) := by omega
  have hsq : (2*L+1)^2 ≤ 4*(L+1)^2 := by
    calc
      _ ≤ (2*(L+1))^2 := Nat.pow_le_pow_left (by omega) 2
      _ = _ := by ring
  have hP : 1 ≤ (L+1)^2 := by nlinarith
  have hf : 17+40*(2*L+1)^2 ≤ 200*(L+1)^2 := by nlinarith
  have hmul := Nat.mul_le_mul hlin hf
  unfold lowQueryControl
  nlinarith

/-- Selected HIGH reads traverse a materialized physical key and read a
single coefficient. This bound contains no cyclic coefficient scan. -/
theorem highSelectedRead_work {L m t q : ℕ}
    (prepared : PreparedHigh L m t q) (w : States L m t) (r : Fin q) :
    (queryHighState prepared w r).2 = 6*L+2 := queryHighState_work prepared w r

/-- One polynomial factor pays all materialized control refinements. -/
def refinementFactor (L m : ℕ) : ℕ := 10000*(L+m+1)^5

lemma highFactor_le_refinement (L m : ℕ) : 3000*(L+1)^5 ≤ refinementFactor L m := by
  unfold refinementFactor
  exact Nat.mul_le_mul (by norm_num) (Nat.pow_le_pow_left (by omega) _)

lemma lowPreparation_le_refinement (L m : ℕ) : 2*(2*m+1) ≤ refinementFactor L m := by
  have hP : 1 ≤ L+m+1 := by omega
  have hp : L+m+1 ≤ (L+m+1)^5 := by simpa using Nat.pow_le_pow_right hP (show 1≤5 by omega)
  unfold refinementFactor
  omega

lemma lowQuery_le_refinement (L m : ℕ) (hm : m ≤ L) : lowQueryControl L m ≤ refinementFactor L m := by
  apply (lowQueryControl_le L m hm).trans
  have hp : (L+1)^3 ≤ (L+m+1)^5 := by
    calc
      _ ≤ (L+m+1)^3 := Nat.pow_le_pow_left (by omega) _
      _ ≤ _ := Nat.pow_le_pow_right (by omega) (by omega)
  exact Nat.mul_le_mul (by norm_num) hp

lemma highRead_le_refinement (L m : ℕ) : 6*L+2 ≤ refinementFactor L m := by
  have hP : 1 ≤ L+m+1 := by omega
  have hp : L+m+1 ≤ (L+m+1)^5 := by simpa using Nat.pow_le_pow_right hP (show 1≤5 by omega)
  unfold refinementFactor
  omega

def refinementConstant (k : ℕ) : ℝ :=
  10000*((RealCertificate.c+3)*ReductionCosts.Overhead.indexMajor k)^5

/-- Uniform conversion from the actual rounded lengths to logarithmic
control overhead, independent of the chosen candidate primes. -/
theorem actual_refinementFactor_le_polylog (n k : ℕ) (hn : 3 ≤ n)
    (call : PhaseGeometry.PhaseCall AlignedCertificate.R
      (PhaseGeometry.primeScale n AsymptoticCosts.eta k)) :
    (refinementFactor
      (Nat.ceil (RealCertificate.c*(PhaseGeometry.innerPower n call AlignedCertificate.S:ℝ)))
      (PhaseGeometry.innerPower n call AlignedCertificate.S):ℝ) ≤
      refinementConstant k*(Real.log (n:ℝ))^5 := by
  let m := PhaseGeometry.innerPower n call AlignedCertificate.S
  let L := Nat.ceil (RealCertificate.c*(m:ℝ))
  have hL := ReductionCosts.Overhead.actual_roundedLength_le_log n k hn call
  have hm := ReductionCosts.Overhead.actual_innerPower_add_one_le_log n k hn call
  have hc : 0 ≤ RealCertificate.c+3 := by norm_num [RealCertificate.c]
  have hM : 0 ≤ ReductionCosts.Overhead.indexMajor k := by
    unfold ReductionCosts.Overhead.indexMajor
    positivity
  have hlog : 0 ≤ Real.log (n:ℝ) := by linarith [PhaseGeometry.one_le_log_nat n hn]
  have hsum : (L:ℝ)+(m:ℝ)+1 ≤
      ((RealCertificate.c+3)*ReductionCosts.Overhead.indexMajor k)*Real.log (n:ℝ) := by
    change (L:ℝ)+1 ≤ (RealCertificate.c+2)*ReductionCosts.Overhead.indexMajor k*Real.log (n:ℝ) at hL
    change (m:ℝ)+1 ≤ ReductionCosts.Overhead.indexMajor k*Real.log (n:ℝ) at hm
    nlinarith
  calc
    _ = 10000*((L:ℝ)+(m:ℝ)+1)^5 := by simp [refinementFactor, L, m]
    _ ≤ 10000*(((RealCertificate.c+3)*ReductionCosts.Overhead.indexMajor k)*Real.log (n:ℝ))^5 := by gcongr
    _ = _ := by unfold refinementConstant; ring

/-- The logarithmic tensor dimension tends to infinity uniformly over all
actual candidate choices; source-gap thresholds therefore apply uniformly. -/
theorem actual_innerPower_uniformly_large (k M : ℕ) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ call : PhaseGeometry.PhaseCall AlignedCertificate.R
      (PhaseGeometry.primeScale n AsymptoticCosts.eta k),
      M ≤ PhaseGeometry.innerPower n call AlignedCertificate.S := by
  have hb : 0 < AsymptoticCosts.b := by norm_num [AsymptoticCosts.b, AlignedCertificate.b]
  have ht := (tendsto_rpow_atTop hb).comp tendsto_natCast_atTop_atTop
  have hlarge := ht.eventually (Filter.eventually_gt_atTop ((4:ℝ)^M))
  filter_upwards [hlarge, Filter.eventually_ge_atTop (3:ℕ)] with n hn hn3
  intro call
  have hD := (PhaseGeometry.actual_inner_bounds AlignedCertificate.R AlignedCertificate.S n k hn3 call).1
  have hs := (PhaseGeometry.aligned_fold_exponent_range call.factors.length).1
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast (show 1≤n by omega)
  have hpow := Real.rpow_le_rpow_of_exponent_le hn1
    (show AsymptoticCosts.b ≤ AsymptoticCosts.b+PhaseGeometry.foldExponent AlignedCertificate.S call.factors.length by linarith)
  rw [PhaseGeometry.innerDimension_eq_power, Nat.cast_pow, Nat.cast_ofNat] at hD
  by_contra hnot
  have hle : PhaseGeometry.innerPower n call AlignedCertificate.S ≤ M := by omega
  have hf : (4:ℝ)^(PhaseGeometry.innerPower n call AlignedCertificate.S) ≤ (4:ℝ)^M :=
    pow_le_pow_right₀ (by norm_num) hle
  change (4:ℝ)^M < (n:ℝ)^AsymptoticCosts.b at hn
  exact (not_lt_of_ge (hpow.trans (hD.trans hf))) hn

/-- Uniform actual-phase source bound for the SAME SourcePreparation value,
with every full cyclic coefficient retained. -/
theorem actual_sourcePreparation_fit (k : ℕ) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ call : PhaseGeometry.PhaseCall AlignedCertificate.R
      (PhaseGeometry.primeScale n AsymptoticCosts.eta k),
      ∀ (q : ℕ) [NeZero q],
      let m := PhaseGeometry.innerPower n call AlignedCertificate.S
      let L := Nat.ceil (RealCertificate.c*(m:ℝ))
      ∀ (A : Matrix (OuterIndex L m) (InnerIndex m) (CyclicRing.Cyclic q))
        (B : Matrix (InnerIndex m) (OuterIndex L m) (CyclicRing.Cyclic q)),
        ((prepareSources A B).operations:ℝ) ≤
          (q:ℝ)*((4:ℝ)^m)^(2*RealCertificate.T-RealCertificate.G) := by
  obtain ⟨M,hM⟩ := Filter.eventually_atTop.mp SourceCosts.eventual_prepareSources_fit
  filter_upwards [actual_innerPower_uniformly_large k M] with n hn
  intro call q inst
  exact hM (PhaseGeometry.innerPower n call AlignedCertificate.S) (hn call) q

namespace StoredAdapters
open SourceFormation WalshEmbedding
theorem readerAllowance_dominates (L m : ℕ) :
    64*(L+1)^2*(2^L+1)+16*(L+1)^2+100*(L+m+1)^3 ≤
      4*inputEntryAllowance L m := by
  let P := L+m+1
  have hP : 1 ≤ P := by omega
  have hL : L+1 ≤ P := by dsimp [P]; omega
  have h2 : (L+1)^2 ≤ P^3 :=
    (Nat.pow_le_pow_left hL 2).trans (pow_le_pow_right₀ hP (show 2≤3 by omega))
  have hp : 1 ≤ 2^L := Nat.one_le_pow _ _ (by norm_num)
  have hp' : 2^L+1 ≤ 2*2^L := by omega
  have hfirst : 64*(L+1)^2*(2^L+1) ≤ 128*P^3*2^L := by
    calc
      _ ≤ 64*P^3*(2*2^L) := Nat.mul_le_mul (Nat.mul_le_mul_left _ h2) hp'
      _ = _ := by ring
  have hsecond : 16*(L+1)^2 ≤ 16*P^3*2^L := by
    calc
      _ ≤ 16*P^3 := Nat.mul_le_mul_left _ h2
      _ ≤ _ := Nat.le_mul_of_pos_right _ hp
  have hthird : 100*P^3 ≤ 100*P^3*2^L := Nat.le_mul_of_pos_right _ hp
  unfold inputEntryAllowance
  change 64*(L+1)^2*(2^L+1)+16*(L+1)^2+100*P^3 ≤ 4*(100*P^3*2^L)
  nlinarith

theorem originalLeftReader_cost {L m q : ℕ} (layout : RowIndexing.GoodIndexStore L m)
    (data : StoredLeftMatrix L m q) (row : OuterIndex L m) (h : InnerIndex m) (r : Fin q)
    (hm : m ≤ L) :
    (originalLeftReader layout data row h r).operations ≤ 64*(L+1)^2*(2^L+1) :=
  RowIndexing.readOriginalLeftProgram_cost layout data 0 row h r hm

theorem originalRightReader_cost {L m q : ℕ} (layout : RowIndexing.GoodIndexStore L m)
    (data : StoredRightMatrix L m q) (h : InnerIndex m) (col : OuterIndex L m) (r : Fin q)
    (hm : m ≤ L) :
    (originalRightReader layout data h col r).operations ≤ 64*(L+1)^2*(2^L+1) :=
  RowIndexing.readOriginalRightProgram_cost layout data 0 h col r hm

theorem storedRawLeftReader_cost {L m q : ℕ}
    (good : GoodStore L) (hg : ∀ Q, readGoodSet good Q = decide (Q ∈ GoodMapEmbedding.goodSlots L m))
    (layout : RowIndexing.GoodIndexStore L m) (data : StoredLeftMatrix L m q)
    (Q : Finset (Fin L)) (bits : Cube L) (outer : Cube (L-m)) (h1 h2 : Cube m) (r : Fin q)
    (hm : m ≤ L) :
    (storedRawLeftReader good hg layout data Q bits outer h1 h2 r).operations ≤
      4*inputEntryAllowance L m := by
  unfold storedRawLeftReader
  split_ifs with hb
  · dsimp only
    have h := originalLeftReader_cost layout data
      (⟨Q, by rw [hg Q] at hb; exact of_decide_eq_true hb⟩,
        (asCube (compressOutsideProgram Q
          (GoodMapEmbedding.goodSlots_size L m Q (by rw [hg Q] at hb; exact of_decide_eq_true hb)) bits).value,outer))
      (h1,h2) r hm
    exact (Nat.add_le_add_right (Nat.add_le_add_right h (16*(L+1)^2))
      (100*(L+m+1)^3)).trans (readerAllowance_dominates L m)
  · dsimp only
    have h := readerAllowance_dominates L m
    omega

theorem storedRawRightReader_cost {L m q : ℕ}
    (good : GoodStore L) (hg : ∀ Q, readGoodSet good Q = decide (Q ∈ GoodMapEmbedding.goodSlots L m))
    (layout : RowIndexing.GoodIndexStore L m) (data : StoredRightMatrix L m q)
    (Q : Finset (Fin L)) (bits : Cube L) (h1 h2 : Cube m) (outer : Cube (L-m)) (r : Fin q)
    (hm : m ≤ L) :
    (storedRawRightReader good hg layout data Q bits h1 h2 outer r).operations ≤
      4*inputEntryAllowance L m := by
  unfold storedRawRightReader
  split_ifs with hb
  · dsimp only
    have h := originalRightReader_cost layout data (h1,h2)
      (⟨Q, by rw [hg Q] at hb; exact of_decide_eq_true hb⟩,
        (asCube (compressOutsideProgram Q
          (GoodMapEmbedding.goodSlots_size L m Q (by rw [hg Q] at hb; exact of_decide_eq_true hb)) bits).value,outer))
      r hm
    exact (Nat.add_le_add_right (Nat.add_le_add_right h (16*(L+1)^2))
      (100*(L+m+1)^3)).trans (readerAllowance_dominates L m)
  · dsimp only
    have h := readerAllowance_dominates L m
    omega


theorem tableBuild_four_cost {α : Type*} (n B : ℕ)
    (f : (Fin n → Fin 2) → Program α) (hf : ∀ key, (f key).operations ≤ 4*B) :
    (tableBuild 2 n f).operations ≤ 4*binaryTableBudget n B := by
  have h := tableBuild_cost 2 n (4*B) f hf
  have h' : (tableBuild 2 n f).operations ≤ (4*B+16*n)*2^n := by simpa using h
  have hc : 4*B+16*n ≤ 4*(B+16*n) := by omega
  exact h'.trans (by simpa only [binaryTableBudget, Nat.mul_assoc] using Nat.mul_le_mul_right (2^n) hc)

theorem vectorBuild_four_cost {α : Type*} (n B : ℕ)
    (f : Fin n → Program α) (hf : ∀ i, (f i).operations ≤ 4*B) :
    (vectorBuild n f).operations ≤ 4*((B+8)*n) := by
  have h := vectorBuild_cost n (4*B) f hf
  nlinarith

theorem buildLeftAdapter_cost {L m q : ℕ} (read : LeftRead L m (L-m) q)
    (hr : ∀ Q bits outer h1 h2 r, (read Q bits outer h1 h2 r).operations ≤
      4*inputEntryAllowance L m) :
    (buildLeftAdapter read).operations ≤ 4*inputBudget L m q := by
  unfold buildLeftAdapter inputBudget
  apply tableBuild_four_cost
  intro Q
  apply tableBuild_four_cost
  intro bits
  apply tableBuild_four_cost
  intro outer
  apply tableBuild_four_cost
  intro h1
  apply tableBuild_four_cost
  intro h2
  apply vectorBuild_four_cost
  intro r
  exact hr _ _ _ _ _ _

theorem buildRightAdapter_cost {L m q : ℕ} (read : RightRead L m (L-m) q)
    (hr : ∀ Q bits h1 h2 outer r, (read Q bits h1 h2 outer r).operations ≤
      4*inputEntryAllowance L m) :
    (buildRightAdapter read).operations ≤ 4*inputBudget L m q := by
  unfold buildRightAdapter inputBudget
  apply tableBuild_four_cost
  intro Q
  apply tableBuild_four_cost
  intro bits
  apply tableBuild_four_cost
  intro outer
  apply tableBuild_four_cost
  intro h1
  apply tableBuild_four_cost
  intro h2
  apply vectorBuild_four_cost
  intro r
  exact hr _ _ _ _ _ _

end StoredAdapters

/-- Uniform good-map construction is also below the direct source family.
Its individual kernel rank/arithmetic work remains a polynomial primitive unit. -/
theorem goodMap_kernel_source_bound (L m : ℕ) (hm : m ≤ L) :
    GoodSetConstruction.constructionKernelSites L m ≤ 4*L*12^L*2^(L-m) := by
  have h := GoodSetConstruction.constructionKernelSites_fit L m
    (L.choose m*4^(L-m)) hm (le_refl _)
  have hc := Nat.choose_le_two_pow L m
  have he : 4^(L-m)*4^m = 4^L := by rw [← pow_add, Nat.sub_add_cancel hm]
  have hs : L.choose m*4^L ≤ 8^L := by
    calc
      _ ≤ 2^L*4^L := Nat.mul_le_mul_right _ hc
      _ = _ := by rw [← mul_pow]; norm_num
  have hraw : 8^L ≤ 12^L*2^(L-m) := by
    calc
      _ ≤ 12^L := Nat.pow_le_pow_left (by norm_num) _
      _ ≤ _ := Nat.le_mul_of_pos_right _ (Nat.one_le_pow _ _ (by norm_num))
  calc
    _ ≤ 4*L*(L.choose m*4^(L-m))*4^m := h
    _ = 4*L*(L.choose m*4^L) := by
      simpa only [mul_assoc] using congrArg (fun x => 4*L*(L.choose m*x)) he
    _ ≤ 4*L*(12^L*2^(L-m)) := Nat.mul_le_mul_left _ (hs.trans hraw)
    _ = _ := by ring

/-- Source and LOW cache work of one returned physical band. -/
def bandSourceBudget (L m q : ℕ) : ℕ :=
  4*inputBudget L m q+(2*m+1)*SourceFormation.sourceBudget L m (L-m) q (SourceCosts.readerBudget L m)

def bandBudget (L m t q : ℕ) : ℕ := bandSourceBudget L m q+
  (2*m+1)*CacheBounds.retainedLeafCount L m t*CachedLowQuery.preparationFactor L q (2*m+1)

lemma prepareBandRun_operations_le {L m t q : ℕ} [NeZero q] (side : Bool)
    (source : SourceFormation.Program (SourceFormation.RawStore L q)) :
    (prepareBandRun (m:=m) (t:=t) side source).operations ≤
      source.operations+CacheBounds.retainedLeafCount L m t*CachedLowQuery.preparationFactor L q (2*m+1) := by
  have h := CacheDenseLowering.prepareSource_work_le (m:=m) (t:=t) (q:=q) (width:=2*m+1)
    (by omega) side (sourceValue source.value)
  simpa only [prepareBandRun, CacheDenseLowering.prepareSource_refines] using
    Nat.add_le_add_left h source.operations

/-- This bound concerns the SAME actual left-band record reused by all
column tiles. Its stored reader, source runs and LOW trie are all charged. -/
theorem prepareLeftBand_operations_le {L m t q : ℕ} [NeZero q] (shape : ShapePlan L m)
    (data : StoredLeftMatrix L m q) (hm : m ≤ L) :
    (prepareLeftBand (t:=t) shape data).operations ≤ bandBudget L m t q := by
  let reader := storedRawLeftReader shape.environment.good shape.good shape.layout data
  let input := buildLeftAdapter reader
  have hi : input.operations ≤ 4*inputBudget L m q :=
    StoredAdapters.buildLeftAdapter_cost reader (fun Q bits outer h1 h2 r =>
      StoredAdapters.storedRawLeftReader_cost _ _ _ _ Q bits outer h1 h2 r hm)
  have hr (i : Fin (2*m+1)) :
      (prepareBandRun (m:=m) (t:=t) true
        (SourceFormation.formLeftSource shape.environment (leftInputReader input.value)
          (CachedLowQuery.sourceRun i))).operations ≤
      SourceFormation.sourceBudget L m (L-m) q (SourceCosts.readerBudget L m)+
        CacheBounds.retainedLeafCount L m t*CachedLowQuery.preparationFactor L q (2*m+1) := by
    have hs := SourceFormation.formLeftSource_cost (B:=SourceCosts.readerBudget L m)
      shape.environment (leftInputReader input.value) (fun _ _ _ _ _ _ => le_rfl) (CachedLowQuery.sourceRun i)
    exact (prepareBandRun_operations_le true _).trans (Nat.add_le_add_right hs _)
  have hsum := Finset.sum_le_sum (s:=Finset.univ) (fun i (_ : i ∈ Finset.univ) => hr i)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hsum
  simp only [prepareLeftBand, Vector.get_ofFn]
  change input.operations+(∑ i : Fin (2*m+1),
    (prepareBandRun (m:=m) (t:=t) true
      (SourceFormation.formLeftSource shape.environment (leftInputReader input.value)
        (CachedLowQuery.sourceRun i))).operations) ≤ _
  unfold bandBudget bandSourceBudget
  nlinarith

/-- The right-band record has the symmetric same-execution bound. -/
theorem prepareRightBand_operations_le {L m t q : ℕ} [NeZero q] (shape : ShapePlan L m)
    (data : StoredRightMatrix L m q) (hm : m ≤ L) :
    (prepareRightBand (t:=t) shape data).operations ≤ bandBudget L m t q := by
  let reader := storedRawRightReader shape.environment.good shape.good shape.layout data
  let input := buildRightAdapter reader
  have hi : input.operations ≤ 4*inputBudget L m q :=
    StoredAdapters.buildRightAdapter_cost reader (fun Q bits h1 h2 outer r =>
      StoredAdapters.storedRawRightReader_cost _ _ _ _ Q bits h1 h2 outer r hm)
  have hr (i : Fin (2*m+1)) :
      (prepareBandRun (m:=m) (t:=t) false
        (SourceFormation.formRightSource shape.environment (rightInputReader input.value)
          (CachedLowQuery.sourceRun i))).operations ≤
      SourceFormation.sourceBudget L m (L-m) q (SourceCosts.readerBudget L m)+
        CacheBounds.retainedLeafCount L m t*CachedLowQuery.preparationFactor L q (2*m+1) := by
    have hs := SourceFormation.formRightSource_cost (B:=SourceCosts.readerBudget L m)
      shape.environment (rightInputReader input.value) (fun _ _ _ _ _ _ => le_rfl) (CachedLowQuery.sourceRun i)
    exact (prepareBandRun_operations_le false _).trans (Nat.add_le_add_right hs _)
  have hsum := Finset.sum_le_sum (s:=Finset.univ) (fun i (_ : i ∈ Finset.univ) => hr i)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hsum
  simp only [prepareRightBand, Vector.get_ofFn]
  change input.operations+(∑ i : Fin (2*m+1),
    (prepareBandRun (m:=m) (t:=t) false
      (SourceFormation.formRightSource shape.environment (rightInputReader input.value)
        (CachedLowQuery.sourceRun i))).operations) ≤ _
  unfold bandBudget bandSourceBudget
  nlinarith

namespace BandShapeCosts
open SourceFormation SourceCosts
theorem bandSourceBudget_polynomial (L m q : ℕ) (hm : 4*m ≤ L) (hq : 1 ≤ q) :
    bandSourceBudget L m q ≤ 50000*(L+m+1)^4*q*12^L*2^(L-m) := by
  let P := L+m+1
  let W := q*12^L*2^(L-m)
  have hml : m ≤ L := by omega
  have hP : 1 ≤ P := by omega
  have hinput : inputBudget L m q ≤ 256*P^3*W := by
    calc
      _ ≤ 256*P^3*q*2^(4*L+m) := inputBudget_exp_bound L m q hml hq
      _ ≤ 256*P^3*q*(12^L*2^(L-m)) :=
        Nat.mul_le_mul_left _ (input_exp_le_raw L m hm)
      _ = _ := by dsimp [W]; ring
  have hB : readerBudget L m+1 ≤ 25*P := by unfold readerBudget; dsimp [P]; omega
  have hlen : L+m+(L-m)+1 ≤ 2*P := by dsimp [P]; omega
  have hcoefficient : 200*(readerBudget L m+1)*(L+m+(L-m)+1)^2 ≤ 20000*P^3 := by
    calc
      _ ≤ 200*(25*P)*(2*P)^2 := by gcongr
      _ = _ := by ring
  have hsource : sourceBudget L m (L-m) q (readerBudget L m) ≤ 20000*P^3*W := by
    calc
      _ ≤ 200*(readerBudget L m+1)*(L+m+(L-m)+1)^2*q*12^L*2^(L-m) :=
        sourceBudget_polynomial _ _ _ _ _ hq
      _ ≤ (20000*P^3)*q*12^L*2^(L-m) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hcoefficient))
      _ = _ := by dsimp [W]; ring
  have hrun : (2*m+1)*(20000*P^3) ≤ 40000*P^4 := by
    calc
      _ ≤ (2*P)*(20000*P^3) := by
        apply Nat.mul_le_mul_right
        dsimp [P]
        omega
      _ = _ := by ring
  have hP3 : P^3 ≤ P^4 := pow_le_pow_right₀ hP (by omega)
  have hpoly : 4*(256*P^3)+(2*m+1)*(20000*P^3) ≤ 50000*P^4 := by omega
  calc
    _ ≤ 4*(256*P^3*W)+(2*m+1)*(20000*P^3*W) :=
      Nat.add_le_add (Nat.mul_le_mul_left _ hinput) (Nat.mul_le_mul_left _ hsource)
    _ = (4*(256*P^3)+(2*m+1)*(20000*P^3))*W := by ring
    _ ≤ (50000*P^4)*W := Nat.mul_le_mul_right _ hpoly
    _ = _ := by dsimp [P, W]; ring

theorem prepareShape_polynomial (L m q : ℕ) (hm : m ≤ L) (hq : 1 ≤ q) :
    (prepareShape L m).operations ≤ 50000*(L+m+1)^6*q*12^L*2^(L-m) := by
  let P := L+m+1
  let U := 12^L*2^(L-m)
  let W := q*U
  have hP : 1 ≤ P := by omega
  have hL : L+1 ≤ P := by dsimp [P]; omega
  have hraw : 4^L ≤ U := by
    calc
      _ ≤ 12^L := Nat.pow_le_pow_left (by norm_num) L
      _ ≤ _ := Nat.le_mul_of_pos_right _ (Nat.one_le_pow _ _ (by norm_num))
  have hUW : U ≤ W := Nat.le_mul_of_pos_left _ hq
  have hpow : 4^L ≤ W := hraw.trans hUW
  have hfirst : (GoodMapRuntime.construct L m).sites ≤ 20241*P^6*W := by
    calc
      _ ≤ 20241*(L+1)^6*U := GoodMapRuntime.construct_source_budget L m hm
      _ ≤ _ := Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hL 6)) hUW
  have h2 : (L+1)^2 ≤ P^6 :=
    (Nat.pow_le_pow_left hL 2).trans (pow_le_pow_right₀ hP (show 2≤6 by omega))
  have h5 : P^5 ≤ P^6 := Nat.pow_le_pow_right hP (by omega)
  have hgood := prepareGood_cost (runtimeGoodMasks L m) (runtimeGoodMasks_nodup L m)
  have hgood' : (prepareGood (runtimeGoodMasks L m)).operations ≤ 32*P^6*W := by
    calc
      _ ≤ 32*(L+1)^2*4^L := hgood
      _ ≤ _ := Nat.mul_le_mul (Nat.mul_le_mul_left _ h2) hpow
  have hlast : 1000*P^5*4^L ≤ 1000*P^6*W :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ h5) hpow
  change (GoodMapRuntime.construct L m).sites+
    (prepareGood (runtimeGoodMasks L m)).operations+1000*P^5*4^L ≤ _
  have h := Nat.add_le_add (Nat.add_le_add hfirst hgood') hlast
  calc
    _ ≤ 20241*P^6*W+32*P^6*W+1000*P^6*W := h
    _ = 21273*P^6*W := by ring
    _ ≤ 50000*P^6*W := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by norm_num : 21273≤50000))
    _ = _ := by dsimp [P, U, W]; ring


theorem eventual_rounded_polynomial_raw_fit (degree coefficient : ℕ) :
    ∀ᶠ m : ℕ in Filter.atTop, ∀ q : ℕ,
      (coefficient*(Nat.ceil (RealCertificate.c*(m:ℝ))+m+1)^degree*q*
        12^(Nat.ceil (RealCertificate.c*(m:ℝ)))*
        2^(Nat.ceil (RealCertificate.c*(m:ℝ))-m):ℕ) ≤
      (q:ℝ)*(((4:ℝ)^m)^(2*RealCertificate.T-RealCertificate.G)) := by
  let C : ℝ := (coefficient:ℝ)*(RealCertificate.c+2)^degree
  have hc : 0 ≤ RealCertificate.c := by norm_num [RealCertificate.c]
  have hC : 0 ≤ C := by unfold C; positivity
  have hfit := eventual_polynomial_source_fit degree C hC
  filter_upwards [hfit] with m hm
  intro q
  let L := Nat.ceil (RealCertificate.c*(m:ℝ))
  have hL : (L:ℝ) ≤ RealCertificate.c*(m:ℝ)+1 :=
    (Nat.ceil_lt_add_one (by positivity : 0 ≤ RealCertificate.c*(m:ℝ))).le
  have hP : (L:ℝ)+(m:ℝ)+1 ≤ (RealCertificate.c+2)*((m:ℝ)+1) := by nlinarith
  push_cast
  change (coefficient:ℝ)*((L:ℝ)+(m:ℝ)+1)^degree*(q:ℝ)*(12:ℝ)^L*(2:ℝ)^(L-m) ≤ _
  calc
    _ ≤ (coefficient:ℝ)*((RealCertificate.c+2)*((m:ℝ)+1))^degree*(q:ℝ)*(12:ℝ)^L*(2:ℝ)^(L-m) := by gcongr
    _ = (q:ℝ)*(C*((m:ℝ)+1)^degree*(12:ℝ)^L*(2:ℝ)^(L-m)) := by unfold C; rw [mul_pow]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hm (Nat.cast_nonneg q)

theorem eventual_bandSourceBudget_fit :
    ∀ᶠ m : ℕ in Filter.atTop, ∀ q : ℕ, 1 ≤ q →
      (bandSourceBudget (Nat.ceil (RealCertificate.c*(m:ℝ))) m q:ℝ) ≤
        (q:ℝ)*(((4:ℝ)^m)^(2*RealCertificate.T-RealCertificate.G)) := by
  filter_upwards [eventual_rounded_polynomial_raw_fit 4 50000] with m hm
  intro q hq
  have hc : 4 ≤ RealCertificate.c := by norm_num [RealCertificate.c]
  have hceil := Nat.le_ceil (RealCertificate.c*(m:ℝ))
  have hm0 : 0 ≤ (m:ℝ) := Nat.cast_nonneg m
  have h4m : 4*m ≤ Nat.ceil (RealCertificate.c*(m:ℝ)) := by
    exact_mod_cast (show (4:ℝ)*m ≤ (Nat.ceil (RealCertificate.c*(m:ℝ)):ℝ) by nlinarith)
  have h := bandSourceBudget_polynomial _ _ _ h4m hq
  apply le_trans ?_ (hm q)
  exact_mod_cast h

theorem eventual_prepareShape_fit :
    ∀ᶠ m : ℕ in Filter.atTop, ∀ q : ℕ, 1 ≤ q →
      ((prepareShape (Nat.ceil (RealCertificate.c*(m:ℝ))) m).operations:ℝ) ≤
        (q:ℝ)*(((4:ℝ)^m)^(2*RealCertificate.T-RealCertificate.G)) := by
  filter_upwards [eventual_rounded_polynomial_raw_fit 6 50000] with m hm
  intro q hq
  have hc : 1 ≤ RealCertificate.c := by norm_num [RealCertificate.c]
  have hceil := Nat.le_ceil (RealCertificate.c*(m:ℝ))
  have hm0 : 0 ≤ (m:ℝ) := Nat.cast_nonneg m
  have hml : m ≤ Nat.ceil (RealCertificate.c*(m:ℝ)) := by
    exact_mod_cast (show (m:ℝ) ≤ (Nat.ceil (RealCertificate.c*(m:ℝ)):ℝ) by nlinarith)
  have h := prepareShape_polynomial _ _ _ hml hq
  apply le_trans ?_ (hm q)
  exact_mod_cast h

end BandShapeCosts

/-- The actual good-set tiles retain the full-grid exponent with its proved
constant density. No encoder exponent is substituted into this geometry. -/
theorem tileWidth_comparison (L m : ℕ) :
    tileWidth L m ≤ gridSide L m ∧ gridSide L m ≤ 16*tileWidth L m := by
  have hgood : (GoodMapEmbedding.goodSlots L m).card ≤ L.choose m := by
    have h := Finset.card_le_card
      (Finset.filter_subset (fun Q => GoodSetConstruction.restrictionTest
        (GoodSetConstruction.constructGoodMaps L m).1 Q &&
        GoodSetConstruction.restrictionTest (GoodSetConstruction.constructGoodMaps L m).2 Qᶜ)
        (Finset.univ.powersetCard m))
    simpa only [GoodMapEmbedding.goodSlots, Finset.card_powersetCard, Finset.card_univ,
      Fintype.card_fin] using h
  constructor
  · exact Nat.mul_le_mul_right _ hgood
  · have h := Nat.mul_le_mul_right (4^(L-m)) (GoodMapEmbedding.goodSlots_density L m)
    simpa only [tileWidth, gridSide, mul_assoc] using h

/-- Good-set density changes the finite number of bands by at most sixteen. -/
theorem actual_bandCount_le (N L m : ℕ) (hm : m ≤ L) :
    TilingCosts.bandCount N (tileWidth L m) ≤ 16*TilingCosts.bandCount N (gridSide L m) := by
  have hb := tileWidth_pos L m hm
  have hg := ThinProductCosts.gridSide_pos L m hm
  have hpadding := TilingCosts.padding_lower N (gridSide L m) hg
  have hdensity := (tileWidth_comparison L m).2
  apply (ceilDiv_le_iff_le_smul hb).mpr
  change N ≤ tileWidth L m*(16*TilingCosts.bandCount N (gridSide L m))
  calc
    N ≤ TilingCosts.bandCount N (gridSide L m)*gridSide L m := hpadding
    _ ≤ TilingCosts.bandCount N (gridSide L m)*(16*tileWidth L m) :=
      Nat.mul_le_mul_left _ hdensity
    _ = _ := by ring

/-- This finite comparison pays actual good-set tiles before any entropy
or real-power substitution is applied. -/
theorem actual_uniformLedger_le (N Q reads L m enc box residual lookup : ℕ) (hm : m ≤ L) :
    TilingCosts.uniformLedger (TilingCosts.bandCount N (tileWidth L m)) Q reads enc box residual lookup ≤
      256*TilingCosts.uniformLedger (TilingCosts.bandCount N (gridSide L m)) Q reads enc box residual lookup := by
  have hb := actual_bandCount_le N L m hm
  have he := Nat.mul_le_mul_right enc (Nat.mul_le_mul_left 2 hb)
  have ht := Nat.mul_le_mul_right box (Nat.pow_le_pow_left hb 2)
  have hquery := Nat.le_mul_of_pos_left (Q*(residual+reads*lookup)) (show 1≤256 by norm_num)
  unfold TilingCosts.uniformLedger
  nlinarith

/-- Every same-run HIGH table is prepared once per tile. LOW caches remain
in the two band records passed to this actual preparation. -/
theorem prepareTile_operations_le {L m t q : ℕ} [NeZero q] (M : FullMultiplier q)
    (left right : PreparedBand L m q) (fullBudget : ℕ)
    (hmul : ∀ (i : Fin (2*m+1)) (w : BaseStates L m t),
      (M.run
        (HighBaseEncoder.readBase (HighBaseEncoder.encodeLeftSource (m:=m) (t:=t)
          (sourceValue (left.runs.get i).source)) w)
        (HighBaseEncoder.readBase (HighBaseEncoder.encodeRightSource (m:=m) (t:=t)
          (sourceValue (right.runs.get i).source)) w)).2 ≤ fullBudget) :
    (prepareTile (t:=t) M left right).operations ≤
      (2*m+1)*3000*(L+1)^5*highPreprocessingCost L m t q 1 fullBudget := by
  have hs := Finset.sum_le_sum (s:=Finset.univ) (fun (i : Fin (2*m+1)) _ =>
    prepareHigh_le_old_schedule M (sourceValue (left.runs.get i).source)
      (sourceValue (right.runs.get i).source) fullBudget (hmul i))
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hs
  simpa only [prepareTile, Vector.get_ofFn, mul_assoc] using hs

/-- Actual LOW from the two reused band stores includes all generated
channels, all runs and only one requested cyclic coefficient. -/
theorem queryLowFromBands_operations_le {L m t q : ℕ} [NeZero q]
    (left right : PreparedBand L m q) (row col : OuterIndex L m) (r : Fin q)
    (hm : m ≤ L) (ht : t ≤ 2*m) :
    (queryLowFromBands (t:=t) left right row col r).2 ≤
      lowQueryControl L m*lowCoefficientCost m t q (2*m+1) := by
  exact queryLowRuns_le_old_budget _ _ _ r hm (by omega) (by omega) (by omega)

/-- HIGH generates its physical keys and selects one already stored
coefficient per handle. The work factor includes key construction. -/
theorem queryHighFromTile_operations {L m t q : ℕ} [NeZero q]
    (tile : PreparedTile L m t q) (row col : OuterIndex L m) (r : Fin q) (ht : t ≤ 2*m) :
    (queryHighFromTile tile row col r).2 ≤
      (2*m+1)*highKeyWork L (2*m)*highCoefficientReads m t := by
  let d := storedQueryGeometry tile.environment row col
  have hh := List.sum_le_card_nsmul
    ((List.finRange (2*m+1)).map (fun i =>
      (queryHigh rfl d.embedding d.outside d.left_cap d.right_cap (tile.high.get i) r).2))
    ((2*m).choose t*4^t*highKeyWork L (2*m)) (by
      intro x hx
      obtain ⟨i,_,rfl⟩ := List.mem_map.mp hx
      exact queryHigh_work rfl d.embedding d.outside d.left_cap d.right_cap (tile.high.get i) r ht)
  simpa only [queryHighFromTile, List.map_map, Function.comp_def, List.length_map,
    List.length_finRange, highCoefficientReads_eq, smul_eq_mul,
    Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hh

lemma normalization_denominator_size (L : ℕ) : (4^L:ℕ).size ≤ 2*L+1 := by
  apply Nat.size_le.mpr
  have he : (4^L:ℕ) = 2^(2*L) := by rw [show (4:ℕ)=2^2 by norm_num, pow_mul]
  rw [he, pow_succ]
  have hp : 0 < (2:ℕ)^(2*L) := by positivity
  omega

def normalizationBudget (L B : ℕ) : ℕ := 20*(B+1)*(B+2*L+2)+4

def queryRefinement (L m B : ℕ) : ℕ :=
  lowQueryControl L m+(2*m+1)*highKeyWork L (2*m)+normalizationBudget L B+1000*(L+m+1)^5

lemma lowCoefficientCost_pos (m t q width : ℕ) (hq : 1 ≤ q) (hw : 1 ≤ width) :
    1 ≤ lowCoefficientCost m t q width := by
  have hc := CachedLowQuery.channelBall_pos (2*m) t
  rw [lowCoefficientCost_eq]
  have hq0 : 0 < q := by omega
  have hw0 : 0 < width := by omega
  have hc0 : 0 < CacheCardinality.channelBall (2*m) t := by omega
  exact (show 0 < 5*CacheCardinality.channelBall (2*m) t*width^2*q by positivity)

/-- The SAME query result is decoded only after adding LOW and HIGH.
The size premise concerns that complete numerator, not its individual terms. -/
theorem queryTile_operations_le {L m t q : ℕ} [NeZero q]
    (left right : PreparedBand L m q) (tile : PreparedTile L m t q)
    (row col : OuterIndex L m) (r : Fin q) (B : ℕ)
    (hm : m ≤ L) (ht : t ≤ 2*m)
    (hsize : ((queryLowFromBands (t:=t) left right row col r).1+
      (queryHighFromTile tile row col r).1).natAbs.size ≤ B) :
    (queryTile left right tile row col r).2 ≤
      queryRefinement L m B*(lowCoefficientCost m t q (2*m+1)+highCoefficientReads m t) := by
  have hl := queryLowFromBands_operations_le left right row col r hm ht
  have hh := queryHighFromTile_operations tile row col r ht
  have hd := IntegerArithmetic.fixedDenominator_bound (4^L) B
    ((queryLowFromBands (t:=t) left right row col r).1+(queryHighFromTile tile row col r).1) hsize
  have hdsize := normalization_denominator_size L
  have hd' : (IntegerArithmetic.binaryExactDivCounted (4^L)
      ((queryLowFromBands (t:=t) left right row col r).1+(queryHighFromTile tile row col r).1)).2 ≤
      normalizationBudget L B := by
    apply hd.trans
    unfold normalizationBudget
    have h := Nat.mul_le_mul_left (20*(B+1)) (Nat.add_le_add_right (Nat.add_le_add_left hdsize B) 1)
    nlinarith
  have hlow := lowCoefficientCost_pos m t q (2*m+1) (Nat.pos_of_neZero q) (by omega)
  have he : normalizationBudget L B+1000*(L+m+1)^5 ≤
      (normalizationBudget L B+1000*(L+m+1)^5)*lowCoefficientCost m t q (2*m+1) :=
    Nat.le_mul_of_pos_right _ hlow
  change (queryLowFromBands (t:=t) left right row col r).2+
    (queryHighFromTile tile row col r).2+
    (IntegerArithmetic.binaryExactDivCounted (4^L)
      ((queryLowFromBands (t:=t) left right row col r).1+(queryHighFromTile tile row col r).1)).2+
      1000*(L+m+1)^5 ≤ _
  calc
    _ ≤ lowQueryControl L m*lowCoefficientCost m t q (2*m+1)+
        (2*m+1)*highKeyWork L (2*m)*highCoefficientReads m t+normalizationBudget L B+1000*(L+m+1)^5 := by omega
    _ = lowQueryControl L m*lowCoefficientCost m t q (2*m+1)+
        (2*m+1)*highKeyWork L (2*m)*highCoefficientReads m t+
        (normalizationBudget L B+1000*(L+m+1)^5) := by ring
    _ ≤ lowQueryControl L m*lowCoefficientCost m t q (2*m+1)+
        (2*m+1)*highKeyWork L (2*m)*highCoefficientReads m t+
        (normalizationBudget L B+1000*(L+m+1)^5)*lowCoefficientCost m t q (2*m+1) :=
      Nat.add_le_add_left he _
    _ = (lowQueryControl L m+normalizationBudget L B+1000*(L+m+1)^5)*
          lowCoefficientCost m t q (2*m+1)+(2*m+1)*highKeyWork L (2*m)*highCoefficientReads m t := by ring
    _ ≤ queryRefinement L m B*lowCoefficientCost m t q (2*m+1)+
        queryRefinement L m B*highCoefficientReads m t := by
      apply Nat.add_le_add
      · apply Nat.mul_le_mul_right
        unfold queryRefinement
        omega
      · apply Nat.mul_le_mul_right
        unfold queryRefinement
        omega
    _ = _ := by ring

/-- A concrete full-vector allowance, only at the operand pairs actually
used by this returned global preparation. -/
def GlobalMultiplierBudget {N D L m t q : ℕ} [NeZero q] (M : FullMultiplier q)
    (prepared : PreparedGlobal N D L m t q) (fullBudget : ℕ) : Prop :=
  ∀ (b c : Fin (TilingCosts.bandCount N (tileWidth L m))) (i : Fin (2*m+1)) (w : BaseStates L m t),
    (M.run
      (HighBaseEncoder.readBase (HighBaseEncoder.encodeLeftSource (m:=m) (t:=t)
        (sourceValue ((prepared.left.get b).runs.get i).source)) w)
      (HighBaseEncoder.readBase (HighBaseEncoder.encodeRightSource (m:=m) (t:=t)
        (sourceValue ((prepared.right.get c).runs.get i).source)) w)).2 ≤ fullBudget

def globalPreparationBudget (N L m t q fullBudget : ℕ) : ℕ :=
  let bands := TilingCosts.bandCount N (tileWidth L m)
  (prepareShape L m).operations+20*q*bands*tileWidth L m*4^m+
    2*bands*bandBudget L m t q+
    bands^2*((2*m+1)*3000*(L+1)^5*highPreprocessingCost L m t q 1 fullBudget)

/-- Finite composition of the SAME global backend preparation: shape once,
input copies, each band once, and each HIGH tile once. -/
theorem prepareGlobal_operations_le {N D L m t q : ℕ} [NeZero q] (M : FullMultiplier q)
    (A : OriginalLeft N D q) (B : OriginalRight N D q) (hm : m ≤ L) (fullBudget : ℕ)
    (hmul : GlobalMultiplierBudget M (prepareGlobal (L:=L) (m:=m) (t:=t) M A B) fullBudget) :
    (prepareGlobal (L:=L) (m:=m) (t:=t) M A B).operations ≤
      globalPreparationBudget N L m t q fullBudget := by
  let prepared := prepareGlobal (L:=L) (m:=m) (t:=t) M A B
  let R := TilingCosts.bandCount N (tileWidth L m)
  have hl (b : Fin R) : (prepared.left.get b).operations ≤ bandBudget L m t q := by
    simpa only [prepared, prepareGlobal_refines, prepareGlobalReference, prepareGlobalShapeReference, Vector.get_map, Vector.get_ofFn] using
      prepareLeftBand_operations_le (t:=t) (prepareShape L m) (makeLeftBand (L:=L) (m:=m) A b) hm
  have hr (c : Fin R) : (prepared.right.get c).operations ≤ bandBudget L m t q := by
    simpa only [prepared, prepareGlobal_refines, prepareGlobalReference, prepareGlobalShapeReference, Vector.get_map, Vector.get_ofFn] using
      prepareRightBand_operations_le (t:=t) (prepareShape L m) (makeRightBand (L:=L) (m:=m) B c) hm
  have ht (b c : Fin R) : ((prepared.tiles.get b).get c).operations ≤
      (2*m+1)*3000*(L+1)^5*highPreprocessingCost L m t q 1 fullBudget := by
    have h := prepareTile_operations_le (t:=t) M (prepared.left.get b) (prepared.right.get c)
      fullBudget (hmul b c)
    simpa only [prepared, prepareGlobal_refines, prepareGlobalReference, prepareGlobalShapeReference, Vector.get_ofFn] using h
  have hls := Finset.sum_le_sum (s:=Finset.univ) (fun b _ => hl b)
  have hrs := Finset.sum_le_sum (s:=Finset.univ) (fun c _ => hr c)
  have hts := Finset.sum_le_sum (s:=Finset.univ) (fun b _ =>
    Finset.sum_le_sum (s:=Finset.univ) (fun c _ => ht b c))
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hls hrs hts
  change prepared.operations ≤ _
  have he : prepared.operations = (prepareShape L m).operations+20*q*R*tileWidth L m*4^m+
      (∑ b : Fin R, (prepared.left.get b).operations)+(∑ c : Fin R, (prepared.right.get c).operations)+
      ∑ b : Fin R, ∑ c : Fin R, ((prepared.tiles.get b).get c).operations := by
    simp only [prepared, prepareGlobal_refines, prepareGlobalReference, prepareGlobalShapeReference, R]
  rw [he]
  unfold globalPreparationBudget
  change _ ≤ (prepareShape L m).operations+20*q*R*tileWidth L m*4^m+2*R*bandBudget L m t q+
    R^2*((2*m+1)*3000*(L+1)^5*highPreprocessingCost L m t q 1 fullBudget)
  nlinarith

/-- The complete numerator at the actual selected global folded position. -/
def globalNumerator {N D L m t q : ℕ} [NeZero q] (hB : 0 < tileWidth L m)
    (prepared : PreparedGlobal N D L m t q) (i j : Fin N) (r : Fin q) : ℤ :=
  let bi := TilingCosts.locate hB i
  let bj := TilingCosts.locate hB j
  let row := RowIndexing.rowUnrank prepared.shape.layout bi.2
  let col := RowIndexing.rowUnrank prepared.shape.layout bj.2
  (queryLowFromBands (t:=t) (prepared.left.get bi.1) (prepared.right.get bj.1) row col r).1+
    (queryHighFromTile ((prepared.tiles.get bi.1).get bj.1) row col r).1

def globalQueryRefinement (N L m B : ℕ) : ℕ :=
  queryRefinement L m B+1000*(L+m+N.log2+1)^5

/-- The actual global query pays compact locators and complete-numerator
integer division. Stored HIGH reads retain no extra q multiplier. -/
theorem queryGlobal_operations_le {N D L m t q : ℕ} [NeZero q] (hB : 0 < tileWidth L m)
    (prepared : PreparedGlobal N D L m t q) (i j : Fin N) (r : Fin q) (B : ℕ)
    (hm : m ≤ L) (ht : t ≤ 2*m) (hsize : (globalNumerator hB prepared i j r).natAbs.size ≤ B) :
    (queryGlobal hB prepared i j r).2 ≤ globalQueryRefinement N L m B*
      (lowCoefficientCost m t q (2*m+1)+highCoefficientReads m t) := by
  rw [queryGlobal_refines]
  let bi := TilingCosts.locate hB i
  let bj := TilingCosts.locate hB j
  let row := RowIndexing.rowUnrank prepared.shape.layout bi.2
  let col := RowIndexing.rowUnrank prepared.shape.layout bj.2
  have h := queryTile_operations_le (prepared.left.get bi.1) (prepared.right.get bj.1)
    ((prepared.tiles.get bi.1).get bj.1) row col r B hm ht hsize
  have hlow := lowCoefficientCost_pos m t q (2*m+1) (Nat.pos_of_neZero q) (by omega)
  have hbase : 1 ≤ lowCoefficientCost m t q (2*m+1)+highCoefficientReads m t := by omega
  have hloc := Nat.le_mul_of_pos_right (1000*(L+m+N.log2+1)^5) hbase
  change (queryTile (prepared.left.get bi.1) (prepared.right.get bj.1)
    ((prepared.tiles.get bi.1).get bj.1) row col r).2+1000*(L+m+N.log2+1)^5 ≤ _
  unfold globalQueryRefinement
  nlinarith


/-- A list of genuine selected requests is answered from one shared preparation.
The counter is the sum of the exact preparation/query counters returned by the
same payload-producing programs. -/
structure ExecutedRequests (N D L m t q Q : ℕ) where
  prepared : PreparedGlobal N D L m t q
  answers : Vector ℤ Q
  operations : ℕ

noncomputable def executeRequests {N D L m t q Q : ℕ} [NeZero q]
    (hB : 0 < tileWidth L m) (M : FullMultiplier q)
    (A : OriginalLeft N D q) (B : OriginalRight N D q)
    (requests : Vector (TilingCosts.Request N q) Q) : ExecutedRequests N D L m t q Q :=
  let prepared := prepareGlobal (L:=L) (m:=m) (t:=t) M A B
  let answers := Vector.ofFn (fun i : Fin Q =>
    let request := requests.get i
    queryGlobal hB prepared request.row request.column request.coefficient)
  ⟨prepared, answers.map Prod.fst, prepared.operations+∑ i : Fin Q, (answers.get i).2⟩

theorem executeRequests_correct {N D L m t q Q : ℕ} [NeZero q]
    (M : FullMultiplier q) (A : OriginalLeft N D q) (B : OriginalRight N D q)
    (requests : Vector (TilingCosts.Request N q) Q) (hm : m ≤ L) (ht : t ≤ 2*m)
    (hD : D ≤ 4^m) (i : Fin Q) :
    ((executeRequests (t:=t) (tileWidth_pos L m hm) M A B requests).answers.get i) =
      (originalLeftMatrix A * originalRightMatrix B) (requests.get i).row
        (requests.get i).column (requests.get i).coefficient := by
  simpa only [executeRequests, Vector.get_map, Vector.get_ofFn] using
    queryGlobal_correct M hm ht hD A B (requests.get i).row
      (requests.get i).column (requests.get i).coefficient

/-- This is a bound on one actual execution, not an asymptotic runtime
assumption. The two premises name precisely its multiplier operands and the
bit length of each complete, divisible query numerator. -/
theorem executeRequests_operations_le {N D L m t q Q : ℕ} [NeZero q]
    (M : FullMultiplier q) (A : OriginalLeft N D q) (B : OriginalRight N D q)
    (requests : Vector (TilingCosts.Request N q) Q) (hm : m ≤ L) (ht : t ≤ 2*m)
    (fullBudget numeratorBits : ℕ)
    (hmul : GlobalMultiplierBudget M (prepareGlobal (L:=L) (m:=m) (t:=t) M A B) fullBudget)
    (hsize : ∀ i : Fin Q, (globalNumerator (tileWidth_pos L m hm)
      (prepareGlobal (L:=L) (m:=m) (t:=t) M A B) (requests.get i).row
        (requests.get i).column (requests.get i).coefficient).natAbs.size ≤ numeratorBits) :
    (executeRequests (t:=t) (tileWidth_pos L m hm) M A B requests).operations ≤
      globalPreparationBudget N L m t q fullBudget+
      Q*globalQueryRefinement N L m numeratorBits*
        (lowCoefficientCost m t q (2*m+1)+highCoefficientReads m t) := by
  have hp := prepareGlobal_operations_le M A B hm fullBudget hmul
  have hq := Finset.sum_le_sum (s:=Finset.univ) (fun (i : Fin Q) _ =>
    queryGlobal_operations_le (tileWidth_pos L m hm)
      (prepareGlobal (L:=L) (m:=m) (t:=t) M A B) (requests.get i).row
        (requests.get i).column (requests.get i).coefficient numeratorBits hm ht (hsize i))
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hq
  simp only [executeRequests, Vector.get_ofFn]
  exact (Nat.add_le_add hp hq).trans (by ring_nf; rfl)

def commonFactor (N L m B : ℕ) : ℕ :=
  2*(2*m+1)+(2*m+1)*3000*(L+1)^5+globalQueryRefinement N L m B

theorem weighted_uniformLedger_le (R Q reads enc box residual a b c : ℕ) :
    2*R*(a*enc)+R^2*(b*box)+Q*(c*(residual+reads)) ≤
      (a+b+c)*TilingCosts.uniformLedger R Q reads enc box residual 1 := by
  have ha : a ≤ a+b+c := by omega
  have hb : b ≤ a+b+c := by omega
  have hc : c ≤ a+b+c := by omega
  calc
    _ ≤ 2*R*((a+b+c)*enc)+R^2*((a+b+c)*box)+Q*((a+b+c)*(residual+reads)) :=
      Nat.add_le_add (Nat.add_le_add
        (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ ha))
        (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hb)))
        (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hc))
    _ = _ := by unfold TilingCosts.uniformLedger; ring

theorem global_finite_comparison (N Q L m t q fullBudget B : ℕ)
    (hm : m ≤ L) (hq : 1 ≤ q) :
    globalPreparationBudget N L m t q fullBudget+
      Q*globalQueryRefinement N L m B*
        (lowCoefficientCost m t q (2*m+1)+highCoefficientReads m t) ≤
      256*commonFactor N L m B*uniformCost N Q L m t q (2*m+1) 1 fullBudget 1 +
        (prepareShape L m).operations+
        20*q*TilingCosts.bandCount N (tileWidth L m)*tileWidth L m*4^m+
        2*TilingCosts.bandCount N (tileWidth L m)*bandSourceBudget L m q := by
  let R := TilingCosts.bandCount N (tileWidth L m)
  let enc := encoderPolynomial L*q*(2*m+1)*CacheBounds.retainedLeafCount L m t
  let box := highPreprocessingCost L m t q 1 fullBudget
  let low := lowCoefficientCost m t q (2*m+1)
  let reads := highCoefficientReads m t
  let a := 2*(2*m+1)
  let b := (2*m+1)*3000*(L+1)^5
  let c := globalQueryRefinement N L m B
  let extra := (prepareShape L m).operations+20*q*R*tileWidth L m*4^m+
    2*R*bandSourceBudget L m q
  have hprep := lowPreparationFactor_le L q (2*m+1) hq (by omega)
  have hband : bandBudget L m t q ≤ bandSourceBudget L m q+a*enc := by
    unfold bandBudget
    have h := Nat.mul_le_mul_left ((2*m+1)*CacheBounds.retainedLeafCount L m t) hprep
    dsimp only [a, enc]
    nlinarith
  have hprepare : globalPreparationBudget N L m t q fullBudget ≤
      extra+2*R*(a*enc)+R^2*(b*box) := by
    have h := Nat.mul_le_mul_left (2*R) hband
    unfold globalPreparationBudget
    change (prepareShape L m).operations+20*q*R*tileWidth L m*4^m+
      2*R*bandBudget L m t q+R^2*(b*box) ≤ _
    dsimp only [extra]
    nlinarith
  have hfirst : globalPreparationBudget N L m t q fullBudget+Q*c*(low+reads) ≤
      extra+commonFactor N L m B*TilingCosts.uniformLedger R Q reads enc box low 1 := by
    calc
      _ ≤ extra+(2*R*(a*enc)+R^2*(b*box)+Q*(c*(low+reads))) := by nlinarith
      _ ≤ extra+(a+b+c)*TilingCosts.uniformLedger R Q reads enc box low 1 :=
        Nat.add_le_add_left (weighted_uniformLedger_le R Q reads enc box low a b c) extra
      _ = _ := rfl
  have hswitch := actual_uniformLedger_le N Q reads L m enc box low 1 hm
  have hscaled := Nat.mul_le_mul_left (commonFactor N L m B) hswitch
  change _ ≤ _ at hfirst
  calc
    _ ≤ extra+commonFactor N L m B*TilingCosts.uniformLedger R Q reads enc box low 1 := hfirst
    _ ≤ extra+commonFactor N L m B*(256*TilingCosts.uniformLedger
        (TilingCosts.bandCount N (gridSide L m)) Q reads enc box low 1) :=
      Nat.add_le_add_left hscaled extra
    _ = _ := by dsimp [extra, R, enc, box, low, reads, uniformCost]; ring


theorem source_extras_bound (N m q : ℕ) (hm : 0 < m)
    (hgeometry : gridSide (Nat.ceil (RealCertificate.c*(m:ℝ))) m ≤ N)
    (hband : (bandSourceBudget (Nat.ceil (RealCertificate.c*(m:ℝ))) m q:ℝ) ≤
      (q:ℝ)*((4:ℝ)^m)^(2*RealCertificate.T-RealCertificate.G))
    (hshape : ((prepareShape (Nat.ceil (RealCertificate.c*(m:ℝ))) m).operations:ℝ) ≤
      (q:ℝ)*((4:ℝ)^m)^(2*RealCertificate.T-RealCertificate.G)) :
    let L := Nat.ceil (RealCertificate.c*(m:ℝ))
    ((prepareShape L m).operations:ℝ)+
      2*(TilingCosts.bandCount N (tileWidth L m):ℝ)*(bandSourceBudget L m q:ℝ) ≤
      64*(q:ℝ)*N*((L:ℝ)+1)*((4:ℝ)^m)^RealCertificate.Ebox+
      (q:ℝ)*(N:ℝ)^2*((L:ℝ)+1)^2*((4:ℝ)^m)^(-RealCertificate.G) := by
  let L := Nat.ceil (RealCertificate.c*(m:ℝ))
  let grid : ℝ := EntropyBounds.gridCount L m
  let R := TilingCosts.bandCount N (tileWidth L m)
  have hc : 1 ≤ RealCertificate.c := by norm_num [RealCertificate.c]
  have hceil := Nat.le_ceil (RealCertificate.c*(m:ℝ))
  have hm0 : 0 ≤ (m:ℝ) := Nat.cast_nonneg m
  have hmL : m ≤ L := by exact_mod_cast (show (m:ℝ) ≤ (L:ℝ) by nlinarith)
  have hgridNat := gridSide_pos L m hmL
  have hgridPos : 0 < grid := by dsimp only [grid]; rw [← gridSide_cast]; exact_mod_cast hgridNat
  have hgridN : grid ≤ (N:ℝ) := by dsimp only [grid]; rw [← gridSide_cast]; exact_mod_cast hgeometry
  have hRold : (R:ℝ) ≤ 16*(TilingCosts.bandCount N (gridSide L m):ℝ) := by
    exact_mod_cast actual_bandCount_le N L m hmL
  have hRcanonical := TilingCosts.bandCount_real_bound N (gridSide L m) hgridNat hgeometry
  rw [gridSide_cast] at hRcanonical
  have hR : (R:ℝ) ≤ 32*(N:ℝ)/grid := by
    calc
      _ ≤ 16*(TilingCosts.bandCount N (gridSide L m):ℝ) := hRold
      _ ≤ 16*(2*(N:ℝ)/grid) := mul_le_mul_of_nonneg_left hRcanonical (by norm_num)
      _ = _ := by ring
  have hbandDiv := source_cost_div_grid_bound m q (bandSourceBudget L m q:ℝ) hm hband
  have hbandBound : 2*(R:ℝ)*(bandSourceBudget L m q:ℝ) ≤
      64*(q:ℝ)*N*((L:ℝ)+1)*((4:ℝ)^m)^RealCertificate.Ebox := by
    calc
      _ ≤ 2*(32*(N:ℝ)/grid)*(bandSourceBudget L m q:ℝ) := by gcongr
      _ = 64*(N:ℝ)*((bandSourceBudget L m q:ℝ)/grid) := by ring
      _ ≤ 64*(N:ℝ)*((q:ℝ)*((L:ℝ)+1)*((4:ℝ)^m)^RealCertificate.Ebox) :=
        mul_le_mul_of_nonneg_left hbandDiv (by positivity)
      _ = _ := by ring
  have hshapeDiv := source_cost_div_grid_sq_bound m q ((prepareShape L m).operations:ℝ) hm hshape
  have hgridSq : grid^2 ≤ (N:ℝ)^2 := by gcongr
  have hshapeBound : ((prepareShape L m).operations:ℝ) ≤
      (q:ℝ)*(N:ℝ)^2*((L:ℝ)+1)^2*((4:ℝ)^m)^(-RealCertificate.G) := by
    calc
      _ = grid^2*(((prepareShape L m).operations:ℝ)/grid^2) := by field_simp
      _ ≤ (N:ℝ)^2*(((prepareShape L m).operations:ℝ)/grid^2) :=
        mul_le_mul_of_nonneg_right hgridSq (by positivity)
      _ ≤ (N:ℝ)^2*((q:ℝ)*((L:ℝ)+1)^2*((4:ℝ)^m)^(-RealCertificate.G)) :=
        mul_le_mul_of_nonneg_left hshapeDiv (by positivity)
      _ = _ := by ring
  change _ ≤ _
  linarith

theorem inputCopies_bound (N L m q : ℕ) (hm : m ≤ L) (hgeometry : gridSide L m ≤ N) :
    20*q*TilingCosts.bandCount N (tileWidth L m)*tileWidth L m*4^m ≤
      40*q*N*4^m := by
  have htile := tileWidth_pos L m hm
  have htileN := (tileWidth_comparison L m).1.trans hgeometry
  have h := TilingCosts.padding_upper N (tileWidth L m) htile htileN
  have h' : TilingCosts.bandCount N (tileWidth L m)*tileWidth L m ≤ 2*N := h
  calc
    _ = (20*q)*(TilingCosts.bandCount N (tileWidth L m)*tileWidth L m)*4^m := by ring
    _ ≤ (20*q)*(2*N)*4^m := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ h')
    _ = _ := by ring

/-- Exact homogeneity isolates one scalar primitive allowance. Full-vector
multiplication retains its full q-dependent concrete counter. -/
theorem uniformCost_scale (N Q L m t q width fullBudget scalarUnit : ℕ) :
    uniformCost N Q L m t q width 1 fullBudget 1*scalarUnit =
      uniformCost N Q L m t q width scalarUnit (fullBudget*scalarUnit) scalarUnit := by
  unfold uniformCost TilingCosts.uniformLedger highPreprocessingCost vectorUnit
  ring

/-- One scalar allowance charges every returned scalar/array site of the
same executed requests. No backend-time domination premise is used. -/
theorem executeRequests_scalar_ledger {N D L m t q Q : ℕ} [NeZero q]
    (M : FullMultiplier q) (A : OriginalLeft N D q) (B : OriginalRight N D q)
    (requests : Vector (TilingCosts.Request N q) Q) (hm : m ≤ L) (ht : t ≤ 2*m)
    (fullBudget numeratorBits scalarUnit : ℕ)
    (hmul : GlobalMultiplierBudget M (prepareGlobal (L:=L) (m:=m) (t:=t) M A B) fullBudget)
    (hsize : ∀ i : Fin Q, (globalNumerator (tileWidth_pos L m hm)
      (prepareGlobal (L:=L) (m:=m) (t:=t) M A B) (requests.get i).row
        (requests.get i).column (requests.get i).coefficient).natAbs.size ≤ numeratorBits) :
    (executeRequests (t:=t) (tileWidth_pos L m hm) M A B requests).operations*scalarUnit ≤
      256*commonFactor N L m numeratorBits*
        uniformCost N Q L m t q (2*m+1) scalarUnit (fullBudget*scalarUnit) scalarUnit+
      ((prepareShape L m).operations+
        20*q*TilingCosts.bandCount N (tileWidth L m)*tileWidth L m*4^m+
        2*TilingCosts.bandCount N (tileWidth L m)*bandSourceBudget L m q)*scalarUnit := by
  have he := executeRequests_operations_le M A B requests hm ht fullBudget numeratorBits hmul hsize
  have hc := global_finite_comparison N Q L m t q fullBudget numeratorBits hm (Nat.pos_of_neZero q)
  have h := Nat.mul_le_mul_right scalarUnit (he.trans hc)
  calc
    _ ≤ (256*commonFactor N L m numeratorBits*uniformCost N Q L m t q (2*m+1) 1 fullBudget 1+
      (prepareShape L m).operations+
      20*q*TilingCosts.bandCount N (tileWidth L m)*tileWidth L m*4^m+
      2*TilingCosts.bandCount N (tileWidth L m)*bandSourceBudget L m q)*scalarUnit := h
    _ = _ := by rw [show (256*commonFactor N L m numeratorBits*uniformCost N Q L m t q (2*m+1) 1 fullBudget 1+
      (prepareShape L m).operations+
      20*q*TilingCosts.bandCount N (tileWidth L m)*tileWidth L m*4^m+
      2*TilingCosts.bandCount N (tileWidth L m)*bandSourceBudget L m q)*scalarUnit =
      256*commonFactor N L m numeratorBits*(uniformCost N Q L m t q (2*m+1) 1 fullBudget 1*scalarUnit)+
      ((prepareShape L m).operations+
      20*q*TilingCosts.bandCount N (tileWidth L m)*tileWidth L m*4^m+
      2*TilingCosts.bandCount N (tileWidth L m)*bandSourceBudget L m q)*scalarUnit by ring,
      uniformCost_scale]



/-- Rounded six-term bound for the actual shared preparation and genuine
selected requests. The direct source family and setup have their own charged
terms; full vectors and LOW products retain q, while HIGH lookups are scalar. -/
def roundedCostBound (N Q m q fullBudget numeratorBits scalarUnit : ℕ) : ℝ :=
  let L := Nat.ceil (RealCertificate.c*(m:ℝ))
  256*(commonFactor N L m numeratorBits:ℝ)*
    powerBound RealCertificate.c RealCertificate.theta N Q m q (2*m+1)
      scalarUnit (fullBudget*scalarUnit) scalarUnit+
    (40*(q:ℝ)*N*(4:ℝ)^m+
      64*(q:ℝ)*N*((L:ℝ)+1)*((4:ℝ)^m)^RealCertificate.Ebox+
      (q:ℝ)*(N:ℝ)^2*((L:ℝ)+1)^2*((4:ℝ)^m)^(-RealCertificate.G))*scalarUnit

theorem rounded_executeRequests_bound {N D L m t q Q : ℕ} [NeZero q]
    (M : FullMultiplier q) (A : OriginalLeft N D q) (B : OriginalRight N D q)
    (requests : Vector (TilingCosts.Request N q) Q) (hm : m ≤ L) (ht : t ≤ 2*m)
    (hm0 : 0 < m) (hL : L=Nat.ceil (RealCertificate.c*(m:ℝ)))
    (htheta : t=Nat.ceil (2*RealCertificate.theta*(m:ℝ)))
    (hgeometry : gridSide L m ≤ N) (fullBudget numeratorBits scalarUnit : ℕ)
    (hmul : GlobalMultiplierBudget M (prepareGlobal (L:=L) (m:=m) (t:=t) M A B) fullBudget)
    (hsize : ∀ i : Fin Q, (globalNumerator (tileWidth_pos L m hm)
      (prepareGlobal (L:=L) (m:=m) (t:=t) M A B) (requests.get i).row
        (requests.get i).column (requests.get i).coefficient).natAbs.size ≤ numeratorBits)
    (hband : (bandSourceBudget L m q:ℝ) ≤
      (q:ℝ)*((4:ℝ)^m)^(2*RealCertificate.T-RealCertificate.G))
    (hshape : ((prepareShape L m).operations:ℝ) ≤
      (q:ℝ)*((4:ℝ)^m)^(2*RealCertificate.T-RealCertificate.G)) :
    ((executeRequests (t:=t) (tileWidth_pos L m hm) M A B requests).operations*scalarUnit:ℕ) ≤
      roundedCostBound N Q m q fullBudget numeratorBits scalarUnit := by
  subst L
  subst t
  let L := Nat.ceil (RealCertificate.c*(m:ℝ))
  let t := Nat.ceil (2*RealCertificate.theta*(m:ℝ))
  have hn := executeRequests_scalar_ledger M A B requests hm ht fullBudget numeratorBits scalarUnit hmul hsize
  have hf : (((executeRequests (t:=t) (tileWidth_pos L m hm) M A B requests).operations*scalarUnit:ℕ):ℝ) ≤
      256*(commonFactor N L m numeratorBits:ℝ)*
        (uniformCost N Q L m t q (2*m+1) scalarUnit (fullBudget*scalarUnit) scalarUnit:ℝ)+
      (((prepareShape L m).operations:ℝ)+
        20*(q:ℝ)*TilingCosts.bandCount N (tileWidth L m)*tileWidth L m*(4:ℝ)^m+
        2*(TilingCosts.bandCount N (tileWidth L m):ℝ)*bandSourceBudget L m q)*scalarUnit := by
    exact_mod_cast hn
  have hp := rounded_uniform_power RealCertificate.c RealCertificate.theta N Q m q (2*m+1)
    scalarUnit (fullBudget*scalarUnit) scalarUnit
    (by norm_num [RealCertificate.c]) (by norm_num [RealCertificate.theta])
    (by norm_num [RealCertificate.theta]) hm0 hgeometry
  have hs := source_extras_bound N m q hm0 hgeometry hband hshape
  have hc : 20*(q:ℝ)*TilingCosts.bandCount N (tileWidth L m)*tileWidth L m*(4:ℝ)^m ≤
      40*(q:ℝ)*N*(4:ℝ)^m := by
    exact_mod_cast inputCopies_bound N L m q hm hgeometry
  have he : ((prepareShape L m).operations:ℝ)+
      20*(q:ℝ)*TilingCosts.bandCount N (tileWidth L m)*tileWidth L m*(4:ℝ)^m+
      2*(TilingCosts.bandCount N (tileWidth L m):ℝ)*bandSourceBudget L m q ≤
      40*(q:ℝ)*N*(4:ℝ)^m+
      64*(q:ℝ)*N*((L:ℝ)+1)*((4:ℝ)^m)^RealCertificate.Ebox+
      (q:ℝ)*(N:ℝ)^2*((L:ℝ)+1)^2*((4:ℝ)^m)^(-RealCertificate.G) := by
    dsimp only at hs
    linarith
  have hp' := mul_le_mul_of_nonneg_left hp (show 0 ≤ 256*(commonFactor N L m numeratorBits:ℝ) by positivity)
  have he' := mul_le_mul_of_nonneg_right he (Nat.cast_nonneg scalarUnit)
  exact hf.trans (by dsimp only [roundedCostBound]; linarith)


theorem commonFactor_polynomial (N L m B : ℕ) :
    commonFactor N L m B ≤ 100000000*(L+m+B+N.log2+1)^6 := by
  let P := L+m+B+N.log2+1
  have hP : 1 ≤ P := by omega
  have hL : L+1 ≤ P := by dsimp [P]; omega
  have hm : 2*m+1 ≤ 2*P := by dsimp [P]; omega
  have h2L : 2*L+1 ≤ 2*P := by dsimp [P]; omega
  have hLm : L+2*m+1 ≤ 2*P := by dsimp [P]; omega
  have hB : B+1 ≤ P := by dsimp [P]; omega
  have hBL : B+2*L+2 ≤ 2*P := by dsimp [P]; omega
  have hLM : L+m+1 ≤ P := by dsimp [P]; omega
  have hLMN : L+m+N.log2+1 ≤ P := by dsimp [P]; omega
  have hP1 : P ≤ P^6 := by simpa using pow_le_pow_right₀ hP (show 1≤6 by omega)
  have hP2 : P^2 ≤ P^6 := pow_le_pow_right₀ hP (by omega)
  have hP3 : P^3 ≤ P^6 := pow_le_pow_right₀ hP (by omega)
  have hP5 : P^5 ≤ P^6 := pow_le_pow_right₀ hP (by omega)
  have hP0 : 1 ≤ P^6 := one_le_pow₀ hP
  have ha : 2*(2*m+1) ≤ 4*P^6 := by
    calc
      _ ≤ 2*(2*P) := Nat.mul_le_mul_left _ hm
      _ = 4*P := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ hP1
  have hb : (2*m+1)*3000*(L+1)^5 ≤ 6000*P^6 := by
    calc
      _ ≤ (2*P)*3000*P^5 := Nat.mul_le_mul (Nat.mul_le_mul_right _ hm) (Nat.pow_le_pow_left hL 5)
      _ = _ := by ring
  have hlow : lowQueryControl L m ≤ 354*P^6 := by
    calc
      _ ≤ 16*(2*P)+(2*P)*(1+40*(2*P)^2) := by
        unfold lowQueryControl
        exact Nat.add_le_add (Nat.mul_le_mul_left _ hm)
          (Nat.mul_le_mul hm (Nat.add_le_add_left
            (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h2L 2)) _))
      _ = 34*P+320*P^3 := by ring
      _ ≤ 34*P^6+320*P^6 := Nat.add_le_add (Nat.mul_le_mul_left _ hP1) (Nat.mul_le_mul_left _ hP3)
      _ = _ := by ring
  have hhigh : (2*m+1)*highKeyWork L (2*m) ≤ 640000*P^6 := by
    calc
      _ ≤ (2*P)*(10000*(2*P)^5) := Nat.mul_le_mul hm
        ((highKeyWork_bound L (2*m)).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hLm 5)))
      _ = _ := by ring
  have hnorm : normalizationBudget L B ≤ 44*P^6 := by
    calc
      _ ≤ 20*P*(2*P)+4 := by
        unfold normalizationBudget
        exact Nat.add_le_add_right (Nat.mul_le_mul (Nat.mul_le_mul_left _ hB) hBL) _
      _ = 40*P^2+4*1 := by ring
      _ ≤ 40*P^6+4*P^6 := Nat.add_le_add (Nat.mul_le_mul_left _ hP2) (Nat.mul_le_mul_left _ hP0)
      _ = _ := by ring
  have hmeta : 1000*(L+m+1)^5 ≤ 1000*P^6 :=
    Nat.mul_le_mul_left _ ((Nat.pow_le_pow_left hLM 5).trans hP5)
  have hglobal : 1000*(L+m+N.log2+1)^5 ≤ 1000*P^6 :=
    Nat.mul_le_mul_left _ ((Nat.pow_le_pow_left hLMN 5).trans hP5)
  have hc : globalQueryRefinement N L m B ≤ 642398*P^6 := by
    unfold globalQueryRefinement queryRefinement
    calc
      _ ≤ 354*P^6+640000*P^6+44*P^6+1000*P^6+1000*P^6 :=
        Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hlow hhigh) hnorm) hmeta) hglobal
      _ = _ := by ring
  unfold commonFactor
  calc
    _ ≤ 4*P^6+6000*P^6+642398*P^6 := Nat.add_le_add (Nat.add_le_add ha hb) hc
    _ = 648402*P^6 := by ring
    _ ≤ 100000000*P^6 := Nat.mul_le_mul_right _ (by norm_num : 648402≤100000000)

/-- The strict direct-source gap applies uniformly to every actual computed
candidate phase, independently of its selected prime history. -/
theorem computed_source_budgets_fit (R S : ℕ) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ call : ComputedPhaseGeometry.Call R n, ∀ q : ℕ, 1 ≤ q →
      let m := ComputedPhaseGeometry.innerPower n call S
      let L := Nat.ceil (RealCertificate.c*(m:ℝ))
      (bandSourceBudget L m q:ℝ) ≤ (q:ℝ)*((4:ℝ)^m)^(2*RealCertificate.T-RealCertificate.G) ∧
      ((prepareShape L m).operations:ℝ) ≤ (q:ℝ)*((4:ℝ)^m)^(2*RealCertificate.T-RealCertificate.G) := by
  obtain ⟨M,hM⟩ := Filter.eventually_atTop.mp
    (BandShapeCosts.eventual_bandSourceBudget_fit.and BandShapeCosts.eventual_prepareShape_fit)
  filter_upwards [ComputedPhaseGeometry.actual_innerPower_uniformly_large R M] with n hn
  intro call q hq
  exact ⟨(hM _ (hn call S)).1 q hq,(hM _ (hn call S)).2 q hq⟩

/-- Explicit logarithmic control cost at the actual computed dimensions.
The bit allowance names the complete numerator width, derived downstream from
original input coefficient bounds. -/
theorem computed_commonFactor_le_polylog (R S n numeratorBits : ℕ) (hn : 3 ≤ n)
    (call : ComputedPhaseGeometry.Call R n) (Cbits : ℝ)
    (hbits : (numeratorBits:ℝ) ≤ Cbits*Real.log (n:ℝ)) :
    let m := ComputedPhaseGeometry.innerPower n call S
    let L := Nat.ceil (RealCertificate.c*(m:ℝ))
    (commonFactor (PhaseGeometry.outerSize call S n) L m numeratorBits:ℝ) ≤
      100000000*((RealCertificate.c+3)*ComputedPhaseGeometry.indexMajor R+
        ComputedPhaseGeometry.outerLogConstant R+Cbits)^6*(Real.log (n:ℝ))^6 := by
  let m := ComputedPhaseGeometry.innerPower n call S
  let L := Nat.ceil (RealCertificate.c*(m:ℝ))
  let N := PhaseGeometry.outerSize call S n
  have hL := ComputedPhaseGeometry.actual_roundedLength_le_log R S n hn call
  have hm := ComputedPhaseGeometry.actual_innerPower_add_one_le_log R S n hn call
  have hN := ComputedPhaseGeometry.actual_outer_log2 R S n hn call
  have hsum : (L:ℝ)+(m:ℝ)+numeratorBits+(N.log2:ℝ)+1 ≤
      ((RealCertificate.c+3)*ComputedPhaseGeometry.indexMajor R+
        ComputedPhaseGeometry.outerLogConstant R+Cbits)*Real.log (n:ℝ) := by
    change (L:ℝ)+1 ≤ _ at hL
    change (m:ℝ)+1 ≤ _ at hm
    change (N.log2:ℝ) ≤ _ at hN
    nlinarith
  have hc : (commonFactor N L m numeratorBits:ℝ) ≤
      100000000*((L:ℝ)+(m:ℝ)+numeratorBits+(N.log2:ℝ)+1)^6 := by
    exact_mod_cast commonFactor_polynomial N L m numeratorBits
  calc
    _ ≤ 100000000*((L:ℝ)+(m:ℝ)+numeratorBits+(N.log2:ℝ)+1)^6 := hc
    _ ≤ 100000000*(((RealCertificate.c+3)*ComputedPhaseGeometry.indexMajor R+
        ComputedPhaseGeometry.outerLogConstant R+Cbits)*Real.log (n:ℝ))^6 := by gcongr
    _ = _ := by rw [mul_pow]; ring


def backendLocalFactor (N L m B : ℕ) : ℝ :=
  256*(commonFactor N L m B:ℝ)*
    ReductionCosts.localFactor RealCertificate.c RealCertificate.theta m (2*m+1)+
    40+64*((L:ℝ)+1)+((L:ℝ)+1)^2

open ReductionCosts in
theorem roundedCostBound_le_raw (n N m q μ B u : ℕ) (A : ℝ)
    (hA : 0 ≤ A) (hu : (u:ℝ) ≤ A) (hμ : (μ*u:ℕ) ≤ (q:ℝ)*A) :
    roundedCostBound N (n^2) m q μ B u ≤
      A*backendLocalFactor N (Nat.ceil (RealCertificate.c*(m:ℝ))) m B*
        ∑ i : Fin 6, rawTerm RealCertificate.c RealCertificate.theta n N ((4:ℝ)^m) q i := by
  let L := Nat.ceil (RealCertificate.c*(m:ℝ))
  let S := ∑ i : Fin 6, rawTerm RealCertificate.c RealCertificate.theta n N ((4:ℝ)^m) q i
  have hterm (i : Fin 6) : 0 ≤ rawTerm RealCertificate.c RealCertificate.theta n N ((4:ℝ)^m) q i :=
    rawTerm_nonneg _ _ _ _ _ _ (Nat.cast_nonneg n) (Nat.cast_nonneg N) (by positivity) (Nat.cast_nonneg q) i
  have hsingle (i : Fin 6) : rawTerm RealCertificate.c RealCertificate.theta n N ((4:ℝ)^m) q i ≤ S :=
    Finset.single_le_sum (fun j _ => hterm j) (Finset.mem_univ i)
  have hp := blockPower_le_raw RealCertificate.c RealCertificate.theta n N m q (2*m+1)
    u (μ*u) u 0 A hA hu hu (by simpa only [Nat.cast_zero] using hA) hμ
  have hp' : powerBound RealCertificate.c RealCertificate.theta N (n^2) m q (2*m+1) u (μ*u) u ≤
      A*localFactor RealCertificate.c RealCertificate.theta m (2*m+1)*S := by
    simpa only [Nat.cast_zero, mul_zero, zero_add] using hp
  have h5 : rawTerm RealCertificate.c RealCertificate.theta n N ((4:ℝ)^m) q 5 =
      (q:ℝ)*N*(4:ℝ)^m := by simp [rawTerm]
  have h4 : rawTerm RealCertificate.c RealCertificate.theta n N ((4:ℝ)^m) q 4 =
      (q:ℝ)*N*((4:ℝ)^m)^RealCertificate.Ebox := by
    change (q:ℝ)*N*((4:ℝ)^m)^(EntropyBounds.tileExponent RealCertificate.c-HighBoxEntropy.boxSaving RealCertificate.c RealCertificate.theta) = _
    rw [PhaseGeometry.tileExponent_eq_T, boxSaving_eq_G]
    rfl
  have h0 : rawTerm RealCertificate.c RealCertificate.theta n N ((4:ℝ)^m) q 0 =
      (q:ℝ)*(N:ℝ)^2*((4:ℝ)^m)^(-RealCertificate.G) := by
    norm_num [rawTerm, boxSaving_eq_G]
  let E : ℝ := 40*(q:ℝ)*N*(4:ℝ)^m+
    64*(q:ℝ)*N*((L:ℝ)+1)*((4:ℝ)^m)^RealCertificate.Ebox+
    (q:ℝ)*(N:ℝ)^2*((L:ℝ)+1)^2*((4:ℝ)^m)^(-RealCertificate.G)
  have hE0 : 0 ≤ E := by dsimp [E]; positivity
  have hE : E*(u:ℝ) ≤ A*(40+64*((L:ℝ)+1)+((L:ℝ)+1)^2)*S := by
    calc
      _ ≤ E*A := mul_le_mul_of_nonneg_left hu hE0
      _ = A*(40*rawTerm RealCertificate.c RealCertificate.theta n N ((4:ℝ)^m) q 5+
          (64*((L:ℝ)+1))*rawTerm RealCertificate.c RealCertificate.theta n N ((4:ℝ)^m) q 4+
          ((L:ℝ)+1)^2*rawTerm RealCertificate.c RealCertificate.theta n N ((4:ℝ)^m) q 0) := by
        rw [h5,h4,h0]
        dsimp [E]
        ring
      _ ≤ A*(40*S+(64*((L:ℝ)+1))*S+((L:ℝ)+1)^2*S) := by
        gcongr <;> exact hsingle _
      _ = _ := by ring
  have hscaled := mul_le_mul_of_nonneg_left hp'
    (show 0 ≤ 256*(commonFactor N L m B:ℝ) by positivity)
  change 256*(commonFactor N L m B:ℝ)*
    powerBound RealCertificate.c RealCertificate.theta N (n^2) m q (2*m+1) u (μ*u) u+E*u ≤ _
  calc
    _ ≤ 256*(commonFactor N L m B:ℝ)*
        (A*localFactor RealCertificate.c RealCertificate.theta m (2*m+1)*S)+
        A*(40+64*((L:ℝ)+1)+((L:ℝ)+1)^2)*S := add_le_add hscaled hE
    _ = _ := by dsimp [backendLocalFactor, S, L]; ring


open ReductionCosts in
theorem localFactor_width_bound (c theta : ℝ) (m w v : ℕ) (hw : 1 ≤ w) (hv : 1 ≤ v) :
    localFactor c theta m w ≤ (w:ℝ)^2*localFactor c theta m v := by
  let W : ℝ := w
  let V : ℝ := v
  let Cs := 4*(encoderPolynomial (Nat.ceil (c*(m:ℝ))):ℝ)*encoderTailFactor c theta m*gridRoundingFactor c
  let Cb := 8*boxFactor c theta m
  let Cl := 5*channelFactor theta m
  let Ch := 4*channelFactor theta m
  have hW : 1 ≤ W := by dsimp [W]; exact_mod_cast hw
  have hV : 1 ≤ V := by dsimp [V]; exact_mod_cast hv
  have hW0 : 0 ≤ W := by linarith
  have hV0 : 0 ≤ V := by linarith
  have hW2 : 1 ≤ W^2 := one_le_pow₀ hW
  have hV2 : 1 ≤ V^2 := one_le_pow₀ hV
  have hWW : W ≤ W^2 := by nlinarith
  have hWWV : W ≤ W^2*V := hWW.trans (by nlinarith)
  have hCs : 0 ≤ Cs := by dsimp [Cs]; unfold encoderTailFactor channelFactor gridRoundingFactor; positivity
  have hCb : 0 ≤ Cb := by dsimp [Cb]; unfold boxFactor; positivity
  have hCl : 0 ≤ Cl := by dsimp [Cl]; unfold channelFactor; positivity
  have hCh : 0 ≤ Ch := by dsimp [Ch]; unfold channelFactor; positivity
  have h0 : 2 ≤ W^2*2 := by nlinarith
  have hs := mul_le_mul_of_nonneg_left hWWV hCs
  have hb := mul_le_mul_of_nonneg_left hW2 hCb
  have hl := mul_le_mul_of_nonneg_left hV2 (mul_nonneg hCl (sq_nonneg W))
  have hh := mul_le_mul_of_nonneg_left hW2 hCh
  have h : 2+Cs*W+Cb+Cl*W^2+Ch ≤ W^2*(2+Cs*V+Cb+Cl*V^2+Ch) := by
    nlinarith only [h0,hs,hb,hl,hh]
  convert h using 1 <;> dsimp [localFactor, Cs,Cb,Cl,Ch,W,V] <;> ring

open ReductionCosts in
theorem localFactor_wide_polynomial (c theta : ℝ) (m : ℕ)
    (hc : 0 ≤ c) (ht : 0 ≤ theta) :
    localFactor c theta m (2*m+1) ≤ 4*Overhead.combinedConstant c theta*((m:ℝ)+1)^7 := by
  let M : ℝ := (m:ℝ)+1
  let v := Nat.ceil (2*theta*(m:ℝ))+1
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hv : 1 ≤ v := by dsimp [v]; omega
  have hwidth : (2*m+1:ℝ) ≤ 2*M := by dsimp [M]; linarith
  have hcombined : 0 ≤ Overhead.combinedFactor c theta m := by
    simpa [v, Overhead.combinedFactor, localFactor] using localFactor_nonneg c theta m v
  have hconstant := Overhead.combinedConstant_nonneg c theta hc ht
  calc
    _ ≤ (2*m+1:ℝ)^2*Overhead.combinedFactor c theta m := by
      simpa [v, Overhead.combinedFactor, localFactor] using localFactor_width_bound c theta m (2*m+1) v (by omega) hv
    _ ≤ (2*M)^2*(Overhead.combinedConstant c theta*M^5) := by
      gcongr
      exact Overhead.combinedFactor_le_fifth c theta m hc ht
    _ = _ := by dsimp [M]; ring


theorem size_add_one_le_log (n : ℕ) (hn : 3 ≤ n) :
    ((n.size+1:ℕ):ℝ) ≤ (2+1/Real.log 2)*Real.log (n:ℝ) := by
  have hs : 1 ≤ n.size := Nat.size_pos.mpr (by omega)
  have hp : (2:ℕ)^(n.size-1) ≤ n := Nat.lt_size.mp (by omega)
  have hpR : (2:ℝ)^(n.size-1) ≤ n := by exact_mod_cast hp
  have hl := Real.log_le_log (by positivity : (0:ℝ)<2^(n.size-1)) hpR
  rw [Real.log_pow] at hl
  have hcast : ((n.size-1:ℕ):ℝ)+1=(n.size:ℝ) := by exact_mod_cast Nat.sub_add_cancel hs
  have hl2 : (0:ℝ)<Real.log 2 := Real.log_pos (by norm_num)
  have hlog := PhaseGeometry.one_le_log_nat n hn
  apply (mul_le_mul_iff_right₀ hl2).mp
  have he : Real.log 2*((2+1/Real.log 2)*Real.log (n:ℝ)) =
      2*Real.log (n:ℝ)*Real.log 2+Real.log (n:ℝ) := by
    field_simp
  rw [he]
  push_cast
  nlinarith

theorem roundedCostBound_query_mono (N Q Q' m q fullBudget numeratorBits scalarUnit : ℕ)
    (hQ : Q ≤ Q') :
    roundedCostBound N Q m q fullBudget numeratorBits scalarUnit ≤
      roundedCostBound N Q' m q fullBudget numeratorBits scalarUnit := by
  unfold roundedCostBound powerBound
  dsimp only
  gcongr
  unfold channelFactor
  positivity

/-- A fixed number of window requests changes the actual bound by that
constant, while preparation is still performed only once. -/
theorem roundedCostBound_query_mul_bound (N Q m q fullBudget numeratorBits scalarUnit windows : ℕ)
    (hwindows : 1 ≤ windows) :
    roundedCostBound N (windows*Q) m q fullBudget numeratorBits scalarUnit ≤
      (windows:ℝ)*roundedCostBound N Q m q fullBudget numeratorBits scalarUnit := by
  have hzero : 0 ≤ roundedCostBound N 0 m q fullBudget numeratorBits scalarUnit := by
    unfold roundedCostBound powerBound encoderTailFactor channelFactor gridRoundingFactor boxFactor
    positivity
  have hw : (1:ℝ) ≤ windows := by exact_mod_cast hwindows
  have he : roundedCostBound N (windows*Q) m q fullBudget numeratorBits scalarUnit =
      (windows:ℝ)*roundedCostBound N Q m q fullBudget numeratorBits scalarUnit-
      ((windows:ℝ)-1)*roundedCostBound N 0 m q fullBudget numeratorBits scalarUnit := by
    unfold roundedCostBound powerBound
    push_cast
    ring
  rw [he]
  exact sub_le_self _ (mul_nonneg (by linarith) hzero)

/- Actual selected-request execution with all primitive adapters isolated.
The result is derived from its returned preparation and query counters, and
has exactly the six monomials needed by the computed phase ledger. -/
open ReductionCosts in
theorem executeRequests_le_raw {N D L m t q Q : ℕ} [NeZero q]
    (M : FullMultiplier q) (X : OriginalLeft N D q) (Y : OriginalRight N D q)
    (requests : Vector (TilingCosts.Request N q) Q) (hm : m ≤ L) (ht : t ≤ 2*m)
    (n windows : ℕ) (hwindows : 1 ≤ windows) (hQ : Q ≤ windows*n^2) (hm0 : 0 < m)
    (hL : L=Nat.ceil (RealCertificate.c*(m:ℝ)))
    (htheta : t=Nat.ceil (2*RealCertificate.theta*(m:ℝ)))
    (hgeometry : gridSide L m ≤ N) (fullBudget numeratorBits scalarUnit : ℕ)
    (hmul : GlobalMultiplierBudget M (prepareGlobal (L:=L) (m:=m) (t:=t) M X Y) fullBudget)
    (hsize : ∀ i : Fin Q, (globalNumerator (tileWidth_pos L m hm)
      (prepareGlobal (L:=L) (m:=m) (t:=t) M X Y) (requests.get i).row
        (requests.get i).column (requests.get i).coefficient).natAbs.size ≤ numeratorBits)
    (hband : (bandSourceBudget L m q:ℝ) ≤
      (q:ℝ)*((4:ℝ)^m)^(2*RealCertificate.T-RealCertificate.G))
    (hshape : ((prepareShape L m).operations:ℝ) ≤
      (q:ℝ)*((4:ℝ)^m)^(2*RealCertificate.T-RealCertificate.G))
    (A : ℝ) (hA : 0 ≤ A) (hscalar : (scalarUnit:ℝ) ≤ A)
    (hfull : (fullBudget*scalarUnit:ℕ) ≤ (q:ℝ)*A) :
    ((executeRequests (t:=t) (tileWidth_pos L m hm) M X Y requests).operations*scalarUnit:ℕ) ≤
      (windows:ℝ)*A*backendLocalFactor N L m numeratorBits*
        ∑ i : Fin 6, rawTerm RealCertificate.c RealCertificate.theta n N ((4:ℝ)^m) q i := by
  have he := rounded_executeRequests_bound M X Y requests hm ht hm0 hL htheta hgeometry
    fullBudget numeratorBits scalarUnit hmul hsize hband hshape
  have hmono := roundedCostBound_query_mono N Q (windows*n^2) m q fullBudget numeratorBits scalarUnit hQ
  have hwindow := roundedCostBound_query_mul_bound N (n^2) m q fullBudget numeratorBits scalarUnit windows hwindows
  have hraw := roundedCostBound_le_raw n N m q fullBudget numeratorBits scalarUnit A hA hscalar hfull
  rw [←hL] at hraw
  calc
    _ ≤ roundedCostBound N Q m q fullBudget numeratorBits scalarUnit := he
    _ ≤ roundedCostBound N (windows*n^2) m q fullBudget numeratorBits scalarUnit := hmono
    _ ≤ (windows:ℝ)*roundedCostBound N (n^2) m q fullBudget numeratorBits scalarUnit := hwindow
    _ ≤ (windows:ℝ)*(A*backendLocalFactor N L m numeratorBits*
        ∑ i : Fin 6, rawTerm RealCertificate.c RealCertificate.theta n N ((4:ℝ)^m) q i) :=
      mul_le_mul_of_nonneg_left hraw (Nat.cast_nonneg windows)
    _ = _ := by ring


open ReductionCosts in
def backendCoefficientConstant (R : ℕ) (Cbits : ℝ) : ℝ :=
  let Ccommon := 100000000*((RealCertificate.c+3)*ComputedPhaseGeometry.indexMajor R+
    ComputedPhaseGeometry.outerLogConstant R+Cbits)^6
  let Cwide := 4*Overhead.combinedConstant RealCertificate.c RealCertificate.theta*
    (ComputedPhaseGeometry.indexMajor R)^7
  let lenC := (RealCertificate.c+2)*ComputedPhaseGeometry.indexMajor R
  256*Ccommon*Cwide+40+64*lenC+lenC^2

open ReductionCosts in
theorem computed_backendLocalFactor_le_polylog (R S n numeratorBits : ℕ) (hn : 3 ≤ n)
    (call : ComputedPhaseGeometry.Call R n) (Cbits : ℝ) (_hCbits : 0 ≤ Cbits)
    (hbits : (numeratorBits:ℝ) ≤ Cbits*Real.log (n:ℝ)) :
    let m := ComputedPhaseGeometry.innerPower n call S
    let L := Nat.ceil (RealCertificate.c*(m:ℝ))
    backendLocalFactor (PhaseGeometry.outerSize call S n) L m numeratorBits ≤
      backendCoefficientConstant R Cbits*(Real.log (n:ℝ))^13 := by
  let m := ComputedPhaseGeometry.innerPower n call S
  let L := Nat.ceil (RealCertificate.c*(m:ℝ))
  let N := PhaseGeometry.outerSize call S n
  let l := Real.log (n:ℝ)
  let Ccommon := 100000000*((RealCertificate.c+3)*ComputedPhaseGeometry.indexMajor R+
    ComputedPhaseGeometry.outerLogConstant R+Cbits)^6
  let Cwide := 4*Overhead.combinedConstant RealCertificate.c RealCertificate.theta*
    (ComputedPhaseGeometry.indexMajor R)^7
  let lenC := (RealCertificate.c+2)*ComputedPhaseGeometry.indexMajor R
  have hc : 0 ≤ RealCertificate.c := by norm_num [RealCertificate.c]
  have ht : 0 ≤ RealCertificate.theta := by norm_num [RealCertificate.theta]
  have hI := (ComputedPhaseGeometry.indexMajor_pos R).le
  have hO : 0 ≤ ComputedPhaseGeometry.outerLogConstant R := by
    have heta := AsymptoticCosts.stageRelations.1
    unfold ComputedPhaseGeometry.outerLogConstant
    positivity
  have hCcommon : 0 ≤ Ccommon := by dsimp [Ccommon]; positivity
  have hcomb := Overhead.combinedConstant_nonneg RealCertificate.c RealCertificate.theta hc ht
  have hCwide : 0 ≤ Cwide := by dsimp [Cwide]; positivity
  have hlenC : 0 ≤ lenC := by dsimp [lenC]; positivity
  have hl : 1 ≤ l := PhaseGeometry.one_le_log_nat n hn
  have hl0 : 0 ≤ l := by linarith
  have hcommon : (commonFactor N L m numeratorBits:ℝ) ≤ Ccommon*l^6 :=
    computed_commonFactor_le_polylog R S n numeratorBits hn call Cbits hbits
  have hm := ComputedPhaseGeometry.actual_innerPower_add_one_le_log R S n hn call
  have hlocal : localFactor RealCertificate.c RealCertificate.theta m (2*m+1) ≤ Cwide*l^7 := by
    calc
      _ ≤ 4*Overhead.combinedConstant RealCertificate.c RealCertificate.theta*((m:ℝ)+1)^7 :=
        localFactor_wide_polynomial _ _ _ hc ht
      _ ≤ 4*Overhead.combinedConstant RealCertificate.c RealCertificate.theta*
          (ComputedPhaseGeometry.indexMajor R*l)^7 := by gcongr
      _ = _ := by dsimp [Cwide]; rw [mul_pow]; ring
  have hL : (L:ℝ)+1 ≤ lenC*l := ComputedPhaseGeometry.actual_roundedLength_le_log R S n hn call
  have hlocal0 := localFactor_nonneg RealCertificate.c RealCertificate.theta m (2*m+1)
  have hmain : 256*(commonFactor N L m numeratorBits:ℝ)*
      localFactor RealCertificate.c RealCertificate.theta m (2*m+1) ≤
      (256*Ccommon*Cwide)*l^13 := by
    calc
      _ ≤ 256*(Ccommon*l^6)*(Cwide*l^7) := by
        gcongr
      _ = _ := by rw [show (13:ℕ)=6+7 by omega, pow_add]; ring
  have hl1 : l ≤ l^13 := by simpa using pow_le_pow_right₀ hl (show 1≤13 by omega)
  have hl2 : l^2 ≤ l^13 := pow_le_pow_right₀ hl (by omega)
  have hl13 : 1 ≤ l^13 := one_le_pow₀ hl
  have h40 : (40:ℝ) ≤ 40*l^13 := by nlinarith
  have h64 : 64*((L:ℝ)+1) ≤ (64*lenC)*l^13 := by
    calc
      _ ≤ 64*(lenC*l) := mul_le_mul_of_nonneg_left hL (by norm_num)
      _ = (64*lenC)*l := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hl1 (by positivity)
  have hsq : ((L:ℝ)+1)^2 ≤ lenC^2*l^13 := by
    calc
      _ ≤ (lenC*l)^2 := by gcongr
      _ = lenC^2*l^2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hl2 (sq_nonneg _)
  change backendLocalFactor N L m numeratorBits ≤ _
  unfold backendLocalFactor
  calc
    _ ≤ (256*Ccommon*Cwide)*l^13+40*l^13+(64*lenC)*l^13+lenC^2*l^13 := by
      exact add_le_add (add_le_add (add_le_add hmain h40) h64) hsq
    _ = _ := by dsimp [backendCoefficientConstant, Ccommon, Cwide, lenC, l]; ring



theorem backendCoefficientConstant_nonneg (R : ℕ) (Cbits : ℝ) :
    0 ≤ backendCoefficientConstant R Cbits := by
  have hc : 0 ≤ RealCertificate.c := by norm_num [RealCertificate.c]
  have ht : 0 ≤ RealCertificate.theta := by norm_num [RealCertificate.theta]
  have hI := (ComputedPhaseGeometry.indexMajor_pos R).le
  have hC := ReductionCosts.Overhead.combinedConstant_nonneg RealCertificate.c RealCertificate.theta hc ht
  unfold backendCoefficientConstant
  positivity


end
end ThinMatrix.BackendCostRefinement

#print axioms ThinMatrix.BackendCostRefinement.prepareHigh_le_old_schedule
#print axioms ThinMatrix.BackendCostRefinement.fftFullMultiplier_allowance
#print axioms ThinMatrix.BackendCostRefinement.actual_sourcePreparation_fit
#print axioms ThinMatrix.BackendCostRefinement.actual_refinementFactor_le_polylog
#print axioms ThinMatrix.BackendCostRefinement.prepareLeftBand_operations_le
#print axioms ThinMatrix.BackendCostRefinement.prepareRightBand_operations_le
#print axioms ThinMatrix.BackendCostRefinement.BandShapeCosts.eventual_bandSourceBudget_fit
#print axioms ThinMatrix.BackendCostRefinement.BandShapeCosts.eventual_prepareShape_fit
#print axioms ThinMatrix.BackendCostRefinement.actual_uniformLedger_le
#print axioms ThinMatrix.BackendCostRefinement.prepareTile_operations_le
#print axioms ThinMatrix.BackendCostRefinement.queryTile_operations_le
#print axioms ThinMatrix.BackendCostRefinement.prepareGlobal_operations_le
#print axioms ThinMatrix.BackendCostRefinement.queryGlobal_operations_le

#print axioms ThinMatrix.BackendCostRefinement.executeRequests_correct
#print axioms ThinMatrix.BackendCostRefinement.executeRequests_operations_le

#print axioms ThinMatrix.BackendCostRefinement.global_finite_comparison

#print axioms ThinMatrix.BackendCostRefinement.source_extras_bound
#print axioms ThinMatrix.BackendCostRefinement.executeRequests_scalar_ledger

#print axioms ThinMatrix.BackendCostRefinement.rounded_executeRequests_bound

#print axioms ThinMatrix.BackendCostRefinement.computed_source_budgets_fit
#print axioms ThinMatrix.BackendCostRefinement.computed_commonFactor_le_polylog

#print axioms ThinMatrix.BackendCostRefinement.roundedCostBound_le_raw

#print axioms ThinMatrix.BackendCostRefinement.localFactor_wide_polynomial

#print axioms ThinMatrix.BackendCostRefinement.executeRequests_le_raw

#print axioms ThinMatrix.BackendCostRefinement.computed_backendLocalFactor_le_polylog

#print axioms ThinMatrix.BackendCostRefinement.backendCoefficientConstant_nonneg
